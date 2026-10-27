module

public import CFSG.RankThree.GF2n.Stroth80.Sec1110FieldRecovery
public import CFSG.RankThree.GF2n.Stroth80.Sec1110Final
public import CFSG.RankThree.GF2n.Stroth80.Sec1110Orth
public import CFSG.RankThree.GF2n.Stroth80.Sec1110Kernel

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.Adapters.RankTwoModelTransports
open scoped commutatorElement Matrix

variable {G : Type} [Group G]

private def funAddEquiv {ι : Type} {K L : Type} [Field K] [Field L] (e : K ≃+* L) :
    (ι → K) ≃+ (ι → L) where
  toFun v i := e (v i)
  invFun v i := e.symm (v i)
  left_inv v := by funext i; simp
  right_inv v := by funext i; simp
  map_add' v w := by funext i; simp

theorem glCongr_mulVec {ι : Type} [Fintype ι] {K L : Type} [Field K] [Field L]
    (e : K ≃+* L) (M : Matrix ι ι K) (v : ι → K) :
    (M.map e.toRingHom) *ᵥ (fun i => e (v i)) = fun i => e ((M *ᵥ v) i) := by
  funext i
  exact (RingHom.map_mulVec e.toRingHom M v i).symm

theorem glCongr_statedSL {n : ℕ} {K L : Type} [Field K] [Field L] (e : K ≃+* L) :
    (StatedSL n K).map (glCongr (ι := Fin n) e).toMonoidHom = StatedSL n L := by
  unfold StatedSL
  rw [MonoidHom.map_closure]
  congr 1
  ext B
  constructor
  · rintro ⟨A, hA, rfl⟩
    show (((glCongr (ι := Fin n) e) A : GL (Fin n) L) :
      Matrix (Fin n) (Fin n) L).det = 1
    have hdet : (((A : Matrix (Fin n) (Fin n) K)).map e).det =
        e ((A : Matrix (Fin n) (Fin n) K).det) := by
      change (e.toRingHom.mapMatrix (A : Matrix (Fin n) (Fin n) K)).det =
        e ((A : Matrix (Fin n) (Fin n) K).det)
      exact (RingHom.map_det e.toRingHom (A : Matrix (Fin n) (Fin n) K)).symm
    rw [glCongr_coe, hdet, hA, map_one]
  · intro hB
    refine ⟨(glCongr (ι := Fin n) e).symm B, ?_, (glCongr (ι := Fin n) e).apply_symm_apply B⟩
    show ((((glCongr (ι := Fin n) e).symm B : GL (Fin n) K)) :
      Matrix (Fin n) (Fin n) K).det = 1
    have hdet : (((B : Matrix (Fin n) (Fin n) L)).map e.symm).det =
        e.symm ((B : Matrix (Fin n) (Fin n) L).det) := by
      change (e.symm.toRingHom.mapMatrix (B : Matrix (Fin n) (Fin n) L)).det =
        e.symm ((B : Matrix (Fin n) (Fin n) L).det)
      exact (RingHom.map_det e.symm.toRingHom (B : Matrix (Fin n) (Fin n) L)).symm
    rw [glCongr_symm_coe, hdet, hB, map_one]

theorem sectionAct_of_ringEquiv {ι : Type} [Fintype ι] [DecidableEq ι]
    {K L : Type} [Field K] [Field L] (e : K ≃+* L)
    {S V Z : Subgroup G} {φ : S →* GL ι K} {act : GL ι K → Matrix ι ι K}
    {actL : GL ι L → Matrix ι ι L}
    (hact : ∀ g : GL ι K, actL (glCongr (ι := ι) e g) = (act g).map e.toRingHom)
    (h : SectionAct K S V Z φ act) :
    SectionAct L S V Z ((glCongr (ι := ι) e).toMonoidHom.comp φ) actL := by
  obtain ⟨hnorm, hN, ψ, hψ⟩ := h
  letI := hN
  let ψL : ↥V ⧸ Z.subgroupOf V ≃* Multiplicative (ι → L) :=
    ψ.trans (funAddEquiv e).toMultiplicative
  refine ⟨hnorm, hN, ψL, ?_⟩
  intro s v w hw
  have hψ' := hψ s v w hw
  have hψL : ∀ x : ↥V ⧸ Z.subgroupOf V,
      Multiplicative.toAdd (ψL x) = fun i => e (Multiplicative.toAdd (ψ x) i) := fun x => rfl
  change Multiplicative.toAdd (ψL (QuotientGroup.mk w)) =
    actL (glCongr (ι := ι) e (φ s)) *ᵥ Multiplicative.toAdd (ψL (QuotientGroup.mk v))
  rw [hψL, hψL, hψ', hact]
  exact (glCongr_mulVec e (act (φ s))
    (Multiplicative.toAdd (ψ (QuotientGroup.mk v)))).symm

theorem naturalRep_of_ringEquiv {ι : Type} [Fintype ι] [DecidableEq ι]
    {K L : Type} [Field K] [Field L] (e : K ≃+* L)
    {X : Subgroup (GL ι K)} {R V Z N : Subgroup G}
    (h : NaturalRep (ι := ι) K X R V Z N) :
    NaturalRep (ι := ι) L (X.map (glCongr (ι := ι) e).toMonoidHom) R V Z N := by
  obtain ⟨φ, hrange, hker, hact⟩ := h
  refine ⟨(glCongr (ι := ι) e).toMonoidHom.comp φ, ?_, ?_, ?_⟩
  · rw [MonoidHom.range_comp, hrange]
  · ext x
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← hker, MonoidHom.mem_ker]
    constructor
    · intro hx
      exact (glCongr (ι := ι) e).injective (by simpa using hx)
    · intro hx
      rw [hx, map_one]
  · exact sectionAct_of_ringEquiv (act := fun g => (g : Matrix ι ι K))
      (actL := fun g => (g : Matrix ι ι L)) e (fun g => glCongr_coe e g) hact

theorem naturalDualRep_of_ringEquiv {ι : Type} [Fintype ι] [DecidableEq ι]
    {K L : Type} [Field K] [Field L] (e : K ≃+* L)
    {X : Subgroup (GL ι K)} {R V Z N : Subgroup G}
    (h : NaturalDualRep (ι := ι) K X R V Z N) :
    NaturalDualRep (ι := ι) L (X.map (glCongr (ι := ι) e).toMonoidHom) R V Z N := by
  obtain ⟨φ, hrange, hker, hact⟩ := h
  refine ⟨(glCongr (ι := ι) e).toMonoidHom.comp φ, ?_, ?_, ?_⟩
  · rw [MonoidHom.range_comp, hrange]
  · ext x
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← hker, MonoidHom.mem_ker]
    constructor
    · intro hx
      exact (glCongr (ι := ι) e).injective (by simpa using hx)
    · intro hx
      rw [hx, map_one]
  · refine sectionAct_of_ringEquiv
      (act := fun g => (((g⁻¹ : GL ι K) : Matrix ι ι K))ᵀ)
      (actL := fun g => (((g⁻¹ : GL ι L) : Matrix ι ι L))ᵀ) e ?_ hact
    intro g
    rw [← map_inv, glCongr_coe, Matrix.transpose_map]
    rfl

theorem center_statedOmega_quadPlus_eq_bot {m : ℕ} {K : Type} [Field K] [CharP K 2]
    (hm : 3 ≤ m) : Subgroup.center (StatedOmega (StatedQuadPlus m K)) = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro z hz
  have hmem : (z : GL (Fin m ⊕ Fin m) K) ∈ StatedOmega (StatedQuadPlus m K) := z.2
  let f : (Fin m ⊕ Fin m → K) →+ (Fin m ⊕ Fin m → K) :=
    (Matrix.mulVecLin (Units.val (z : GL (Fin m ⊕ Fin m) K))).toAddMonoidHom
  have hf : ∀ A ∈ StatedOmega (StatedQuadPlus m K), ∀ v,
      f ((A : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ v) =
        (A : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ f v := by
    intro A hA v
    have hcomm : ((z : GL (Fin m ⊕ Fin m) K) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) * (A : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) =
        (A : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) * ((z : GL (Fin m ⊕ Fin m) K) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) := by
      have h := Subgroup.mem_center_iff.mp hz ⟨A, hA⟩
      have h' := congrArg (fun g : ↥(StatedOmega (StatedQuadPlus m K)) =>
        ((g : GL (Fin m ⊕ Fin m) K) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K)) h
      simpa using h'.symm
    change ((z : GL (Fin m ⊕ Fin m) K) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ
        ((A : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ v) =
      (A : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ (((z : GL (Fin m ⊕ Fin m) K) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ v)
    rw [Matrix.mulVec_mulVec, hcomm, ← Matrix.mulVec_mulVec]
  obtain ⟨c, hc⟩ := addCommutantScalar_statedOmegaPlus (m := m) hm f hf
  have hzmat : ((z : GL (Fin m ⊕ Fin m) K) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) =
      c • 1 := by
    ext i j
    have h := congrFun (hc (Pi.single j 1)) i
    simpa [f, Matrix.mulVec_single_one, Matrix.col_apply, Pi.smul_apply,
      Matrix.one_apply, Pi.single_apply, smul_eq_mul] using h
  have hm0 : 0 < m := by omega
  let P : CFSG.ClassicalGroups.Orthogonal.HypPair
      (CFSG.LieType.Universal.Spin.quadPlus m K) :=
    CFSG.ClassicalGroups.Orthogonal.plusPair K ⟨0, hm0⟩
  have hQv : CFSG.LieType.Universal.Spin.quadPlus m K (P.e + P.f) = 1 := by
    rw [QuadraticMap.map_add (CFSG.LieType.Universal.Spin.quadPlus m K) P.e P.f,
      P.Q_e, P.Q_f, P.polar_ef]
    ring
  have hpres := statedOmega_quadPlus_mulVec (m := m) hmem (P.e + P.f)
  have hc2 : c * c = 1 := by
    have hc1 : ((c • (1 : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K)) *ᵥ
        (P.e + P.f)) = c • (P.e + P.f) := by
      rw [Matrix.smul_mulVec, Matrix.one_mulVec]
    have h : CFSG.LieType.Universal.Spin.quadPlus m K (c • (P.e + P.f)) = 1 := by
      rw [← hc1, ← hzmat]
      simpa [hQv] using hpres
    rw [QuadraticMap.map_smul (CFSG.LieType.Universal.Spin.quadPlus m K) c
      (P.e + P.f), smul_eq_mul, hQv, mul_one] at h
    exact h
  rcases mul_self_eq_one_iff.mp hc2 with h1 | h1
  · apply Subtype.ext
    apply Units.ext
    rw [hzmat, h1, one_smul]
    rfl
  · apply Subtype.ext
    apply Units.ext
    rw [hzmat, h1, CharTwo.neg_eq, one_smul]
    rfl


theorem XbarPreCenter_eq_Q_of_naturalRep_omega [Finite G]
    {M Q Z B : Subgroup G} [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B)
    {K : Type} [Field K] [CharP K 2]
    (nat : NaturalRep (ι := Fin 3 ⊕ Fin 3) K (StatedOmega (StatedQuadPlus 3 K))
      (XbarPre M Q Z B) Q Z (Q)) :
    XbarPreCenter M Q Z B = Q := by
  refine le_antisymm ?_ (Q_le_XbarPreCenter hc)
  intro x hx
  obtain ⟨m, hmcent, hmx⟩ := Subgroup.mem_map.mp hx
  obtain ⟨c, hc_center, hceq⟩ := Subgroup.mem_map.mp hmcent
  obtain ⟨φ, hrange, hker, -⟩ := nat
  let φ' : ↥(XbarPre M Q Z B) →* ↥(StatedOmega (StatedQuadPlus 3 K)) :=
    φ.codRestrict _ (fun g => by rw [← hrange]; exact ⟨g, rfl⟩)
  have hker' : φ'.ker = Q.subgroupOf (XbarPre M Q Z B) := by
    rw [MonoidHom.ker_codRestrict]
    exact hker
  have hsurj : Function.Surjective φ' := by
    intro y
    have hy : (y : GL (Fin 3 ⊕ Fin 3) K) ∈ φ.range := by
      rw [hrange]
      exact y.2
    obtain ⟨g, hg⟩ := MonoidHom.mem_range.mp hy
    exact ⟨g, Subtype.ext hg⟩
  have hxpre : (m : G) ∈ XbarPre M Q Z B := by
    refine Subgroup.mem_map.mpr ⟨m, ?_, rfl⟩
    rw [Subgroup.mem_comap, ← hceq]
    exact c.2
  have hmQ : (m : G) ∈ Q := by
    have hφcent : φ' ⟨(m : G), hxpre⟩ ∈
        Subgroup.center (StatedOmega (StatedQuadPlus 3 K)) := by
      rw [Subgroup.mem_center_iff]
      intro a
      obtain ⟨y, hy⟩ := hsurj a
      have hyM : ((y : ↥(XbarPre M Q Z B)) : G) ∈ M := XbarPre_le_M hc y.2
      have hybar : (QuotientGroup.mk' (Q.subgroupOf M)) ⟨(y : G), hyM⟩ ∈
          Xbar M Q Z B := by
        obtain ⟨n, hn, hny⟩ := Subgroup.mem_map.mp y.2
        have hyn : (⟨(y : G), hyM⟩ : ↥M) = n := Subtype.ext hny.symm
        rw [hyn]
        exact hn
      have hcommc : (Xbar M Q Z B).subtype c *
          (QuotientGroup.mk' (Q.subgroupOf M)) ⟨(y : G), hyM⟩ =
        (QuotientGroup.mk' (Q.subgroupOf M)) ⟨(y : G), hyM⟩ *
          (Xbar M Q Z B).subtype c := by
        have h := (Subgroup.mem_center_iff.mp hc_center ⟨_, hybar⟩).symm
        exact congrArg (fun z : ↥(Xbar M Q Z B) => (z : Mbar M Q)) h
      have hcommM : (QuotientGroup.mk' (Q.subgroupOf M))
          ⁅m, (⟨(y : G), hyM⟩ : ↥M)⁆ = 1 := by
        rw [map_commutatorElement, ← hceq]
        exact commutatorElement_eq_one_iff_mul_comm.mpr hcommc
      have hqsub : ⁅(⟨(m : G), hxpre⟩ : ↥(XbarPre M Q Z B)), y⁆ ∈
          Q.subgroupOf (XbarPre M Q Z B) := by
        have hqM : ⁅m, (⟨(y : G), hyM⟩ : ↥M)⁆ ∈ Q.subgroupOf M :=
          (QuotientGroup.eq_one_iff (N := Q.subgroupOf M) _).mp hcommM
        rw [Subgroup.mem_subgroupOf] at hqM ⊢
        simpa [commutatorElement_def] using hqM
      have hqker : ⁅(⟨(m : G), hxpre⟩ : ↥(XbarPre M Q Z B)), y⁆ ∈ φ'.ker := by
        rw [hker']
        exact hqsub
      have hφcomm : φ' ⁅(⟨(m : G), hxpre⟩ : ↥(XbarPre M Q Z B)), y⁆ = 1 :=
        MonoidHom.mem_ker.mpr hqker
      rw [map_commutatorElement] at hφcomm
      have hcomm := commutatorElement_eq_one_iff_mul_comm.mp hφcomm
      rw [← hy]
      exact hcomm.symm
    have hcentbot : Subgroup.center (StatedOmega (StatedQuadPlus 3 K)) = ⊥ :=
      center_statedOmega_quadPlus_eq_bot (m := 3) (by norm_num)
    rw [hcentbot] at hφcent
    have hφ1 : φ' ⟨(m : G), hxpre⟩ = 1 := Subgroup.mem_bot.mp hφcent
    have hmker : (⟨(m : G), hxpre⟩ : ↥(XbarPre M Q Z B)) ∈ φ'.ker :=
      MonoidHom.mem_ker.mpr hφ1
    rw [hker'] at hmker
    exact Subgroup.mem_subgroupOf.mp hmker
  rw [← hmx]
  exact hmQ


theorem caseVICore_of_CMLmChain [Finite G]
    {M Q Z B : Subgroup G} [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B)
    {n m x : ℕ} (hw : Width Q Z n) (hn : 2 < n)
    (ha2 : ∃ a ∈ LB M Q B, IsA2 Q Z a)
    (hC : CMLmChain) (hLm : CFSG.Blueprint.LieModel (XbarMod M Q Z B) .PSL m 2 x)
    (hm : 3 ≤ m)
    (hLgen : Lgen M (LB M Q B) ≤ XbarPre M Q Z B) :
    Xbar M Q Z B = bar M Q (Lgen M (LB M Q B)) ∧
      CaseVICore M Q Z (Lgen M (LB M Q B)) n := by
  obtain ⟨n₀, γ₀, M₀₀, hZcard, hD₀⟩ := stroth_globalModelDataGF hc.hyp
  have hn₀ : n₀ ≠ 0 := by
    rintro rfl
    simp only [pow_zero] at hZcard
    have := hc.hyp.q4
    omega
  have hK₀card : Nat.card (GaloisField 2 n₀) = Nat.card Z :=
    (GaloisField.card 2 n₀ hn₀).trans hZcard.symm
  have hZ₂ : 2 ≤ Nat.card Z := by have := hc.hyp.q4; omega
  have hC' := hC G M Q Z B hc n m x hw hn ha2 hLm hm
  rcases hC' with hLmBranch | hL4Branch
  · obtain ⟨X₁, X₂, X₃, X₄, hX₁, h₁₂, h₂₃, h₃₄, hX₄Q, hcomm, hX₂, hX₃, hX₄,
      K', hK'f, hK'fin, hK'card, nat2, nat4⟩ := hLmBranch
    letI : Field K' := hK'f
    letI : Finite K' := hK'fin
    have hX₂Q' : X₂ ≤ Q := by rw [← hX₄Q]; exact h₂₃.trans h₃₄
    have hx : 2 ^ x = Nat.card Z :=
      two_pow_eq_card_Z_of_naturalRep hc (by omega) hX₁ hX₂Q' nat2 hLm hK'card
    letI : Fintype K' := Fintype.ofFinite K'
    letI : Fintype (GaloisField 2 n₀) := Fintype.ofFinite _
    have hcardEq : Fintype.card K' = Fintype.card (GaloisField 2 n₀) := by
      rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hK'card, hK₀card]
    let e : K' ≃+* GaloisField 2 n₀ := FiniteField.ringEquivOfCardEq hcardEq
    have hZ₁ : Z ≤ X₁ := hX₁ ▸ le_rfl
    have hcardX₄ : Nat.card X₄ = Nat.card Z * Nat.card K' ^ (2 * m) :=
      card_X₄_of_dualRep (K := K') (m := m) hX₁ hZ₁ h₁₂ h₂₃ h₃₄ hX₃ nat2 nat4
    have hQcard : Nat.card Q = Nat.card Z ^ (2 * m + 1) := by
      rw [← hX₄Q, hcardX₄, hK'card, ← pow_succ']
    have hexp : 2 * n + 1 = 2 * m + 1 := by
      have h := hw
      rw [Width] at h
      rw [hQcard] at h
      exact (Nat.pow_right_injective hZ₂ h).symm
    have hnm : n = m := by omega
    have hw' : Width Q Z m := by
      rw [Width] at hw ⊢
      rwa [hnm] at hw
    have nat2K : NaturalRep (ι := Fin m) (GaloisField 2 n₀) (StatedSL m (GaloisField 2 n₀))
        (XbarPre M Q Z B) X₂ X₁ Q := by
      have h := naturalRep_of_ringEquiv (ι := Fin m) e nat2
      rwa [glCongr_statedSL] at h
    have nat4K : NaturalDualRep (ι := Fin m) (GaloisField 2 n₀)
        (StatedSL m (GaloisField 2 n₀)) (XbarPre M Q Z B) X₄ X₃ Q := by
      have h := naturalDualRep_of_ringEquiv (ι := Fin m) e nat4
      rwa [glCongr_statedSL] at h
    have hcore : CaseVICore M Q Z (XbarPre M Q Z B) m :=
      caseVICore_of_chain_final_unconditional (K := GaloisField 2 n₀) (γ := γ₀)
        (M₀ := M₀₀) (n := m) hc hw' (by omega) hD₀ hK₀card hX₁ h₁₂ h₂₃ h₃₄ hX₄Q.le
        hX₂ hX₃ hX₄ nat2K nat4K
    have hLgen_eq := Lgen_eq_XbarPre_of_le hc hLgen
    have hcore' : CaseVICore M Q Z (Lgen M (LB M Q B)) n := by
      rw [← hLgen_eq] at hcore
      rw [← hnm] at hcore
      exact hcore
    exact ⟨(bar_Lgen_eq_Xbar hc hLgen).symm, hcore'⟩
  · obtain ⟨hm4, X₁, X₂, hX₁, h₁₂, hX₂Q, hcomm, hX₂,
      K', hK'f, hK'fin, hK'card, nat⟩ := hL4Branch
    letI : Field K' := hK'f
    letI : Finite K' := hK'fin
    letI : Fintype K' := Fintype.ofFinite K'
    letI : Fintype (GaloisField 2 n₀) := Fintype.ofFinite _
    have hcardEq : Fintype.card K' = Fintype.card (GaloisField 2 n₀) := by
      rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hK'card, hK₀card]
    let e : K' ≃+* GaloisField 2 n₀ := FiniteField.ringEquivOfCardEq hcardEq
    haveI : CharP K' 2 := by
      apply charP_of_card_eq_prime_pow (p := 2) (f := n₀)
      rw [Fintype.card_eq_nat_card, hK'card, hZcard]
    have natQ : NaturalRep (ι := Fin 3 ⊕ Fin 3) K' (StatedOmega (StatedQuadPlus 3 K'))
        (XbarPre M Q Z B) Q Z Q := by
      simpa [hX₂Q, hX₁] using nat
    have hcenter : XbarPreCenter M Q Z B = Q :=
      XbarPreCenter_eq_Q_of_naturalRep_omega (K := K') hc natQ
    have natC : NaturalRep (ι := Fin 3 ⊕ Fin 3) K' (StatedOmega (StatedQuadPlus 3 K'))
        (XbarPre M Q Z B) X₂ X₁ (XbarPreCenter M Q Z B) := by
      rw [hcenter]
      exact nat
    have hQmap : ∀ v : Fin 3 ⊕ Fin 3 → K',
        StatedQuadPlus 3 (GaloisField 2 n₀) (e ∘ v) =
          e (StatedQuadPlus 3 K' v) := by
      intro v
      unfold StatedQuadPlus
      simp [CFSG.MatrixModel.plusQuadCore, map_sum, map_mul]
    have hΩmap := CFSG.ClassicalInvolution.Upgrade.map_statedOmega (K := K')
      (L := GaloisField 2 n₀) (QK := StatedQuadPlus 3 K')
      (QL := StatedQuadPlus 3 (GaloisField 2 n₀)) e hQmap
    have natCK : NaturalRep (ι := Fin 3 ⊕ Fin 3) (GaloisField 2 n₀)
        (StatedOmega (StatedQuadPlus 3 (GaloisField 2 n₀))) (XbarPre M Q Z B) X₂ X₁
        (XbarPreCenter M Q Z B) := by
      have h := naturalRep_of_ringEquiv (ι := Fin 3 ⊕ Fin 3) e natC
      rwa [hΩmap] at h
    exact (l4Orthogonal_case_false_of_chain (K := GaloisField 2 n₀) (γ := γ₀)
      (M₀ := M₀₀) hc hw (by omega) hD₀ hX₂Q hX₁ natCK).elim

end CFSG.RankThree.GF2n.Stroth80
