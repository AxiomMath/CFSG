module

public import CFSG.Quasithin.SteinbergCCSylowCoreResidual
public import CFSG.Quasithin.SteinbergCCNormalizerFactorization
public import CFSG.LocalAnalysis.SectionRank.Ccomm.PrimeRecognition
public import CFSG.LocalAnalysis.SectionRank.Ccomm.ElementaryAut
public import CFSG.GroupTheory.FrattiniQuotient
public import CFSG.LocalAnalysis.SteinbergCCCComponentSubnormalSolvable
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.LocalAnalysis.ComponentInitial.QuasisimpleRankOne
public import CFSG.LieType.BorelTits.Basic

public section

namespace CFSG.Quasithin.H13.NQTerm

open Subgroup
open CFSG.Quasithin.SteinbergCC (frattiniQuotConj coreQuotConj)
open scoped commutatorElement Pointwise

theorem isQuasisimple_of_le_mulAut_plane
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {W : Type*}
    [Group W] [Finite W] (hcomm : ∀ a b : W, a * b = b * a) (hpow : ∀ a : W, a ^ p = 1)
    (hcard : Nat.card W = p ^ 2) (J : Subgroup (MulAut W)) [Group.IsPerfect J] (hJ : J ≠ ⊥) :
    CFSG.IsQuasisimple J := by
  obtain ⟨e⟩ := CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary hcomm hpow hcard
  set φ := CFSG.SectionRank.Ccomm.elemAutEquivGL e
  have : Group.IsPerfect (J.map φ.toMonoidHom) := Group.IsPerfect.map _
  have hne : J.map φ.toMonoidHom ≠ ⊥ := fun h =>
    hJ ((Subgroup.map_eq_bot_iff_of_injective J φ.injective).mp h)
  obtain ⟨-, -, hq, -⟩ := CFSG.SectionRank.Ccomm.perfect_prime_linear_recognition hp2 _ hne
  have hq' : CFSG.IsQuasisimple (J.map φ.toMonoidHom) := by
    first
    | exact hq
    | exact A3.isQuasisimple_iff_open.mpr hq
  exact (CFSG.LocalAnalysis.ComponentInitial.isQuasisimple_congr
    (J.equivMapOfInjective φ.toMonoidHom φ.injective)).mpr hq'

variable {H : Type*} [Group H] [Finite H]

theorem isSolvable_inf_ker_of_mem_cComp {G' : Type*} [Group G'] {L : Subgroup H} [L.Normal]
    (hL : L ∈ cComp L) (ψ : H →* G') (hψ : L.map ψ ≠ ⊥) : Group.IsSolvable ↥(L ⊓ ψ.ker) := by
  have hLC : CFSG.IsCComponent L := mem_cComp_top_iff_isCComponent.mp
    (cComp_mem_of_subnormal (A3.subnormal_top_iff.mpr (inferInstance : L.Normal).isSubnormal) hL)
  have hlt : L ⊓ ψ.ker < L := by
    refine lt_of_le_of_ne inf_le_left fun h => hψ ?_
    rw [Subgroup.map_eq_bot_iff]
    exact h.symm.le.trans inf_le_right
  have hsub : ((L ⊓ ψ.ker).subgroupOf L).IsSubnormal := by
    have h : (L ⊓ ψ.ker).subgroupOf L = ψ.ker.subgroupOf L := by
      ext x
      simp [Subgroup.mem_subgroupOf]
    rw [h]
    exact (inferInstance : (ψ.ker.subgroupOf L).Normal).isSubnormal
  exact CFSG.LocalAnalysis.Ccomponent_proper_subnormal_solvable hLC hlt hsub

theorem mem_cComp_self_of_isQuasisimple_map {G' : Type*} [Group G'] [Finite G']
    {A : Subgroup H} (hA : ⁅A, A⁆ = A) (ψ : H →* G') (hq : CFSG.IsQuasisimple (A.map ψ))
    (hs : Group.IsSolvable ↥(A ⊓ ψ.ker)) : A ∈ cComp A := by
  set f := ψ.comp A.subtype with hf
  have hN : Group.IsSolvable f.ker := by
    refine Group.isSolvable_of_isSolvable_injective
      (f := (A.subtype.comp f.ker.subtype).codRestrict (A ⊓ ψ.ker) fun x => ⟨(x : A).2, x.2⟩)
      fun x y hxy => ?_
    have h := congrArg Subtype.val hxy
    exact Subtype.ext (Subtype.ext h)
  have hrange : f.range = A.map ψ := by
    rw [hf, MonoidHom.range_comp, Subgroup.range_subtype]
  have hJ : (⊤ : Subgroup ↥(A.map ψ)) ∈ cComp (⊤ : Subgroup ↥(A.map ψ)) := by
    refine mem_cComp_top_of_isComponent ⟨?_, Subgroup.IsSubnormal.top⟩
    exact (CFSG.LocalAnalysis.ComponentInitial.isQuasisimple_congr Subgroup.topEquiv).mpr hq
  let e : (↥A ⧸ f.ker) ≃* ↥(A.map ψ) :=
    (QuotientGroup.quotientKerEquivRange f).trans (MulEquiv.subgroupCongr hrange)
  have hQ : (⊤ : Subgroup (↥A ⧸ f.ker)) ∈ cComp (⊤ : Subgroup (↥A ⧸ f.ker)) := by
    have h := cComp_map_mulEquiv e.symm hJ
    have hsurj : Function.Surjective e.symm.toMonoidHom := e.symm.surjective
    rwa [Subgroup.map_top_of_surjective _ hsurj] at h
  obtain ⟨L₁, hL₁, hL₁π⟩ := (cComp_quotient_bijOn f.ker hN).surjOn hQ
  have h1 : L₁ ⊔ f.ker = ⊤ := by
    have h := congrArg (Subgroup.comap (QuotientGroup.mk' f.ker)) hL₁π
    rwa [Subgroup.comap_map_eq, QuotientGroup.ker_mk', Subgroup.comap_top] at h
  have hperf : ⁅(⊤ : Subgroup ↥A), ⊤⁆ = ⊤ :=
    (Subgroup.isPerfect_iff.mpr hA).commutator_eq_top
  have h2 := (cComp_commutator_perfectCore hL₁ le_top hN Subgroup.le_normalizer_of_normal).2
  rw [h1, perfectCore_eq_self_of_perfect hperf] at h2
  rw [← h2] at hL₁
  have h3 := map_subtype_mem_cComp hL₁
  rwa [← MonoidHom.range_eq_map, Subgroup.range_subtype] at h3

omit [Finite H] in
theorem not_isQuasisimple_pCore_quotient_of_commutator {A X Y : Subgroup H} (hXA : X ≤ A)
    (hXn : (X.subgroupOf A).Normal) (hXs : Group.IsSolvable X) (hYA : Y ≤ A)
    (hXY : ⁅X, Y⁆ = X) (hX2 : ¬ IsPGroup 2 X) : ¬ CFSG.IsQuasisimple (A ⧸ CFSG.pCore 2 A) := by
  intro hq
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' (CFSG.pCore 2 A) with hπ
  have hXbn : ((X.subgroupOf A).map π).Normal := hXn.map π (QuotientGroup.mk'_surjective _)
  have : Group.IsSolvable ↥(X.subgroupOf A) :=
    Group.isSolvable_of_isSolvable_injective (f := (Subgroup.subgroupOfEquivOfLe hXA).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hXA).injective
  have hXbs : Group.IsSolvable ↥((X.subgroupOf A).map π) :=
    Group.isSolvable_of_surjective (π.subgroupMap_surjective (X.subgroupOf A))
  rcases CFSG.LocalAnalysis.ComponentInitial.quasisimple_normal_subgroups hq hXbn with h | h
  · apply CFSG.LocalAnalysis.ComponentInitial.not_isSolvable_of_isQuasisimple hq
    rw [h] at hXbs
    let e : (A ⧸ CFSG.pCore 2 A) ≃* ↥(⊤ : Subgroup (A ⧸ CFSG.pCore 2 A)) :=
      Subgroup.topEquiv.symm
    exact Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
  · apply hX2
    have hXO : X ≤ (CFSG.pCore 2 A).map A.subtype := by
      rw [← hXY, Subgroup.commutator_le]
      intro x hx y hy
      have hz : π ⟨x, hXA hx⟩ ∈ center (A ⧸ CFSG.pCore 2 A) := h ⟨⟨x, hXA hx⟩, hx, rfl⟩
      have h1 : π ⁅(⟨x, hXA hx⟩ : A), ⟨y, hYA hy⟩⁆ = 1 := by
        rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
        exact (Subgroup.mem_center_iff.mp hz _).symm
      exact ⟨⁅(⟨x, hXA hx⟩ : A), ⟨y, hYA hy⟩⁆, (QuotientGroup.eq_one_iff _).mp h1, rfl⟩
    exact ((CFSG.pCore_isPGroup (p := 2) (G := A)).map A.subtype).to_le hXO

theorem isSolvable_ker_restrict {G' : Type*} [Group G'] {K B T : Subgroup H} (hBK : B ≤ K)
    (hBn : (B.subgroupOf K).Normal) (hT : IsPGroup 2 T)
    (hKBT : (K : Set H) ⊆ (B : Set H) * (T : Set H)) (ψ : H →* G')
    (hs : Group.IsSolvable ↥(B ⊓ ψ.ker)) : Group.IsSolvable (ψ.domRestrict K).ker := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set E := (ψ.domRestrict K).ker
  set f : E →* ↥K ⧸ B.subgroupOf K := (QuotientGroup.mk' (B.subgroupOf K)).comp E.subtype
  have hQ2 : IsPGroup 2 (↥K ⧸ B.subgroupOf K) := by
    intro q
    obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective (B.subgroupOf K) q
    obtain ⟨b, hb, t, ht, hbt⟩ := hKBT k.2
    have hbt' : b * t = (k : H) := hbt
    have htK : t ∈ K := by
      have h1 : t = b⁻¹ * k := by rw [← hbt', inv_mul_cancel_left]
      rw [h1]
      exact mul_mem (inv_mem (hBK hb)) k.2
    obtain ⟨n, hn⟩ := hT ⟨t, ht⟩
    refine ⟨n, ?_⟩
    have hk : k = ⟨b, hBK hb⟩ * ⟨t, htK⟩ := Subtype.ext hbt'.symm
    have hb1 : QuotientGroup.mk' (B.subgroupOf K) ⟨b, hBK hb⟩ = 1 :=
      (QuotientGroup.eq_one_iff _).mpr hb
    have htn : (⟨t, htK⟩ : K) ^ 2 ^ n = 1 :=
      Subtype.ext (by rw [Subgroup.coe_pow]; exact congrArg Subtype.val hn)
    rw [hk, map_mul, hb1, one_mul, ← map_pow, htn, map_one]
  have : Group.IsSolvable (↥K ⧸ B.subgroupOf K) := by
    have : Group.IsNilpotent (↥K ⧸ B.subgroupOf K) := hQ2.isNilpotent
    infer_instance
  have : Group.IsSolvable f.ker := by
    refine Group.isSolvable_of_isSolvable_injective
      (f := ((K.subtype.comp E.subtype).comp f.ker.subtype).codRestrict (B ⊓ ψ.ker)
        fun x => by
          have h1 : ((x : E) : K) ∈ B.subgroupOf K := (QuotientGroup.eq_one_iff _).mp x.2
          exact Subgroup.mem_inf.mpr ⟨h1, (x : E).2⟩) fun x y hxy => ?_
    have h := congrArg Subtype.val hxy
    exact Subtype.ext (Subtype.ext (Subtype.ext h))
  exact Group.isSolvable_of_ker_le_range f.ker.subtype f (by rw [Subgroup.range_subtype])

omit [Finite H] in
theorem eq_commutator_of_map_eq {G' : Type*} [Group G'] {A Y : Subgroup H} (hA : ⁅A, A⁆ = A)
    (hYA : Y ≤ A) (ψ : H →* G') (hψ : Y.map ψ = A.map ψ)
    (hperf : ⁅Y.map ψ, Y.map ψ⁆ = Y.map ψ) (hs : Group.IsSolvable ↥(A ⊓ ψ.ker)) :
    A = ⁅A, Y⁆ := by
  have hDA : ⁅A, Y⁆ ≤ A := (Subgroup.commutator_mono le_rfl hYA).trans hA.le
  have hDn : ((⁅A, Y⁆ : Subgroup H).subgroupOf A).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hDA).mpr
      (le_sup_left.trans (A3.sup_le_normalizer_commutator A Y))
  have hψD : (⁅A, Y⁆ : Subgroup H).map ψ = A.map ψ := by
    rw [Subgroup.map_commutator, ← hψ, hperf]
  have hAeq : A = ⁅A, Y⁆ ⊔ (A ⊓ ψ.ker) := by
    refine le_antisymm (fun a ha => ?_) (sup_le hDA inf_le_left)
    obtain ⟨d, hd, hda⟩ : ψ a ∈ (⁅A, Y⁆ : Subgroup H).map ψ := by
      rw [hψD]
      exact Subgroup.mem_map_of_mem ψ ha
    have hrest : d⁻¹ * a ∈ A ⊓ ψ.ker :=
      Subgroup.mem_inf.mpr ⟨mul_mem (inv_mem (hDA hd)) ha, by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hda, inv_mul_cancel]⟩
    have h := Subgroup.mul_mem_sup hd hrest
    rwa [mul_inv_cancel_left] at h
  have h := perfectCore_le_of_sup_solvable hDA hDn hAeq hs
  rw [perfectCore_eq_self_of_perfect hA] at h
  exact le_antisymm h hDA

theorem quasithinIsLocal_of_mem_cComp_normalizer {A C : Subgroup H} (T : Sylow 2 H)
    (hAK : A ∈ cComp (normalizer (C : Set H))) (hTK : (T : Subgroup H) ≤ normalizer (C : Set H))
    (hCT : C ≤ T) (hC1 : C ≠ ⊥) : CFSG.Open.quasithinIsLocal (T : Subgroup H) A := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hATK : A ⊔ (T : Subgroup H) ≤ normalizer (C : Set H) := sup_le (le_of_mem_cComp hAK) hTK
  refine ⟨T.isPGroup', cComp_mem_of_le hAK le_sup_left hATK, fun h2 => ?_, fun hbot => ?_⟩
  · exact T.not_dvd_index (h2.trans (Subgroup.relIndex_dvd_index_of_le le_sup_right))
  · apply hC1
    have hC := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      (hCT.trans le_sup_right) hATK (T.isPGroup'.to_le hCT)
    rw [hbot] at hC
    exact le_bot_iff.mp hC

theorem characteristic_normalizer_perfect_residuals_are_original_nonquasisimple_local_Ccomponents
    {L : Subgroup H} [L.Normal] (hL : L ∈ cComp L) (T : Sylow 2 H)
    (hLT : L ⊔ (T : Subgroup H) = ⊤) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    {X : Subgroup H} [X.Normal] (hXL : X ≤ L)
    (hX2 : ∀ (N : Subgroup X) [N.Normal], IsPGroup 2 (X ⧸ N) → N = ⊤)
    (hP : IsPGroup p (X ⧸ CFSG.pCore 2 X))
    (hW : Nat.card ((X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X)) = p ^ 2)
    (hirr : ∀ U : Subgroup ((X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X)),
      (∀ l ∈ L, ∀ u ∈ U, frattiniQuotConj X l u ∈ U) → U = ⊥ ∨ U = ⊤)
    (hnt : ∃ l ∈ L, ∃ w, frattiniQuotConj X l w ≠ w) :
    let R := (CFSG.pCore 2 (X ⊔ (T : Subgroup H) : Subgroup H)).map
      (X ⊔ (T : Subgroup H)).subtype
    let Y := (CFSG.perfectResidual ↥(L ⊓ normalizer (R : Set H))).map
      (L ⊓ normalizer (R : Set H)).subtype
    ∀ C : Subgroup H, C ≤ R → (C.subgroupOf R).Characteristic → C ≠ ⊥ →
      let K := normalizer (C : Set H)
      let B := L ⊓ K
      let A := (CFSG.perfectResidual ↥B).map B.subtype
      K = B ⊔ (T : Subgroup H) ∧ (K : Set H) = (B : Set H) * (T : Set H) ∧
        (B.subgroupOf K).Normal ∧ (A.subgroupOf B).Characteristic ∧ (A.subgroupOf K).Normal ∧
        ⁅X, Y⁆ = X ∧ X ≤ Y ∧ Y ≤ A ∧
        Group.IsSolvable ((frattiniQuotConj X).domRestrict K).ker ∧
        CFSG.IsQuasisimple (L.map (frattiniQuotConj X)) ∧
        ((L.map (frattiniQuotConj X)).subgroupOf (K.map (frattiniQuotConj X))).Normal ∧
        A.map (frattiniQuotConj X) = B.map (frattiniQuotConj X) ∧
        B.map (frattiniQuotConj X) = Y.map (frattiniQuotConj X) ∧
        Y.map (frattiniQuotConj X) = L.map (frattiniQuotConj X) ∧
        A ∈ cComp K ∧ ¬ CFSG.IsQuasisimple (A ⧸ CFSG.pCore 2 A) ∧
        CFSG.Open.quasithinIsLocal (T : Subgroup H) A ∧ A = ⁅A, Y⁆ := by
  intro R Y C hCR hCchar hC1 K B A
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  have hLperf : Group.IsPerfect L := Subgroup.isPerfect_iff.mpr (perfect_of_mem_cComp hL)
  have hWne : frattini (X ⧸ CFSG.pCore 2 X) ≠ ⊤ := by
    intro htop
    have h1 : Nat.card ((X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X)) = 1 := by
      rw [← Subgroup.index_eq_card, htop, Subgroup.index_top]
    rw [h1] at hW
    have : 1 < p ^ 2 := Nat.one_lt_pow two_ne_zero hp.one_lt
    omega
  obtain ⟨-, hRS, -, -, hNR, -, hYperf, hYNR, -, -, -, hYψ, hXY, hXleY, hYA, -, -⟩ :=
    CFSG.Quasithin.SteinbergCC.sylow_core_normalizer_perfect_residual_retains_original_prime_witness
      hLperf T hLT hp hp2 hXL hX2 hP hWne hirr hnt
  have hRT : R ≤ T := by
    have h : R = (T : Subgroup H) ⊓ (coreQuotConj X).ker := hRS
    rw [h]
    exact inf_le_left
  have hTNR : (T : Subgroup H) ≤ normalizer (R : Set H) := by
    have h : normalizer (R : Set H) = (L ⊓ normalizer (R : Set H)) ⊔ (T : Subgroup H) := hNR
    rw [h]
    exact le_sup_right
  have hYNR' : Y ≤ normalizer (R : Set H) := hYNR
  have hYA' : Y ≤ L ⊓ normalizer (R : Set H) := hYA
  have hYψ' : Y.map (frattiniQuotConj X) = L.map (frattiniQuotConj X) := hYψ
  have hXY' : ⁅X, Y⁆ = X := hXY
  have hXleY' : X ≤ Y := hXleY
  have hYperf' : ⁅Y, Y⁆ = Y := Subgroup.isPerfect_iff.mp hYperf
  have hTK : (T : Subgroup H) ≤ K :=
    CFSG.Quasithin.SteinbergCC.le_normalizer_of_characteristic hCR hTNR
  have hYK : Y ≤ K := CFSG.Quasithin.SteinbergCC.le_normalizer_of_characteristic hCR hYNR'
  have hYL : Y ≤ L := hYA'.trans inf_le_left
  have hBK : B ≤ K := inf_le_right
  have hBL : B ≤ L := inf_le_left
  have hYB : Y ≤ B := le_inf hYL hYK
  have hKBT : (K : Set H) = (B : Set H) * (T : Set H) := by
    ext k
    constructor
    · intro hk
      have hk' : k ∈ ((L ⊔ (T : Subgroup H) : Subgroup H) : Set H) := by
        rw [hLT]
        exact Subgroup.mem_top k
      rw [Subgroup.normal_mul] at hk'
      obtain ⟨l, hl, t, ht, hlt⟩ := hk'
      have hlt' : l * t = k := hlt
      refine ⟨l, ?_, t, ht, hlt'⟩
      show l ∈ L ⊓ K
      refine Subgroup.mem_inf.mpr ⟨hl, ?_⟩
      have hl' : l = k * t⁻¹ := by rw [← hlt', mul_inv_cancel_right]
      rw [hl']
      exact mul_mem hk (inv_mem (hTK ht))
    · rintro ⟨b, hb, t, ht, rfl⟩
      exact mul_mem (hBK hb) (hTK ht)
  have hKsup : K = B ⊔ (T : Subgroup H) := by
    refine le_antisymm (fun k hk => ?_) (sup_le hBK hTK)
    have hk' : k ∈ (B : Set H) * (T : Set H) := by
      rw [← hKBT]
      exact hk
    obtain ⟨b, hb, t, ht, hbt⟩ := hk'
    have hbt' : b * t = k := hbt
    rw [← hbt']
    exact Subgroup.mul_mem_sup hb ht
  have hKNB : K ≤ normalizer (B : Set H) := fun k hk =>
    Subgroup.inf_normalizer_le_normalizer_inf
      ⟨by rw [Subgroup.normalizer_eq_top]; exact Subgroup.mem_top k, Subgroup.le_normalizer hk⟩
  have hBn : (B.subgroupOf K).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hBK).mpr hKNB
  have hAcore : A = perfectCore B := (perfectCore_eq_map_perfectResidual B).symm
  have hAB : A ≤ B := by
    rw [hAcore]
    exact perfectCore_le B
  have hAperf : ⁅A, A⁆ = A := by
    rw [hAcore]
    exact perfectCore_perfect B
  have hAchar : (A.subgroupOf B).Characteristic := by
    have h : A.subgroupOf B = CFSG.perfectResidual ↥B :=
      Subgroup.comap_map_eq_self_of_injective B.subtype_injective _
    rw [h]
    infer_instance
  have hKNA : K ≤ normalizer (A : Set H) := by
    rw [hAcore]
    exact hKNB.trans (normalizer_le_normalizer_perfectCore B)
  have hAK : A ≤ K := hAB.trans hBK
  have hAL : A ≤ L := hAB.trans hBL
  have hAn : (A.subgroupOf K).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hAK).mpr hKNA
  have hYleA : Y ≤ A := by
    rw [hAcore]
    exact le_perfectCore_of_perfect hYB hYperf'
  set ψ := frattiniQuotConj X with hψ
  have hψBY : B.map ψ = Y.map ψ :=
    le_antisymm (by rw [hYψ']; exact Subgroup.map_mono hBL) (Subgroup.map_mono hYB)
  have hψAB : A.map ψ = B.map ψ :=
    le_antisymm (Subgroup.map_mono hAB) (by rw [hψBY]; exact Subgroup.map_mono hYleA)
  have hJne : L.map ψ ≠ ⊥ := by
    obtain ⟨l, hl, w, hw⟩ := hnt
    intro hbot
    have h1 : ψ l ∈ L.map ψ := Subgroup.mem_map_of_mem ψ hl
    rw [hbot, Subgroup.mem_bot] at h1
    exact hw (by rw [h1]; rfl)
  obtain ⟨-, hWc, hWpow, -, -⟩ := CFSG.GroupTheory.frattini_elementary_quotient hP
  have : Group.IsPerfect (L.map ψ) := Group.IsPerfect.map ψ
  have hJq : CFSG.IsQuasisimple (L.map ψ) :=
    isQuasisimple_of_le_mulAut_plane hp2 (fun a b => hWc.is_comm.comm a b) hWpow hW (L.map ψ)
      hJne
  have hJK : L.map ψ ≤ K.map ψ := by
    rw [← hYψ', ← hψBY]
    exact Subgroup.map_mono hBK
  have hJn : ((L.map ψ).subgroupOf (K.map ψ)).Normal := by
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer hJK).mpr ?_
    have hLN : K ≤ normalizer (L : Set H) := by
      rw [Subgroup.normalizer_eq_top]
      exact le_top
    exact (Subgroup.map_mono hLN).trans (Subgroup.le_normalizer_map ψ)
  have hUs : Group.IsSolvable ↥(L ⊓ ψ.ker) := isSolvable_inf_ker_of_mem_cComp hL ψ hJne
  have hBs : Group.IsSolvable ↥(B ⊓ ψ.ker) :=
    Group.isSolvable_of_isSolvable_injective
      (f := Subgroup.inclusion (inf_le_inf_right ψ.ker hBL)) (Subgroup.inclusion_injective _)
  have hAs : Group.IsSolvable ↥(A ⊓ ψ.ker) :=
    Group.isSolvable_of_isSolvable_injective
      (f := Subgroup.inclusion (inf_le_inf_right ψ.ker hAL)) (Subgroup.inclusion_injective _)
  have hEs : Group.IsSolvable (ψ.domRestrict K).ker :=
    isSolvable_ker_restrict hBK hBn T.isPGroup' hKBT.le ψ hBs
  have : Finite (MulAut ((X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X))) :=
    Finite.of_injective (fun e => (e : _ → _)) fun a b h => MulEquiv.ext (congrFun h)
  have hAq : CFSG.IsQuasisimple ↥(A.map ψ) := by
    rw [hψAB, hψBY, hYψ']
    exact hJq
  have hAself : A ∈ cComp A := mem_cComp_self_of_isQuasisimple_map hAperf ψ hAq hAs
  have hAcK : A ∈ cComp K := cComp_mem_of_subnormal (A3.subnormal_of_normal hAK hAn) hAself
  have hXs : Group.IsSolvable X := by
    have : Group.IsSolvable (X ⧸ CFSG.pCore 2 X) := by
      have : Group.IsNilpotent (X ⧸ CFSG.pCore 2 X) := hP.isNilpotent
      infer_instance
    have : Group.IsSolvable (CFSG.pCore 2 X) := by
      have : Group.IsNilpotent (CFSG.pCore 2 X) :=
        (CFSG.pCore_isPGroup (p := 2) (G := X)).isNilpotent
      infer_instance
    exact Group.isSolvable_of_ker_le_range (CFSG.pCore 2 X).subtype
      (QuotientGroup.mk' (CFSG.pCore 2 X)) (by rw [QuotientGroup.ker_mk', Subgroup.range_subtype])
  have hX2' : ¬ IsPGroup 2 X := by
    intro h2
    have htop : CFSG.pCore 2 X = ⊤ :=
      eq_top_iff.mpr (le_sSup ⟨inferInstance, h2.of_equiv Subgroup.topEquiv.symm⟩)
    have hsub : Subsingleton ((X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X)) := by
      refine ⟨fun a b => ?_⟩
      obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
      obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
      obtain ⟨a'', rfl⟩ := QuotientGroup.mk_surjective a'
      obtain ⟨b'', rfl⟩ := QuotientGroup.mk_surjective b'
      have ha : ((a'' : X ⧸ CFSG.pCore 2 X)) = 1 :=
        (QuotientGroup.eq_one_iff a'').mpr (by rw [htop]; exact Subgroup.mem_top _)
      have hb : ((b'' : X ⧸ CFSG.pCore 2 X)) = 1 :=
        (QuotientGroup.eq_one_iff b'').mpr (by rw [htop]; exact Subgroup.mem_top _)
      rw [ha, hb]
    have h1 : Nat.card ((X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X)) = 1 :=
      Nat.card_eq_one_iff_unique.mpr ⟨hsub, ⟨1⟩⟩
    rw [h1] at hW
    have : 1 < p ^ 2 := Nat.one_lt_pow two_ne_zero hp.one_lt
    omega
  have hnq : ¬ CFSG.IsQuasisimple (A ⧸ CFSG.pCore 2 A) :=
    not_isQuasisimple_pCore_quotient_of_commutator (hXleY'.trans hYleA) inferInstance hXs hYleA
      hXY' hX2'
  have hlocal : CFSG.Open.quasithinIsLocal (T : Subgroup H) A :=
    quasithinIsLocal_of_mem_cComp_normalizer T hAcK hTK (hCR.trans hRT) hC1
  have hAY : A = ⁅A, Y⁆ := by
    refine eq_commutator_of_map_eq hAperf hYleA ψ (hψAB.trans hψBY).symm ?_ hAs
    rw [← Subgroup.map_commutator, hYperf']
  exact ⟨hKsup, hKBT, hBn, hAchar, hAn, hXY', hXleY', hYleA, hEs, hJq, hJn, hψAB, hψBY, hYψ',
    hAcK, hnq, hlocal, hAY⟩

end CFSG.Quasithin.H13.NQTerm
