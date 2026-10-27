module

public import CFSG.Quasithin.MS93.ASC134
public import CFSG.Quasithin.MS93.ASC134NCLin
public import CFSG.Quasithin.MS93.ASC134Ord

public section

namespace CFSG.Quasithin.MS93

open CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.Open hiding StatedSL StatedSp
open CFSG.Assembly.LowTwoRank (StatedSL StatedSp specialLinearGroupEquivStatedSL
  specialLinearGroupEquivStatedSL_coe)
open scoped Pointwise
open Matrix

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem exists_standard_natural {L W T : Subgroup G} {F : Type} [Field F] [Fintype F] {n : ℕ}
    (hF : Fintype.card F = 2 ^ n) {α : ↥L →* ↥(StatedSL 3 F)} (hα : Function.Surjective α)
    (hW : IsSumOfNaturalModulesVia L W ⊥ α false 1) (hT : IsSylowTwoOf T L) :
    ∃ (α₁ : ↥L →* SL3 F) (b : ↥W → Fin 3 → F), Function.Surjective α₁ ∧ α₁.ker = α.ker ∧
      (T.subgroupOf L).map α₁ = sStar ∧ Function.Bijective b ∧
      ∀ (ℓ : ↥L) (u v : ↥W), (v : G) = ℓ * u * ℓ⁻¹ →
        b v = ((α₁ ℓ : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ b u := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hF' : Nat.card F = 2 ^ n := by rw [Nat.card_eq_fintype_card, hF]
  set e := specialLinearGroupEquivStatedSL 3 F with he
  set α₀ : ↥L →* SL3 F := e.symm.toMonoidHom.comp α with hα₀
  have hα₀s : Function.Surjective α₀ := e.symm.surjective.comp hα
  have hα₀ker : α₀.ker = α.ker := MonoidHom.ker_comp_of_injective α _ e.symm.injective
  have hcoe : ∀ ℓ : ↥L, (((α ℓ : StatedSL 3 F) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      ((α₀ ℓ : SL3 F) : Matrix (Fin 3) (Fin 3) F) := fun ℓ => by
    rw [← specialLinearGroupEquivStatedSL_coe 3 F (α₀ ℓ)]
    simp [hα₀, he]
  have hT2 : IsPGroup 2 ↥(T.subgroupOf L) :=
    hT.2.1.comap_of_injective L.subtype L.subtype_injective
  obtain ⟨γ, hγ⟩ := exists_map_conj_eq_sStar hF' (hT2.map α₀)
    (fun h2 => hT.2.2 (h2.trans (Subgroup.index_map_dvd _ hα₀s)))
  set α₁ : ↥L →* SL3 F := (MulAut.conj γ).toMonoidHom.comp α₀ with hα₁
  obtain ⟨-, -, β, hβs, hβk, hβeq⟩ := hW
  have hβinj : Function.Injective β := by
    rw [← MonoidHom.ker_eq_bot_iff, hβk, Subgroup.bot_subgroupOf]
  set b : ↥W → Fin 3 → F := fun w => ((γ : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ
    Multiplicative.toAdd (β w) 0 with hb
  refine ⟨α₁, b, (MulAut.conj γ).surjective.comp hα₀s, ?_, ?_, ⟨?_, ?_⟩, ?_⟩
  · rw [hα₁, MonoidHom.ker_comp_of_injective _ _ (MulAut.conj γ).injective, hα₀ker]
  · rw [hα₁, ← Subgroup.map_map, hγ]
  · intro u v huv
    apply hβinj
    apply Multiplicative.toAdd.injective
    funext i
    rw [Subsingleton.elim i 0]
    have := congrArg (fun x => ((γ⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ x) huv
    simp only [hb, ← sl3_mulVec_mul, inv_mul_cancel, sl3_one_mulVec] at this
    exact this
  · intro v
    obtain ⟨u, hu⟩ := hβs (Multiplicative.ofAdd fun _ => ((γ⁻¹ : SL3 F) :
      Matrix (Fin 3) (Fin 3) F) *ᵥ v)
    refine ⟨u, ?_⟩
    simp only [hb, hu, toAdd_ofAdd]
    rw [← sl3_mulVec_mul, mul_inv_cancel, sl3_one_mulVec]
  · intro ℓ u v huv
    have := hβeq ℓ u v huv 0
    simp only [moduleAct, Bool.false_eq_true, ↓reduceIte] at this
    have hcomm : γ * α₀ ℓ = α₁ ℓ * γ := by
      simp only [hα₁, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    simp only [hb, this, hcoe]
    rw [← sl3_mulVec_mul, hcomm, sl3_mulVec_mul]

theorem notCentralizerCore_of_natural {G₀ R L W : Subgroup G} (h : PUHyp G₀ R L)
    {F : Type} [Field F] [Fintype F] {n : ℕ} (hF : Fintype.card F = 2 ^ n)
    {α : ↥L →* ↥(StatedSL 3 F)} (hα : Function.Surjective α) (hker : α.ker = CFSG.pCore 2 ↥L)
    (hW : IsSumOfNaturalModulesVia L W ⊥ α false 1)
    (hdec : ∀ x ∈ Xq G₀, ∃ c ∈ Subgroup.centralizer (L : Set G), ∃ w ∈ W, x = c * w)
    (hQj : ∀ T : Subgroup G, IsSylowTwoOf T L → R ≤ Subgroup.normalizer (T : Set G) →
      ∃ X : Subgroup G, IsParRadOver L T X ∧
        (W ⊓ Subgroup.centralizer (X : Set G)).relIndex W ≤ 2 ^ n ∧
        ¬ W ≤ Subgroup.centralizer (X : Set G) ∧ X ≤ R) :
    C134NotCentralizerCore G₀ R := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP F 2 := charP_two_of_card_eq hF
  have hF' : Nat.card F = 2 ^ n := by rw [Nat.card_eq_fintype_card, hF]
  have hn : 1 ≤ n := one_le_of_card_eq_two_pow hF
  have hq : 2 ≤ Nat.card F := by
    rw [hF']
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hLW : L ≤ Subgroup.normalizer (W : Set G) := hW.1
  intro S hS hRS hRO
  set C := G₀ ⊓ Subgroup.centralizer (omegaOneCenterOf S : Set G) with hCdef
  have hLn : (L.subgroupOf G₀).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.L_le).2 h.le_normalizer
  have hSL : IsSylowTwoOf (S ⊓ L) L :=
    RankOneRecog.isSylowTwoOf_inf_of_subnormal hS h.L_le hLn.isSubnormal
  have hRN : R ≤ Subgroup.normalizer ((S ⊓ L : Subgroup G) : Set G) :=
    hRS.trans (le_normalizer_inf Subgroup.le_normalizer (hS.1.trans h.le_normalizer))
  obtain ⟨X, ⟨P, hP, hSLP, rfl⟩, hidx, hnc, hXR⟩ := hQj (S ⊓ L) hSL hRN
  obtain ⟨α₁, b, hα₁, hker₁, hα₁S, hb, hbeq⟩ := exists_standard_natural hF hα hW hSL
  have hPL : P ≤ L := hP.1.1
  have hXL : pCoreOf 2 P ≤ L := (pCoreOf_le' P).trans hPL
  set A : Subgroup (SL3 F) := ((pCoreOf 2 P).subgroupOf L).map α₁ with hA
  have hinvP : ∀ t : ↥L, (t : G) ∈ P → ∀ v ∈ fixN A,
      ((α₁ t : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v ∈ fixN A := by
    intro t ht v hv g hg
    obtain ⟨x', hx', rfl⟩ := hg
    have hconj : t⁻¹ * x' * t ∈ (pCoreOf 2 P).subgroupOf L := by
      rw [Subgroup.mem_subgroupOf]
      have := (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf P (P.inv_mem ht))
        (x' : G)).mp hx'
      simpa using this
    have hfix := hv _ ⟨_, hconj, rfl⟩
    have e : α₁ x' * α₁ t = α₁ t * α₁ (t⁻¹ * x' * t) := by
      rw [map_mul, map_mul, map_inv]
      group
    rw [← sl3_mulVec_mul, e, sl3_mulVec_mul, hfix]
  have hinvS : ∀ g ∈ (sStar : Subgroup (SL3 F)), ∀ v ∈ fixN A,
      ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v ∈ fixN A := by
    intro g hg v hv
    rw [← hα₁S] at hg
    obtain ⟨t, ht, rfl⟩ := hg
    exact hinvP t (hSLP (Subgroup.mem_subgroupOf.mp ht)) v hv
  have hcen : ∀ w : ↥W,
      (w : G) ∈ Subgroup.centralizer (pCoreOf 2 P : Set G) ↔ b w ∈ fixN A := by
    intro w
    constructor
    · intro hw g hg
      obtain ⟨x', hx', rfl⟩ := hg
      have hcomm : (x' : G) * w = w * x' := Subgroup.mem_centralizer_iff.mp hw x' hx'
      exact (hbeq x' w w (by rw [hcomm, Subgroup.coe_inv, mul_inv_cancel_right])).symm
    · intro hbw
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have hv : x * (w : G) * x⁻¹ ∈ W :=
        (Subgroup.mem_normalizer_iff.mp (hLW (hXL hx)) w).mp w.2
      have e1 := hbeq ⟨x, hXL hx⟩ w ⟨_, hv⟩ rfl
      have e2 := hbw (α₁ ⟨x, hXL hx⟩) ⟨⟨x, hXL hx⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
      have heq : (⟨_, hv⟩ : ↥W) = w := hb.1 (e1.trans e2)
      have hxw : x * (w : G) * x⁻¹ = w := congrArg Subtype.val heq
      calc x * (w : G) = x * w * x⁻¹ * x := by group
        _ = w * x := by rw [hxw]
  have hcardW : Nat.card ↥W = Nat.card F ^ 3 := by
    rw [Nat.card_congr (Equiv.ofBijective b hb), Nat.card_fun,
      Nat.card_eq_fintype_card (α := Fin 3), Fintype.card_fin]
  have hcardC : Nat.card ↥(Subgroup.centralizer (pCoreOf 2 P : Set G) ⊓ W) =
      Nat.card ↥(fixN A) := by
    refine Nat.card_congr (Equiv.ofBijective (fun z => ⟨b ⟨z, (Subgroup.mem_inf.mp z.2).2⟩,
      (hcen _).mp (Subgroup.mem_inf.mp z.2).1⟩) ⟨fun z₁ z₂ hz => ?_, fun v => ?_⟩)
    · have := hb.1 (congrArg Subtype.val hz)
      exact Subtype.ext (congrArg (fun y : ↥W => (y : G)) this)
    · obtain ⟨w, hw⟩ := hb.2 v
      refine ⟨⟨w, Subgroup.mem_inf.mpr ⟨(hcen w).mpr (hw ▸ v.2), w.2⟩⟩, ?_⟩
      exact Subtype.ext hw
  have hrel := Subgroup.relIndex_mul_card (Subgroup.centralizer (pCoreOf 2 P : Set G)) W
  rw [hcardC, hcardW] at hrel
  rw [Subgroup.inf_relIndex_left] at hidx
  have hq1 : Nat.card F < Nat.card F ^ 2 := by
    calc Nat.card F = Nat.card F ^ 1 := (pow_one _).symm
      _ < Nat.card F ^ 2 := Nat.pow_lt_pow_right (by omega) (by norm_num)
  have hq2 : Nat.card F ^ 2 < Nat.card F ^ 3 := Nat.pow_lt_pow_right (by omega) (by norm_num)
  have hln : fixN A = ln01 := by
    rcases sStar_invariant_cases (fixN A) hinvS with h0 | h0 | h0 | h0
    · exfalso
      have h1 : Nat.card ↥(⊥ : Submodule F (Fin 3 → F)) = 1 := Nat.card_unique
      rw [h0, h1, mul_one] at hrel
      omega
    · exfalso
      rw [h0, card_pt0] at hrel
      have h3 : Nat.card F ^ 3 = Nat.card F ^ 2 * Nat.card F := by ring
      rw [h3] at hrel
      have h4 := Nat.eq_of_mul_eq_mul_right (by omega : 0 < Nat.card F) hrel
      omega
    · exact h0
    · exfalso
      apply hnc
      intro w hw
      exact (hcen ⟨w, hw⟩).mpr (h0 ▸ Submodule.mem_top)
  have hPstab : ∀ t : ↥L, (t : G) ∈ P → α₁ t ∈ lnStab := fun t ht =>
    mem_lnStab_iff.mpr fun v hv => by
      rw [← hln] at hv ⊢
      exact hinvP t ht v hv
  set P₂ : Subgroup G := ((lnStab : Subgroup (SL3 F)).comap α₁).map L.subtype with hP₂
  have hPP₂ : P ≤ P₂ := fun p hp => ⟨⟨p, hPL hp⟩, hPstab ⟨p, hPL hp⟩ hp, rfl⟩
  obtain ⟨ℓ₀, hℓ₀⟩ := hα₁ (rootElt 2 1 1)
  have hP₂ne : P₂ ≠ L := by
    intro heq
    have hmem : (ℓ₀ : G) ∈ P₂ := by rw [heq]; exact ℓ₀.2
    obtain ⟨ℓ', hℓ', hℓ'eq⟩ := Subgroup.mem_map.mp hmem
    have h1 : ℓ' = ℓ₀ := Subtype.ext hℓ'eq
    have h2 : α₁ ℓ' ∈ lnStab := hℓ'
    rw [h1, hℓ₀] at h2
    exact rootElt_two_one_not_mem_lnStab h2
  have hP₂par : IsParabolic2 L P₂ := by
    obtain ⟨-, S', hS', hNS'⟩ := hP.1
    exact ⟨Subgroup.map_subtype_le _, S', hS', hNS'.trans hPP₂⟩
  have hP₂eq : P₂ = P := hP.2.2 P₂ hP₂par hP₂ne hPP₂
  set K : Subgroup G := ((qLn : Subgroup (SL3 F)).comap α₁).map L.subtype with hK
  have hKP₂ : K ≤ P₂ := Subgroup.map_mono (Subgroup.comap_mono qLn_le_lnStab)
  have hKn : (K.subgroupOf P₂).Normal := by
    refine ⟨fun k hk p => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hk ⊢
    obtain ⟨k', hk', hk'eq⟩ := hk
    obtain ⟨p', hp', hp'eq⟩ := p.2
    refine ⟨p' * k' * p'⁻¹, ?_, ?_⟩
    · show α₁ (p' * k' * p'⁻¹) ∈ (qLn : Subgroup (SL3 F))
      rw [map_mul, map_mul, map_inv]
      exact conj_mem_qLn hp' hk'
    · simp only [map_mul, map_inv, hk'eq, hp'eq, Subgroup.coe_mul, Subgroup.coe_inv]
  have hK2 : IsPGroup 2 ↥K := by
    have h1 : IsPGroup 2 ↥α₁.ker := by
      rw [hker₁, hker]
      exact isPGroup_cfsgPCore ↥L
    exact ((isPGroup_qLn hF').comap_of_ker_isPGroup α₁ h1).map L.subtype
  have hKX : K ≤ pCoreOf 2 P := by
    rw [← hP₂eq]
    exact CFSG.LieType.BorelTits.le_pCoreOf 2 hKP₂ hKn hK2
  obtain ⟨x₀, hx₀⟩ := hα₁ (rootElt 1 2 1)
  have hx₀K : (x₀ : G) ∈ K :=
    ⟨x₀, show α₁ x₀ ∈ (qLn : Subgroup (SL3 F)) by rw [hx₀]; exact rootElt_one_two_mem_qLn 1,
      rfl⟩
  have hx₀O : (x₀ : G) ∈ pCoreOf 2 C := hRO ▸ hXR (hKX hx₀K)
  have hℓ₀C : (ℓ₀ : G) ∈ C := by
    refine Subgroup.mem_inf.mpr ⟨h.L_le ℓ₀.2, ?_⟩
    have hQS : pCoreOf 2 G₀ ≤ S := h.pCore_le.trans hRS
    unfold omegaOneCenterOf omegaOneOf
    rw [Subgroup.centralizer_closure, Subgroup.mem_centralizer_iff]
    rintro x ⟨⟨hxS, hxC⟩, hx2⟩
    have hxCQ : x ∈ Subgroup.centralizer (pCoreOf 2 G₀ : Set G) :=
      Subgroup.centralizer_le hQS hxC
    have hxQ : x ∈ pCoreOf 2 G₀ := h.charTwo ⟨hS.1 hxS, hxCQ⟩
    have hxX : x ∈ Xq G₀ := Subgroup.subset_closure ⟨⟨hxQ, hxCQ⟩, hx2⟩
    obtain ⟨c, hc, w, hw, rfl⟩ := hdec x hxX
    have hwS : ∀ t : ↥L, t ∈ (S ⊓ L).subgroupOf L → (w : G) = t * w * t⁻¹ := by
      intro t ht
      have htS : (t : G) ∈ S := (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp ht)).1
      have h1 : (t : G) * (c * w) = c * w * t := Subgroup.mem_centralizer_iff.mp hxC t htS
      have h2 : (t : G) * c = c * t := Subgroup.mem_centralizer_iff.mp hc t t.2
      have h3 : (t : G) * w = w * t := by
        have e : c * ((t : G) * w) = c * (w * t) := by
          rw [← mul_assoc, ← h2, mul_assoc, h1, mul_assoc]
        exact mul_left_cancel e
      have h4 : (w : G) = t * w * (t : G)⁻¹ := by rw [h3, mul_inv_cancel_right]
      exact h4
    have hbw : b ⟨w, hw⟩ ∈ (pt0 : Submodule F (Fin 3 → F)) := by
      rw [← fixN_sStar, ← hα₁S]
      rintro g ⟨t, ht, rfl⟩
      exact (hbeq t ⟨w, hw⟩ ⟨w, hw⟩ (hwS t ht)).symm
    have hℓw : (ℓ₀ : G) * w * (ℓ₀ : G)⁻¹ ∈ W :=
      (Subgroup.mem_normalizer_iff.mp (hLW ℓ₀.2) w).mp hw
    have hfixw : (ℓ₀ : G) * w * (ℓ₀ : G)⁻¹ = w := by
      have e := hbeq ℓ₀ ⟨w, hw⟩ ⟨_, hℓw⟩ rfl
      rw [hℓ₀, rootElt_two_one_mulVec hbw] at e
      exact congrArg Subtype.val (hb.1 e)
    have hcℓ : (ℓ₀ : G) * c = c * ℓ₀ := Subgroup.mem_centralizer_iff.mp hc ℓ₀ ℓ₀.2
    have hℓw' : (ℓ₀ : G) * w = w * ℓ₀ := by
      calc (ℓ₀ : G) * w = (ℓ₀ : G) * w * (ℓ₀ : G)⁻¹ * ℓ₀ := by group
        _ = w * ℓ₀ := by rw [hfixw]
    calc c * w * ℓ₀ = c * (w * ℓ₀) := mul_assoc _ _ _
      _ = c * (ℓ₀ * w) := by rw [hℓw']
      _ = (c * ℓ₀) * w := (mul_assoc _ _ _).symm
      _ = (ℓ₀ * c) * w := by rw [hcℓ]
      _ = ℓ₀ * (c * w) := mul_assoc _ _ _
  have hconjO : (ℓ₀ : G) * x₀ * (ℓ₀ : G)⁻¹ ∈ pCoreOf 2 C :=
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf C hℓ₀C) x₀).mp hx₀O
  have hmO := (pCoreOf 2 C).mul_mem hx₀O hconjO
  obtain ⟨k, hk⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 C ⟨_, hmO⟩
  have hk' : (x₀ * (ℓ₀ * x₀ * ℓ₀⁻¹)) ^ 2 ^ k = 1 := by
    apply Subtype.ext
    have := congrArg Subtype.val hk
    simpa using this
  have hM := congrArg α₁ hk'
  rw [map_pow, map_one, map_mul, map_mul, map_mul, map_inv, hx₀, hℓ₀] at hM
  exact threeElt_ne_one (eq_one_of_pow_two_pow_of_pow_three hM threeElt_pow_three)

theorem Uq_le_centerOf_Vq {M T L : Subgroup G} (h : PUHyp M T L) :
    Uq M T L ≤ centerOf (Vq M L) := by
  show Uq M T L ≤ Vq M L ⊓ Subgroup.centralizer (Vq M L : Set G)
  refine le_inf (Subgroup.commutator_mono h.Z0q_le_pCoreOf le_rfl) fun u hu => ?_
  have huC : u ∈ Subgroup.centralizer (pCoreOf 2 M : Set G) :=
    A4.centerOf_le_centralizer _ (A4.omegaOneCenterOf_le_centerOf _ (h.Uq_le_Xq hu))
  exact Subgroup.centralizer_le (Vq_le_pCoreOf h.L_le) huC

theorem le_normalizer_centerOf_Vq {M T L : Subgroup G} (h : PUHyp M T L) :
    M ≤ Subgroup.normalizer (centerOf (Vq M L) : Set G) :=
  le_normalizer_inf (le_normalizer_Vq h.le_normalizer)
    (le_normalizer_centralizer (le_normalizer_Vq h.le_normalizer))

theorem c134NotCentralizer11_holds : C134NotCentralizer11 := by
  intro G _ _ G₀ R L hMS hL hG h hX h11
  obtain ⟨n, F, _, _, α, hF, hα, h1, h2, hQj⟩ := h11
  have hmod := isModO2Surj_of_case11_data h hα h1 h2
  have hn : 1 ≤ n := one_le_of_card_eq_two_pow hF
  have hZN : Zq G₀ L ≤ Subgroup.normalizer (centerOf (Vq G₀ L) : Set G) :=
    Zq_le.trans (le_normalizer_centerOf_Vq h)
  refine notCentralizerCore_of_natural h hF hα hmod.2 h1 (fun x hx => ?_) (fun T hT hRT => ?_)
  · have hxZ : x ∈ Zq G₀ L ⊔ centerOf (Vq G₀ L) :=
      sup_le_sup_left (Uq_le_centerOf_Vq h) _ (hX hx)
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hZN] at hxZ
    obtain ⟨c, hc, w, hw, rfl⟩ := hxZ
    exact ⟨c, (Subgroup.mem_inf.mp hc).2, w, hw, rfl⟩
  · obtain ⟨X, hXpar, hidx, hXR⟩ := hQj T hT hRT
    refine ⟨X, hXpar, hidx.le, fun hle => ?_, hXR⟩
    have h1' : (centerOf (Vq G₀ L) ⊓ Subgroup.centralizer (X : Set G)).relIndex
        (centerOf (Vq G₀ L)) = 1 := by
      rw [inf_eq_left.mpr hle, Subgroup.relIndex_self]
    rw [h1'] at hidx
    have : 2 ≤ 2 ^ n := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    omega

theorem c134NotCentralizer13_holds : C134NotCentralizer13 := by
  intro G _ _ G₀ R L hMS hL hG h hX h13
  obtain ⟨n, F, _, _, α, hF, hα, -, -, hZeq, -, hU, hΦ, hC, hVC, hQj⟩ := h13
  have hmod := isModO2Surj_of_case13_data h hα hZeq hU hΦ hC hVC
  have hn : 1 ≤ n := one_le_of_card_eq_two_pow hF
  have hGZ : G₀ ≤ Subgroup.normalizer (centerOf (Vq G₀ L) : Set G) := le_normalizer_centerOf_Vq h
  have hGW : G₀ ≤ Subgroup.normalizer ((⁅centerOf (Vq G₀ L), L⁆ : Subgroup G) : Set G) :=
    le_normalizer_commutator hGZ h.le_normalizer
  have hWZ : ⁅centerOf (Vq G₀ L), L⁆ ≤ centerOf (Vq G₀ L) :=
    commutator_le_left_of_le_normalizer (h.L_le.trans hGZ)
  refine notCentralizerCore_of_natural h hF hα hmod.2 hU (fun x hx => ?_) (fun T hT hRT => ?_)
  · have hxZ : x ∈ Zq G₀ L ⊔ centerOf (Vq G₀ L) :=
      sup_le_sup_left (Uq_le_centerOf_Vq h) _ (hX hx)
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ (Zq_le.trans hGZ)]
      at hxZ
    obtain ⟨c₁, hc₁, z, hz, rfl⟩ := hxZ
    have hz' : z ∈ (Vq G₀ L ⊓ Subgroup.centralizer (L : Set G)) ⊔ ⁅centerOf (Vq G₀ L), L⁆ :=
      hZeq ▸ hz
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _
      ((inf_le_left.trans (Vq_le h.L_le)).trans hGW)] at hz'
    obtain ⟨c₂, hc₂, u, hu, rfl⟩ := hz'
    exact ⟨c₁ * c₂, Subgroup.mul_mem _ (Subgroup.mem_inf.mp hc₁).2 (Subgroup.mem_inf.mp hc₂).2,
      u, hu, by group⟩
  · obtain ⟨X, hXpar, hidx, hXR⟩ := hQj T hT hRT
    obtain ⟨P, hP, -, hXP⟩ := id hXpar
    have hXL : X ≤ L := hXP ▸ (pCoreOf_le' P).trans hP.1.1
    refine ⟨X, hXpar, ?_, fun hle => ?_, hXR⟩
    · rw [Subgroup.inf_relIndex_left]
      have hne : (Subgroup.centralizer (X : Set G)).relIndex (centerOf (Vq G₀ L)) ≠ 0 := by
        rw [← Subgroup.inf_relIndex_left, hidx]
        positivity
      calc (Subgroup.centralizer (X : Set G)).relIndex ⁅centerOf (Vq G₀ L), L⁆
          ≤ (Subgroup.centralizer (X : Set G)).relIndex (centerOf (Vq G₀ L)) :=
            Subgroup.relIndex_le_of_le_right hWZ hne
        _ = 2 ^ n := by rw [← Subgroup.inf_relIndex_left, hidx]
    · have hZC : centerOf (Vq G₀ L) ≤ Subgroup.centralizer (X : Set G) := by
        rw [hZeq]
        exact sup_le (inf_le_right.trans (Subgroup.centralizer_le hXL)) hle
      have h1' : (centerOf (Vq G₀ L) ⊓ Subgroup.centralizer (X : Set G)).relIndex
          (centerOf (Vq G₀ L)) = 1 := by
        rw [inf_eq_left.mpr hZC, Subgroup.relIndex_self]
      rw [h1'] at hidx
      have : 2 ≤ 2 ^ n := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
      omega

end CFSG.Quasithin.MS93
