module

public import CFSG.Timmesfeld.Bridge.RootStructN0Cycle
public import CFSG.Timmesfeld.Bridge.RootSetsSyl
public import CFSG.Timmesfeld.Bridge.RootStructN0Torus

public section

namespace CFSG.Timmesfeld.Bridge

open CFSG.Timmesfeld CFSG.Glauberman.Dickson RootDegen

section SL2

variable {F : Type*} [Field F]

theorem conj_upperElt_one_apply_one_zero (A : Matrix.SpecialLinearGroup (Fin 2) F) :
    ((A * RankOne.upperElt F 1 * A⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F) 1 0 = -((A : Matrix (Fin 2) (Fin 2) F) 1 0) ^ 2 := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
  simp [RankOne.upperElt, Matrix.mul_apply, Fin.sum_univ_two]
  ring

theorem conj_lowerElt_one_apply_zero_one (A : Matrix.SpecialLinearGroup (Fin 2) F) :
    ((A * RankOne.lowerElt F 1 * A⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F) 0 1 = -((A : Matrix (Fin 2) (Fin 2) F) 0 1) ^ 2 := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
  simp [RankOne.lowerElt, Matrix.mul_apply, Fin.sum_univ_two]
  ring

theorem exists_eq_splitTorus_of_normalizes (A : Matrix.SpecialLinearGroup (Fin 2) F)
    (hU : A * RankOne.upperElt F 1 * A⁻¹ ∈ upperUnipotent F)
    (hL : A * RankOne.lowerElt F 1 * A⁻¹ ∈ lowerUnipotent F) :
    ∃ a : Fˣ, A = splitTorusSLHom F a := by
  obtain ⟨t, ht⟩ := (RankOne.mem_upperUnipotent_iff F).1 hU
  obtain ⟨s, hs⟩ := (RankOne.mem_lowerUnipotent_iff F).1 hL
  have hc : (A : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by
    have h1 := conj_upperElt_one_apply_one_zero A
    rw [ht] at h1
    simp [RankOne.upperElt] at h1
    exact h1
  have hb : (A : Matrix (Fin 2) (Fin 2) F) 0 1 = 0 := by
    have h1 := conj_lowerElt_one_apply_zero_one A
    rw [hs] at h1
    simp [RankOne.lowerElt] at h1
    exact h1
  have hdet := A.2
  rw [Matrix.det_fin_two, hb, hc, mul_zero, sub_zero] at hdet
  have ha : (A : Matrix (Fin 2) (Fin 2) F) 0 0 ≠ 0 := left_ne_zero_of_mul_eq_one hdet
  refine ⟨Units.mk0 _ ha, ?_⟩
  apply Subtype.ext
  rw [splitTorusSLHom_coe]
  ext i j
  fin_cases i <;> fin_cases j
  · rfl
  · simpa using hb
  · simpa using hc
  · simp only [Units.val_mk0]
    exact (eq_inv_of_mul_eq_one_right hdet)

theorem standardSplitWeylSL_conj_upperElt (t : F) :
    standardSplitWeylSL F * RankOne.upperElt F t * (standardSplitWeylSL F)⁻¹ =
      RankOne.lowerElt F (-t) := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, standardSplitWeylSL_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [RankOne.upperElt, RankOne.lowerElt, Matrix.mul_apply,
    Fin.sum_univ_two]

theorem standardSplitWeylSL_conj_lowerElt (t : F) :
    standardSplitWeylSL F * RankOne.lowerElt F t * (standardSplitWeylSL F)⁻¹ =
      RankOne.upperElt F (-t) := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, standardSplitWeylSL_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [RankOne.upperElt, RankOne.lowerElt, Matrix.mul_apply,
    Fin.sum_univ_two]

end SL2

variable {G : Type} [Group G] {D : Set G}

theorem conj_ne_one_of_ne_one {g z : G} (hz : z ≠ 1) : g * z * g⁻¹ ≠ 1 := by
  intro h'
  apply hz
  have := congrArg (fun w => g⁻¹ * w * g) h'
  simpa [mul_assoc] using this

theorem exists_weyl_of_oneOpposite (h : Hyp G D) (hc : RootClosure D) (hs : SpecialClosure D)
    (hl : ∃ d ∈ D, ∃ e ∈ rootSet D d, e ≠ d) {b x : G} (hb : b ∈ D) (hx : x ∈ D)
    (hbx : ¬ Commute b x) (hoddbx : Odd (orderOf (b * x))) (h1 : OneOpposite D b x) :
    ∃ h₀ ∈ rootGroup D x ⊔ rootGroup D b, (orderOf h₀).Prime ∧ orderOf h₀ ≠ 2 ∧
      h₀ * b * h₀⁻¹ ∈ rootSet D b ∧ h₀ * x * h₀⁻¹ ∈ rootSet D x ∧
      (∀ t ∈ rootGroup D x ⊔ rootGroup D b, t * b * t⁻¹ ∈ rootSet D b →
        t * x * t⁻¹ ∈ rootSet D x → orderOf t = orderOf h₀ → t ∈ Subgroup.zpowers h₀) ∧
      ∃ μ ∈ D, μ ∈ rootGroup D x ⊔ rootGroup D b ∧ μ * h₀ * μ⁻¹ = h₀⁻¹ ∧
        μ * b * μ⁻¹ ∈ rootSet D x ∧ μ * x * μ⁻¹ ∈ rootSet D b ∧
        ∃ k ∈ rootGroup D b, ∃ u ∈ rootSet D x, μ = k * u * k⁻¹ := by
  classical
  have := h.finite
  have hD := h.root
  have hclass := h.isClass
  have hQ : Moufang.CommLambda D :=
    commLambda_of_nCoreCommutatorInRoot hclass hD (nCoreCommutatorInRoot_of_hyp h hc)
  set Y := rootGroup D x ⊔ rootGroup D b with hY
  obtain ⟨n, hn, -, φ, hφx, hφb⟩ := exists_mulEquiv_SL2_of_oneOpposite h hc hs hQ hb hx hbx
    hoddbx h1 (four_le_card_rootGroup hclass hD hc hl hb)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hF : 4 ≤ Nat.card (GaloisField 2 n) := by
    rw [GaloisField.card 2 n (by omega)]
    exact (Nat.pow_le_pow_right (by norm_num) hn : 2 ^ 2 ≤ 2 ^ n)
  have hbY : rootGroup D b ≤ Y := le_sup_right
  have hxY : rootGroup D x ≤ Y := le_sup_left
  have hbY' : b ∈ Y := hbY (rootSet_subset_rootGroup D b (mem_rootSet_self hb))
  have hxY' : x ∈ Y := hxY (rootSet_subset_rootGroup D x (mem_rootSet_self hx))
  have hmemK : ∀ {K : Subgroup G}
      {K' : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n))},
      (K.subgroupOf Y).map φ.toMonoidHom = K' → ∀ z : ↥Y, (z : G) ∈ K ↔ φ z ∈ K' := by
    intro K K' hK z
    rw [← hK]
    constructor
    · intro hz
      exact ⟨z, hz, rfl⟩
    · rintro ⟨z', hz', hzz'⟩
      have := φ.injective hzz'
      rw [← this]
      exact hz'
  have hsymm : ∀ {K : Subgroup G}
      {K' : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n))},
      (K.subgroupOf Y).map φ.toMonoidHom = K' → ∀ {s}, s ∈ K' → ((φ.symm s : ↥Y) : G) ∈ K := by
    intro K K' hK s hs'
    exact (hmemK hK (φ.symm s)).2 (by simpa using hs')
  obtain ⟨p, hp, hp2, hT, hord, hlow, hup, -⟩ :=
    exists_splitTorus_weyl (F := GaloisField 2 n) hF
  obtain ⟨a₀, ha₀⟩ := exists_eq_splitTorus_of_normalizes hT
    (hup _ ((RankOne.mem_upperUnipotent_iff _).2 ⟨1, rfl⟩))
    (hlow _ ((RankOne.mem_lowerUnipotent_iff _).2 ⟨1, rfl⟩))
  have hnorm : ∀ {K : Subgroup G}
      {K' : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n))},
      (K.subgroupOf Y).map φ.toMonoidHom = K' → K ≤ Y →
      ∀ {s : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n)}, (∀ u ∈ K', s * u * s⁻¹ ∈ K') →
        ∀ β ∈ K, ((φ.symm s : ↥Y) : G) * β * ((φ.symm s : ↥Y) : G)⁻¹ ∈ K := by
    intro K K' hK hKY s hs' β hβ
    have hβY : β ∈ Y := hKY hβ
    have h1' := hs' _ ((hmemK hK ⟨β, hβY⟩).1 hβ)
    have h2 : φ (φ.symm s * ⟨β, hβY⟩ * (φ.symm s)⁻¹) = s * φ ⟨β, hβY⟩ * s⁻¹ := by simp
    rw [← h2, ← hmemK hK] at h1'
    simpa using h1'
  have horder : orderOf ((φ.symm hT : ↥Y) : G) = p := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, hord]
  refine ⟨(φ.symm hT : G), (φ.symm hT).2, horder ▸ hp, horder ▸ hp2, ?_, ?_, ?_, ?_⟩
  · exact mem_rootSet_of_mem_rootGroup_of_ne_one hD hc hb
      (hnorm hφb hbY hlow b (rootSet_subset_rootGroup D b (mem_rootSet_self hb)))
      (conj_ne_one_of_ne_one (hD.ne_one hb))
  · exact mem_rootSet_of_mem_rootGroup_of_ne_one hD hc hx
      (hnorm hφx hxY hup x (rootSet_subset_rootGroup D x (mem_rootSet_self hx)))
      (conj_ne_one_of_ne_one (hD.ne_one hx))
  ·
    intro t htY htb htx hto
    set t' : ↥Y := ⟨t, htY⟩ with ht'
    have hconjK : ∀ {K : Subgroup G}
        {K' : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n))},
        (K.subgroupOf Y).map φ.toMonoidHom = K' → (∀ β ∈ K, t * β * t⁻¹ ∈ K) →
        ∀ {s}, s ∈ K' → φ t' * s * (φ t')⁻¹ ∈ K' := by
      intro K K' hK htK s hs'
      have hs'' := hs'
      rw [← hK] at hs''
      obtain ⟨z, hz, rfl⟩ := hs''
      have := (hmemK hK (t' * z * t'⁻¹)).1 (by simpa [ht'] using htK _ hz)
      simpa using this
    obtain ⟨a, ha⟩ := exists_eq_splitTorus_of_normalizes (φ t')
      (hconjK hφx (fun β hβ => conj_mem_rootGroup_of_conj_mem_rootSet hclass htx hβ)
        ((RankOne.mem_upperUnipotent_iff _).2 ⟨1, rfl⟩))
      (hconjK hφb (fun β hβ => conj_mem_rootGroup_of_conj_mem_rootSet hclass htb hβ)
        ((RankOne.mem_lowerUnipotent_iff _).2 ⟨1, rfl⟩))
    have hoa : orderOf a = orderOf a₀ := by
      have e1 : orderOf a = orderOf t := by
        rw [← orderOf_injective _ splitTorusSLHom_injective a, ← ha, MulEquiv.orderOf_eq,
          ← Subgroup.orderOf_coe]
      have e2 : orderOf a₀ = orderOf ((φ.symm hT : ↥Y) : G) := by
        rw [← orderOf_injective _ splitTorusSLHom_injective a₀, ← ha₀, Subgroup.orderOf_coe,
          MulEquiv.orderOf_eq]
      rw [e1, e2, hto]
    have hz : Subgroup.zpowers a = Subgroup.zpowers a₀ := by
      rw [IsCyclic.subgroup_eq_iff_card_eq, Nat.card_zpowers, Nat.card_zpowers, hoa]
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 (hz ▸ Subgroup.mem_zpowers a)
    refine Subgroup.mem_zpowers_iff.2 ⟨m, ?_⟩
    have h2 : φ t' = φ ((φ.symm hT) ^ m) := by
      rw [ha, ← hm, map_zpow, ← ha₀, map_zpow, MulEquiv.apply_symm_apply]
    have h3 := φ.injective h2
    have h4 := congrArg Subtype.val h3
    simpa [ht'] using h4.symm
  ·
    set w₀ := standardSplitWeylSL (GaloisField 2 n) with hw₀
    obtain ⟨g, hg, u, hu, hu1, hw⟩ := standardSplitWeylSL_eq_conj (F := GaloisField 2 n)
    have hk := hsymm hφb hg
    have hu' := hsymm hφx hu
    have hu'1 : ((φ.symm u : ↥Y) : G) ≠ 1 := by
      intro h'
      apply hu1
      have : φ.symm u = 1 := Subtype.ext h'
      simpa using congrArg φ this
    have hu'T := mem_rootSet_of_mem_rootGroup_of_ne_one hD hc hx hu' hu'1
    have hμeq : ((φ.symm w₀ : ↥Y) : G) =
        ((φ.symm g : ↥Y) : G) * ((φ.symm u : ↥Y) : G) * ((φ.symm g : ↥Y) : G)⁻¹ := by
      have := congrArg (fun z => ((φ.symm z : ↥Y) : G)) hw
      simpa using this
    have hμD : ((φ.symm w₀ : ↥Y) : G) ∈ D := by
      rw [hμeq]
      exact conj_mem_of_isClass hclass _ hu'T.1
    refine ⟨(φ.symm w₀ : G), hμD, (φ.symm w₀).2, ?_, ?_, ?_, _, hk, _, hu'T, hμeq⟩
    · have h2 : w₀ * hT * w₀⁻¹ = hT⁻¹ := by
        rw [hw₀, ha₀, standardSplitWeylSL_conj, map_inv]
      have := congrArg (fun z => ((φ.symm z : ↥Y) : G)) h2
      simpa using this
    · obtain ⟨s, hs'⟩ := (RankOne.mem_lowerUnipotent_iff _).1
        ((hmemK hφb ⟨b, hbY'⟩).1 (rootSet_subset_rootGroup D b (mem_rootSet_self hb)))
      have h2 : φ (φ.symm w₀ * ⟨b, hbY'⟩ * (φ.symm w₀)⁻¹) ∈
          upperUnipotent (GaloisField 2 n) := by
        rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, hs',
          standardSplitWeylSL_conj_lowerElt]
        exact (RankOne.mem_upperUnipotent_iff _).2 ⟨_, rfl⟩
      have h3 := (hmemK hφx _).2 h2
      simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h3
      exact mem_rootSet_of_mem_rootGroup_of_ne_one hD hc hx h3
        (conj_ne_one_of_ne_one (hD.ne_one hb))
    · obtain ⟨s, hs'⟩ := (RankOne.mem_upperUnipotent_iff _).1
        ((hmemK hφx ⟨x, hxY'⟩).1 (rootSet_subset_rootGroup D x (mem_rootSet_self hx)))
      have h2 : φ (φ.symm w₀ * ⟨x, hxY'⟩ * (φ.symm w₀)⁻¹) ∈
          lowerUnipotent (GaloisField 2 n) := by
        rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, hs',
          standardSplitWeylSL_conj_upperElt]
        exact (RankOne.mem_lowerUnipotent_iff _).2 ⟨_, rfl⟩
      have h3 := (hmemK hφb _).2 h2
      simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h3
      exact mem_rootSet_of_mem_rootGroup_of_ne_one hD hc hb h3
        (conj_ne_one_of_ne_one (hD.ne_one hx))

end CFSG.Timmesfeld.Bridge
