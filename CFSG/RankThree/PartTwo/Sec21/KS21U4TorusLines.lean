module

public import CFSG.RankThree.PartTwo.Sec21.KS21U4Blocks
public import CFSG.RankThree.PartOne.KF.SUSylow
public import CFSG.RankThree.PartTwo.Sec21.KS21U4Transport

public section

namespace CFSG.RankThree.PartTwo.Sec21.U4Lines

open Matrix CFSG CFSG.RankThree
open CFSG.LieType.Universal.Unitary (SU)
open CFSG.LieType.BorelTits (unitaryInvolution unitaryInvolution_apply
  unitaryInvolution_involutive)
open CFSG.Assembly.RankThreeEven (projSL)
open CFSG.RankThree.PartOne.KFU (D8Mod d8Tor d8Vec d8VecHom diagU diagUHom permGL d8Comb_four
  d8Vec_mem_SU permGL_mem_SU permGL_conj_diagU exists_conj_into_d8Tor_su diagU_val)

section Torus

variable {F : Type} [Field F]

@[expose] noncomputable def torusD : D8Mod 3 F →* GL (Fin 4) F := diagUHom.comp (d8VecHom 4)

theorem torusD_apply (v : D8Mod 3 F) : torusD v = diagU (d8Vec 4 v) := rfl

theorem coe_torusD (v : D8Mod 3 F) :
    ((torusD v : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
      diagonal ![((v.1 : Fˣ) : F), ((v.2 : Fˣ) : F), (((v.2 : Fˣ)⁻¹ : Fˣ) : F),
        (((v.1 : Fˣ)⁻¹ : Fˣ) : F)] := by
  rw [torusD_apply, diagU_val]
  congr 1
  funext i
  fin_cases i <;> rfl

@[expose] noncomputable def weyl₁ : GL (Fin 4) F := permGL (Equiv.swap 0 1 * Equiv.swap 2 3)

@[expose] noncomputable def weyl₂ : GL (Fin 4) F := permGL (Equiv.swap 1 2)

theorem conj_weyl₁ (v : D8Mod 3 F) : weyl₁ * torusD v * weyl₁⁻¹ = torusD (v.2, v.1) := by
  rw [weyl₁, torusD_apply, torusD_apply, permGL_conj_diagU]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem conj_weyl₂ (v : D8Mod 3 F) : weyl₂ * torusD v * weyl₂⁻¹ = torusD (v.1, v.2⁻¹) := by
  rw [weyl₂, torusD_apply, torusD_apply, permGL_conj_diagU]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem zpowers_torusD_inv (v : D8Mod 3 F) :
    Subgroup.zpowers (torusD v⁻¹) = Subgroup.zpowers (torusD v) := by
  rw [map_inv, Subgroup.zpowers_inv]

theorem not_mem_map_conj {G : Type*} [Group G] {S : Subgroup G} {w x : G} (hx : x ∉ S)
    (h : w * x * w⁻¹ = x ∨ w * x * w⁻¹ = x⁻¹) : x ∉ S.map (MulAut.conj w).toMonoidHom := by
  rintro ⟨y, hy, hyx⟩
  change w * y * w⁻¹ = x at hyx
  apply hx
  rcases h with h | h
  · have : y = x := (MulAut.conj w).injective (by simp only [MulAut.conj_apply]; rw [hyx, h])
    rwa [← this]
  · have : y = x⁻¹ := (MulAut.conj w).injective (by
      simp only [MulAut.conj_apply]
      rw [hyx, show w * x⁻¹ * w⁻¹ = (w * x * w⁻¹)⁻¹ by group, h, inv_inv])
    rw [← inv_inv x, ← this]
    exact S.inv_mem hy

end Torus

section Roots

variable {F : Type} [Field F] [Finite F] {b : ℕ}

omit [Field F] [Finite F] in
theorem three_dvd_card_sub_one (hbe : Even b) (hF : Nat.card F = (2 ^ b) ^ 2) :
    3 ∣ Nat.card F - 1 := by
  rw [hF]
  have h : 2 ^ b - 1 ∣ (2 ^ b) ^ 2 - 1 := by
    simpa only [one_pow] using Nat.sub_dvd_pow_sub_pow (2 ^ b) 1 2
  exact (three_dvd_two_pow_sub_one hbe).trans h

theorem card_rootsOfUnity_three (hbe : Even b) (hF : Nat.card F = (2 ^ b) ^ 2) :
    Nat.card (rootsOfUnity 3 F) = 3 :=
  CFSG.LinearGroups.card_rootsOfUnity_of_dvd (three_dvd_card_sub_one hbe hF)

theorem unitaryInvolution_rootsOfUnity [CharP F 2] (hbe : Even b) (u : rootsOfUnity 3 F) :
    unitaryInvolution F 2 b ((u : Fˣ) : F) = (u : Fˣ) := by
  have h1 : (u : Fˣ) ^ 3 = 1 := (mem_rootsOfUnity 3 _).mp u.2
  obtain ⟨k, hk⟩ := three_dvd_two_pow_sub_one hbe
  rw [unitaryInvolution_apply, ← Units.val_pow_eq_pow_val]
  congr 1
  calc (u : Fˣ) ^ 2 ^ b = (u : Fˣ) ^ (2 ^ b - 1) * (u : Fˣ) := by
        rw [← pow_succ, Nat.sub_add_cancel Nat.one_le_two_pow]
    _ = (u : Fˣ) := by rw [hk, pow_mul, h1, one_pow, one_mul]

omit [Finite F] in
theorem eq_one_or_eq_or_eq_inv (hμ : Nat.card (rootsOfUnity 3 F) = 3) {ω : rootsOfUnity 3 F}
    (hω : ω ≠ 1) (u : rootsOfUnity 3 F) : u = 1 ∨ u = ω ∨ u = ω⁻¹ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h3 : ω ^ 3 = 1 := by
    have h := pow_card_eq_one' (G := rootsOfUnity 3 F) (x := ω)
    rwa [hμ] at h
  have hord : orderOf ω = 3 := orderOf_eq_prime h3 hω
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp (mem_zpowers_of_prime_card hμ hω (g' := u))
  rw [← zpow_mod_orderOf, hord]
  have h : k % ((3 : ℕ) : ℤ) = 0 ∨ k % ((3 : ℕ) : ℤ) = 1 ∨ k % ((3 : ℕ) : ℤ) = 2 := by omega
  rcases h with h | h | h
  · left
    rw [h, zpow_zero]
  · right; left
    rw [h, zpow_one]
  · right; right
    rw [h, show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast]
    exact eq_inv_of_mul_eq_one_left (by rw [← pow_succ]; exact h3)

theorem line_cases (hμ : Nat.card (rootsOfUnity 3 F) = 3) {ω : rootsOfUnity 3 F} (hω : ω ≠ 1)
    {ℓ : Subgroup (GL (Fin 4) F)} (hℓ : ℓ ≤ d8Tor 3 F 4) (h3 : Nat.card ℓ = 3) :
    ℓ = Subgroup.zpowers (torusD (ω, 1)) ∨ ℓ = Subgroup.zpowers (torusD (1, ω)) ∨
      ℓ = Subgroup.zpowers (torusD (ω, ω)) ∨ ℓ = Subgroup.zpowers (torusD (ω, ω⁻¹)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Nontrivial ℓ := Finite.one_lt_card_iff_nontrivial.mp (by rw [h3]; norm_num)
  obtain ⟨⟨x, hx⟩, hx1⟩ := exists_ne (1 : ℓ)
  have hx1' : x ≠ 1 := fun h => hx1 (Subtype.ext h)
  have hx3 : x ^ 3 = 1 := by
    have h := pow_card_eq_one' (G := ℓ) (x := ⟨x, hx⟩)
    rw [h3] at h
    exact congrArg Subtype.val h
  have hℓx : ℓ = Subgroup.zpowers x := by
    symm
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hx) ?_
    rw [h3, Nat.card_zpowers, orderOf_eq_prime hx3 hx1']
  obtain ⟨v, hv⟩ := hℓ hx
  have hv' : torusD v = x := hv
  rw [hℓx, ← hv']
  obtain ⟨α, β⟩ := v
  have hi : ∀ u w : rootsOfUnity 3 F,
      Subgroup.zpowers (torusD (u⁻¹, w⁻¹)) = Subgroup.zpowers (torusD (u, w)) := fun u w => by
    rw [show ((u⁻¹, w⁻¹) : D8Mod 3 F) = (u, w)⁻¹ from rfl, zpowers_torusD_inv]
  rcases eq_one_or_eq_or_eq_inv hμ hω α with rfl | rfl | rfl <;>
    rcases eq_one_or_eq_or_eq_inv hμ hω β with rfl | rfl | rfl
  · exact absurd (hv'.symm.trans (map_one torusD)) hx1'
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inl (by rw [← hi, inv_one, inv_inv]))
  · exact Or.inl rfl
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr rfl))
  · exact Or.inl (by rw [← hi, inv_one, inv_inv])
  · exact Or.inr (Or.inr (Or.inr (by rw [← hi, inv_inv])))
  · exact Or.inr (Or.inr (Or.inl (by rw [hi])))

end Roots

theorem pow_three_of_mem_sup {G : Type*} [Group G] {ℓ₁ ℓ₂ : Subgroup G}
    (hc : ℓ₁ ≤ Subgroup.centralizer (ℓ₂ : Set G)) (h₁ : Nat.card ℓ₁ = 3)
    (h₂ : Nat.card ℓ₂ = 3) {x : G} (hx : x ∈ ℓ₁ ⊔ ℓ₂) : x ^ 3 = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : IsCyclic ℓ₁ := isCyclic_of_prime_card h₁
  have : IsCyclic ℓ₂ := isCyclic_of_prime_card h₂
  have hp : ∀ y ∈ (ℓ₁ : Set G) ∪ ℓ₂, y ^ 3 = 1 := by
    rintro y (hy | hy)
    · have h := pow_card_eq_one' (G := ℓ₁) (x := ⟨y, hy⟩)
      rw [h₁] at h
      exact congrArg Subtype.val h
    · have h := pow_card_eq_one' (G := ℓ₂) (x := ⟨y, hy⟩)
      rw [h₂] at h
      exact congrArg Subtype.val h
  have hcomm : ((ℓ₁ : Set G) ∪ ℓ₂).Pairwise Commute := by
    rintro y (hy | hy) z (hz | hz) -
    · exact congrArg Subtype.val (IsMulCommutative.is_comm.comm (⟨y, hy⟩ : ℓ₁) ⟨z, hz⟩)
    · exact (Subgroup.mem_centralizer_iff.mp (hc hy) z hz).symm
    · exact Subgroup.mem_centralizer_iff.mp (hc hz) y hy
    · exact congrArg Subtype.val (IsMulCommutative.is_comm.comm (⟨y, hy⟩ : ℓ₂) ⟨z, hz⟩)
  have hab := Subgroup.isMulCommutative_closure hcomm
  rw [← Subgroup.closure_eq ℓ₁, ← Subgroup.closure_eq ℓ₂, ← Subgroup.closure_union] at hx
  induction hx using Subgroup.closure_induction with
  | mem y hy => exact hp y hy
  | one => exact one_pow 3
  | mul y z hy hz ihy ihz =>
    have hyz : Commute y z := congrArg Subtype.val (hab.is_comm.comm ⟨y, hy⟩ ⟨z, hz⟩)
    rw [hyz.mul_pow, ihy, ihz, one_mul]
  | inv y hy ihy => rw [inv_pow, ihy, inv_one]

section Core

variable {F : Type} [Field F] [Finite F] [CharP F 2] {b : ℕ}

omit [CharP F 2] in
theorem nonempty_shortSL_mulEquiv_galois (σ : F ≃+* F) (hb : 0 < b)
    (hF : Nat.card F = (2 ^ b) ^ 2) : Nonempty (shortSL σ ≃* projSL 2 (GaloisField 2 (2 * b))) := by
  have := Fintype.ofFinite F
  have := Fintype.ofFinite (GaloisField 2 (2 * b))
  have hcard : Fintype.card F = Fintype.card (GaloisField 2 (2 * b)) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hF,
      card_galoisField_two_mul b hb]
  exact ⟨(MonoidHom.ofInjective (iotaS_injective σ)).symm.trans
    ((CFSG.Adapters.RankTwoModelTransports.specialLinearGroupCongr (Fin 2)
      (FiniteField.ringEquivOfCardEq hcard)).trans (projSLTwoEquivSL _).symm)⟩

theorem linesConcl_of_le_torus (hb : 0 < b) (hbe : Even b) (hF : Nat.card F = (2 ^ b) ^ 2)
    {ℓ₁ ℓ₂ ℓ₃ : Subgroup (GL (Fin 4) F)} (h₁ : ℓ₁ ≤ d8Tor 3 F 4) (h₂ : ℓ₂ ≤ d8Tor 3 F 4)
    (h₃ : ℓ₃ ≤ d8Tor 3 F 4) (hl : LinesHyp (SU (unitaryInvolution F 2 b) 4) ℓ₁ ℓ₂ ℓ₃) :
    LinesConcl (SU (unitaryInvolution F 2 b) 4) ℓ₁ ℓ₃ b := by
  set σ : F ≃+* F := unitaryInvolution F 2 b with hσdef
  have hb2 : 2 ≤ b := by obtain ⟨k, hk⟩ := hbe; omega
  have hσσ : ∀ c, σ (σ c) = c := unitaryInvolution_involutive hF
  have hμ := card_rootsOfUnity_three hbe hF
  have : Nontrivial (rootsOfUnity 3 F) :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [hμ]; norm_num)
  obtain ⟨ω, hω⟩ := exists_ne (1 : rootsOfUnity 3 F)
  set a : F := ((ω : Fˣ) : F) with ha
  have ha3 : a ^ 3 = 1 := by
    rw [ha, ← Units.val_pow_eq_pow_val, (mem_rootsOfUnity 3 _).mp ω.2, Units.val_one]
  have ha1 : a ≠ 1 := fun h => hω (Subtype.ext (Units.ext h))
  have ha0 : a ≠ 0 := fun h => by rw [h] at ha3; norm_num at ha3
  have hainv : a ≠ a⁻¹ := by
    intro h
    apply ha1
    have h2 : a * a = 1 := by
      calc a * a = a * a⁻¹ := by rw [← h]
        _ = 1 := mul_inv_cancel₀ ha0
    calc a = a ^ 3 * a⁻¹ * a⁻¹ := by field_simp
      _ = 1 := by rw [ha3, one_mul, ← h, h2]
  have hinv1 : (1 : F) ≠ a⁻¹ := fun h => ha1 (by rw [← inv_inv a, ← h, inv_one])
  have hval : (((ω : Fˣ)⁻¹ : Fˣ) : F) = a⁻¹ := Units.val_inv_eq_inv_val _
  have hfix := unitaryInvolution_rootsOfUnity (F := F) hbe
  have hw₁ : weyl₁ ∈ SU σ 4 := permGL_mem_SU σ _ (by decide)
  have hw₂ : weyl₂ ∈ SU σ 4 := permGL_mem_SU σ _ (by decide)
  have ht₁ : ((torusD ((ω, 1) : D8Mod 3 F) : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
      diagonal ![a, 1, 1, a⁻¹] := by
    rw [coe_torusD]
    simp [ha]
  have ht₃ : ((torusD ((ω, ω) : D8Mod 3 F) : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
      diagonal ![a, a, a⁻¹, a⁻¹] := by
    rw [coe_torusD]
    simp [ha]
  obtain ⟨eL⟩ := nonempty_longSL_mulEquiv (F := F) hb hF
  obtain ⟨eS⟩ := nonempty_shortSL_mulEquiv_galois σ hb hF
  have hperfL : ⁅longSL σ, longSL σ⁆ = longSL σ :=
    Subgroup.isPerfect_iff.mp (isPerfect_of_mulEquiv_projSL hb2 eL)
  have hperfS : ⁅shortSL σ, shortSL σ⁆ = shortSL σ :=
    Subgroup.isPerfect_iff.mp (isPerfect_of_mulEquiv_projSL (by omega) eS)
  have hS₁ : inSubgroup perfectResidual (SU σ 4 ⊓ Subgroup.centralizer
      (Subgroup.zpowers (torusD ((ω, 1) : D8Mod 3 F)) : Set (GL (Fin 4) F))) = longSL σ :=
    perfectResidual_long σ ht₁ ha1 hainv hinv1 hperfL
  have hS₃ : inSubgroup perfectResidual (SU σ 4 ⊓ Subgroup.centralizer
      (Subgroup.zpowers (torusD ((ω, ω) : D8Mod 3 F)) : Set (GL (Fin 4) F))) = shortSL σ :=
    perfectResidual_short σ hσσ ht₃ hainv hperfS
  have hL₂ : Subgroup.zpowers (torusD ((1, ω) : D8Mod 3 F)) =
      (Subgroup.zpowers (torusD ((ω, 1) : D8Mod 3 F))).map (MulAut.conj weyl₁).toMonoidHom := by
    rw [MonoidHom.map_zpowers]
    congr 1
    exact (conj_weyl₁ ((ω, 1) : D8Mod 3 F)).symm
  have hL₄ : Subgroup.zpowers (torusD ((ω, ω⁻¹) : D8Mod 3 F)) =
      (Subgroup.zpowers (torusD ((ω, ω) : D8Mod 3 F))).map (MulAut.conj weyl₂).toMonoidHom := by
    rw [MonoidHom.map_zpowers]
    congr 1
    exact (conj_weyl₂ ((ω, ω) : D8Mod 3 F)).symm
  have hS₂ : inSubgroup perfectResidual (SU σ 4 ⊓ Subgroup.centralizer
      (Subgroup.zpowers (torusD ((1, ω) : D8Mod 3 F)) : Set (GL (Fin 4) F))) =
      (longSL σ).map (MulAut.conj weyl₁).toMonoidHom := by
    rw [hL₂, perfectResidual_conj hw₁, hS₁]
  have hS₄ : inSubgroup perfectResidual (SU σ 4 ⊓ Subgroup.centralizer
      (Subgroup.zpowers (torusD ((ω, ω⁻¹) : D8Mod 3 F)) : Set (GL (Fin 4) F))) =
      (shortSL σ).map (MulAut.conj weyl₂).toMonoidHom := by
    rw [hL₄, perfectResidual_conj hw₂, hS₃]
  have e₁ : Nonempty (inSubgroup perfectResidual (SU σ 4 ⊓ Subgroup.centralizer
      (Subgroup.zpowers (torusD ((ω, 1) : D8Mod 3 F)) : Set (GL (Fin 4) F))) ≃*
        projSL 2 (GaloisField 2 b)) := by
    rw [hS₁]
    exact ⟨eL⟩
  have e₂ : Nonempty (inSubgroup perfectResidual (SU σ 4 ⊓ Subgroup.centralizer
      (Subgroup.zpowers (torusD ((1, ω) : D8Mod 3 F)) : Set (GL (Fin 4) F))) ≃*
        projSL 2 (GaloisField 2 b)) := by
    rw [hS₂]
    exact ⟨((longSL σ).equivMapOfInjective _ (MulAut.conj weyl₁).injective).symm.trans eL⟩
  have e₃ : Nonempty (inSubgroup perfectResidual (SU σ 4 ⊓ Subgroup.centralizer
      (Subgroup.zpowers (torusD ((ω, ω) : D8Mod 3 F)) : Set (GL (Fin 4) F))) ≃*
        projSL 2 (GaloisField 2 (2 * b))) := by
    rw [hS₃]
    exact ⟨eS⟩
  have e₄ : Nonempty (inSubgroup perfectResidual (SU σ 4 ⊓ Subgroup.centralizer
      (Subgroup.zpowers (torusD ((ω, ω⁻¹) : D8Mod 3 F)) : Set (GL (Fin 4) F))) ≃*
        projSL 2 (GaloisField 2 (2 * b))) := by
    rw [hS₄]
    exact ⟨((shortSL σ).equivMapOfInjective _ (MulAut.conj weyl₂).injective).symm.trans eS⟩
  have n₃L : torusD ((ω, ω) : D8Mod 3 F) ∉ longSL σ := fun h => ha1 (by
    have := entry_zero_zero_of_mem_longSL σ h
    rw [coe_torusD] at this
    simpa [ha] using this)
  have n₄L : torusD ((ω, ω⁻¹) : D8Mod 3 F) ∉ longSL σ := fun h => ha1 (by
    have := entry_zero_zero_of_mem_longSL σ h
    rw [coe_torusD] at this
    simpa [ha] using this)
  have n₁S : torusD ((ω, 1) : D8Mod 3 F) ∉ shortSL σ := fun h => ha1 (by
    have := det_block_of_mem_shortSL σ h
    rw [ht₁] at this
    simpa [ha] using this)
  have n₂S : torusD ((1, ω) : D8Mod 3 F) ∉ shortSL σ := fun h => ha1 (by
    have := det_block_of_mem_shortSL σ h
    rw [coe_torusD] at this
    simpa [ha] using this)
  have n₃ : torusD ((ω, ω) : D8Mod 3 F) ∉ (longSL σ).map (MulAut.conj weyl₁).toMonoidHom :=
    not_mem_map_conj n₃L (Or.inl (conj_weyl₁ _))
  have n₄ : torusD ((ω, ω⁻¹) : D8Mod 3 F) ∉ (longSL σ).map (MulAut.conj weyl₁).toMonoidHom :=
    not_mem_map_conj n₄L (Or.inr (by rw [conj_weyl₁, ← map_inv]; rfl))
  have n₁ : torusD ((ω, 1) : D8Mod 3 F) ∉ (shortSL σ).map (MulAut.conj weyl₂).toMonoidHom :=
    not_mem_map_conj n₁S (Or.inl (by rw [conj_weyl₂, inv_one]))
  have n₂ : torusD ((1, ω) : D8Mod 3 F) ∉ (shortSL σ).map (MulAut.conj weyl₂).toMonoidHom :=
    not_mem_map_conj n₂S (Or.inr (by rw [conj_weyl₂, ← map_inv]; rfl))
  obtain ⟨-, -, -, h4, h5, h6, -, h8, h9, h10, h11⟩ := hl
  rcases line_cases hμ hω h₁ h4 with rfl | rfl | rfl | rfl <;>
    rcases line_cases hμ hω h₂ h5 with rfl | rfl | rfl | rfl <;>
    rcases line_cases hμ hω h₃ h6 with rfl | rfl | rfl | rfl <;>
    first
    | exact absurd rfl h8
    | exact absurd rfl h9
    | exact absurd rfl h10
    | exact Or.inl ⟨e₁, e₃⟩
    | exact Or.inl ⟨e₁, e₄⟩
    | exact Or.inl ⟨e₂, e₃⟩
    | exact Or.inl ⟨e₂, e₄⟩
    | exact Or.inr ⟨e₃, e₁⟩
    | exact Or.inr ⟨e₃, e₂⟩
    | exact Or.inr ⟨e₄, e₁⟩
    | exact Or.inr ⟨e₄, e₂⟩
    | exact absurd (h11 (Subgroup.mem_zpowers _)) (by rw [hS₁]; exact n₃L)
    | exact absurd (h11 (Subgroup.mem_zpowers _)) (by rw [hS₁]; exact n₄L)
    | exact absurd (h11 (Subgroup.mem_zpowers _)) (by rw [hS₂]; exact n₃)
    | exact absurd (h11 (Subgroup.mem_zpowers _)) (by rw [hS₂]; exact n₄)
    | exact absurd (h11 (Subgroup.mem_zpowers _)) (by rw [hS₃]; exact n₁S)
    | exact absurd (h11 (Subgroup.mem_zpowers _)) (by rw [hS₃]; exact n₂S)
    | exact absurd (h11 (Subgroup.mem_zpowers _)) (by rw [hS₄]; exact n₁)
    | exact absurd (h11 (Subgroup.mem_zpowers _)) (by rw [hS₄]; exact n₂)

end Core

theorem linesAt_SU {b : ℕ} (hb : 0 < b) (hbe : Even b) :
    LinesAt (SU (unitaryInvolution (GaloisField 2 (2 * b)) 2 b) 4) b := by
  have hF := card_galoisField_two_mul b hb
  intro ℓ₁ ℓ₂ ℓ₃ hl
  obtain ⟨h1, h2, h3, h4, h5, -, h7, -⟩ := id hl
  have hle : ℓ₁ ⊔ ℓ₂ ≤ SU (unitaryInvolution (GaloisField 2 (2 * b)) 2 b) 4 := sup_le h1 h2
  have hX : ∀ x ∈ (ℓ₁ ⊔ ℓ₂).subgroupOf (SU (unitaryInvolution (GaloisField 2 (2 * b)) 2 b) 4),
      x ^ 3 = 1 := fun x hx =>
    Subtype.ext (by rw [Subgroup.coe_pow]; exact pow_three_of_mem_sup h3 h4 h5 hx)
  obtain ⟨g, hg⟩ := exists_conj_into_d8Tor_su (n := 4) (Or.inl rfl) d8Comb_four hF
    Nat.prime_three (by norm_num) (three_dvd_two_pow_sub_one hbe) _ hX
  have hT : ∀ ℓ ≤ ℓ₁ ⊔ ℓ₂, mapL (MulAut.conj g) ℓ ≤ d8Tor 3 (GaloisField 2 (2 * b)) 4 := by
    intro ℓ hℓ
    rw [mapL_conj g (hℓ.trans hle)]
    rintro _ ⟨x, hx, rfl⟩
    exact hg ⟨x, hle (hℓ hx)⟩ (hℓ hx)
  exact linesConcl_of_mapL (MulAut.conj g) h1 (h7.trans hle)
    (linesConcl_of_le_torus hb hbe hF (hT ℓ₁ le_sup_left) (hT ℓ₂ le_sup_right) (hT ℓ₃ h7)
      (linesHyp_mapL (MulAut.conj g) hl))

theorem u4ThreeTorusLines : U4ThreeTorusLines :=
  u4ThreeTorusLines_of_SU fun _ hb hbe => linesAt_SU hb hbe

end CFSG.RankThree.PartTwo.Sec21.U4Lines

namespace CFSG.RankThree.PartTwo.Sec21

theorem item229UnitaryRoots_of_item228 (h2131 : Item2131One) (h222 : Item222) (h228 : Item228)
    (hKW : KOfWellDefinedAll) : Item229UnitaryRoots :=
  item229UnitaryRoots_of h2131 h222 h228 hKW U4Lines.u4ThreeTorusLines

end CFSG.RankThree.PartTwo.Sec21
