module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm11_1RowHalf
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4RowIndex
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4RowCenter
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4RowEp2
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4RowFstarLift
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4RowLiftEquiv
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4RowHePack
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1HeFacts
public import CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit.Heisenberg

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Blueprint CFSG.QuasithinUnique.Setup CFSG.QuasithinUnique.Setup.X1
  CFSG.QuasithinUnique.Setup.Family CFSG.Quasithin.B45Exc.HSRu CFSG.Sporadic.HeldB
  CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit

namespace W4Row

private theorem orderOf_two_zmod_five : orderOf (2 : ZMod 5) = 4 := by
  rw [orderOf_eq_iff (by norm_num)]
  refine ⟨by decide, fun m hm hm0 => ?_⟩
  interval_cases m <;> decide

private theorem he_e25_index_twenty {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w * w = 1) {ψ : ↥heP →* MulAut W} (hψ : Function.Injective ψ)
    {x₁ x₂ : Equiv.Perm (Fin 8330)} (hx₁ : x₁ ∈ heP) (hx₂ : x₂ ∈ heP)
    (h51 : x₁ ^ 5 = 1) (h52 : x₂ ^ 5 = 1) (hne : x₁ ≠ 1) (hcomm : x₁ * x₂ = x₂ * x₁)
    (hba : ∀ j < 5, x₂ ≠ x₁ ^ j) (hm₀ : ∃ m ∈ heP, m * x₁ * m⁻¹ = x₂)
    (hmi : ∀ i, 0 < i → i < 5 → ∃ m ∈ heP, m * x₁ * m⁻¹ = x₁ * x₂ ^ i) :
    2 ^ 20 ≤ (fixV (zpowers (ψ ⟨x₁, hx₁⟩))).index := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  let P₁ : ↥heP := ⟨x₁, hx₁⟩
  let P₂ : ↥heP := ⟨x₂, hx₂⟩
  have ha : ψ P₁ ^ 5 = 1 := by
    rw [← map_pow, show P₁ ^ 5 = 1 from Subtype.ext (by simpa using h51), map_one]
  have hb : ψ P₂ ^ 5 = 1 := by
    rw [← map_pow, show P₂ ^ 5 = 1 from Subtype.ext (by simpa using h52), map_one]
  have ha1 : ψ P₁ ≠ 1 := fun h =>
    hne (congrArg Subtype.val (hψ (h.trans (map_one ψ).symm)))
  have hab : ψ P₁ * ψ P₂ = ψ P₂ * ψ P₁ := by
    rw [← map_mul, ← map_mul, show P₁ * P₂ = P₂ * P₁ from Subtype.ext hcomm]
  have hba' : ∀ j < 5, ψ P₂ ≠ ψ P₁ ^ j := fun j hj h =>
    hba j hj (by simpa using congrArg Subtype.val (hψ (h.trans (map_pow ψ P₁ j).symm)))
  have h₀ : (fixV (zpowers (ψ P₂))).index = (fixV (zpowers (ψ P₁))).index := by
    obtain ⟨m, hm, hmx⟩ := hm₀
    exact index_fixV_hom_conj ψ P₁ P₂ hm hmx
  have h : ∀ i, 0 < i → i < 5 →
      (fixV (zpowers (ψ P₁ * ψ P₂ ^ i))).index = (fixV (zpowers (ψ P₁))).index := by
    intro i hi0 hi
    obtain ⟨m, hm, hmx⟩ := hmi i hi0 hi
    rw [← map_pow, ← map_mul]
    exact index_fixV_hom_conj ψ P₁ (P₁ * P₂ ^ i) hm (by simpa using hmx)
  have h20 := two_pow_le_index_of_ep2 hW (by norm_num) ha hb ha1 hab hba' h₀ h
  rwa [orderOf_two_zmod_five] at h20

private theorem he_inv_conj_p
    {W : Type} [CommGroup W] {Y L : Subgroup (MulAut W)} {t : MulAut W} (ht : t ∈ Y)
    (hto : orderOf t = 2) (ψL : Lift L Y heAutGroup heP) {x₁ : Equiv.Perm (Fin 8330)}
    (hx₁ : x₁ ∈ heP)
    (hinv : ∀ t ∈ [heGenPerm 0, heT1P, heAutU], ∃ h ∈ heP,
      t * (h * x₁ * h⁻¹) * t⁻¹ = (h * x₁ * h⁻¹)⁻¹) :
    ∃ c : ↥heP, ∃ r : ↥heAutGroup,
      (r : Equiv.Perm (Fin 8330)) =
          (ψL.hom ⟨t, Subgroup.mem_sup_right ht⟩ : Equiv.Perm (Fin 8330)) ∧
        (r : Equiv.Perm (Fin 8330)) *
            ((c * ⟨x₁, hx₁⟩ * c⁻¹ : ↥heP) : Equiv.Perm (Fin 8330)) *
            (r : Equiv.Perm (Fin 8330))⁻¹ =
          ((c * ⟨x₁, hx₁⟩ * c⁻¹ : ↥heP) : Equiv.Perm (Fin 8330))⁻¹ := by
  have ht2 : t * t = 1 := by
    rw [← pow_two, ← hto]
    exact pow_orderOf_eq_one t
  let t' : ↥(L ⊔ Y) := ⟨t, Subgroup.mem_sup_right ht⟩
  have ht'2 : t' * t' = 1 := Subtype.ext (by simpa [t'] using ht2)
  let r : ↥heAutGroup := ψL.hom t'
  have hr2 : (r : Equiv.Perm (Fin 8330)) ^ 2 = 1 := by
    have h : r * r = 1 := by
      change ψL.hom t' * ψL.hom t' = 1
      rw [← map_mul, ht'2, map_one]
    rw [sq]
    exact congrArg (fun x : ↥heAutGroup => (x : Equiv.Perm (Fin 8330))) h
  have hr1 : (r : Equiv.Perm (Fin 8330)) ≠ 1 := by
    intro h
    have h1 : ψL.hom t' = 1 := Subtype.ext h
    have h2 : t' = 1 := ψL.inj (by rw [h1, map_one])
    have h3 : t = 1 := by
      simpa [t'] using congrArg (fun x : ↥(L ⊔ Y) => (x : MulAut W)) h2
    rw [h3, orderOf_one] at hto
    exact absurd hto (by norm_num)
  have hro : orderOf (r : Equiv.Perm (Fin 8330)) = 2 := orderOf_eq_prime hr2 hr1
  obtain ⟨g, hg, τ, hτ, hgτ⟩ : ∃ g ∈ heP, ∃ τ ∈ [heGenPerm 0, heT1P, heAutU],
      (r : Equiv.Perm (Fin 8330)) = g * τ * g⁻¹ := by
    by_cases hrP : (r : Equiv.Perm (Fin 8330)) ∈ heP
    · rcases involution_conj_cases hrP hro with ⟨g, hg, hgr⟩ | ⟨g, hg, hgr⟩
      · exact ⟨g, hg, heGenPerm 0, by simp, hgr⟩
      · exact ⟨g, hg, heT1P, by simp, hgr⟩
    · obtain ⟨g, hg, hgr⟩ := exists_conj_heAutU r.2 hrP hro
      exact ⟨g, hg, heAutU, by simp, hgr⟩
  obtain ⟨h, hh, hinv'⟩ := hinv τ hτ
  let c : ↥heP := ⟨g * h, heP.mul_mem hg hh⟩
  refine ⟨c, r, rfl, ?_⟩
  have hp : ((c * ⟨x₁, hx₁⟩ * c⁻¹ : ↥heP) : Equiv.Perm (Fin 8330)) =
      g * (h * x₁ * h⁻¹) * g⁻¹ := by
    simp only [c, Subgroup.coe_mul, Subgroup.coe_inv]
    group
  rw [hgτ, hp]
  calc (g * τ * g⁻¹) * (g * (h * x₁ * h⁻¹) * g⁻¹) * (g * τ * g⁻¹)⁻¹
      = g * (τ * (h * x₁ * h⁻¹) * τ⁻¹) * g⁻¹ := by group
    _ = g * (h * x₁ * h⁻¹)⁻¹ * g⁻¹ := by rw [hinv']
    _ = (g * (h * x₁ * h⁻¹) * g⁻¹)⁻¹ := by group

private theorem he_inv_index_sq
    {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w * w = 1) {Y L : Subgroup (MulAut W)} (hLY : L ≤ Y)
    (hF : Fstar Y = L) (hperf : Group.IsPerfect ↥L)
    (hY : Y ≤ Subgroup.normalizer (L : Set (MulAut W)))
    (e₀ : (↥L ⧸ Subgroup.center ↥L) ≃* NativeSporadic.Carrier .He)
    (hZ : Subgroup.center ↥L = ⊥) {t : MulAut W} (ht : t ∈ Y) (hto : orderOf t = 2) :
    2 ^ 20 ≤ (fixV (zpowers t)).index ^ 2 := by
  obtain ⟨Φ0, hΦ0⟩ := he_model
  let Φ : ↥heAutGroup ≃* MulAut (NativeSporadic.Carrier .He) := Φ0
  let θ : NativeSporadic.Carrier .He ≃* heP := heEquivP
  have hΦ : ∀ (x : ↥heAutGroup) (s : NativeSporadic.Carrier .He),
      Φ x s = θ.symm (heConjR x (θ s)) := hΦ0
  obtain ⟨x₁, hx₁, x₂, hx₂, h51, h52, hne, hcomm, hba, hm₀, hmi, hinv⟩ := he_e25_package
  let ψL : Lift L Y heAutGroup heP := liftOfFstar hLY hF hperf hY e₀ hZ heP_le_heAutGroup Φ θ
    fun s => conj_compat heP_le_heAutGroup heConjR (fun x a => heConjR_apply x a) Φ θ hΦ s
  let ψ : ↥heP →* MulAut W := psiOfLift ψL
  let P₁ : ↥heP := ⟨x₁, hx₁⟩
  have ha20 : 2 ^ 20 ≤ (fixV (zpowers (ψ P₁))).index :=
    he_e25_index_twenty hW (psiOfLift_injective ψL) hx₁ hx₂ h51 h52 hne hcomm hba hm₀ hmi
  obtain ⟨c, r, hr, hinvP⟩ := he_inv_conj_p ht hto ψL hx₁ hinv
  let p : ↥heP := c * P₁ * c⁻¹
  have hp5 : p ^ 5 = 1 := by
    have hPP : p = c * P₁ * c⁻¹ := rfl
    rw [hPP, conj_pow, show P₁ ^ 5 = 1 from Subtype.ext (by simpa using h51)]
    group
  have hz : (ψ p) ^ 5 = 1 ∧ t * ψ p * t⁻¹ = (ψ p)⁻¹ :=
    ⟨by rw [← map_pow, hp5, map_one],
      conj_psiOfLift_eq_inv heP_le_heAutGroup ψL ht (by rw [← hr]; exact hinvP)⟩
  have ht2 : t * t = 1 := by
    rw [← pow_two, ← hto]
    exact pow_orderOf_eq_one t
  have hzidx : (fixV (zpowers (ψ p))).index = (fixV (zpowers (ψ P₁))).index := by
    change (fixV (zpowers (ψ (c * P₁ * c⁻¹)))).index = (fixV (zpowers (ψ P₁))).index
    rw [map_mul, map_mul, map_inv]
    rw [CFSG.QuasithinUnique.Setup.X1.index_fixV_conj (ψ c) (ψ P₁)]
  have hsq := index_fixV_le_sq_of_inverts (W := W) (p := 5) (by norm_num) hz.1 ht2 hz.2
  calc 2 ^ 20 ≤ (fixV (zpowers (ψ P₁))).index := ha20
    _ = (fixV (zpowers (ψ p))).index := hzidx.symm
    _ ≤ (fixV (zpowers t)).index ^ 2 := hsq

end W4Row

theorem w4Thm11_1RowM_He_holds :
    W4Thm11_1RowM .He := by
  intro W _ _ hW Y L hLY hLn hF hq hO2 hs
  obtain ⟨e₀⟩ := hs
  have hW' : ∀ w : W, w * w = 1 := fun w => by rw [← sq]; exact hW w
  have hZ : Subgroup.center ↥L = ⊥ :=
    W4Row.center_eq_bot_of_o2Trivial_of_cover hq.1 hO2 e₀ he_cover
  have hcard : Nat.card (NativeSporadic.Carrier .He) = 4030387200 := CFSG.Sporadic.He.card_He
  obtain ⟨t₀, ht₀, ht₀o⟩ := W4Row.exists_orderOf_eq_two_of_cq e₀ (by rw [hcard]; norm_num)
  have hY : Y ≤ Subgroup.normalizer (L : Set (MulAut W)) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLY).1 hLn
  show tableM .He ≤ E3.mParam Y
  rw [show tableM .He = 10 from rfl]
  exact W4Row.le_mParam_of_index_sq hW' ⟨t₀, hLY ht₀, ht₀o⟩ fun t ht hto =>
    W4Row.he_inv_index_sq hW' hLY hF hq.1 hY e₀ hZ ht hto

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
