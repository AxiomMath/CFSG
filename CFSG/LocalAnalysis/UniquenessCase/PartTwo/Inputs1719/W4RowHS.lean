module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm11_1RowHalf
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4RowIndex
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4RowCenter
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4RowE9
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4RowFstarLift
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4RowLiftEquiv
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4RowHSPack
public import CFSG.Quasithin.Background.SmithB45ExcHSDisp
public import CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit.Heisenberg

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Blueprint CFSG.QuasithinUnique.Setup CFSG.QuasithinUnique.Setup.X1
  CFSG.QuasithinUnique.Setup.Family CFSG.QuasithinUnique.Bridge.HSExcl CFSG.Quasithin.B45Exc.HSRu
  CFSG.Quasithin.B45Exc.HS CFSG.Sporadic.Schreier CFSG.Sporadic.SmallOddCore
  CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit

namespace W4Row

variable {W : Type} [CommGroup W] {Y L : Subgroup (MulAut W)}

variable [Finite W]

private theorem hs_e9_index_eq {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w * w = 1)
    {ψ : ↥hsP →* MulAut W} (hψ : Function.Injective ψ)
    {x₁ x₂ : Equiv.Perm (Fin 3850)} (hx₁ : x₁ ∈ hsP) (hx₂ : x₂ ∈ hsP)
    (h31 : x₁ ^ 3 = 1) (h32 : x₂ ^ 3 = 1) (hne : x₁ ≠ 1) (hcomm : x₁ * x₂ = x₂ * x₁)
    (hba : ∀ j < 3, x₂ ≠ x₁ ^ j)
    (hm₂ : ∃ m ∈ hsP, m * x₁ * m⁻¹ = x₂)
    (hm₃ : ∃ m ∈ hsP, m * x₁ * m⁻¹ = x₁ * x₂)
    (hm₄ : ∃ m ∈ hsP, m * x₁ * m⁻¹ = x₁ * x₂ ^ 2) :
    ∃ j : ℕ, (fixV (zpowers (ψ ⟨x₁, hx₁⟩))).index = 2 ^ (6 * j) := by
  let P₁ : ↥hsP := ⟨x₁, hx₁⟩
  let P₂ : ↥hsP := ⟨x₂, hx₂⟩
  let a : MulAut W := ψ P₁
  let b : MulAut W := ψ P₂
  have ha3 : a ^ 3 = 1 := by
    change (ψ P₁) ^ 3 = 1
    rw [← map_pow, show P₁ ^ 3 = 1 from Subtype.ext (by simpa using h31), map_one]
  have hb3 : b ^ 3 = 1 := by
    change (ψ P₂) ^ 3 = 1
    rw [← map_pow, show P₂ ^ 3 = 1 from Subtype.ext (by simpa using h32), map_one]
  have ha1 : a ≠ 1 := by
    intro h
    apply hne
    have h1 : P₁ = 1 := hψ (h.trans (map_one ψ).symm)
    have h2 : (P₁ : Equiv.Perm (Fin 3850)) = 1 := by rw [h1]; simp
    simpa [P₁] using h2
  have hab : a * b = b * a := by
    change ψ P₁ * ψ P₂ = ψ P₂ * ψ P₁
    rw [← map_mul, ← map_mul, show P₁ * P₂ = P₂ * P₁ from Subtype.ext (by
      simpa only [Subgroup.coe_mul] using hcomm)]
  have hba' : ∀ j < 3, b ≠ a ^ j := by
    intro j hj h
    apply hba j hj
    have h2 : P₂ = P₁ ^ j := hψ (by
      show ψ P₂ = ψ (P₁ ^ j)
      rw [map_pow]
      exact h)
    simpa using congrArg (fun x : ↥hsP => (x : Equiv.Perm (Fin 3850))) h2
  have h₁ : (fixV (zpowers b)).index = (fixV (zpowers a)).index := by
    obtain ⟨m, hm, hmx⟩ := hm₂
    exact index_fixV_hom_conj ψ P₁ P₂ hm hmx
  have h₂ : (fixV (zpowers (a * b))).index = (fixV (zpowers a)).index := by
    obtain ⟨m, hm, hmx⟩ := hm₃
    change (fixV (zpowers (ψ P₁ * ψ P₂))).index = (fixV (zpowers (ψ P₁))).index
    rw [← map_mul]
    exact index_fixV_hom_conj ψ P₁ (P₁ * P₂) hm hmx
  have h₃ : (fixV (zpowers (a * b ^ 2))).index = (fixV (zpowers a)).index := by
    obtain ⟨m, hm, hmx⟩ := hm₄
    change (fixV (zpowers (ψ P₁ * ψ P₂ ^ 2))).index = (fixV (zpowers (ψ P₁))).index
    rw [← map_pow, ← map_mul]
    exact index_fixV_hom_conj ψ P₁ (P₁ * P₂ ^ 2) hm hmx
  exact exists_index_eq_two_pow_six_mul_of_e9 hW ha3 hb3 ha1 hab hba' h₁ h₂ h₃

private theorem hs_e9_sixteen
    {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w * w = 1)
    {L : Subgroup (MulAut W)} {ψ : ↥hsP →* MulAut W} (hψ : Function.Injective ψ)
    (hψL : ∀ x : ↥hsP, ψ x ∈ L) (eqv : ↥L ≃* NativeSporadic.Carrier .HS)
    {x₁ : Equiv.Perm (Fin 3850)} (hx₁ : x₁ ∈ hsP)
    (hk5 : ∃ k ∈ hsP, (x₁ * (k * x₁ * k⁻¹)) ^ 5 = 1 ∧ x₁ * (k * x₁ * k⁻¹) ≠ 1) :
    2 ^ 16 ≤ (fixV (zpowers (ψ ⟨x₁, hx₁⟩))).index ^ 2 := by
  obtain ⟨k, hk, hk5a, hk1⟩ := hk5
  let P₁ : ↥hsP := ⟨x₁, hx₁⟩
  let k' : ↥hsP := ⟨k, hk⟩
  let z : MulAut W := ψ (P₁ * (k' * P₁ * k'⁻¹))
  have hzL : z ∈ L := hψL _
  have hz5 : z ^ 5 = 1 := by
    change (ψ (P₁ * (k' * P₁ * k'⁻¹))) ^ 5 = 1
    rw [← map_pow,
      show (P₁ * (k' * P₁ * k'⁻¹)) ^ 5 = 1 from Subtype.ext (by simpa using hk5a), map_one]
  have hz1 : z ≠ 1 := by
    intro h
    apply hk1
    have h2 : P₁ * (k' * P₁ * k'⁻¹) = 1 := hψ (h.trans (map_one ψ).symm)
    simpa using congrArg (fun x : ↥hsP => (x : Equiv.Perm (Fin 3850))) h2
  have hzle : (fixV (zpowers z)).index ≤
      (fixV (zpowers (ψ P₁))).index * (fixV (zpowers (ψ P₁))).index := by
    have hz : z = ψ P₁ * (ψ k' * ψ P₁ * (ψ k')⁻¹) := by
      change ψ (P₁ * (k' * P₁ * k'⁻¹)) = ψ P₁ * (ψ k' * ψ P₁ * (ψ k')⁻¹)
      simp only [map_mul, map_inv]
    rw [hz]
    calc (fixV (zpowers (ψ P₁ * (ψ k' * ψ P₁ * (ψ k')⁻¹)))).index
        ≤ (fixV (zpowers (ψ P₁))).index *
            (fixV (zpowers (ψ k' * ψ P₁ * (ψ k')⁻¹))).index := index_fixV_mul_le _ _
      _ = (fixV (zpowers (ψ P₁))).index * (fixV (zpowers (ψ P₁))).index := by
          rw [CFSG.QuasithinUnique.Setup.X1.index_fixV_conj (ψ k') (ψ P₁)]
  have hz16 : 2 ^ 16 ≤ (fixV (zpowers z)).index := hs_two_pow_sixteen hW eqv hzL hz5 hz1
  calc 2 ^ 16 ≤ (fixV (zpowers z)).index := hz16
    _ ≤ (fixV (zpowers (ψ P₁))).index * (fixV (zpowers (ψ P₁))).index := hzle
    _ = (fixV (zpowers (ψ P₁))).index ^ 2 := (sq _).symm

private theorem hs_e9_index_twelve
    (hW : ∀ w : W, w * w = 1) {L : Subgroup (MulAut W)} {ψ : ↥hsP →* MulAut W}
    (hψ : Function.Injective ψ) (hψL : ∀ x : ↥hsP, ψ x ∈ L)
    (eqv : ↥L ≃* NativeSporadic.Carrier .HS)
    {x₁ x₂ : Equiv.Perm (Fin 3850)} (hx₁ : x₁ ∈ hsP) (hx₂ : x₂ ∈ hsP)
    (h31 : x₁ ^ 3 = 1) (h32 : x₂ ^ 3 = 1) (hne : x₁ ≠ 1) (hcomm : x₁ * x₂ = x₂ * x₁)
    (hba : ∀ j < 3, x₂ ≠ x₁ ^ j)
    (hm₂ : ∃ m ∈ hsP, m * x₁ * m⁻¹ = x₂)
    (hm₃ : ∃ m ∈ hsP, m * x₁ * m⁻¹ = x₁ * x₂)
    (hm₄ : ∃ m ∈ hsP, m * x₁ * m⁻¹ = x₁ * x₂ ^ 2)
    (hk5 : ∃ k ∈ hsP, (x₁ * (k * x₁ * k⁻¹)) ^ 5 = 1 ∧ x₁ * (k * x₁ * k⁻¹) ≠ 1) :
    2 ^ 12 ≤ (fixV (zpowers (ψ ⟨x₁, hx₁⟩))).index := by
  obtain ⟨j, hj⟩ := hs_e9_index_eq hW hψ hx₁ hx₂ h31 h32 hne hcomm hba hm₂ hm₃ hm₄
  have h16 := hs_e9_sixteen hW hψ hψL eqv hx₁ hk5
  rw [hj, ← pow_mul] at h16
  have hj2 : 2 ≤ j := by
    have h := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 h16
    omega
  calc 2 ^ 12 = 2 ^ (6 * 2) := by norm_num
    _ ≤ 2 ^ (6 * j) := Nat.pow_le_pow_right (by norm_num) (by omega)
    _ = (fixV (zpowers (ψ ⟨x₁, hx₁⟩))).index := hj.symm

private theorem hs_inv_conj_p
    {W : Type} [CommGroup W] {Y L : Subgroup (MulAut W)} {t : MulAut W} (ht : t ∈ Y)
    (hto : orderOf t = 2) (ψL : Lift L Y hsR hsP) {x₁ : Equiv.Perm (Fin 3850)}
    (hx₁ : x₁ ∈ hsP)
    (hinv : ∀ i ∈ [5, 12, 21, 34], ∃ h ∈ hsP,
      hsT i * (h * x₁ * h⁻¹) * (hsT i)⁻¹ = (h * x₁ * h⁻¹)⁻¹) :
    ∃ c : ↥hsP, ∃ r : ↥hsR,
      (r : Equiv.Perm (Fin 3850)) =
          (ψL.hom ⟨t, Subgroup.mem_sup_right ht⟩ : Equiv.Perm (Fin 3850)) ∧
        (r : Equiv.Perm (Fin 3850)) *
            ((c * ⟨x₁, hx₁⟩ * c⁻¹ : ↥hsP) : Equiv.Perm (Fin 3850)) *
            (r : Equiv.Perm (Fin 3850))⁻¹ =
          ((c * ⟨x₁, hx₁⟩ * c⁻¹ : ↥hsP) : Equiv.Perm (Fin 3850))⁻¹ := by
  have ht2 : t * t = 1 := by
    rw [← pow_two, ← hto]
    exact pow_orderOf_eq_one t
  let t' : ↥(L ⊔ Y) := ⟨t, Subgroup.mem_sup_right ht⟩
  have ht'2 : t' * t' = 1 := Subtype.ext (by simpa [t'] using ht2)
  let r : ↥hsR := ψL.hom t'
  have hr2 : (r : Equiv.Perm (Fin 3850)) * r = 1 := by
    have h : r * r = 1 := by
      change ψL.hom t' * ψL.hom t' = 1
      rw [← map_mul, ht'2, map_one]
    exact congrArg (fun x : ↥hsR => (x : Equiv.Perm (Fin 3850))) h
  have hr1 : (r : Equiv.Perm (Fin 3850)) ≠ 1 := by
    intro h
    have h1 : ψL.hom t' = 1 := Subtype.ext h
    have h2 : t' = 1 := ψL.inj (by rw [h1, map_one])
    have h3 : t = 1 := by
      simpa [t'] using congrArg (fun x : ↥(L ⊔ Y) => (x : MulAut W)) h2
    rw [h3, orderOf_one] at hto
    exact absurd hto (by norm_num)
  obtain ⟨g, hg, i, hi, hgi⟩ := hs_inv_conj r.2 hr2 hr1
  obtain ⟨h, hh, hinv'⟩ := hinv i hi
  let c : ↥hsP := ⟨g * h, hsP.mul_mem hg hh⟩
  refine ⟨c, r, rfl, ?_⟩
  have hp : ((c * ⟨x₁, hx₁⟩ * c⁻¹ : ↥hsP) : Equiv.Perm (Fin 3850)) =
      g * (h * x₁ * h⁻¹) * g⁻¹ := by
    simp only [c, Subgroup.coe_mul, Subgroup.coe_inv]
    group
  rw [hgi, hp]
  calc (g * hsT i * g⁻¹) * (g * (h * x₁ * h⁻¹) * g⁻¹) * (g * hsT i * g⁻¹)⁻¹
      = g * (hsT i * (h * x₁ * h⁻¹) * (hsT i)⁻¹) * g⁻¹ := by group
    _ = g * (h * x₁ * h⁻¹)⁻¹ * g⁻¹ := by rw [hinv']
    _ = (g * (h * x₁ * h⁻¹) * g⁻¹)⁻¹ := by group

private theorem hs_inv_index_sq
    (hW : ∀ w : W, w * w = 1) {Y L : Subgroup (MulAut W)} (hLY : L ≤ Y)
    (hF : Fstar Y = L) (hperf : Group.IsPerfect ↥L)
    (hY : Y ≤ Subgroup.normalizer (L : Set (MulAut W)))
    (e₀ : (↥L ⧸ Subgroup.center ↥L) ≃* NativeSporadic.Carrier .HS)
    (hZ : Subgroup.center ↥L = ⊥)
    (Φ : ↥hsR ≃* MulAut (NativeSporadic.Carrier .HS))
    (hΦ : ∀ s, Φ ⟨(hsEquivC s : Equiv.Perm (Fin 3850)), hsP_le_hsR (hsEquivC s).2⟩ =
      MulAut.conj s)
    {t : MulAut W} (ht : t ∈ Y) (hto : orderOf t = 2) :
    2 ^ 12 ≤ (fixV (zpowers t)).index ^ 2 := by
  obtain ⟨x₁, hx₁, x₂, hx₂, h31, h32, hne, hcomm, hba, hm₂, hm₃, hm₄, hk5, hinv⟩ :=
    hs_e9_package
  let ψL : Lift L Y hsR hsP := liftOfFstar hLY hF hperf hY e₀ hZ hsP_le_hsR Φ hsEquivC hΦ
  let ψ : ↥hsP →* MulAut W := psiOfLift ψL
  have hψ : Function.Injective ψ := psiOfLift_injective ψL
  have hψL : ∀ x : ↥hsP, ψ x ∈ L := psiOfLift_mem ψL
  let P₁ : ↥hsP := ⟨x₁, hx₁⟩
  have ha12 : 2 ^ 12 ≤ (fixV (zpowers (ψ P₁))).index :=
    hs_e9_index_twelve hW hψ hψL (redEquiv e₀ hZ) hx₁ hx₂ h31 h32 hne hcomm hba hm₂ hm₃ hm₄ hk5
  obtain ⟨c, r, hr, hinvP⟩ := hs_inv_conj_p ht hto ψL hx₁ hinv
  let p : ↥hsP := c * P₁ * c⁻¹
  have hp3 : p ^ 3 = 1 := by
    have hPP : p = c * P₁ * c⁻¹ := rfl
    rw [hPP, conj_pow, show P₁ ^ 3 = 1 from Subtype.ext (by simpa using h31)]
    group
  have hz : (ψ p) ^ 3 = 1 ∧ t * ψ p * t⁻¹ = (ψ p)⁻¹ :=
    ⟨by rw [← map_pow, hp3, map_one],
      conj_psiOfLift_eq_inv hsP_le_hsR ψL ht (by rw [← hr]; exact hinvP)⟩
  have ht2 : t * t = 1 := by
    rw [← pow_two, ← hto]
    exact pow_orderOf_eq_one t
  have hzidx : (fixV (zpowers (ψ p))).index = (fixV (zpowers (ψ P₁))).index := by
    change (fixV (zpowers (ψ (c * P₁ * c⁻¹)))).index = (fixV (zpowers (ψ P₁))).index
    rw [map_mul, map_mul, map_inv]
    rw [CFSG.QuasithinUnique.Setup.X1.index_fixV_conj (ψ c) (ψ P₁)]
  have hsq := index_fixV_le_sq_of_inverts (W := W) (p := 3) (by norm_num) hz.1 ht2 hz.2
  calc 2 ^ 12 ≤ (fixV (zpowers (ψ P₁))).index := ha12
    _ = (fixV (zpowers (ψ p))).index := hzidx.symm
    _ ≤ (fixV (zpowers t)).index ^ 2 := hsq

end W4Row

theorem w4Thm11_1RowM_HS_holds :
    W4Thm11_1RowM .HS := by
  intro W _ _ hW Y L hLY hLn hF hq hO2 hs
  obtain ⟨e₀⟩ := hs
  have hW' : ∀ w : W, w * w = 1 := fun w => by rw [← sq]; exact hW w
  have hZ : Subgroup.center ↥L = ⊥ :=
    W4Row.center_eq_bot_of_o2Trivial_of_cover hq.1 hO2 e₀ hs_cover
  obtain ⟨t₀, ht₀, ht₀o⟩ :=
    W4Row.exists_orderOf_eq_two_of_cq e₀ (by rw [card_hsCarrier]; norm_num)
  have hY : Y ≤ Subgroup.normalizer (L : Set (MulAut W)) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLY).1 hLn
  obtain ⟨Φ, hΦ⟩ := hs_aut_model
  have hperf : Group.IsPerfect ↥L := hq.1
  show tableM .HS ≤ E3.mParam Y
  rw [show tableM .HS = 6 from rfl]
  exact W4Row.le_mParam_of_index_sq hW' ⟨t₀, hLY ht₀, ht₀o⟩ fun t ht hto =>
    W4Row.hs_inv_index_sq hW' hLY hF hperf hY e₀ hZ Φ hΦ ht hto

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
