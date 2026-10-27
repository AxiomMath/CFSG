module

public import CFSG.Quasithin.EmptyFaithful.S153E58M
public import CFSG.Quasithin.EmptyFaithful.S153E58A
public import CFSG.Quasithin.EmptyFaithful.S153E58B

public section

namespace CFSG.Quasithin

open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.LieType.BorelTits
open scoped commutatorElement

namespace S153E58

open S153E57

section Iso

variable {W : Type} [CommGroup W] [Finite W] {H K : Subgroup (MulAut W)} {W₁ W₂ : Subgroup W}
  {bil : W → W → ZMod 2}

omit [Finite W] in
theorem Setup58.eq_one_of_centralizes (hS : Setup58 H K W₁ W₂ bil)
    {π : ↥(StatedSL 3 (ZMod 2)) →* ↥K}
    (hπ : (FFModel.nat (StatedSL 3 (ZMod 2))).RealizesVia K W₁ ⊥ π) {h : MulAut W} (hh : h ∈ H)
    (hc : ∀ k ∈ K, h * k = k * h) : h = 1 := by
  obtain ⟨e, hT, -⟩ := exists_coords_of_realizes hπ
  have hst : ∀ w ∈ W₁, h w ∈ W₁ := by
    rcases hS.cases_swap hT hh with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact h1
    · exfalso
      have hf := form_zero_of_transv hT hS.inv₁ (fun a b => bil (h a) b)
        (fun a b c => hS.bil_right _ b c)
        (fun k hk a _ b _ => by
          have hka : h (k a) = k (h a) := by
            have := DFunLike.congr_fun (hc k hk) a
            simpa using this
          show bil (h (k a)) (k b) = bil (h a) b
          rw [hka]
          exact hS.bil_inv_K hk _ _)
      obtain ⟨a, ha, ha1⟩ := hS.exists_ne_one₁
      have h2 : h a = 1 := hS.eq_one_of_orth hT (h a) (h1 a ha)
        (fun x hx => by rw [hS.bil_symm]; exact hf a ha x hx)
      apply ha1
      apply h.injective
      rw [h2, map_one]
  have hid := eq_id_of_commute hT hS.inv₁ hst hc
  exact hS.eq_one_of_triv₁ hT hh hid

omit [Finite W] in
theorem Setup58.pi_injective (hS : Setup58 H K W₁ W₂ bil) {π : ↥(StatedSL 3 (ZMod 2)) →* ↥K}
    (hπ : (FFModel.nat (StatedSL 3 (ZMod 2))).RealizesVia K W₁ ⊥ π) : Function.Injective π := by
  have hsimple := isSimpleGroup_statedSL_three_two
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal π.ker with h | h
  · exact (MonoidHom.ker_eq_bot_iff π).1 h
  · exfalso
    apply hS.K1
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    obtain ⟨γ, hγ⟩ : ∃ γ : ↥(StatedSL 3 (ZMod 2)), π γ = ⟨x, hx⟩ := hπ.1 ⟨x, hx⟩
    have h1 : γ ∈ π.ker := h ▸ Subgroup.mem_top γ
    rw [MonoidHom.mem_ker] at h1
    exact congrArg Subtype.val (hγ.symm.trans h1)

omit [Finite W] in
noncomputable def Setup58.piEquiv (hS : Setup58 H K W₁ W₂ bil) {π : ↥(StatedSL 3 (ZMod 2)) →* ↥K}
    (hπ : (FFModel.nat (StatedSL 3 (ZMod 2))).RealizesVia K W₁ ⊥ π) : ↥(StatedSL 3 (ZMod 2)) ≃* ↥K :=
  MulEquiv.ofBijective π ⟨hS.pi_injective hπ, hπ.1⟩

omit [Finite W] in
theorem Setup58.card_K (hS : Setup58 H K W₁ W₂ bil) {π : ↥(StatedSL 3 (ZMod 2)) →* ↥K}
    (hπ : (FFModel.nat (StatedSL 3 (ZMod 2))).RealizesVia K W₁ ⊥ π) : Nat.card ↥K = 168 := by
  rw [← Nat.card_congr (hS.piEquiv hπ).toEquiv]
  exact card_statedSL_three_two

theorem Setup58.card_H (hS : Setup58 H K W₁ W₂ bil) {π : ↥(StatedSL 3 (ZMod 2)) →* ↥K}
    (hπ : (FFModel.nat (StatedSL 3 (ZMod 2))).RealizesVia K W₁ ⊥ π) : Nat.card ↥H = 336 := by
  have h2 := hS.relIndex_eq_two hπ
  have e := Subgroup.relIndex_mul_card K H
  rw [inf_eq_left.2 hS.KH, h2, hS.card_K hπ] at e
  omega

theorem Setup58.oTwoUpper_eq (hS : Setup58 H K W₁ W₂ bil) {π : ↥(StatedSL 3 (ZMod 2)) →* ↥K}
    (hπ : (FFModel.nat (StatedSL 3 (ZMod 2))).RealizesVia K W₁ ⊥ π) (hperf : ⁅K, K⁆ = K) :
    oTwoUpper H = K := by
  obtain ⟨e, hT, -⟩ := exists_coords_of_realizes hπ
  have hKo : K = oTwoUpper K := (oTwoUpper_eq_of_perfect hperf).symm
  have : Finite (MulAut W) := finite_mulAut_of_finite W
  refine (eq_oTwoUpper_of_pow_mem hS.KH (fun x hx => ?_) hKo).symm
  by_cases hxK : x ∈ K
  · exact ⟨0, by simpa using hxK⟩
  · refine ⟨1, ?_⟩
    have hsw := hS.swap_of_not_mem_K hπ hx hxK
    have : x ^ 2 ∈ K := by
      refine hS.mem_K_of_stab hπ (H.pow_mem hx 2) fun w hw => ?_
      rw [pow_two, MulAut.mul_apply]
      exact hsw.2 _ (hsw.1 w hw)
    simpa using this

noncomputable def Setup58.conjHom (hS : Setup58 H K W₁ W₂ bil) {π : ↥(StatedSL 3 (ZMod 2)) →* ↥K}
    (hπ : (FFModel.nat (StatedSL 3 (ZMod 2))).RealizesVia K W₁ ⊥ π) :
    ↥H →* MulAut ↥(StatedSL 3 (ZMod 2)) :=
  have : Finite (MulAut W) := finite_mulAut_of_finite W
  (MulAut.congr (hS.piEquiv hπ).symm).toMonoidHom.comp
    (K.normalizerMonoidHom.comp (Subgroup.inclusion (fun h hh => mem_normalizer_of_forall' (hS.Kn h hh))))

theorem Setup58.conjHom_injective (hS : Setup58 H K W₁ W₂ bil) {π : ↥(StatedSL 3 (ZMod 2)) →* ↥K}
    (hπ : (FFModel.nat (StatedSL 3 (ZMod 2))).RealizesVia K W₁ ⊥ π) :
    Function.Injective (hS.conjHom hπ) := by
  have : Finite (MulAut W) := finite_mulAut_of_finite W
  rw [injective_iff_map_eq_one]
  intro h hh
  have h1 : (K.normalizerMonoidHom.comp
      (Subgroup.inclusion (fun h hh => mem_normalizer_of_forall' (hS.Kn h hh)))) h = 1 := by
    have h0 : (MulAut.congr (hS.piEquiv hπ).symm) ((K.normalizerMonoidHom.comp
        (Subgroup.inclusion (fun h hh => mem_normalizer_of_forall' (hS.Kn h hh)))) h) = 1 := hh
    exact (map_eq_one_iff _ (MulAut.congr (hS.piEquiv hπ).symm).injective).1 h0
  apply Subtype.ext
  apply hS.eq_one_of_centralizes hπ h.2
  intro k hk
  have h2 := congrArg (fun φ : MulAut ↥K => (φ ⟨k, hk⟩ : MulAut W)) h1
  have h3 : (h : MulAut W) * k * (h : MulAut W)⁻¹ = k := by
    simpa [Subgroup.normalizerMonoidHom_apply_apply_coe] using h2
  calc (h : MulAut W) * k = ((h : MulAut W) * k * (h : MulAut W)⁻¹) * h := by group
    _ = k * h := by rw [h3]

theorem Setup58.nonempty_mulEquiv (hS : Setup58 H K W₁ W₂ bil) {π : ↥(StatedSL 3 (ZMod 2)) →* ↥K}
    (hπ : (FFModel.nat (StatedSL 3 (ZMod 2))).RealizesVia K W₁ ⊥ π) :
    Nonempty (↥H ≃* MulAut ↥(StatedSL 3 (ZMod 2))) := by
  have : Finite (MulAut ↥(StatedSL 3 (ZMod 2))) := by
    have : Finite ↥(StatedSL 3 (ZMod 2)) := Nat.finite_of_card_ne_zero (by rw [card_statedSL_three_two]; omega)
    exact finite_mulAut_of_finite _
  have hbij : Function.Bijective (hS.conjHom hπ) :=
    (hS.conjHom_injective hπ).bijective_of_nat_card_le (by
      rw [card_mulAut_statedSL_three_two, hS.card_H hπ])
  exact ⟨MulEquiv.ofBijective _ hbij⟩

end Iso

end S153E58

end CFSG.Quasithin
