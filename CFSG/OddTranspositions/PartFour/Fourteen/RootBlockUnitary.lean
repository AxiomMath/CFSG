module

public import CFSG.OddTranspositions.PartFour.Fourteen.RootBlock
public import CFSG.LocalAnalysis.WeakClosure81.W16Gt2KFactsJ

public section

namespace CFSG.OddTranspositions.PartFour

open CFSG.Open CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
  CFSG.LocalAnalysis.WeakClosure81 CFSG.LocalAnalysis.WeakClosure81.SevenK

section UnitaryCentres

variable {F : Type} [Field F] {σ : F ≃+* F} {m : ℕ}

theorem suTv_smul_mem_of_mem (hσ : IsUnitaryInvolution σ) {H : Subgroup (SUid σ m)}
    {a : Fin m → F} (ha : herm σ a a = 0) (hca : ∀ c, c + σ c = 0 → suTv hσ a c ∈ H)
    {g : SUid σ m} (hg : g ∈ H) {c : F} (hc : c + σ c = 0) : suTv hσ (g • a) c ∈ H := by
  rw [← suTv_conj hσ g ha hc]
  exact H.mul_mem (H.mul_mem hg (hca c hc)) (H.inv_mem hg)

theorem exists_iso_perp_pair_herm_eq (hσ : IsUnitaryInvolution σ) (hm : 4 ≤ m)
    {u w v : Fin m → F} (hu : herm σ u u = 0) (hw : herm σ w w = 0) (huw : herm σ u w = 1)
    (hv0 : herm σ (v - herm σ w v • u - herm σ u v • w)
      (v - herm σ w v • u - herm σ u v • w) ≠ 0) (γ : F) :
    ∃ z, herm σ z z = 0 ∧ herm σ z u = 0 ∧ herm σ z w = 0 ∧ herm σ z v = γ := by
  have hinv := hσ.invol
  obtain ⟨v₀, hv₀⟩ : ∃ v₀, v₀ = v - herm σ w v • u - herm σ u v • w := ⟨_, rfl⟩
  obtain ⟨hv₀u, hv₀w⟩ := herm_proj_pair hσ hu hw huw v
  rw [← hv₀] at hv₀u hv₀w hv0
  obtain ⟨c, hc⟩ := exists_smul_norm_one hσ hv0
  have hc0 : c ≠ 0 := by
    rintro rfl
    simp at hc
  obtain ⟨x₁, hx₁⟩ : ∃ x₁, x₁ = c • v₀ := ⟨_, rfl⟩
  rw [← hx₁] at hc
  have hx₁u : herm σ x₁ u = 0 := by
    rw [hx₁, herm_smul_left, herm_conj σ hinv, hv₀u, map_zero, mul_zero]
  have hx₁w : herm σ x₁ w = 0 := by
    rw [hx₁, herm_smul_left, herm_conj σ hinv, hv₀w, map_zero, mul_zero]
  obtain ⟨y, hy, hx₁y, huy, hwy⟩ :=
    exists_norm_one_perp_three hσ hm hc hu hw huw hx₁u hx₁w
  obtain ⟨μ, hμ⟩ := hσ.exists_norm_neg_one
  have hyx₁ : herm σ y x₁ = 0 := herm_eq_zero_comm σ hinv hx₁y
  have hv₀y : herm σ v₀ y = 0 := by
    have h1 := hx₁y
    rw [hx₁, herm_smul_left] at h1
    exact (mul_eq_zero.mp h1).resolve_left ((map_ne_zero σ).mpr hc0)
  have hyv₀ : herm σ y v₀ = 0 := herm_eq_zero_comm σ hinv hv₀y
  obtain ⟨z₀, hz₀⟩ : ∃ z₀, z₀ = x₁ + μ • y := ⟨_, rfl⟩
  have hz₀z₀ : herm σ z₀ z₀ = 0 := by
    rw [hz₀]
    simp only [herm_add_left, herm_add_right, herm_smul_left, herm_smul_right, hc, hx₁y, hyx₁,
      hy]
    linear_combination hμ
  have hyu : herm σ y u = 0 := herm_eq_zero_comm σ hinv huy
  have hyw : herm σ y w = 0 := herm_eq_zero_comm σ hinv hwy
  have hz₀u : herm σ z₀ u = 0 := by
    rw [hz₀, herm_add_left, herm_smul_left, hx₁u, hyu, mul_zero, add_zero]
  have hz₀w : herm σ z₀ w = 0 := by
    rw [hz₀, herm_add_left, herm_smul_left, hx₁w, hyw, mul_zero, add_zero]
  have hvdec : v = v₀ + herm σ w v • u + herm σ u v • w := by
    rw [hv₀]
    abel
  have hz₀v : herm σ z₀ v = σ c * herm σ v₀ v₀ := by
    rw [hvdec, herm_add_right, herm_add_right, herm_smul_right, herm_smul_right, hz₀u, hz₀w,
      hz₀, herm_add_left, herm_smul_left, hyv₀, hx₁, herm_smul_left]
    ring
  have hδ : σ c * herm σ v₀ v₀ ≠ 0 := by
    refine mul_ne_zero ((map_ne_zero σ).mpr hc0) ?_
    exact hv0
  refine ⟨σ (γ / (σ c * herm σ v₀ v₀)) • z₀, ?_, ?_, ?_, ?_⟩
  · rw [herm_smul_left, herm_smul_right, hz₀z₀, mul_zero, mul_zero]
  · rw [herm_smul_left, hz₀u, mul_zero]
  · rw [herm_smul_left, hz₀w, mul_zero]
  · rw [herm_smul_left, hinv, hz₀v, div_mul_cancel₀ _ hδ]

theorem suTv_mem_of_perp_pair (hσ : IsUnitaryInvolution σ) (hm : 4 ≤ m) {H : Subgroup (SUid σ m)}
    {u w : Fin m → F} (hu : herm σ u u = 0) (hw : herm σ w w = 0) (huw : herm σ u w = 1)
    (hcu : ∀ z, herm σ z z = 0 → herm σ z u = 0 → ∀ c, c + σ c = 0 → suTv hσ z c ∈ H)
    (hcw : ∀ z, herm σ z z = 0 → herm σ z w = 0 → ∀ c, c + σ c = 0 → suTv hσ z c ∈ H)
    {v : Fin m → F} (hv : herm σ v v = 0) {c : F} (hc : c + σ c = 0) : suTv hσ v c ∈ H := by
  have hinv := hσ.invol
  have hwu : herm σ w u = 1 := by rw [herm_conj σ hinv, huw, map_one]
  have hA : ∀ v, herm σ v v = 0 →
      σ (herm σ u v) * herm σ w v + σ (σ (herm σ u v) * herm σ w v) = 0 →
      ∀ c, c + σ c = 0 → suTv hσ v c ∈ H := by
    intro v hv hx c hc
    by_cases hβ : herm σ u v = 0
    · exact hcu v hv (herm_eq_zero_comm σ hinv hβ) c hc
    by_cases hα : herm σ w v = 0
    · exact hcw v hv (herm_eq_zero_comm σ hinv hα) c hc
    set α := herm σ w v with hαdef
    set β := herm σ u v with hβdef
    have hvu : herm σ v u = σ β := herm_conj σ hinv u v
    have hvw : herm σ v w = σ α := herm_conj σ hinv w v
    have hau : herm σ (α • u) u = 0 := by rw [herm_smul_left, hu, mul_zero]
    have haa : herm σ (α • u) (α • u) = 0 := by rw [herm_smul_left, herm_smul_right, hu]; ring
    set b := v - α • u with hb
    have hbw : herm σ b w = 0 := by
      rw [hb, herm_sub_left, herm_smul_left, hvw, huw, mul_one, sub_self]
    have hbb : herm σ b b = 0 := by
      rw [hb]
      simp only [herm_sub_left, herm_sub_right, herm_smul_left, herm_smul_right, hv, hu, hvu,
        ← hβdef]
      rw [map_mul, hinv] at hx
      linear_combination -hx
    have hba : herm σ b (α • u) = σ β * α := by
      rw [hb, herm_smul_right, herm_sub_left, herm_smul_left, hvu, hu]
      ring
    have hx0 : σ β * α ≠ 0 := mul_ne_zero ((map_ne_zero σ).mpr hβ) hα
    have hs : (σ β * α)⁻¹ + σ (σ β * α)⁻¹ = 0 := by
      have hσx : σ (σ β * α) = -(σ β * α) := by linear_combination hx
      rw [map_inv₀, hσx, inv_neg, add_neg_cancel]
    have key : suTv hσ b (σ β * α)⁻¹ • (α • u) = v := by
      rw [suTv_smul hσ hbb hs, hba, inv_mul_cancel₀ hx0, one_smul, hb, add_sub_cancel]
    have h1 := suTv_smul_mem_of_mem hσ haa (hcu _ haa hau) (hcw b hbb hbw _ hs) hc
    rwa [key] at h1
  set α := herm σ w v with hαdef
  set β := herm σ u v with hβdef
  by_cases hx : σ β * α + σ (σ β * α) = 0
  · exact hA v hv hx c hc
  have hβ : β ≠ 0 := by
    rintro h0
    apply hx
    rw [h0, map_zero, zero_mul, map_zero, add_zero]
  have hvu : herm σ v u = σ β := herm_conj σ hinv u v
  have hvw : herm σ v w = σ α := herm_conj σ hinv w v
  have hv0 : herm σ (v - α • u - β • w) (v - α • u - β • w) ≠ 0 := by
    intro h0
    apply hx
    simp only [herm_sub_left, herm_sub_right, herm_smul_left, herm_smul_right, hv, hu, hw, huw,
      hwu, hvu, hvw, ← hαdef, ← hβdef] at h0
    rw [map_mul, hinv]
    linear_combination -h0
  obtain ⟨ε, hε⟩ := hσ.exists_ne
  obtain ⟨z, hz, hzu, hzw, hzv⟩ :=
    exists_iso_perp_pair_herm_eq hσ hm hu hw huw hv0 (ε / σ β)
  have huz : herm σ u z = 0 := herm_eq_zero_comm σ hinv hzu
  have hwz : herm σ w z = 0 := herm_eq_zero_comm σ hinv hzw
  set x := u + z with hxdef
  have hxx : herm σ x x = 0 := by
    rw [hxdef]
    simp only [herm_add_left, herm_add_right, hu, hz, hzu, huz, add_zero]
  have hxu : herm σ x u = 0 := by rw [hxdef, herm_add_left, hu, hzu, add_zero]
  have hD : ε - σ ε ≠ 0 := fun h0 => hε (by linear_combination -h0)
  set s := -(σ β * α + σ (σ β * α)) / (ε - σ ε) with hsdef
  have hs : s + σ s = 0 := by
    have hfix : σ (σ β * α + σ (σ β * α)) = σ β * α + σ (σ β * α) := by
      rw [map_add, hinv, add_comm]
    rw [hsdef, map_div₀, map_neg, hfix, map_sub, hinv]
    have hD' : σ ε - ε ≠ 0 := fun h0 => hD (by linear_combination -h0)
    field_simp
    ring
  have hgH : suTv hσ x s ∈ H := hcu x hxx hxu s hs
  set v' := suTv hσ x s • v with hv'
  have hv'v' : herm σ v' v' = 0 := by rw [hv', herm_smul_smul, hv]
  have hκ : herm σ x v = β + ε / σ β := by rw [hxdef, herm_add_left, hzv]
  have hβ' : herm σ u v' = β := by
    rw [hv', suTv_smul hσ hxx hs, herm_add_right, herm_smul_right, hxdef, herm_add_right, hu,
      huz, add_zero, mul_zero, add_zero]
  have hα' : herm σ w v' = α + s * (β + ε / σ β) := by
    rw [hv', suTv_smul hσ hxx hs, herm_add_right, herm_smul_right, hκ, hxdef, herm_add_right,
      hwu, hwz, add_zero, mul_one]
  have hx' : σ (herm σ u v') * herm σ w v' + σ (σ (herm σ u v') * herm σ w v') = 0 := by
    have hσβ : σ β ≠ 0 := (map_ne_zero σ).mpr hβ
    have hσs : σ s = -s := by linear_combination hs
    rw [hβ', hα', map_mul, map_add, map_mul, hσs, map_add, map_div₀, hinv]
    rw [hsdef]
    simp only [map_mul, hinv]
    field_simp
    ring
  have hmem' := hA v' hv'v' hx' c hc
  have hinvmem : (suTv hσ x s)⁻¹ ∈ H := H.inv_mem hgH
  have h1 := suTv_smul_mem_of_mem hσ hv'v' (fun c hc => hA v' hv'v' hx' c hc) hinvmem hc
  rwa [hv', inv_smul_smul] at h1

end UnitaryCentres

section UnitaryModel

variable {F : Type} [Field F] [Finite F] [CharP F 2] {n : ℕ}

theorem herm_eq_zero_of_commute_kFactsSuProjTv (hF : Nat.card F = (2 ^ n) ^ 2) {m : ℕ}
    (hm : 3 ≤ m) {a b : Fin m → F} (ha0 : a ≠ 0) (ha : herm (unitaryInvolution F 2 n) a a = 0)
    (hb : herm (unitaryInvolution F 2 n) b b = 0)
    (h : Commute (kFactsSuProjTv hF m a 1) (kFactsSuProjTv hF m b 1)) :
    herm (unitaryInvolution F 2 n) a b = 0 := by
  set σ := unitaryInvolution F 2 n with hσdef
  have hσ := isUnitaryInvolution_unitaryInvolution hF
  have hinv := hσ.invol
  have h1 : (1 : F) + σ 1 = 0 := by rw [map_one]; exact CharTwo.add_self_eq_zero 1
  by_contra hab
  set c := herm σ a b with hcdef
  have hb' : herm σ (c⁻¹ • b) (c⁻¹ • b) = 0 := by
    rw [herm_smul_left, herm_smul_right, hb, mul_zero, mul_zero]
  have hab' : herm σ a (c⁻¹ • b) = 1 := by rw [herm_smul_right, ← hcdef, inv_mul_cancel₀ hab]
  obtain ⟨z, hz, haz, hbz'⟩ := exists_norm_one_perp_pair hσ hm ha hb' hab'
  have hbz : herm σ b z = 0 := by
    rw [herm_smul_left] at hbz'
    exact (mul_eq_zero.mp hbz').resolve_left ((map_ne_zero σ).mpr (inv_ne_zero hab))
  have hz0 : z ≠ 0 := by
    rintro rfl
    simp at hz
  have hfa : suTv hσ a 1 • z = z := by
    rw [suTv_smul hσ ha h1, haz, mul_zero, zero_smul, add_zero]
  have hfb : suTv hσ b 1 • z = z := by
    rw [suTv_smul hσ hb h1, hbz, mul_zero, zero_smul, add_zero]
  have hπ : kFactsSuProj hF m (suTv hσ a 1 * suTv hσ b 1) =
      kFactsSuProj hF m (suTv hσ b 1 * suTv hσ a 1) := by
    rw [map_mul, map_mul]
    exact h.eq
  obtain ⟨u, hu⟩ := (kFacts_suProj_eq_iff hF _ _).mp hπ
  have hzu : z = (u : F) • z := by
    have h2 := congrArg (fun M => Matrix.mulVec M z) hu
    rw [← Matrix.mulVec_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, Matrix.mulVec_smul,
      ← smul_def, ← smul_def, mul_smul, mul_smul, hfa, hfb, hfa] at h2
    exact h2
  have hu1 : (u : F) = 1 := by
    have h3 : ((u : F) - 1) • z = 0 := by rw [sub_smul, one_smul, ← hzu, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp h3).resolve_right hz0)
  have hcomm : suTv hσ a 1 * suTv hσ b 1 = suTv hσ b 1 * suTv hσ a 1 := by
    rw [hu1, one_smul, mul_one] at hu
    exact Subtype.ext (Units.ext hu.symm)
  have hb₂ : herm σ (suTv hσ a 1 • b) (suTv hσ a 1 • b) = 0 := by rw [herm_smul_smul, hb]
  have hconj : suTv hσ (suTv hσ a 1 • b) 1 = suTv hσ b 1 := by
    rw [← suTv_conj hσ (suTv hσ a 1) hb h1, hcomm, mul_inv_cancel_right]
  have h4 : suTv hσ (suTv hσ a 1 • b) 1 • a = suTv hσ b 1 • a := by rw [hconj]
  rw [suTv_smul hσ hb₂ h1, suTv_smul hσ hb h1, suTv_smul hσ ha h1, one_mul, one_mul, one_mul,
    herm_add_left, herm_smul_left, ha, mul_zero, add_zero, add_right_inj, smul_add,
    add_eq_left, smul_smul] at h4
  have hba : herm σ b a = σ c := herm_conj σ hinv a b
  rcases smul_eq_zero.mp h4 with h5 | h5
  · rw [hba] at h5
    exact mul_ne_zero ((map_ne_zero σ).mpr hab) hab h5
  · exact ha0 h5

theorem subset_rootBlock_and_ne_of_isUnitaryTransvection {X : Type} [Group X] {E : Set X}
    (hcls : ∃ d₀ : X, E = {g | IsConj d₀ g}) (hZ : Subgroup.center X = ⊥) {s : X} (hs : s ∈ E)
    {m f : ℕ} (hm : 4 ≤ m) (h : IsUnitaryTransvection X m f s) :
    (∀ β, IsBlock E β → s ∈ β → β ⊆ rootBlock E s) ∧ rootBlock E s ≠ E := by
  classical
  obtain ⟨F, _, _, hF, e, hrank⟩ := h
  have : Fintype F := Fintype.ofFinite F
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := 2 * f)
    (by rw [← Nat.card_eq_fintype_card, hF, ← pow_mul, mul_comm])
  set σ := unitaryInvolution F 2 f with hσdef
  have hσ : IsUnitaryInvolution σ := isUnitaryInvolution_unitaryInvolution hF
  have hinv := hσ.invol
  have h1 : (1 : F) + σ 1 = 0 := by rw [map_one]; exact CharTwo.add_self_eq_zero 1
  set π := kFactsSuProj hF m with hπdef
  have hπsurj : Function.Surjective π := kFacts_suProj_surjective hF m
  set ψ : X →* StatedProj (StatedSU m (2 ^ f) F) :=
    e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center X)) with hψdef
  have hψinj : Function.Injective ψ := by
    intro a b hab
    have h1 : QuotientGroup.mk' (Subgroup.center X) a = QuotientGroup.mk' (Subgroup.center X) b :=
      e.injective hab
    rw [QuotientGroup.mk'_eq_mk'] at h1
    obtain ⟨z, hz, hzb⟩ := h1
    rw [hZ, Subgroup.mem_bot] at hz
    rw [hz, mul_one] at hzb
    exact hzb
  have hψsurj : Function.Surjective ψ :=
    e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hcomm : ∀ x y : X, Commute x y ↔ Commute (ψ x) (ψ y) := fun x y =>
    ⟨fun h => h.map ψ, fun h => hψinj (by rw [map_mul, map_mul]; exact h.eq)⟩
  obtain ⟨u, hu0, hu, hψs⟩ := kFacts_su_exists_centre hF hrank
  change ψ s = π (suTv hσ u 1) at hψs
  have hEs : ∀ x, x ∈ E ↔ IsConj s x := by
    obtain ⟨d₀, rfl⟩ := hcls
    intro x
    exact ⟨fun hx => (isConj_comm.mp hs).trans hx, fun hx => (show IsConj d₀ s from hs).trans hx⟩
  have hconjE : ∀ g x, x ∈ E → g * x * g⁻¹ ∈ E := fun g x hx =>
    (hEs _).mpr (((hEs x).mp hx).trans (isConj_iff.mpr ⟨g, rfl⟩))
  have hconjψ : ∀ (g : X) (g' : SUid σ m), ψ g = π g' →
      ψ (g * s * g⁻¹) = π (suTv hσ (g' • u) 1) := by
    intro g g' hg
    rw [map_mul, map_mul, map_inv, hψs, hg, ← map_inv, ← map_mul, ← map_mul,
      suTv_conj hσ g' hu h1]
  have hiso : ∀ g' : SUid σ m, herm σ (g' • u) (g' • u) = 0 := fun g' => by
    rw [herm_smul_smul, hu]
  have hne0 : ∀ g' : SUid σ m, g' • u ≠ 0 := fun g' h0 => hu0 (by
    rw [← inv_smul_smul g' u, h0, smul_zero])
  have hEtr : ∀ x ∈ E, ∃ v, v ≠ 0 ∧ herm σ v v = 0 ∧ ψ x = π (suTv hσ v 1) := by
    intro x hx
    obtain ⟨g, rfl⟩ := isConj_iff.mp ((hEs x).mp hx)
    obtain ⟨g', hg'⟩ := hπsurj (ψ g)
    exact ⟨g' • u, hne0 g', hiso g', hconjψ g g' hg'.symm⟩
  have hcommE : ∀ a b : Fin m → F, a ≠ 0 → herm σ a a = 0 → b ≠ 0 → herm σ b b = 0 →
      (Commute (π (suTv hσ a 1)) (π (suTv hσ b 1)) ↔ herm σ a b = 0) := by
    intro a b ha0 ha _ hb
    refine ⟨herm_eq_zero_of_commute_kFactsSuProjTv hF (by omega) ha0 ha hb, fun hab => ?_⟩
    exact kFacts_suProjTv_comm_of_herm_eq_zero hF ha hb hab h1 h1
  have hroot : ∀ t ∈ E, ∀ c : F, c ≠ 0 → ψ t = π (suTv hσ (c • u) 1) →
      t ∈ rootBlock E s := by
    intro t ht c hc htc
    have hcu0 : c • u ≠ 0 := smul_ne_zero hc hu0
    have hcu : herm σ (c • u) (c • u) = 0 := by
      rw [herm_smul_left, herm_smul_right, hu, mul_zero, mul_zero]
    refine ⟨ht, fun y hy => ?_⟩
    obtain ⟨v, hv0, hv, hyv⟩ := hEtr y hy
    rw [hcomm, hcomm, hyv, htc, hψs, hcommE v _ hv0 hv hcu0 hcu, hcommE v u hv0 hv hu0 hu,
      herm_smul_right, mul_eq_zero, or_iff_right hc]
  have hne : rootBlock E s ≠ E := by
    intro hEq
    obtain ⟨d, hd, hud, -⟩ := exists_cno hσ hu0 hu hu0
    obtain ⟨g, hg⟩ := hψsurj (π (suTv hσ d 1))
    have hx : g * s * g⁻¹ ∈ E := hconjE g s hs
    rw [← hEq] at hx
    have h2 := (hx.2 s hs).mpr (Commute.refl s)
    rw [hcomm, hψs, hconjψ g _ hg, hcommE u _ hu0 hu (hne0 _) (hiso _),
      suTv_smul hσ hd h1, herm_add_right, herm_smul_right, hu, zero_add, one_mul,
      herm_conj σ hinv u d] at h2
    exact mul_ne_zero ((map_ne_zero σ).mpr hud) hud h2
  refine ⟨fun β hβ hsβ t htβ => ?_, hne⟩
  have htE := hβ.1 htβ
  obtain ⟨w, hw0, hw, htw⟩ := hEtr t htE
  by_cases hprop : ∃ c : F, w = c • u
  · obtain ⟨c, rfl⟩ := hprop
    have hc : c ≠ 0 := by
      rintro rfl
      exact hw0 (zero_smul _ _)
    exact hroot t htE c hc htw
  exfalso
  push Not at hprop
  have huw' : ∀ c : F, u ≠ c • w := by
    intro c huc
    have hc : c ≠ 0 := by
      rintro rfl
      exact hu0 (by rw [huc, zero_smul])
    exact hprop c⁻¹ (by rw [huc, smul_smul, inv_mul_cancel₀ hc, one_smul])
  have hCN : ∀ x ∈ β, ∀ g : X, Commute g x → g ∈ Subgroup.normalizer β := by
    intro x hx g hg
    by_contra hgN
    refine Set.disjoint_left.mp (hβ.2.2.2 g hgN) hx ⟨x, hx, ?_⟩
    change g * x * g⁻¹ = x
    rw [hg.eq, mul_inv_cancel_right]
  have hNmem : ∀ g ∈ Subgroup.normalizer β, ∀ x ∈ β, g * x * g⁻¹ ∈ β := by
    intro g hg x hx
    have h2 := Subgroup.mem_normalizer_iff_conj_image_eq.mp hg
    rw [← h2]
    exact ⟨x, hx, rfl⟩
  set H : Subgroup (StatedProj (StatedSU m (2 ^ f) F)) := (Subgroup.normalizer β).map ψ
  set H' : Subgroup (SUid σ m) := H.comap π
  have hcen : ∀ x ∈ β, ∀ v, herm σ v v = 0 → ψ x = π (suTv hσ v 1) → ∀ z, herm σ z z = 0 →
      herm σ z v = 0 → ∀ c, c + σ c = 0 → suTv hσ z c ∈ H' := by
    intro x hx v hv hxv z hz hzv c hc
    obtain ⟨g, hg⟩ := hψsurj (π (suTv hσ z c))
    refine ⟨g, hCN x hx g ?_, hg⟩
    rw [hcomm, hxv, hg]
    exact kFacts_suProjTv_comm_of_herm_eq_zero hF hz hv hzv hc h1
  have hall : ∀ z, herm σ z z = 0 → ∀ c, c + σ c = 0 → suTv hσ z c ∈ H' := by
    obtain ⟨u', hu', hu'u, hcu'⟩ : ∃ u', herm σ u' u' = 0 ∧ herm σ u u' ≠ 0 ∧
        ∀ z, herm σ z z = 0 → herm σ z u' = 0 → ∀ c, c + σ c = 0 → suTv hσ z c ∈ H' := by
      by_cases huw : herm σ u w = 0
      · obtain ⟨d, hd, hwd, hud⟩ := exists_iso_perp hσ hw0 hw hu
          (herm_eq_zero_comm σ hinv huw) huw'
        have hdH : suTv hσ d 1 ∈ H' :=
          hcen t htβ w hw htw d hd (herm_eq_zero_comm σ hinv hwd) 1 h1
        obtain ⟨g, hgN, hg⟩ := hdH
        refine ⟨suTv hσ d 1 • u, hiso _, ?_, hcen _ (hNmem g hgN s hsβ) _ (hiso _)
          (hconjψ g _ hg)⟩
        rw [suTv_smul hσ hd h1, herm_add_right, herm_smul_right, hu, zero_add, one_mul,
          herm_conj σ hinv u d]
        exact mul_ne_zero ((map_ne_zero σ).mpr hud) hud
      · exact ⟨w, hw, huw, hcen t htβ w hw htw⟩
    set k := herm σ u u' with hk
    have hw₁ : herm σ (k⁻¹ • u') (k⁻¹ • u') = 0 := by
      rw [herm_smul_left, herm_smul_right, hu', mul_zero, mul_zero]
    have huw₁ : herm σ u (k⁻¹ • u') = 1 := by rw [herm_smul_right, ← hk, inv_mul_cancel₀ hu'u]
    intro z hz c hc
    refine suTv_mem_of_perp_pair hσ hm hu hw₁ huw₁ (hcen s hsβ u hu hψs) ?_ hz hc
    intro z' hz' hz'w c' hc'
    refine hcu' z' hz' ?_ c' hc'
    rw [herm_smul_right] at hz'w
    exact (mul_eq_zero.mp hz'w).resolve_left (inv_ne_zero hu'u)
  have hT : T σ m ≤ H' := by
    refine (Subgroup.closure_le H').2 ?_
    rintro g ⟨a, c, ha, hc, hg⟩
    have hga : g = suTv hσ a c := ext_smul σ fun v => by rw [hg v, suTv_smul hσ ha hc]
    rw [hga]
    exact hall a ha c hc
  have hH'top : H' = ⊤ := by
    rw [eq_top_iff, ← T_eq_top hσ (by omega) (fun h3 => absurd h3 (by omega))]
    exact hT
  have hN : ∀ g : X, g ∈ Subgroup.normalizer β := fun g => by
    obtain ⟨g', hg'⟩ := hπsurj (ψ g)
    have hg'H : g' ∈ H' := hH'top ▸ Subgroup.mem_top g'
    obtain ⟨g'', hg''N, hg''⟩ := hg'H
    rwa [← hψinj (hg''.trans hg')]
  refine hβ.2.2.1 (hβ.1.antisymm fun x hx => ?_)
  obtain ⟨g, rfl⟩ := isConj_iff.mp ((hEs x).mp hx)
  exact hNmem g (hN g) s hsβ

end UnitaryModel

end CFSG.OddTranspositions.PartFour
