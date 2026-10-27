module

public import CFSG.Quasithin.Background.E11Stmt
public import CFSG.Quasithin.Background.G118Basic

public section

namespace CFSG.Quasithin

open CFSG.Open

namespace G11

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

namespace G118

theorem card_linearEquiv_finrank_two {F U : Type*} [Field F] [Fintype F] [AddCommGroup U]
    [Module F U] (hk : Module.finrank F U = 2) :
    Nat.card (U ≃ₗ[F] U) = (Fintype.card F ^ 2 - 1) * (Fintype.card F ^ 2 - Fintype.card F) := by
  have : Module.Finite F U := Module.finite_of_finrank_pos (by omega)
  let b : Module.Basis (Fin 2) F U := Module.finBasisOfFinrankEq F U hk
  let e : (U ≃ₗ[F] U) ≃* Matrix.GeneralLinearGroup (Fin 2) F :=
    ((LinearMap.GeneralLinearGroup.generalLinearEquiv F U).symm.trans
      (Matrix.GeneralLinearGroup.toLin' b).symm)
  rw [Nat.card_congr e.toEquiv, Matrix.card_GL_field]
  simp [Fin.prod_univ_two]

theorem le_two_of_dvd_six_of_pow {n : ℕ} (hn : ∃ a : ℕ, n = 2 ^ a) (hd : n ∣ 6) : n ≤ 2 := by
  obtain ⟨a, rfl⟩ := hn
  by_contra h
  push Not at h
  have h4 : 4 ∣ 2 ^ a := by
    have : 2 ≤ a := by
      by_contra ha
      push Not at ha
      interval_cases a <;> simp at h
    exact (pow_dvd_pow 2 this)
  have : 4 ∣ 6 := h4.trans hd
  omega

section K2

variable [Finite V] {B : LinearMap.BilinForm (ZMod 2) V} {Γ : Subgroup (GLV V)} {v₁ : V}
  {W : Submodule (ZMod 2) V} {X X₀ L : Subgroup (GLV V)} {I : Submodule (ZMod 2) V}

theorem ker_sub_one_eq_of_mem (D : E11Data (normalClosure Γ L) I)
    (hd : Module.finrank (ZMod 2) V = 2 * Module.finrank (ZMod 2) I)
    (hI0 : 0 < Module.finrank (ZMod 2) I) {y : GLV V}
    (hyc : ∀ h ∈ normalClosure Γ L, y * h = h * y) (hyI : ∀ i ∈ I, y i = i) (hy1 : y ≠ 1) :
    ∀ v : V, y v = v ↔ v ∈ I := by
  set M : Submodule (ZMod 2) V := LinearMap.ker (y.toLinearMap - LinearMap.id) with hM
  have hmemM : ∀ v : V, v ∈ M ↔ y v = v := fun v => by
    simp [hM, LinearMap.mem_ker, sub_eq_zero]
  have hMinv : Invariant (normalClosure Γ L) M := by
    intro h hh v hv
    rw [hmemM] at hv ⊢
    have := congrArg (fun g : GLV V => g v) (hyc h hh)
    have h2 : y (h v) = h (y v) := this
    rw [h2, hv]
  have hIM : I ≤ M := fun i hi => (hmemM i).2 (hyI i hi)
  have hMtop : M < ⊤ := by
    refine lt_top_iff_ne_top.2 fun h => hy1 ?_
    ext v
    exact (hmemM v).1 (h ▸ Submodule.mem_top)
  obtain ⟨S, -, hS⟩ := D.exists_subspace M hMinv
  have h1 : Module.finrank (ZMod 2) M < Module.finrank (ZMod 2) V :=
    Submodule.finrank_lt hMtop.ne
  have h2 : Module.finrank (ZMod 2) I ≤ Module.finrank (ZMod 2) M := Submodule.finrank_mono hIM
  have h3 : 0 < Module.finrank (ZMod 2) M := lt_of_lt_of_le hI0 h2
  have hS1 : Module.finrank D.F S = 1 := by
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
    · have : Module.finrank D.F S = 0 := by omega
      rw [this, zero_mul] at hS
      omega
    · have : 2 * Module.finrank (ZMod 2) I ≤ Module.finrank D.F S * Module.finrank (ZMod 2) I :=
        Nat.mul_le_mul_right _ hgt
      omega
  have hMI : M = I := by
    symm
    refine Submodule.eq_of_le_of_finrank_eq hIM ?_
    rw [← hS, hS1, one_mul]
  intro v
  rw [← hmemM, hMI]

theorem range_sub_one_eq_of_mem (D : E11Data (normalClosure Γ L) I)
    (hd : Module.finrank (ZMod 2) V = 2 * Module.finrank (ZMod 2) I)
    (hI0 : 0 < Module.finrank (ZMod 2) I) {y : GLV V} (hy2 : y * y = 1)
    (hyc : ∀ h ∈ normalClosure Γ L, y * h = h * y) (hyI : ∀ i ∈ I, y i = i) (hy1 : y ≠ 1) :
    LinearMap.range (y.toLinearMap - LinearMap.id) = I := by
  have hker := ker_sub_one_eq_of_mem D hd hI0 hyc hyI hy1
  have hker' : LinearMap.ker (y.toLinearMap - LinearMap.id) = I := by
    ext v
    rw [LinearMap.mem_ker, ← hker v]
    simp [sub_eq_zero]
  have hle : LinearMap.range (y.toLinearMap - LinearMap.id) ≤ I := by
    rintro _ ⟨v, rfl⟩
    rw [← hker]
    have h2 : ∀ u : V, y (y u) = u := fun u => congrArg (fun g : GLV V => g u) hy2
    have hdouble : ∀ x : V, x + x = 0 := fun x => by
      rw [← two_smul (ZMod 2) x]
      have : (2 : ZMod 2) = 0 := by decide
      rw [this, zero_smul]
    show y (y v - v) = y v - v
    rw [map_sub, h2]
    have h3 := eq_neg_of_add_eq_zero_left (hdouble (y v - v))
    rw [neg_sub] at h3
    exact h3.symm
  have hrn := LinearMap.finrank_range_add_finrank_ker (y.toLinearMap - LinearMap.id)
  rw [hker'] at hrn
  refine Submodule.eq_of_le_of_finrank_eq hle ?_
  omega

theorem isPGroup_centralizerIn (h108 : G108Hyp B Γ v₁ W X X₀ L) :
    IsPGroup 2 ↥(centralizerIn X (normalClosure Γ L)) := fun g => ⟨1, by
  have hgX : (g : GLV V) ∈ X := (mem_centralizerIn_iff.1 g.2).1
  have := h108.X_sq g hgX
  rw [pow_one, pow_two]
  exact Subtype.ext this⟩

omit [Finite V] in
theorem centralizerIn_le_centralizer :
    centralizerIn X (normalClosure Γ L) ≤ Subgroup.centralizer (normalClosure Γ L : Set (GLV V)) :=
  fun _ hy => Subgroup.mem_centralizer_iff.2 fun h hh =>
    ((mem_centralizerIn_iff.1 hy).2 h hh).symm

theorem card_centralizerIn_le_two_of_card_two (h108 : G108Hyp B Γ v₁ W X X₀ L)
    (D : E11Data (normalClosure Γ L) I) (hk : Module.finrank D.F D.U = 2)
    (hF : Nat.card D.F = 2) : Nat.card ↥(centralizerIn X (normalClosure Γ L)) ≤ 2 := by
  let _ : Fintype D.F := Fintype.ofFinite D.F
  have hdvd : Nat.card ↥(centralizerIn X (normalClosure Γ L)) ∣
      Nat.card ↥(Subgroup.centralizer (normalClosure Γ L : Set (GLV V))) :=
    Subgroup.card_dvd_of_le centralizerIn_le_centralizer
  have hC₀ : Nat.card ↥(Subgroup.centralizer (normalClosure Γ L : Set (GLV V))) = 6 := by
    rw [Nat.card_congr D.θ.toEquiv, card_linearEquiv_finrank_two hk]
    have : Fintype.card D.F = 2 := by rw [← Nat.card_eq_fintype_card, hF]
    rw [this]
    norm_num
  rw [hC₀] at hdvd
  exact le_two_of_dvd_six_of_pow (isPGroup_centralizerIn h108).exists_card_eq hdvd

theorem ker_eq_of_mem_centralizerIn (h108 : G108Hyp B Γ v₁ W X X₀ L)
    (hI : G116Props B Γ v₁ X L I) (D : E11Data (normalClosure Γ L) I)
    (hd : Module.finrank (ZMod 2) V = 2 * Module.finrank (ZMod 2) I) {y : GLV V}
    (hy : y ∈ centralizerIn X (normalClosure Γ L)) (hy1 : y ≠ 1) : ∀ v : V, y v = v ↔ v ∈ I :=
  ker_sub_one_eq_of_mem D hd (Module.finrank_pos_iff_exists_ne_zero.2
    (by
      obtain ⟨i, hi, hi0⟩ := (Submodule.ne_bot_iff I).1 (isIrr_I h108 hI).ne_bot
      exact ⟨⟨i, hi⟩, fun h => hi0 (congrArg Subtype.val h)⟩))
    (mem_centralizerIn_iff.1 hy).2 (fixes_of_mem_centralizerIn h108 hI hy) hy1

end K2

end G118

end G11

end CFSG.Quasithin
