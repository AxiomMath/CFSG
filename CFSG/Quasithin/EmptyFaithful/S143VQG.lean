module

public import CFSG.Quasithin.EmptyFaithful.S143VQ8
public import CFSG.Quasithin.EmptyFaithful.S143VAut

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique

namespace S143V

variable {G : Type} [Group G] {T M L : Subgroup G}

@[expose] noncomputable def piU (D : HatModel T M) : ↥(uOfL22 T M) →* Multiplicative D.V where
  toFun u := Multiplicative.ofAdd (D.π (u : G))
  map_one' := by
    show Multiplicative.ofAdd (D.π ((1 : ↥(uOfL22 T M)) : G)) = 1
    rw [Subgroup.coe_one, D.π_one]
    rfl
  map_mul' u v := by
    show Multiplicative.ofAdd (D.π ((u * v : ↥(uOfL22 T M)) : G)) =
      Multiplicative.ofAdd (D.π (u : G)) * Multiplicative.ofAdd (D.π (v : G))
    rw [Subgroup.coe_mul, D.π_mul _ u.2 _ v.2, ofAdd_add]

theorem piU_apply (D : HatModel T M) (u : ↥(uOfL22 T M)) :
    piU D u = Multiplicative.ofAdd (D.π (u : G)) := rfl

theorem mulV_self (D : HatModel T M) (w : Multiplicative D.V) : w * w = 1 := by
  show Multiplicative.ofAdd (Multiplicative.toAdd w + Multiplicative.toAdd w) = 1
  have : ∀ a : D.V, a + a = 0 := by
    intro a
    calc a + a = (1 + 1 : ZMod 2) • a := by rw [add_smul, one_smul]
      _ = 0 := by
        have h2 : (1 + 1 : ZMod 2) = 0 := by decide
        rw [h2, zero_smul]
  rw [this]
  rfl

section Orth

variable {W : Type*} [CommGroup W] {U₁ U₂ : Subgroup W}

open scoped Classical in
theorem quadPolar_quadOf_orth (hinf : U₁ ⊓ U₂ = ⊥) (hsup : U₁ ⊔ U₂ = ⊤)
    (φ₁ : ↥U₁ ≃* S1417.F2sq) (φ₂ : ↥U₂ ≃* S1417.F2sq) {y z : W} (hy : y ∈ U₁) (hz : z ∈ U₂) :
    quadPolar (S1417.quadOf hinf hsup φ₁ φ₂) y z = 0 := by
  have h1 := S1417.quadOf_mul hinf hsup φ₁ φ₂ hy hz
  have h2 := S1417.quadOf_mul hinf hsup φ₁ φ₂ hy U₂.one_mem
  have h3 := S1417.quadOf_mul hinf hsup φ₁ φ₂ U₁.one_mem hz
  rw [mul_one] at h2
  rw [one_mul] at h3
  unfold quadPolar
  rw [h1, h2, h3]
  simp only [ite_true]
  generalize (if y = 1 then (0 : ZMod 2) else 1) = a
  generalize (if z = 1 then (0 : ZMod 2) else 1) = b
  revert a b
  decide

end Orth

section Main

variable [Finite G]
variable (h : Hyp1281Two G T M L) (hZU : centerOf (uOfL22 T M) = quasithinOmegaOneCenter T)
  (D : HatModel T M)

include h hZU in
theorem isQ8Sq_of_plus (hd : Module.finrank (ZMod 2) D.V = 4)
    (hplus : CFSG.GroupTheory.WeirSylow.IsPlusType
      (G11.P4InspOrth.p4insporth_quad (f := D.B) (q := qhat D) (fun x y => qhat_add h hZU D x y))) :
    IsQ8Sq ↥(uOfL22 T M) := by
  classical
  set θ := theta h hZU D with hθ
  let Q : Multiplicative D.V → ZMod 2 := fun w => qhat D (Multiplicative.toAdd w)
  have hQ : Q = fun w => qtilde h hZU D (θ.symm w) := by
    funext w
    show qhat D (Multiplicative.toAdd w) = qhat D (Multiplicative.toAdd (θ (θ.symm w)))
    rw [MulEquiv.apply_symm_apply]
  have hQf : IsQuadraticFormOn Q := by
    rw [hQ]
    exact S1417.isQuadratic_comp θ.symm (qtilde_isQuadraticFormOn h hZU D)
  have hQn : IsNondegQuadratic Q := by
    rw [hQ]
    exact S1417.isNondeg_comp θ.symm (qtilde_isNondeg h hZU D)
  have hQp : IsPlusType Q := by
    rw [hQ]
    exact S1417.isPlus_comp θ.symm (qtilde_isPlusType h hZU D hd hplus)
  have hcard : Nat.card (Multiplicative D.V) = 16 := by
    rw [Nat.card_congr Multiplicative.toAdd, natCard_eq_two_pow_finrank, hd]
    norm_num
  obtain ⟨U₁, U₂, hinf, hsup, φ₁, φ₂, hQd⟩ :=
    S153.exists_decomposition_of_plusType (mulV_self D) hcard hQf hQn hQp
  have hQπ : ∀ x : ↥(uOfL22 T M), Q (piU D x) = if (x : G) ^ 2 = 1 then 0 else 1 := fun x =>
    qhat_π h hZU D x.2
  obtain ⟨z, hzZ, hz1, -, hall⟩ := exists_zgen_sq h
  have hzC : z ∈ centerOf (uOfL22 T M) := h.omegaOneCenter_le_centerOf_uOfL22 hzZ
  let z' : ↥(uOfL22 T M) := ⟨z, hzC.1⟩
  have hz1' : z' ≠ 1 := fun he => hz1 (congrArg Subtype.val he)
  have hzc : ∀ x : ↥(uOfL22 T M), x * z' = z' * x := fun x =>
    Subtype.ext (Subgroup.mem_centralizer_iff.mp hzC.2 (x : G) x.2)
  have hker : ∀ x : ↥(uOfL22 T M), piU D x = 1 ↔ (x = 1 ∨ x = z') := by
    intro x
    rw [piU_apply, ofAdd_eq_one, D.π_eq_zero_iff x.2, hZU]
    constructor
    · intro hx
      rcases hall _ hx with h1 | h1
      · exact Or.inl (Subtype.ext h1)
      · exact Or.inr (Subtype.ext h1)
    · rintro (hx | hx)
      · have : (x : G) = 1 := by rw [hx]; rfl
        rw [this]
        exact (quasithinOmegaOneCenter T).one_mem
      · have : (x : G) = z := by rw [hx]
        rw [this]
        exact hzZ
  have hπ : Function.Surjective (piU D) := by
    intro w
    obtain ⟨u, hu, hπu⟩ := D.π_surj (Multiplicative.toAdd w)
    refine ⟨⟨u, hu⟩, ?_⟩
    rw [piU_apply]
    show Multiplicative.ofAdd (D.π u) = w
    rw [hπu]
    rfl
  have hU₁ : Nat.card U₁ = 4 := by
    rw [Nat.card_congr φ₁.toEquiv]
    exact S1417.card_F2sq
  have hU₂ : Nat.card U₂ = 4 := by
    rw [Nat.card_congr φ₂.toEquiv]
    exact S1417.card_F2sq
  have hsq_ne : ∀ x : ↥(uOfL22 T M), piU D x ≠ 1 → (piU D x ∈ U₁ ∨ piU D x ∈ U₂) →
      x ^ 2 ≠ 1 := by
    intro x hne hmem hx2
    have hx2' : (x : G) ^ 2 = 1 := by simpa using congrArg Subtype.val hx2
    have h1 : Q (piU D x) = 0 := by
      rw [hQπ]
      simp [hx2']
    have h2 : S1417.quadOf hinf hsup φ₁ φ₂ (piU D x) = 1 :=
      (S1417.quadOf_eq_one_iff hinf hsup φ₁ φ₂ (w := piU D x)).mpr ⟨hmem, hne⟩
    rw [hQd] at h1
    rw [h1] at h2
    exact zero_ne_one h2
  have horth : ∀ a b : ↥(uOfL22 T M), piU D a ∈ U₁ → piU D b ∈ U₂ → a * b = b * a := by
    intro a b ha hb
    have hpol := quadPolar_quadOf_orth hinf hsup φ₁ φ₂ ha hb
    have hpol' : quadPolar Q (piU D a) (piU D b) = 0 := by
      unfold quadPolar at hpol ⊢
      simp only [hQd]
      exact hpol
    have hB : D.B (D.π (a : G)) (D.π (b : G)) = 0 := by
      have e : quadPolar Q (piU D a) (piU D b) = D.B (D.π (a : G)) (D.π (b : G)) := by
        show qhat D (Multiplicative.toAdd (piU D a * piU D b)) + qhat D (D.π (a : G)) +
          qhat D (D.π (b : G)) = _
        rw [toAdd_mul]
        show qhat D (D.π (a : G) + D.π (b : G)) + _ + _ = _
        rw [qhat_add h hZU D]
        exact zmod_two_aux _ _ _
      rw [← e]
      exact hpol'
    have hc : (a : G) * b * (a : G)⁻¹ * (b : G)⁻¹ = 1 := (D.B_spec _ a.2 _ b.2).mp hB
    have : (a : G) * b = b * a := by
      calc (a : G) * b = ((a : G) * b * (a : G)⁻¹ * (b : G)⁻¹) * b * a := by group
        _ = b * a := by rw [hc]; group
    exact Subtype.ext this
  exact isQ8Sq_of_orthogonal_planes (piU D) hπ hz1' hzc hker (mulV_self D) U₁ U₂ hinf hsup hU₁ hU₂
    (fun x hx hne => hsq_ne x hne (Or.inl hx)) (fun x hx hne => hsq_ne x hne (Or.inr hx)) horth

end Main

end S143V

end CFSG.Quasithin
