module

public import CFSG.Quasithin.Background.SimsG4Defs

public section

namespace CFSG.Quasithin.SimsG4

variable {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V]

theorem mul_inv_apply (g : V ≃ₗ[F] V) (y : V) : g (g⁻¹ y) = y :=
  congrArg (fun e : V ≃ₗ[F] V => e y) (mul_inv_cancel g)

theorem inv_mul_apply (g : V ≃ₗ[F] V) (y : V) : g⁻¹ (g y) = y :=
  congrArg (fun e : V ≃ₗ[F] V => e y) (inv_mul_cancel g)

theorem transv_mul_self [CharP F 2] (g : V ≃ₗ[F] V) (hg : IsTransv g) : g * g = 1 := by
  obtain ⟨-, h2⟩ := hg
  have hvv : ∀ v : V, v + v = 0 := fun v => by
    rw [← two_smul F v, CharTwo.two_eq_zero, zero_smul]
  apply LinearEquiv.ext
  intro x
  have hx := LinearMap.congr_fun h2 x
  simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.zero_apply,
    LinearEquiv.coe_coe, map_sub] at hx
  have h3 : g (g x) + x = 0 := by
    calc g (g x) + x = (g (g x) - g x - (g x - x)) + (g x + g x) := by abel
      _ = 0 := by rw [hx, hvv (g x), add_zero]
  calc g (g x) = g (g x) + (x + x) := by rw [hvv x, add_zero]
    _ = (g (g x) + x) + x := by abel
    _ = x := by rw [h3, zero_add]

theorem transv_ne_one (g : V ≃ₗ[F] V) (hg : IsTransv g) : g ≠ 1 := by
  rintro rfl
  obtain ⟨h1, -⟩ := hg
  have h0 : ((1 : V ≃ₗ[F] V) : V →ₗ[F] V) - LinearMap.id = 0 := by
    apply LinearMap.ext
    intro x
    simp
  rw [h0, LinearMap.range_zero, finrank_bot] at h1
  exact zero_ne_one h1

theorem isTransv_conj (g d : V ≃ₗ[F] V) (hd : IsTransv d) : IsTransv (g * d * g⁻¹) := by
  obtain ⟨h1, h2⟩ := hd
  have hkey : ((g * d * g⁻¹ : V ≃ₗ[F] V) : V →ₗ[F] V) - LinearMap.id
      = ((g : V →ₗ[F] V) ∘ₗ ((d : V →ₗ[F] V) - LinearMap.id)) ∘ₗ
          ((g⁻¹ : V ≃ₗ[F] V) : V →ₗ[F] V) := by
    apply LinearMap.ext
    intro x
    simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.id_apply,
      LinearEquiv.coe_coe, LinearEquiv.mul_apply, map_sub, mul_inv_apply]
  refine ⟨?_, ?_⟩
  · rw [hkey, LinearMap.range_comp_of_range_eq_top _ (LinearEquiv.range (g⁻¹ : V ≃ₗ[F] V)),
      LinearMap.range_comp, LinearEquiv.finrank_map_eq]
    exact h1
  · rw [hkey]
    apply LinearMap.ext
    intro x
    have hMM := LinearMap.congr_fun h2 ((g⁻¹ : V ≃ₗ[F] V) x)
    simp only [LinearMap.comp_apply, LinearMap.zero_apply] at hMM
    simp only [LinearMap.comp_apply, LinearMap.zero_apply, LinearEquiv.coe_coe, inv_mul_apply]
    rw [hMM, map_zero]

theorem conj_mem_transvSet {G₀ : Subgroup (V ≃ₗ[F] V)} {g : V ≃ₗ[F] V} (hg : g ∈ G₀)
    {d : V ≃ₗ[F] V} (hd : d ∈ transvSet G₀) : g * d * g⁻¹ ∈ transvSet G₀ :=
  ⟨G₀.mul_mem (G₀.mul_mem hg hd.1) (G₀.inv_mem hg), isTransv_conj g d hd.2⟩

theorem transvGen_le (G₀ : Subgroup (V ≃ₗ[F] V)) : transvGen G₀ ≤ G₀ :=
  (Subgroup.closure_le G₀).mpr fun _ hd => hd.1

theorem conj_mem_transvGen {G₀ : Subgroup (V ≃ₗ[F] V)} {g : V ≃ₗ[F] V} (hg : g ∈ G₀)
    {x : V ≃ₗ[F] V} (hx : x ∈ transvGen G₀) : g * x * g⁻¹ ∈ transvGen G₀ := by
  have hsub : transvSet G₀ ⊆
      ((transvGen G₀).comap (MulAut.conj g).toMonoidHom : Set (V ≃ₗ[F] V)) :=
    fun d hd => Subgroup.subset_closure (conj_mem_transvSet hg hd)
  exact ((Subgroup.closure_le _).mpr hsub) hx

theorem core_trivial [Finite V] (G₀ : Subgroup (V ≃ₗ[F] V)) (hirr : IsIrredOnV G₀)
    (heven : Even (Nat.card V)) (P : Subgroup (V ≃ₗ[F] V)) (hP2 : IsPGroup 2 P)
    (hPG : ∀ g ∈ G₀, ∀ h ∈ P, g * h * g⁻¹ ∈ P) : P = ⊥ := by
  let W : Submodule F V :=
    { carrier := {v | ∀ h ∈ P, h v = v}
      add_mem' := by
        intro a b ha hb
        show ∀ h ∈ P, h (a + b) = a + b
        intro h hh
        have ha' : ∀ h ∈ P, h a = a := ha
        have hb' : ∀ h ∈ P, h b = b := hb
        rw [map_add, ha' h hh, hb' h hh]
      zero_mem' := by
        show ∀ h ∈ P, h 0 = 0
        intro h _
        exact map_zero h
      smul_mem' := by
        intro c v hv
        show ∀ h ∈ P, h (c • v) = c • v
        intro h hh
        have hv' : ∀ h ∈ P, h v = v := hv
        rw [map_smul, hv' h hh] }
  have hcount := IsPGroup.card_modEq_card_fixedPoints (α := V) hP2
  have hex : ∃ v : V, v ≠ 0 ∧ ∀ h ∈ P, h v = v := by
    by_contra hcon
    push Not at hcon
    have hfix : MulAction.fixedPoints ↥P V = {0} := by
      ext v
      rw [Set.mem_singleton_iff]
      constructor
      · intro hv
        by_contra hv0
        obtain ⟨h, hh, hne⟩ := hcon v hv0
        exact hne (MulAction.mem_fixedPoints.mp hv ⟨h, hh⟩)
      · rintro rfl
        exact MulAction.mem_fixedPoints.mpr fun m => map_zero (m : V ≃ₗ[F] V)
    rw [hfix] at hcount
    have h1 : Nat.card (↥({0} : Set V)) = 1 := by simp
    rw [h1] at hcount
    have h2 := Nat.even_iff.mp heven
    unfold Nat.ModEq at hcount
    omega
  obtain ⟨v, hv0, hvfix⟩ := hex
  have hWne : W ≠ ⊥ := by
    intro hbot
    have hvW : v ∈ W := hvfix
    rw [hbot, Submodule.mem_bot] at hvW
    exact hv0 hvW
  have hWinv : ∀ g ∈ G₀, ∀ w ∈ W, g w ∈ W := by
    intro g hg w hw
    have hw' : ∀ h ∈ P, h w = w := hw
    show ∀ h ∈ P, h (g w) = g w
    intro h hh
    have hc := hPG g⁻¹ (G₀.inv_mem hg) h hh
    rw [inv_inv] at hc
    have e1 : (g⁻¹ * h * g) w = w := hw' _ hc
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply] at e1
    calc h (g w) = g (g⁻¹ (h (g w))) := (mul_inv_apply g _).symm
      _ = g w := by rw [e1]
  rcases hirr W hWinv with hbot | htop
  · exact absurd hbot hWne
  · rw [eq_bot_iff]
    intro h hh
    rw [Subgroup.mem_bot]
    apply LinearEquiv.ext
    intro x
    have hx : x ∈ W := by rw [htop]; exact Submodule.mem_top
    have hx' : ∀ h ∈ P, h x = x := hx
    exact hx' h hh

theorem sq_eq_one_of_comm (S : Set (V ≃ₗ[F] V)) (hS : ∀ d ∈ S, d * d = 1)
    (hcomm : ∀ a ∈ Subgroup.closure S, ∀ b ∈ Subgroup.closure S, a * b = b * a) :
    ∀ x ∈ Subgroup.closure S, x * x = 1 := by
  intro x hx
  induction hx using Subgroup.closure_induction with
  | mem x hx => exact hS x hx
  | one => exact mul_one 1
  | mul x y hx hy ihx ihy =>
    have hyx := hcomm x hx y hy
    calc x * y * (x * y) = x * (y * x) * y := by simp only [mul_assoc]
      _ = x * (x * y) * y := by rw [← hyx]
      _ = (x * x) * (y * y) := by simp only [mul_assoc]
      _ = 1 := by rw [ihx, ihy, mul_one]
  | inv x hx ihx =>
    calc x⁻¹ * x⁻¹ = (x * x)⁻¹ := (mul_inv_rev x x).symm
      _ = 1 := by rw [ihx, inv_one]

theorem finite_even_card [Finite F] [CharP F 2] (hdim : Module.finrank F V = 4) :
    Finite V ∧ Even (Nat.card V) := by
  have hfinV : Module.Finite F V := Module.finite_of_finrank_pos (by rw [hdim]; norm_num)
  haveI : Finite V := Module.finite_of_finite (R := F) (M := V)
  refine ⟨inferInstance, ?_⟩
  letI := Fintype.ofFinite F
  obtain ⟨n, -, hn⟩ := FiniteField.card F 2
  have hF : Even (Nat.card F) := by
    rw [Nat.card_eq_fintype_card, hn]
    exact Nat.even_pow.mpr ⟨even_two, n.ne_zero⟩
  rw [Module.natCard_eq_pow_finrank (K := F), hdim]
  exact hF.pow_of_ne_zero (by norm_num)

theorem advSet_nonempty [Finite F] [CharP F 2] (hdim : Module.finrank F V = 4)
    (G₀ : Subgroup (V ≃ₗ[F] V)) (hirr : IsIrredOnV G₀) {d : V ≃ₗ[F] V}
    (hd : d ∈ transvSet G₀) : (advSet G₀ d).Nonempty := by
  obtain ⟨hfin, heven⟩ := finite_even_card (V := V) hdim
  by_contra hcon
  have hcomm : ∀ e ∈ transvSet G₀, e * d = d * e := by
    intro e he
    by_contra hne
    exact hcon ⟨e, he, hne⟩
  set S : Set (V ≃ₗ[F] V) := {x | ∃ g ∈ G₀, x = g * d * g⁻¹} with hS
  have hSD : S ⊆ transvSet G₀ := by
    rintro x ⟨g, hg, rfl⟩
    exact conj_mem_transvSet hg hd
  have hScomm : ∀ x ∈ S, ∀ e ∈ transvSet G₀, e * x = x * e := by
    rintro x ⟨g, hg, rfl⟩ e he
    have h1 := hcomm (g⁻¹ * e * g⁻¹⁻¹) (conj_mem_transvSet (G₀.inv_mem hg) he)
    rw [inv_inv] at h1
    calc e * (g * d * g⁻¹) = g * ((g⁻¹ * e * g) * d) * g⁻¹ := by group
      _ = g * (d * (g⁻¹ * e * g)) * g⁻¹ := by rw [h1]
      _ = g * d * g⁻¹ * e := by group
  have hcl : ∀ a ∈ Subgroup.closure S, ∀ b ∈ Subgroup.closure S, a * b = b * a := by
    have hle : Subgroup.closure S ≤ Subgroup.centralizer S := by
      rw [Subgroup.closure_le]
      intro x hx y hy
      exact hScomm x hx y (hSD hy)
    intro a ha b hb
    have hcen : Subgroup.closure S ≤ Subgroup.centralizer (Subgroup.closure S : Set _) := by
      rw [Subgroup.centralizer_closure]
      exact hle
    exact hcen hb a ha
  have hsq := sq_eq_one_of_comm S (fun x hx => transv_mul_self x (hSD hx).2) hcl
  have hP2 : IsPGroup 2 (Subgroup.closure S) := fun x =>
    ⟨1, Subtype.ext (by simpa [pow_one, pow_two] using hsq x.1 x.2)⟩
  have hPG : ∀ g ∈ G₀, ∀ h ∈ Subgroup.closure S, g * h * g⁻¹ ∈ Subgroup.closure S := by
    intro g hg
    have hsub : S ⊆
        ((Subgroup.closure S).comap (MulAut.conj g).toMonoidHom : Set (V ≃ₗ[F] V)) := by
      rintro x ⟨k, hk, rfl⟩
      refine Subgroup.subset_closure ⟨g * k, G₀.mul_mem hg hk, ?_⟩
      show g * (k * d * k⁻¹) * g⁻¹ = g * k * d * (g * k)⁻¹
      group
    intro h hh
    exact ((Subgroup.closure_le _).mpr hsub) hh
  have hbot := core_trivial G₀ hirr heven _ hP2 hPG
  have hdS : d ∈ Subgroup.closure S := Subgroup.subset_closure ⟨1, G₀.one_mem, by group⟩
  rw [hbot, Subgroup.mem_bot] at hdS
  exact transv_ne_one d hd.2 hdS

end CFSG.Quasithin.SimsG4
