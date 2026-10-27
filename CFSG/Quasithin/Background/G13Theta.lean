module

public import CFSG.Quasithin.Background.G13Gen

public section

open Matrix CFSG.Quasithin.SL2Model
open scoped MatrixGroups

namespace CFSG.Quasithin.G1

variable {F : Type*} [Field F] [CharP F 2] {n : ℕ} {i j k : Fin n}
  {U : Type*} [AddCommGroup U] [DistribMulAction (Matrix.SpecialLinearGroup (Fin n) F) U]
  {φ : Submodule F (Fin n → F) → AddSubgroup U}

section Gs

variable (hn : 2 ≤ n)

@[expose] noncomputable def gS (F : Type*) [Field F] [CharP F 2] {n : ℕ} (hn : 2 ≤ n)
    (k : Fin n) : Matrix.SpecialLinearGroup (Fin n) F :=
  if h : idx0 hn = k then 1 else wS F h

theorem gS_idx0 : gS F hn (idx0 hn) = 1 := by
  simp [gS]

theorem gS_of_ne (h : idx0 hn ≠ k) : gS F hn k = wS F h := by
  simp [gS, h]

theorem gS_mem (hφ : G13Hyp F n U φ) (k : Fin n) {y : U} (hy : y ∈ φ (Vi F n (idx0 hn))) :
    gS F hn k • y ∈ φ (Vi F n k) := by
  by_cases h : idx0 hn = k
  · subst h
    rw [gS_idx0, one_smul]
    exact hy
  · rw [gS_of_ne hn h, phi_Vi_eq hφ h]
    exact ⟨y, hy, rfl⟩

theorem wS_gS_left (hφ : G13Hyp F n U φ) (hij : i ≠ j) {y : U}
    (hy : y ∈ φ (Vi F n (idx0 hn))) : wS F hij • gS F hn i • y = gS F hn j • y := by
  by_cases hoi : idx0 hn = i
  · subst hoi
    rw [gS_idx0, one_smul, gS_of_ne hn hij]
  · rw [gS_of_ne hn hoi]
    by_cases hoj : idx0 hn = j
    · subst hoj
      rw [gS_idx0, one_smul, wS_symm hij, wS_smul_smul]
    · rw [← mul_smul, wS_cocycle hij hoi hoj, mul_smul, wS_smul_of_ne hφ hij hoi hoj hy,
        gS_of_ne hn hoj]

theorem wS_gS (hφ : G13Hyp F n U φ) (hij : i ≠ j) (k : Fin n) {y : U}
    (hy : y ∈ φ (Vi F n (idx0 hn))) :
    wS F hij • gS F hn k • y = gS F hn (Equiv.swap i j k) • y := by
  by_cases hki : k = i
  · subst hki
    rw [Equiv.swap_apply_left]
    exact wS_gS_left hn hφ hij hy
  · by_cases hkj : k = j
    · subst hkj
      rw [Equiv.swap_apply_right]
      have := wS_gS_left hn hφ hij.symm hy
      rwa [← wS_symm hij] at this
    · rw [Equiv.swap_apply_of_ne_of_ne hki hkj]
      exact wS_smul_of_ne hφ hij hki hkj (gS_mem hn hφ k hy)

end Gs

section Theta

variable (hn : 2 ≤ n) (φ)

abbrev Yz (φ : Submodule F (Fin n → F) → AddSubgroup U) (hn : 2 ≤ n) : AddSubgroup U :=
  φ (Vi F n (idx0 hn))

variable [Module F ↥(Yz φ hn)]

@[expose] noncomputable def thetaMap {s : ℕ} (β : (Fin s → F) ≃ₗ[F] ↥(Yz φ hn)) :
    (Fin s → Fin n → F) →+ U where
  toFun x := ∑ k : Fin n, gS F hn k • ((β (fun l => x l k) : ↥(Yz φ hn)) : U)
  map_zero' := by
    simp only [show ∀ k : Fin n, (fun l : Fin s => (0 : Fin s → Fin n → F) l k) = 0 from
      fun k => rfl, map_zero, ZeroMemClass.coe_zero, smul_zero, Finset.sum_const_zero]
  map_add' x y := by
    have h : ∀ k : Fin n, (fun l : Fin s => (x + y) l k) =
        (fun l => x l k) + (fun l => y l k) := fun k => rfl
    simp only [h, map_add, AddSubgroup.coe_add, smul_add, Finset.sum_add_distrib]

variable {φ hn}

theorem thetaMap_single {s : ℕ} (β : (Fin s → F) ≃ₗ[F] ↥(Yz φ hn)) (k : Fin n) (a : Fin s → F) :
    thetaMap φ hn β (fun l => Pi.single k (a l)) = gS F hn k • ((β a : ↥(Yz φ hn)) : U) := by
  show ∑ m : Fin n, gS F hn m • ((β (fun l => (Pi.single k (a l) : Fin n → F) m) : ↥(Yz φ hn)) : U)
    = _
  rw [Finset.sum_eq_single k]
  · simp
  · intro m _ hm
    have : (fun l => (Pi.single k (a l) : Fin n → F) m) = 0 := by
      funext l
      simp [hm]
    rw [this]
    simp
  · intro h
    exact absurd (Finset.mem_univ k) h

variable (hmod : ∀ (c : F) (y : ↥(Yz φ hn)), ((c • y : ↥(Yz φ hn)) : U) =
    Matrix.SpecialLinearGroup.transvection (idx0_ne_idx1 hn) c • wS F (idx0_ne_idx1 hn) • (y : U) -
      wS F (idx0_ne_idx1 hn) • (y : U))

include hmod in
theorem thetaMap_transvection (hφ : G13Hyp F n U φ) {s : ℕ} (β : (Fin s → F) ≃ₗ[F] ↥(Yz φ hn))
    (c : F) (x : Fin s → Fin n → F) :
    thetaMap φ hn β (fun l => Matrix.SpecialLinearGroup.transvection (idx0_ne_idx1 hn) c • x l) =
      Matrix.SpecialLinearGroup.transvection (idx0_ne_idx1 hn) c • thetaMap φ hn β x := by
  set T := Matrix.SpecialLinearGroup.transvection (idx0_ne_idx1 hn) c with hT
  have hx : (fun l => T • x l) = x + (fun l => Pi.single (idx0 hn) (c * x l (idx1 hn))) := by
    funext l m
    rw [hT, T_smul_apply]
    by_cases hm : m = idx0 hn
    · subst hm
      simp
    · simp [hm]
  rw [hx, map_add, thetaMap_single, gS_idx0, one_smul]
  show _ = T • ∑ m : Fin n, gS F hn m • ((β (fun l => x l m) : ↥(Yz φ hn)) : U)
  rw [Finset.smul_sum]
  have hterm : ∀ m : Fin n, T • (gS F hn m • ((β (fun l => x l m) : ↥(Yz φ hn)) : U)) =
      gS F hn m • ((β (fun l => x l m) : ↥(Yz φ hn)) : U) +
        if m = idx1 hn then ((c • β (fun l => x l (idx1 hn)) : ↥(Yz φ hn)) : U) else 0 := by
    intro m
    by_cases hm : m = idx1 hn
    · subst hm
      simp only [ite_true]
      rw [gS_of_ne hn (idx0_ne_idx1 hn), hmod]
      abel
    · simp only [hm, ite_false, add_zero]
      exact root_smul_of_ne hφ (idx0_ne_idx1 hn) hm (T_mem_Rij _ c)
        (gS_mem hn hφ m (β _).2)
  rw [Finset.sum_congr rfl fun m _ => hterm m, Finset.sum_add_distrib, Finset.sum_ite_eq']
  simp only [Finset.mem_univ, ite_true]
  congr 1
  rw [← map_smul]
  rfl

theorem thetaMap_wS (hφ : G13Hyp F n U φ) {s : ℕ} (β : (Fin s → F) ≃ₗ[F] ↥(Yz φ hn))
    (hij : i ≠ j) (x : Fin s → Fin n → F) :
    thetaMap φ hn β (fun l => wS F hij • x l) = wS F hij • thetaMap φ hn β x := by
  have h1 : ∀ m : Fin n, (fun l : Fin s => (wS F hij • x l) m) =
      fun l => x l (Equiv.swap i j m) := fun m => by
    funext l
    rw [wS_smul]
  show ∑ m : Fin n, gS F hn m • ((β (fun l => (wS F hij • x l) m) : ↥(Yz φ hn)) : U) =
    wS F hij • ∑ m : Fin n, gS F hn m • ((β (fun l => x l m) : ↥(Yz φ hn)) : U)
  simp only [h1]
  rw [Finset.smul_sum]
  have h2 : ∀ m : Fin n, wS F hij • gS F hn m • ((β (fun l => x l m) : ↥(Yz φ hn)) : U) =
      gS F hn (Equiv.swap i j m) • ((β (fun l => x l m) : ↥(Yz φ hn)) : U) :=
    fun m => wS_gS hn hφ hij m (β _).2
  rw [Finset.sum_congr rfl fun m _ => h2 m]
  have h3 := Equiv.sum_comp (Equiv.swap i j)
    (fun m => gS F hn (Equiv.swap i j m) • ((β (fun l => x l m) : ↥(Yz φ hn)) : U))
  simpa only [Equiv.swap_apply_self] using h3

include hmod in
theorem thetaMap_equivariant (hφ : G13Hyp F n U φ) {s : ℕ} (β : (Fin s → F) ≃ₗ[F] ↥(Yz φ hn))
    (g : Matrix.SpecialLinearGroup (Fin n) F) (x : Fin s → Fin n → F) :
    thetaMap φ hn β (fun l => g • x l) = g • thetaMap φ hn β x := by
  let S : Subgroup (Matrix.SpecialLinearGroup (Fin n) F) :=
    { carrier := {g | ∀ x : Fin s → Fin n → F,
        thetaMap φ hn β (fun l => g • x l) = g • thetaMap φ hn β x}
      one_mem' := fun x => by simp
      mul_mem' := fun {g h} hg hh x => by
        have e : (fun l => (g * h) • x l) = fun l => g • (h • x l) := by
          funext l
          exact mul_smul g h (x l)
        rw [e, hg (fun l => h • x l), hh x, mul_smul]
      inv_mem' := fun {g} hg x => by
        have := hg (fun l => g⁻¹ • x l)
        have e : (fun l => g • g⁻¹ • x l) = x := by
          funext l
          exact smul_inv_smul g (x l)
        rw [e] at this
        rw [this, inv_smul_smul] }
  have hS : S = ⊤ := eq_top_of_swaps hn S
    (fun c x => thetaMap_transvection hmod hφ β c x) (fun i j hij x => thetaMap_wS hφ β hij x)
  have hg : g ∈ S := by
    rw [hS]
    exact Subgroup.mem_top g
  exact hg x

include hmod in
theorem thetaMap_injective (hφ : G13Hyp F n U φ) {s : ℕ} (β : (Fin s → F) ≃ₗ[F] ↥(Yz φ hn)) :
    Function.Injective (thetaMap φ hn β) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  have hcol : ∀ j : Fin n, idx0 hn ≠ j → ∀ l, x l j = 0 := by
    intro j hj l
    set T := Matrix.SpecialLinearGroup.transvection hj (1 : F) with hT
    have hxT : (fun l => T • x l) = x + (fun l => Pi.single (idx0 hn) (x l j)) := by
      funext l m
      rw [hT, T_smul_apply]
      by_cases hm : m = idx0 hn
      · subst hm
        simp
      · simp [hm]
    have h1 := thetaMap_equivariant hmod hφ β T x
    rw [hxT, map_add, hx, zero_add, thetaMap_single, gS_idx0, one_smul, smul_zero] at h1
    have h2 : β (fun l => x l j) = 0 := Subtype.ext h1
    have h3 : (fun l => x l j) = 0 := β.injective (by rw [h2, map_zero])
    exact congrFun h3 l
  have hx0 : x = fun l => Pi.single (idx0 hn) (x l (idx0 hn)) := by
    funext l m
    by_cases hm : m = idx0 hn
    · subst hm
      simp
    · simp [hm, hcol m (fun h => hm h.symm) l]
  rw [hx0, thetaMap_single, gS_idx0, one_smul] at hx
  have h2 : β (fun l => x l (idx0 hn)) = 0 := Subtype.ext hx
  have h3 : (fun l => x l (idx0 hn)) = 0 := β.injective (by rw [h2, map_zero])
  funext l m
  by_cases hm : m = idx0 hn
  · subst hm
    exact congrFun h3 l
  · exact hcol m (fun h => hm h.symm) l

theorem thetaMap_surjective (hφ : G13Hyp F n U φ) {s : ℕ} (β : (Fin s → F) ≃ₗ[F] ↥(Yz φ hn)) :
    Function.Surjective (thetaMap φ hn β) := by
  intro u
  have hu : u ∈ ⨆ m : Fin n, φ (Vi F n m) := by
    rw [iSup_phi_Vi_eq_top hn hφ]
    exact AddSubgroup.mem_top u
  have hle : (⨆ m : Fin n, φ (Vi F n m)) ≤ (thetaMap φ hn β).range := by
    refine iSup_le fun m y hy => ?_
    have hy' : ∃ y' ∈ Yz φ hn, gS F hn m • y' = y := by
      by_cases h : idx0 hn = m
      · subst h
        exact ⟨y, hy, by rw [gS_idx0, one_smul]⟩
      · rw [phi_Vi_eq hφ h] at hy
        obtain ⟨y', hy', rfl⟩ := hy
        exact ⟨y', hy', by rw [gS_of_ne hn h]; rfl⟩
    obtain ⟨y', hy', rfl⟩ := hy'
    obtain ⟨a, ha⟩ := β.surjective ⟨y', hy'⟩
    refine ⟨fun l => (Pi.single m (a l) : Fin n → F), ?_⟩
    rw [thetaMap_single, ha]
  exact hle hu

theorem exists_equiv_gen [Finite U] (hn : 2 ≤ n) (hsq : ∀ u : U, u + u = 0)
    (hφ : G13Hyp F n U φ) :
    ∃ (s : ℕ) (Θ : (Fin s → Fin n → F) ≃+ U),
      (∀ (g : Matrix.SpecialLinearGroup (Fin n) F) (x : Fin s → Fin n → F),
        Θ (fun l => g • x l) = g • Θ x) ∧
      Nat.card (Yz φ hn) = Nat.card F ^ s := by
  obtain ⟨_, hmod⟩ := exists_module hφ hsq (idx0_ne_idx1 hn)
  have : Module.Finite F ↥(Yz φ hn) := Module.Finite.of_finite
  let β : (Fin (Module.finrank F ↥(Yz φ hn)) → F) ≃ₗ[F] ↥(Yz φ hn) :=
    (Module.finBasis F ↥(Yz φ hn)).equivFun.symm
  refine ⟨Module.finrank F ↥(Yz φ hn),
    AddEquiv.ofBijective (thetaMap φ hn β)
      ⟨thetaMap_injective hmod hφ β, thetaMap_surjective hφ β⟩,
    fun g x => thetaMap_equivariant hmod hφ β g x, ?_⟩
  rw [← Nat.card_congr β.toEquiv, Nat.card_fun, Nat.card_eq_fintype_card (α := Fin _),
    Fintype.card_fin]

omit [CharP F 2] in
theorem exists_decomp_of_equiv_gen {s : ℕ} (Θ : (Fin s → Fin n → F) ≃+ U)
    (hΘ : ∀ (g : Matrix.SpecialLinearGroup (Fin n) F) (x : Fin s → Fin n → F),
      Θ (fun l => g • x l) = g • Θ x) :
    ∃ W : Fin s → AddSubgroup U, iSupIndep W ∧ ⨆ j, W j = ⊤ ∧ ∀ j,
      (∀ (g : Matrix.SpecialLinearGroup (Fin n) F) (w : U), w ∈ W j → g • w ∈ W j) ∧
      ∃ f : (Fin n → F) →+ U, Function.Injective f ∧ f.range = W j ∧
        ∀ (g : Matrix.SpecialLinearGroup (Fin n) F) (v : Fin n → F), f (g • v) = g • f v := by
  let ι : Fin s → ((Fin n → F) →+ U) := fun j =>
    Θ.toAddMonoidHom.comp (AddMonoidHom.single (fun _ : Fin s => Fin n → F) j)
  have hι : ∀ (j : Fin s) (v : Fin n → F), ι j v = Θ (Pi.single j v) := fun j v => rfl
  have hsingle : ∀ (g : Matrix.SpecialLinearGroup (Fin n) F) (j : Fin s) (v : Fin n → F),
      (fun i => g • (Pi.single j v : Fin s → Fin n → F) i) = Pi.single j (g • v) := by
    intro g j v
    funext i
    by_cases hij : i = j
    · subst hij
      simp
    · simp [hij]
  have hequiv : ∀ (g : Matrix.SpecialLinearGroup (Fin n) F) (j : Fin s) (v : Fin n → F),
      ι j (g • v) = g • ι j v := by
    intro g j v
    rw [hι, hι, ← hΘ g, hsingle]
  refine ⟨fun j => (ι j).range, ?_, ?_, fun j => ⟨?_, ι j, ?_, rfl, fun g v => hequiv g j v⟩⟩
  · intro i
    rw [AddSubgroup.disjoint_def]
    intro u hu hu'
    obtain ⟨v, rfl⟩ := hu
    have hQ : (⨆ (j) (_ : j ≠ i), (ι j).range) ≤
        (Pi.evalAddMonoidHom (fun _ : Fin s => Fin n → F) i).ker.map Θ.toAddMonoidHom := by
      refine iSup₂_le fun j hj => ?_
      rintro _ ⟨v', rfl⟩
      refine ⟨Pi.single j v', ?_, rfl⟩
      simp [Pi.single_eq_of_ne (Ne.symm hj)]
    obtain ⟨x, hx, hxv⟩ := hQ hu'
    have hx' : x = Pi.single i v := Θ.injective hxv
    have hxi : x i = 0 := hx
    rw [hx'] at hxi
    simp only [Pi.single_eq_same] at hxi
    rw [hι, hxi]
    simp
  · rw [eq_top_iff]
    intro u _
    obtain ⟨x, rfl⟩ := Θ.surjective u
    have hsum : x = ∑ j : Fin s, Pi.single j (x j) := (Finset.univ_sum_single x).symm
    rw [hsum, map_sum]
    refine AddSubgroup.sum_mem _ fun j _ => ?_
    exact AddSubgroup.mem_iSup_of_mem j ⟨x j, rfl⟩
  · rintro g w ⟨v, rfl⟩
    exact ⟨g • v, hequiv g j v⟩
  · intro v v' hvv
    exact Pi.single_injective j (Θ.injective hvv)

end Theta

theorem theorem_G_1_3 [Finite F] (hn : 2 ≤ n) : Theorem_G_1_3 F n hn := by
  intro U _ _ _ hsq φ hφ
  obtain ⟨s, Θ, hΘ, hcard⟩ := exists_equiv_gen hn hsq hφ
  exact ⟨s, hcard, exists_decomp_of_equiv_gen Θ hΘ⟩

end CFSG.Quasithin.G1
