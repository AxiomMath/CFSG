module

public import CFSG.Quasithin.Background.G13Perm
public import CFSG.Quasithin.Background.G1Module

public section

open Matrix CFSG.Quasithin.SL2Model
open scoped MatrixGroups

namespace CFSG.Quasithin.G1

variable {F : Type*} [Field F] [CharP F 2] {n : ℕ}
  {U : Type*} [AddCommGroup U] [DistribMulAction (Matrix.SpecialLinearGroup (Fin n) F) U]

variable (F) in
structure G13Fam (hn : 2 ≤ n) (Uk : Fin n → AddSubgroup U) : Prop where
  swap : ∀ (k : Fin n) (h : idx0 hn ≠ k), Uk k = (Uk (idx0 hn)).map (actU (wS F h))
  torus : ∀ (d : Fˣ) (y : U), y ∈ Uk (idx0 hn) → embSL (idx0_ne_idx1 hn) (dgm d) • y ∈ Uk (idx0 hn)
  root_fix : ∀ (a b : Fin n) (hab : a ≠ b) (k : Fin n), k ≠ b → ∀ (c : F) (y : U), y ∈ Uk k →
    Matrix.SpecialLinearGroup.transvection hab c • y = y
  comm : ∀ (c : F) (u : U), Matrix.SpecialLinearGroup.transvection (idx0_ne_idx1 hn) c • u - u ∈
    Uk (idx0 hn)
  disj : Uk (idx0 hn) ⊓ Uk (idx1 hn) = ⊥
  sup : ⨆ k, Uk k = ⊤

namespace G13Fam

@[expose] def fixSub (Y : AddSubgroup U) : Subgroup (Matrix.SpecialLinearGroup (Fin n) F) where
  carrier := {g | ∀ y ∈ Y, g • y = y}
  one_mem' := fun y _ => one_smul _ y
  mul_mem' := fun {g h} hg hh y hy => by rw [mul_smul, hh y hy, hg y hy]
  inv_mem' := fun {g} hg y hy => by
    rw [inv_smul_eq_iff]
    exact (hg y hy).symm

omit [CharP F 2] in
theorem embSL_e12 {i j : Fin n} (hij : i ≠ j) (c : F) :
    embSL hij (e12 c) = Matrix.SpecialLinearGroup.transvection hij c := by
  apply Subtype.ext
  rw [embSL_coe, Matrix.SpecialLinearGroup.transvection_coe]
  have h := emb_transvection hij 0 1 zero_ne_one c
  have he : (e12 c : Matrix (Fin 2) (Fin 2) F) = Matrix.transvection 0 1 c := by
    ext a b
    fin_cases a <;> fin_cases b <;> simp [Matrix.transvection]
  rw [he, h]
  simp [Matrix.transvection]

variable (F) in
@[expose, instance_reducible] noncomputable def pairAct {i j : Fin n} (hij : i ≠ j) :
    DistribMulAction (Matrix.SpecialLinearGroup (Fin 2) F) U :=
  DistribMulAction.compHom U (embSL hij)

variable {hn : 2 ≤ n} {Uk : Fin n → AddSubgroup U} (hfam : G13Fam F hn Uk)

include hfam

theorem Lij_smul {a b k : Fin n} (hab : a ≠ b) (hka : k ≠ a) (hkb : k ≠ b)
    {g : Matrix.SpecialLinearGroup (Fin n) F} (hg : g ∈ Lij F a b) {y : U} (hy : y ∈ Uk k) :
    g • y = y := by
  have hle : Lij F a b ≤ fixSub (Uk k) := by
    refine sup_le (fun t ht y hy => ?_) (fun t ht y hy => ?_)
    · obtain ⟨c, rfl⟩ := (mem_Rij_iff hab).1 ht
      exact hfam.root_fix a b hab k hkb c y hy
    · obtain ⟨c, rfl⟩ := (mem_Rij_iff hab.symm).1 ht
      exact hfam.root_fix b a hab.symm k hka c y hy
  exact hle hg y hy

theorem wS_fix {i j k : Fin n} (hij : i ≠ j) (hki : k ≠ i) (hkj : k ≠ j) {y : U}
    (hy : y ∈ Uk k) : wS F hij • y = y :=
  hfam.Lij_smul hij hki hkj (wS_mem_Lij hij) hy

theorem pre : @G13Pre F _ _ U _ (pairAct F (idx0_ne_idx1 hn)) (Uk (idx0 hn)) := by
  let _ := pairAct F (U := U) (idx0_ne_idx1 hn)
  refine ⟨fun d y hy => hfam.torus d y hy, fun c y hy => ?_, fun c u => ?_, fun z hz hwz => ?_⟩
  · show embSL (idx0_ne_idx1 hn) (e12 c) • y = y
    rw [embSL_e12]
    exact hfam.root_fix _ _ (idx0_ne_idx1 hn) _ (idx0_ne_idx1 hn) c y hy
  · show embSL (idx0_ne_idx1 hn) (e12 c) • u - u ∈ Uk (idx0 hn)
    rw [embSL_e12]
    exact hfam.comm c u
  · have h2 : wS F (idx0_ne_idx1 hn) • z ∈ Uk (idx1 hn) := by
      rw [hfam.swap (idx1 hn) (idx0_ne_idx1 hn)]
      exact ⟨z, hz, rfl⟩
    have h4 : wS F (idx0_ne_idx1 hn) • z ∈ Uk (idx0 hn) ⊓ Uk (idx1 hn) := ⟨hwz, h2⟩
    rw [hfam.disj] at h4
    have h5 : wS F (idx0_ne_idx1 hn) • z = 0 := AddSubgroup.mem_bot.1 h4
    have h6 : wS F (idx0_ne_idx1 hn) • wS F (idx0_ne_idx1 hn) • z =
        wS F (idx0_ne_idx1 hn) • (0 : U) := by rw [h5]
    rwa [wS_smul_smul, smul_zero] at h6

theorem exists_module (hsq : ∀ u : U, u + u = 0) :
    ∃ _ : Module F ↥(Uk (idx0 hn)), ∀ (c : F) (y : ↥(Uk (idx0 hn))),
      ((c • y : ↥(Uk (idx0 hn))) : U) =
        Matrix.SpecialLinearGroup.transvection (idx0_ne_idx1 hn) c •
          wS F (idx0_ne_idx1 hn) • (y : U) - wS F (idx0_ne_idx1 hn) • (y : U) := by
  let _ := pairAct F (U := U) (idx0_ne_idx1 hn)
  have hpre : G13Pre F (Uk (idx0 hn)) := hfam.pre
  refine ⟨hpre.module hsq, fun c y => ?_⟩
  show th c (y : U) = _
  show embSL (idx0_ne_idx1 hn) (e12 c) • embSL (idx0_ne_idx1 hn) (wmat F) • (y : U) -
    embSL (idx0_ne_idx1 hn) (wmat F) • (y : U) = _
  rw [embSL_e12]
  rfl

omit hfam in
variable (F) in
@[expose] noncomputable def gS (hn : 2 ≤ n) (k : Fin n) : Matrix.SpecialLinearGroup (Fin n) F :=
  if h : idx0 hn = k then 1 else wS F h

omit hfam in
theorem gS_idx0 : gS F hn (idx0 hn) = 1 := by
  simp [gS]

omit hfam in
theorem gS_of_ne {k : Fin n} (h : idx0 hn ≠ k) : gS F hn k = wS F h := by
  simp [gS, h]

theorem gS_mem (k : Fin n) {y : U} (hy : y ∈ Uk (idx0 hn)) : gS F hn k • y ∈ Uk k := by
  by_cases h : idx0 hn = k
  · subst h
    rw [gS_idx0, one_smul]
    exact hy
  · rw [gS_of_ne h, hfam.swap k h]
    exact ⟨y, hy, rfl⟩

theorem wS_gS_left {i j : Fin n} (hij : i ≠ j) {y : U} (hy : y ∈ Uk (idx0 hn)) :
    wS F hij • gS F hn i • y = gS F hn j • y := by
  by_cases hoi : idx0 hn = i
  · subst hoi
    rw [gS_idx0, one_smul, gS_of_ne hij]
  · rw [gS_of_ne hoi]
    by_cases hoj : idx0 hn = j
    · subst hoj
      rw [gS_idx0, one_smul, wS_symm hij, wS_smul_smul]
    · rw [← mul_smul, wS_cocycle hij hoi hoj, mul_smul, hfam.wS_fix hij hoi hoj hy,
        gS_of_ne hoj]

theorem wS_gS {i j : Fin n} (hij : i ≠ j) (k : Fin n) {y : U} (hy : y ∈ Uk (idx0 hn)) :
    wS F hij • gS F hn k • y = gS F hn (Equiv.swap i j k) • y := by
  by_cases hki : k = i
  · subst hki
    rw [Equiv.swap_apply_left]
    exact hfam.wS_gS_left hij hy
  · by_cases hkj : k = j
    · subst hkj
      rw [Equiv.swap_apply_right]
      have := hfam.wS_gS_left hij.symm hy
      rwa [← wS_symm hij] at this
    · rw [Equiv.swap_apply_of_ne_of_ne hki hkj]
      exact hfam.wS_fix hij hki hkj (hfam.gS_mem k hy)

omit hfam in
@[expose] noncomputable def thetaMap (Uk : Fin n → AddSubgroup U) (hn : 2 ≤ n)
    [Module F ↥(Uk (idx0 hn))] {s : ℕ} (β : (Fin s → F) ≃ₗ[F] ↥(Uk (idx0 hn))) :
    (Fin s → Fin n → F) →+ U where
  toFun x := ∑ k : Fin n, gS F hn k • ((β (fun l => x l k) : ↥(Uk (idx0 hn))) : U)
  map_zero' := by
    simp only [show ∀ k : Fin n, (fun l : Fin s => (0 : Fin s → Fin n → F) l k) = 0 from
      fun k => rfl, map_zero, ZeroMemClass.coe_zero, smul_zero, Finset.sum_const_zero]
  map_add' x y := by
    have h : ∀ k : Fin n, (fun l : Fin s => (x + y) l k) =
        (fun l => x l k) + (fun l => y l k) := fun k => rfl
    simp only [h, map_add, AddSubgroup.coe_add, smul_add, Finset.sum_add_distrib]

section Theta

variable [Module F ↥(Uk (idx0 hn))] {s : ℕ} (β : (Fin s → F) ≃ₗ[F] ↥(Uk (idx0 hn)))

omit hfam in
theorem thetaMap_single (k : Fin n) (a : Fin s → F) :
    thetaMap Uk hn β (fun l => Pi.single k (a l)) =
      gS F hn k • ((β a : ↥(Uk (idx0 hn))) : U) := by
  show ∑ m : Fin n, gS F hn m • ((β (fun l => (Pi.single k (a l) : Fin n → F) m) :
    ↥(Uk (idx0 hn))) : U) = _
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

variable (hmod : ∀ (c : F) (y : ↥(Uk (idx0 hn))), ((c • y : ↥(Uk (idx0 hn))) : U) =
    Matrix.SpecialLinearGroup.transvection (idx0_ne_idx1 hn) c • wS F (idx0_ne_idx1 hn) • (y : U) -
      wS F (idx0_ne_idx1 hn) • (y : U))

include hmod in
theorem thetaMap_transvection (c : F) (x : Fin s → Fin n → F) :
    thetaMap Uk hn β (fun l => Matrix.SpecialLinearGroup.transvection (idx0_ne_idx1 hn) c • x l) =
      Matrix.SpecialLinearGroup.transvection (idx0_ne_idx1 hn) c • thetaMap Uk hn β x := by
  set T := Matrix.SpecialLinearGroup.transvection (idx0_ne_idx1 hn) c with hT
  have hx : (fun l => T • x l) = x + (fun l => Pi.single (idx0 hn) (c * x l (idx1 hn))) := by
    funext l m
    rw [hT, T_smul_apply]
    by_cases hm : m = idx0 hn
    · subst hm
      simp
    · simp [hm]
  rw [hx, map_add, thetaMap_single, gS_idx0, one_smul]
  show _ = T • ∑ m : Fin n, gS F hn m • ((β (fun l => x l m) : ↥(Uk (idx0 hn))) : U)
  rw [Finset.smul_sum]
  have hterm : ∀ m : Fin n, T • (gS F hn m • ((β (fun l => x l m) : ↥(Uk (idx0 hn))) : U)) =
      gS F hn m • ((β (fun l => x l m) : ↥(Uk (idx0 hn))) : U) +
        if m = idx1 hn then ((c • β (fun l => x l (idx1 hn)) : ↥(Uk (idx0 hn))) : U) else 0 := by
    intro m
    by_cases hm : m = idx1 hn
    · subst hm
      simp only [ite_true]
      rw [gS_of_ne (idx0_ne_idx1 hn), hmod]
      abel
    · simp only [hm, ite_false, add_zero]
      exact hfam.root_fix _ _ (idx0_ne_idx1 hn) m hm c _ (hfam.gS_mem m (β _).2)
  rw [Finset.sum_congr rfl fun m _ => hterm m, Finset.sum_add_distrib, Finset.sum_ite_eq']
  simp only [Finset.mem_univ, ite_true]
  congr 1
  rw [← map_smul]
  rfl

theorem thetaMap_wS {i j : Fin n} (hij : i ≠ j) (x : Fin s → Fin n → F) :
    thetaMap Uk hn β (fun l => wS F hij • x l) = wS F hij • thetaMap Uk hn β x := by
  have h1 : ∀ m : Fin n, (fun l : Fin s => (wS F hij • x l) m) =
      fun l => x l (Equiv.swap i j m) := fun m => by
    funext l
    rw [wS_smul]
  show ∑ m : Fin n, gS F hn m • ((β (fun l => (wS F hij • x l) m) : ↥(Uk (idx0 hn))) : U) =
    wS F hij • ∑ m : Fin n, gS F hn m • ((β (fun l => x l m) : ↥(Uk (idx0 hn))) : U)
  simp only [h1]
  rw [Finset.smul_sum]
  have h2 : ∀ m : Fin n, wS F hij • gS F hn m • ((β (fun l => x l m) : ↥(Uk (idx0 hn))) : U) =
      gS F hn (Equiv.swap i j m) • ((β (fun l => x l m) : ↥(Uk (idx0 hn))) : U) :=
    fun m => hfam.wS_gS hij m (β _).2
  rw [Finset.sum_congr rfl fun m _ => h2 m]
  have h3 := Equiv.sum_comp (Equiv.swap i j)
    (fun m => gS F hn (Equiv.swap i j m) • ((β (fun l => x l m) : ↥(Uk (idx0 hn))) : U))
  simpa only [Equiv.swap_apply_self] using h3

include hmod in
theorem thetaMap_equivariant (g : Matrix.SpecialLinearGroup (Fin n) F) (x : Fin s → Fin n → F) :
    thetaMap Uk hn β (fun l => g • x l) = g • thetaMap Uk hn β x := by
  let S : Subgroup (Matrix.SpecialLinearGroup (Fin n) F) :=
    { carrier := {g | ∀ x : Fin s → Fin n → F,
        thetaMap Uk hn β (fun l => g • x l) = g • thetaMap Uk hn β x}
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
    (fun c x => hfam.thetaMap_transvection β hmod c x) (fun i j hij x => hfam.thetaMap_wS β hij x)
  have hg : g ∈ S := by
    rw [hS]
    exact Subgroup.mem_top g
  exact hg x

include hmod in
theorem thetaMap_injective : Function.Injective (thetaMap Uk hn β) := by
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
    have h1 := hfam.thetaMap_equivariant β hmod T x
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

theorem mem_Uk_iff_exists (k : Fin n) (u : U) :
    u ∈ Uk k ↔ ∃ a : Fin s → F, u = thetaMap Uk hn β (fun l => Pi.single k (a l)) := by
  constructor
  · intro hu
    have hu' : ∃ y ∈ Uk (idx0 hn), gS F hn k • y = u := by
      by_cases h : idx0 hn = k
      · subst h
        exact ⟨u, hu, by rw [gS_idx0, one_smul]⟩
      · rw [hfam.swap k h] at hu
        obtain ⟨y, hy, rfl⟩ := hu
        exact ⟨y, hy, by rw [gS_of_ne h]; rfl⟩
    obtain ⟨y, hy, rfl⟩ := hu'
    obtain ⟨a, ha⟩ := β.surjective ⟨y, hy⟩
    refine ⟨a, ?_⟩
    rw [thetaMap_single, ha]
  · rintro ⟨a, rfl⟩
    rw [thetaMap_single]
    exact hfam.gS_mem k (β a).2

theorem thetaMap_surjective : Function.Surjective (thetaMap Uk hn β) := by
  intro u
  have hu : u ∈ ⨆ m : Fin n, Uk m := by
    rw [hfam.sup]
    exact AddSubgroup.mem_top u
  have hle : (⨆ m : Fin n, Uk m) ≤ (thetaMap Uk hn β).range := by
    refine iSup_le fun m y hy => ?_
    obtain ⟨a, rfl⟩ := (hfam.mem_Uk_iff_exists β m y).1 hy
    exact ⟨_, rfl⟩
  exact hle hu

end Theta

theorem exists_equiv_fam [Finite U] (hsq : ∀ u : U, u + u = 0) :
    ∃ (s : ℕ) (Θ : (Fin s → Fin n → F) ≃+ U),
      (∀ (g : Matrix.SpecialLinearGroup (Fin n) F) (x : Fin s → Fin n → F),
        Θ (fun l => g • x l) = g • Θ x) ∧
      Nat.card (Uk (idx0 hn)) = Nat.card F ^ s ∧
      ∀ (k : Fin n) (u : U), u ∈ Uk k ↔ ∃ a : Fin s → F, u = Θ (fun l => Pi.single k (a l)) := by
  obtain ⟨_, hmod⟩ := hfam.exists_module hsq
  have : Module.Finite F ↥(Uk (idx0 hn)) := Module.Finite.of_finite
  let β : (Fin (Module.finrank F ↥(Uk (idx0 hn))) → F) ≃ₗ[F] ↥(Uk (idx0 hn)) :=
    (Module.finBasis F ↥(Uk (idx0 hn))).equivFun.symm
  refine ⟨Module.finrank F ↥(Uk (idx0 hn)),
    AddEquiv.ofBijective (thetaMap Uk hn β)
      ⟨hfam.thetaMap_injective β hmod, hfam.thetaMap_surjective β⟩,
    fun g x => hfam.thetaMap_equivariant β hmod g x, ?_, fun k u => hfam.mem_Uk_iff_exists β k u⟩
  rw [← Nat.card_congr β.toEquiv, Nat.card_fun, Nat.card_eq_fintype_card (α := Fin _),
    Fintype.card_fin]

end G13Fam

end CFSG.Quasithin.G1
