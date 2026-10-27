module

public import CFSG.Quasithin.Background.SmithCurtisMain

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin.SmithCurtis

private noncomputable def omMinusSumRep {G : Type*} [Group G] {k V : Type*} [Field k]
    [AddCommGroup V] [Module k V] (ρ : Representation k G V) (P : Subgroup G) [Fintype P]
    (v : V) : (P → k) →ₗ[k] V where
  toFun c := ∑ x : P, c x • ρ (x : G) v
  map_add' c d := by
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' a c := by
    simp only [Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum, RingHom.id_apply]

private theorem omMinusSumRep_apply {G : Type*} [Group G] {k V : Type*} [Field k]
    [AddCommGroup V] [Module k V] (ρ : Representation k G V) (P : Subgroup G) [Fintype P]
    (v : V) (c : P → k) : omMinusSumRep ρ P v c = ∑ x : P, c x • ρ (x : G) v := rfl

private noncomputable def omMinusLeftReg (k P : Type*) [Field k] [Group P] :
    Representation k P (P → k) where
  toFun g :=
    { toFun := fun c x => c (g⁻¹ * x)
      map_add' c d := by ext x; rfl
      map_smul' a c := by ext x; rfl }
  map_one' := by ext c x; simp
  map_mul' g h := by
    ext c x
    show c ((g * h)⁻¹ * x) = c (h⁻¹ * (g⁻¹ * x))
    rw [mul_inv_rev, mul_assoc]

private theorem omMinusLeftReg_apply {k P : Type*} [Field k] [Group P] (g : P) (c : P → k)
    (x : P) : omMinusLeftReg k P g c x = c (g⁻¹ * x) := rfl

private theorem omMinusSumRep_leftReg {G : Type*} [Group G] {k V : Type*} [Field k]
    [AddCommGroup V] [Module k V] (ρ : Representation k G V) (P : Subgroup G) [Fintype P]
    (v : V) (g : P) (c : P → k) :
    omMinusSumRep ρ P v (omMinusLeftReg k P g c) = ρ (g : G) (omMinusSumRep ρ P v c) := by
  classical
  simp only [omMinusSumRep_apply, omMinusLeftReg_apply]
  have hreindex : ∑ x : P, c (g⁻¹ * x) • ρ (x : G) v
      = ∑ y : P, c y • ρ ((g * y : P) : G) v := by
    refine (Fintype.sum_equiv (Equiv.mulLeft g) (fun y : P => c y • ρ ((g * y : P) : G) v)
      (fun x : P => c (g⁻¹ * x) • ρ (x : G) v) ?_).symm
    intro y
    simp only [Equiv.coe_mulLeft, inv_mul_cancel_left]
  rw [hreindex, map_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Subgroup.coe_mul, ← act_mul, map_smul]

theorem linearIndependent_smul_of_sum_ne_zero {G : Type*} [Group G] {k V : Type*} [Field k]
    [AddCommGroup V] [Module k V] {p : ℕ} [Fact p.Prime] [CharP k p]
    (ρ : Representation k G V) (P : Subgroup G) [Fintype P] (hP : IsPGroup p P) {v : V}
    (hv : ∑ x : P, ρ x v ≠ 0) : LinearIndependent k fun x : P => ρ x v := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  have hker : LinearMap.ker (omMinusSumRep ρ P v) = ⊥ := by
    by_contra hne
    have hS : IsPGroup p (⊤ : Subgroup P) :=
      hP.of_equiv (Subgroup.topEquiv (G := P)).symm
    have hW : ∀ (g : P) (w : P → k), w ∈ LinearMap.ker (omMinusSumRep ρ P v) →
        omMinusLeftReg k P g w ∈ LinearMap.ker (omMinusSumRep ρ P v) := by
      intro g w hw
      rw [LinearMap.mem_ker] at hw ⊢
      rw [omMinusSumRep_leftReg ρ P v g w, hw, map_zero]
    obtain ⟨x, hxmem, hx0, hxfix⟩ :=
      exists_fixed_mem (omMinusLeftReg k P) hS hW hne
    rw [LinearMap.mem_ker, omMinusSumRep_apply] at hxmem
    have hconst : ∀ y : P, x y = x 1 := by
      intro y
      have h := congrFun (hxfix y⁻¹ (Subgroup.mem_top y⁻¹)) 1
      rw [omMinusLeftReg_apply] at h
      simpa using h
    have ha : x 1 ≠ 0 := by
      intro h
      apply hx0
      funext y
      rw [Pi.zero_apply, hconst y, h]
    have hsum0 : ∑ y : P, x 1 • ρ (y : G) v = 0 := by
      simpa only [hconst] using hxmem
    have hsmul : x 1 • (∑ y : P, ρ (y : G) v) = 0 := by
      rw [Finset.smul_sum]
      exact hsum0
    exact hv ((smul_eq_zero.mp hsmul).resolve_left ha)
  have hmem : c ∈ LinearMap.ker (omMinusSumRep ρ P v) := by
    rw [LinearMap.mem_ker, omMinusSumRep_apply]
    exact hc
  rw [hker] at hmem
  have hc0 : c = 0 := by simpa using hmem
  rw [hc0]
  rfl

private theorem omMinusRho_commute {G : Type*} [Group G] {k V : Type*} [Field k]
    [AddCommGroup V] [Module k V] (ρ : Representation k G V) {t g : G} (h : Commute t g)
    (v : V) : ρ t (ρ g v) = ρ g (ρ t v) := by
  calc ρ t (ρ g v) = ρ (t * g) v := act_mul ρ t g v
    _ = ρ (g * t) v := by rw [h.eq]
    _ = ρ g (ρ t v) := (act_mul ρ g t v).symm

private theorem omMinusHeckeT_commute {G : Type*} [Group G] [Finite G] {B : Type*}
    {M : CoxeterMatrix B} {W : Type*} [Group W] {cs : CoxeterSystem M W} {p : ℕ}
    {D : CurtisDatum G cs p} {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
    {ρ : Representation k G V} {s : B} {t : G}
    (htX : ∀ x ∈ D.X s, Commute t x) (htn : Commute t (D.n s)) (v : V) :
    D.heckeT ρ s (ρ t v) = ρ t (D.heckeT ρ s v) :=
  letI : Fintype (D.X s) := Fintype.ofFinite (D.X s)
  by
    rw [D.heckeT_apply ρ s (ρ t v), D.heckeT_apply ρ s v, map_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    exact (omMinusRho_commute ρ ((htX x x.2).mul_right htn) v).symm

private theorem omMinusRange_apply {G : Type*} [Group G] {k V : Type*} [Field k]
    [AddCommGroup V] [Module k V] (ρ : Representation k G V) {t n x : G}
    (hx : Commute t x) (hn : Commute t n) (y : V) :
    (ρ t - 1) (ρ (x * n) y) = ρ x (ρ n (ρ t y - y)) := by
  rw [LinearMap.sub_apply, Module.End.one_apply, omMinusRho_commute ρ (hx.mul_right hn) y]
  simp only [map_sub, ← act_mul]

theorem card_X_le_finrank_range_sub_one_of_commute {G : Type*} [Group G] [Finite G]
    {B : Type*} {M : CoxeterMatrix B} {W : Type*} [Group W] {cs : CoxeterSystem M W} {p : ℕ}
    [Fact p.Prime] {D : CurtisDatum G cs p} {k V : Type*} [Field k] [CharP k p] [AddCommGroup V]
    [Module k V] [Module.Finite k V] {ρ : Representation k G V} {y : V} {χ : G → k}
    {μ : B → k} (ht : D.IsCurtisType ρ y χ μ) {s : B} (hμ : μ s ≠ 0) {t : G}
    (htX : ∀ x ∈ D.X s, Commute t x) (htn : Commute t (D.n s)) (hty : ρ t y ≠ y) :
    Nat.card (D.X s) ≤ Module.finrank k (LinearMap.range (ρ t - 1)) :=
  letI : Fintype (D.X s) := Fintype.ofFinite (D.X s)
  by
    classical
    let T : V →ₗ[k] V := ρ t - 1
    have hTy : D.heckeT ρ s y = μ s • y := ht.2.2.2 s
    have hz : ρ t y - y ≠ 0 := fun h => hty (sub_eq_zero.mp h)
    have hTz : D.heckeT ρ s (ρ t y - y) = μ s • (ρ t y - y) := by
      rw [map_sub, omMinusHeckeT_commute (D := D) htX htn y, hTy, map_smul, smul_sub]
    have hsum : ∑ x : D.X s, ρ x (ρ (D.n s) (ρ t y - y)) ≠ 0 := by
      have h1 := D.heckeT_apply ρ s (ρ t y - y)
      rw [hTz] at h1
      simp only [← act_mul] at h1
      rw [← h1]
      exact smul_ne_zero hμ hz
    have hXs : IsPGroup p (D.X s) := (D.isPGroup_U).to_le (D.X_le s)
    have hli : LinearIndependent k fun x : D.X s => ρ x (ρ (D.n s) (ρ t y - y)) :=
      linearIndependent_smul_of_sum_ne_zero ρ (D.X s) hXs hsum
    have hfun : (fun x : D.X s => T (ρ ((x : G) * D.n s) y))
        = fun x : D.X s => ρ x (ρ (D.n s) (ρ t y - y)) := by
      funext x
      exact omMinusRange_apply ρ (htX x x.2) htn y
    have hliT : LinearIndependent k (fun x : D.X s => T (ρ ((x : G) * D.n s) y)) := by
      rw [hfun]
      exact hli
    let w : D.X s → LinearMap.range T := fun x =>
      ⟨T (ρ ((x : G) * D.n s) y), ⟨ρ ((x : G) * D.n s) y, rfl⟩⟩
    have hw : LinearIndependent k w := by
      rw [Fintype.linearIndependent_iff] at hliT ⊢
      intro c hc
      refine hliT c ?_
      have h := congrArg (fun z => (LinearMap.range T).subtype z) hc
      simpa [w, map_sum, map_smul] using h
    have hcard := hw.fintype_card_le_finrank
    rw [Nat.card_eq_fintype_card]
    simpa [T] using hcard

end CFSG.LocalAnalysis.WeakClosure81
