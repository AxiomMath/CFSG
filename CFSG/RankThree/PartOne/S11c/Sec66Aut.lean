module

public import CFSG.RankThree.PartOne.S11.PlaneData
public import CFSG.RankThree.PartOne.S11c.Sec66Plane

public section

namespace CFSG.RankThree.PartOne.PlaneInner

open Subgroup CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.GroupTheory

variable {H : Type} [Group H] [Finite H]

omit [Finite H] in
theorem centerQuotientConj_inner_of_mem_sup {J : Subgroup H} {a : H}
    (ha : a ∈ Subgroup.normalizer (J : Set H))
    (hmem : a ∈ J ⊔ Subgroup.centralizer (J : Set H)) :
    ∃ q : J ⧸ Subgroup.center J, centerQuotientConj J ⟨a, ha⟩ = MulAut.conj q := by
  obtain ⟨j, hj, z, hz, hjz⟩ := exists_mul_of_mem_sup_centralizer hmem
  refine ⟨((⟨j, hj⟩ : J) : J ⧸ Subgroup.center J), ?_⟩
  ext q
  induction q using QuotientGroup.induction_on with
  | H l =>
    change ((J.normalizerMonoidHom ⟨a, ha⟩ l : J) : J ⧸ Subgroup.center J) = _
    rw [MulAut.conj_apply]
    have hzl : (l : H) * z = z * l := (Subgroup.mem_centralizer_iff.mp hz) l l.2
    have : (J.normalizerMonoidHom ⟨a, ha⟩ l : J) = ⟨j, hj⟩ * l * ⟨j, hj⟩⁻¹ := by
      apply Subtype.ext
      simp only [Subgroup.normalizerMonoidHom_apply_apply_coe, Subgroup.coe_mul,
        Subgroup.coe_inv]
      rw [hjz]
      calc j * z * l * (j * z)⁻¹ = j * (z * l) * z⁻¹ * j⁻¹ := by group
        _ = j * (l * z) * z⁻¹ * j⁻¹ := by rw [hzl]
        _ = j * l * j⁻¹ := by group
    rw [this]
    rfl


omit [Finite H] in
theorem conj_mem_center {J : Subgroup H} {a : H} (ha : a ∈ Subgroup.normalizer (J : Set H))
    {w : H} (hw : w ∈ (Subgroup.center J).map J.subtype) :
    a * w * a⁻¹ ∈ (Subgroup.center J).map J.subtype := by
  obtain ⟨w0, hw0, rfl⟩ := hw
  have hJ : a * (w0 : H) * a⁻¹ ∈ J := (Subgroup.mem_normalizer_iff.mp ha (w0 : H)).mp w0.2
  refine ⟨⟨a * (w0 : H) * a⁻¹, hJ⟩, ?_, rfl⟩
  change (⟨a * (w0 : H) * a⁻¹, hJ⟩ : J) ∈ Subgroup.center J
  rw [Subgroup.mem_center_iff]
  intro g
  apply Subtype.ext
  have hg : a⁻¹ * (g : H) * a ∈ J := by
    have := (Subgroup.mem_normalizer_iff.mp (inv_mem ha) (g : H)).mp g.2
    simpa using this
  have h1 := Subgroup.mem_center_iff.mp hw0 ⟨a⁻¹ * (g : H) * a, hg⟩
  have h2 : a⁻¹ * (g : H) * a * (w0 : H) = (w0 : H) * (a⁻¹ * (g : H) * a) :=
    congrArg Subtype.val h1
  show (g : H) * (a * (w0 : H) * a⁻¹) = a * (w0 : H) * a⁻¹ * (g : H)
  calc (g : H) * (a * (w0 : H) * a⁻¹) = a * (a⁻¹ * (g : H) * a * (w0 : H)) * a⁻¹ := by group
    _ = a * ((w0 : H) * (a⁻¹ * (g : H) * a)) * a⁻¹ := by rw [h2]
    _ = a * (w0 : H) * a⁻¹ * (g : H) := by group

omit [Finite H] in
theorem commute_of_mem_center_map {J : Subgroup H} {z : H}
    (hz : z ∈ (Subgroup.center J).map J.subtype) {x : H} (hx : x ∈ J) : x * z = z * x := by
  obtain ⟨z0, hz0, rfl⟩ := hz
  have := Subgroup.mem_center_iff.mp hz0 ⟨x, hx⟩
  exact congrArg Subtype.val this.symm |>.symm

theorem exists_fixed_in_coset {p : ℕ} (hp : p.Prime) {J : Subgroup H}
    (hZ : ¬ p ∣ Nat.card (Subgroup.center J)) {a : H}
    (ha : a ∈ Subgroup.normalizer (J : Set H)) (hap : a ^ p = 1) {x : H} (hxJ : x ∈ J)
    (hfix : a * x * a⁻¹ * x⁻¹ ∈ (Subgroup.center J).map J.subtype) :
    ∃ y ∈ J, a * y * a⁻¹ = y ∧ x⁻¹ * y ∈ (Subgroup.center J).map J.subtype := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨Zs, hZs⟩ : ∃ Zs : Subgroup H, Zs = (Subgroup.center J).map J.subtype := ⟨_, rfl⟩
  rw [← hZs] at hfix ⊢
  have hZJ : ∀ w ∈ Zs, w ∈ J := by
    intro w hw
    rw [hZs] at hw
    obtain ⟨w0, -, rfl⟩ := hw
    exact w0.2
  have hconj : ∀ w ∈ Zs, a * w * a⁻¹ ∈ Zs := fun w hw => hZs ▸ conj_mem_center ha (hZs ▸ hw)
  have hcomm : ∀ z ∈ Zs, x * z = z * x := fun z hz =>
    commute_of_mem_center_map (hZs ▸ hz) hxJ
  have hmaps : ∀ y : H, x⁻¹ * y ∈ Zs → x⁻¹ * (a * y * a⁻¹) ∈ Zs := by
    intro y hy
    have hw : a * (x⁻¹ * y) * a⁻¹ ∈ Zs := hconj _ hy
    have h1 : x⁻¹ * (a * y * a⁻¹) =
        (x⁻¹ * (a * x * a⁻¹ * x⁻¹) * x) * (a * (x⁻¹ * y) * a⁻¹) := by group
    rw [h1]
    refine mul_mem ?_ hw
    have h2 : x⁻¹ * (a * x * a⁻¹ * x⁻¹) * x = a * x * a⁻¹ * x⁻¹ := by
      have := hcomm _ hfix
      calc x⁻¹ * (a * x * a⁻¹ * x⁻¹) * x = x⁻¹ * ((a * x * a⁻¹ * x⁻¹) * x) := by group
        _ = x⁻¹ * (x * (a * x * a⁻¹ * x⁻¹)) := by rw [← this]
        _ = a * x * a⁻¹ * x⁻¹ := by group
    rw [h2]
    exact hfix
  let C : Type := {y : H // x⁻¹ * y ∈ Zs}
  let F : Function.End C := fun y => ⟨a * y * a⁻¹, hmaps y y.2⟩
  have hFn : ∀ (n : ℕ) (y : C), (((F ^ n : Function.End C) y : C) : H) = a ^ n * y * (a ^ n)⁻¹ := by
    intro n
    induction n with
    | zero => intro y; rw [pow_zero, pow_zero, inv_one, mul_one, one_mul]; rfl
    | succ n ih =>
      intro y
      rw [pow_succ]
      show ((F ^ n : Function.End C) (F y) : H) = _
      rw [ih]
      show a ^ n * (a * (y : H) * a⁻¹) * (a ^ n)⁻¹ = a ^ (n + 1) * y * (a ^ (n + 1))⁻¹
      group
  have hF1 : F ^ p ^ 1 = 1 := by
    funext y
    apply Subtype.ext
    rw [pow_one, hFn p y, hap]
    simp
    rfl
  have : Fintype C := Fintype.ofFinite C
  have hmod := Equiv.Perm.card_fixedPoints_modEq (α := C) (f := F) (p := p) (n := 1) hF1
  have hcardC : Fintype.card C = Nat.card Zs := by
    rw [← Nat.card_eq_fintype_card]
    refine Nat.card_congr ⟨fun y => ⟨x⁻¹ * y.1, y.2⟩, fun w => ⟨x * w.1, by simp⟩, ?_, ?_⟩
    · intro y; apply Subtype.ext; simp
    · intro w; apply Subtype.ext; simp
  have hZsCard : Nat.card Zs = Nat.card (Subgroup.center J) := by
    rw [hZs]
    exact Subgroup.card_map_of_injective J.subtype_injective
  have hnd : ¬ p ∣ Fintype.card C := by
    rw [hcardC, hZsCard]
    exact hZ
  have hfp : Fintype.card (Function.fixedPoints F) ≠ 0 := by
    intro h0
    apply hnd
    rw [h0] at hmod
    exact (Nat.modEq_zero_iff_dvd).mp hmod
  obtain ⟨⟨y, hy⟩⟩ := Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero hfp)
  have hyfix' : a * (y : H) * a⁻¹ = y := congrArg Subtype.val hy
  have hxZ : x⁻¹ * (y : H) ∈ Zs := y.2
  have hyJ : (y : H) ∈ J := by
    have : (y : H) = x * (x⁻¹ * y) := by group
    rw [this]
    exact J.mul_mem hxJ (hZJ _ hxZ)
  exact ⟨y, hyJ, hyfix', hxZ⟩


end CFSG.RankThree.PartOne.PlaneInner
