module

public import CFSG.Quasithin.EmptyFaithful.SzC4ChirApi
public import Mathlib.GroupTheory.NoncommCoprod
public import Mathlib.Data.Rat.Floor

public section

namespace CFSG.Quasithin.SzC4

variable {G : Type} [Group G]

@[expose] def conjOn (Y : Subgroup G) (g : G) (hg : g ∈ Subgroup.normalizer (Y : Set G)) :
    MulAut ↥Y where
  toFun y := ⟨g * y * g⁻¹, (Subgroup.mem_normalizer_iff.1 hg y).1 y.2⟩
  invFun y := ⟨g⁻¹ * y * g, by
    have := (Subgroup.mem_normalizer_iff.1 ((Subgroup.normalizer (Y : Set G)).inv_mem hg) y).1 y.2
    simpa using this⟩
  left_inv y := by
    apply Subtype.ext
    simp [mul_assoc]
  right_inv y := by
    apply Subtype.ext
    simp [mul_assoc]
  map_mul' x y := by
    apply Subtype.ext
    simp [mul_assoc]

theorem conjOn_apply (Y : Subgroup G) (g : G) (hg : g ∈ Subgroup.normalizer (Y : Set G))
    (y : ↥Y) : ((conjOn Y g hg y : ↥Y) : G) = g * y * g⁻¹ := rfl

theorem conjOn_pow_apply (Y : Subgroup G) (g : G) (hg : g ∈ Subgroup.normalizer (Y : Set G))
    (n : ℕ) (y : ↥Y) : (((conjOn Y g hg ^ n) y : ↥Y) : G) = g ^ n * y * (g ^ n)⁻¹ := by
  induction n generalizing y with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, MulAut.mul_apply, ih]
    rw [conjOn_apply, pow_succ]
    simp [mul_assoc]

theorem conjOn_pow_seven (Y : Subgroup G) (g : G) (hg : g ∈ Subgroup.normalizer (Y : Set G))
    (h7 : g ^ 7 = 1) : conjOn Y g hg ^ 7 = 1 := by
  ext y
  rw [conjOn_pow_apply, h7]
  simp

theorem conjOn_eq_one (Y : Subgroup G) (g : G) (hg : g ∈ Subgroup.normalizer (Y : Set G))
    (h : ∀ y ∈ Y, g * y * g⁻¹ = y) : conjOn Y g hg = 1 := by
  ext y
  exact h y y.2

open Classical in
@[expose] noncomputable def chiC [Finite G] (A : ChiAPI) (Y : Subgroup G) (g : G) : ℤ :=
  if hg : g ∈ Subgroup.normalizer (Y : Set G) then A.chi ↥Y (conjOn Y g hg) else 0

variable [Finite G]

theorem chiC_of_mem (A : ChiAPI) (Y : Subgroup G) {g : G}
    (hg : g ∈ Subgroup.normalizer (Y : Set G)) :
    chiC A Y g = A.chi ↥Y (conjOn Y g hg) := by
  unfold chiC
  simp [hg]

theorem chiC_exact (A : ChiAPI) {Y N : Subgroup G} (hY : IsPGroup 2 ↥Y) (hNY : N ≤ Y) {g : G}
    (hgY : g ∈ Subgroup.normalizer (Y : Set G)) (hgN : g ∈ Subgroup.normalizer (N : Set G))
    (hg7 : g ^ 7 = 1) {B : Type} [Group B] [Finite B] (π : ↥Y →* B)
    (hπ : Function.Surjective π) (hker : ∀ y : ↥Y, π y = 1 ↔ (y : G) ∈ N) (φB : MulAut B)
    (hφ : ∀ y : ↥Y, π (conjOn Y g hgY y) = φB (π y)) :
    chiC A Y g = chiC A N g + A.chi B φB := by
  rw [chiC_of_mem A Y hgY, chiC_of_mem A N hgN]
  refine A.chi_exact hY (Subgroup.inclusion hNY) π (Subgroup.inclusion_injective hNY) hπ ?_
    (conjOn N g hgN) (conjOn Y g hgY) φB (conjOn_pow_seven Y g hgY hg7) (fun a => rfl) hφ
  ext y
  constructor
  · rintro ⟨a, rfl⟩
    exact (hker _).2 a.2
  · intro hy
    exact ⟨⟨y, (hker y).1 hy⟩, rfl⟩

theorem chiC_conj (A : ChiAPI) (Y : Subgroup G) {g w : G}
    (hw : w ∈ Subgroup.normalizer (Y : Set G)) (hg : g ∈ Subgroup.normalizer (Y : Set G)) :
    chiC A Y (w * g * w⁻¹) = chiC A Y g := by
  have hg' : w * g * w⁻¹ ∈ Subgroup.normalizer (Y : Set G) :=
    (Subgroup.normalizer (Y : Set G)).mul_mem ((Subgroup.normalizer (Y : Set G)).mul_mem hw hg)
      ((Subgroup.normalizer (Y : Set G)).inv_mem hw)
  rw [chiC_of_mem A Y hg', chiC_of_mem A Y hg]
  refine A.chi_congr (conjOn Y w hw) (conjOn Y g hg) (conjOn Y (w * g * w⁻¹) hg') fun x => ?_
  apply Subtype.ext
  simp only [conjOn_apply]
  group

theorem chiC_of_centralizes (A : ChiAPI) (Y : Subgroup G) {g : G}
    (hg : g ∈ Subgroup.normalizer (Y : Set G)) (h : ∀ y ∈ Y, g * y * g⁻¹ = y) :
    chiC A Y g = 0 := by
  rw [chiC_of_mem A Y hg, conjOn_eq_one Y g hg h, A.chi_one]

theorem chiC_bot (A : ChiAPI) (g : G) : chiC A (⊥ : Subgroup G) g = 0 := by
  have hg : g ∈ Subgroup.normalizer ((⊥ : Subgroup G) : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    simp [conj_eq_one_iff]
  exact chiC_of_centralizes A ⊥ hg fun y hy => by rw [Subgroup.mem_bot.1 hy]; simp

@[expose] def prodAut {C U : Type} [Group C] [Group U] (φ : MulAut C) (ψ : MulAut U) :
    MulAut (C × U) := MulEquiv.prodCongr φ ψ

theorem prodAut_apply {C U : Type} [Group C] [Group U] (φ : MulAut C) (ψ : MulAut U)
    (x : C × U) : prodAut φ ψ x = (φ x.1, ψ x.2) := rfl

theorem prodAut_pow {C U : Type} [Group C] [Group U] (φ : MulAut C) (ψ : MulAut U) (n : ℕ) :
    prodAut φ ψ ^ n = prodAut (φ ^ n) (ψ ^ n) := by
  induction n with
  | zero => exact MulEquiv.ext fun x => rfl
  | succ n ih =>
    rw [pow_succ, ih, pow_succ, pow_succ]
    exact MulEquiv.ext fun x => rfl

theorem chi_prod (A : ChiAPI) {C U : Type} [Group C] [Group U] [Finite C] [Finite U]
    (hP : IsPGroup 2 (C × U)) (φ : MulAut C) (ψ : MulAut U) (hφ : φ ^ 7 = 1) (hψ : ψ ^ 7 = 1) :
    A.chi (C × U) (prodAut φ ψ) = A.chi C φ + A.chi U ψ := by
  have h7 : prodAut φ ψ ^ 7 = 1 := by
    rw [prodAut_pow, hφ, hψ]
    exact MulEquiv.ext fun x => rfl
  refine A.chi_exact hP (MonoidHom.inl C U) (MonoidHom.snd C U) (fun a b h => (Prod.mk.inj h).1)
    (fun u => ⟨(1, u), rfl⟩) ?_ φ (prodAut φ ψ) ψ h7 (fun a => by simp [prodAut_apply])
    (fun m => by simp [prodAut_apply])
  ext m
  rw [MonoidHom.mem_range, MonoidHom.mem_ker]
  constructor
  · rintro ⟨a, rfl⟩
    rfl
  · intro hm
    exact ⟨m.1, Prod.ext rfl hm.symm⟩

theorem chiC_split (A : ChiAPI) {Z C U : Subgroup G} (hZ : IsPGroup 2 ↥Z) (hCZ : C ≤ Z)
    (hUZ : U ≤ Z) (hcomm : ∀ c ∈ C, ∀ u ∈ U, c * u = u * c) (hdisj : C ⊓ U = ⊥)
    (hsup : C ⊔ U = Z) {g : G} (hgZ : g ∈ Subgroup.normalizer (Z : Set G))
    (hgC : g ∈ Subgroup.normalizer (C : Set G)) (hgU : g ∈ Subgroup.normalizer (U : Set G))
    (hg7 : g ^ 7 = 1) : chiC A Z g = chiC A C g + chiC A U g := by
  have hcomm' : ∀ (c : ↥C) (u : ↥U),
      Commute (Subgroup.inclusion hCZ c) (Subgroup.inclusion hUZ u) := fun c u =>
    Subtype.ext (hcomm _ c.2 _ u.2)
  set e0 : ↥C × ↥U →* ↥Z := (Subgroup.inclusion hCZ).noncommCoprod (Subgroup.inclusion hUZ) hcomm'
    with he0
  have hinj : Function.Injective e0 := by
    rw [he0, MonoidHom.noncommCoprod_injective]
    refine ⟨Subgroup.inclusion_injective hCZ, Subgroup.inclusion_injective hUZ, ?_⟩
    rw [Subgroup.inclusion_range, Subgroup.inclusion_range, Subgroup.disjoint_def]
    intro x hxC hxU
    have hx : (x : G) ∈ C ⊓ U := ⟨hxC, hxU⟩
    rw [hdisj, Subgroup.mem_bot] at hx
    exact Subtype.ext hx
  have hsurj : Function.Surjective e0 := by
    rw [← MonoidHom.range_eq_top, he0, MonoidHom.noncommCoprod_range, Subgroup.inclusion_range,
      Subgroup.inclusion_range, ← Subgroup.subgroupOf_sup hCZ hUZ, hsup, Subgroup.subgroupOf_self]
  let e : ↥C × ↥U ≃* ↥Z := MulEquiv.ofBijective e0 ⟨hinj, hsurj⟩
  have he : ∀ c u, (e (c, u) : G) = c * u := fun c u => rfl
  rw [chiC_of_mem A Z hgZ, chiC_of_mem A C hgC, chiC_of_mem A U hgU]
  have hP : IsPGroup 2 (↥C × ↥U) := hZ.of_equiv e.symm
  have h1 : A.chi ↥Z (conjOn Z g hgZ) =
      A.chi (↥C × ↥U) (prodAut (conjOn C g hgC) (conjOn U g hgU)) := by
    refine A.chi_congr e (prodAut (conjOn C g hgC) (conjOn U g hgU)) (conjOn Z g hgZ) ?_
    rintro ⟨c, u⟩
    apply Subtype.ext
    simp only [he, conjOn_apply, prodAut_apply]
    group
  rw [h1]
  exact chi_prod A hP _ _ (conjOn_pow_seven C g hgC hg7) (conjOn_pow_seven U g hgU hg7)

end CFSG.Quasithin.SzC4
