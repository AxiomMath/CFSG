module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtNoE9Z4P0Pln

public section

namespace CFSG.Quasithin

namespace E9Z4Str

variable {V : Type} [CommGroup V] [Finite V] {X Tb P P₁ P₂ : Subgroup (MulAut V)}

theorem eq_one_of_fix_plane (h : E9Z4Str X Tb P) {Q : Subgroup (MulAut V)} (hQ3 : Nat.card Q = 3)
    {g : MulAut V} (hg : g ∈ Q) (hg1 : g ≠ 1) {v : V} (hv : v ∈ commV Q) (hgv : g v = v) :
    v = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hz := zpowers_eq_of_prime_card hQ3 hg hg1
  obtain ⟨-, hinf, -, -⟩ := commV_card_three h.sq hQ3
  have hmem : v ∈ commV Q ⊓ fixV Q := ⟨hv, by rw [← hz]; exact mem_fixV_zpowers_iff.mpr hgv⟩
  rw [hinf, Subgroup.mem_bot] at hmem
  exact hmem

theorem plane_transitive (h : E9Z4Str X Tb P) {Q : Subgroup (MulAut V)} (hQ3 : Nat.card Q = 3)
    (hrk : rk (commV Q) = 2) {v w : V} (hv : v ∈ commV Q) (hw : w ∈ commV Q) (hv1 : v ≠ 1)
    (hw1 : w ≠ 1) : ∃ a ∈ Q, a v = w := by
  have hmem : ∀ a : Q, (a : MulAut V) v ∈ commV Q ∧ (a : MulAut V) v ≠ 1 := fun a =>
    ⟨commV_smul_mem (fun q hq => Q.mul_mem (Q.mul_mem a.2 hq) (Q.inv_mem a.2)) hv, fun e =>
      hv1 ((a : MulAut V).injective (by rw [e, map_one]))⟩
  let f : Q → {c : V // c ∈ commV Q ∧ c ≠ 1} := fun a => ⟨(a : MulAut V) v, hmem a⟩
  have hinj : Function.Injective f := by
    intro a b hab
    have hab' : (a : MulAut V) v = (b : MulAut V) v := congrArg Subtype.val hab
    have hfix : ((b : MulAut V)⁻¹ * a) v = v := by
      rw [MulAut.mul_apply, hab']
      simp
    have h1 : (b : MulAut V)⁻¹ * a = 1 := by
      by_contra hne
      exact hv1 (h.eq_one_of_fix_plane hQ3 (Q.mul_mem (Q.inv_mem b.2) a.2) hne hv hfix)
    exact Subtype.ext (inv_mul_eq_one.mp h1).symm
  have hcard : Nat.card {c : V // c ∈ commV Q ∧ c ≠ 1} = 3 := by
    have := card_ne_one_add_one (commV Q)
    rw [card_eq_two_pow h.sq, hrk] at this
    omega
  have hbij : Function.Bijective f :=
    hinj.bijective_of_nat_card_le (by rw [hcard, hQ3])
  obtain ⟨a, ha⟩ := hbij.2 ⟨w, hw, hw1⟩
  exact ⟨a, a.2, congrArg Subtype.val ha⟩

omit [Finite V] in
theorem exists_mul_planes (h : E9Z4Str X Tb P) (hp : PlanePair Tb P P₁ P₂) {a : MulAut V}
    (ha : a ∈ P) : ∃ a₁ ∈ P₁, ∃ a₂ ∈ P₂, a = a₁ * a₂ := by
  obtain ⟨hP₁, hP₂, -, -, hsup, -⟩ := hp
  have hn : P₂ ≤ Subgroup.normalizer (P₁ : Set (MulAut V)) := by
    intro y hy
    rw [Subgroup.mem_normalizer_iff]
    intro q
    have hcomm : ∀ z ∈ P₁, y * z * y⁻¹ = z := fun z hz => by
      rw [h.comm_P y (hP₂ hy) z (hP₁ hz)]
      group
    constructor
    · intro hq
      rw [hcomm q hq]
      exact hq
    · intro hq
      have h1 : y⁻¹ * (y * q * y⁻¹) * y = y * q * y⁻¹ := by
        rw [h.comm_P y⁻¹ (P.inv_mem (hP₂ hy)) _ (hP₁ hq)]
        group
      have hq' : q = y * q * y⁻¹ := by
        calc q = y⁻¹ * (y * q * y⁻¹) * y := by group
          _ = y * q * y⁻¹ := h1
      rwa [← hq'] at hq
  have hmem : a ∈ ((P₁ ⊔ P₂ : Subgroup (MulAut V)) : Set (MulAut V)) := by
    rw [hsup]
    exact ha
  rw [Subgroup.coe_mul_of_right_le_normalizer_left P₁ P₂ hn] at hmem
  obtain ⟨a₁, ha₁, a₂, ha₂, rfl⟩ := Set.mem_mul.mp hmem
  exact ⟨a₁, ha₁, a₂, ha₂, rfl⟩

theorem nonsingular_eq (h : E9Z4Str X Tb P) (hp : PlanePair Tb P P₁ P₂) :
    Nonsingular P = {v | v ≠ 1 ∧ (v ∈ commV P₁ ∨ v ∈ commV P₂)} := by
  have hp' := hp
  obtain ⟨hP₁, hP₂, hc₁, hc₂, -, hdisj, hcsup, hf₁, hf₂, -⟩ := hp
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  ext v
  constructor
  · rintro ⟨hv1, a, ha, ha1, hav⟩
    refine ⟨hv1, ?_⟩
    obtain ⟨a₁, ha₁, a₂, ha₂, rfl⟩ := h.exists_mul_planes hp' ha
    have hvsup : v ∈ commV P₁ ⊔ commV P₂ := by
      rw [hcsup]
      exact Subgroup.mem_top v
    obtain ⟨v₁, hv₁, v₂, hv₂, rfl⟩ := Subgroup.mem_sup.mp hvsup
    have hinv₁ : a₁ v₁ ∈ commV P₁ :=
      commV_smul_mem (fun q hq => P₁.mul_mem (P₁.mul_mem ha₁ hq) (P₁.inv_mem ha₁)) hv₁
    have hinv₂ : a₂ v₂ ∈ commV P₂ :=
      commV_smul_mem (fun q hq => P₂.mul_mem (P₂.mul_mem ha₂ hq) (P₂.inv_mem ha₂)) hv₂
    have h2v₁ : a₂ v₁ = v₁ := hf₁ hv₁ a₂ ha₂
    have h1w₂ : a₁ (a₂ v₂) = a₂ v₂ := hf₂ hinv₂ a₁ ha₁
    have hav' : a₁ v₁ * a₂ v₂ = v₁ * v₂ := by
      have : (a₁ * a₂) (v₁ * v₂) = a₁ v₁ * a₂ v₂ := by
        simp only [MulAut.mul_apply, map_mul]
        rw [h2v₁, h1w₂]
      rw [← this]
      exact hav
    have hpair := Subgroup.mul_injective_of_disjoint hdisj
      (a₁ := (⟨a₁ v₁, hinv₁⟩, ⟨a₂ v₂, hinv₂⟩)) (a₂ := (⟨v₁, hv₁⟩, ⟨v₂, hv₂⟩)) hav'
    have e₁ : a₁ v₁ = v₁ := congrArg (fun p => (p.1 : V)) hpair
    have e₂ : a₂ v₂ = v₂ := congrArg (fun p => (p.2 : V)) hpair
    by_cases h1 : a₁ = 1
    · by_cases h2 : a₂ = 1
      · exact (ha1 (by rw [h1, h2, one_mul])).elim
      · have : v₂ = 1 := h.eq_one_of_fix_plane hc₂ ha₂ h2 hv₂ e₂
        left
        rw [this, mul_one]
        exact hv₁
    · have : v₁ = 1 := h.eq_one_of_fix_plane hc₁ ha₁ h1 hv₁ e₁
      right
      rw [this, one_mul]
      exact hv₂
  · rintro ⟨hv1, hv | hv⟩
    · obtain ⟨g, hg, hg1, -, -⟩ := exists_generator_of_prime_card hc₂
      exact ⟨hv1, g, hP₂ hg, hg1, hf₁ hv g hg⟩
    · obtain ⟨g, hg, hg1, -, -⟩ := exists_generator_of_prime_card hc₁
      exact ⟨hv1, g, hP₁ hg, hg1, hf₂ hv g hg⟩

omit [Finite V] in
theorem nonsingular_stable (h : E9Z4Str X Tb P) {x : MulAut V} (hx : x ∈ X) {v : V}
    (hv : v ∈ Nonsingular P) : x v ∈ Nonsingular P := by
  obtain ⟨hv1, a, ha, ha1, hav⟩ := hv
  refine ⟨fun e => hv1 (x.injective (by rw [e, map_one])), x * a * x⁻¹, h.normalP x hx a ha,
    fun e => ha1 ?_, ?_⟩
  · have h1 : x⁻¹ * (x * a * x⁻¹) * x = a := by group
    rw [← h1, e]
    group
  · show (x * a * x⁻¹) (x v) = x v
    simp [MulAut.mul_apply, hav]

omit [Finite V] in
theorem exists_mem_plane_one (h : E9Z4Str X Tb P) (hp : PlanePair Tb P P₁ P₂) {u : V} (hu1 : u ≠ 1)
    (hu : u ∈ commV P₁ ∨ u ∈ commV P₂) : ∃ x ∈ X, x u ∈ commV P₁ ∧ x u ≠ 1 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, σ, hσ, hσP⟩ := hp
  rcases hu with hu | hu
  · exact ⟨1, X.one_mem, by simpa using hu, by simpa using hu1⟩
  · have hσB : commV P₂ = (commV P₁).map (MulEquiv.toMonoidHom σ) := by
      rw [← hσP, commV_conjBy]
    rw [hσB] at hu
    obtain ⟨z, hz, rfl⟩ := hu
    refine ⟨σ⁻¹, X.inv_mem (h.Tb_le_X hσ), ?_, ?_⟩
    · simpa using hz
    · intro e
      apply hu1
      have hz1 : z = 1 := by simpa using e
      show σ z = 1
      rw [hz1, map_one]

theorem nonsingular_transitive (h : E9Z4Str X Tb P) {v w : V} (hv : v ∈ Nonsingular P)
    (hw : w ∈ Nonsingular P) : ∃ x ∈ X, x v = w := by
  obtain ⟨P₁, P₂, hp⟩ := h.exists_planePair
  have hr := h.rk_commV_plane hp
  rw [h.nonsingular_eq hp] at hv hw
  obtain ⟨x, hx, hxv, hxv1⟩ := h.exists_mem_plane_one hp hv.1 hv.2
  obtain ⟨y, hy, hyw, hyw1⟩ := h.exists_mem_plane_one hp hw.1 hw.2
  obtain ⟨hP₁, -, hc₁, -⟩ := hp
  obtain ⟨a, ha, hax⟩ := h.plane_transitive hc₁ hr.1 hxv hyw hxv1 hyw1
  refine ⟨y⁻¹ * a * x, X.mul_mem (X.mul_mem (X.inv_mem hy) (h.P_le_X (hP₁ ha))) hx, ?_⟩
  show y⁻¹ (a (x v)) = w
  rw [hax]
  simp

end E9Z4Str

end CFSG.Quasithin
