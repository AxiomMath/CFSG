module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Walter.ReeOrder.JT.Section7G

public section

namespace CFSG.Walter.JT

open scoped IsMulCommutative Pointwise MatrixGroups

variable {G : Type} [Group G] [Finite G]

structure TorusConf (h : JTHyp G) where
  C : Subgroup G
  w : G
  torus : TorusData h.F C w
  card_C : 2 * Nat.card C + 1 = h.q

namespace JTHyp

variable (h : JTHyp G) (hp3 : h.p = 3)
include hp3

theorem exists_conj_of_isCyclic {C₁ C₂ : Subgroup G} (hC₁F : C₁ ≤ h.F) (hC₂F : C₂ ≤ h.F)
    (hC₁ : IsCyclic C₁) (hC₂ : IsCyclic C₂) (h₁ : 2 * Nat.card C₁ + 1 = h.q)
    (h₂ : 2 * Nat.card C₂ + 1 = h.q) :
    ∃ g ∈ h.F, C₂ = C₁.map (MulAut.conj g).toMonoidHom := by
  classical
  have hp := h.p_ne_two_of_eq_three hp3
  have hf := h.f_ne_zero
  set K := GaloisField h.p h.f
  have hKcard : Nat.card K = h.p ^ h.f := GaloisField.card h.p h.f hf
  let ι : PSL(2, K) →* G := h.F.subtype.comp h.iso.symm.toMonoidHom
  have hι : Function.Injective ι := h.F.subtype_injective.comp h.iso.symm.injective
  have hrange : ι.range = h.F := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact (h.iso.symm y).2
    · intro hx
      exact ⟨h.iso ⟨x, hx⟩, by simp [ι]⟩
  have hmapcomap : ∀ X : Subgroup G, X ≤ h.F → (X.comap ι).map ι = X := fun X hX =>
    Subgroup.map_comap_eq_self (hrange ▸ hX)
  have hcyc : ∀ X : Subgroup G, X ≤ h.F → IsCyclic X → IsCyclic (X.comap ι) := by
    intro X hX hXc
    exact isCyclic_of_surjective (((X.comap ι).equivMapOfInjective ι hι).trans
      (MulEquiv.subgroupCongr (hmapcomap X hX))).symm (MulEquiv.surjective _)
  have hcard : ∀ X : Subgroup G, X ≤ h.F → Nat.card (X.comap ι) = Nat.card X := fun X hX => by
    rw [← Subgroup.card_map_of_injective hι, hmapcomap X hX]
  have h5 : 5 ≤ h.p ^ h.f := h.five_lt.le
  obtain ⟨g, hg⟩ := psl2_exists_conj_of_cyclic hKcard hp hf h5 (hcyc C₁ hC₁F hC₁)
    (hcyc C₂ hC₂F hC₂) (by rw [hcard C₁ hC₁F]; exact h₁) (by rw [hcard C₂ hC₂F]; exact h₂)
  have hcomm : ι.comp (MulAut.conj g).toMonoidHom = (MulAut.conj (ι g)).toMonoidHom.comp ι := by
    ext x
    simp [map_mul, map_inv]
  refine ⟨ι g, hrange ▸ ⟨g, rfl⟩, ?_⟩
  rw [← hmapcomap C₂ hC₂F, hg, Subgroup.map_map, hcomm, ← Subgroup.map_map, hmapcomap C₁ hC₁F]

theorem nonempty_torusConf :
    Nonempty (TorusConf h) := by
  have hp := h.p_ne_two_of_eq_three hp3
  have hq8 := h.q_mod_eight_of_eq_three hp3
  obtain ⟨U, w, hU, hUcard⟩ := (h.facts hp).odd_torus
  refine ⟨⟨U, w, hU, ?_⟩⟩
  rw [JTHyp.q_eq] at hq8 ⊢
  rcases hUcard with ⟨-, h1⟩ | ⟨h1, -⟩
  · exact h1
  · omega

theorem exists_conj_mem_of_commute
    {C : Subgroup G} (hCF : C ≤ h.F) (hC : IsCyclic C)
    (hCcard : 2 * Nat.card C + 1 = h.q) {r : ℕ} [hr : Fact r.Prime] (hrq : r ∣ (h.q - 1) / 2)
    {x u : G} (hx : orderOf x = r) (hu : orderOf u = 2) (hxu : x * u = u * x) :
    ∃ g : G, g * x * g⁻¹ ∈ C := by
  classical
  have hp := h.p_ne_two_of_eq_three hp3
  have hr7 := h.seven_le_of_pi hp3 hrq
  obtain ⟨a, ha⟩ := h.exists_conj_eq_t hp hu
  have hx'o : orderOf (a * x * a⁻¹) = r := by
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, hx]
  have hx't : a * x * a⁻¹ ∈ Subgroup.centralizer ({h.t} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff, ← ha]
    calc a * x * a⁻¹ * (a * u * a⁻¹) = a * (x * u) * a⁻¹ := by group
      _ = a * (u * x) * a⁻¹ := by rw [hxu]
      _ = a * u * a⁻¹ * (a * x * a⁻¹) := by group
  have hx'F : a * x * a⁻¹ ∈ h.F :=
    h.mem_F_of_odd hx't (by rw [hx'o]; exact hr.out.odd_of_ne_two (by omega))
  have hx'1 : a * x * a⁻¹ ≠ 1 := fun h0 => by
    rw [h0, orderOf_one] at hx'o
    exact hr.out.one_lt.ne hx'o
  have hcop : Nat.Coprime (orderOf (a * x * a⁻¹)) h.p := by
    rw [hx'o, hp3]
    exact (Nat.coprime_primes hr.out Nat.prime_three).mpr (by omega)
  obtain ⟨C', hC'F, hC'c, hx'C', hC'card⟩ :=
    exists_cyclic_of_coprime h.F h.iso hp h.five_lt hx'F hx'1 hcop
  rw [← JTHyp.q_eq] at hC'card
  have hC'card' : 2 * Nat.card C' + 1 = h.q := by
    rcases hC'card with h1 | h1
    · exact h1
    · exfalso
      have h2 : r ∣ Nat.card C' := hx'o ▸ Subgroup.orderOf_dvd_natCard C' hx'C'
      have h3 : r ∣ Nat.card C' - (h.q - 1) / 2 := Nat.dvd_sub h2 hrq
      have hq3 := h.three_dvd_q hp3
      have hq8 := h.q_mod_eight_of_eq_three hp3
      have : Nat.card C' - (h.q - 1) / 2 = 1 := by omega
      rw [this] at h3
      exact hr.out.one_lt.ne' (Nat.dvd_one.mp h3)
  obtain ⟨f, -, hf⟩ := h.exists_conj_of_isCyclic hp3 hC'F hCF hC'c hC hC'card' hCcard
  refine ⟨f * a, ?_⟩
  rw [hf]
  refine ⟨a * x * a⁻¹, hx'C', ?_⟩
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  group

theorem not_three_dvd_card_centralizer_of_commute
    (c : TorusConf h) {r : ℕ} [hr : Fact r.Prime]
    (hrq : r ∣ (h.q - 1) / 2) {x u : G} (hx : orderOf x = r) (hu : orderOf u = 2)
    (hxu : x * u = u * x) : ¬ 3 ∣ Nat.card (Subgroup.centralizer ({x} : Set G)) := by
  obtain ⟨g, hg⟩ := h.exists_conj_mem_of_commute hp3 c.torus.le c.torus.cyclic c.card_C hrq hx hu
    hxu
  have hr7 := h.seven_le_of_pi hp3 hrq
  have hg1 : g * x * g⁻¹ ≠ 1 := by
    intro h0
    have : x = 1 := by
      have := congrArg (fun y => g⁻¹ * y * g) h0
      simpa [mul_assoc] using this
    rw [this, orderOf_one] at hx
    omega
  have h74 := h.lemma_7_4 hp3 c.torus.le c.torus.cyclic c.card_C hg hg1
  have hcard : Nat.card (Subgroup.centralizer ({g * x * g⁻¹} : Set G)) =
      Nat.card (Subgroup.centralizer ({x} : Set G)) := by
    have := centralizer_singleton_map (MulAut.conj g) x
    rw [MulAut.conj_apply] at this
    rw [← this, Subgroup.card_map_of_injective (MulAut.conj g).injective]
  rwa [hcard] at h74

end JTHyp

end CFSG.Walter.JT
