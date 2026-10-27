module

public import CFSG.RankThree.PartOne.S9.Sylow.ExclusionBasic
public import CFSG.RankThree.PartOne.S9.Defs

public section

namespace CFSG.RankThree.PartOne.Sec9Excl

open Subgroup CFSG

variable {G : Type*} [Group G]

theorem le_normalizer_map_subtype (H : Subgroup G) (N : Subgroup H) [N.Normal] :
    H ≤ normalizer ((N.map H.subtype : Subgroup G) : Set G) := by
  have key : ∀ h : G, h ∈ H → ∀ x ∈ N.map H.subtype, h * x * h⁻¹ ∈ N.map H.subtype := by
    intro h hh x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    exact Subgroup.mem_map.mpr ⟨⟨h, hh⟩ * y * ⟨h, hh⟩⁻¹,
      Normal.conj_mem inferInstance y hy ⟨h, hh⟩, rfl⟩
  intro h hh
  exact mem_normalizer_of_forward (key h hh) (fun x hx => by
    simpa using key h⁻¹ (Subgroup.inv_mem _ hh) x hx)

theorem isPGroup_inSubgroup_pCore (q : ℕ) (H : Subgroup G) :
    IsPGroup q (inSubgroup (pCore q) H) :=
  IsPGroup.map (pCore_isPGroup (p := q) (G := H)) H.subtype

theorem le_normalizer_inSubgroup_pCore (q : ℕ) (H : Subgroup G) :
    H ≤ normalizer ((inSubgroup (pCore q) H : Subgroup G) : Set G) :=
  le_normalizer_map_subtype H (pCore q H)

theorem mem_normalizer_inSubgroup_pCore (q : ℕ) {W : Subgroup G} {c : G}
    (hc : c ∈ normalizer (W : Set G)) :
    c ∈ normalizer ((inSubgroup (pCore q) W : Subgroup G) : Set G) := by
  have key : ∀ c : G, c ∈ normalizer (W : Set G) →
      ∀ x ∈ inSubgroup (pCore q) W, c * x * c⁻¹ ∈ inSubgroup (pCore q) W := by
    intro c hc x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    let φ : MulAut W := W.normalizerMonoidHom ⟨c, hc⟩
    have hφ : φ y ∈ pCore q W := by
      have h := (pCore_characteristic (p := q) (G := W)).fixed φ
      have : y ∈ (pCore q W).comap φ.toMonoidHom := by rw [h]; exact hy
      exact this
    exact Subgroup.mem_map.mpr ⟨φ y, hφ, rfl⟩
  exact mem_normalizer_of_forward (key c hc) (fun x hx => by
    simpa using key c⁻¹ (Subgroup.inv_mem _ hc) x hx)

theorem omegaOne_le (q : ℕ) (K : Subgroup G) : omegaOne q K ≤ K :=
  (Subgroup.closure_le K).mpr fun _ hx => hx.1

theorem mem_normalizer_omegaOne {q : ℕ} {K : Subgroup G} {h : G}
    (hh : h ∈ normalizer (K : Set G)) : h ∈ normalizer ((omegaOne q K : Subgroup G) : Set G) := by
  have key : ∀ h : G, h ∈ normalizer (K : Set G) →
      ∀ x ∈ omegaOne q K, h * x * h⁻¹ ∈ omegaOne q K := by
    intro h hh x hx
    have hle : omegaOne q K ≤ (omegaOne q K).comap (MulAut.conj h).toMonoidHom := by
      refine (Subgroup.closure_le _).mpr ?_
      rintro y ⟨hyK, hyq⟩
      refine Subgroup.subset_closure ⟨(Subgroup.mem_normalizer_iff.mp hh y).mp hyK, ?_⟩
      show (h * y * h⁻¹) ^ q = 1
      rw [conj_pow, hyq]
      group
    exact hle hx
  exact mem_normalizer_of_forward (key h hh) (fun x hx => by
    simpa using key h⁻¹ (Subgroup.inv_mem _ hh) x hx)

theorem mem_normalizer_zpowers_self (c : G) :
    c ∈ normalizer ((zpowers c : Subgroup G) : Set G) :=
  Subgroup.le_normalizer (Subgroup.mem_zpowers c)

theorem le_normalizer_zpowers_of_mem {A : Subgroup G} [IsMulCommutative A] {c : G} (hc : c ∈ A) :
    A ≤ normalizer ((zpowers c : Subgroup G) : Set G) := by
  intro a ha
  have hcomm : Commute c a := (congrArg Subtype.val (mul_comm' (⟨c, hc⟩ : A) ⟨a, ha⟩))
  refine centralizer_le_normalizer _ ?_
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  exact (hcomm.zpow_left k).eq

theorem mul_comm_of_isPGroup {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) {c : G}
    (hc : orderOf c = p) {D : Subgroup G} (hD : IsPGroup q D)
    (hDc : D ≤ normalizer ((zpowers c : Subgroup G) : Set G))
    (hcD : c ∈ normalizer (D : Set G)) {d : G} (hd : d ∈ D) : c * d = d * c := by
  have hz : IsPGroup p (zpowers c) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hc, pow_one])
  exact mul_comm_of_inf_eq_bot (inf_eq_bot_of_isPGroup hp hq hpq hz hD) (Subgroup.mem_zpowers c)
    hd hcD (hDc hd)

theorem commutator_inSubgroup_frattini_eq_bot [Finite G] {q : ℕ} (hq : q.Prime) {R A D : Subgroup G}
    (hRD : R ≤ normalizer (D : Set G)) (hAD : A ≤ normalizer (D : Set G)) (hRA : ⁅R, A⁆ = R)
    (hD : IsQDShape q D) : ⁅R, inSubgroup frattini D⁆ = ⊥ := by
  have : Fact q.Prime := ⟨hq⟩
  rcases hD with ⟨hel, -⟩ | ⟨-, -, hcard, -, hfrat⟩
  · have hpg : Fact (IsPGroup q D) := ⟨IsElementaryAbelian.isPGroup q D⟩
    have : inSubgroup frattini D = ⊥ := by
      rw [inSubgroup, frattini_eq_bot_of_isElementaryAbelian (p := q), Subgroup.map_bot]
    rw [this, Subgroup.commutator_bot_right]
  · rw [hfrat]
    have hcyc : IsCyclic (⁅D, D⁆ : Subgroup G) := isCyclic_of_prime_card hcard
    have hR : R ≤ normalizer ((⁅D, D⁆ : Subgroup G) : Set G) := fun r hr =>
      mem_normalizer_commutator (hRD hr) (hRD hr)
    have hA : A ≤ normalizer ((⁅D, D⁆ : Subgroup G) : Set G) := fun a ha =>
      mem_normalizer_commutator (hAD ha) (hAD ha)
    have h1 := commutator_le_centralizer_of_isCyclic hcyc hR hA
    rw [hRA] at h1
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr h1

end CFSG.RankThree.PartOne.Sec9Excl
