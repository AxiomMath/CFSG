module

public import CFSG.Quasithin.Background.RonanE611Defs
public import CFSG.Quasithin.Background.ONanE68LieBar

public section

namespace CFSG.Quasithin.RonanE611

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.E6.E68Proof

section Sylow

variable {G : Type} [Group G] [Finite G]

theorem isSylowTwoOf_of_le {S P L : Subgroup G} (hS : IsSylowTwoOf S L) (hSP : S ≤ P)
    (hPL : P ≤ L) : IsSylowTwoOf S P := by
  refine ⟨hSP, hS.2.1, fun h => hS.2.2 ?_⟩
  have h1 := Subgroup.relIndex_mul_relIndex S P L hSP hPL
  have h2 : (S.subgroupOf P).index = S.relIndex P := rfl
  have h3 : (S.subgroupOf L).index = S.relIndex L := rfl
  rw [h3, ← h1]
  rw [h2] at h
  exact Dvd.dvd.mul_right h _

theorem exists_conj_mem_of_two_element {P S : Subgroup G} (hS : IsSylowTwoOf S P) {y : G}
    (hyP : y ∈ P) (hy : ∃ k : ℕ, y ^ 2 ^ k = 1) : ∃ p ∈ P, p * y * p⁻¹ ∈ S := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := hy
  have hS0 := isSylowTwoOf_subgroupOf_top_of hS
  have hS02 : IsPGroup 2 (S.subgroupOf P) := hS0.2.1
  have hS0i : ¬ 2 ∣ (S.subgroupOf P).index := by
    have := hS0.2.2
    rwa [show ((S.subgroupOf P).subgroupOf (⊤ : Subgroup ↥P)).index = (S.subgroupOf P).index from
      Subgroup.relIndex_top_right _] at this
  let S₀ : Sylow 2 ↥P := hS02.toSylow hS0i
  set yb : ↥P := ⟨y, hyP⟩ with hyb
  have hybk : yb ^ 2 ^ k = 1 := Subtype.ext (by simpa using hk)
  have hgrp : IsPGroup 2 (Subgroup.zpowers yb) := by
    have hord : orderOf yb ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hybk
    obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hord
    exact IsPGroup.of_card (n := m) (by rw [Nat.card_zpowers, hm])
  obtain ⟨Q, hQ⟩ := hgrp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (↥P) Q S₀
  have hmem : ∀ z : ↥P, z ∈ Subgroup.zpowers yb → g * z * g⁻¹ ∈ (S₀ : Subgroup ↥P) := by
    intro z hz
    have h1 : z ∈ (Q : Subgroup ↥P) := hQ hz
    have h2 : g * z * g⁻¹ ∈ ((g • Q : Sylow 2 ↥P) : Subgroup ↥P) := by
      rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def,
        MulAut.conj_inv_apply]
      simpa [mul_assoc] using h1
    rw [hg] at h2
    exact h2
  have h3 := hmem yb (Subgroup.mem_zpowers yb)
  refine ⟨(g : G), g.2, ?_⟩
  have h4 : (g * yb * g⁻¹ : ↥P) ∈ S.subgroupOf P := h3
  exact h4

end Sylow

section RootGroup

variable {Y : Type} [Group Y] [Finite Y]

theorem le_rootGroupOfParabolicR {P S W : Subgroup Y} (hS : IsSylowTwoOf S P) (hWS : W ≤ S)
    (hWc : ∀ w ∈ W, ∀ s ∈ S, w * s = s * w) (hWn : ∀ p ∈ P, ∀ w ∈ W, p * w * p⁻¹ ∈ W)
    (hW2 : ∀ w ∈ W, ∃ k : ℕ, w ^ 2 ^ k = 1) : W ≤ rootGroupOfParabolicR P := by
  intro w hw
  refine Subgroup.mem_inf.2 ⟨Subgroup.subset_closure ⟨hS.1 (hWS hw), hW2 w hw⟩, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have key : y * w = w * y := by
    refine Subgroup.closure_induction (p := fun y _ => y * w = w * y) ?_ ?_ ?_ ?_ hy
    · intro x hx
      obtain ⟨hxP, hx2⟩ := hx
      obtain ⟨p, hp, hpx⟩ := exists_conj_mem_of_two_element hS hxP hx2
      have hw' : p * w * p⁻¹ ∈ W := hWn p hp w hw
      have h1 := hWc _ hw' _ hpx
      have h2 : p * (w * x) * p⁻¹ = p * (x * w) * p⁻¹ := by
        have e1 : p * (w * x) * p⁻¹ = (p * w * p⁻¹) * (p * x * p⁻¹) := by group
        have e2 : p * (x * w) * p⁻¹ = (p * x * p⁻¹) * (p * w * p⁻¹) := by group
        rw [e1, e2]
        exact h1
      exact (mul_left_cancel (mul_right_cancel h2)).symm
    · simp
    · intro a b _ _ ha hb
      calc a * b * w = a * (b * w) := by rw [mul_assoc]
        _ = a * (w * b) := by rw [hb]
        _ = (a * w) * b := by rw [mul_assoc]
        _ = (w * a) * b := by rw [ha]
        _ = w * (a * b) := by rw [mul_assoc]
    · intro a _ ha
      calc a⁻¹ * w = a⁻¹ * w * a * a⁻¹ := by group
        _ = a⁻¹ * (w * a) * a⁻¹ := by rw [mul_assoc a⁻¹ w a]
        _ = a⁻¹ * (a * w) * a⁻¹ := by rw [← ha]
        _ = w * a⁻¹ := by group
  exact key

end RootGroup

section OddIndex

variable {G : Type} [Group G] [Finite G]

theorem normalizes_of_odd_index {N Q W W₁ W₂ : Subgroup G} (hQ : IsSylowTwoOf Q N)
    (hQW : Q ≤ Subgroup.normalizer (W : Set G))
    (hW : ∀ g ∈ N, W.map (MulAut.conj g).toMonoidHom = W₁ ∨ W.map (MulAut.conj g).toMonoidHom = W₂) :
    N ≤ Subgroup.normalizer (W : Set G) := by
  classical
  set T : Subgroup ↥N := (Subgroup.normalizer (W : Set G)).subgroupOf N with hT
  have hQT : Q.subgroupOf N ≤ T := fun q hq => hQW hq
  have hodd : ¬ 2 ∣ T.index := by
    intro h2
    apply hQ.2.2
    have h1 := Subgroup.index_dvd_of_le hQT
    exact h2.trans h1
  let F : ↥N → Subgroup G := fun h => W.map (MulAut.conj (h : G)).toMonoidHom
  have hFmem : ∀ (h : ↥N) (z : G), z ∈ F h ↔ (h : G)⁻¹ * z * (h : G) ∈ W := by
    intro h z
    exact Subgroup.mem_map_equiv (f := MulAut.conj (h : G)) (K := W)
  have hF : ∀ h h' : ↥N, F h = F h' ↔ h⁻¹ * h' ∈ T := by
    intro h h'
    rw [hT, Subgroup.mem_subgroupOf, Subgroup.mem_normalizer_iff]
    constructor
    · intro hh u
      have h1 := hFmem h ((h' : G) * u * (h' : G)⁻¹)
      have h2 := hFmem h' ((h' : G) * u * (h' : G)⁻¹)
      rw [hh] at h1
      have e1 : (h' : G)⁻¹ * ((h' : G) * u * (h' : G)⁻¹) * (h' : G) = u := by group
      have e2 : (h : G)⁻¹ * ((h' : G) * u * (h' : G)⁻¹) * (h : G) =
          ((h⁻¹ * h' : ↥N) : G) * u * ((h⁻¹ * h' : ↥N) : G)⁻¹ := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        group
      rw [e1] at h2
      rw [e2] at h1
      exact h2.symm.trans h1
    · intro hh
      ext z
      rw [hFmem, hFmem]
      have h3 := hh ((h' : G)⁻¹ * z * (h' : G))
      have e3 : ((h⁻¹ * h' : ↥N) : G) * ((h' : G)⁻¹ * z * (h' : G)) * ((h⁻¹ * h' : ↥N) : G)⁻¹ =
          (h : G)⁻¹ * z * (h : G) := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        group
      rw [e3] at h3
      exact h3.symm
  have hcard : T.index ≤ 2 := by
    let f : (↥N ⧸ T) → Subgroup G := Quotient.lift F (fun a b hab =>
      (hF a b).2 (QuotientGroup.leftRel_apply.1 hab))
    have hf : Function.Injective f := by
      intro a b hab
      induction a using QuotientGroup.induction_on with
      | H a =>
        induction b using QuotientGroup.induction_on with
        | H b =>
          exact QuotientGroup.eq.2 ((hF a b).1 hab)
    have hrange : Set.range f ⊆ {W₁, W₂} := by
      rintro _ ⟨q, rfl⟩
      induction q using QuotientGroup.induction_on with
      | H a => exact hW a a.2
    rw [Subgroup.index_eq_card, ← Nat.card_range_of_injective hf]
    calc Nat.card (Set.range f) ≤ Nat.card ({W₁, W₂} : Set (Subgroup G)) :=
          Nat.card_mono (Set.toFinite _) hrange
      _ ≤ 2 := by
          rw [Nat.card_coe_set_eq]
          exact (Set.ncard_insert_le _ _).trans (by simp)
  have h1 : T.index = 1 := by
    have : 0 < T.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
    omega
  have hTtop : T = ⊤ := Subgroup.index_eq_one.1 h1
  intro g hg
  have : (⟨g, hg⟩ : ↥N) ∈ T := by rw [hTtop]; exact Subgroup.mem_top _
  exact this

end OddIndex

end CFSG.Quasithin.RonanE611
