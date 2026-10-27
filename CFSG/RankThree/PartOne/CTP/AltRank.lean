module

public import CFSG.RankThree.PartOne.CTP.AltGen
public import Mathlib.GroupTheory.PGroup
public import Mathlib.Tactic.NormNum.Prime

public section

namespace CFSG.RankThree.PartOne.CTP.Alt

open Equiv Equiv.Perm

theorem prime_sq_dvd_factorial {p n : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hn : n ≤ 12)
    (h : p ^ 2 ∣ n.factorial) : p = 5 ∧ 10 ≤ n := by
  have hpn : p ≤ n := (hp.dvd_factorial).mp (dvd_trans (dvd_pow_self p two_ne_zero) h)
  have hp12 : p ≤ 12 := hpn.trans hn
  interval_cases p <;> first | (exfalso; revert hp; norm_num; done) | skip
  all_goals interval_cases n <;> simp_all [Nat.factorial]

theorem five_dvd_card_support {V : Type*} [Fintype V] [DecidableEq V] {x : Perm V}
    (hx : x ^ 5 = 1) : 5 ∣ x.support.card := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have h := Equiv.Perm.card_compl_support_modEq (p := 5) (n := 1) (σ := x) (by simpa using hx)
  rw [Nat.modEq_iff_dvd' (Finset.card_le_univ _), ← Finset.card_compl, compl_compl] at h
  exact h

theorem orbit_stabilizer_of_moved {V : Type*} [Finite V] {E : Subgroup (Perm V)}
    (hE : Nat.card E = 25) (hV : Nat.card V ≤ 14) {v : V} (hv : ∃ g ∈ E, g v ≠ v) :
    (MulAction.orbit E v).ncard = 5 ∧ Nat.card (MulAction.stabilizer E v) = 5 := by
  have h1 := MulAction.index_stabilizer E v
  have h2 : (MulAction.stabilizer E v).index * Nat.card (MulAction.stabilizer E v) = 25 := by
    rw [← hE]
    exact Subgroup.index_mul_card _
  have h3 : (MulAction.stabilizer E v).index ≤ 14 := by
    rw [h1]
    exact (Set.ncard_le_card _).trans hV
  have hk1 : (MulAction.stabilizer E v).index ≠ 1 := by
    intro h
    have htop : MulAction.stabilizer E v = ⊤ := Subgroup.index_eq_one.mp h
    obtain ⟨g, hg, hgv⟩ := hv
    have hmem : (⟨g, hg⟩ : E) ∈ MulAction.stabilizer E v := by
      rw [htop]
      exact Subgroup.mem_top _
    exact hgv (MulAction.mem_stabilizer_iff.mp hmem)
  rw [← h1]
  generalize (MulAction.stabilizer E v).index = k at *
  generalize Nat.card (MulAction.stabilizer E v) = m at *
  interval_cases k <;> omega

theorem exists_stabilizer_element {V : Type*} [Fintype V] [DecidableEq V] {E : Subgroup (Perm V)}
    (hE : Nat.card E = 25) (hpow : ∀ x ∈ E, x ^ 5 = 1) (hV : Fintype.card V ≤ 14) {v : V}
    (hv : ∃ g ∈ E, g v ≠ v) :
    ∃ b ∈ E, b ≠ 1 ∧ b.support.card = 5 ∧ ∀ g ∈ E, b (g v) = g v := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hcomm : IsMulCommutative E := IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 5)
    (by rw [hE]; norm_num)
  have hV' : Nat.card V ≤ 14 := by simpa using hV
  obtain ⟨h5, h5'⟩ := orbit_stabilizer_of_moved hE hV' hv
  have hnt : Nontrivial (MulAction.stabilizer E v) := by
    rw [← Finite.one_lt_card_iff_nontrivial]
    omega
  obtain ⟨b, hb1⟩ := exists_ne (1 : MulAction.stabilizer E v)
  have hbE : ((b : E) : Perm V) ∈ E := (b : E).2
  have hbv : ((b : E) : Perm V) v = v := MulAction.mem_stabilizer_iff.mp b.2
  have hb1' : ((b : E) : Perm V) ≠ 1 := by
    intro h
    apply hb1
    apply Subtype.ext
    apply Subtype.ext
    simpa using h
  have hfix : ∀ g ∈ E, ((b : E) : Perm V) (g v) = g v := by
    intro g hg
    have h1 := (IsMulCommutative.is_comm (M := E)).comm (b : E) ⟨g, hg⟩
    have h2 := congrArg (fun t : E => (t : Perm V) v) h1
    simp only [Subgroup.coe_mul, Perm.coe_mul, Function.comp_apply] at h2
    rw [h2, hbv]
  refine ⟨(b : E), hbE, hb1', ?_, hfix⟩
  have hsub : (((b : E) : Perm V).support : Set V) ⊆ (MulAction.orbit E v)ᶜ := by
    intro u hu hu'
    obtain ⟨g, rfl⟩ := hu'
    exact (Equiv.Perm.mem_support.mp hu) (hfix g g.2)
  have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [Set.ncard_coe_finset, Set.ncard_compl, h5] at hle
  have hpos : 0 < ((b : E) : Perm V).support.card := by
    rw [Finset.card_pos, Finset.nonempty_iff_ne_empty]
    intro h
    exact hb1' (Equiv.Perm.support_eq_empty_iff.mp h)
  have hdvd := five_dvd_card_support (hpow _ hbE)
  omega

theorem orbit_eq_support {V : Type*} [Fintype V] [DecidableEq V] {E : Subgroup (Perm V)}
    (hE : Nat.card E = 25) (hV : Fintype.card V ≤ 14) {b : Perm V} (hb : b ∈ E)
    (hb5 : b.support.card = 5) {w : V} (hw : w ∈ b.support) :
    (MulAction.orbit E w : Set V) = ↑b.support := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hcomm : IsMulCommutative E := IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 5)
    (by rw [hE]; norm_num)
  have hmoved : ∃ g ∈ E, g w ≠ w := ⟨b, hb, Equiv.Perm.mem_support.mp hw⟩
  obtain ⟨h5, -⟩ := orbit_stabilizer_of_moved hE (by simpa using hV) hmoved
  have hsub : MulAction.orbit E w ⊆ ↑b.support := by
    rintro u ⟨g, rfl⟩
    simp only [Finset.mem_coe, Equiv.Perm.mem_support]
    have h1 := (IsMulCommutative.is_comm (M := E)).comm ⟨b, hb⟩ g
    have h2 := congrArg (fun t : E => (t : Perm V) w) h1
    simp only [Subgroup.coe_mul, Perm.coe_mul, Function.comp_apply] at h2
    show b ((g : Perm V) w) ≠ (g : Perm V) w
    rw [h2]
    intro h
    exact (Equiv.Perm.mem_support.mp hw) ((g : Perm V).injective h)
  exact Set.eq_of_subset_of_ncard_le hsub (by rw [h5, Set.ncard_coe_finset, hb5]) (Set.toFinite _)

theorem exists_disjoint_supports {V : Type*} [Fintype V] [DecidableEq V] {E : Subgroup (Perm V)}
    (hE : Nat.card E = 25) (hpow : ∀ x ∈ E, x ^ 5 = 1) (hV : Fintype.card V ≤ 14) :
    ∃ a ∈ E, ∃ b ∈ E, a ≠ 1 ∧ b ≠ 1 ∧ a.support.card = 5 ∧ b.support.card = 5 ∧
      Disjoint a.support b.support := by
  obtain ⟨x, hxE, hx1⟩ : ∃ x ∈ E, x ≠ 1 := by
    by_contra h
    have hbot : E = ⊥ := (Subgroup.eq_bot_iff_forall E).mpr fun y hy => by
      by_contra hy1
      exact h ⟨y, hy, hy1⟩
    rw [hbot] at hE
    simp at hE
  obtain ⟨v, hv⟩ : ∃ v, x v ≠ v := by
    by_contra h
    exact hx1 (Equiv.ext fun u => by_contra fun hu => h ⟨u, hu⟩)
  obtain ⟨b, hbE, hb1, hb5, -⟩ := exists_stabilizer_element hE hpow hV ⟨x, hxE, hv⟩
  obtain ⟨w, hw⟩ : b.support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h
    exact hb1 (Equiv.Perm.support_eq_empty_iff.mp h)
  obtain ⟨a, haE, ha1, ha5, hafix⟩ :=
    exists_stabilizer_element hE hpow hV ⟨b, hbE, Equiv.Perm.mem_support.mp hw⟩
  refine ⟨a, haE, b, hbE, ha1, hb1, ha5, hb5, ?_⟩
  rw [Finset.disjoint_left]
  intro u hua hub
  have hu : u ∈ MulAction.orbit E w := by
    rw [orbit_eq_support hE hV hbE hb5 hw]
    exact hub
  obtain ⟨g, rfl⟩ := hu
  exact (Equiv.Perm.mem_support.mp hua) (hafix g g.2)

theorem alternatingGroup_le_closure_centralizers {V : Type*} [Fintype V] [DecidableEq V]
    (hV₁ : 11 ≤ Fintype.card V) (hV₂ : Fintype.card V ≤ 14) {E : Subgroup (Perm V)}
    (hE : Nat.card E = 25) (hpow : ∀ x ∈ E, x ^ 5 = 1) :
    alternatingGroup V ≤ Subgroup.closure
      {k : Perm V | k ∈ alternatingGroup V ∧ ∃ x ∈ E, x ≠ 1 ∧ k * x = x * k} := by
  obtain ⟨a, haE, b, hbE, ha1, hb1, ha5, hb5, hab⟩ := exists_disjoint_supports hE hpow hV₂
  refine alternatingGroup_le_of_two_supports hab (by omega) (by omega) ?_ ?_ ?_
  · obtain ⟨r, -, hr⟩ := Finset.exists_mem_notMem_of_card_lt_card
      (s := a.support ∪ b.support) (t := Finset.univ)
      (by rw [Finset.card_union_of_disjoint hab, ha5, hb5, Finset.card_univ]; omega)
    simp only [Finset.mem_union, not_or] at hr
    exact ⟨r, hr.1, hr.2⟩
  · intro k hk hka
    exact Subgroup.subset_closure ⟨hk, a, haE, ha1, hka⟩
  · intro k hk hkb
    exact Subgroup.subset_closure ⟨hk, b, hbE, hb1, hkb⟩

theorem closure_centralizers_eq_top {G V : Type*} [Group G] [Fintype V] [DecidableEq V]
    (hV₁ : 11 ≤ Fintype.card V) (hV₂ : Fintype.card V ≤ 14)
    (φ : G →* Perm V) (hφ : Function.Injective φ) (hrange : φ.range = alternatingGroup V)
    {E : Subgroup G} (hE : Nat.card E = 25) (hpow : ∀ x ∈ E, x ^ 5 = 1) :
    Subgroup.closure {k : G | ∃ x ∈ E, x ≠ 1 ∧ k * x = x * k} = ⊤ := by
  have hcard : Nat.card (E.map φ) = 25 := by
    rw [Subgroup.card_map_of_injective hφ]
    exact hE
  have hpow' : ∀ y ∈ E.map φ, y ^ 5 = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, hpow x hx, map_one]
  have hmain := alternatingGroup_le_closure_centralizers hV₁ hV₂ hcard hpow'
  have h2 : Subgroup.closure {k : Perm V | k ∈ alternatingGroup V ∧
      ∃ x ∈ E.map φ, x ≠ 1 ∧ k * x = x * k} ≤
      (Subgroup.closure {k : G | ∃ x ∈ E, x ≠ 1 ∧ k * x = x * k}).map φ := by
    rw [MonoidHom.map_closure]
    refine Subgroup.closure_mono ?_
    rintro k ⟨hk, x', ⟨x, hx, rfl⟩, hx1, hkx⟩
    rw [← hrange] at hk
    obtain ⟨g, rfl⟩ := hk
    refine ⟨g, ⟨x, hx, ?_, ?_⟩, rfl⟩
    · intro h
      exact hx1 (by rw [h, map_one])
    · apply hφ
      simpa using hkx
  rw [eq_top_iff]
  intro g _
  have hg : φ g ∈ alternatingGroup V := by
    rw [← hrange]
    exact ⟨g, rfl⟩
  obtain ⟨t, ht, hφt⟩ := h2 (hmain hg)
  rwa [← hφ hφt]

theorem closure_centralizers_alternatingGroup {n : ℕ} (hn₁ : 11 ≤ n) (hn₂ : n ≤ 14)
    {E : Subgroup (alternatingGroup (Fin n))} (hE : Nat.card E = 25) (hpow : ∀ x ∈ E, x ^ 5 = 1) :
    Subgroup.closure {k : alternatingGroup (Fin n) | ∃ x ∈ E, x ≠ 1 ∧ k * x = x * k} = ⊤ :=
  closure_centralizers_eq_top (V := Fin n) (by simpa using hn₁) (by simpa using hn₂)
    (alternatingGroup (Fin n)).subtype Subtype.val_injective (by simp) hE hpow

end CFSG.RankThree.PartOne.CTP.Alt
