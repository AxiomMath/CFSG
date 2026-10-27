module

public import CFSG.Walter.W67.W2Lemma26A

public section

namespace CFSG.Walter.W67

open scoped MatrixGroups Pointwise

variable {G : Type} [Group G] [Finite G]

theorem commutator_eq_top_of_surjective {X Y : Type*} [Group X] [Group Y] (f : X →* Y)
    (hf : Function.Surjective f) (hX : commutator X = ⊤) : commutator Y = ⊤ := by
  have h1 : (commutator X).map f = commutator Y := by
    rw [commutator_def, commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective f hf]
  rw [hX, Subgroup.map_top_of_surjective f hf] at h1
  exact h1.symm

theorem eq_top_of_odd_index_of_perfect {X : Type} [Group X] [Finite X]
    (hperf : commutator X = ⊤) {L : Subgroup X} [L.Normal] (hodd : Odd L.index) : L = ⊤ := by
  by_contra hne
  have hsolv : Group.IsSolvable (X ⧸ L) :=
    CFSG.FeitThompson.isSolvable_of_odd_natCard _ (by rw [← Subgroup.index_eq_card]; exact hodd)
  have hperf' : commutator (X ⧸ L) = ⊤ :=
    commutator_eq_top_of_surjective (QuotientGroup.mk' L) (QuotientGroup.mk'_surjective L) hperf
  have : Nontrivial (X ⧸ L) := by
    rw [← Finite.one_lt_card_iff_nontrivial, ← Subgroup.index_eq_card]
    have h1 : L.index ≠ 1 := fun h1 => hne (Subgroup.index_eq_one.mp h1)
    have h0 : L.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    omega
  have := Group.IsSolvable.commutator_lt_top_of_nontrivial (X ⧸ L)
  rw [hperf'] at this
  exact lt_irrefl _ this

theorem MinCE.false_of_centralizer_eq_top (m : MinCE G) (fr : Frame m.toHyp) (hq : 3 < m.q)
    (hperf : commutator G = ⊤) (hJ : JFacts) (hM : RMult) {X : Subgroup G} (hXE : X ≤ fr.E)
    (hX : X ≠ ⊥) (htop : Subgroup.centralizer (X : Set G) = ⊤) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hXZ : X ≤ Subgroup.center G := fun x hx => Subgroup.mem_center_iff.mpr fun g => by
    have hg : g ∈ Subgroup.centralizer (X : Set G) := htop ▸ Subgroup.mem_top g
    exact (Subgroup.mem_centralizer_iff.mp hg x hx).symm
  have : X.Normal := Subgroup.normal_of_le_center hXZ
  have hXodd : Odd (Nat.card X) := Odd.of_dvd_nat fr.odd_card_E (Subgroup.card_dvd_of_le hXE)
  let hQ : Hyp (G ⧸ X) := m.quotient X hXodd
  have hlt : Nat.card (G ⧸ X) < Nat.card G := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup X
    have h2 : 1 < Nat.card X := (Subgroup.one_lt_card_iff_ne_bot X).mpr hX
    have hpos : 0 < Nat.card (G ⧸ X) := Nat.card_pos
    nlinarith
  have hperfQ : commutator (G ⧸ X) = ⊤ :=
    commutator_eq_top_of_surjective (QuotientGroup.mk' X) (QuotientGroup.mk'_surjective X) hperf
  rcases m.ih (G ⧸ X) hQ hlt with hc | hc
  · obtain ⟨N, hN, h2⟩ := hQ.exists_normal_index_two_of_case1 hc
    exact index_ne_two_of_perfect hperfQ N hN h2
  obtain ⟨L, hLn, hLodd, -, ⟨K', hK'L, hJK', hCL, ⟨eK'⟩⟩, -⟩ := hc
  have hLtop : L = ⊤ := eq_top_of_odd_index_of_perfect hperfQ hLodd
  subst hLtop
  set S' := Sylow.mapSurjective (p := 2) (QuotientGroup.mk'_surjective X) fr.S
  have hS'el : IsElementaryAbelian 2 (S' : Subgroup (G ⧸ X)) := by
    have hab : IsMulCommutative (S' : Subgroup (G ⧸ X)) := hQ.abelian_sylow S'
    refine { toIsMulCommutative := hab, exponent_dvd_p := ?_ }
    refine Monoid.exponent_dvd_of_forall_pow_eq_one fun y => ?_
    have hy : (y : G ⧸ X) ∈ (fr.S : Subgroup G).map (QuotientGroup.mk' X) := by
      rw [← Sylow.coe_mapSurjective (QuotientGroup.mk'_surjective X) fr.S]
      exact y.2
    obtain ⟨s, hs, hsy⟩ := hy
    apply Subtype.ext
    rw [Subgroup.coe_pow, ← hsy, ← map_pow, pow_two, fr.mul_self_of_mem_S hs, map_one]
    rfl
  have hJR : IsJRSubgroup (⊤ : Subgroup (G ⧸ X)) hQ.J K' hQ.p hQ.f :=
    ⟨Subgroup.mem_top _, hQ.orderOf_J, hK'L, hJK', hCL, ⟨eK'⟩, fun N _ hn h2 =>
      index_ne_two_of_perfect hperfQ N
        ⟨fun n hn' g => hn.conj_mem ⟨n, Subgroup.mem_top n⟩ hn' ⟨g, Subgroup.mem_top g⟩⟩
        (by rw [← Subgroup.relIndex_top_right]; exact h2),
      ⟨S', le_top, hS'el, hQ.card_sylow S'⟩⟩
  obtain ⟨hL', hp, hf, -, -⟩ := IsJRSubgroup.nonempty_jrGroup (G ⧸ X) hQ.p_ne_two hQ.f_pos hJR
  have hqL : hL'.q = m.q := by rw [JRGroup.q, hp, hf]; rfl
  have hmult : OddMultiplierTrivial (⊤ : Subgroup (G ⧸ X)) := by
    by_cases h5 : hL'.q = 5
    · obtain ⟨-, -, -, ⟨-, hm⟩, -⟩ := hJ _ hL' h5
      exact hm
    · exact hM _ hL' h5 (hqL ▸ hq)
  exact hX (hmult G X hXZ hXodd hperf ⟨Subgroup.topEquiv.symm⟩)

end CFSG.Walter.W67
