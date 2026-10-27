module

public import CFSG.Quasithin.EmptyFaithful.ModDStab
public import CFSG.Quasithin.EmptyFaithful.ModDOrbit

public section

namespace CFSG.Quasithin.ModD

open CFSG.CosetTable CFSG.Quasithin


variable {M : Type} [Group M] [Finite M]

omit [Finite M] in
theorem ncard_ne_one : ({m : M | m ≠ 1} : Set M).ncard = Nat.card M - 1 := by
  have h1 : ({m : M | m ≠ 1}) = (Set.univ \ {1} : Set M) := by
    ext m
    simp
  rw [h1, Set.ncard_sdiff_singleton_of_mem (Set.mem_univ _), Set.ncard_univ]

@[expose] def fixSub (f : MulAut M) : Subgroup M where
  carrier := {m | f m = m}
  mul_mem' := by
    intro a b ha hb
    have ha' : f a = a := ha
    have hb' : f b = b := hb
    show f (a * b) = a * b
    rw [map_mul, ha', hb']
  one_mem' := by
    show f 1 = 1
    exact map_one f
  inv_mem' := by
    intro a ha
    have ha' : f a = a := ha
    show f a⁻¹ = a⁻¹
    rw [map_inv, ha']

theorem not_stab_B (hcard : Nat.card M = 2 ^ 6) (φ : U33G →* MulAut M) {z : M} (hz : z ≠ 1)
    (hB : stabSub φ z = u33Data.B) : False := by
  classical
  have hst : ∀ g, φ g z = z ↔ lHom g 0 = 0 := by
    intro g
    have h : g ∈ stabSub φ z ↔ g ∈ stabπ lHom := by rw [hB, stab_lHom]
    exact h.trans mem_stabπ
  obtain ⟨ε, hε1, hε2, hε3⟩ := exists_label φ z lHom 0 hst
  have hsurj : ∀ j, ∃ g, ε (φ g z) = j := fun j => by
    obtain ⟨g, hg⟩ := lHom_trans j
    exact ⟨g, by rw [hε1]; exact hg⟩
  have horb : ∀ m, m ≠ 1 → ∃ g, φ g z = m :=
    orbit_eq_ne_one φ hz (by rw [hcard]; simp) ε hε2 hsurj
  have hy : lHom (u33GenPG 4) = lImg 4 := lHom_gen 4
  let y : U33G := u33GenPG 4
  let S : Set M := {m | m ≠ 1 ∧ φ y m = m}
  let F9 : Set (Fin 63) := {j | lImg 4 j = j}
  have hmaps : ε '' S = F9 := by
    ext j
    constructor
    · rintro ⟨m, ⟨hm1, hm⟩, rfl⟩
      have h1 := hε3 y m (horb m hm1)
      rw [hm, hy] at h1
      exact h1.symm
    · intro hj
      obtain ⟨g, hg⟩ := hsurj j
      have hm1 : φ g z ≠ 1 := fun h => hz ((φ g).injective (by rw [h, map_one]))
      refine ⟨φ g z, ⟨hm1, ?_⟩, hg⟩
      have h1 := hε3 y (φ g z) ⟨g, rfl⟩
      rw [hg, hy] at h1
      have h2 : ε (φ y (φ g z)) = ε (φ g z) := by rw [h1, hg]; exact hj
      refine hε2 _ _ ⟨y * g, ?_⟩ ⟨g, rfl⟩ h2
      rw [map_mul]
      rfl
  have hinj : Set.InjOn ε S := fun m hm n hn h => hε2 m n (horb m hm.1) (horb n hn.1) h
  have hSc : S.ncard = 9 := by
    rw [← hinj.ncard_image, hmaps]
    have : F9 = ↑(Finset.univ.filter fun i : Fin 63 => lImg 4 i = i) := by
      ext i
      simp [F9]
    rw [this, Set.ncard_coe_finset]
    exact lImg_four_fix
  let Fy : Subgroup M := fixSub (φ y)
  have hFy : (Fy : Set M) = insert 1 S := by
    ext m
    simp only [Fy, fixSub, Subgroup.coe_set_mk, SetLike.mem_coe, Set.mem_ofPred_eq, Set.mem_insert_iff, S]
    constructor
    · intro h
      by_cases hm : m = 1
      · exact Or.inl hm
      · exact Or.inr ⟨hm, h⟩
    · rintro (rfl | ⟨_, h⟩)
      · exact map_one _
      · exact h
  have h1S : (1 : M) ∉ S := fun h => h.1 rfl
  have hc : Nat.card Fy = 10 := by
    have h1 : Nat.card Fy = (Fy : Set M).ncard := Nat.card_coe_set_eq (Fy : Set M)
    rw [h1, hFy, Set.ncard_insert_of_notMem h1S, hSc]
  have hdvd := Subgroup.card_subgroup_dvd_card Fy
  rw [hc, hcard] at hdvd
  omega

theorem stab_eq_A (hcard : Nat.card M = 2 ^ 6) (φ : U33G →* MulAut M)
    (hirr : ∀ N : Subgroup M, (∀ g : U33G, ∀ n ∈ N, φ g n ∈ N) → N = ⊥ ∨ N = ⊤)
    {z : M} (hz : z ≠ 1) (hz2 : z ^ 2 = 1) (hzT : ∀ g ∈ u33Data.T, φ g z = z) :
    stabSub φ z = u33Data.A := by
  classical
  have hTS : u33Data.T ≤ stabSub φ z := fun g hg => hzT g hg
  have hne : ∀ g : U33G, φ g z ≠ 1 := fun g h => hz ((φ g).injective (by rw [h, map_one]))
  have hidx : (stabSub φ z).index ≤ 63 := by
    let f : U33G ⧸ stabSub φ z → {m : M | m ≠ 1} :=
      Quotient.lift (fun g => (⟨φ g z, hne g⟩ : {m : M | m ≠ 1})) (by
        intro g g' hg
        apply Subtype.ext
        have h1 : g⁻¹ * g' ∈ stabSub φ z := QuotientGroup.leftRel_apply.1 hg
        have h2 := congrArg (φ g) (mem_stabSub.1 h1)
        rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel_left] at h2
        exact h2.symm)
    have hinj : Function.Injective f := by
      intro q q'
      induction q using Quotient.inductionOn with
      | _ g =>
        induction q' using Quotient.inductionOn with
        | _ g' =>
          intro h
          have h' : φ g z = φ g' z := congrArg Subtype.val h
          exact Quotient.sound (QuotientGroup.leftRel_apply.2 (mem_stabSub.2 (apply_inv_mul_eq h')))
    have h1 := Nat.card_le_card_of_injective f hinj
    rw [Nat.card_coe_set_eq, ncard_ne_one, hcard] at h1
    show Nat.card (U33G ⧸ stabSub φ z) ≤ 63
    omega
  have hSzTop : stabSub φ z ≠ ⊤ := by
    intro htop
    have hinv : ∀ g : U33G, ∀ n ∈ Subgroup.zpowers z, φ g n ∈ Subgroup.zpowers z := by
      intro g n hn
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hn
      have hg : φ g z = z := mem_stabSub.1 (htop ▸ Subgroup.mem_top g)
      rw [map_zpow, hg]
      exact ⟨k, rfl⟩
    rcases hirr _ hinv with h | h
    · exact hz (Subgroup.zpowers_eq_bot.1 h)
    · have hc : Nat.card (Subgroup.zpowers z) = orderOf z := Nat.card_zpowers z
      have hle : orderOf z ≤ 2 := orderOf_le_of_pow_eq_one (by norm_num) hz2
      have h3 : Nat.card (Subgroup.zpowers z) = Nat.card M := by
        rw [h]
        exact Subgroup.card_top
      rw [hcard] at h3
      omega
  have hSzT : stabSub φ z ≠ u33Data.T := by
    intro h
    have h1 := Subgroup.card_mul_index u33Data.T
    rw [u33_card_T, card_u33Pres] at h1
    rw [h] at hidx
    omega
  rcases u33Data.lattice _ hTS with h | h | h | h
  · exact absurd h hSzT
  · exact h
  · exact absurd (not_stab_B hcard φ hz h) id
  · exact absurd h hSzTop

omit [Finite M] in
theorem gen_mem_A : ∀ i : Fin 5, i ≠ 4 → u33GenPG i.val ∈ u33Data.A := by
  intro i hi
  fin_cases i
  · exact u33Data.T_le_A u33Data.a_mem_T
  · exact u33Data.T_le_A u33Data.b_mem_T
  · exact u33Data.T_le_A u33Data.s_mem_T
  · exact u33Data.x_mem_A
  · exact absurd rfl hi

omit [Finite M] in
theorem gen_mem_B : ∀ i : Fin 5, i ≠ 3 → u33GenPG i.val ∈ u33Data.B := by
  intro i hi
  fin_cases i
  · exact u33Data.T_le_B u33Data.a_mem_T
  · exact u33Data.T_le_B u33Data.b_mem_T
  · exact u33Data.T_le_B u33Data.s_mem_T
  · exact absurd rfl hi
  · exact u33Data.y_mem_B

end CFSG.Quasithin.ModD
