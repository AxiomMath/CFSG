module

public import CFSG.Quasithin.Vol2.Ch5Sec1Borel
public import CFSG.Quasithin.Vol2.Ch5LieQuot

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped Pointwise

@[expose] def E22MSolvableFact : Prop :=
  ∀ (Γ : Type) [Group Γ] [Finite Γ] (H T M₀ : Subgroup Γ), MinParabolic H T M₀ →
    SQTKGroup ↥H → ¬ Group.IsSolvable ↥H → (∃ K ∈ cComp H, E2.HasE22LieQuot K) →
      Group.IsSolvable ↥M₀

section General

variable {G : Type} [Group G] [Finite G]

theorem exists_complement_of_coprime {P Y : Subgroup G} (hPY : P ≤ Y)
    (hYN : Y ≤ Subgroup.normalizer (P : Set G))
    (hcop : Nat.Coprime (Nat.card P) (P.relIndex Y)) :
    ∃ E : Subgroup G, E ≤ Y ∧ P ⊓ E = ⊥ ∧ P ⊔ E = Y ∧ Nat.card E = P.relIndex Y ∧
      E.relIndex Y = Nat.card P := by
  have hN : (P.subgroupOf Y).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hPY).mpr hYN
  have hc : Nat.card (P.subgroupOf Y) = Nat.card P :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPY).toEquiv
  obtain ⟨C, hC⟩ := Subgroup.exists_right_complement'_of_coprime (N := P.subgroupOf Y)
    (by rw [hc]; exact hcop)
  have hCE : (C.map Y.subtype).subgroupOf Y = C :=
    Subgroup.comap_map_eq_self_of_injective Y.subtype_injective C
  have hcC : Nat.card (C.map Y.subtype) = Nat.card C :=
    Subgroup.card_map_of_injective Y.subtype_injective
  refine ⟨C.map Y.subtype, Subgroup.map_subtype_le C, ?_, ?_, ?_, ?_⟩
  · rw [eq_bot_iff]
    intro g hg
    rw [Subgroup.mem_inf] at hg
    obtain ⟨hgP, hgE⟩ := hg
    obtain ⟨c, hcC', rfl⟩ := Subgroup.mem_map.mp hgE
    have h1 : c ∈ P.subgroupOf Y ⊓ C := ⟨Subgroup.mem_subgroupOf.mpr hgP, hcC'⟩
    rw [hC.disjoint.eq_bot, Subgroup.mem_bot] at h1
    rw [h1, map_one]
    exact Subgroup.one_mem _
  · have h1 : (P.subgroupOf Y ⊔ C).map Y.subtype = Y := by
      rw [hC.sup_eq_top, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    rwa [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hPY] at h1
  · rw [hcC]
    have h1 := hC.card_mul_card
    have h2 := Subgroup.card_mul_index (P.subgroupOf Y)
    have hpos : 0 < Nat.card (P.subgroupOf Y) := Nat.card_pos
    rw [← h2] at h1
    exact Nat.eq_of_mul_eq_mul_left hpos h1
  · rw [Subgroup.relIndex, hCE, hC.index_eq_card, hc]

theorem exists_mem_conj_of_complements {P Y E₁ E₂ : Subgroup G} (hPY : P ≤ Y)
    (hYN : Y ≤ Subgroup.normalizer (P : Set G)) (hP2 : IsPGroup 2 P) (hodd : Odd (P.relIndex Y))
    (hE₁ : E₁ ≤ Y) (hE₁P : P ⊓ E₁ = ⊥) (hE₁s : P ⊔ E₁ = Y)
    (hE₂ : E₂ ≤ Y) (hE₂P : P ⊓ E₂ = ⊥) (hE₂s : P ⊔ E₂ = Y) :
    ∃ x ∈ P, E₂ = E₁.map (MulAut.conj x).toMonoidHom := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hN : (P.subgroupOf Y).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hPY).mpr hYN
  have hN2 : IsPGroup 2 (P.subgroupOf Y) := hP2.of_equiv (Subgroup.subgroupOfEquivOfLe hPY).symm
  have hNsolv : Group.IsSolvable (P.subgroupOf Y) := by
    have := hN2.isNilpotent
    infer_instance
  have hcop : Nat.Coprime (Nat.card (P.subgroupOf Y)) (P.subgroupOf Y).index := by
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp hN2
    rw [hk]
    exact Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hodd)
  have hprod : ∀ E : Subgroup G, E ≤ Y → P ⊔ E = Y →
      ((P.subgroupOf Y : Subgroup ↥Y) : Set ↥Y) * (E.subgroupOf Y : Set ↥Y) = Set.univ := by
    intro E hE hs
    have htop : P.subgroupOf Y ⊔ E.subgroupOf Y = ⊤ := by
      rw [← Subgroup.subgroupOf_sup hPY hE, hs, Subgroup.subgroupOf_self]
    rw [← Subgroup.normal_mul, htop]
    rfl
  have hinf : ∀ E : Subgroup G, P ⊓ E = ⊥ → P.subgroupOf Y ⊓ E.subgroupOf Y = ⊥ := by
    intro E h
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_inf, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf] at hx
    have hx' : (x : G) ∈ P ⊓ E := ⟨hx.1, hx.2⟩
    rw [h, Subgroup.mem_bot] at hx'
    exact (Subgroup.mem_bot).mpr (Subtype.ext hx')
  obtain ⟨m, hm, hK⟩ := CFSG.SolvableHall.solvable_normal_hall_complement_conjugacy
    (P.subgroupOf Y) hNsolv hcop (hprod E₁ hE₁ hE₁s) (hprod E₂ hE₂ hE₂s) (hinf E₁ hE₁P)
    (hinf E₂ hE₂P)
  refine ⟨((m⁻¹ : ↥Y) : G), Subgroup.mem_subgroupOf.mp ((P.subgroupOf Y).inv_mem hm), ?_⟩
  have hcomp : Y.subtype.comp (MulAut.conj m⁻¹).toMonoidHom =
      (MulAut.conj ((m⁻¹ : ↥Y) : G)).toMonoidHom.comp Y.subtype := by
    ext y
    simp
  rw [← Subgroup.map_subgroupOf_eq_of_le hE₂, hK, Subgroup.map_map, hcomp, ← Subgroup.map_map,
    Subgroup.map_subgroupOf_eq_of_le hE₁]

omit [Finite G] in
theorem inf_sup_le_sup_inf {P W E : Subgroup G} (hPW : P ≤ W)
    (hEN : E ≤ Subgroup.normalizer (P : Set G)) : W ⊓ (P ⊔ E) ≤ P ⊔ (W ⊓ E) := by
  intro x hx
  obtain ⟨hxW, hxPE⟩ := hx
  have hx' : x ∈ ((P : Set G) * (E : Set G)) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left P E hEN]
    exact hxPE
  obtain ⟨p, hp, e, he, rfl⟩ := hx'
  have heW : e ∈ W := by
    have := W.mul_mem (W.inv_mem (hPW hp)) hxW
    simpa using this
  exact Subgroup.mul_mem_sup hp ⟨heW, he⟩

theorem inf_eq_bot_of_odd_of_isPGroup {P U : Subgroup G} (hP : IsPGroup 2 P)
    (hU : Odd (Nat.card U)) : P ⊓ U = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine (Subgroup.disjoint_of_coprime_natCard ?_).eq_bot
  obtain ⟨m, hm⟩ := (IsPGroup.iff_card).mp hP
  rw [hm]
  exact Nat.Coprime.pow_left m (Nat.coprime_two_left.mpr hU)

theorem isHallTwoPrimeOf_map_conj {U X : Subgroup G} (hU : Lin2.IsHallTwoPrimeOf U X) {y : G}
    (hy : y ∈ X) : Lin2.IsHallTwoPrimeOf (U.map (MulAut.conj y).toMonoidHom) X := by
  obtain ⟨hUX, hodd, k, hk⟩ := hU
  have hinj : Function.Injective (MulAut.conj y).toMonoidHom := (MulAut.conj y).injective
  have hc : Nat.card (U.map (MulAut.conj y).toMonoidHom) = Nat.card U :=
    Subgroup.card_map_of_injective hinj
  have hle : U.map (MulAut.conj y).toMonoidHom ≤ X := by
    rintro _ ⟨u, hu, rfl⟩
    exact X.mul_mem (X.mul_mem hy (hUX hu)) (X.inv_mem hy)
  refine ⟨hle, hc ▸ hodd, k, ?_⟩
  have h1 := Subgroup.relIndex_mul_card (U.map (MulAut.conj y).toMonoidHom) X
  have h2 := Subgroup.relIndex_mul_card U X
  rw [inf_eq_left.mpr hle, hc] at h1
  rw [inf_eq_left.mpr hUX, hk] at h2
  have hpos : 0 < Nat.card U := Nat.card_pos
  rw [← h2] at h1
  exact Nat.eq_of_mul_eq_mul_right hpos h1

theorem exists_isHallTwoPrimeOf_of_isSolvable {X : Subgroup G} (hX : Group.IsSolvable ↥X) :
    ∃ D : Subgroup G, Lin2.IsHallTwoPrimeOf D X := by
  obtain ⟨D, hD⟩ := CFSG.SolvableHall.solvable_hall_existence hX {p : Nat.Primes | (p : ℕ) ≠ 2}
  have hcD : Nat.card (D.map X.subtype) = Nat.card D :=
    Subgroup.card_map_of_injective X.subtype_injective
  have hDD : (D.map X.subtype).subgroupOf X = D :=
    Subgroup.comap_map_eq_self_of_injective X.subtype_injective D
  refine ⟨D.map X.subtype, Subgroup.map_subtype_le D, ?_, ?_⟩
  · rw [hcD, Nat.odd_iff]
    rcases Nat.mod_two_eq_zero_or_one (Nat.card D) with h | h
    · exfalso
      have h2 := hD.p_in_pi_of_p_dvd_card ⟨2, Nat.prime_two⟩ (Nat.dvd_of_mod_eq_zero h)
      exact h2 rfl
    · exact h
  · rw [Subgroup.relIndex, hDD]
    rcases Nat.eq_two_pow_or_exists_odd_prime_and_dvd D.index with h | ⟨p, hp, hpd, hpo⟩
    · exact h
    · exfalso
      have h2 := hD.p_in_pi_of_p_dvd_index ⟨p, hp⟩ hpd
      apply h2
      show p ≠ 2
      rintro rfl
      exact (Nat.not_even_iff_odd.mpr hpo) even_two

end General

namespace Hyp5_0_1

variable {G : Type} [Group G] [Finite G] {T M L : Subgroup G} {n : ℕ}

theorem exists_isHall_borel (h : Hyp5_0_1 G T M L n) :
    ∃ D : Subgroup G, Lin2.IsHallTwoPrimeOf D (borelL T L) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSB := h.isSylowTwoOf_borel
  have hPB : T ⊓ L ≤ borelL T L := inf_le_borel T L
  have hBN : borelL T L ≤ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G) := inf_le_right
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp hSB.2.1
  have hodd : Odd ((T ⊓ L).relIndex (borelL T L)) :=
    Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hSB.2.2)
  have hcop : Nat.Coprime (Nat.card (T ⊓ L : Subgroup G)) ((T ⊓ L).relIndex (borelL T L)) := by
    rw [hk]
    exact Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hodd)
  obtain ⟨E, hEB, -, -, hcE, hiE⟩ := exists_complement_of_coprime hPB hBN hcop
  refine ⟨E, hEB, ?_, k, hiE.trans hk⟩
  rw [hcE]
  exact hodd

theorem lemma_5_1_5_two (h : Hyp5_0_1 G T M L n) (h331 : Stmt3_3_1) (hR : L2RankOneSylowFact)
    (hE : E22MSolvableFact) {H D : Subgroup G} (hH : IsHStar T M H)
    (hD : Lin2.IsHallTwoPrimeOf D (borelL T L)) (hq : ∃ K ∈ cComp H, E2.HasE22LieQuot K) :
    Group.IsSolvable ↥(H ⊓ M) ∧ ∃ B : Subgroup G, Lin2.IsHallTwoPrimeOf B (H ⊓ M) ∧
      B ≤ Subgroup.normalizer (D : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hmp, -⟩ := h.minParabolic_of_isHStar h331 hH
  obtain ⟨hnsolv, hsqtk⟩ := h.not_isSolvable_and_sqtk_of_lie hH hq
  have hsolv : Group.IsSolvable ↥(H ⊓ M) := hE G H T (H ⊓ M) hmp hsqtk hnsolv hq
  refine ⟨hsolv, ?_⟩
  obtain ⟨P, hP⟩ : ∃ P : Subgroup G, P = T ⊓ L := ⟨_, rfl⟩
  obtain ⟨Bl, hBl⟩ : ∃ Bl : Subgroup G, Bl = borelL T L := ⟨_, rfl⟩
  have hSB : IsSylowTwoOf P Bl := by
    rw [hP, hBl]
    exact h.isSylowTwoOf_borel
  have hP2 : IsPGroup 2 P := hSB.2.1
  have hPB : P ≤ Bl := hSB.1
  have hBN : Bl ≤ Subgroup.normalizer (P : Set G) := by
    rw [hP, hBl]
    exact inf_le_right
  have hHMP : H ⊓ M ≤ Subgroup.normalizer (P : Set G) := by
    rw [hP]
    exact h.inf_le_normalizer_inf h331 hR hH
  have hHMB : H ⊓ M ≤ Subgroup.normalizer (Bl : Set G) := by
    rw [hBl]
    exact h.inf_le_normalizer_borel h331 hR hH
  have hTHM : T ≤ H ⊓ M := le_inf hH.1.1 h.T_le
  have hPHM : P ≤ H ⊓ M := by
    rw [hP]
    exact inf_le_left.trans hTHM
  have hD' : Lin2.IsHallTwoPrimeOf D Bl := by
    rw [hBl]
    exact hD
  obtain ⟨U, hU⟩ := exists_isHallTwoPrimeOf_of_isSolvable hsolv
  have hUHM : U ≤ H ⊓ M := hU.1
  obtain ⟨Y, hY⟩ : ∃ Y : Subgroup G, Y = U ⊔ Bl := ⟨_, rfl⟩
  have hUY : U ≤ Y := by
    rw [hY]
    exact le_sup_left
  have hBY : Bl ≤ Y := by
    rw [hY]
    exact le_sup_right
  have hPY : P ≤ Y := hPB.trans hBY
  have hYP : Y ≤ Subgroup.normalizer (P : Set G) := by
    rw [hY]
    exact sup_le (hUHM.trans hHMP) hBN
  have hYB : Y ≤ Subgroup.normalizer (Bl : Set G) := by
    rw [hY]
    exact sup_le (hUHM.trans hHMB) Subgroup.le_normalizer
  have hoddB : Odd (P.relIndex Bl) := Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hSB.2.2)
  have hoddBY : Odd (Bl.relIndex Y) := by
    have hnorm : (Bl.subgroupOf Y).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hBY).mpr hYB
    have h1 := Subgroup.relIndex_sup_right (H := U.subgroupOf Y) (K := Bl.subgroupOf Y)
    have hsup : U.subgroupOf Y ⊔ Bl.subgroupOf Y = ⊤ := by
      rw [← Subgroup.subgroupOf_sup hUY hBY, ← hY, Subgroup.subgroupOf_self]
    rw [hsup, Subgroup.relIndex_top_right, Subgroup.relIndex_subgroupOf hUY] at h1
    have h2 := Subgroup.relIndex_mul_card Bl U
    have hdvd : Bl.relIndex U ∣ Nat.card U := Dvd.intro _ h2
    show Odd (Bl.subgroupOf Y).index
    rw [h1]
    exact hU.2.1.of_dvd_nat hdvd
  have hoddY : Odd (P.relIndex Y) := by
    rw [← Subgroup.relIndex_mul_relIndex P Bl Y hPB hBY]
    exact hoddB.mul hoddBY
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp hP2
  have hcopY : Nat.Coprime (Nat.card P) (P.relIndex Y) := by
    rw [hk]
    exact Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hoddY)
  obtain ⟨E, hEY, hEP, hEs, -, -⟩ := exists_complement_of_coprime hPY hYP hcopY
  have hEN : E ≤ Subgroup.normalizer (P : Set G) := hEY.trans hYP
  obtain ⟨W, hW⟩ : ∃ W : Subgroup G, W = P ⊔ U := ⟨_, rfl⟩
  have hPW : P ≤ W := by
    rw [hW]
    exact le_sup_left
  have hUW : U ≤ W := by
    rw [hW]
    exact le_sup_right
  have hWY : W ≤ Y := by
    rw [hW]
    exact sup_le hPY hUY
  have hPU : P ⊓ U = ⊥ := inf_eq_bot_of_odd_of_isPGroup hP2 hU.2.1
  have hoddW : Odd (P.relIndex W) := by
    have := Subgroup.relIndex_mul_relIndex P W Y hPW hWY
    exact hoddY.of_dvd_nat (Dvd.intro _ this)
  have hWE : P ⊔ (W ⊓ E) = W := by
    apply le_antisymm (sup_le hPW inf_le_left)
    calc W = W ⊓ (P ⊔ E) := by rw [hEs]; exact (inf_eq_left.mpr hWY).symm
      _ ≤ P ⊔ (W ⊓ E) := inf_sup_le_sup_inf hPW hEN
  have hWEP : P ⊓ (W ⊓ E) = ⊥ :=
    eq_bot_iff.mpr ((inf_le_inf_left P inf_le_right).trans hEP.le)
  obtain ⟨x, hxP, hUx⟩ := exists_mem_conj_of_complements hPW (hWY.trans hYP) hP2 hoddW
    inf_le_left hWEP hWE hUW hPU hW.symm
  have hxY : x ∈ Y := hPY hxP
  have hinj : ∀ z : G, Function.Injective (MulAut.conj z).toMonoidHom :=
    fun z => (MulAut.conj z).injective
  obtain ⟨E', hE'⟩ : ∃ E' : Subgroup G, E' = E.map (MulAut.conj x).toMonoidHom := ⟨_, rfl⟩
  have hUE' : U ≤ E' := by
    rw [hUx, hE']
    exact Subgroup.map_mono inf_le_right
  have hPx : P.map (MulAut.conj x).toMonoidHom = P := map_conj_eq_of_mem_normalizer (hYP hxY)
  have hYx : Y.map (MulAut.conj x).toMonoidHom = Y :=
    map_conj_eq_of_mem_normalizer (Subgroup.le_normalizer hxY)
  have hE'Y : E' ≤ Y := by
    rw [← hYx, hE']
    exact Subgroup.map_mono hEY
  have hE'P : P ⊓ E' = ⊥ := by
    rw [← hPx, hE', ← Subgroup.map_inf _ _ _ (hinj x), hEP, Subgroup.map_bot]
  have hE's : P ⊔ E' = Y := by
    rw [← hPx, hE', ← Subgroup.map_sup, hEs, hYx]
  have hE'N : E' ≤ Subgroup.normalizer (P : Set G) := hE'Y.trans hYP
  have hBE : P ⊔ (Bl ⊓ E') = Bl := by
    apply le_antisymm (sup_le hPB inf_le_left)
    calc Bl = Bl ⊓ (P ⊔ E') := by rw [hE's]; exact (inf_eq_left.mpr hBY).symm
      _ ≤ P ⊔ (Bl ⊓ E') := inf_sup_le_sup_inf hPB hE'N
  have hBEP : P ⊓ (Bl ⊓ E') = ⊥ :=
    eq_bot_iff.mpr ((inf_le_inf_left P inf_le_right).trans hE'P.le)
  have hDP : P ⊓ D = ⊥ := by
    rw [inf_comm, hP]
    exact Hyp5_0_1.inf_eq_bot_of_isHall hD (h.sylow.1.to_le inf_le_left)
  have hDs : P ⊔ D = Bl := by
    rw [sup_comm, hP, hBl]
    exact h.borelL_eq_sup hD
  obtain ⟨y, hyP, hDy⟩ := exists_mem_conj_of_complements hPB hBN hP2 hoddB inf_le_left hBEP hBE
    hD'.1 hDP hDs
  have hyHM : y ∈ H ⊓ M := hPHM hyP
  refine ⟨U.map (MulAut.conj y).toMonoidHom, isHallTwoPrimeOf_map_conj hU hyHM, ?_⟩
  obtain ⟨E'', hE''⟩ : ∃ E'' : Subgroup G, E'' = E'.map (MulAut.conj y).toMonoidHom := ⟨_, rfl⟩
  have hBy : Bl.map (MulAut.conj y).toMonoidHom = Bl :=
    map_conj_eq_of_mem_normalizer (Subgroup.le_normalizer (hPB hyP))
  have hYy : Y.map (MulAut.conj y).toMonoidHom = Y :=
    map_conj_eq_of_mem_normalizer (Subgroup.le_normalizer (hPY hyP))
  have hD'' : D = Bl ⊓ E'' := by
    rw [hDy, Subgroup.map_inf _ _ _ (hinj y), hBy, hE'']
  have hE''Y : E'' ≤ Y := by
    rw [← hYy, hE'']
    exact Subgroup.map_mono hE'Y
  have hE''N : E'' ≤ Subgroup.normalizer ((Bl ⊓ E'' : Subgroup G) : Set G) :=
    (le_inf (hE''Y.trans hYB) Subgroup.le_normalizer).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  rw [hD'']
  have hUE'' : U.map (MulAut.conj y).toMonoidHom ≤ E'' := by
    rw [hE'']
    exact Subgroup.map_mono hUE'
  exact hUE''.trans hE''N

end Hyp5_0_1

theorem stmt5_1_5_of (h331 : Stmt3_3_1) (hR : L2RankOneSylowFact) (hE : E22MSolvableFact) :
    Stmt5_1_5 := by
  intro G _ _ T M L H D n h hH hD
  obtain ⟨h1, h2⟩ := h.lemma_5_1_5_one h331 hR hH hD
  exact ⟨h1, h2, fun hq => h.lemma_5_1_5_two h331 hR hE hH hD hq⟩

end CFSG.Quasithin.H13
