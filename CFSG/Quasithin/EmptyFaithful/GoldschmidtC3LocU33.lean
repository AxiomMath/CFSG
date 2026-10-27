module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtC3LocAsm
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtCMaxU33

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.H13.U3
open scoped commutatorElement

namespace GoldC3

open CFSG.QuasithinUnique.Vol2Native.L239.U33 (Witness)

theorem u33_conjN_check : ∀ k : Fin 4, ∀ i j : Fin 4,
    (∃ i' j' : Fin 4, u33GenP k * (u33GenP 0 ^ (i : ℕ) * u33GenP 1 ^ (j : ℕ)) * (u33GenP k)⁻¹ =
        u33GenP 0 ^ (i' : ℕ) * u33GenP 1 ^ (j' : ℕ)) ∧
    (∃ i' j' : Fin 4, (u33GenP k)⁻¹ * (u33GenP 0 ^ (i : ℕ) * u33GenP 1 ^ (j : ℕ)) * u33GenP k =
        u33GenP 0 ^ (i' : ℕ) * u33GenP 1 ^ (j' : ℕ)) := by
  decide +kernel

theorem u33_comm_ne : ⁅⁅u33GenP 0, u33GenP 3⁆, u33GenP 3⁆ ^ 2 ≠ 1 := by decide +kernel

theorem u33_x_ne : u33GenP 3 ≠ 1 := by decide +kernel

section U33


@[expose] def u33NSet : Set U33G :=
  {u | ∃ i j : Fin 4, u33PresHom u = u33GenP 0 ^ (i : ℕ) * u33GenP 1 ^ (j : ℕ)}

theorem u33NSet_le_T : Subgroup.closure u33NSet ≤ u33Data.T := by
  refine (Subgroup.closure_le _).2 ?_
  rintro u ⟨i, j, hij⟩
  have hw : u33GenPG 0 ^ (i : ℕ) * u33GenPG 1 ^ (j : ℕ) ∈ u33Data.T :=
    u33Data.T.mul_mem (u33Data.T.pow_mem u33Data.a_mem_T _) (u33Data.T.pow_mem u33Data.b_mem_T _)
  have : u = u33GenPG 0 ^ (i : ℕ) * u33GenPG 1 ^ (j : ℕ) := by
    apply u33PresHom_injective
    rw [hij, map_mul, map_pow, map_pow, u33PresHom_genPG, u33PresHom_genPG]
  rw [SetLike.mem_coe, this]
  exact hw

theorem u33_conj_N (k : Fin 4) :
    u33GenPG k ∈ Subgroup.normalizer (Subgroup.closure u33NSet : Set U33G) := by
  apply mem_normalizer_closure_of
  · rintro u ⟨i, j, hij⟩
    obtain ⟨⟨i', j', h⟩, -⟩ := u33_conjN_check k i j
    refine ⟨i', j', ?_⟩
    rw [map_mul, map_mul, map_inv, u33PresHom_genPG, hij]
    exact h
  · rintro u ⟨i, j, hij⟩
    obtain ⟨-, ⟨i', j', h⟩⟩ := u33_conjN_check k i j
    refine ⟨i', j', ?_⟩
    rw [map_mul, map_mul, map_inv, u33PresHom_genPG, hij]
    exact h

theorem u33_A_le_normalizer_N :
    u33Data.A ≤ Subgroup.normalizer (Subgroup.closure u33NSet : Set U33G) := by
  refine (Subgroup.closure_le _).2 ?_
  rintro g (rfl | rfl | rfl | rfl)
  · exact u33_conj_N 0
  · exact u33_conj_N 1
  · exact u33_conj_N 2
  · exact u33_conj_N 3

theorem witness_u33_A : Witness u33Data.A := by
  refine ⟨⟨5, by rw [card_u33_A]; norm_num⟩, ?_⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hx3 : orderOf (u33GenPG 3) = 3 := by
    refine orderOf_eq_prime u33Data.hx fun h => u33_x_ne ?_
    have := congrArg u33PresHom h
    rwa [u33PresHom_genPG, map_one] at this
  refine ⟨u33GenPG 3, u33Data.x_mem_A, hx3, Subgroup.closure u33NSet,
    u33NSet_le_T.trans u33Data.T_le_A, fun g hg x hx =>
      (Subgroup.mem_normalizer_iff.1 (u33_A_le_normalizer_N hg) x).1 hx,
    u33_syl.1.to_le u33NSet_le_T, u33GenPG 0,
    Subgroup.subset_closure ⟨1, 0, by rw [u33PresHom_genPG]; simp⟩, fun h => u33_comm_ne ?_⟩
  have h1 := congrArg u33PresHom h
  rw [map_pow, map_commutatorElement, map_commutatorElement, u33PresHom_genPG,
    u33PresHom_genPG, map_one] at h1
  exact h1

theorem u33_isSylowT : IsSylowTwoOf u33Data.T ⊤ := by
  refine ⟨le_top, u33_syl.1, ?_⟩
  have h : (u33Data.T.subgroupOf ⊤).index = u33Data.T.index := Subgroup.relIndex_top_right _
  rw [h]
  exact u33_syl.2

theorem u33_sup_AB : u33Data.A ⊔ u33Data.B = ⊤ := by
  have hTle : u33Data.T ≤ u33Data.A ⊔ u33Data.B := u33Data.T_le_A.trans le_sup_left
  have hA : u33Data.A ≤ u33Data.A ⊔ u33Data.B := le_sup_left
  have hB : u33Data.B ≤ u33Data.A ⊔ u33Data.B := le_sup_right
  rcases u33Data.lattice _ hTle with h | h | h | h
  · rw [h] at hA
    exact absurd (le_antisymm u33Data.T_le_A hA) u33Data.T_ne_A
  · rw [h] at hB
    have hB' : u33Data.B ≤ u33Data.T := u33Data.inf_AB ▸ le_inf hB le_rfl
    exact absurd (le_antisymm u33Data.T_le_B hB') u33Data.T_ne_B
  · rw [h] at hA
    have hA' : u33Data.A ≤ u33Data.T := u33Data.inf_AB ▸ le_inf le_rfl hA
    exact absurd (le_antisymm u33Data.T_le_A hA') u33Data.T_ne_A
  · exact h

theorem u33_centerOf_ne_bot : centerOf u33Data.T ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT : Nontrivial u33Data.T := by
    refine Finite.one_lt_card_iff_nontrivial.mp ?_
    rw [u33_card_T]
    norm_num
  have hz' : Nontrivial (Subgroup.center u33Data.T) := u33_syl.1.center_nontrivial
  obtain ⟨z, hz⟩ := exists_ne (1 : Subgroup.center u33Data.T)
  intro hbot
  have hzc : ((z : u33Data.T) : U33G) ∈ centerOf u33Data.T :=
    ⟨(z : u33Data.T).2, Subgroup.mem_centralizer_iff.2 fun h hh =>
      congrArg Subtype.val (Subgroup.mem_center_iff.1 z.2 ⟨h, hh⟩)⟩
  rw [hbot, Subgroup.mem_bot] at hzc
  exact hz (Subtype.ext (Subtype.ext hzc))

theorem u33_B_le_C :
    u33Data.B ≤ Subgroup.centralizer (centerOf u33Data.T : Set U33G) := by
  have hWz : centerOf u33Data.T ≤ Subgroup.zpowers GoldCMax.u33zc := GoldCMax.centerOf_T_le
  unfold OvergroupData.B
  rw [Subgroup.closure_le]
  intro g hg
  have hgz : g * GoldCMax.u33zc = GoldCMax.u33zc * g := by
    rcases hg with rfl | rfl | rfl | rfl
    · exact (GoldCMax.zc_comm_gen (n := 0) (by norm_num) (by norm_num)).symm
    · exact (GoldCMax.zc_comm_gen (n := 1) (by norm_num) (by norm_num)).symm
    · exact (GoldCMax.zc_comm_gen (n := 2) (by norm_num) (by norm_num)).symm
    · exact (GoldCMax.zc_comm_gen (n := 4) (by norm_num) (by norm_num)).symm
  exact Subgroup.mem_centralizer_iff.mpr fun w hw => GoldCMax.comm_of_mem_zpowers hgz (hWz hw)

theorem u33_not_A_le_C :
    ¬ u33Data.A ≤ Subgroup.centralizer (centerOf u33Data.T : Set U33G) := fun h =>
  GoldCMax.centralizer_ne_top_u33 u33_centerOf_ne_bot
    (top_le_iff.1 (u33_sup_AB ▸ sup_le h u33_B_le_C))

theorem u33_eq_A {Y : Subgroup U33G} (hTY : u33Data.T ≤ Y) (hY : Nat.card Y = 96)
    (hC : ¬ Y ≤ Subgroup.centralizer (centerOf u33Data.T : Set U33G)) : Y = u33Data.A := by
  rcases u33Data.lattice Y hTY with rfl | rfl | rfl | rfl
  · rw [u33_card_T] at hY
    norm_num at hY
  · rfl
  · exact absurd u33_B_le_C hC
  · rw [Subgroup.card_top, card_u33Pres] at hY
    norm_num at hY

theorem u33_inv (α : MulAut U33G) (hα : u33Data.T.map α.toMonoidHom = u33Data.T) :
    u33Data.A.map α.toMonoidHom = u33Data.A := by
  have hZ : (centerOf u33Data.T).map α.toMonoidHom = centerOf u33Data.T := by
    rw [← centerOf_map_equiv α, hα]
  have hC : (Subgroup.centralizer (centerOf u33Data.T : Set U33G)).map α.toMonoidHom =
      Subgroup.centralizer (centerOf u33Data.T : Set U33G) := by
    rw [← centralizer_map_equiv α (centerOf u33Data.T), hZ]
  refine u33_eq_A ?_ ?_ ?_
  · rw [← hα]
    exact Subgroup.map_mono u33Data.T_le_A
  · rw [Subgroup.card_map_of_injective α.injective, card_u33_A]
  · intro h
    rw [← hC] at h
    exact u33_not_A_le_C ((Subgroup.map_le_map_iff_of_injective α.injective).1 h)

theorem u33_normalizer_T : Subgroup.normalizer (u33Data.T : Set U33G) = u33Data.T :=
  u33Extra.normalizer_T

theorem c3Facts_u33 : C3Facts U33G u33Data.T u33Data.A where
  le := u33Data.T_le_A
  card := by rw [card_u33_A, u33_card_T]
  not_normal := by
    rw [u33_normalizer_T]
    exact fun h => u33Data.T_ne_A (le_antisymm u33Data.T_le_A h)
  not_centralizes := u33_not_A_le_C
  maximal := by
    rw [u33_normalizer_T, sup_eq_left.2 u33Data.T_le_A]
    refine isMaxSubgroupIn_of_overgroup_bound (B := 96) ?_ (by rw [card_u33_A]) fun Y hY => ?_
    · intro h
      have h3 : Nat.card u33Data.A = Nat.card (⊤ : Subgroup U33G) := by rw [h]
      rw [card_u33_A, Subgroup.card_top, card_u33Pres] at h3
      norm_num at h3
    · rcases u33Data.lattice Y (u33Data.T_le_A.trans hY) with rfl | rfl | rfl | rfl
      · right
        rw [u33_card_T]
        norm_num
      · right
        rw [card_u33_A]
      · right
        rw [card_u33_B]
      · left
        rfl
  blockFree := Or.inr witness_u33_A
  inv := u33_inv
  cent := by
    rw [u33_normalizer_T]
    exact le_centralizer_centerOf _
  norm := Or.inl u33_normalizer_T.le

theorem threeCLocConcl_u33 {G : Type} [Group G] [Finite G] {L S : Subgroup G}
    (hL : IsPSU 3 3 1 ↥L) (hS2 : IsPGroup 2 S) (hSN : S ≤ Subgroup.normalizer (L : Set G))
    (hSyl : IsSylowTwoOf (S ⊓ L) L) : ThreeCLocConcl G L S := by
  have hLie : CFSG.Blueprint.LieModel ↥L .PSU 3 3 1 := Or.inl ⟨by decide, hL⟩
  let eU : ↥L ≃* U33G :=
    (CFSG.Timmesfeld.nonempty_mulEquiv_PSU3_of_lieModel hLie).some.trans
      u33Pres_mulEquiv_PSU3.some.symm
  exact threeCLocConcl_of_hasC3Data eU u33_isSylowT ⟨_, c3Facts_u33⟩ hS2 hSN hSyl

end U33

end GoldC3

end CFSG.Quasithin
