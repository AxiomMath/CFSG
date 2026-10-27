module

import CFSG.LocalAnalysis.UniquenessCase.UC22S2114K2Five
import CFSG.LocalAnalysis.UniquenessCase.UC22P2214f
import CFSG.LocalAnalysis.UniquenessCase.UC22P22f
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.QuotInfBar2
import CFSG.RankThree.GroupTheory.SteinbergCEMutualSupplementResidual
import CFSG.Adapters.StatedClassicalSmallOrders
import CFSG.Adapters.StatedSLTwoField
import CFSG.Quasithin.EmptyFaithful.S143FiveAux
import CFSG.Quasithin.EmptyFaithful.S153QSL2
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21d
public import CFSG.RankThree.SteinbergR3ELinearUnitaryOuterOrder

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open CFSG.QuasithinUnique (IsSylowTwoOf)
open CFSG.Blueprint (LieModel)

theorem uc22s2114_exists_normal_of_index_five {H : Type} [Group H] [Finite H] {S : Subgroup H}
    (hS : IsPGroup 2 S) (hidx : S.index = 5) :
    ∃ X : Subgroup H, X.Normal ∧ IsPGroup 2 ↥⁅X, X⁆ ∧ ∃ g ∈ X, orderOf g = 5 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hK2 : IsPGroup 2 ↥S.normalCore := hS.to_le S.normalCore_le
  have h2 : ∀ N : Subgroup (H ⧸ S.normalCore), N.Normal → IsPGroup 2 N → N = ⊥ := by
    intro N hN hN2
    have : (N.comap (QuotientGroup.mk' S.normalCore)).Normal := hN.comap _
    have hNK : N.comap (QuotientGroup.mk' S.normalCore) ≤ S.normalCore := by
      refine normal_le_normalCore.2 ((hN2.comap_of_ker_isPGroup _ ?_).le_sylow_of_normal
        (hS.toSylow (by rw [hidx]; norm_num)))
      rw [QuotientGroup.ker_mk']
      exact hK2
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective S.normalCore x
    exact mem_bot.2 ((QuotientGroup.eq_one_iff y).2
      (hNK (show y ∈ N.comap (QuotientGroup.mk' S.normalCore) from hx)))
  have hidx' : (S.map (QuotientGroup.mk' S.normalCore)).index = 5 := by
    rw [index_map_eq S (QuotientGroup.mk'_surjective S.normalCore)
      (by rw [QuotientGroup.ker_mk']; exact S.normalCore_le), hidx]
  obtain ⟨P, hPn, hP5, -, -⟩ := CFSG.Quasithin.exists_normal_five_complement h2
    (hS.map (QuotientGroup.mk' S.normalCore)) hidx'
  have : IsCyclic ↥P := isCyclic_of_prime_card hP5
  refine ⟨P.comap (QuotientGroup.mk' S.normalCore), hPn.comap _, hK2.to_le ?_, ?_⟩
  ·
    rw [commutator_le]
    intro a ha b hb
    rw [← QuotientGroup.ker_mk' S.normalCore, MonoidHom.mem_ker, map_commutatorElement,
      commutatorElement_eq_one_iff_mul_comm]
    exact setLike_mul_comm (s := P) (a := QuotientGroup.mk' S.normalCore a)
      (b := QuotientGroup.mk' S.normalCore b) ha hb
  ·
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥P) 5 (dvd_of_eq hP5.symm)
    obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective S.normalCore (x : H ⧸ S.normalCore)
    have hy5 : 5 ∣ orderOf y := by
      rw [← hx, ← Subgroup.orderOf_coe, ← hy]
      exact orderOf_map_dvd _ y
    refine ⟨y ^ (orderOf y / 5), pow_mem ?_ _, orderOf_pow_orderOf_div (orderOf_pos y).ne' hy5⟩
    show QuotientGroup.mk' S.normalCore y ∈ P
    rw [hy]
    exact x.2

theorem uc22s2114_exists_of_solvable_five {Y : Type} [Group Y] [Finite Y]
    (h25 : ¬ 25 ∣ Nat.card Y) {S V : Subgroup Y} (hS : IsSylowTwoOf S ⊤) (hSV : S ≤ V)
    (hV : Group.IsSolvable ↥V) (h5 : 5 ∣ Nat.card ↥V) :
    ∃ X : Subgroup Y, S ≤ normalizer (X : Set Y) ∧ IsPGroup 2 ↥⁅X, X⁆ ∧
      ∃ g ∈ X, orderOf g = 5 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hSodd : ¬ 2 ∣ S.index := by
    have h := hS.2.2
    rwa [show (S.subgroupOf ⊤).index = S.index from relIndex_top_right S] at h
  have hS2 : IsPGroup 2 ↥(S.subgroupOf V) := hS.2.1.comap_subtype
  have hSπ : CFSG.IsPiSubgroup {p : Nat.Primes | (p : ℕ) = 2 ∨ (p : ℕ) = 5} (S.subgroupOf V) := by
    intro p hp
    obtain ⟨k, hk⟩ := hS2.exists_card_eq
    rw [hk] at hp
    exact Or.inl ((Nat.prime_dvd_prime_iff_eq p.2 Nat.prime_two).1 (p.2.dvd_of_dvd_pow hp))
  obtain ⟨H, hH, hSH⟩ := CFSG.SolvableHall.solvable_hall_containment hV _ _ hSπ
  have hS2' : IsPGroup 2 ↥((S.subgroupOf V).subgroupOf H) := hS2.comap_subtype
  have hidx : S.index = ((S.subgroupOf V).subgroupOf H).index * H.index * V.index := by
    rw [show ((S.subgroupOf V).subgroupOf H).index * H.index = (S.subgroupOf V).index from
        relIndex_mul_index hSH,
      show (S.subgroupOf V).index * V.index = S.index from relIndex_mul_index hSV]
  have hodd : ¬ 2 ∣ ((S.subgroupOf V).subgroupOf H).index := fun h =>
    hSodd (hidx ▸ (h.mul_right _).mul_right _)
  obtain ⟨k, hk⟩ : ∃ k : ℕ, ((S.subgroupOf V).subgroupOf H).index = 5 ^ k := by
    refine ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd index_ne_zero_of_finite fun {d} hd hdi => ?_⟩
    have h := hH.p_in_pi_of_p_dvd_card ⟨d, hd⟩ (hdi.trans (index_dvd_card _))
    change d = 2 ∨ d = 5 at h
    rcases h with rfl | rfl
    · exact absurd hdi hodd
    · rfl
  have h5H : 5 ∣ Nat.card ↥H := by
    rw [← card_mul_index H] at h5
    rcases (Nat.Prime.dvd_mul Nat.prime_five).1 h5 with h | h
    · exact h
    · exact (hH.p_in_pi_of_p_dvd_index ⟨5, Nat.prime_five⟩ h (Or.inr rfl)).elim
  have h5S : 5 ∣ ((S.subgroupOf V).subgroupOf H).index := by
    rw [← card_mul_index ((S.subgroupOf V).subgroupOf H)] at h5H
    obtain ⟨j, hj⟩ := hS2'.exists_card_eq
    rw [hj] at h5H
    rcases (Nat.Prime.dvd_mul Nat.prime_five).1 h5H with h | h
    · exact absurd ((Nat.prime_dvd_prime_iff_eq Nat.prime_five Nat.prime_two).1
        (Nat.prime_five.dvd_of_dvd_pow h)) (by norm_num)
    · exact h
  have hY : 5 ^ k ∣ Nat.card Y := hk ▸
    (index_dvd_card _).trans ((card_subgroup_dvd_card H).trans (card_subgroup_dvd_card V))
  have hk1 : ((S.subgroupOf V).subgroupOf H).index = 5 := by
    rw [hk] at h5S ⊢
    rcases k with _ | _ | k
    · norm_num at h5S
    · rfl
    · exact (h25 (by simpa using (pow_dvd_pow 5 (by omega : 2 ≤ k + 2)).trans hY)).elim
  obtain ⟨X₀, hX₀n, hX₀c, g, hgX, hgo⟩ := uc22s2114_exists_normal_of_index_five hS2' hk1
  refine ⟨(X₀.map H.subtype).map V.subtype, ?_, ?_,
    ((g : ↥V) : Y), mem_map_of_mem _ (mem_map_of_mem _ hgX), ?_⟩
  ·
    intro s hs
    refine mem_normalizer_fintype fun z hz => ?_
    obtain ⟨_, ⟨x, hx, rfl⟩, rfl⟩ := hz
    have hsH : (⟨s, hSV hs⟩ : ↥V) ∈ H := hSH (mem_subgroupOf.2 hs)
    exact ⟨_, ⟨_, hX₀n.conj_mem x hx ⟨⟨s, hSV hs⟩, hsH⟩, rfl⟩, rfl⟩
  · rw [← map_commutator, ← map_commutator]
    exact (hX₀c.map _).map _
  · rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hgo]

variable {G : Type} [Group G] [Finite G]

theorem uc22s2114_false_of_isL5_two {D : Data G} {Ch : Choice2011 G} (c : Ctx21 D Ch)
    {L : Subgroup G} (hL : L ∈ calC D.M) (hX : LieModel (BarInf L) .PSL 5 2 1) (hn : 4 ∣ c.n)
    (hBL : c.B0 ≤ normalizer (L : Set G)) (hfaith : ∀ b ∈ c.B0, CentralizesBar b L → b = 1) :
    False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hSCM := LieModel.statedClassicalModel hX (by decide)
  obtain ⟨b, hb, hbL, hb5, hb1⟩ := uc22s2114_exists_five c hL hn hBL hfaith
  have hα5 : inducedBarInfAutHom L ⟨b, hbL⟩ ^ 5 = 1 := rhoInf_pow_eq_one L hbL hb5
  have hin := uc22p2214_out_mem_of_card_dvd
    (CFSG.RankThree.OuterOrder.higher_linear_unitary_outer_order_determinant_bound (Or.inl rfl)
      (by norm_num) Nat.prime_two le_rfl hSCM).1 Nat.prime_five
    (by norm_num [CFSG.RankThree.OuterOrder.determinantParameter]) hα5
  obtain ⟨-, hB0c, -, -, -, -, -, -, -, hperm, -⟩ := c.hB0
  have hXs : Group.IsSolvable ↥(c.B0 ⊔ D.T) :=
    uc22p2214_isSolvable_sup (uc22p22f_odd_card_B { c with B := c.B0, hB := c.hB0, hle := le_rfl })
      hB0c (CFSG.ABGLocalTools.isSylowOf_iff.1 D.sylowM).2.1 hperm
  have hWs : Group.IsSolvable ↥(((c.B0 ⊔ D.T).subgroupOf L).map (piInf L)) := by
    have : Group.IsSolvable ↥((c.B0 ⊔ D.T).subgroupOf L) :=
      Group.isSolvable_of_isSolvable_injective
        (L.subtype.subgroupComap_injective _ L.subtype_injective)
    exact Group.isSolvable_of_surjective ((piInf L).subgroupMap_surjective _)
  obtain ⟨Q, hQ⟩ := uc22p2214_isSylowOf_inf D.sylowM hL.1
  have hUW : (Q : Subgroup ↥L).map (piInf L) ≤ ((c.B0 ⊔ D.T).subgroupOf L).map (piInf L) := by
    refine map_mono fun q hq => mem_subgroupOf.2 (mem_sup_right ?_)
    have h := mem_map_of_mem L.subtype hq
    rw [hQ] at h
    exact h.1
  have hWα : (((c.B0 ⊔ D.T).subgroupOf L).map (piInf L)).map
      (inducedBarInfAutHom L ⟨b, hbL⟩).toMonoidHom =
        ((c.B0 ⊔ D.T).subgroupOf L).map (piInf L) := by
    refine CFSG.Quasithin.H13.L32A.C.SkPf.map_eq_of_forall_mem ?_
    rintro _ ⟨x, hx, rfl⟩
    rw [← uc22s2114_rhoInf_eq, rhoInf_mk]
    refine mem_map_of_mem _ (mem_subgroupOf.2 ?_)
    rw [rhoInf_mk_coe]
    exact mul_mem (mul_mem (mem_sup_left hb) (mem_subgroupOf.1 hx)) (inv_mem (mem_sup_left hb))
  obtain ⟨y, hyN, hy1, hy5⟩ :=
    uc22s2114_exists_of_inner (center_barInf_eq_bot hL.2.2) hWα hin hb1 hα5
  have hVs := CFSG.RankThree.GroupTheory.isSolvable_sup_of_le_normalizer (zpowers_le.2 hyN) hWs
    (inferInstance : Group.IsSolvable ↥(zpowers y))
  have h5V : 5 ∣ Nat.card ↥(((c.B0 ⊔ D.T).subgroupOf L).map (piInf L) ⊔ zpowers y) := by
    have h := orderOf_dvd_natCard (⟨y, mem_sup_right (mem_zpowers y)⟩ :
      ↥(((c.B0 ⊔ D.T).subgroupOf L).map (piInf L) ⊔ zpowers y))
    rwa [Subgroup.orderOf_mk, orderOf_eq_prime hy5 hy1] at h
  have h25 : ¬ 25 ∣ Nat.card (BarInf L) := by
    rw [CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_five_two hSCM]
    norm_num
  obtain ⟨X, hSX, hX2, g, hgX, hg5⟩ := uc22s2114_exists_of_solvable_five h25
    (isSylowTwoOf_map_piInf L Q) (hUW.trans le_sup_left) hVs h5V
  obtain ⟨e⟩ := CFSG.Open.StatedAPI.nonempty_mulEquiv_specialLinear_zmod_two_of_psl hSCM
  exact CFSG.Quasithin.QP.false_of_sylow_solv2 (F := ZMod 2) (X := X.map e.toMonoidHom)
    (by simp) (Or.inr rfl) (CFSG.Quasithin.QP.isSylowTwoOf_map_equiv e (isSylowTwoOf_map_piInf L Q))
    (by rw [← map_equiv_normalizer_eq X e]; exact map_mono hSX)
    (CFSG.Quasithin.QP.solv2_of_commutator _ (by rw [← map_commutator]; exact hX2.map _))
    (mem_map_of_mem e.toMonoidHom hgX)
    (by rw [MulEquiv.coe_toMonoidHom, MulEquiv.orderOf_eq]; exact hg5)

end CFSG.LocalAnalysis.UniquenessCase.UC22
