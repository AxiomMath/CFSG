module

public import CFSG.RankThree.PartTwo.Sec19.SimsSolEvenSixQ16A
public import CFSG.RankThree.PartTwo.Sec19.SimsSolEvenSixQ16AltO
public import CFSG.RankThree.PartTwo.Sec19.SimsSolEvenSixAlt
import CFSG.RankThree.PartTwo.Sec19.SimsSolEvenSixQ16Grp
import CFSG.RankThree.PartTwo.Sec15.Item1424Proof
public import CFSG.RankThree.PartTwo.Sec19.SimsSolEvenSixST
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.TypeB2
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.Unitary
import CFSG.RankThree.Asc83Table.PermTables
import CFSG.RankThree.PartTwo.Sec11.Data
import CFSG.RankThree.PartTwo.Sec14.Item1411HJ
import CFSG.RankThree.PartTwo.Sec14.Item143N
import CFSG.RankThree.PartTwo.Sec15.Item1424ProofFive
import CFSG.RankThree.PartTwo.Sec15.Item1424ProofNotHJ
import CFSG.RankThree.PartTwo.Sec15.Item1514Steps1515S17
import CFSG.RankThree.PartTwo.Sec15.Item1514StepsQuot
import CFSG.RankThree.PartTwo.Sec15.Item1514StepsRoute
import CFSG.RankThree.PartTwo.Sec15.Item1514StepsS17
import CFSG.RankThree.PartTwo.Sec16.Item164Proof
import CFSG.RankThree.PartTwo.Sec17.Item1724Two
import CFSG.RankThree.PartTwo.Sec17.Item175Proof
import CFSG.RankThree.PartTwo.Sec17.Item17ParaHJ
import CFSG.RankThree.PartTwo.Sec17.RouteProvers
import CFSG.RankThree.PartTwo.Sec17.RouteProvers142
import CFSG.RankThree.PartTwo.Toolkit.M12Local
import CFSG.RankThree.S4Free.SuzukiEight
import Certificates.Certificate14953
import Certificates.Certificate2246
import Certificates.Certificate5133
import Certificates.Certificate8166
import Certificates.Certificate8169
import TauCeti.GroupTheory.SpecificGroups.CFSG.TypeC.Agreement

public section

namespace CFSG.RankThree.PartTwo.Sec19.SolEven

open CFSG CFSG.QuasithinUnique CFSG.RankThree.PartTwo CFSG.HardMathSupport.Cooperstein.Coordinator
  CFSG.HardMathSupport.Cooperstein.AlternatingGeometry CFSG.CGT.PushingUpLit.SolK
  CFSG.CGT.PushingUpLit.BHS Equiv Equiv.Perm
open CFSG.CGT.Timmesfeld75 (conjSubgroup mem_conjSubgroup)

namespace Cfg.PiData

variable {G : Type} [Group G] [Finite G] {M X : Subgroup G} {C : Cfg G M X 6} (D : C.PiData)

include D in
theorem q16_false_of_card_sylow_le (hR : Nat.card ↥(Rc X) ≤ 2)
    (hQ : Nat.card ↥(CFSG.Open.pCoreOf 2 M) = 16)
    (halt : ∀ m : ↥M, C.θ m ∈ alternatingGroup (Fin 6)) (T : Sylow 2 G) {S₀ : Subgroup G}
    (hS₀M : S₀ ≤ M) (hS₀T : S₀ ≤ T) (hcard : Nat.card (T : Subgroup G) ≤ 2 * Nat.card S₀) :
    False := by
  have hrel := Subgroup.relIndex_mul_card S₀ (T : Subgroup G)
  rw [inf_eq_left.2 hS₀T] at hrel
  have hTS : S₀.relIndex (T : Subgroup G) ≤ 2 := by
    refine Nat.le_of_mul_le_mul_right ?_ (Nat.card_pos : 0 < Nat.card S₀)
    rw [hrel]
    exact hcard
  have hTS0 : S₀.relIndex (T : Subgroup G) ≠ 0 :=
    (Subgroup.isFiniteRelIndex_of_finiteIndex (H := S₀) (K := (T : Subgroup G))).relIndex_ne_zero
  have hP : ∀ P : Subgroup G, P ≤ T → IsPGroup 2 P → (Q16.sqSub P).relIndex P ≤ 32 := by
    intro P hPT hP2
    have hNP : P ⊓ S₀ ≤ P := inf_le_left
    have hNM : P ⊓ S₀ ≤ M := inf_le_right.trans hS₀M
    have hN16 : (Q16.sqSub (P ⊓ S₀)).relIndex (P ⊓ S₀) ≤ 16 :=
      D.q16_relindex_sqSub_le_alt hR hQ hNM (hP2.to_le hNP) fun p hp => halt ⟨p, hNM hp⟩
    have hidx : (P ⊓ S₀).relIndex P ≤ 2 := by
      rw [Subgroup.inf_relIndex_left]
      exact (Subgroup.relIndex_le_of_le_right hPT hTS0).trans hTS
    have hidx0 : (P ⊓ S₀).relIndex P ≠ 0 :=
      (Subgroup.isFiniteRelIndex_of_finiteIndex (H := P ⊓ S₀) (K := P)).relIndex_ne_zero
    have hi : (P ⊓ S₀).relIndex P = 1 ∨ (P ⊓ S₀).relIndex P = 2 := by omega
    rcases hi with h1 | h2
    · have hPN : P ⊓ S₀ = P := le_antisymm inf_le_left (Subgroup.relIndex_eq_one.1 h1)
      rw [hPN] at hN16
      omega
    · have := Q16.relindex_sqSub_le_of_relindex_two hNP h2
      omega
  have hall : ∀ P : Subgroup G, IsPGroup 2 P → (Q16.sqSub P).relIndex P ≤ 32 := by
    intro P hP2
    obtain ⟨S', hPS'⟩ := hP2.exists_le_sylow
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G S' T
    have hle : P.map (MulAut.conj g).toMonoidHom ≤ T := by
      rw [← hg]
      intro y hy
      obtain ⟨p, hp, rfl⟩ := hy
      exact (Subgroup.mem_pointwise_smul_iff_inv_smul_mem).2 (by
        simpa [MulAut.smul_def, MulAut.conj_apply, mul_assoc] using hPS' hp)
    have hP' : IsPGroup 2 (P.map (MulAut.conj g).toMonoidHom) := hP2.map _
    have h := hP _ hle hP'
    rwa [Q16.relindex_sqSub_conj] at h
  have h2 := Q16.evenRank_le_two_of_relindex_sqSub_le C.S.charTwo hall
  have h3 : CFSG.Open.evenRank G = 3 := C.S.evenRank
  omega

end Cfg.PiData

namespace Cfg

variable {G : Type} [Group G] [Finite G] {M X : Subgroup G} (C : Cfg G M X 6)

@[expose] noncomputable def q16S0 : Subgroup G := (Q16Alt.dZero.comap C.θ).map M.subtype

theorem mem_q16S0 {g : G} : g ∈ C.q16S0 ↔ ∃ h : g ∈ M, C.θ ⟨g, h⟩ ∈ Q16Alt.dZero := by
  constructor
  · rintro ⟨m, hm, rfl⟩
    exact ⟨m.2, hm⟩
  · rintro ⟨h, hθ⟩
    exact ⟨⟨g, h⟩, hθ, rfl⟩

theorem q16S0_le : C.q16S0 ≤ M := Subgroup.map_subtype_le _

theorem pCoreOf_le_q16S0 : CFSG.Open.pCoreOf 2 M ≤ C.q16S0 := fun q hq =>
  C.mem_q16S0.2 ⟨pCoreOf_le_self M hq, by
    rw [C.theta_Q (by norm_num) hq]
    exact Subgroup.one_mem _⟩

theorem exists_theta_q16S0 {σ : Perm (Fin 6)} (hσ : σ ∈ Q16Alt.dZero) :
    ∃ s : ↥M, (s : G) ∈ C.q16S0 ∧ C.θ s = σ := by
  obtain ⟨x, hx⟩ := C.exists_lift (Q16Alt.dZero_le_alternatingGroup hσ)
  exact ⟨⟨(x : G), C.S.le x.2⟩, C.mem_q16S0.2 ⟨_, by rw [hx]; exact hσ⟩, hx⟩

theorem map_theta_q16S0 : (C.q16S0.subgroupOf M).map C.θ = Q16Alt.dZero := by
  ext σ
  constructor
  · rintro ⟨m, hm, rfl⟩
    obtain ⟨h, hθ⟩ := C.mem_q16S0.1 (Subgroup.mem_subgroupOf.1 hm)
    exact hθ
  · intro hσ
    obtain ⟨s, hs, hsσ⟩ := C.exists_theta_q16S0 hσ
    exact ⟨s, Subgroup.mem_subgroupOf.2 hs, hsσ⟩

theorem card_q16S0 (hR : Nat.card ↥(Rc X) ≤ 2) (hQ : Nat.card ↥(CFSG.Open.pCoreOf 2 M) = 16) :
    Nat.card C.q16S0 = 128 := by
  have h := C.card_eq_card_inf_mul hR C.q16S0_le
  rw [inf_eq_right.2 C.pCoreOf_le_q16S0, C.map_theta_q16S0, hQ, Q16Alt.card_dZero] at h
  omega

theorem isPGroup_q16S0 (hR : Nat.card ↥(Rc X) ≤ 2)
    (hQ : Nat.card ↥(CFSG.Open.pCoreOf 2 M) = 16) : IsPGroup 2 C.q16S0 :=
  IsPGroup.of_card (n := 7) (by rw [C.card_q16S0 hR hQ]; norm_num)

theorem card_M_alt (hR : Nat.card ↥(Rc X) ≤ 2) (hQ : Nat.card ↥(CFSG.Open.pCoreOf 2 M) = 16)
    (halt : ∀ m : ↥M, C.θ m ∈ alternatingGroup (Fin 6)) : Nat.card ↥M = 2 ^ 7 * 45 := by
  have hrange : C.θ.range = alternatingGroup (Fin 6) := by
    refine le_antisymm (fun σ ⟨m, hm⟩ => hm ▸ halt m) fun σ hσ => ?_
    obtain ⟨y, hy⟩ := C.exists_lift hσ
    exact ⟨_, hy⟩
  rw [Cfg.PiData.q16_card_M (C := C) hR hQ, hrange, nat_card_alternatingGroup,
    Nat.card_eq_fintype_card, Fintype.card_fin]
  rfl

theorem exists_sylow_q16S0 (hR : Nat.card ↥(Rc X) ≤ 2)
    (hQ : Nat.card ↥(CFSG.Open.pCoreOf 2 M) = 16)
    (halt : ∀ m : ↥M, C.θ m ∈ alternatingGroup (Fin 6)) :
    ∃ T : Sylow 2 G, C.q16S0 ≤ T ∧ (T : Subgroup G) ⊓ M = C.q16S0 := by
  obtain ⟨T, hT⟩ := (C.isPGroup_q16S0 hR hQ).exists_le_sylow
  refine ⟨T, hT, ?_⟩
  have hM := C.card_M_alt hR hQ halt
  have hK2 : IsPGroup 2 ↥((T : Subgroup G) ⊓ M) := T.isPGroup'.to_le inf_le_left
  have hle : Nat.card ↥((T : Subgroup G) ⊓ M) ≤ 2 ^ 7 :=
    Q16Mod.card_le_of_dvd hK2 (n := 2 ^ 7 * 45) (m := 7)
      (by rw [← hM]; exact Subgroup.card_dvd_of_le inf_le_right) (by decide)
  refine (Subgroup.eq_of_le_of_card_ge (le_inf hT C.q16S0_le) ?_).symm
  have := C.card_q16S0 hR hQ
  omega

end Cfg

namespace Cfg.PiData

variable {G : Type} [Group G] [Finite G] {M X : Subgroup G} {C : Cfg G M X 6} (D : C.PiData)

include D in
theorem q16_mul_self_eq_one (hR : Nat.card ↥(Rc X) ≤ 2)
    (hQ : Nat.card ↥(CFSG.Open.pCoreOf 2 M) = 16) {q : G} (hq : q ∈ CFSG.Open.pCoreOf 2 M) :
    q * q = 1 := by
  have h : D.piQ (⟨q, hq⟩ * ⟨q, hq⟩) = D.piQ 1 := by
    apply Multiplicative.toAdd.injective
    rw [map_mul, toAdd_mul, permBar_add_self, map_one, toAdd_one]
  exact congrArg Subtype.val (D.q16_piQ_injective hR hQ h)

theorem exists_q16_z : ∃ (z : G) (hz : z ∈ CFSG.Open.pCoreOf 2 M),
    Multiplicative.toAdd (D.piQ ⟨z, hz⟩) = Q16Alt.zBar := by
  obtain ⟨u, hu⟩ := Q16Alt.zPerp_subset_range Q16Alt.zBar_mem_zPerp
  obtain ⟨q, -, hq⟩ := Subgroup.mem_map.1 (D.heart_mem_piQ_Q u)
  refine ⟨(q : G), q.2, ?_⟩
  show Multiplicative.toAdd (D.piQ q) = Q16Alt.zBar
  rw [hq]
  exact hu

theorem TOf_le_q16S0 (hR : Nat.card ↥(Rc X) ≤ 2)
    (halt : ∀ m : ↥M, C.θ m ∈ alternatingGroup (Fin 6)) {z : G}
    (hz : z ∈ CFSG.Open.pCoreOf 2 M)
    (hπz : Multiplicative.toAdd (D.piQ ⟨z, hz⟩) = Q16Alt.zBar) : TOf M z ≤ C.q16S0 := by
  intro t ht
  have htM : t ∈ M := TOf_le_M M z ht
  have hθt : C.θ ⟨t, htM⟩ ∈ klein4 ({4, 5} : Finset (Fin 6))ᶜ := by
    rw [← D.theta_TOf_len_two hR halt hz (I := {4, 5}) (by decide) hπz]
    exact C.mem_thetaN.2 ⟨⟨t, htM⟩, ht, rfl⟩
  exact C.mem_q16S0.2 ⟨htM, Q16Alt.klein4_le_dZero hθt⟩

theorem card_TOf_q16 (hR : Nat.card ↥(Rc X) ≤ 2) (hQ : Nat.card ↥(CFSG.Open.pCoreOf 2 M) = 16)
    (halt : ∀ m : ↥M, C.θ m ∈ alternatingGroup (Fin 6)) {z : G}
    (hz : z ∈ CFSG.Open.pCoreOf 2 M)
    (hπz : Multiplicative.toAdd (D.piQ ⟨z, hz⟩) = Q16Alt.zBar) : Nat.card ↥(TOf M z) = 64 := by
  have hIc : (({4, 5} : Finset (Fin 6))ᶜ).card = 4 := by decide
  have h1 := C.card_eq_card_inf_mul hR (TOf_le_M M z)
  have h2 : TOf M z ⊓ CFSG.Open.pCoreOf 2 M = CFSG.Open.pCoreOf 2 M :=
    inf_eq_right.2 (Q_le_TOf (C.Q_comm hR) hz)
  have h3 : ((TOf M z).subgroupOf M).map C.θ = klein4 ({4, 5} : Finset (Fin 6))ᶜ :=
    D.theta_TOf_len_two hR halt hz (I := {4, 5}) (by decide) hπz
  rw [h2, h3, hQ, card_klein4 hIc] at h1
  omega

theorem q16_mem_M_of_comm_mem (hR : Nat.card ↥(Rc X) ≤ 2)
    (hQ : Nat.card ↥(CFSG.Open.pCoreOf 2 M) = 16)
    (halt : ∀ m : ↥M, C.θ m ∈ alternatingGroup (Fin 6)) {z : G}
    (hz : z ∈ CFSG.Open.pCoreOf 2 M)
    (hπz : Multiplicative.toAdd (D.piQ ⟨z, hz⟩) = Q16Alt.zBar) {O : Subgroup G}
    (hOT : O ≤ TOf M z) (hO32 : Nat.card O = 32) {q : G} (hqQ : q ∈ CFSG.Open.pCoreOf 2 M)
    (hqO : q ∉ O) {t : G} (htO : ∀ x ∈ O, t * x * t⁻¹ ∈ O) (htq : t * q * t⁻¹ * q⁻¹ ∈ O) :
    t ∈ M := by
  have hQT : CFSG.Open.pCoreOf 2 M ≤ TOf M z := Q_le_TOf (C.Q_comm hR) hz
  have hidx : (O.subgroupOf (TOf M z)).index = 2 := by
    have h := Subgroup.relIndex_mul_card O (TOf M z)
    rw [inf_eq_left.2 hOT, hO32, D.card_TOf_q16 hR hQ halt hz hπz] at h
    exact (by omega : O.relIndex (TOf M z) = 2)
  have hcov : ∀ u ∈ TOf M z, u ∈ O ∨ q⁻¹ * u ∈ O := by
    intro u hu
    by_contra hcon
    rw [not_or] at hcon
    obtain ⟨huO, hquO⟩ := hcon
    apply hquO
    have h1 : (⟨q, hQT hqQ⟩ : ↥(TOf M z))⁻¹ ∈ O.subgroupOf (TOf M z) ↔
        (⟨u, hu⟩ : ↥(TOf M z)) ∈ O.subgroupOf (TOf M z) := by
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
      change q⁻¹ ∈ O ↔ u ∈ O
      rw [O.inv_mem_iff]
      exact iff_of_false hqO huO
    exact Subgroup.mem_subgroupOf.1 ((Subgroup.mul_mem_iff_of_index_two hidx).2 h1)
  have hconjT : ∀ u ∈ TOf M z, t * u * t⁻¹ ∈ TOf M z := by
    intro u hu
    rcases hcov u hu with h | h
    · exact hOT (htO u h)
    · have e : t * u * t⁻¹ = (t * q * t⁻¹ * q⁻¹) * q * (t * (q⁻¹ * u) * t⁻¹) := by group
      rw [e]
      exact (TOf M z).mul_mem ((TOf M z).mul_mem (hOT htq) (hQT hqQ)) (hOT (htO _ h))
  have hconj : conjSubgroup t (CFSG.Open.pCoreOf 2 M) ≤ TOf M z := by
    intro x hx
    have hu := hQT (mem_conjSubgroup.1 hx)
    have e : x = t * (t⁻¹ * x * t) * t⁻¹ := by group
    rw [e]
    exact hconjT _ hu
  have hEq := D.conj_eq_of_le_TOf_len_two hR halt hz (I := {4, 5}) (by decide) hπz hconj
  rw [← C.S.normalizer_Q_eq]
  exact TI.mem_normalizer_iff_conj.2 hEq

theorem q16_z_central (hR : Nat.card ↥(Rc X) ≤ 2)
    (hQ : Nat.card ↥(CFSG.Open.pCoreOf 2 M) = 16) {z : G} (hz : z ∈ CFSG.Open.pCoreOf 2 M)
    (hπz : Multiplicative.toAdd (D.piQ ⟨z, hz⟩) = Q16Alt.zBar) (T : Sylow 2 G)
    (hST : C.q16S0 ≤ T) : ∀ t ∈ (T : Subgroup G), t * z = z * t := by
  have hz1 : z ≠ 1 := D.ne_one_of_len_two hz (I := {4, 5}) (by decide) hπz
  have hQT : CFSG.Open.pCoreOf 2 M ≤ (T : Subgroup G) := C.pCoreOf_le_q16S0.trans hST
  haveI : Nontrivial ↥(T : Subgroup G) :=
    ⟨⟨⟨z, hQT hz⟩, 1, fun h => hz1 (congrArg Subtype.val h)⟩⟩
  haveI := T.isPGroup'.center_nontrivial
  obtain ⟨c, hc1⟩ := exists_ne (1 : ↥(Subgroup.center ↥(T : Subgroup G)))
  have hcc : ∀ t : ↥(T : Subgroup G), t * (c : ↥(T : Subgroup G)) = c * t :=
    Subgroup.mem_center_iff.1 c.2
  have hcG1 : ((c : ↥(T : Subgroup G)) : G) ≠ 1 := fun h => hc1 (Subtype.ext (Subtype.ext h))
  have hcQ : ((c : ↥(T : Subgroup G)) : G) ∈ CFSG.Open.pCoreOf 2 M :=
    (C.centralizer_Q_eq hR).le (Subgroup.mem_centralizer_iff.2 fun h hh =>
      congrArg Subtype.val (hcc ⟨h, hQT hh⟩))
  have hrange := D.q16_piQ_mem_range hR hQ ⟨_, hcQ⟩
  have hfix : ∀ σ ∈ Q16Alt.dZero, barAct σ (Multiplicative.toAdd (D.piQ ⟨_, hcQ⟩)) =
      Multiplicative.toAdd (D.piQ ⟨_, hcQ⟩) := by
    intro σ hσ
    obtain ⟨s, hsS, hsσ⟩ := C.exists_theta_q16S0 hσ
    have hcomm : (s : G) * ((c : ↥(T : Subgroup G)) : G) = ((c : ↥(T : Subgroup G)) : G) * s :=
      congrArg Subtype.val (hcc ⟨s, hST hsS⟩)
    have h := D.piQ_conj s ⟨_, hcQ⟩ ⟨_, hcQ⟩ (by
      show ((c : ↥(T : Subgroup G)) : G) = s * ((c : ↥(T : Subgroup G)) : G) * (s : G)⁻¹
      rw [hcomm]
      group)
    rw [hsσ] at h
    exact h.symm
  rcases Q16Alt.fix_dZero hrange (hfix _ Q16Alt.b1_mem_dZero) (hfix _ Q16Alt.b2_mem_dZero)
      (hfix _ Q16Alt.g3_mem_dZero) with h0 | hzB
  · exfalso
    have h : D.piQ ⟨_, hcQ⟩ = D.piQ 1 := by
      apply Multiplicative.toAdd.injective
      rw [h0, map_one, toAdd_one]
    exact hcG1 (congrArg Subtype.val (D.q16_piQ_injective hR hQ h))
  · have hcz := D.q16_piQ_injective hR hQ (Multiplicative.toAdd.injective (hzB.trans hπz.symm))
    have hcz' : ((c : ↥(T : Subgroup G)) : G) = z := congrArg Subtype.val hcz
    intro t ht
    have h : t * ((c : ↥(T : Subgroup G)) : G) = ((c : ↥(T : Subgroup G)) : G) * t :=
      congrArg Subtype.val (hcc ⟨t, ht⟩)
    rw [hcz'] at h
    exact h

include D in
theorem q16_false_alt (hR : Nat.card ↥(Rc X) ≤ 2) (hQ : Nat.card ↥(CFSG.Open.pCoreOf 2 M) = 16)
    (halt : ∀ m : ↥M, C.θ m ∈ alternatingGroup (Fin 6)) : False := by
  obtain ⟨z, hz, hπz⟩ := D.exists_q16_z
  have hz1 : z ≠ 1 := D.ne_one_of_len_two hz (I := {4, 5}) (by decide) hπz
  obtain ⟨T, hST, hTM⟩ := C.exists_sylow_q16S0 hR hQ halt
  have hzT := D.q16_z_central hR hQ hz hπz T hST
  have hTH : (T : Subgroup G) ≤ Subgroup.centralizer ({z} : Set G) := fun t ht =>
    Subgroup.mem_centralizer_singleton_iff.2 (hzT t ht)
  by_cases hK : Subgroup.centralizer ({z} : Set G) ≤ M
  · exact D.q16_false_of_sylow_le hR hQ T (hTH.trans hK)
  obtain ⟨hOT, hQO, hθO⟩ := D.pCore_facts_of_not_le hR halt hz (I := {4, 5}) (by decide) hπz hK
  set Q : Subgroup G := CFSG.Open.pCoreOf 2 M with hQdef
  set H : Subgroup G := Subgroup.centralizer ({z} : Set G) with hHdef
  set O : Subgroup G := CFSG.Open.pCoreOf 2 H with hOdef
  have hQH : Q ≤ H := fun q hq =>
    Subgroup.mem_centralizer_singleton_iff.2 (C.Q_comm hR q hq z hz)
  have hOn : ∀ k ∈ H, ∀ o ∈ O, k * o * k⁻¹ ∈ O := fun k hk o ho => pCoreOf_normalized H hk ho
  have hOM : O ≤ M := hOT.trans (TOf_le_M M z)
  have hKz : H = Subgroup.centralizer ((Subgroup.zpowers z : Subgroup G) : Set G) :=
    centralizer_singleton_eq_zpowers z
  obtain ⟨hzO, hO32, hZO, hcommO⟩ := D.q16_lemma5 hR hQ hz hπz hOM hθO hQO
    (fun q hq o ho => hOn q (hQH hq) o ho)
    (fun y hy o ho => hOn y (by rw [hKz]; exact (Subgroup.mem_inf.1 hy).2) o ho)
  have hz2 : z * z = 1 := D.q16_mul_self_eq_one hR hQ hz
  have h128 := C.card_q16S0 hR hQ
  have hS0 : O ≤ C.q16S0 := hOT.trans (D.TOf_le_q16S0 hR halt hz hπz)
  have hOT' : O ≤ (T : Subgroup G) := hS0.trans hST
  have hC : ∀ t ∈ (T : Subgroup G), (∀ x ∈ O, t * x = x * t) → t ∈ O := by
    intro t ht htc
    exact CFSG.RankThree.PartTwo.Sec15.inf_centralizer_le_pCoreOf_of_fitting
      (C.S.cent z hz hz1)
      (Subgroup.mem_inf.2 ⟨hTH ht, Subgroup.mem_centralizer_iff.2 fun x hx => (htc x hx).symm⟩)
  have hexp : ∀ t ∈ (T : Subgroup G), t ^ 4 ∈ O :=
    Q16Grp.pow_four_mem hOT' T.isPGroup' (fun t ht x hx => hOn t (hTH ht) x hx) hzO hz1 hz2 hzT
      hZO hcommO hO32 hC
  obtain ⟨q, hqQ, hqO⟩ := SetLike.not_le_iff_exists.1 hQO
  have hqq : q * q = 1 := D.q16_mul_self_eq_one hR hQ hqQ
  have hcent : ∀ t ∈ (T : Subgroup G), t * q * t⁻¹ * q⁻¹ ∈ O → t ∈ C.q16S0 := by
    intro t ht htq
    have htM : t ∈ M := D.q16_mem_M_of_comm_mem hR hQ halt hz hπz hOT hO32 hqQ hqO
      (fun x hx => hOn t (hTH ht) x hx) htq
    rw [← hTM]
    exact Subgroup.mem_inf.2 ⟨ht, htM⟩
  have hcardT := Q16Grp.card_le_of_pow_four_mem hS0 hST T.isPGroup'
    (fun t ht x hx => hOn t (hTH ht) x hx) (by omega) (hST (C.pCoreOf_le_q16S0 hqQ)) hqO
    (by rw [hqq]; exact O.one_mem) hcent hexp
  exact D.q16_false_of_card_sylow_le hR hQ halt T C.q16S0_le hST (by omega)

end Cfg.PiData

end CFSG.RankThree.PartTwo.Sec19.SolEven
