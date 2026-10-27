module

public import CFSG.RankThree.PartTwo.Sec17.RouteForms
import CFSG.RankThree.PartTwo.Sec15.Item1515StepsProofPoints
import CFSG.RankThree.PartTwo.Sec15.Item152ExclSL2Tools
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.RankThree.PartTwo.Sec5.Tools
import CFSG.RankThree.GF2n.Basic
import CFSG.Quasithin.Vol2.Ch1Sec3Basic

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155R1

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS CFSG.RankThree.PartTwo.Late

open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem res1340_commutator_deltaZero_le {A : Subgroup G} {LB : Subgroup G → Subgroup G}
    (hA : IsE27 A) (h444 : Item1444 A LB) {K V H : Subgroup G}
    (hV : V ∈ invariantPiSubgroups ⊤ A (piCompl 3))
    (hKV : K ≤ Subgroup.normalizer (V : Set G))
    (hDH : delta A LB V ≤ H) (hVH : V ≤ Subgroup.normalizer (H : Set G))
    (hKH : K ≤ Subgroup.normalizer (H : Set G)) :
    ⁅deltaZero A LB K, V⁆ ≤ H := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hV3 : Nat.Coprime 3 (Nat.card V) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr
      ((isPiSubgroup_piCompl_iff Nat.prime_three V).mp hV.2.1)
  have hQV : ∀ B : Subgroup G, IsHyperplane A B → ∀ Q : Subgroup G,
      Q ∈ collectionIn (scriptQZero A LB) (K ⊓ Subgroup.centralizer (B : Set G)) →
      V ≤ commutatorInSubgroup Q H := by
    intro B hB Q hQ
    have hB9 : 3 ^ 2 ≤ Nat.card B := by
      have h := hB.2
      rw [hA.2] at h
      have h9 : (3 : ℕ) ^ 2 = 9 := by norm_num
      rw [h9]
      omega
    have hQK : Q ≤ K := hQ.2.trans inf_le_left
    refine Sec5.le_of_forall_inf_centralizer_le Nat.prime_three
      (Sec5.isElemAbelian_of_le hA.1 hB.1) hB9 (hB.1.trans hV.2.2) hV3 fun v hv hv1 k hk => ?_
    refine mem_commutatorInSubgroup.mpr ⟨hVH (Subgroup.mem_inf.mp hk).1, fun q hq => ?_⟩
    have hvA : v ∈ A := hB.1 hv
    have hQv : Q ∈ collectionIn (scriptQZero A LB) (Subgroup.centralizer {v}) :=
      ⟨hQ.1, hQ.2.trans (inf_le_right.trans
        (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hv)))⟩
    have hAv : A ≤ Subgroup.normalizer
        ((Subgroup.centralizer ({v} : Set G) : Subgroup G) : Set G) :=
      le_trans (fun x hx => Subgroup.mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (hA.1.1.is_comm.comm ⟨x, hx⟩ ⟨v, hvA⟩))) Subgroup.le_normalizer
    have hS : V ⊓ Subgroup.centralizer {v} ∈
        invariantPiSubgroups (Subgroup.centralizer {v}) (A ⊔ Q) (piCompl 3) :=
      ⟨inf_le_right, isPiSubgroup_piCompl_of_le hV.2.1 inf_le_left,
        sup_le (le_normalizer_inf hV.2.2 hAv)
          (le_normalizer_inf (hQK.trans hKV) (hQv.2.trans Subgroup.le_normalizer))⟩
    have hmem := h444 v hvA hv1 Q hQv _ hS
    have hle : ⁅Q, V ⊓ Subgroup.centralizer {v}⁆ ≤ V := by
      refine (Subgroup.commutator_mono le_rfl inf_le_left).trans ?_
      rw [Subgroup.commutator_comm]
      exact Subgroup.le_normalizer_iff_commutator_le_left.mp (hQK.trans hKV)
    exact hDH (le_delta hmem.1 hle (Subgroup.commutator_mem_commutator hq hk))
  have hXT : deltaZero A LB K ≤ commutatorInSubgroup V H := by
    rw [deltaZero_eq_iSup hA K]
    refine iSup₂_le fun B hB => sSup_le fun Q hQ x hx => ?_
    refine mem_commutatorInSubgroup.mpr ⟨hKH (hQ.2.trans inf_le_left hx), fun k hk => ?_⟩
    have h := (mem_commutatorInSubgroup.mp (hQV B hB Q hQ hk)).2 x hx
    rw [← commutatorElement_inv]
    exact inv_mem h
  rw [Subgroup.commutator_le]
  intro x hx k hk
  rw [← commutatorElement_inv]
  exact inv_mem ((mem_commutatorInSubgroup.mp (hXT hx)).2 k hk)

theorem res1340_mem_scriptQ_of_commutator_eq {A : Subgroup G} {c : G} {L : Subgroup G}
    (hR : Sec15R G A c L) (hbot : Item145BotS14) (h444 : Item1444 A (lB A))
    (h146 : Item146 A (lB A)) {X Z : Subgroup G} (hX : X ∈ scriptY4 A (lB A))
    (hZ2 : IsPGroup 2 Z) (hAZ : A ≤ Subgroup.normalizer (Z : Set G))
    (hXZ : X ≤ Subgroup.normalizer (Z : Set G)) (hZX : ⁅Z, X⁆ = Z) :
    Z ∈ scriptQ A (lB A) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hA : IsE27 A := hR.isE27
  have hZ : Z ∈ invariantPiSubgroups ⊤ A (piCompl 3) :=
    ⟨le_top, Sec15.isPiSubgroup_piCompl_three_of_isPGroup Nat.prime_two (by norm_num) hZ2, hAZ⟩
  set Φ : Subgroup G := (frattini ↥Z).map Z.subtype
  set H : Subgroup G := delta A (lB A) Z ⊔ Φ
  have hΦZ : Φ ≤ Z := Subgroup.map_subtype_le _
  have hHZ : H ≤ Z := sup_le (delta_le Z) hΦZ
  have hXΔ : X ≤ Subgroup.normalizer (delta A (lB A) Z : Set G) :=
    hX.2.2.1.le.trans (delta_le_normalizer_delta
      (fun W hW => delta_mem_scriptQ hA h146 hW) hZ hXZ)
  have hXΦ : X ≤ Subgroup.normalizer (Φ : Set G) := fun x hx =>
    CFSG.RankThree.GF2n.mem_normalizer_inSubgroup_frattini (hXZ hx)
  have hXH : X ≤ Subgroup.normalizer (H : Set G) := Sec14.le_normalizer_sup hXΔ hXΦ
  have hZZ : ⁅Z, Z⁆ ≤ Φ := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    exact Subgroup.mem_map.mpr ⟨⁅(⟨a, ha⟩ : Z), ⟨b, hb⟩⁆,
      CFSG.SectionRank.Ccomm.commutator_mem_frattini hZ2 ⟨a, ha⟩ ⟨b, hb⟩, rfl⟩
  have hZH : Z ≤ Subgroup.normalizer (H : Set G) :=
    Subgroup.le_normalizer_iff_commutator_le_left.mpr
      ((Subgroup.commutator_mono hHZ le_rfl).trans (hZZ.trans le_sup_right))
  have hXZH : ⁅X, Z⁆ ≤ H := by
    have h := res1340_commutator_deltaZero_le hA h444 hZ hXZ le_sup_left hZH hXH
    rwa [← Proof1515.eq_deltaZero_of_mem_scriptY4 hbot hR hX] at h
  have hZle : Z ≤ H := calc
    Z = ⁅Z, X⁆ := hZX.symm
    _ = ⁅X, Z⁆ := Subgroup.commutator_comm Z X
    _ ≤ H := hXZH
  have hDZ : delta A (lB A) Z = Z :=
    CFSG.Quasithin.Ch1Sec3.eq_of_sup_frattiniIn_eq (delta_le Z) (le_antisymm hHZ hZle)
  have hQ := delta_mem_scriptQ hA h146 hZ
  rwa [hDZ] at hQ

end CFSG.RankThree.PartTwo.Sec15.Sylow155R1
