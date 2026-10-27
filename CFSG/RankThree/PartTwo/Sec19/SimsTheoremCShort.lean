module

public import CFSG.RankThree.PartTwo.NotationBlocks
import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.PGroupQuotientOfPPrimeElements
import CFSG.LocalAnalysis.RankThreeCoreUniqueness.LocalCore

public section

namespace CFSG.RankThree.PartTwo.Sec19.SimsTheoremC

open CFSG CFSG.QuasithinUnique CFSG.RankThree.PartTwo
open scoped commutatorElement

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem commutator_commutator_eq_of_coprime {P X : Subgroup G}
    (hXP : X ≤ Subgroup.normalizer (P : Set G))
    (hcop : Nat.Coprime (Nat.card X) (Nat.card P)) : ⁅⁅P, X⁆, X⁆ = ⁅P, X⁆ := by
  have hCP : ⁅P, X⁆ ≤ P := Subgroup.le_normalizer_iff_commutator_le_left.mp hXP
  refine le_antisymm (Subgroup.le_normalizer_iff_commutator_le_left.mp
    (Subgroup.normalizer_commutator_ge_right P X)) ?_
  rw [Subgroup.commutator_le]
  intro p hp x hx
  set C : Subgroup G := ⁅P, X⁆ with hC
  set D : Subgroup G := ⁅C, X⁆ with hD
  have hN : (D.subgroupOf C).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (Subgroup.normalizer_commutator_ge_left C X)
  have hmem : ∀ y : X, ⁅p, (y : G)⁆ ∈ C := fun y => Subgroup.commutator_mem_commutator hp y.2
  let g : X → C := fun y => ⟨⁅p, (y : G)⁆, hmem y⟩
  have hg : ∀ y z : X, ((g (y * z) : C) : C ⧸ D.subgroupOf C) =
      (g y : C ⧸ D.subgroupOf C) * (g z : C ⧸ D.subgroupOf C) := by
    intro y z
    rw [← QuotientGroup.mk_mul, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    show (⁅p, (y : G) * (z : G)⁆)⁻¹ * (⁅p, (y : G)⁆ * ⁅p, (z : G)⁆) ∈ D
    have e : (⁅p, (y : G) * (z : G)⁆)⁻¹ * (⁅p, (y : G)⁆ * ⁅p, (z : G)⁆) =
        ⁅(y : G), ⁅p, (z : G)⁆⁻¹⁆ := by
      simp only [commutatorElement_def]
      group
    rw [e, hD, Subgroup.commutator_comm]
    exact Subgroup.commutator_mem_commutator y.2 (inv_mem (hmem z))
  let f : X →* C ⧸ D.subgroupOf C := MonoidHom.mk' (fun y => (g y : C ⧸ D.subgroupOf C)) hg
  have h1 : orderOf (f ⟨x, hx⟩) = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop ((orderOf_map_dvd f _).trans (orderOf_dvd_natCard _))
      ((orderOf_dvd_natCard _).trans ((Subgroup.card_quotient_dvd_card _).trans
        (Subgroup.card_dvd_of_le hCP)))
  have h2 : ((g ⟨x, hx⟩ : C) : C ⧸ D.subgroupOf C) = 1 := orderOf_eq_one_iff.mp h1
  exact Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp h2)

theorem closure_odd_eq_top_of_twoResidual {J : Subgroup G}
    (hJ : ∀ (N : Subgroup J) [N.Normal], IsPGroup 2 (J ⧸ N) → N = ⊤) :
    Subgroup.closure {x : J | Odd (orderOf x)} = ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hN : (Subgroup.closure {x : J | Odd (orderOf x)}).Normal := by
    refine ⟨fun n hn g => ?_⟩
    induction hn using Subgroup.closure_induction with
    | mem x hx =>
      apply Subgroup.subset_closure
      show Odd (orderOf (g * x * g⁻¹))
      have h := (MulAut.conj g).orderOf_eq x
      rw [MulAut.conj_apply] at h
      rw [h]
      exact hx
    | one => simp
    | mul x y _ _ ihx ihy =>
      rw [show g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) by group]
      exact Subgroup.mul_mem _ ihx ihy
    | inv x _ ih =>
      rw [show g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ by group]
      exact Subgroup.inv_mem _ ih
  exact hJ _ (CFSG.Glauberman.isPGroup_quotient_of_pPrime_order_elements_mem _ fun x hx =>
    Subgroup.subset_closure (Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hx)))

theorem commutator_commutator_eq_of_twoResidual {J P : Subgroup G}
    (hJ : ∀ (N : Subgroup J) [N.Normal], IsPGroup 2 (J ⧸ N) → N = ⊤)
    (hP : IsPGroup 2 P) (hJP : J ≤ Subgroup.normalizer (P : Set G)) :
    ⁅⁅P, J⁆, J⁆ = ⁅P, J⁆ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine le_antisymm (Subgroup.le_normalizer_iff_commutator_le_left.mp
    (Subgroup.normalizer_commutator_ge_right P J)) ?_
  have hJD : J ≤ Subgroup.normalizer ((⁅⁅P, J⁆, J⁆ : Subgroup G) : Set G) :=
    Subgroup.normalizer_commutator_ge_right _ _
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hP
  have hodd : ∀ x : J, Odd (orderOf x) → ∀ p ∈ P, ⁅p, (x : G)⁆ ∈ ⁅⁅P, J⁆, J⁆ := by
    intro x hx p hp
    have hXJ : Subgroup.zpowers (x : G) ≤ J := Subgroup.zpowers_le.mpr x.2
    have hcop : Nat.Coprime (Nat.card (Subgroup.zpowers (x : G))) (Nat.card P) := by
      rw [Nat.card_zpowers, Subgroup.orderOf_coe, hn]
      exact Nat.Coprime.pow_right n (Nat.coprime_two_right.mpr hx)
    have hmem : ⁅p, (x : G)⁆ ∈ ⁅P, Subgroup.zpowers (x : G)⁆ :=
      Subgroup.commutator_mem_commutator hp (Subgroup.mem_zpowers _)
    rw [← commutator_commutator_eq_of_coprime (hXJ.trans hJP) hcop] at hmem
    exact Subgroup.commutator_mono (Subgroup.commutator_mono le_rfl hXJ) hXJ hmem
  have key : ∀ j : J, ∀ p ∈ P, ⁅p, (j : G)⁆ ∈ ⁅⁅P, J⁆, J⁆ := by
    intro j
    have hj : j ∈ Subgroup.closure {x : J | Odd (orderOf x)} := by
      rw [closure_odd_eq_top_of_twoResidual hJ]
      exact Subgroup.mem_top j
    induction hj using Subgroup.closure_induction with
    | mem x hx => exact hodd x hx
    | one =>
      intro p _
      simp
    | mul x y _ _ ihx ihy =>
      intro p hp
      have e : ⁅p, ((x * y : J) : G)⁆ =
          ⁅p, (x : G)⁆ * ((x : G) * ⁅p, (y : G)⁆ * (x : G)⁻¹) := by
        rw [Subgroup.coe_mul]
        simp only [commutatorElement_def]
        group
      rw [e]
      exact Subgroup.mul_mem _ (ihx p hp)
        (Subgroup.le_normalizer_iff.mp hJD _ x.2 _ (ihy p hp))
    | inv x _ ih =>
      intro p hp
      have e : ⁅p, ((x⁻¹ : J) : G)⁆ = (x : G)⁻¹ * ⁅p, (x : G)⁆⁻¹ * (x : G)⁻¹⁻¹ := by
        rw [Subgroup.coe_inv]
        simp only [commutatorElement_def]
        group
      rw [e]
      exact Subgroup.le_normalizer_iff.mp hJD _ (inv_mem x.2) _ (inv_mem (ih p hp))
  rw [Subgroup.commutator_le]
  intro p hp j hj
  exact key ⟨j, hj⟩ p hp

omit [Finite G] in
theorem exists_subgroup_sq_mem {U : Subgroup G} (hU : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a)
    (Z : Subgroup G) : ∃ W : Subgroup G, ∀ g, g ∈ W ↔ g ∈ U ∧ g ^ 2 ∈ Z :=
  ⟨{ carrier := {g | g ∈ U ∧ g ^ 2 ∈ Z}
     mul_mem' := fun {a b} ha hb => ⟨U.mul_mem ha.1 hb.1, by
       rw [Commute.mul_pow (hU a ha.1 b hb.1) 2]
       exact Z.mul_mem ha.2 hb.2⟩
     one_mem' := ⟨U.one_mem, by simp⟩
     inv_mem' := fun {a} ha => ⟨U.inv_mem ha.1, by
       rw [inv_pow]
       exact Z.inv_mem ha.2⟩ },
   fun _ => Iff.rfl⟩

theorem IsShort.isElemAbelian_blockU {L : Subgroup G} (hL : IsShort L) :
    CFSG.Open.IsElemAbelian 2 (blockU L) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQp : IsPGroup 2 (blockQ L) := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 L
  have hLQ : L ≤ Subgroup.normalizer (blockQ L : Set G) :=
    CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 L
  have hLU : L ≤ Subgroup.normalizer (blockU L : Set G) :=
    Subgroup.normalizer_commutator_ge_right (blockQ L) L
  have hUQ : blockU L ≤ blockQ L := fun u hu => (hL.blockU_le_center hu).1
  have hUp : IsPGroup 2 (blockU L) := hQp.to_le hUQ
  have hUcomm : ∀ a ∈ blockU L, ∀ b ∈ blockU L, a * b = b * a := fun a ha b hb =>
    Subgroup.mem_centralizer_iff.mp (hL.blockU_le_center hb).2 a (hUQ ha)
  have hZ : ∀ z ∈ blockZ L, z ∈ blockU L ∧ ∀ l ∈ L, l * z = z * l := fun z hz =>
    ⟨hz.1, Subgroup.mem_centralizer_iff.mp hz.2⟩
  obtain ⟨W, hW⟩ := exists_subgroup_sq_mem hUcomm (blockZ L)
  have hZW : blockZ L ≤ W := fun z hz => (hW z).mpr ⟨(hZ z hz).1, Subgroup.pow_mem _ hz 2⟩
  have hWU : W ≤ blockU L := fun w hw => ((hW w).mp hw).1
  have hLZ : ∀ l ∈ L, ∀ z ∈ blockZ L, l * z * l⁻¹ ∈ blockZ L := fun l hl z hz => by
    rw [(hZ z hz).2 l hl, mul_inv_cancel_right]
    exact hz
  have hLW : L ≤ Subgroup.normalizer (W : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro l hl w hw
    obtain ⟨hwU, hwZ⟩ := (hW w).mp hw
    refine (hW _).mpr ⟨Subgroup.le_normalizer_iff.mp hLU l hl w hwU, ?_⟩
    rw [conj_pow]
    exact hLZ l hl _ hwZ
  refine ⟨IsMulCommutative.of_comm fun a b => Subtype.ext (hUcomm a a.2 b b.2), ?_⟩
  rcases hL.irreducible W hZW hWU hLW with hWZ | hWU'
  ·
    have hsq : ∀ u ∈ blockU L, u ^ 2 ∈ blockZ L → u ∈ blockZ L := fun u hu hu2 => by
      rw [← hWZ]
      exact (hW u).mpr ⟨hu, hu2⟩
    have hpow : ∀ k : ℕ, ∀ u ∈ blockU L, u ^ 2 ^ k ∈ blockZ L → u ∈ blockZ L := by
      intro k
      induction k with
      | zero =>
        intro u _ h
        simpa using h
      | succ k ih =>
        intro u hu h
        refine hsq u hu (ih (u ^ 2) (Subgroup.pow_mem _ hu 2) ?_)
        rwa [← pow_mul, ← pow_succ']
    have hUZ : blockU L ≤ blockZ L := by
      intro u hu
      obtain ⟨k, hk⟩ := hUp ⟨u, hu⟩
      have hk' : u ^ 2 ^ k = 1 := by
        simpa using congrArg Subtype.val hk
      exact hpow k u hu (by rw [hk']; exact Subgroup.one_mem _)
    exact absurd (hL.blockZ_lt_blockU.trans_le hUZ) (lt_irrefl _)
  ·
    have hsq : ∀ u ∈ blockU L, u ^ 2 ∈ blockZ L := fun u hu =>
      ((hW u).mp (by rw [hWU']; exact hu)).2
    obtain ⟨V, hV⟩ := exists_subgroup_sq_mem hUcomm ⊥
    have hUL : ⁅blockU L, L⁆ ≤ V := by
      rw [Subgroup.commutator_le]
      intro u hu l hl
      refine (hV _).mpr ⟨Subgroup.le_normalizer_iff_commutator_le_left.mp hLU
        (Subgroup.commutator_mem_commutator hu hl), ?_⟩
      have hc : l * u⁻¹ * l⁻¹ ∈ blockU L :=
        Subgroup.le_normalizer_iff.mp hLU l hl _ (inv_mem hu)
      have hcomm : Commute u (l * u⁻¹ * l⁻¹) := hUcomm u hu _ hc
      have hlu : Commute l (u ^ 2) := (hZ _ (hsq u hu)).2 l hl
      have e : ⁅u, l⁆ = u * (l * u⁻¹ * l⁻¹) := by
        simp only [commutatorElement_def, mul_assoc]
      rw [Subgroup.mem_bot, e, hcomm.mul_pow, conj_pow, inv_pow, hlu.inv_right.eq]
      group
    have hUeq : ⁅blockU L, L⁆ = blockU L :=
      commutator_commutator_eq_of_twoResidual hL.eq_twoResidual hQp hLQ
    intro u hu
    have hu' := ((hV u).mp (hUL (by rw [hUeq]; exact hu))).2
    rwa [Subgroup.mem_bot] at hu'

end CFSG.RankThree.PartTwo.Sec19.SimsTheoremC
