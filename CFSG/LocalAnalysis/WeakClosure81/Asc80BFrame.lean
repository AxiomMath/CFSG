module

public import CFSG.LocalAnalysis.WeakClosure81.FiveInputs
import CFSG.LocalAnalysis.WeakClosure81.FiveSevenRed
import CFSG.LocalAnalysis.WeakClosure81.FiveSixPart
import CFSG.Adapters.TauCetiLieModels
public import CFSG.Adapters.GeneralizedFitting
public import CFSG.LocalAnalysis.WeakClosure81.FiveFiveBase
public import CFSG.LocalAnalysis.WeakClosure81.FiveFour

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

@[expose] def Asc80ThmBCase (P : ∀ (X : Type) [Group X], Prop) : Prop :=
  ∀ {G : Type} [Group G] [Finite G] (H A M : Subgroup G),
    IsSimpleGroup ↥(Fstar H) → (∃ a b : ↥(Fstar H), a * b ≠ b * a) → P ↥(Fstar H) →
    A ≤ H → IsElemAbelian 2 A → maxOver H A = {M} →
    (∃ n, IsL2 ↥H n ∨ IsSz ↥H n) ∧
      ∃ T : Subgroup G, IsSylowIn 2 T H ∧ M = H ⊓ normalizer (T : Set G)

theorem asc80ThmB_of_cases
    (hAl : Asc80ThmBCase fun X _ => ∃ n : ℕ, 5 ≤ n ∧ Nonempty (X ≃* alternatingGroup (Fin n)))
    (hCO : Asc80ThmBCase fun X _ => CFSG.Models.OddLieType X)
    (hC2 : Asc80ThmBCase fun X _ => CFSG.Models.EvenLieType X)
    (hSp : Asc80ThmBCase fun X _ => CFSG.Models.SporadicRep X) : Asc80ThmB := by
  intro G _ _ H A M hs hnab hcat hAH hA hM
  obtain ⟨i, ⟨e⟩⟩ := hcat
  cases i with
  | cyclic p hp =>
      obtain ⟨a, b, hab⟩ := hnab
      exact absurd (e.injective (by
        rw [map_mul, map_mul]
        exact mul_comm (G := Multiplicative (ZMod p)) _ _)) hab
  | alternating n hn =>
      exact hAl H A M hs hnab ⟨n, hn, ⟨e⟩⟩ hAH hA hM
  | lie d =>
      rcases Models.oddLieType_or_evenLieType_of_valid d ⟨e⟩ with h | h
      · exact hCO H A M hs hnab h hAH hA hM
      · exact hC2 H A M hs hnab h hAH hA hM
  | sporadic s =>
      exact hSp H A M hs hnab ⟨s, ⟨e⟩⟩ hAH hA hM

variable {G : Type} [Group G] [Finite G]

private theorem fstar_self_centralizing_in (H : Subgroup G) :
    H ⊓ Subgroup.centralizer (Fstar H : Set G) ≤ Fstar H := by
  intro x hx
  obtain ⟨hxH, hxC⟩ := hx
  let xH : ↥H := ⟨x, hxH⟩
  have hxHcent : xH ∈ Subgroup.centralizer (genFittingFStar ↥H : Set ↥H) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    apply Subtype.ext
    have hyF : (y : G) ∈ Fstar H := by
      unfold Fstar
      exact Subgroup.mem_map.mpr ⟨y, hy, rfl⟩
    exact (Subgroup.mem_centralizer_iff.mp hxC) (y : G) hyF
  have hxH' := CFSG.Adapters.generalized_fitting_self_centralizing (G := ↥H) hxHcent
  unfold Fstar
  exact Subgroup.mem_map.mpr ⟨xH, hxH', rfl⟩

private theorem inf_centralizer_fstar_eq_bot (H : Subgroup G)
    (hs : IsSimpleGroup ↥(Fstar H))
    (hnab : ∃ a b : ↥(Fstar H), a * b ≠ b * a) :
    H ⊓ Subgroup.centralizer (Fstar H : Set G) = ⊥ := by
  let C : Subgroup G := H ⊓ Subgroup.centralizer (Fstar H : Set G)
  have hCF : C ≤ Fstar H := fstar_self_centralizing_in H
  have hcenter : C.subgroupOf (Fstar H) ≤ Subgroup.center ↥(Fstar H) := by
    intro z hz
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    have hzC : (z : G) ∈ C := Subgroup.mem_subgroupOf.mp hz
    have hzcent : (z : G) ∈ Subgroup.centralizer (Fstar H : Set G) :=
      (Subgroup.mem_inf.mp hzC).2
    exact (Subgroup.mem_centralizer_iff.mp hzcent) (y : G) y.2
  have hZ : Subgroup.center ↥(Fstar H) = ⊥ := by
    haveI : IsSimpleGroup ↥(Fstar H) := hs
    have hnc : ¬ IsMulCommutative ↥(Fstar H) := by
      intro hc
      obtain ⟨a, b, hab⟩ := hnab
      exact hab (hc.is_comm.comm a b)
    exact TauCeti.IsSimpleGroup.center_eq_bot_of_not_isMulCommutative hnc
  have hCbot : C.subgroupOf (Fstar H) = ⊥ := by
    rw [← le_bot_iff]
    exact hcenter.trans (le_of_eq hZ)
  have hmap := Subgroup.map_subgroupOf_eq_of_le hCF
  rw [hCbot, Subgroup.map_bot] at hmap
  exact hmap.symm

private theorem b5_eq_bot_or_fstar_le_of_normal {H N : Subgroup G}
    (hs : IsSimpleGroup ↥(Fstar H))
    (hnab : ∃ a b : ↥(Fstar H), a * b ≠ b * a)
    (hNH : N ≤ H) (hN : (N.subgroupOf H).Normal) :
    N = ⊥ ∨ Fstar H ≤ N := by
  classical
  haveI : IsSimpleGroup ↥(Fstar H) := hs
  have hCn : ((N ⊓ Fstar H).subgroupOf (Fstar H)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff (inf_le_right : N ⊓ Fstar H ≤ Fstar H)]
    intro x g hx hg
    obtain ⟨hxN, hxF⟩ := Subgroup.mem_inf.mp hx
    exact Subgroup.mem_inf.mpr
      ⟨(Subgroup.normal_subgroupOf_iff hNH).1 hN x g hxN (fstar_le_group H hg),
        conj_mem_fstar (fstar_le_group H hg) hxF⟩
  haveI := hCn
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      ((N ⊓ Fstar H).subgroupOf (Fstar H)) with hCbot | hCtop
  · left
    have hNF : N ⊓ Fstar H = ⊥ := by
      have h := Subgroup.map_subgroupOf_eq_of_le (inf_le_right : N ⊓ Fstar H ≤ Fstar H)
      rw [hCbot, Subgroup.map_bot] at h
      exact h.symm
    have hNC : N ≤ H ⊓ Subgroup.centralizer (Fstar H : Set G) := by
      intro x hxN
      refine ⟨hNH hxN, Subgroup.mem_centralizer_iff.mpr ?_⟩
      intro f hf
      have hmemN : f * x⁻¹ * f⁻¹ ∈ N :=
        (Subgroup.normal_subgroupOf_iff hNH).1 hN x⁻¹ f (N.inv_mem hxN) (fstar_le_group H hf)
      have hcN : x * f * x⁻¹ * f⁻¹ ∈ N := by
        have heq : x * f * x⁻¹ * f⁻¹ = x * (f * x⁻¹ * f⁻¹) := by group
        rw [heq]
        exact N.mul_mem hxN hmemN
      have hcF : x * f * x⁻¹ * f⁻¹ ∈ Fstar H :=
        (Fstar H).mul_mem (conj_mem_fstar (hNH hxN) hf) ((Fstar H).inv_mem hf)
      have hbot : x * f * x⁻¹ * f⁻¹ = 1 := by
        have hmem : x * f * x⁻¹ * f⁻¹ ∈ (⊥ : Subgroup G) := by
          rw [← hNF]
          exact Subgroup.mem_inf.mpr ⟨hcN, hcF⟩
        exact Subgroup.mem_bot.mp hmem
      have hxfeq : x * f = f * x := by
        calc x * f = (x * f * x⁻¹ * f⁻¹) * (f * x) := by group
          _ = f * x := by rw [hbot, one_mul]
      exact hxfeq.symm
    have hCbot' := inf_centralizer_fstar_eq_bot H hs hnab
    have hle : N ≤ (⊥ : Subgroup G) := hNC.trans (le_of_eq hCbot')
    exact le_bot_iff.mp hle
  · right
    have htop : N ⊓ Fstar H = Fstar H := by
      have h := Subgroup.map_subgroupOf_eq_of_le (inf_le_right : N ⊓ Fstar H ≤ Fstar H)
      rw [hCtop, Subgroup.map_top, Subgroup.range_subtype] at h
      exact h.symm
    intro f hf
    have : f ∈ N ⊓ Fstar H := by rw [htop]; exact hf
    exact (Subgroup.mem_inf.mp this).1

private theorem ne_bot_of_maxOver_eq_singleton_of_noncomm {H M A : Subgroup G}
    (hM : maxOver H A = {M})
    (hnab : ∃ a b : ↥(Fstar H), a * b ≠ b * a) : A ≠ ⊥ := by
  intro hAbot
  rw [hAbot] at hM
  obtain ⟨hMmax, -, hunique⟩ := isUniqueMaxOver_iff.mp hM
  obtain ⟨x, hxH, hxM⟩ := SetLike.exists_of_lt hMmax.1
  have hzx : Subgroup.zpowers x = H := by
    by_contra hne
    have hlt : Subgroup.zpowers x < H :=
      lt_of_le_of_ne (Subgroup.zpowers_le.mpr hxH) hne
    obtain ⟨N, hNmax, hNge⟩ := exists_isMaxSubgroupIn hlt
    have hNM : N = M := hunique N hNmax bot_le
    exact hxM (hNM ▸ hNge (Subgroup.mem_zpowers x))
  have hcommH : ∀ a b : ↥H, a * b = b * a := by
    intro a b
    have ha : (a : G) ∈ Subgroup.zpowers x := by rw [hzx]; exact a.2
    have hb : (b : G) ∈ Subgroup.zpowers x := by rw [hzx]; exact b.2
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp ha
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hb
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hi, ← hj]
    exact zpow_mul_comm x i j
  obtain ⟨a, b, hab⟩ := hnab
  have h := hcommH ⟨(a : G), fstar_le_group H a.2⟩ ⟨(b : G), fstar_le_group H b.2⟩
  apply hab
  apply Subtype.ext
  simpa using congrArg (fun t : ↥H => (t : G)) h

private theorem kerMOf_eq_bot_of_fstar_noncomm {H M A : Subgroup G}
    (hs : IsSimpleGroup ↥(Fstar H))
    (hnab : ∃ a b : ↥(Fstar H), a * b ≠ b * a)
    (h : Sec5Hyp H M A) (hM : maxOver H A = {M}) : kerMOf M H = ⊥ := by
  classical
  let Y : Subgroup G := kerMOf M H
  have hYH : Y ≤ H := kerMOf_le_group M H
  have hYM : Y ≤ M := kerMOf_le_left M H
  have hYn : (Y.subgroupOf H).Normal := normal_subgroupOf_kerMOf M H
  have hYlt : Y < H := by
    refine lt_of_le_of_ne hYH ?_
    intro hYeq
    exact h.not_le (hYeq ▸ hYM)
  obtain ⟨X, hX⟩ := exists_isMinNormalOver hYlt hYn
  obtain ⟨-, hQnil⟩ := five_four_three h hM hX
  have hYsol : Group.IsSolvable ↥Y := by
    haveI : Group.IsNilpotent ↥(pCore 2 ↥Y) := pCore_isNilpotent
    haveI : Group.IsNilpotent (↥Y ⧸ pCore 2 ↥Y) := hQnil
    refine Group.isSolvable_of_ker_le_range (pCore 2 ↥Y).subtype
      (QuotientGroup.mk' (pCore 2 ↥Y))
      (le_of_eq ((QuotientGroup.ker_mk' (pCore 2 ↥Y)).trans
        (Subgroup.range_subtype (pCore 2 ↥Y)).symm))
  rcases b5_eq_bot_or_fstar_le_of_normal hs hnab hYH hYn with hYbot | hFY
  · exact hYbot
  · exfalso
    haveI : Group.IsSolvable ↥Y := hYsol
    have hFsol : Group.IsSolvable ↥(Fstar H) :=
      Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hFY)
        (Subgroup.inclusion_injective hFY)
    haveI : IsSimpleGroup ↥(Fstar H) := hs
    haveI : Group.IsSolvable ↥(Fstar H) := hFsol
    obtain ⟨a, b, hab⟩ := hnab
    exact hab (IsSimpleGroup.comm_iff_isSolvable.mpr hFsol a b)

structure Asc80BSetup (H A M : Subgroup G) : Prop where
  sec5 : Sec5Hyp H M A
  maxOver_eq : maxOver H A = {M}
  le_of_lt : ∀ X : Subgroup G, A ≤ X → X < H → X ≤ M
  ne_bot : A ≠ ⊥
  kerMOf_eq_bot : kerMOf M H = ⊥
  not_fstar_le : ¬ Fstar H ≤ M
  eq_sup : H = Fstar H ⊔ A
  inf_centralizer : H ⊓ centralizer (Fstar H : Set G) = ⊥

theorem asc80BSetup {H A M : Subgroup G} (hs : IsSimpleGroup ↥(Fstar H))
    (hnab : ∃ a b : ↥(Fstar H), a * b ≠ b * a) (hAH : A ≤ H) (hA : IsElemAbelian 2 A)
    (hM : maxOver H A = {M}) : Asc80BSetup H A M := by
  obtain ⟨hMmax, hAM, hunique⟩ := isUniqueMaxOver_iff.mp hM
  have hsec5 : Sec5Hyp H M A := by
    refine ⟨hA, hAH, hAM, not_le_of_gt hMmax.1, ?_⟩
    obtain ⟨T, hT, hAT⟩ := exists_isSylowIn_ge 2 hAH hA.isPGroup
    have hTlt : T < H := by
      refine lt_of_le_of_ne hT.le ?_
      intro hTeq
      have hH2 : IsPGroup 2 H := hTeq ▸ hT.isPGroup
      have hF2 : IsPGroup 2 (Fstar H) :=
        (hH2.to_subgroup ((Fstar H).subgroupOf H)).of_equiv
          (Subgroup.subgroupOfEquivOfLe (fstar_le_group H))
      have hsol : Group.IsSolvable ↥(Fstar H) := by
        haveI : Group.IsNilpotent ↥(Fstar H) := IsPGroup.isNilpotent hF2
        exact IsNilpotent.to_isSolvable
      haveI : IsSimpleGroup ↥(Fstar H) := hs
      obtain ⟨a, b, hab⟩ := hnab
      exact hab (IsSimpleGroup.comm_iff_isSolvable.mpr hsol a b)
    have hTM : T ≤ M := le_of_lt_of_maxOver_eq_singleton hM hAT hTlt
    have hTodd : Odd (T.relIndex H) := by
      rw [← Nat.not_even_iff_odd]
      intro hev
      exact hT.not_dvd_relIndex (even_iff_two_dvd.mp hev)
    exact Odd.of_dvd_nat hTodd (Subgroup.relIndex_dvd_of_le_left H hTM)
  have hker : kerMOf M H = ⊥ := kerMOf_eq_bot_of_fstar_noncomm hs hnab hsec5 hM
  have hAne : A ≠ ⊥ := ne_bot_of_maxOver_eq_singleton_of_noncomm hM hnab
  have hnotF : ¬ Fstar H ≤ M := by
    intro hFM
    have hle : Fstar H ≤ kerMOf M H :=
      le_kerMOf_of_normal (fstar_le_group H) (normal_subgroupOf_fstar H) hFM
    rw [hker] at hle
    have hbot : Fstar H = ⊥ := le_bot_iff.mp hle
    obtain ⟨a, b, hab⟩ := hnab
    have ha : a = 1 := Subtype.ext (Subgroup.mem_bot.mp (hbot ▸ a.2))
    have hb : b = 1 := Subtype.ext (Subgroup.mem_bot.mp (hbot ▸ b.2))
    exact hab (by simp [ha, hb])
  have hmin : IsMinNormalOver H (kerMOf M H) (Fstar H) := by
    rw [hker]
    refine ⟨bot_lt_iff_ne_bot.mpr ?_, fstar_le_group H, normal_subgroupOf_fstar H, ?_⟩
    · intro hFbot
      obtain ⟨a, b, hab⟩ := hnab
      have ha : a = 1 := Subtype.ext (Subgroup.mem_bot.mp (hFbot ▸ a.2))
      have hb : b = 1 := Subtype.ext (Subgroup.mem_bot.mp (hFbot ▸ b.2))
      exact hab (by simp [ha, hb])
    · intro Z hZ hZF hZN
      rcases b5_eq_bot_or_fstar_le_of_normal hs hnab (hZF.trans (fstar_le_group H)) hZN with hb | hle
      · exact Or.inl hb
      · exact Or.inr (le_antisymm hZF hle)
  exact { sec5 := hsec5
          maxOver_eq := hM
          le_of_lt := fun X hAX hXH => le_of_lt_of_maxOver_eq_singleton hM hAX hXH
          ne_bot := hAne
          kerMOf_eq_bot := hker
          not_fstar_le := hnotF
          eq_sup := five_four_one hM hmin
          inf_centralizer := inf_centralizer_fstar_eq_bot H hs hnab }

theorem Asc80BSetup.maxOver_sylow {H A M : Subgroup G} (h : Asc80BSetup H A M)
    {T : Subgroup G} (hT : IsSylowIn 2 T H) (hAT : A ≤ T) : maxOver H T = {M} := by
  obtain ⟨hMmax, -, hunique⟩ := isUniqueMaxOver_iff.mp h.maxOver_eq
  have hTH : T ≠ H := by
    intro hTeq
    have hH2 : IsPGroup 2 H := hTeq ▸ hT.isPGroup
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hH2
    have hdiv : M.relIndex H ∣ Nat.card ↥H := Subgroup.relIndex_dvd_card M H
    rw [hn] at hdiv
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdiv
    have hk0 : k = 0 := by
      by_contra hkne
      have hev : Even (M.relIndex H) := by
        rw [hk]
        exact Nat.even_pow.mpr ⟨even_two, hkne⟩
      exact (Nat.not_even_iff_odd.mpr h.sec5.odd_relIndex) hev
    have hrel1 : M.relIndex H = 1 := by rw [hk, hk0, pow_zero]
    exact h.sec5.not_le ((Subgroup.relIndex_eq_one).1 hrel1)
  have hTlt : T < H := lt_of_le_of_ne hT.le hTH
  have hTM : T ≤ M := h.le_of_lt T hAT hTlt
  refine isUniqueMaxOver_iff.mpr ⟨hMmax, hTM, ?_⟩
  intro N hN hTN
  exact hunique N hN (hAT.trans hTN)

theorem Asc80BSetup.exists_maximal {H A M : Subgroup G} (h : Asc80BSetup H A M) :
    ∃ A' : Subgroup G, A ≤ A' ∧ A' ≤ H ∧ IsElemAbelian 2 A' ∧
      (∀ B : Subgroup G, A' ≤ B → B ≤ H → IsElemAbelian 2 B → B = A') ∧
      maxOver H A' = {M} := by
  classical
  let S : Set (Subgroup G) := {B | A ≤ B ∧ B ≤ H ∧ IsElemAbelian 2 B}
  have hSfin : S.Finite := Set.toFinite S
  have hSne : S.Nonempty := ⟨A, le_rfl, h.sec5.le_group, h.sec5.isElemAbelian⟩
  obtain ⟨A', hA'S, hA'max⟩ := hSfin.exists_maximal hSne
  have hHnc : ¬ IsMulCommutative ↥H := by
    intro hcomm
    have hHC : H ≤ Subgroup.centralizer (Fstar H : Set G) := by
      intro x hxH
      rw [Subgroup.mem_centralizer_iff]
      intro f hf
      exact congrArg (fun t : ↥H => (t : G))
        (hcomm.is_comm.comm ⟨f, fstar_le_group H hf⟩ ⟨x, hxH⟩)
    have hHbot : H = ⊥ := by
      have hle : H ≤ H ⊓ Subgroup.centralizer (Fstar H : Set G) := le_inf le_rfl hHC
      rw [h.inf_centralizer] at hle
      exact le_bot_iff.mp hle
    exact h.ne_bot (le_bot_iff.mp (hHbot ▸ h.sec5.le_group))
  have hA'lt : A' < H := by
    refine lt_of_le_of_ne hA'S.2.1 ?_
    intro hA'H
    exact hHnc (hA'H ▸ hA'S.2.2.1)
  have hA'M : A' ≤ M := h.le_of_lt A' hA'S.1 hA'lt
  have hMmax : IsMaxSubgroupIn H M := (isUniqueMaxOver_iff.mp h.maxOver_eq).1
  refine ⟨A', hA'S.1, hA'S.2.1, hA'S.2.2, ?_, ?_⟩
  · intro B hA'B hBH hB
    exact le_antisymm (hA'max ⟨hA'S.1.trans hA'B, hBH, hB⟩ hA'B) hA'B
  · ext N
    constructor
    · intro hN
      have hNA : N ∈ maxOver H A := ⟨hN.1, hA'S.1.trans hN.2⟩
      rw [h.maxOver_eq] at hNA
      exact hNA
    · intro hN
      rw [Set.mem_singleton_iff] at hN
      subst hN
      exact ⟨hMmax, hA'M⟩

@[expose] def Asc80NoUMax (P : ∀ (X : Type) [Group X], Prop) : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q] (L T : Subgroup Q), L.Normal → IsSimpleGroup ↥L →
    (∃ a b : ↥L, a * b ≠ b * a) → centralizer (L : Set Q) = ⊥ → P ↥L → IsSylowIn 2 T ⊤ →
    ¬ ∃ M : Subgroup Q, M < ⊤ ∧ ∀ X : Subgroup Q, T ≤ X → X < ⊤ → X ≤ M

theorem asc80ThmBCase_of_noUMax {P : ∀ (X : Type) [Group X], Prop}
    (hP : ∀ (X Y : Type) [Group X] [Group Y], Nonempty (X ≃* Y) → P X → P Y)
    (h : Asc80NoUMax P) : Asc80ThmBCase P := by
  intro G _ _ H A M hs hnab hPfam hAH hA hM
  obtain ⟨T, hT, hAT⟩ := exists_isSylowIn_ge 2 hAH hA.isPGroup
  let L : Subgroup ↥H := (Fstar H).subgroupOf H
  let T' : Subgroup ↥H := T.subgroupOf H
  let e : ↥L ≃* ↥(Fstar H) := Subgroup.subgroupOfEquivOfLe (fstar_le_group H)
  have hsetup := asc80BSetup hs hnab hAH hA hM
  have hMmax : IsMaxSubgroupIn H M := (isUniqueMaxOver_iff.mp hM).1
  exfalso
  have hLnorm : L.Normal := by
    simpa [L] using normal_subgroupOf_fstar H
  have hLsimple : IsSimpleGroup ↥L := e.isSimpleGroup
  have hLnab : ∃ a b : ↥L, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnab
    refine ⟨e.symm a, e.symm b, ?_⟩
    intro hcomm
    apply hab
    have := congrArg e hcomm
    simpa using this
  have hCentL : Subgroup.centralizer (L : Set ↥H) = ⊥ := by
    have heq : Subgroup.centralizer (L : Set ↥H) =
        (H ⊓ Subgroup.centralizer (Fstar H : Set G)).subgroupOf H := by
      ext x
      rw [Subgroup.mem_centralizer_iff]
      constructor
      · intro hx
        rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
        refine ⟨x.2, ?_⟩
        rw [Subgroup.mem_centralizer_iff]
        intro f hf
        let fH : ↥H := ⟨f, fstar_le_group H hf⟩
        have hfL : fH ∈ L := by
          change (fH : G) ∈ Fstar H
          exact hf
        have hcomm := hx fH hfL
        exact congrArg (fun t : ↥H => (t : G)) hcomm
      · intro hx y hy
        have hxcent : (x : G) ∈ Subgroup.centralizer (Fstar H : Set G) :=
          (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hx)).2
        apply Subtype.ext
        have hyF : (y : G) ∈ Fstar H := by
          change y ∈ (Fstar H).subgroupOf H at hy
          exact Subgroup.mem_subgroupOf.mp hy
        exact (Subgroup.mem_centralizer_iff.mp hxcent) (y : G) hyF
    rw [heq, hsetup.inf_centralizer]
    simp
  have hPL : P ↥L := hP ↥(Fstar H) ↥L ⟨e.symm⟩ hPfam
  have hT'syl : IsSylowIn 2 T' ⊤ := by
    refine ⟨le_top, ?_, ?_⟩
    · exact hT.isPGroup.of_equiv (Subgroup.subgroupOfEquivOfLe hT.le).symm
    · rw [Subgroup.relIndex_top_right]
      simpa [Subgroup.relIndex] using hT.not_dvd_relIndex
  have hMlt : M.subgroupOf H < ⊤ :=
    (Subgroup.map_subtype_lt_map_subtype (G' := H) (H := M.subgroupOf H) (K := ⊤)).mp (by
      rw [Subgroup.map_subgroupOf_eq_of_le hMmax.le, Subgroup.map_top,
        Subgroup.range_subtype]
      exact hMmax.1)
  exact (h ↥H L T' hLnorm hLsimple hLnab hCentL hPL hT'syl)
    ⟨M.subgroupOf H, hMlt, fun X hT'X hXlt => by
      let X' : Subgroup G := X.map H.subtype
      have hTX' : T ≤ X' := by
        calc T = (T.subgroupOf H).map H.subtype :=
              (Subgroup.map_subgroupOf_eq_of_le hT.le).symm
          _ ≤ X.map H.subtype := Subgroup.map_mono hT'X
      have hX'lt : X' < H := by
        have h := (Subgroup.map_subtype_lt_map_subtype (G' := H) (H := X) (K := ⊤)).mpr hXlt
        simpa only [X', Subgroup.map_top, Subgroup.range_subtype] using h
      have hX'M : X' ≤ M := hsetup.le_of_lt X' (hAT.trans hTX') hX'lt
      intro x hx
      rw [Subgroup.mem_subgroupOf]
      exact hX'M (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩)⟩

end CFSG.LocalAnalysis.WeakClosure81

end
