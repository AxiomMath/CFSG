module

public import CFSG.RankThree.PartOne.KS.Plane
public import CFSG.RankThree.PartOne.KS.Combine
public import CFSG.RankThree.PartOne.KS.Arith
public import CFSG.RankThree.Native.SuzFiveCentralizers
public import CFSG.Sporadic.SuzOddCore.SmallAut

public section

namespace CFSG.RankThree.PartOne

open Subgroup CFSG CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory CFSG.Sporadic.SmallOddCore
open CFSG.Sporadic.SuzOddCore CFSG.RankThree.Native
open CFSG.Blueprint.NativeSporadic (Carrier)
open scoped Pointwise

theorem suz_autModel : AutModel suzM suzT where
  le := suzM_le_suzT
  conj_mem := fun _ hx _ hp => suzT_conj_mem_suzM hx hp
  surj := fun α => by
    obtain ⟨t, ht⟩ := suzConjT_bijective.2 α
    refine ⟨t, t.2, fun p => ?_⟩
    have := congrArg (fun β : MulAut suzM => ((β p : suzM) : Equiv.Perm (Fin 1782))) ht
    simpa [suzConjT_apply] using this.symm
  inj := fun x hx hc => by
    have h1 : suzConjT ⟨x, hx⟩ = suzConjT 1 := by
      refine MulEquiv.ext fun m => Subtype.ext ?_
      have h2 : x * (m : Equiv.Perm (Fin 1782)) * x⁻¹ = (m : Equiv.Perm (Fin 1782)) := by
        rw [hc m m.2]
        group
      rw [suzConjT_apply, map_one, MulAut.one_apply]
      exact h2
    exact congrArg Subtype.val (suzConjT_injective h1)

theorem suz_card_le : Nat.card suzT ≤ 2 * Nat.card suzM := by
  rw [suzT_card, suzM_card]


theorem suz_D_normalized (i : Fin 6) :
    suzT ⊓ centralizer ({suzFiveLine i} : Set (Equiv.Perm (Fin 1782))) ≤
      normalizer (suzFiveD i : Set (Equiv.Perm (Fin 1782))) := by
  obtain ⟨-, -, hCD, -, -⟩ := R3E_Suz_full_five_centralizer_structures
  rw [inf_comm, ← (hCD i).1]
  exact le_normalizer_commutator_self _

theorem suz_D_le_centralizer (i : Fin 6) :
    suzFiveD i ≤ centralizer ({suzFiveLine i} : Set (Equiv.Perm (Fin 1782))) := by
  obtain ⟨-, -, hCD, -, -⟩ := R3E_Suz_full_five_centralizer_structures
  have h1 : suzFiveD i ≤ suzFiveC i := commutator_self_le _
  rw [(hCD i).1] at h1
  exact h1.trans inf_le_left

theorem suz_D_quasisimple (i : Fin 6) : IsQuasisimple (suzFiveD i) := by
  obtain ⟨-, -, hCD, -, -⟩ := R3E_Suz_full_five_centralizer_structures
  obtain ⟨-, hsimple, ⟨g, hg, h, hh, hne⟩, -⟩ := hCD i
  have := hsimple
  exact isQuasisimple_of_isSimpleGroup ⟨⟨g, hg⟩, ⟨h, hh⟩, fun e => hne (congrArg Subtype.val e)⟩

theorem suz_core_bot_good (i : Fin 6) (hi : i.val = 0 ∨ i.val = 3 ∨ i.val = 4)
    (B : Subgroup (Equiv.Perm (Fin 1782))) (hPB : suzM ≤ B) (hBR : B ≤ suzT) :
    inSubgroup (aschbacherSolvableCore 5)
      (B ⊓ centralizer ({suzFiveLine i} : Set (Equiv.Perm (Fin 1782)))) = ⊥ := by
  obtain ⟨-, -, hCD, hgood, -⟩ := R3E_Suz_full_five_centralizer_structures
  obtain ⟨-, -, hcent, hcard5⟩ := hgood i hi
  refine line_core_bot_of_normal_component Nat.prime_five hPB hBR (hCD i).2.2.2
    (suz_D_quasisimple i) (suz_D_le_centralizer i) (suz_D_normalized i) ?_
  have h1 : suzT ⊓ centralizer ({suzFiveLine i} : Set (Equiv.Perm (Fin 1782))) ⊓
      centralizer (suzFiveD i : Set (Equiv.Perm (Fin 1782))) = zpowers (suzFiveLine i) := by
    rw [inf_comm suzT, ← (hCD i).1, inf_comm]
    exact hcent
  rw [h1]
  exact IsPGroup.of_card (n := 1) (by rw [hcard5, pow_one])

theorem suz_core_card_le (i : Fin 6) (hi : i.val = 1 ∨ i.val = 2 ∨ i.val = 5)
    (B : Subgroup (Equiv.Perm (Fin 1782))) (hPB : suzM ≤ B) (hBR : B ≤ suzT) :
    Nat.card (inSubgroup (aschbacherSolvableCore 5)
      (B ⊓ centralizer ({suzFiveLine i} : Set (Equiv.Perm (Fin 1782))))) ≤ 2 := by
  obtain ⟨-, -, hCD, -, hbad⟩ := R3E_Suz_full_five_centralizer_structures
  obtain ⟨-, -, hcard10⟩ := hbad i hi
  have hle := line_core_le_of_normal_component Nat.prime_five hPB hBR (hCD i).2.2.2
    (suz_D_quasisimple i) (suz_D_le_centralizer i) (suz_D_normalized i)
  have h1 : suzT ⊓ centralizer ({suzFiveLine i} : Set (Equiv.Perm (Fin 1782))) ⊓
      centralizer (suzFiveD i : Set (Equiv.Perm (Fin 1782))) =
      centralizer (suzFiveD i : Set (Equiv.Perm (Fin 1782))) ⊓ suzFiveC i := by
    rw [inf_comm suzT, ← (hCD i).1, inf_comm]
  rw [h1] at hle
  have hd : Nat.card (inSubgroup (aschbacherSolvableCore 5)
      (B ⊓ centralizer ({suzFiveLine i} : Set (Equiv.Perm (Fin 1782))))) ∣ 10 := by
    have := Subgroup.card_dvd_of_le hle
    rwa [hcard10] at this
  have hnd := not_dvd_card_inSubgroup_aschbacherSolvableCore Nat.prime_five
    (B ⊓ centralizer ({suzFiveLine i} : Set (Equiv.Perm (Fin 1782))))
  have hcop : Nat.Coprime (Nat.card (inSubgroup (aschbacherSolvableCore 5)
      (B ⊓ centralizer ({suzFiveLine i} : Set (Equiv.Perm (Fin 1782)))))) 5 :=
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_five).2 hnd).symm
  have h2 := hcop.dvd_of_dvd_mul_right (show _ ∣ 2 * 5 by simpa using hd)
  exact Nat.le_of_dvd (by norm_num) h2

theorem suz_core_card_le_all (i : Fin 6) (B : Subgroup (Equiv.Perm (Fin 1782)))
    (hPB : suzM ≤ B) (hBR : B ≤ suzT) :
    Nat.card (inSubgroup (aschbacherSolvableCore 5)
      (B ⊓ centralizer ({suzFiveLine i} : Set (Equiv.Perm (Fin 1782))))) ≤ 2 := by
  by_cases hg : i.val = 0 ∨ i.val = 3 ∨ i.val = 4
  · rw [suz_core_bot_good i hg B hPB hBR, Subgroup.card_bot]
    norm_num
  · have : i.val = 1 ∨ i.val = 2 ∨ i.val = 5 := by
      have := i.2
      omega
    exact suz_core_card_le i this B hPB hBR


theorem suz_Q_facts :
    suzFiveQ ≤ suzM ∧ Nat.card suzFiveQ = 5 ^ 2 ∧
      (∃ S : Sylow 5 suzM, (S : Subgroup suzM) = suzFiveQ.subgroupOf suzM) ∧
      {H : Subgroup (Equiv.Perm (Fin 1782)) | H ≤ suzFiveQ ∧ Nat.card H = 5} =
        Set.range (fun i : Fin 6 => zpowers (suzFiveLine i)) ∧
      suzFiveLine 0 ∈ suzFiveQ ∧ suzFiveLine 0 ≠ 1 := by
  obtain ⟨⟨hQM, -, -, hQcard, hQsyl⟩, ⟨hlines, -⟩, -, hgood, -⟩ :=
    R3E_Suz_full_five_centralizer_structures
  have hx0Q : suzFiveLine 0 ∈ suzFiveQ := by
    have : zpowers (suzFiveLine 0) ∈
        {H : Subgroup (Equiv.Perm (Fin 1782)) | H ≤ suzFiveQ ∧ Nat.card H = 5} := by
      rw [hlines]
      exact ⟨0, rfl⟩
    exact this.1 (mem_zpowers _)
  have hx01 : suzFiveLine 0 ≠ 1 := by
    intro h
    have := (hgood 0 (Or.inl rfl)).2.2.2
    rw [h, zpowers_one_eq_bot, Subgroup.card_bot] at this
    omega
  exact ⟨hQM, by rw [hQcard]; norm_num, hQsyl, hlines, hx0Q, hx01⟩

theorem almostSimplePlaneOdd_five_Suz : AlmostSimplePlaneOdd 5 (Carrier .Suz) := by
  intro H _ _ K _ hK hC E hE hEcard t htE ht1
  obtain ⟨e⟩ := hK
  obtain ⟨hQM, hQcard, hQsyl, hlines, hx0Q, hx01⟩ := suz_Q_facts
  have hbot := localCoreProduct_eq_bot_of_model_good_bound (P := suzM) (R := suzT)
    (Q := suzFiveQ) suz_autModel suz_card_le Nat.prime_five (by norm_num) hQsyl hQM hQcard
    hx0Q hx01 (fun B hPB hBR => suz_core_bot_good 0 (Or.inl rfl) B hPB hBR)
    (fun B hPB hBR => core_card_le_of_lines Nat.prime_five hQsyl hlines
      (fun i B' hPB' hBR' => suz_core_card_le_all i B' hPB' hBR') B hPB hBR)
    K (e.trans suzEquivM) hC hE hEcard htE ht1
  rw [hbot, Subgroup.card_bot]
  omega

theorem card_core_centralizer_le_of_model {M : Type*} [Group M] [Finite M] {P R : Subgroup M}
    (h : AutModel P R) (hidx : Nat.card R ≤ 2 * Nat.card P) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {k : ℕ} (hline : ∀ B : Subgroup M, P ≤ B → B ≤ R → ∀ y ∈ P, orderOf y = p →
      Nat.card (inSubgroup (aschbacherSolvableCore p) (B ⊓ centralizer ({y} : Set M))) ≤ k)
    {X : Type*} [Group X] [Finite X] (S : Subgroup X) [S.Normal] (θ : S ≃* P)
    (hC : centralizer (S : Set X) = ⊥) (x : X) (hx : orderOf x = p) :
    Nat.card (inSubgroup (aschbacherSolvableCore p) (centralizer ({x} : Set X))) ≤ k := by
  obtain ⟨hyP, B, hPB, hBR, hcard⟩ := card_core_centralizer_eq_of_model h hidx hp hp2 S θ hC x hx
  have hord : orderOf (h.embed S θ x) = p := by
    rw [orderOf_injective _ (h.embed_injective S θ hC), hx]
  rw [hcard]
  exact hline B hPB hBR _ hyP hord

theorem R3E_Suz_almost_simple_five_plane_local_core_product_trivial {H : Type} [Group H]
    [Finite H] (K : Subgroup H) [K.Normal] (hK : Nonempty (K ≃* Carrier .Suz))
    (hC : centralizer (K : Set H) = ⊥) :
    (∀ x : H, orderOf x = 5 →
      Nat.card (inSubgroup (aschbacherSolvableCore 5) (centralizer ({x} : Set H))) ≤ 2) ∧
    ∀ E : Subgroup H, IsElementaryAbelian 5 E → Nat.card E = 5 ^ 2 → ∀ t ∈ E, t ≠ 1 →
      ⁅inSubgroup (aschbacherSolvableCore 5) (centralizer ({t} : Set H)), E⁆ = ⊥ ∧
        thetaT 5 E = ⊥ ∧
        ((⁅inSubgroup (aschbacherSolvableCore 5) (centralizer ({t} : Set H)), E⁆ : Subgroup H) :
          Set H) * (thetaT 5 E : Set H) = 1 := by
  obtain ⟨e⟩ := hK
  obtain ⟨hQM, hQcard, hQsyl, hlines, hx0Q, hx01⟩ := suz_Q_facts
  have hbound := fun (B : Subgroup (Equiv.Perm (Fin 1782))) (hPB : suzM ≤ B) (hBR : B ≤ suzT) =>
    core_card_le_of_lines Nat.prime_five hQsyl hlines
      (fun i B' hPB' hBR' => suz_core_card_le_all i B' hPB' hBR') B hPB hBR
  refine ⟨fun x hx => card_core_centralizer_le_of_model suz_autModel suz_card_le Nat.prime_five
    (by norm_num) hbound K (e.trans suzEquivM) hC x hx, fun E hE hEcard t htE ht1 => ?_⟩
  have hbot := localCoreProduct_eq_bot_of_model_good_bound (P := suzM) (R := suzT)
    (Q := suzFiveQ) suz_autModel suz_card_le Nat.prime_five (by norm_num) hQsyl hQM hQcard
    hx0Q hx01 (fun B hPB hBR => suz_core_bot_good 0 (Or.inl rfl) B hPB hBR) hbound
    K (e.trans suzEquivM) hC hE hEcard htE ht1
  rw [localCoreProduct] at hbot
  have h1 := eq_bot_iff.2 (le_sup_left.trans hbot.le)
  have h2 := eq_bot_iff.2 (le_sup_right.trans hbot.le)
  refine ⟨h1, h2, ?_⟩
  rw [h1, h2]
  simp
  exact Set.singleton_one

theorem sporadicPlaneOdd_Suz : SporadicPlaneOdd (Carrier .Suz) := by
  refine sporadicPlaneOdd_of_almostSimple {5} (fun q hq _ => ?_) ?_
  · rw [Finset.mem_singleton.mp hq]
    exact almostSimplePlaneOdd_five_Suz
  · intro T _ _ _ hnab hTA p hp hp3 hpS
    obtain ⟨e⟩ := hTA
    have hp5 : p ≠ 5 := fun h => hpS (by simp [h])
    have hcard : Nat.card (MulAut T) = 2 ^ 14 * 3 ^ 7 * 5 ^ 2 * 1001 := by
      rw [Nat.card_congr (MulAut.congr (e.trans suzEquivM)).toEquiv, card_mulAut_suzM]
      norm_num
    rw [hcard]
    exact not_sq_dvd_mul_of_coprime (B := 31) hp (coprime_two_three_five_pow hp hp3 hp5 14 7 2)
      (by norm_num) (by decide) (by norm_num)

end CFSG.RankThree.PartOne
