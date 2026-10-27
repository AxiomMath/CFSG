module

import CFSG.RankThree.PartTwo.Sec14.Item148HJProofLB
import CFSG.RankThree.PartTwo.Sec14.Concl143Std
import CFSG.RankThree.PartTwo.Sec6.Item68
public import CFSG.RankThree.PartTwo.Sec14.Item148HJProofPoint

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped commutatorElement Pointwise

namespace Item148PtRes

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem exists_mul_of_mem_sup {N X : Subgroup G} (hXN : X ≤ Subgroup.normalizer (N : Set G))
    {m : G} (hm : m ∈ N ⊔ X) : ∃ n ∈ N, ∃ x ∈ X, m = n * x := by
  have hm' : m ∈ ((N : Set G) * (X : Set G)) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left N X hXN]
    exact hm
  obtain ⟨n, hn, x, hx, rfl⟩ := hm'
  exact ⟨n, hn, x, hx, rfl⟩

omit [Finite G] in
theorem commutator_mem_of_mem_sup {N X : Subgroup G} {u : G}
    (hXN : X ≤ Subgroup.normalizer (N : Set G)) (huN : u ∈ Subgroup.normalizer (N : Set G))
    (hX : ∀ x ∈ X, ⁅x, u⁆ ∈ N) {m : G} (hm : m ∈ N ⊔ X) : ⁅m, u⁆ ∈ N := by
  obtain ⟨n, hn, x, hx, rfl⟩ := exists_mul_of_mem_sup hXN hm
  have h1 : ⁅n * x, u⁆ = n * ⁅x, u⁆ * (u * n⁻¹ * u⁻¹) := by
    simp only [commutatorElement_def]
    group
  rw [h1]
  exact mul_mem (mul_mem hn (hX x hx)) ((Subgroup.mem_normalizer_iff.mp huN _).mp (inv_mem hn))

omit [Finite G] in
theorem exists_pow_eq_mul {N X : Subgroup G} (hXN : X ≤ Subgroup.normalizer (N : Set G))
    {n x : G} (hn : n ∈ N) (hx : x ∈ X) : ∀ k : ℕ, ∃ n' ∈ N, (n * x) ^ k = n' * x ^ k
  | 0 => ⟨1, one_mem _, by simp⟩
  | k + 1 => by
    obtain ⟨n', hn', h⟩ := exists_pow_eq_mul hXN hn hx k
    refine ⟨n' * (x ^ k * n * (x ^ k)⁻¹), mul_mem hn' ?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.mp (hXN (pow_mem hx k)) n).mp hn
    · rw [pow_succ, h, pow_succ]
      group

theorem inf_le_theta_of_quasisimple {N X : Subgroup G}
    (hXN : X ≤ Subgroup.normalizer (N : Set G)) (hN3 : Nat.Coprime 3 (Nat.card N))
    (hq : IsQuasisimple (↥X ⧸ aschbacherSolvableCore 3 ↥X))
    (hZ : Nat.card (Subgroup.center (↥X ⧸ aschbacherSolvableCore 3 ↥X)) = 3) :
    N ⊓ X ≤ inSubgroup (aschbacherSolvableCore 3) X := by
  set M : Subgroup ↥X := N.subgroupOf X with hMdef
  have hMn : M.Normal := by
    refine ⟨fun a ha g => ?_⟩
    rw [hMdef, Subgroup.mem_subgroupOf] at ha ⊢
    exact (Subgroup.mem_normalizer_iff.mp (hXN g.2) a).mp ha
  set P := M.map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X)) with hP
  have hPn : P.Normal := hMn.map _ (QuotientGroup.mk'_surjective _)
  have hP3 : ¬ 3 ∣ Nat.card P := by
    intro h3
    have h1 := h3.trans (Subgroup.card_map_dvd M _)
    have h2 : Nat.card M ∣ Nat.card N := by
      rw [hMdef, ← Subgroup.card_map_of_injective X.subtype_injective,
        Subgroup.subgroupOf_map_subtype]
      exact Subgroup.card_dvd_of_le inf_le_left
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hN3 (h1.trans h2)
  have hPb : P = ⊥ := Item148HJ.eq_bot_of_normal_of_quasisimple hq hZ hPn hP3
  intro y hy
  obtain ⟨hyN, hyX⟩ := Subgroup.mem_inf.mp hy
  have hmem : (⟨y, hyX⟩ : ↥X) ∈ aschbacherSolvableCore 3 ↥X := by
    have h1 : QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X) (⟨y, hyX⟩ : ↥X) ∈ P :=
      ⟨⟨y, hyX⟩, Subgroup.mem_subgroupOf.mpr hyN, rfl⟩
    rw [hPb, Subgroup.mem_bot] at h1
    exact (QuotientGroup.eq_one_iff _).mp h1
  exact ⟨⟨y, hyX⟩, hmem, rfl⟩

theorem mem_normalizer_of_le_sup {b g : G} {X : Subgroup G} (hX : X ∈ thetaComponentsAt 3 b)
    (h3 : 3 ∣ Nat.card X) (hg : g ∈ Subgroup.centralizer ({b} : Set G))
    (hgN : g ∈ Subgroup.normalizer
      ((pPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G)) ⊔ X : Subgroup G) : Set G)) :
    g ∈ Subgroup.normalizer (X : Set G) := by
  set Cb := Subgroup.centralizer ({b} : Set G) with hCb
  set N := pPrimeCoreOf 3 Cb with hN
  have hCbN : Cb ≤ Subgroup.normalizer (N : Set G) := le_normalizer_pPrimeCoreOf 3 Cb
  have hN3 : Nat.Coprime 3 (Nat.card N) := coprime_card_pPrimeCoreOf 3 Cb
  have hXCb : X ≤ Cb := le_centralizer_of_mem_thetaComponentsAt hX
  have hXN : X ≤ Subgroup.normalizer (N : Set G) := hXCb.trans hCbN
  set P := X.map (MulAut.conj g).toMonoidHom with hP
  have hPm : P ∈ thetaComponentsAt 3 b := Sec6.map_conj_mem_thetaComponentsAt hg hX
  by_contra hgX
  have hne : X ≠ P := Sec6.ne_map_conj_of_not_mem_normalizer hgX
  have hcomm : ⁅X, P⁆ ≤ N :=
    (Sec6.commutator_le_theta_of_ne_mem_thetaComponentsAt hX hPm hne).trans
      (inSubgroup_theta_le_pPrimeCoreOf Cb)
  have hPCb : P ≤ Cb := le_centralizer_of_mem_thetaComponentsAt hPm
  have hPle : P ≤ N ⊔ X := by
    rintro _ ⟨x, hx, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hgN x).mp (Subgroup.mem_sup_right hx)
  have hPN : P ≤ N := by
    have hPp : Group.IsPerfect ↥P := Sec6.isPerfect_of_mem_thetaComponentsAt hPm
    rw [← (Subgroup.isPerfect_iff).mp hPp, Subgroup.commutator_le]
    intro p₁ hp₁ p₂ hp₂
    obtain ⟨n, hn, x, hx, rfl⟩ := exists_mul_of_mem_sup hXN (hPle hp₂)
    have h1 : ⁅p₁, n * x⁆ = ⁅p₁, n⁆ * (n * ⁅p₁, x⁆ * n⁻¹) := by
      simp only [commutatorElement_def]
      group
    have h2 : ⁅p₁, n⁆ ∈ N := by
      rw [commutatorElement_def]
      exact mul_mem ((Subgroup.mem_normalizer_iff.mp (hCbN (hPCb hp₁)) n).mp hn) (inv_mem hn)
    have h3' : ⁅p₁, x⁆ ∈ N := by
      have h4 : ⁅x, p₁⁆ ∈ N := hcomm (Subgroup.commutator_mem_commutator hx hp₁)
      have h5 : ⁅p₁, x⁆ = ⁅x, p₁⁆⁻¹ := by
        simp only [commutatorElement_def]
        group
      rw [h5]
      exact inv_mem h4
    rw [h1]
    exact mul_mem h2 (mul_mem (mul_mem hn h3') (inv_mem hn))
  have hcard : Nat.card P = Nat.card X := by
    rw [hP, Subgroup.card_map_of_injective (MulAut.conj g).injective]
  have h3P : 3 ∣ Nat.card N := (hcard ▸ h3).trans (Subgroup.card_dvd_of_le hPN)
  exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hN3 h3P

theorem exists_mem_not_mem_zpowers {A B : Subgroup G} (hA : Nat.card A = 27)
    (hA3 : ∀ a ∈ A, a ^ 3 = 1) (hB : IsHyperplane A B) {b : G} (hbA : b ∈ A) :
    ∃ u ∈ B, u ∉ Subgroup.zpowers b := by
  by_contra hall
  push Not at hall
  have hle : B ≤ Subgroup.zpowers b := fun u hu => hall u hu
  have hB9 : Nat.card B = 9 := by
    have := hB.2
    omega
  have hb3 : Nat.card (Subgroup.zpowers b) ≤ 3 := by
    rw [Nat.card_zpowers]
    exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one (hA3 b hbA))
  have := Subgroup.card_le_of_le hle
  omega

theorem le_pPrimeCoreOf_of_trivial_on {Y Cb M M₀ R Q : Subgroup G} {u : G} (hu3 : u ^ 3 = 1)
    (hNM : pPrimeCoreOf 3 Cb ≤ M) (hMM₀ : M ≤ M₀) (hM₀Cb : M₀ ≤ Cb)
    (hM₀M : M₀ ≤ Subgroup.normalizer (M : Set G))
    (hCbM₀ : Cb ≤ Subgroup.normalizer (M₀ : Set G))
    (huM : u ∈ Subgroup.normalizer (M : Set G)) (huY : u ∈ Subgroup.normalizer (Y : Set G))
    (huCb : u ∈ Cb) (hMu : ∀ m ∈ M, ⁅m, u⁆ ∈ pPrimeCoreOf 3 Cb)
    (hR : Y ⊓ Cb ⊓ Subgroup.centralizer ({u} : Set G) ≤ Subgroup.normalizer (R : Set G))
    (hR3 : Nat.Coprime 3 (Nat.card R)) (hQR : Q ≤ R) (hQ : Q ≤ Y ⊓ Cb) (hQM : Q ≤ M) :
    Q ≤ pPrimeCoreOf 3 (Y ⊓ Cb) := by
  set N := pPrimeCoreOf 3 Cb with hN
  have hCbN : Cb ≤ Subgroup.normalizer (N : Set G) := le_normalizer_pPrimeCoreOf 3 Cb
  have hN3 : Nat.Coprime 3 (Nat.card N) := coprime_card_pPrimeCoreOf 3 Cb
  have hMCb : M ≤ Cb := hMM₀.trans hM₀Cb
  set J := M ⊓ Subgroup.centralizer ({u} : Set G) with hJ
  have hNJ : N ⊔ J = M := by
    apply le_antisymm (sup_le hNM inf_le_left)
    intro m hm
    obtain ⟨c', hc'M, hc'u, hc'm⟩ := Item148HJ.exists_commute_of_commutator_mem hu3 hNM
      (hMCb.trans hCbN) (hCbN huCb) ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hN3) hm
      (hMu m hm)
    have hc'J : c' ∈ J :=
      Subgroup.mem_inf.mpr ⟨hc'M, Subgroup.mem_centralizer_singleton_iff.mpr hc'u⟩
    have hm' : m = c' * (c'⁻¹ * m) := by group
    rw [hm', sup_comm]
    exact mul_mem (Subgroup.mem_sup_left hc'J) (Subgroup.mem_sup_right hc'm)
  set C'' := M ⊔ Subgroup.zpowers u with hC''
  have hC''Cb : C'' ≤ Cb := sup_le hMCb (Subgroup.zpowers_le.mpr huCb)
  have huC'' : u ∈ C'' := Subgroup.mem_sup_right (Subgroup.mem_zpowers u)
  have hC''N : C'' ≤ Subgroup.normalizer ((N ⊔ J : Subgroup G) : Set G) := by
    rw [hNJ]
    exact sup_le Subgroup.le_normalizer (Subgroup.zpowers_le.mpr huM)
  have hR' : Y ⊓ C'' ⊓ Subgroup.centralizer ({u} : Set G) ≤ Subgroup.normalizer (R : Set G) :=
    le_trans (inf_le_inf_right _ (inf_le_inf_left _ hC''Cb)) hR
  have hQC'' : Q ≤ Y ⊓ C'' := le_inf (hQ.trans inf_le_left) (hQM.trans le_sup_left)
  have hQNJ : Q ≤ N ⊔ J := by
    rw [hNJ]
    exact hQM
  have hT := Item148HJ.le_pPrimeCoreOf_of_coprime hu3 (hNM.trans le_sup_left) hN3
    (hC''Cb.trans hCbN) hC''N huY huC'' (inf_le_left.trans le_sup_left) inf_le_right hR' hR3 hQR
    hQC'' hQNJ
  set T := pPrimeCoreOf 3 (Y ⊓ C'') with hTdef
  have h1 : T ⊓ (Y ⊓ M) ≤ pPrimeCoreOf 3 (Y ⊓ M) := by
    refine le_pPrimeCoreOf inf_le_right ?_ ?_
    · refine Late.le_normalizer_inf ?_ Subgroup.le_normalizer
      exact (inf_le_inf_left _ le_sup_left).trans (le_normalizer_pPrimeCoreOf 3 (Y ⊓ C''))
    · exact Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_left)
        (coprime_card_pPrimeCoreOf 3 _)
  have hYM : Y ⊓ M₀ ≤ Subgroup.normalizer ((Y ⊓ M : Subgroup G) : Set G) :=
    Late.le_normalizer_inf (inf_le_left.trans Subgroup.le_normalizer) (inf_le_right.trans hM₀M)
  have h2 : pPrimeCoreOf 3 (Y ⊓ M) ≤ pPrimeCoreOf 3 (Y ⊓ M₀) :=
    le_pPrimeCoreOf ((pPrimeCoreOf_le 3 _).trans (inf_le_inf_left _ hMM₀))
      (hYM.trans (normalizer_le_normalizer_pPrimeCoreOf 3 _)) (coprime_card_pPrimeCoreOf 3 _)
  have hYM₀ : Y ⊓ Cb ≤ Subgroup.normalizer ((Y ⊓ M₀ : Subgroup G) : Set G) :=
    Late.le_normalizer_inf (inf_le_left.trans Subgroup.le_normalizer) (inf_le_right.trans hCbM₀)
  have h3 : pPrimeCoreOf 3 (Y ⊓ M₀) ≤ pPrimeCoreOf 3 (Y ⊓ Cb) :=
    le_pPrimeCoreOf ((pPrimeCoreOf_le 3 _).trans (inf_le_inf_left _ hM₀Cb))
      (hYM₀.trans (normalizer_le_normalizer_pPrimeCoreOf 3 _)) (coprime_card_pPrimeCoreOf 3 _)
  exact (le_inf hT (le_inf (hQ.trans inf_le_left) hQM)).trans (h1.trans (h2.trans h3))

theorem ncard_subgroups_card_three_le {A : Subgroup G} (hA : Nat.card A = 27) :
    {F : Subgroup G | F ≤ A ∧ Nat.card F = 3}.ncard ≤ 13 := by
  classical
  have : Fintype G := Fintype.ofFinite G
  have : Finite (Subgroup G) :=
    Finite.of_injective (fun H : Subgroup G => (H : Set G)) SetLike.coe_injective
  have : Fintype (Subgroup G) := Fintype.ofFinite _
  set Ts : Finset (Subgroup G) :=
    Finset.univ.filter (fun F : Subgroup G => F ≤ A ∧ Nat.card F = 3) with hTs
  have hTeq : {F : Subgroup G | F ≤ A ∧ Nat.card F = 3} = (Ts : Set (Subgroup G)) := by
    ext F
    simp [hTs]
  have hcardS : ∀ S : Subgroup G, (Finset.univ.filter (fun x : G => x ∈ S)).card =
      Nat.card S := fun S => by
    rw [Nat.card_eq_fintype_card, ← Fintype.card_subtype]
  set P : Finset G := (Finset.univ.filter (fun x : G => x ∈ A)).erase 1 with hP
  have hPcard : P.card = 26 := by
    rw [hP, Finset.card_erase_of_mem (by simp [one_mem]), hcardS, hA]
  set f : Subgroup G → Finset G := fun F => (Finset.univ.filter (fun x : G => x ∈ F)).erase 1
    with hf
  have hfcard : ∀ F ∈ Ts, (f F).card = 2 := by
    intro F hF
    obtain ⟨-, h3⟩ := (Finset.mem_filter.mp hF).2
    rw [hf, Finset.card_erase_of_mem (by simp [one_mem]), hcardS, h3]
  have hdisj : (Ts : Set (Subgroup G)).PairwiseDisjoint f := by
    intro F hF F' hF' hne
    obtain ⟨-, h3⟩ := (Finset.mem_filter.mp hF).2
    obtain ⟨-, h3'⟩ := (Finset.mem_filter.mp hF').2
    rw [Function.onFun, Finset.disjoint_left]
    intro x hx hx'
    simp only [hf, Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and] at hx hx'
    apply hne
    have hFx : F = Subgroup.zpowers x := by
      have hxF : Subgroup.zpowers x ≤ F := Subgroup.zpowers_le.mpr hx.2
      refine (Subgroup.eq_of_le_of_card_ge hxF ?_).symm
      have hd : Nat.card (Subgroup.zpowers x) ∣ 3 := h3 ▸ Subgroup.card_dvd_of_le hxF
      rcases (Nat.dvd_prime Nat.prime_three).mp hd with h | h
      · exfalso
        rw [Nat.card_zpowers, orderOf_eq_one_iff] at h
        exact hx.1 h
      · rw [h3, h]
    have hle : F ≤ F' := by
      rw [hFx]
      exact Subgroup.zpowers_le.mpr hx'.2
    exact Subgroup.eq_of_le_of_card_ge hle (by rw [h3, h3'])
  have hsub : Ts.biUnion f ⊆ P := by
    intro x hx
    obtain ⟨F, hF, hxF⟩ := Finset.mem_biUnion.mp hx
    obtain ⟨hFA, -⟩ := (Finset.mem_filter.mp hF).2
    simp only [hf, Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and] at hxF
    simp only [hP, Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hxF.1, hFA hxF.2⟩
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_biUnion hdisj, Finset.sum_congr rfl hfcard, Finset.sum_const, smul_eq_mul,
    hPcard] at hcard
  rw [hTeq, Set.ncard_coe_finset]
  omega

omit [Finite G] in
theorem isThreeCentralIn_of_mem_zpowers {L : Subgroup G} {x y : G} (hx : IsThreeCentralIn L x)
    (hy : y ∈ Subgroup.zpowers x) : IsThreeCentralIn L y := by
  obtain ⟨hxL, S, hxS, hSx⟩ := hx
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  have hyL : x ^ k ∈ L := zpow_mem hxL k
  have hk : (⟨x ^ k, hyL⟩ : ↥L) = (⟨x, hxL⟩ : ↥L) ^ k := Subtype.ext (by simp)
  refine ⟨hyL, S, ?_, ?_⟩
  · rw [hk]
    exact zpow_mem hxS k
  · intro s hs
    rw [Subgroup.mem_centralizer_singleton_iff, hk]
    exact ((Commute.zpow_left (Subgroup.mem_centralizer_singleton_iff.mp (hSx hs)).symm k).symm)

theorem isThreeCentralIn_map_conj {L : Subgroup G} {x : G} (hx : IsThreeCentralIn L x) (w : G) :
    IsThreeCentralIn (L.map (MulAut.conj w).toMonoidHom) (w * x * w⁻¹) := by
  obtain ⟨hxL, S, hxS, hSx⟩ := hx
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set e := L.equivMapOfInjective (MulAut.conj w).toMonoidHom (MulAut.conj w).injective with he
  have hxw : w * x * w⁻¹ ∈ L.map (MulAut.conj w).toMonoidHom := ⟨x, hxL, rfl⟩
  have hex : e ⟨x, hxL⟩ = ⟨w * x * w⁻¹, hxw⟩ := Subtype.ext rfl
  refine ⟨hxw, S.mapSurjective (f := e.toMonoidHom) e.surjective, ?_, ?_⟩
  · change _ ∈ (S : Subgroup ↥L).map e.toMonoidHom
    rw [← hex]
    exact ⟨⟨x, hxL⟩, hxS, rfl⟩
  · change (S : Subgroup ↥L).map e.toMonoidHom ≤ _
    rintro _ ⟨s, hs, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, ← hex]
    have h1 := Subgroup.mem_centralizer_singleton_iff.mp (hSx hs)
    simp only [MulEquiv.coe_toMonoidHom]
    rw [← map_mul, ← map_mul, h1]

end Item148PtRes

end CFSG.RankThree.PartTwo.Sec14
