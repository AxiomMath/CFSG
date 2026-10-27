module

public import CFSG.RankThree.PartOne.FTL.Fit
public import CFSG.RankThree.PartTwo.Sec21.Item22Tools

public section

namespace CFSG.RankThree.PartTwo.Sec21.Commute33Steps

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
open Subgroup
open scoped commutatorElement Pointwise

variable {G : Type} [Group G]

theorem commutator_le_of_perfect {K J R : Subgroup G} (hK : ⁅K, K⁆ = K)
    (hKR : K ≤ normalizer (R : Set G)) (hJR : J ≤ normalizer (R : Set G))
    (h : ⁅⁅K, J⁆, K⁆ ≤ R) : ⁅K, J⁆ ≤ R := by
  have h3 := PartOne.FTL.commutator_commutator_le_of_rotate (N := R) (H₁ := K) (H₂ := K)
    (H₃ := J) hKR hKR hJR h (by rw [Subgroup.commutator_comm J K]; exact h)
  rwa [hK] at h3

theorem commutator_le_of_simple {K P R : Subgroup G} [IsSimpleGroup K]
    (hKP : K ≤ normalizer (P : Set G)) (hKR : K ≤ normalizer (R : Set G)) {z : G} (hzK : z ∈ K)
    (hz1 : z ≠ 1) (hz : ∀ p ∈ P, ⁅p, z⁆ ∈ R) : ⁅P, K⁆ ≤ R := by
  have hconj : ∀ g ∈ K, ∀ r ∈ R, g * r * g⁻¹ ∈ R := fun g hg r hr =>
    (mem_normalizer_iff.mp (hKR hg) r).mp hr
  have hconjP : ∀ g ∈ K, ∀ p ∈ P, g⁻¹ * p * g ∈ P := fun g hg p hp => by
    have := (mem_normalizer_iff.mp (hKP (K.inv_mem hg)) p).mp hp
    simpa using this
  let H : Subgroup K :=
    { carrier := {k | ∀ p ∈ P, ⁅p, (k : G)⁆ ∈ R}
      mul_mem' := fun {a b} ha hb p hp => by
        have e : ⁅p, ((a * b : K) : G)⁆ =
            ⁅p, (a : G)⁆ * ((a : G) * ⁅p, (b : G)⁆ * (a : G)⁻¹) := by
          simp only [Subgroup.coe_mul, commutatorElement_def]
          group
        rw [e]
        exact R.mul_mem (ha p hp) (hconj _ a.2 _ (hb p hp))
      one_mem' := fun p _ => by simp
      inv_mem' := fun {a} ha p hp => by
        have e : ⁅p, ((a⁻¹ : K) : G)⁆ = (a : G)⁻¹ * ⁅p, (a : G)⁆⁻¹ * (a : G) := by
          simp only [Subgroup.coe_inv, commutatorElement_def]
          group
        rw [e]
        have := hconj _ (K.inv_mem a.2) _ (R.inv_mem (ha p hp))
        simpa using this }
  have hHn : H.Normal := ⟨fun k hk g p hp => by
    have e : ⁅p, ((g * k * g⁻¹ : K) : G)⁆ =
        (g : G) * ⁅(g : G)⁻¹ * p * g, (k : G)⁆ * (g : G)⁻¹ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def]
      group
    rw [e]
    exact hconj _ g.2 _ (hk _ (hconjP _ g.2 p hp))⟩
  rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal _ _ _ H hHn with hb | ht
  · exfalso
    have hzH : (⟨z, hzK⟩ : K) ∈ H := hz
    rw [hb, Subgroup.mem_bot] at hzH
    exact hz1 (congrArg Subtype.val hzH)
  · rw [Subgroup.commutator_le]
    intro p hp k hk
    have hkH : (⟨k, hk⟩ : K) ∈ H := ht ▸ Subgroup.mem_top _
    exact hkH p hp

theorem normalizer_le_normalizer_inf_centralizer (Q : Subgroup G) :
    normalizer (Q : Set G) ≤
      normalizer ((normalizer (Q : Set G) ⊓ centralizer (Q : Set G) : Subgroup G) : Set G) := by
  have key : ∀ w ∈ normalizer (Q : Set G), ∀ x ∈ normalizer (Q : Set G) ⊓ centralizer (Q : Set G),
      w * x * w⁻¹ ∈ normalizer (Q : Set G) ⊓ centralizer (Q : Set G) := by
    intro w hw x hx
    obtain ⟨hxN, hxC⟩ := Subgroup.mem_inf.mp hx
    refine Subgroup.mem_inf.mpr ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hw hxN)
      (Subgroup.inv_mem _ hw), ?_⟩
    rw [mem_centralizer_iff]
    intro q hq
    have hq' : w⁻¹ * q * w ∈ Q := by
      have := (mem_normalizer_iff.mp (Subgroup.inv_mem _ hw) q).mp hq
      simpa using this
    have h1 := mem_centralizer_iff.mp hxC _ hq'
    calc q * (w * x * w⁻¹) = w * ((w⁻¹ * q * w) * x) * w⁻¹ := by group
      _ = w * (x * (w⁻¹ * q * w)) * w⁻¹ := by rw [h1]
      _ = w * x * w⁻¹ * q := by group
  intro w hw
  rw [mem_normalizer_iff]
  intro x
  refine ⟨key w hw x, fun hx => ?_⟩
  have := key w⁻¹ (Subgroup.inv_mem _ hw) _ hx
  simpa [mul_assoc] using this

theorem le_centralizer_of_le_sup [Finite G] {Q K N : Subgroup G} (hK : ⁅K, K⁆ = K)
    (hKQ : K ≤ normalizer (Q : Set G)) (hNQ : N ≤ normalizer (Q : Set G))
    (hN : Group.IsSolvable N)
    (h : K ≤ (normalizer (Q : Set G) ⊓ centralizer (Q : Set G)) ⊔ N) :
    K ≤ centralizer (Q : Set G) := by
  set W := normalizer (Q : Set G) with hW
  set C := W ⊓ centralizer (Q : Set G) with hC
  set ρ : W →* MulAut Q := Q.normalizerMonoidHom with hρ
  have hρC : ∀ c : W, (c : G) ∈ C → ρ c = 1 := by
    intro c hc
    refine MulEquiv.ext fun q => Subtype.ext ?_
    change (c : G) * q * (c : G)⁻¹ = q
    rw [← mem_centralizer_iff.mp hc.2 q q.2, mul_inv_cancel_right]
  have hNC : N ≤ normalizer (C : Set G) := hNQ.trans (normalizer_le_normalizer_inf_centralizer Q)
  have hset : ((C ⊔ N : Subgroup G) : Set G) = (C : Set G) * (N : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left C N hNC
  set K' := K.subgroupOf W
  set N' := N.subgroupOf W
  have hle : K'.map ρ ≤ N'.map ρ := by
    rintro _ ⟨k, hk, rfl⟩
    have hkCN : (k : G) ∈ ((C ⊔ N : Subgroup G) : Set G) := h hk
    rw [hset] at hkCN
    obtain ⟨c, hc, n, hn, hcn⟩ := hkCN
    have hcW : c ∈ W := hc.1
    have hnW : n ∈ W := hNQ hn
    have hk' : k = ⟨c, hcW⟩ * ⟨n, hnW⟩ := Subtype.ext hcn.symm
    refine ⟨⟨n, hnW⟩, hn, ?_⟩
    rw [hk', map_mul, hρC ⟨c, hcW⟩ hc, one_mul]
  have hKperf : Group.IsPerfect K' := by
    have : Group.IsPerfect K := Subgroup.isPerfect_iff.mpr hK
    exact Group.IsPerfect.ofSurjective
      (f := (Subgroup.subgroupOfEquivOfLe hKQ).symm.toMonoidHom) (MulEquiv.surjective _)
  have hNsol : Group.IsSolvable N' :=
    Group.isSolvable_of_isSolvable_injective (f := (Subgroup.subgroupOfEquivOfLe hNQ).toMonoidHom)
      (MulEquiv.injective _)
  have himperf : Group.IsPerfect (K'.map ρ) :=
    Group.IsPerfect.ofSurjective (f := ρ.subgroupMap K') (ρ.subgroupMap_surjective K')
  have himsol : Group.IsSolvable (K'.map ρ) := by
    have : Group.IsSolvable (N'.map ρ) :=
      Group.isSolvable_of_surjective (f := ρ.subgroupMap N') (ρ.subgroupMap_surjective N')
    exact Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hle)
      (Subgroup.inclusion_injective hle)
  have hsub := subsingleton_of_isPerfect_of_isSolvable himperf himsol
  intro k hk
  have hkW : k ∈ W := hKQ hk
  have hρk : ρ ⟨k, hkW⟩ = 1 := by
    have h1 : (⟨ρ ⟨k, hkW⟩, ⟨⟨k, hkW⟩, hk, rfl⟩⟩ : K'.map ρ) = 1 := Subsingleton.elim _ _
    exact congrArg Subtype.val h1
  rw [mem_centralizer_iff]
  intro q hq
  have h2 := congrArg (fun σ : MulAut Q => ((σ ⟨q, hq⟩ : Q) : G)) hρk
  change k * q * k⁻¹ = q at h2
  calc q * k = k * q * k⁻¹ * k := by rw [h2]
    _ = k * q := by group

theorem eq_one_of_forall_commute_of_simple {K : Subgroup G} [IsSimpleGroup K] (hK : ⁅K, K⁆ = K)
    {r : G} (hrK : r ∈ K) (h : ∀ k ∈ K, r * k = k * r) : r = 1 := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center K) with hb | ht
  · have hr : (⟨r, hrK⟩ : K) ∈ center K := by
      rw [mem_center_iff]
      intro k
      exact Subtype.ext (h k k.2).symm
    rw [hb, Subgroup.mem_bot] at hr
    exact congrArg Subtype.val hr
  · exfalso
    have hcomm : ⁅K, K⁆ = ⊥ := by
      rw [eq_bot_iff, Subgroup.commutator_le]
      intro x hx y hy
      have hx' : (⟨x, hx⟩ : K) ∈ center K := ht ▸ Subgroup.mem_top _
      have hxy := (mem_center_iff.mp hx') ⟨y, hy⟩
      rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
      exact (congrArg Subtype.val hxy).symm
    rw [hK] at hcomm
    have : Nontrivial K := IsSimpleGroup.toNontrivial
    obtain ⟨⟨x, hx⟩, hx1⟩ := exists_ne (1 : K)
    exact hx1 (Subtype.ext (by rw [hcomm] at hx; exact (Subgroup.mem_bot.mp hx)))

theorem le_centralizer_of_commutator_mem [Finite G] {Q K N : Subgroup G} [IsSimpleGroup K]
    (hK : ⁅K, K⁆ = K) (hKQ : K ≤ normalizer (Q : Set G)) (hNQ : N ≤ normalizer (Q : Set G))
    (hKN : K ≤ normalizer (N : Set G)) (hN : Group.IsSolvable N) {r : G} (hrK : r ∈ K)
    (hr1 : r ≠ 1)
    (h : ∀ k ∈ K, ⁅r, k⁆ ∈ (normalizer (Q : Set G) ⊓ centralizer (Q : Set G)) ⊔ N) :
    K ≤ centralizer (Q : Set G) := by
  set X : Subgroup G := (normalizer (Q : Set G) ⊓ centralizer (Q : Set G)) ⊔ N with hX
  have hKX : K ≤ normalizer (X : Set G) := by
    intro k hk
    have hk1 : k ∈ normalizer
        ((normalizer (Q : Set G) ⊓ centralizer (Q : Set G) : Subgroup G) : Set G) :=
      normalizer_le_normalizer_inf_centralizer Q (hKQ hk)
    rw [mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      exact Subgroup.conj_mem_sup_of_mem_inf_normalizer_of_mem_inf
        (Subgroup.mem_inf.mpr ⟨hk1, hKN hk⟩) x hx
    · intro hx
      have := Subgroup.conj_mem_sup_of_mem_inf_normalizer_of_mem_inf
        (s := k⁻¹) (Subgroup.mem_inf.mpr ⟨Subgroup.inv_mem _ hk1, Subgroup.inv_mem _ (hKN hk)⟩)
        _ hx
      simpa [mul_assoc] using this
  have hHn : (X.subgroupOf K).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact (mem_normalizer_iff.mp (hKX g.2) _).mp hn⟩
  rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal _ _ _ _ hHn with hb | ht
  · exfalso
    apply hr1
    refine eq_one_of_forall_commute_of_simple hK hrK fun k hk => ?_
    have hrkK : ⁅r, k⁆ ∈ K := by
      rw [commutatorElement_def]
      exact K.mul_mem (K.mul_mem (K.mul_mem hrK hk) (K.inv_mem hrK)) (K.inv_mem hk)
    have hc : (⟨⁅r, k⁆, hrkK⟩ : K) ∈ X.subgroupOf K := Subgroup.mem_subgroupOf.mpr (h k hk)
    rw [hb] at hc
    have hc' : (⟨⁅r, k⁆, hrkK⟩ : K) = 1 := Subgroup.mem_bot.mp hc
    have := congrArg Subtype.val hc'
    rw [Subgroup.coe_one, commutatorElement_eq_one_iff_mul_comm] at this
    exact this
  · have hKX' : K ≤ X := Subgroup.subgroupOf_eq_top.mp ht
    exact le_centralizer_of_le_sup hK hKQ hNQ hN hKX'

theorem eq_bot_of_forall_pCore [Finite G] {K J N : Subgroup G} (hN : N = ⁅K, J⁆)
    (hK : ⁅K, K⁆ = K) (hJ : ⁅J, J⁆ = J) (hNs : Group.IsSolvable N)
    (h : ∀ s : ℕ, s.Prime → K ≤ centralizer (inSubgroup (pCore s) N : Set G) ∨
      J ≤ centralizer (inSubgroup (pCore s) N : Set G)) : N = ⊥ := by
  classical
  set M : ℕ → Subgroup G := fun s => inSubgroup (pCore s) N with hM
  have hKN : K ≤ normalizer (N : Set G) := by
    rw [hN]; exact Subgroup.normalizer_commutator_ge_left K J
  have hJN : J ≤ normalizer (N : Set G) := by
    rw [hN]; exact Subgroup.normalizer_commutator_ge_right K J
  have hMN : ∀ s, M s ≤ N := fun s => SteinbergBY.inSubgroup_pCore_le s N
  have hKM : ∀ s, K ≤ normalizer (M s : Set G) := fun s k hk =>
    SteinbergBY.normalizer_le_normalizer_inSubgroup_pCore s N (hKN hk)
  have hJM : ∀ s, J ≤ normalizer (M s : Set G) := fun s j hj =>
    SteinbergBY.normalizer_le_normalizer_inSubgroup_pCore s N (hJN hj)
  have hNM : ∀ s, N ≤ normalizer (M s : Set G) := fun s =>
    SteinbergBY.le_normalizer_inSubgroup_pCore s N
  have hcentM : ∀ s : ℕ, s.Prime → N ≤ centralizer (M s : Set G) := by
    intro s hs
    rcases h s hs with hKC | hJC
    · have := PartOne.Sec9B.commutator_le_centralizer_of_centralizes (hJM s) hKC
      rw [hN, Subgroup.commutator_comm]
      exact this
    · rw [hN]
      exact PartOne.Sec9B.commutator_le_centralizer_of_centralizes (hKM s) hJC
  have hFC : inSubgroup fittingSubgroup N ≤ centralizer (N : Set G) := by
    rw [inSubgroup, LocalCores.fittingSubgroup_eq_iSup_pCore, Subgroup.map_iSup]
    refine iSup_le fun s => ?_
    have hsp : (s : ℕ).Prime := Nat.prime_of_mem_primeFactors s.2
    exact Subgroup.le_centralizer_iff.mp (hcentM s hsp)
  have hNC : N ≤ centralizer (inSubgroup fittingSubgroup N : Set G) :=
    Subgroup.le_centralizer_iff.mp hFC
  have hNF : N ≤ inSubgroup fittingSubgroup N := fun z hz =>
    PartOne.Sec9B.inf_centralizer_fitting_le hNs ⟨hz, hNC hz⟩
  set NK : Subgroup G := ⨆ s : {s : ℕ // s.Prime ∧ K ≤ centralizer (M s : Set G)}, M s.1
    with hNK
  set NJ : Subgroup G := ⨆ s : {s : ℕ // s.Prime ∧ ¬ K ≤ centralizer (M s : Set G)}, M s.1
    with hNJ
  have hNKN : NK ≤ N := iSup_le fun s => hMN s.1
  have hNJN : NJ ≤ N := iSup_le fun s => hMN s.1
  have hFle : inSubgroup fittingSubgroup N ≤ NK ⊔ NJ := by
    rw [inSubgroup, LocalCores.fittingSubgroup_eq_iSup_pCore, Subgroup.map_iSup]
    refine iSup_le fun s => ?_
    have hsp : (s : ℕ).Prime := Nat.prime_of_mem_primeFactors s.2
    by_cases hKs : K ≤ centralizer (M (s : ℕ) : Set G)
    · exact le_sup_of_le_left (le_iSup
        (fun t : {t : ℕ // t.Prime ∧ K ≤ centralizer (M t : Set G)} => M t.1) ⟨s, hsp, hKs⟩)
    · exact le_sup_of_le_right (le_iSup
        (fun t : {t : ℕ // t.Prime ∧ ¬ K ≤ centralizer (M t : Set G)} => M t.1) ⟨s, hsp, hKs⟩)
  have hNNJ : N ≤ normalizer (NJ : Set G) := fun g hg =>
    PartOne.Sec9B.mem_normalizer_iSup fun s => hNM s.1 hg
  have hKNJ : K ≤ normalizer (NJ : Set G) := fun g hg =>
    PartOne.Sec9B.mem_normalizer_iSup fun s => hKM s.1 hg
  have hJNJ : J ≤ normalizer (NJ : Set G) := fun g hg =>
    PartOne.Sec9B.mem_normalizer_iSup fun s => hJM s.1 hg
  have hNK_K : NK ≤ centralizer (K : Set G) := iSup_le fun s =>
    Subgroup.le_centralizer_iff.mp s.2.2
  have hNJ_J : NJ ≤ centralizer (J : Set G) := iSup_le fun s =>
    Subgroup.le_centralizer_iff.mp ((h s.1 s.2.1).resolve_left s.2.2)
  have hconj : ∀ g ∈ normalizer (NJ : Set G), ∀ n ∈ NJ, g * n * g⁻¹ ∈ NJ := fun g hg n hn =>
    (mem_normalizer_iff.mp hg n).mp hn
  have hsupN : NK ⊔ NJ ≤ normalizer (NJ : Set G) := sup_le (hNKN.trans hNNJ) (hNJN.trans hNNJ)
  have key : ∀ w ∈ NK ⊔ NJ, ∀ k ∈ K, ⁅w, k⁆ ∈ NJ := by
    intro w hw k hk
    rw [Subgroup.sup_eq_closure] at hw
    induction hw using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with hx | hx
      · have hc : k * x = x * k := mem_centralizer_iff.mp (hNK_K hx) k hk
        have h1 : ⁅x, k⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr hc.symm
        rw [h1]
        exact one_mem _
      · rw [commutatorElement_def]
        have := hconj k (hKNJ hk) x⁻¹ (inv_mem hx)
        have e1 : x * k * x⁻¹ * k⁻¹ = x * (k * x⁻¹ * k⁻¹) := by group
        rw [e1]
        exact mul_mem hx this
    | one => simp
    | mul a b ha hb iha ihb =>
      have haN : a ∈ normalizer (NJ : Set G) := hsupN (by rwa [Subgroup.sup_eq_closure])
      have e1 : ⁅a * b, k⁆ = (a * ⁅b, k⁆ * a⁻¹) * ⁅a, k⁆ := by
        simp only [commutatorElement_def]
        group
      rw [e1]
      exact mul_mem (hconj a haN _ ihb) iha
    | inv a ha iha =>
      have haN : a ∈ normalizer (NJ : Set G) := hsupN (by rwa [Subgroup.sup_eq_closure])
      have e1 : ⁅a⁻¹, k⁆ = a⁻¹ * (⁅a, k⁆)⁻¹ * a := by
        simp only [commutatorElement_def]
        group
      rw [e1]
      have := hconj a⁻¹ (inv_mem haN) _ (NJ.inv_mem iha)
      simpa using this
  have hNKle : ⁅N, K⁆ ≤ NJ := Subgroup.commutator_le.mpr fun z hz k hk =>
    key z (hFle (hNF hz)) k hk
  have hNle : N ≤ NJ := by
    rw [hN]
    exact commutator_le_of_perfect hK hKNJ hJNJ (by rw [← hN]; exact hNKle)
  have hJC : J ≤ centralizer (N : Set G) :=
    (Subgroup.le_centralizer_iff.mp hNJ_J).trans (Subgroup.centralizer_le hNle)
  have hbot : ⁅J, K⁆ ≤ ⊥ := by
    have hbotN : ∀ X : Subgroup G, X ≤ normalizer ((⊥ : Subgroup G) : Set G) := fun X g _ =>
      mem_normalizer_iff.mpr fun x => by
        rw [Subgroup.mem_bot, Subgroup.mem_bot]
        constructor
        · rintro rfl; group
        · intro hx
          calc x = g⁻¹ * (g * x * g⁻¹) * g := by group
            _ = 1 := by rw [hx]; group
    refine commutator_le_of_perfect hJ (hbotN J) (hbotN K) ?_
    rw [Subgroup.commutator_comm J K, ← hN, Subgroup.commutator_comm]
    exact le_of_eq (Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hJC)
  rw [hN, Subgroup.commutator_comm]
  exact le_bot_iff.mp hbot

end CFSG.RankThree.PartTwo.Sec21.Commute33Steps
