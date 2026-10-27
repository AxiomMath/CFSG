module

public import CFSG.LocalAnalysis.SteinbergSFSingleCommLocalSixKDefs
public import CFSG.LocalAnalysis.SteinbergSFSingleCommLocalSixHGeneric
public import CFSG.LocalAnalysis.SteinbergSFSingleCommRootStandardTorus
public import CFSG.LocalAnalysis.SteinbergSFFullCenterRootNormalizersOrbit
public import CFSG.LocalAnalysis.SteinbergSFFullCenterTorusComplementBase
public import CFSG.LocalAnalysis.SteinbergSFSingleCommLocalSixFNontrivial

public section

namespace CFSG.LocalAnalysis.SymplecticFourStandard

namespace SingleCommParts

open Subgroup GomiFusion
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.QuasithinUnique.Setup.X7b
  CFSG.RankThree.PartOne.KCRootAxis

section Steps

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {L : Subgroup G} {K : Type} [Field K]
  [CharP K 2] [Finite K] {n : ℕ} {φ : L ≃* antiSp K} {t : G} {i : Axis}

theorem sixK_k1_aux_orbit_card (H : Subgroup G) (c : G) :
    ((fun x : G => x * c * x⁻¹) '' (H : Set G)).ncard * Nat.card ↥(H ⊓ centralizer ({c} : Set G)) =
      Nat.card ↥H := by
  obtain ⟨N, hN⟩ : ∃ N : Subgroup ↥H, N = (H ⊓ centralizer ({c} : Set G)).subgroupOf H :=
    ⟨_, rfl⟩
  have key : ∀ a b : ↥H,
      (a : G) * c * (a : G)⁻¹ = (b : G) * c * (b : G)⁻¹ ↔ (a⁻¹ * b : ↥H) ∈ N := by
    intro a b
    obtain ⟨z, hz⟩ : ∃ z : G, (b : G) = (a : G) * z := ⟨(a : G)⁻¹ * (b : G), by group⟩
    have hcoe : ((a⁻¹ * b : ↥H) : G) = z := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, hz, inv_mul_cancel_left]
    have hzH : z ∈ H := by
      rw [← hcoe]; exact (a⁻¹ * b : ↥H).2
    have hfb : (b : G) * c * (b : G)⁻¹ = (a : G) * (z * c * z⁻¹) * (a : G)⁻¹ := by
      rw [hz]; group
    have hN_iff : (a⁻¹ * b : ↥H) ∈ N ↔ c * z = z * c := by
      rw [hN, Subgroup.mem_subgroupOf, hcoe, Subgroup.mem_inf, and_iff_right hzH,
        mem_centralizer_iff]
      constructor
      · intro h; exact h c (Set.mem_singleton c)
      · intro h x hx; rw [Set.mem_singleton_iff.mp hx]; exact h
    rw [hfb, hN_iff]
    constructor
    · intro h
      have hcz : c = z * c * z⁻¹ := by
        calc c = (a : G)⁻¹ * ((a : G) * c * (a : G)⁻¹) * (a : G) := by group
          _ = (a : G)⁻¹ * ((a : G) * (z * c * z⁻¹) * (a : G)⁻¹) * (a : G) := by rw [h]
          _ = z * c * z⁻¹ := by group
      calc c * z = (z * c * z⁻¹) * z := by rw [← hcz]
        _ = z * c := by group
    · intro h
      have hzc : z * c * z⁻¹ = c := by
        calc z * c * z⁻¹ = c * z * z⁻¹ := by rw [h]
          _ = c := by group
      rw [hzc]
  let e : ↥H ⧸ N → ↥((fun x : G => x * c * x⁻¹) '' (H : Set G)) :=
    Quotient.lift (s := QuotientGroup.leftRel N)
      (fun a => ⟨(a : G) * c * (a : G)⁻¹, (a : G), a.2, rfl⟩)
      (fun a b hab => Subtype.ext ((key a b).mpr (QuotientGroup.leftRel_apply.mp hab)))
  have hbij : Function.Bijective e := by
    refine ⟨?_, ?_⟩
    · intro q1 q2 hq
      obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective q1
      obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective q2
      have hab : (a : G) * c * (a : G)⁻¹ = (b : G) * c * (b : G)⁻¹ := congrArg Subtype.val hq
      exact QuotientGroup.eq.mpr ((key a b).mp hab)
    · rintro ⟨y, x, hx, rfl⟩
      exact ⟨QuotientGroup.mk ⟨x, hx⟩, rfl⟩
  have hquot : Nat.card ↥((fun x : G => x * c * x⁻¹) '' (H : Set G)) = Nat.card (↥H ⧸ N) :=
    Nat.card_congr (Equiv.ofBijective e hbij).symm
  have hNc : Nat.card N = Nat.card ↥(H ⊓ centralizer ({c} : Set G)) := by
    rw [hN]; exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have hcard : Nat.card N * N.index = Nat.card ↥H := Subgroup.card_mul_index N
  rw [← Nat.card_coe_set_eq, hquot, ← hNc, mul_comm]
  exact hcard

theorem sixK_k1_aux_U_sq {w : G} (hw : w ∈ U φ i) : w * w = 1 := by
  obtain ⟨hL, hmem⟩ := GomiFusion.mem_pull.mp hw
  have hA : φ ⟨w, hL⟩ ∈ rootA K i := FullCenter.rootU_le_rootA i hmem
  have h1 : φ (⟨w, hL⟩ * ⟨w, hL⟩) = 1 := by
    rw [map_mul]; exact FullCenter.rootA_mul_self i hA
  have h2 : (⟨w, hL⟩ * ⟨w, hL⟩ : L) = 1 := (MulEquiv.map_eq_one_iff φ).mp h1
  simpa using congrArg Subtype.val h2

theorem sixK_k1_aux_sq_mem_U (hH : SixHConclusion φ t i) {v : G} (hv : v ∈ Vtor φ t i i) :
    v * v ∈ U φ i := by
  have hVM : Vtor φ t i i ≤ Mhat φ t i i := inf_le_left.trans le_sup_left
  rw [← hH.sq_Mhat_i]
  exact Subgroup.subset_closure (show v * v ∈ {x : G | ∃ y ∈ Mhat φ t i i, x = y * y} from
    ⟨v, hVM hv, rfl⟩)

theorem sixK_k1_aux_mem_W (h : FullCenter.FCHyp L K n φ t)
    (hne : ⁅A φ i, F φ t ⊓ D φ t i.swap⁆ ≠ ⊥) (hbot : ⁅A φ i.swap, F φ t ⊓ D φ t i⁆ = ⊥)
    {v : G} (hv : v ∈ Vtor φ t i i)
    (hc : (t⁻¹ * (v⁻¹ * t * v)) * (t⁻¹ * (v⁻¹ * t * v)) = 1) : v ∈ Wk φ t i := by
  obtain ⟨hn, e, he⟩ := RootStandard.quotient_V h i hne hbot
  have h1 := he ⟨v, hv⟩
  have h2 : e (QuotientGroup.mk ⟨v, hv⟩) = 1 := Subtype.ext (h1.trans hc)
  have h3 : (QuotientGroup.mk ⟨v, hv⟩ : ↥(Vtor φ t i i) ⧸ (Wk φ t i).subgroupOf (Vtor φ t i i)) = 1 :=
    (MulEquiv.map_eq_one_iff e).mp h2
  exact Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp h3)

theorem sixK_k1_aux_mem_W_of_inv (h : FullCenter.FCHyp L K n φ t)
    (hne : ⁅A φ i, F φ t ⊓ D φ t i.swap⁆ ≠ ⊥) (hbot : ⁅A φ i.swap, F φ t ⊓ D φ t i⁆ = ⊥)
    (hH : SixHConclusion φ t i) (ht : t * t = 1) {u : G} (hu : u ∈ Vtor φ t i i)
    (hinv : t * u * t = u⁻¹) : u ∈ Wk φ t i := by
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have e2 : t * u⁻¹ * t = u := by
    rw [← hinv]
    calc t * (t * u * t) * t = (t * t) * u * (t * t) := by group
      _ = u := by rw [ht, one_mul, mul_one]
  have e1 : t⁻¹ * (u⁻¹ * t * u) = u * u := by
    rw [hti]
    calc t * (u⁻¹ * t * u) = (t * u⁻¹ * t) * u := by group
      _ = u * u := by rw [e2]
  have hc : (t⁻¹ * (u⁻¹ * t * u)) * (t⁻¹ * (u⁻¹ * t * u)) = 1 := by
    rw [e1]; exact sixK_k1_aux_U_sq (sixK_k1_aux_sq_mem_U hH hu)
  exact sixK_k1_aux_mem_W h hne hbot hu hc

theorem sixK_k1
    (hS : SCSetting L K n φ t i) (hH : SixHConclusion φ t i) :
    K1Concl φ t i := by
  unfold K1Concl
  intro v hv hvinv
  have ht : t * t = 1 := SixF.t_mul_t hS.fc
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have hN : t ∈ normalizer ((Vtor φ t i i : Subgroup G) : Set G) :=
    RootStandard.t_mem_normalizer_V hS.fc i hS.ne_bot hS.eq_bot i
  have hVcard : Nat.card ↥(Vtor φ t i i) = Nat.card K ^ 3 :=
    RootStandard.card_V hS.fc i hS.ne_bot hS.eq_bot
  have hVC : Vtor φ t i i ⊓ centralizer ({t} : Set G) = U φ i :=
    RootStandard.V_inf_C hS.fc i hS.ne_bot hS.eq_bot
  have hUcard : Nat.card ↥(U φ i) = Nat.card K := FullCenter.FCHyp.card_U i
  have hWcard : Nat.card ↥(Wk φ t i) = Nat.card K ^ 2 := FullCenterTorus.card_W hS.fc i
  have hvt : t * v * t = v⁻¹ := by
    refine eq_inv_of_mul_eq_one_left ?_
    simpa only [mul_assoc] using hvinv
  have hvW : v ∈ Wk φ t i :=
    sixK_k1_aux_mem_W_of_inv hS.fc hS.ne_bot hS.eq_bot hH ht hv hvt
  have hO := sixK_k1_aux_orbit_card (Vtor φ t i i) t
  rw [hVC, hUcard, hVcard] at hO
  have hq : 0 < Nat.card K := Nat.card_pos
  have hOc : ((fun y : G => y * t * y⁻¹) '' (Vtor φ t i i : Set G)).ncard = Nat.card K ^ 2 := by
    apply Nat.eq_of_mul_eq_mul_right hq
    rw [hO]; ring
  have hWc : (Wk φ t i : Set G).ncard = Nat.card K ^ 2 := by
    rw [← hWcard]; exact (Nat.card_coe_set_eq _).symm
  have hAW : (fun y : G => t * (y * t * y⁻¹)) '' (Vtor φ t i i : Set G) ⊆
      (Wk φ t i : Set G) := by
    rintro _ ⟨y, hy, rfl⟩
    have hy' : y ∈ Vtor φ t i i := hy
    have hyt : t * y * t⁻¹ ∈ Vtor φ t i i := (mem_normalizer_iff.mp hN y).mp hy'
    have hu : t * (y * t * y⁻¹) ∈ Vtor φ t i i := by
      have e1 : t * (y * t * y⁻¹) = (t * y * t⁻¹) * y⁻¹ := by
        rw [hti]; simp only [mul_assoc]
      rw [e1]; exact mul_mem hyt (inv_mem hy')
    have hg : (y * t * y⁻¹) * (y * t * y⁻¹) = 1 := by
      calc (y * t * y⁻¹) * (y * t * y⁻¹) = y * (t * t) * y⁻¹ := by group
        _ = 1 := by rw [ht]; group
    have hinv : t * (t * (y * t * y⁻¹)) * t = (t * (y * t * y⁻¹))⁻¹ := by
      rw [mul_inv_rev, inv_eq_of_mul_eq_one_right hg, hti]
      calc t * (t * (y * t * y⁻¹)) * t = (t * t) * (y * t * y⁻¹) * t := by group
        _ = (y * t * y⁻¹) * t := by rw [ht, one_mul]
    exact sixK_k1_aux_mem_W_of_inv hS.fc hS.ne_bot hS.eq_bot hH ht hu hinv
  have hAc : ((fun y : G => t * (y * t * y⁻¹)) '' (Vtor φ t i i : Set G)).ncard =
      ((fun y : G => y * t * y⁻¹) '' (Vtor φ t i i : Set G)).ncard := by
    have e2 : (fun y : G => t * (y * t * y⁻¹)) '' (Vtor φ t i i : Set G) =
        (fun g : G => t * g) '' ((fun y : G => y * t * y⁻¹) '' (Vtor φ t i i : Set G)) := by
      rw [Set.image_image]
    rw [e2, Set.ncard_image_of_injective _ (mul_right_injective t)]
  have hAeq : (fun y : G => t * (y * t * y⁻¹)) '' (Vtor φ t i i : Set G) =
      (Wk φ t i : Set G) :=
    Set.eq_of_subset_of_ncard_le hAW (le_of_eq (by rw [hWc, hAc, hOc]))
  have hvA : v ∈ (fun y : G => t * (y * t * y⁻¹)) '' (Vtor φ t i i : Set G) := by
    rw [hAeq]; exact hvW
  obtain ⟨y, hy, hyv⟩ := hvA
  have hy' : y ∈ Vtor φ t i i := hy
  have hyv' : t * (y * t * y⁻¹) = v := hyv
  have hgt : y * t * y⁻¹ = t * v := by
    rw [← hyv']
    calc y * t * y⁻¹ = (t * t) * (y * t * y⁻¹) := by rw [ht, one_mul]
      _ = t * (t * (y * t * y⁻¹)) := by group
  exact ⟨y⁻¹, inv_mem hy', by rw [inv_inv]; exact hgt⟩

theorem sixK_k2_aux_U_le_Mhat (hH : SixHConclusion φ t i) : U φ i ≤ Mhat φ t i i := by
  rw [← hH.sq_Mhat_i]
  refine (Subgroup.closure_le _).mpr ?_
  rintro x ⟨y, hy, rfl⟩
  exact mul_mem hy hy

theorem sixK_k2_aux_t_not_mem (hS : SCSetting L K n φ t i) : t ∉ Mhat φ t i i := by
  intro h
  have h1 : t ∈ Mhat φ t i i ⊓ zpowers t := ⟨h, mem_zpowers t⟩
  rw [SixF.Mhat_inf_t hS.fc i hS.ne_bot hS.eq_bot, Subgroup.mem_bot] at h1
  apply hS.fc.not_conj 1
  rw [inv_one, one_mul, mul_one, h1]
  exact L.one_mem

theorem sixK_k2_aux_K_le_Mhat (hS : SCSetting L K n φ t i) : Kc φ t i ≤ Mhat φ t i i := by
  refine sup_le ?_ ?_
  · exact (le_of_eq (SixF.Mhat_inf_C hS.fc i hS.ne_bot hS.eq_bot).symm).trans inf_le_left
  · exact inf_le_left.trans ((NextCores.F_le_M hS.fc i hS.ne_bot hS.eq_bot).trans le_sup_left)

theorem sixK_k2_aux_conj_mem (hH : SixHConclusion φ t i) (hT : t ∈ Tplus φ t i) {y : G}
    (hy : y ∈ Mhat φ t i i) : t * y * t⁻¹ ∈ Mhat φ t i i := by
  obtain ⟨hle, hnorm, -⟩ := hH.normal_Mhat i
  have hyT : y ∈ Tplus φ t i := hle hy
  have h := Subgroup.Normal.conj_mem hnorm ⟨y, hyT⟩ (Subgroup.mem_subgroupOf.mpr hy) ⟨t, hT⟩
  exact Subgroup.mem_subgroupOf.mp h

theorem sixK_k2_aux_step1 (hS : SCSetting L K n φ t i) (hH : SixHConclusion φ t i)
    {m : G} (hm : m ∈ Mhat φ t i i) (hinv : t * m * (t * m) = 1) : m ∈ Kc φ t i := by
  have ht : t * t = 1 := SixF.t_mul_t hS.fc
  have htM : t ∉ Mhat φ t i i := sixK_k2_aux_t_not_mem hS
  have hUM : U φ i ≤ Mhat φ t i i := sixK_k2_aux_U_le_Mhat hH
  have hUK : U φ i ≤ Kc φ t i :=
    (GomiFusion.pull_mono φ (FullCenter.rootU_le_rootA i)).trans le_sup_left
  have hDeq : D φ t i = zpowers t ⊔ Kc φ t i := NextCores.D_eq_sup_K hS.fc i
  have hKD : Kc φ t i ≤ D φ t i := by
    rw [hDeq]
    exact le_sup_right
  have hUD : U φ i ≤ D φ t i := hUK.trans hKD
  have hKM : Kc φ t i ≤ Mhat φ t i i := sixK_k2_aux_K_le_Mhat hS
  have hPeq : Mhat φ t i i ⊔ zpowers t = P₁ φ t i :=
    SixF.Mhat_sup_t hS.fc i hS.ne_bot hS.eq_bot
  have htP : t ∈ P₁ φ t i := by
    rw [← hPeq]
    exact mem_sup_right (mem_zpowers t)
  have htmP : t * m ∈ P₁ φ t i :=
    mul_mem htP (SixF.Mhat_le_P₁ hS.fc i hS.ne_bot hS.eq_bot hm)
  obtain ⟨hNorm, hmax⟩ := hH.maximal_P₁
  unfold SixG.MNMaximal at hmax
  haveI : Finite (↥(P₁ φ t i) ⧸ (U φ i).subgroupOf (P₁ φ t i)) :=
    Finite.of_surjective (QuotientGroup.mk : ↥(P₁ φ t i) → _) QuotientGroup.mk_surjective
  obtain ⟨x, hxdef⟩ : ∃ x : ↥(P₁ φ t i) ⧸ (U φ i).subgroupOf (P₁ φ t i),
      x = QuotientGroup.mk' ((U φ i).subgroupOf (P₁ φ t i)) ⟨t * m, htmP⟩ := ⟨_, rfl⟩
  have hx2 : x ^ 2 = 1 := by
    have hsq : (⟨t * m, htmP⟩ : ↥(P₁ φ t i)) ^ 2 = 1 :=
      Subtype.ext (by simpa only [sq, Subgroup.coe_mul, Subgroup.coe_one] using hinv)
    rw [hxdef, ← map_pow, hsq, map_one]
  have hxX : x ∈ ((P₁ φ t i).subgroupOf (P₁ φ t i)).map
      (QuotientGroup.mk' ((U φ i).subgroupOf (P₁ φ t i))) := by
    rw [hxdef]
    exact Subgroup.mem_map.mpr ⟨⟨t * m, htmP⟩, Subgroup.mem_subgroupOf.mpr htmP, rfl⟩
  haveI := IsElementaryAbelian.zpowers_of_pow_eq_one hx2
  obtain ⟨Sg, hzS, hSmax⟩ := sixH_g6_exists_maximal (Subgroup.zpowers_le.mpr hxX)
  have hxS : x ∈ Sg := hzS (Subgroup.mem_zpowers x)
  rcases (hmax Sg).mp hSmax with hSM | hSD
  · exfalso
    rw [hSM, hxdef] at hxS
    obtain ⟨b, hbM, hbtm⟩ := sixH_g7_quot_mem htmP hxS
    have h3 : b * (b⁻¹ * (t * m)) ∈ Mhat φ t i i := mul_mem hbM (hUM hbtm)
    rw [mul_inv_cancel_left] at h3
    have h4 : t * m * m⁻¹ ∈ Mhat φ t i i := mul_mem h3 (inv_mem hm)
    rw [mul_inv_cancel_right] at h4
    exact htM h4
  · rw [hSD, hxdef] at hxS
    obtain ⟨a, haD, hau⟩ := sixH_g7_quot_mem htmP hxS
    have hD : t * m ∈ D φ t i := by
      have h5 := mul_mem haD (hUD hau)
      rwa [mul_inv_cancel_left] at h5
    rw [hDeq, sup_comm] at hD
    rcases FullCenterWeyl.mem_or_mul_mem ht (SixG.t_mem_normalizer_K hS.fc i) hD with h1 | h1
    · have h2 : t * m * m⁻¹ ∈ Mhat φ t i i := mul_mem (hKM h1) (inv_mem hm)
      rw [mul_inv_cancel_right] at h2
      exact (htM h2).elim
    · have e : t * (t * m) = m := by rw [← mul_assoc, ht, one_mul]
      rw [e] at h1
      exact h1

theorem sixK_k2
    (hS : SCSetting L K n φ t i) (hH : SixHConclusion φ t i) :
    K2Concl φ t i := by
  unfold K2Concl
  intro m hm hinv
  have ht : t * t = 1 := SixF.t_mul_t hS.fc
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have hKm : m ∈ Kc φ t i := sixK_k2_aux_step1 hS hH hm hinv
  have hT : t ∈ Tplus φ t i := by
    rw [← hH.sup_t]; exact mem_sup_right (mem_zpowers t)
  have hAI : Mhat φ t i i ⊓ centralizer ({t} : Set G) = A φ i :=
    SixF.Mhat_inf_C hS.fc i hS.ne_bot hS.eq_bot
  have hcard : Nat.card ↥(Mhat φ t i i ⊓ centralizer ({t} : Set G)) = Nat.card K ^ 3 := by
    rw [hAI]
    exact (GomiFusion.card_pull φ _).trans (FullCenter.card_rootA i)
  have hMc : Nat.card ↥(Mhat φ t i i) = Nat.card K ^ 7 :=
    SixF.card_Mhat hS.fc i hS.ne_bot hS.eq_bot
  have hO := sixK_k1_aux_orbit_card (Mhat φ t i i) t
  rw [hcard, hMc] at hO
  have hq : 0 < Nat.card K ^ 3 := pow_pos Nat.card_pos 3
  have hOc : ((fun y : G => y * t * y⁻¹) '' (Mhat φ t i i : Set G)).ncard = Nat.card K ^ 4 := by
    apply Nat.eq_of_mul_eq_mul_right hq
    rw [hO]; ring
  have hTc : ((fun k : G => t * k) '' (Kc φ t i : Set G)).ncard = Nat.card K ^ 4 := by
    rw [Set.ncard_image_of_injective _ (mul_right_injective t), ← Nat.card_coe_set_eq]
    exact FullCenterWeyl.card_K hS.fc i
  have hsub : (fun y : G => y * t * y⁻¹) '' (Mhat φ t i i : Set G) ⊆
      (fun k : G => t * k) '' (Kc φ t i : Set G) := by
    rintro _ ⟨y, hy, rfl⟩
    have hy' : y ∈ Mhat φ t i i := hy
    have hyc : t * y * t⁻¹ ∈ Mhat φ t i i := sixK_k2_aux_conj_mem hH hT hy'
    have hc : t * (t * (y * t * y⁻¹)) = y * t * y⁻¹ := by
      rw [← mul_assoc, ht, one_mul]
    refine ⟨t * (y * t * y⁻¹), sixK_k2_aux_step1 hS hH ?_ ?_, hc⟩
    · have e1 : t * (y * t * y⁻¹) = (t * y * t⁻¹) * y⁻¹ := by
        rw [hti]; group
      rw [e1]; exact mul_mem hyc (inv_mem hy')
    · rw [hc]
      calc (y * t * y⁻¹) * (y * t * y⁻¹) = y * (t * t) * y⁻¹ := by group
        _ = 1 := by rw [ht]; group
  have heq := Set.eq_of_subset_of_ncard_le hsub (le_of_eq (by rw [hTc, hOc]))
  have hmem : t * m ∈ (fun y : G => y * t * y⁻¹) '' (Mhat φ t i i : Set G) := by
    rw [heq]; exact ⟨m, hKm, rfl⟩
  obtain ⟨y, hy, hyc⟩ := hmem
  have hy' : y ∈ Mhat φ t i i := hy
  exact ⟨y⁻¹, inv_mem hy', by rw [inv_inv]; exact hyc⟩

theorem sixK_k3_aux_conj_mem (hH : SixHConclusion φ t i) {y : G} (hyT : y ∈ Tplus φ t i)
    {m : G} (hm : m ∈ Mhat φ t i i) : y * m * y⁻¹ ∈ Mhat φ t i i := by
  obtain ⟨hle, hnorm, -⟩ := hH.normal_Mhat i
  have hmT : m ∈ Tplus φ t i := hle hm
  have h := Subgroup.Normal.conj_mem hnorm ⟨m, hmT⟩ (Subgroup.mem_subgroupOf.mpr hm) ⟨y, hyT⟩
  exact Subgroup.mem_subgroupOf.mp h

theorem sixK_k3_aux_sq_mem {Γ : Type} [Group Γ] {M : Subgroup Γ} {g m' : Γ}
    (hn : g * m' * g⁻¹ ∈ M) (hm' : m' ∈ M) (h : g * m' * (g * m') = 1) : g * g ∈ M := by
  have e : g * g = (g * m' * g⁻¹)⁻¹ * m'⁻¹ := by
    calc g * g = (g * m' * g⁻¹)⁻¹ * ((g * m' * g⁻¹) * (g * g) * m') * m'⁻¹ := by group
      _ = (g * m' * g⁻¹)⁻¹ * (g * m' * (g * m')) * m'⁻¹ := by group
      _ = (g * m' * g⁻¹)⁻¹ * 1 * m'⁻¹ := by rw [h]
      _ = (g * m' * g⁻¹)⁻¹ * m'⁻¹ := by rw [mul_one]
  rw [e]
  exact mul_mem (inv_mem hn) (inv_mem hm')

theorem sixK_k3_aux_core {Γ : Type} [Group Γ] {t : Γ} {M V T : Subgroup Γ}
    (ht : t * t = 1) (htT : t ∈ T) (hVT : V ≤ T)
    (hMn : ∀ y ∈ T, ∀ m ∈ M, y * m * y⁻¹ ∈ M)
    (hVn : ∀ v ∈ V, t * v * t⁻¹ ∈ V) (hMV : M ⊓ V = ⊥)
    (k1 : ∀ v ∈ V, t * v * (t * v) = 1 → ∃ x ∈ V, x⁻¹ * t * x = t * v)
    (k2 : ∀ m ∈ M, t * m * (t * m) = 1 → ∃ x ∈ M, x⁻¹ * t * x = t * m)
    {x : Γ} (hx : x ∈ M ⊔ V) (hinv : t * x * (t * x) = 1) :
    ∃ s ∈ M ⊔ V, s⁻¹ * t * s = t * x := by
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  obtain ⟨m, hm, v, hv, rfl⟩ :=
    sixH_g8_mem_sup_mul (N := M) (A := V) (fun b hb n hn => hMn b (hVT hb) n hn) hx
  have hvT : v ∈ T := hVT hv
  have hgT : t * v ∈ T := mul_mem htT hvT
  have hm' : v⁻¹ * m * v ∈ M := by
    have h := hMn v⁻¹ (inv_mem hvT) m hm
    rwa [inv_inv] at h
  have hgm : t * v * (v⁻¹ * m * v) = t * (m * v) := by group
  have hsqV : t * v * (t * v) ∈ V := by
    have e : t * v * (t * v) = t * v * t⁻¹ * v := by rw [hti]; group
    rw [e]
    exact mul_mem (hVn v hv) hv
  have hn : t * v * (v⁻¹ * m * v) * (t * v)⁻¹ ∈ M := hMn (t * v) hgT _ hm'
  have hsqM : t * v * (t * v) ∈ M :=
    sixK_k3_aux_sq_mem hn hm' (by rw [hgm]; exact hinv)
  have hsqI : t * v * (t * v) ∈ M ⊓ V := ⟨hsqM, hsqV⟩
  rw [hMV, Subgroup.mem_bot] at hsqI
  obtain ⟨x₁, hx₁V, hx₁⟩ := k1 v hv hsqI
  have hcj : x₁ * (t * v) * x₁⁻¹ = t := by
    rw [← hx₁]
    group
  have hm''M : x₁ * (v⁻¹ * m * v) * x₁⁻¹ ∈ M := hMn x₁ (hVT hx₁V) _ hm'
  have hconj : t * (x₁ * (v⁻¹ * m * v) * x₁⁻¹) = x₁ * (t * (m * v)) * x₁⁻¹ := by
    calc t * (x₁ * (v⁻¹ * m * v) * x₁⁻¹)
        = (x₁ * (t * v) * x₁⁻¹) * (x₁ * (v⁻¹ * m * v) * x₁⁻¹) := by rw [hcj]
      _ = x₁ * (t * (m * v)) * x₁⁻¹ := by rw [← hgm]; group
  have hsq2 : t * (x₁ * (v⁻¹ * m * v) * x₁⁻¹) * (t * (x₁ * (v⁻¹ * m * v) * x₁⁻¹)) = 1 := by
    rw [hconj]
    calc x₁ * (t * (m * v)) * x₁⁻¹ * (x₁ * (t * (m * v)) * x₁⁻¹)
        = x₁ * (t * (m * v) * (t * (m * v))) * x₁⁻¹ := by group
      _ = 1 := by rw [hinv]; group
  obtain ⟨x₂, hx₂M, hx₂⟩ := k2 _ hm''M hsq2
  refine ⟨x₂ * x₁, mul_mem (mem_sup_left hx₂M) (mem_sup_right hx₁V), ?_⟩
  calc (x₂ * x₁)⁻¹ * t * (x₂ * x₁) = x₁⁻¹ * (x₂⁻¹ * t * x₂) * x₁ := by group
    _ = x₁⁻¹ * (t * (x₁ * (v⁻¹ * m * v) * x₁⁻¹)) * x₁ := by rw [hx₂]
    _ = x₁⁻¹ * (x₁ * (t * (m * v)) * x₁⁻¹) * x₁ := by rw [hconj]
    _ = t * (m * v) := by group

theorem sixK_k3_aux_k1_transport {Γ : Type} [Group Γ] {t w : Γ} {V₀ : Subgroup Γ}
    (ht : t * t = 1) (hww : w * w = 1) (hwt : t * w = w * t)
    (k1 : ∀ u ∈ V₀, t * u * (t * u) = 1 → ∃ x ∈ V₀, x⁻¹ * t * x = t * u) :
    ∀ v ∈ V₀.map (MulAut.conj w⁻¹).toMonoidHom, t * v * (t * v) = 1 →
      ∃ x ∈ V₀.map (MulAut.conj w⁻¹).toMonoidHom, x⁻¹ * t * x = t * v := by
  have hwinv : w⁻¹ = w := inv_eq_of_mul_eq_one_right hww
  have hwtw : w * t * w = t := by rw [← hwt, mul_assoc, hww, mul_one]
  have hcj : ∀ y : Γ, (MulAut.conj w⁻¹).toMonoidHom y = w * y * w := fun y => by
    show w⁻¹ * y * w⁻¹⁻¹ = w * y * w
    rw [inv_inv, hwinv]
  intro v hv hvinv
  obtain ⟨u, hu, hue⟩ := Subgroup.mem_map.mp hv
  have hveq : v = w * u * w := by rw [← hue, hcj]
  have hwtu : w * (t * v) * w = t * u := by
    rw [hveq]
    calc w * (t * (w * u * w)) * w = (w * t * w) * u * (w * w) := by group
      _ = t * u := by rw [hwtw, hww, mul_one]
  have htu : t * u * (t * u) = 1 := by
    rw [← hwtu]
    calc w * (t * v) * w * (w * (t * v) * w) = w * (t * v) * (w * w) * (t * v) * w := by group
      _ = w * (t * v * (t * v)) * w := by rw [hww]; group
      _ = 1 := by rw [hvinv, mul_one, hww]
  obtain ⟨x, hxV, hx⟩ := k1 u hu htu
  refine ⟨w * x * w, Subgroup.mem_map.mpr ⟨x, hxV, hcj x⟩, ?_⟩
  have hwx : (w * x * w)⁻¹ = w * (x⁻¹ * w) := by rw [mul_inv_rev, mul_inv_rev, hwinv]
  calc (w * x * w)⁻¹ * t * (w * x * w) = w * (x⁻¹ * w) * t * (w * x * w) := by rw [hwx]
    _ = w * (x⁻¹ * (w * t * w) * x) * w := by group
    _ = w * (x⁻¹ * t * x) * w := by rw [hwtw]
    _ = w * (t * u) * w := by rw [hx]
    _ = t * v := by
      rw [← hwtu]
      calc w * (w * (t * v) * w) * w = (w * w) * (t * v) * (w * w) := by group
        _ = t * v := by rw [hww, one_mul, mul_one]

theorem sixK_k3_aux_t_conj {Γ : Type} [Group Γ] {t w : Γ} {V₀ : Subgroup Γ}
    (ht : t * t = 1) (hww : w * w = 1) (hwt : t * w = w * t)
    (hN : ∀ u ∈ V₀, t * u * t⁻¹ ∈ V₀) :
    ∀ v ∈ V₀.map (MulAut.conj w⁻¹).toMonoidHom,
      t * v * t⁻¹ ∈ V₀.map (MulAut.conj w⁻¹).toMonoidHom := by
  have hwinv : w⁻¹ = w := inv_eq_of_mul_eq_one_right hww
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have hcj : ∀ y : Γ, (MulAut.conj w⁻¹).toMonoidHom y = w * y * w := fun y => by
    show w⁻¹ * y * w⁻¹⁻¹ = w * y * w
    rw [inv_inv, hwinv]
  intro v hv
  obtain ⟨u, hu, hue⟩ := Subgroup.mem_map.mp hv
  refine Subgroup.mem_map.mpr ⟨t * u * t⁻¹, hN u hu, ?_⟩
  rw [← hue, hcj, hcj, hti]
  calc w * (t * u * t) * w = (w * t) * u * (t * w) := by group
    _ = (w * t) * u * (w * t) := by rw [hwt]
    _ = (t * w) * u * (w * t) := by rw [hwt]
    _ = t * (w * u * w) * t := by group

theorem sixK_k3 (hS : SCSetting L K n φ t i) (hH : SixHConclusion φ t i)
    (hE : EmbConclusion φ t i) (k1 : K1Concl φ t i) (k2 : K2Concl φ t i) : K3Concl φ t i := by
  have ht : t * t = 1 := SixF.t_mul_t hS.fc
  have hww : w φ i.swap * w φ i.swap = 1 := FullCenterWeyl.w_mul_self (φ := φ) i.swap
  have hwt : t * w φ i.swap = w φ i.swap * t :=
    Subgroup.mem_centralizer_iff.mp (FullCenterWeyl.w_facts hS.fc i.swap).1 t (Set.mem_singleton t)
  have hST : S φ t i ≤ Tplus φ t i := by
    rw [← hH.sup_t]; exact le_sup_left
  have htT : t ∈ Tplus φ t i := by
    rw [← hH.sup_t]; exact mem_sup_right (mem_zpowers t)
  have hMn : ∀ y ∈ Tplus φ t i, ∀ m ∈ Mhat φ t i i, y * m * y⁻¹ ∈ Mhat φ t i i :=
    fun y hy m hm => sixK_k3_aux_conj_mem hH hy hm
  have hN : ∀ u ∈ Vtor φ t i i, t * u * t⁻¹ ∈ Vtor φ t i i := fun u hu =>
    (mem_normalizer_iff.mp (RootStandard.t_mem_normalizer_V hS.fc i hS.ne_bot hS.eq_bot i) u).mp hu
  have hV'S : (Vtor φ t i i).map (MulAut.conj (w φ i.swap)⁻¹).toMonoidHom ≤ S φ t i := by
    rw [← hE.sup_Vw]; exact le_sup_right
  have hVT : (Vtor φ t i i).map (MulAut.conj (w φ i.swap)⁻¹).toMonoidHom ≤ Tplus φ t i :=
    hV'S.trans hST
  have hVn := sixK_k3_aux_t_conj ht hww hwt hN
  have k1' := sixK_k3_aux_k1_transport (V₀ := Vtor φ t i i) ht hww hwt k1
  intro x hx hinv
  have hSeq : S φ t i = Mhat φ t i i ⊔
      (Vtor φ t i i).map (MulAut.conj (w φ i.swap)⁻¹).toMonoidHom := hE.sup_Vw.symm
  rw [hSeq] at hx ⊢
  exact sixK_k3_aux_core ht htT hVT hMn hVn hE.inf_Vw k1' k2 hx hinv

end Steps

end SingleCommParts

end CFSG.LocalAnalysis.SymplecticFourStandard
