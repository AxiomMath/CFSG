module

public import CFSG.LocalAnalysis.SteinbergSFSingleCommLocalSixHCenter

public section

namespace CFSG.LocalAnalysis.SymplecticFourStandard

namespace SingleCommParts

open Subgroup GomiFusion
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.QuasithinUnique.Setup.X7b
  CFSG.RankThree.PartOne.KCRootAxis

section Aux3

variable {G : Type} [Group G]

theorem sixH_h3_comm_closure {S : Set G} {N : Subgroup G}
    (hS : ∀ a ∈ S, ∀ b ∈ S, a⁻¹ * b⁻¹ * a * b ∈ N)
    (hN : ∀ g ∈ closure S, ∀ n ∈ N, g * n * g⁻¹ ∈ N) :
    ∀ x ∈ closure S, ∀ y ∈ closure S, x⁻¹ * y⁻¹ * x * y ∈ N := by
  have hgen : ∀ x ∈ S, ∀ y ∈ closure S, x⁻¹ * y⁻¹ * x * y ∈ N := by
    intro x hx y hy
    induction hy using Subgroup.closure_induction with
    | mem y hy => exact hS x hx y hy
    | one =>
      have e : x⁻¹ * (1 : G)⁻¹ * x * 1 = 1 := by group
      rw [e]
      exact N.one_mem
    | mul y z hy hz ihy ihz =>
      have e : x⁻¹ * (y * z)⁻¹ * x * (y * z)
          = (x⁻¹ * z⁻¹ * x * z) * (z⁻¹ * (x⁻¹ * y⁻¹ * x * y) * z) := by group
      rw [e]
      have hc := hN z⁻¹ (inv_mem hz) _ ihy
      rw [inv_inv] at hc
      exact mul_mem ihz hc
    | inv y hy ihy =>
      have e : x⁻¹ * (y⁻¹)⁻¹ * x * y⁻¹ = y * (x⁻¹ * y⁻¹ * x * y)⁻¹ * y⁻¹ := by group
      rw [e]
      exact hN y hy _ (inv_mem ihy)
  intro x hx
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    intro y hy
    exact hgen x hx y hy
  | one =>
    intro y _
    have e : (1 : G)⁻¹ * y⁻¹ * 1 * y = 1 := by group
    rw [e]
    exact N.one_mem
  | mul x z hx hz ihx ihz =>
    intro y hy
    have e : (x * z)⁻¹ * y⁻¹ * (x * z) * y
        = z⁻¹ * (x⁻¹ * y⁻¹ * x * y) * z * (z⁻¹ * y⁻¹ * z * y) := by group
    rw [e]
    have hc := hN z⁻¹ (inv_mem hz) _ (ihx y hy)
    rw [inv_inv] at hc
    exact mul_mem hc (ihz y hy)
  | inv x hx ihx =>
    intro y hy
    have e : (x⁻¹)⁻¹ * y⁻¹ * x⁻¹ * y = x * (x⁻¹ * y⁻¹ * x * y)⁻¹ * x⁻¹ := by group
    rw [e]
    exact hN x hx _ (inv_mem (ihx y hy))

theorem sixH_h3_sq_closure {S : Set G} {N : Subgroup G}
    (hcomm : ∀ x ∈ closure S, ∀ y ∈ closure S, x⁻¹ * y⁻¹ * x * y ∈ N)
    (hN : ∀ g ∈ closure S, ∀ n ∈ N, g * n * g⁻¹ ∈ N)
    (hS : ∀ a ∈ S, a * a ∈ N) : ∀ x ∈ closure S, x * x ∈ N := by
  intro x hx
  induction hx using Subgroup.closure_induction with
  | mem x hx => exact hS x hx
  | one =>
    have e : (1 : G) * 1 = 1 := by group
    rw [e]
    exact N.one_mem
  | mul x z hx hz ihx ihz =>
    have e : x * z * (x * z) = (x * x) * (z * (x⁻¹ * z⁻¹ * x * z)⁻¹ * z⁻¹) * (z * z) := by
      group
    rw [e]
    have hc : x⁻¹ * z⁻¹ * x * z ∈ N := hcomm x hx z hz
    have hd : z * (x⁻¹ * z⁻¹ * x * z)⁻¹ * z⁻¹ ∈ N := hN z hz _ (inv_mem hc)
    exact mul_mem (mul_mem ihx hd) ihz
  | inv x hx ihx =>
    have e : x⁻¹ * x⁻¹ = (x * x)⁻¹ := by group
    rw [e]
    exact inv_mem ihx

theorem sixH_h3_conj_comm (P a f : G) :
    a⁻¹ * (P * f * P⁻¹)⁻¹ * a * (P * f * P⁻¹)
      = P * ((P⁻¹ * a * P)⁻¹ * f⁻¹ * (P⁻¹ * a * P) * f) * P⁻¹ := by
  group

theorem sixH_h3_comm_conj_gen {A N : Subgroup G} {P a f : G}
    (hA : ∀ x ∈ A, ∀ y ∈ A, x⁻¹ * y⁻¹ * x * y ∈ N)
    (hfix : ∀ u ∈ N, P * u * P⁻¹ = u)
    (ha : P⁻¹ * a * P ∈ A) (hf : f ∈ A) :
    a⁻¹ * (P * f * P⁻¹)⁻¹ * a * (P * f * P⁻¹) ∈ N := by
  rw [sixH_h3_conj_comm]
  have hc := hA (P⁻¹ * a * P) ha f hf
  rw [hfix _ hc]
  exact hc

theorem sixH_h3_sq_conj_gen {N : Subgroup G} {P f : G}
    (hfix : ∀ u ∈ N, P * u * P⁻¹ = u) (hf : f * f ∈ N) :
    (P * f * P⁻¹) * (P * f * P⁻¹) ∈ N := by
  have e : (P * f * P⁻¹) * (P * f * P⁻¹) = P * (f * f) * P⁻¹ := by group
  rw [e, hfix _ hf]
  exact hf

theorem sixH_h3_map_closure {S T : Set G} (σ : G →* G) (hT : ∀ s ∈ T, σ s ∈ S) :
    ∀ m ∈ closure T, σ m ∈ closure S := by
  intro m hm
  induction hm using Subgroup.closure_induction with
  | mem x hx => exact subset_closure (hT x hx)
  | one => rw [map_one]; exact one_mem _
  | mul x y hx hy ihx ihy => rw [map_mul]; exact mul_mem ihx ihy
  | inv x hx ihx => rw [map_inv]; exact inv_mem ihx

theorem sixH_h4_sup_cases {M : Subgroup G} {t : G} (htt : t * t = 1)
    (ht : t ∈ normalizer (M : Set G)) {x : G} (hx : x ∈ M ⊔ zpowers t) :
    x ∈ M ∨ ∃ v ∈ M, x = v * t := by
  have hle : zpowers t ≤ normalizer (M : Set G) := zpowers_le.mpr ht
  have hx' : x ∈ ((M ⊔ zpowers t : Subgroup G) : Set G) := hx
  rw [Subgroup.coe_mul_of_right_le_normalizer_left M (zpowers t) hle] at hx'
  obtain ⟨v, hv, y, hy, rfl⟩ := hx'
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  show v * t ^ j ∈ M ∨ ∃ v' ∈ M, v * t ^ j = v' * t
  rcases RootAxisTwoCore.zpow_eq_one_or_eq htt j with h | h
  · left
    rw [h, mul_one]
    exact hv
  · right
    exact ⟨v, hv, by rw [h]⟩

theorem sixH_h4_comm_form {X N : Subgroup G}
    (h : ∀ x ∈ X, ∀ y ∈ X, x⁻¹ * y⁻¹ * x * y ∈ N) :
    ∀ x ∈ X, ∀ y ∈ X, x * y * x⁻¹ * y⁻¹ ∈ N := by
  intro x hx y hy
  have h' := h x⁻¹ (inv_mem hx) y⁻¹ (inv_mem hy)
  rw [inv_inv, inv_inv] at h'
  exact h'

end Aux3

section Steps

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2]
  [Finite K] {n : ℕ} {φ : L ≃* antiSp K} {t : G} {i : Axis}

theorem sixH_h3_w_fix (hS : SCSetting L K n φ t i) :
    ∀ u ∈ U φ i, (w φ i)⁻¹ * u * (w φ i)⁻¹⁻¹ = u := by
  intro u hu
  have hc : u * w φ i = w φ i * u := (FullCenterWeyl.w_facts hS.fc i).2.2.2.2.2 u hu
  rw [inv_inv, mul_assoc, hc, inv_mul_cancel_left]

theorem sixH_h3_conj_Vtor (h2b : H2bConcl φ t i) {a : G} (ha : a ∈ Vtor φ t i i) :
    (w φ i)⁻¹⁻¹ * a * (w φ i)⁻¹ ∈ Vtor φ t i i := by
  have hwi : (w φ i)⁻¹ = w φ i := FullCenterWeyl.w_inv (φ := φ) i
  have h := h2b.1 a ha
  rw [hwi] at h
  rw [inv_inv, hwi]
  exact h

theorem sixH_h3_F_le_Mc (hS : SCSetting L K n φ t i) : F φ t ≤ Mc φ t i :=
  NextCores.F_le_M hS.fc i hS.ne_bot hS.eq_bot

theorem sixH_h3_Mc_le_closure (hS : SCSetting L K n φ t i) :
    Mc φ t i ≤ closure ((Vtor φ t i i : Set G) ∪ (F φ t : Set G)) := by
  intro x hx
  obtain ⟨a, ha, w', hw', rfl⟩ := RootStandard.exists_V_mul_W hS.fc i hS.ne_bot hS.eq_bot hx
  have hwF : w' ∈ F φ t := (Subgroup.mem_inf.mp hw').1
  exact mul_mem (subset_closure (Set.mem_union_left _ (SetLike.mem_coe.mpr ha)))
    (subset_closure (Set.mem_union_right _ (SetLike.mem_coe.mpr hwF)))

theorem sixH_h3_conj_Vtor' (h2b : H2bConcl φ t i) {a : G} (ha : a ∈ Vtor φ t i i) :
    (w φ i)⁻¹ * a * (w φ i)⁻¹⁻¹ ∈ Vtor φ t i i := by
  have hwi : (w φ i)⁻¹ = w φ i := FullCenterWeyl.w_inv (φ := φ) i
  have e : (w φ i)⁻¹ * a * (w φ i)⁻¹⁻¹ = (w φ i)⁻¹⁻¹ * a * (w φ i)⁻¹ := by
    rw [inv_inv, hwi]
  rw [e]
  exact sixH_h3_conj_Vtor h2b ha

theorem sixH_h3_Fw_elem {a : G} (ha : a ∈ Fw φ t i) :
    ∃ f ∈ F φ t, a = (w φ i)⁻¹ * f * (w φ i)⁻¹⁻¹ := by
  obtain ⟨f, hf, hfa⟩ := Subgroup.mem_map.mp ha
  exact ⟨f, hf, hfa.symm⟩

theorem sixH_h3_Fw_le_Mw (hS : SCSetting L K n φ t i) : Fw φ t i ≤ Mw φ t i i :=
  Subgroup.map_mono (sixH_h3_F_le_Mc hS)

theorem sixH_h3_Vtor_le_Mc {a : G} (ha : a ∈ Vtor φ t i i) : a ∈ Mc φ t i :=
  (Subgroup.mem_inf.mp ha).1

theorem sixH_h3_Mc_le_S (hS : SCSetting L K n φ t i) :
    Mc φ t i ≤ closure ((Vtor φ t i i : Set G) ∪ (F φ t : Set G) ∪ (Fw φ t i : Set G)) :=
  (sixH_h3_Mc_le_closure hS).trans (Subgroup.closure_mono (fun x hx => Set.mem_union_left _ hx))

theorem sixH_h3_Mw_le_S (hS : SCSetting L K n φ t i) (h2b : H2bConcl φ t i) :
    Mw φ t i i ≤ closure ((Vtor φ t i i : Set G) ∪ (F φ t : Set G) ∪ (Fw φ t i : Set G)) := by
  intro x hx
  obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.mp hx
  have hmap : ∀ s ∈ (Vtor φ t i i : Set G) ∪ (F φ t : Set G),
      (MulAut.conj (w φ i)⁻¹).toMonoidHom s ∈
        (Vtor φ t i i : Set G) ∪ (F φ t : Set G) ∪ (Fw φ t i : Set G) := by
    intro s hs
    rcases hs with hs | hs
    · exact Set.mem_union_left _ (Set.mem_union_left _
        (SetLike.mem_coe.mpr (sixH_h3_conj_Vtor' h2b (SetLike.mem_coe.mp hs))))
    · exact Set.mem_union_right _ (SetLike.mem_coe.mpr
        (Subgroup.mem_map_of_mem (MulAut.conj (w φ i)⁻¹).toMonoidHom (SetLike.mem_coe.mp hs)))
  exact sixH_h3_map_closure _ hmap m (sixH_h3_Mc_le_closure hS hm)

theorem sixH_h3_Mhat_le_S (hS : SCSetting L K n φ t i) (h2b : H2bConcl φ t i) :
    Mhat φ t i i ≤ closure ((Vtor φ t i i : Set G) ∪ (F φ t : Set G) ∪ (Fw φ t i : Set G)) :=
  sup_le (sixH_h3_Mc_le_S hS) (sixH_h3_Mw_le_S hS h2b)

theorem sixH_h3_S_le_Mhat (hS : SCSetting L K n φ t i) :
    closure ((Vtor φ t i i : Set G) ∪ (F φ t : Set G) ∪ (Fw φ t i : Set G)) ≤ Mhat φ t i i := by
  refine (Subgroup.closure_le _).mpr ?_
  intro x hx
  rcases hx with (hx | hx) | hx
  · exact SetLike.mem_coe.mpr
      (Subgroup.mem_sup_left (sixH_h3_Vtor_le_Mc (SetLike.mem_coe.mp hx)))
  · exact SetLike.mem_coe.mpr
      (Subgroup.mem_sup_left (sixH_h3_F_le_Mc hS (SetLike.mem_coe.mp hx)))
  · exact SetLike.mem_coe.mpr
      (Subgroup.mem_sup_right (sixH_h3_Fw_le_Mw hS (SetLike.mem_coe.mp hx)))

theorem sixH_h3_closure_eq (hS : SCSetting L K n φ t i) (h2b : H2bConcl φ t i) :
    closure ((Vtor φ t i i : Set G) ∪ (F φ t : Set G) ∪ (Fw φ t i : Set G)) = Mhat φ t i i :=
  le_antisymm (sixH_h3_S_le_Mhat hS) (sixH_h3_Mhat_le_S hS h2b)

theorem sixH_h3_V_W (hS : SCSetting L K n φ t i) (h2a : H2aConcl φ t i) (h2b : H2bConcl φ t i)
    {v x : G} (hv : v ∈ Vtor φ t i i) (hx : x ∈ Fw φ t i) :
    v⁻¹ * x⁻¹ * v * x ∈ U φ i := by
  obtain ⟨f, hf, rfl⟩ := sixH_h3_Fw_elem hx
  exact sixH_h3_comm_conj_gen h2a.comm_M (sixH_h3_w_fix hS)
    (Subgroup.mem_inf.mp (sixH_h3_conj_Vtor h2b hv)).1 (sixH_h3_F_le_Mc hS hf)

theorem sixH_h3_Mhat_le_P₁ (hS : SCSetting L K n φ t i) : Mhat φ t i i ≤ P₁ φ t i :=
  SixF.Mhat_le_P₁ hS.fc i hS.ne_bot hS.eq_bot

theorem sixH_h3_P₁_le_Tplus {x : G} (hx : x ∈ P₁ φ t i) : x ∈ Tplus φ t i :=
  Subgroup.mem_sup_left (Subgroup.mem_sup_left (Subgroup.mem_sup_right hx))

theorem sixH_h3_Mhat_le_Tplus (hS : SCSetting L K n φ t i) {x : G} (hx : x ∈ Mhat φ t i i) :
    x ∈ Tplus φ t i :=
  sixH_h3_P₁_le_Tplus (sixH_h3_Mhat_le_P₁ hS hx)

theorem sixH_h3_Mhat_norm_U (hS : SCSetting L K n φ t i) (h1 : H1Concl φ t i) :
    ∀ g ∈ Mhat φ t i i, ∀ u ∈ U φ i, g * u * g⁻¹ ∈ U φ i := by
  intro g hg u hu
  have hc : u * g = g * u := sixH_U_central_Tplus h1 u hu g (sixH_h3_Mhat_le_Tplus hS hg)
  rw [← hc, mul_inv_cancel_right]
  exact hu

theorem sixH_h3_gen_comm (hS : SCSetting L K n φ t i) (h2a : H2aConcl φ t i)
    (h2b : H2bConcl φ t i) {a b : G}
    (ha : a ∈ (Vtor φ t i i : Set G) ∪ (F φ t : Set G) ∪ (Fw φ t i : Set G))
    (hb : b ∈ (Vtor φ t i i : Set G) ∪ (F φ t : Set G) ∪ (Fw φ t i : Set G)) :
    a⁻¹ * b⁻¹ * a * b ∈ U φ i := by
  have hX : ∀ {x y : G}, x ∈ Xk φ t i → y ∈ Xk φ t i → x⁻¹ * y⁻¹ * x * y ∈ U φ i :=
    fun hx hy => SixF.comm_X_mem_U hS.fc i hS.ne_bot hS.eq_bot hx hy
  have hFX : ∀ {x : G}, x ∈ F φ t → x ∈ Xk φ t i := fun hx => Subgroup.mem_sup_left hx
  have hWX : ∀ {x : G}, x ∈ Fw φ t i → x ∈ Xk φ t i := fun hx => Subgroup.mem_sup_right hx
  have hVM : ∀ {x : G}, x ∈ Vtor φ t i i → x ∈ Mc φ t i := sixH_h3_Vtor_le_Mc
  have hFM : ∀ {x : G}, x ∈ F φ t → x ∈ Mc φ t i := fun hx => sixH_h3_F_le_Mc hS hx
  have hinv : ∀ {x y : G}, y⁻¹ * x⁻¹ * y * x ∈ U φ i → x⁻¹ * y⁻¹ * x * y ∈ U φ i := by
    intro x y h
    have e : x⁻¹ * y⁻¹ * x * y = (y⁻¹ * x⁻¹ * y * x)⁻¹ := by group
    rw [e]
    exact inv_mem h
  rcases ha with (ha | ha) | ha <;> rcases hb with (hb | hb) | hb <;>
    replace ha := SetLike.mem_coe.mp ha <;> replace hb := SetLike.mem_coe.mp hb
  · exact h2a.comm_M a (hVM ha) b (hVM hb)
  · exact h2a.comm_M a (hVM ha) b (hFM hb)
  · exact sixH_h3_V_W hS h2a h2b ha hb
  · exact h2a.comm_M a (hFM ha) b (hVM hb)
  · exact h2a.comm_M a (hFM ha) b (hFM hb)
  · exact hX (hFX ha) (hWX hb)
  · exact hinv (sixH_h3_V_W hS h2a h2b hb ha)
  · exact hX (hWX ha) (hFX hb)
  · exact hX (hWX ha) (hWX hb)

theorem sixH_h3_gen_sq (hS : SCSetting L K n φ t i) (hM2 : ∀ x ∈ Mc φ t i, x * x ∈ U φ i)
    {a : G} (ha : a ∈ (Vtor φ t i i : Set G) ∪ (F φ t : Set G) ∪ (Fw φ t i : Set G)) :
    a * a ∈ U φ i := by
  rcases ha with (ha | ha) | ha
  · exact hM2 a (sixH_h3_Vtor_le_Mc (SetLike.mem_coe.mp ha))
  · exact hM2 a (sixH_h3_F_le_Mc hS (SetLike.mem_coe.mp ha))
  · obtain ⟨f, hf, rfl⟩ := sixH_h3_Fw_elem (SetLike.mem_coe.mp ha)
    exact sixH_h3_sq_conj_gen (sixH_h3_w_fix hS) (hM2 f (sixH_h3_F_le_Mc hS hf))

theorem sixH_h3 (hS : SCSetting L K n φ t i) (hM2 : ∀ x ∈ Mc φ t i, x * x ∈ U φ i)
    (h1 : H1Concl φ t i) (h2a : H2aConcl φ t i) (h2b : H2bConcl φ t i) : H3Concl φ t i := by
  have hcl := sixH_h3_closure_eq hS h2b
  have hN : ∀ g ∈ closure ((Vtor φ t i i : Set G) ∪ (F φ t : Set G) ∪ (Fw φ t i : Set G)),
      ∀ u ∈ U φ i, g * u * g⁻¹ ∈ U φ i := by
    rw [hcl]
    exact sixH_h3_Mhat_norm_U hS h1
  have hcomm := sixH_h3_comm_closure (N := U φ i)
    (fun a ha b hb => sixH_h3_gen_comm hS h2a h2b ha hb) hN
  have hsq := sixH_h3_sq_closure hcomm hN (fun a ha => sixH_h3_gen_sq hS hM2 ha)
  rw [hcl] at hcomm hsq
  refine ⟨hcomm, le_antisymm ?_ ?_⟩
  · refine (Subgroup.closure_le _).mpr ?_
    rintro x ⟨y, hy, rfl⟩
    exact hsq y hy
  · rw [← h2a.sq_M]
    exact Subgroup.closure_mono fun x ⟨y, hy, hx⟩ => ⟨y, Subgroup.mem_sup_left hy, hx⟩

theorem sixH_h4a_aux {x w t u : G} (hx : x⁻¹ * t⁻¹ * x * t = u) (hw : w⁻¹ * t⁻¹ * w * t = u) :
    (x * w⁻¹)⁻¹ * t⁻¹ * (x * w⁻¹) * t = 1 := by
  calc (x * w⁻¹)⁻¹ * t⁻¹ * (x * w⁻¹) * t
      = w * (x⁻¹ * t⁻¹ * x * t) * t⁻¹ * w⁻¹ * t := by group
    _ = w * (w⁻¹ * t⁻¹ * w * t) * t⁻¹ * w⁻¹ * t := by rw [hx, hw]
    _ = 1 := by group

theorem sixH_h4a_A_le_Mhat (hS : SCSetting L K n φ t i) : A φ i ≤ Mhat φ t i i :=
  (SixF.Mhat_inf_C hS.fc i hS.ne_bot hS.eq_bot).ge.trans inf_le_left

theorem sixH_h4a_K_le_Mhat (hS : SCSetting L K n φ t i) : Kc φ t i ≤ Mhat φ t i i :=
  sup_le (sixH_h4a_A_le_Mhat hS) fun _ hx =>
    Subgroup.mem_sup_left (sixH_h3_F_le_Mc hS (Subgroup.mem_inf.mp hx).1)

theorem sixH_h4a_K_comm_U (hS : SCSetting L K n φ t i) {x : G} (hx : x ∈ Kc φ t i) :
    x⁻¹ * t⁻¹ * x * t ∈ U φ i := by
  have h := NextCores.kappa_K_mem_U hS.fc i hx
  have e : x⁻¹ * t⁻¹ * x * t = (t⁻¹ * (x⁻¹ * t * x))⁻¹ := by group
  rw [e]
  exact inv_mem h

theorem sixH_h4a_comm_U_mem_K (hS : SCSetting L K n φ t i) {x : G} (hxM : x ∈ Mhat φ t i i)
    (hxU : x⁻¹ * t⁻¹ * x * t ∈ U φ i) : x ∈ Kc φ t i := by
  obtain ⟨w, hwW, hwκ, -⟩ := RootStandard.exists_W_kappa hS.fc i (inv_mem hxU)
  have hwK : w ∈ Kc φ t i := Subgroup.mem_sup_right (FullCenterTorus.W_le_Fi hS.fc i hwW)
  have hwM : w ∈ Mhat φ t i i := sixH_h4a_K_le_Mhat hS hwK
  have hw : w⁻¹ * t⁻¹ * w * t = x⁻¹ * t⁻¹ * x * t := by
    have e : w⁻¹ * t⁻¹ * w * t = (t⁻¹ * (w⁻¹ * t * w))⁻¹ := by group
    rw [e, hwκ, inv_inv]
  have hy := sixH_h4a_aux (u := x⁻¹ * t⁻¹ * x * t) rfl hw
  have hyC : x * w⁻¹ ∈ centralizer ({t} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc x * w⁻¹ * t = t * (x * w⁻¹) * ((x * w⁻¹)⁻¹ * t⁻¹ * (x * w⁻¹) * t) := by group
      _ = t * (x * w⁻¹) := by rw [hy, mul_one]
  have hyA : x * w⁻¹ ∈ A φ i :=
    (SixF.Mhat_inf_C hS.fc i hS.ne_bot hS.eq_bot).le
      (Subgroup.mem_inf.mpr ⟨mul_mem hxM (inv_mem hwM), hyC⟩)
  have hx' : x = (x * w⁻¹) * w := by group
  rw [hx']
  exact mul_mem (Subgroup.mem_sup_left hyA) hwK

theorem sixH_h4a (hS : SCSetting L K n φ t i) (hM2 : ∀ x ∈ Mc φ t i, x * x ∈ U φ i)
    (h1 : H1Concl φ t i) (h3 : H3Concl φ t i) : H4aConcl φ t i :=
  ⟨sixH_h4a_K_le_Mhat hS, fun _ hx =>
    ⟨sixH_h4a_comm_U_mem_K hS hx, sixH_h4a_K_comm_U hS⟩⟩

theorem sixH_h4_he1 (h3 : H3Concl φ t i) :
    ∀ x ∈ Mhat φ t i i, ∀ y ∈ Mhat φ t i i, x * y * x⁻¹ * y⁻¹ ∈ U φ i ∧ x * x ∈ U φ i := by
  intro x hx y hy
  refine ⟨sixH_h4_comm_form h3.1 x hx y hy, ?_⟩
  have hmem : x * x ∈ closure {z : G | ∃ w ∈ Mhat φ t i i, z = w * w} :=
    subset_closure ⟨x, hx, rfl⟩
  rw [h3.2] at hmem
  exact hmem

theorem sixH_h4_P₁_cases (hS : SCSetting L K n φ t i) {x : G} (hx : x ∈ P₁ φ t i) :
    x ∈ Mhat φ t i i ∨ ∃ v ∈ Mhat φ t i i, x = v * t := by
  have hx' : x ∈ Mhat φ t i i ⊔ zpowers t :=
    (SixF.Mhat_sup_t hS.fc i hS.ne_bot hS.eq_bot).symm.le hx
  exact sixH_h4_sup_cases (SixF.t_mul_t hS.fc)
    (SixF.t_mem_normalizer_Mhat hS.fc i hS.ne_bot hS.eq_bot) hx'

theorem sixH_h4_D_le_P₁ (hS : SCSetting L K n φ t i) : D φ t i ≤ P₁ φ t i :=
  (FullCenter.FCHyp.D_le_E hS.fc i).trans (NextCores.E_le_P₁ hS.fc i hS.ne_bot hS.eq_bot)

theorem sixH_h4_K_le_D (hS : SCSetting L K n φ t i) : Kc φ t i ≤ D φ t i :=
  FullCenterWeyl.K_le_D hS.fc i

theorem sixH_h4_t_mem_D (hS : SCSetting L K n φ t i) : t ∈ D φ t i :=
  FullCenterTorus.t_mem_D hS.fc i

theorem sixH_h4_comm_t_mem_K (hS : SCSetting L K n φ t i) (h1 : H1Concl φ t i)
    (h4a : H4aConcl φ t i) {y : G} (hy : y ∈ Mhat φ t i i) (h : t * y * t⁻¹ * y⁻¹ ∈ U φ i) :
    y ∈ Kc φ t i := by
  refine (h4a.2 y hy).mp ?_
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right (SixF.t_mul_t hS.fc)
  have hcen : (t * y * t⁻¹ * y⁻¹) * y = y * (t * y * t⁻¹ * y⁻¹) :=
    sixH_U_central_Tplus h1 _ h y (sixH_h3_Mhat_le_Tplus hS hy)
  have e : y⁻¹ * t⁻¹ * y * t = y⁻¹ * (t * y * t⁻¹ * y⁻¹) * y := by
    rw [hti]
    group
  rw [e, mul_assoc, hcen, ← mul_assoc, inv_mul_cancel, one_mul]
  exact h

theorem sixH_h4_sq_mem_K (hS : SCSetting L K n φ t i) (h1 : H1Concl φ t i)
    (h3 : H3Concl φ t i) (h4a : H4aConcl φ t i) {v : G} (hv : v ∈ Mhat φ t i i)
    (h : (v * t) * (v * t) ∈ U φ i) : v ∈ Kc φ t i := by
  refine sixH_h4_comm_t_mem_K hS h1 h4a hv ?_
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right (SixF.t_mul_t hS.fc)
  have hvv : v * v ∈ U φ i := (sixH_h4_he1 h3 v hv v hv).2
  have hcen : (v * t * (v * t)) * v⁻¹ = v⁻¹ * (v * t * (v * t)) :=
    sixH_U_central_Tplus h1 _ h v⁻¹ (inv_mem (sixH_h3_Mhat_le_Tplus hS hv))
  have e : t * v * t⁻¹ * v⁻¹ = (v * t * (v * t)) * (v * v)⁻¹ := by
    calc t * v * t⁻¹ * v⁻¹ = v⁻¹ * (v * t * (v * t)) * v⁻¹ := by
          rw [hti]
          group
      _ = (v * t * (v * t)) * v⁻¹ * v⁻¹ := by rw [← hcen]
      _ = (v * t * (v * t)) * (v * v)⁻¹ := by group
  rw [e]
  exact mul_mem h (inv_mem hvv)

theorem sixH_h4_comm_vt (hS : SCSetting L K n φ t i) (h3 : H3Concl φ t i) {v z : G}
    (hv : v ∈ Mhat φ t i i) (hz : z ∈ Mhat φ t i i)
    (h : (v * t) * z * (v * t)⁻¹ * z⁻¹ ∈ U φ i) : t * z * t⁻¹ * z⁻¹ ∈ U φ i := by
  have hw : t * z * t⁻¹ ∈ Mhat φ t i i :=
    (Subgroup.mem_normalizer_iff.mp
      (SixF.t_mem_normalizer_Mhat hS.fc i hS.ne_bot hS.eq_bot) z).mp hz
  have hb := (sixH_h4_he1 h3 v hv (t * z * t⁻¹) hw).1
  have e : t * z * t⁻¹ * z⁻¹ =
      (v * (t * z * t⁻¹) * v⁻¹ * (t * z * t⁻¹)⁻¹)⁻¹ * ((v * t) * z * (v * t)⁻¹ * z⁻¹) := by
    group
  rw [e]
  exact mul_mem (inv_mem hb) h

theorem sixH_h4_D_eq_closure (hS : SCSetting L K n φ t i) :
    closure (({t} : Set G) ∪ (Kc φ t i : Set G)) = D φ t i := by
  rw [Subgroup.closure_union, ← Subgroup.zpowers_eq_closure, Subgroup.closure_eq]
  exact (NextCores.D_eq_sup_K hS.fc i).symm

theorem sixH_h4_D_gen_comm (hS : SCSetting L K n φ t i) (h3 : H3Concl φ t i) {a b : G}
    (ha : a ∈ ({t} : Set G) ∪ (Kc φ t i : Set G)) (hb : b ∈ ({t} : Set G) ∪ (Kc φ t i : Set G)) :
    a⁻¹ * b⁻¹ * a * b ∈ U φ i := by
  rcases ha with ha | ha <;> rcases hb with hb | hb
  · rw [Set.mem_singleton_iff.mp ha, Set.mem_singleton_iff.mp hb]
    have e : t⁻¹ * t⁻¹ * t * t = 1 := by group
    rw [e]
    exact one_mem _
  · rw [Set.mem_singleton_iff.mp ha]
    have h := NextCores.kappa_K_mem_U hS.fc i (SetLike.mem_coe.mp hb)
    have e : t⁻¹ * b⁻¹ * t * b = t⁻¹ * (b⁻¹ * t * b) := by group
    rw [e]
    exact h
  · rw [Set.mem_singleton_iff.mp hb]
    exact sixH_h4a_K_comm_U hS (SetLike.mem_coe.mp ha)
  · exact h3.1 a (sixH_h4a_K_le_Mhat hS (SetLike.mem_coe.mp ha)) b
      (sixH_h4a_K_le_Mhat hS (SetLike.mem_coe.mp hb))

theorem sixH_h4_he2 (hS : SCSetting L K n φ t i) (h1 : H1Concl φ t i) (h3 : H3Concl φ t i) :
    ∀ x ∈ D φ t i, ∀ y ∈ D φ t i, x * y * x⁻¹ * y⁻¹ ∈ U φ i ∧ x * x ∈ U φ i := by
  have hcl := sixH_h4_D_eq_closure hS
  have hN : ∀ g ∈ closure (({t} : Set G) ∪ (Kc φ t i : Set G)),
      ∀ u ∈ U φ i, g * u * g⁻¹ ∈ U φ i := by
    intro g hg u hu
    rw [hcl] at hg
    have hc : u * g = g * u :=
      sixH_U_central_Tplus h1 u hu g (sixH_h3_P₁_le_Tplus (sixH_h4_D_le_P₁ hS hg))
    rw [← hc, mul_inv_cancel_right]
    exact hu
  have hcomm := sixH_h3_comm_closure (N := U φ i)
    (fun a ha b hb => sixH_h4_D_gen_comm hS h3 ha hb) hN
  have hsq := sixH_h3_sq_closure hcomm hN (fun a ha => by
    rcases ha with ha | ha
    · rw [Set.mem_singleton_iff.mp ha, SixF.t_mul_t hS.fc]
      exact one_mem _
    · exact (sixH_h4_he1 h3 a (sixH_h4a_K_le_Mhat hS (SetLike.mem_coe.mp ha)) a
        (sixH_h4a_K_le_Mhat hS (SetLike.mem_coe.mp ha))).2)
  rw [hcl] at hcomm hsq
  intro x hx y hy
  exact ⟨sixH_h4_comm_form hcomm x hx y hy, hsq x hx⟩

theorem sixH_h4_classify (hS : SCSetting L K n φ t i) (h1 : H1Concl φ t i)
    (h3 : H3Concl φ t i) (h4a : H4aConcl φ t i) (E : Subgroup G) (hEP : E ≤ P₁ φ t i)
    (hE : ∀ x ∈ E, ∀ y ∈ E, x * y * x⁻¹ * y⁻¹ ∈ U φ i ∧ x * x ∈ U φ i) :
    E ≤ Mhat φ t i i ∨ E ≤ D φ t i := by
  by_cases hEM : E ≤ Mhat φ t i i
  · exact Or.inl hEM
  right
  obtain ⟨x, hxE, hxM⟩ := SetLike.not_le_iff_exists.mp hEM
  rcases sixH_h4_P₁_cases hS (hEP hxE) with h | ⟨v, hv, rfl⟩
  · exact absurd h hxM
  intro z hz
  rcases sixH_h4_P₁_cases hS (hEP hz) with hzM | ⟨v', hv', rfl⟩
  · exact sixH_h4_K_le_D hS (sixH_h4_comm_t_mem_K hS h1 h4a hzM
      (sixH_h4_comm_vt hS h3 hv hzM (hE _ hxE z hz).1))
  · exact mul_mem (sixH_h4_K_le_D hS (sixH_h4_sq_mem_K hS h1 h3 h4a hv' (hE _ hz _ hz).2))
      (sixH_h4_t_mem_D hS)

theorem sixH_h4_card_D_lt (hS : SCSetting L K n φ t i) :
    Nat.card (D φ t i) < Nat.card (Mhat φ t i i) := by
  have hD : Nat.card (D φ t i) = 2 * Nat.card K ^ 4 := hS.fc.card_D i
  have hM : Nat.card (Mhat φ t i i) = Nat.card K ^ 7 :=
    SixF.card_Mhat hS.fc i hS.ne_bot hS.eq_bot
  have hq : 4 ≤ Nat.card K := hS.fc.four_le_card
  have h1 : 0 < Nat.card K ^ 4 := by positivity
  have h2 : 4 ^ 3 ≤ Nat.card K ^ 3 := Nat.pow_le_pow_left hq 3
  rw [hD, hM]
  calc 2 * Nat.card K ^ 4 < 64 * Nat.card K ^ 4 := by omega
    _ ≤ Nat.card K ^ 3 * Nat.card K ^ 4 := Nat.mul_le_mul_right _ (by norm_num at h2; exact h2)
    _ = Nat.card K ^ 7 := by ring

theorem sixH_h4_not_M_le_D (hS : SCSetting L K n φ t i) : ¬ Mhat φ t i i ≤ D φ t i := fun h =>
  absurd (Subgroup.card_le_of_le h) (not_le.mpr (sixH_h4_card_D_lt hS))

theorem sixH_h4_not_D_le_M (hS : SCSetting L K n φ t i) : ¬ D φ t i ≤ Mhat φ t i i := by
  intro h
  have ht : t ∈ Mhat φ t i i ⊓ zpowers t :=
    ⟨h (sixH_h4_t_mem_D hS), Subgroup.mem_zpowers t⟩
  have ht' : t ∈ (⊥ : Subgroup G) := (SixF.Mhat_inf_t hS.fc i hS.ne_bot hS.eq_bot).le ht
  exact hS.fc.setup.t_ne_one (Subgroup.mem_bot.mp ht')

theorem sixH_h4_U_le_Mhat (hS : SCSetting L K n φ t i) : U φ i ≤ Mhat φ t i i :=
  (SixG.U_le_K i i).trans (sixH_h4a_K_le_Mhat hS)

theorem sixH_h4_U_le_D (hS : SCSetting L K n φ t i) : U φ i ≤ D φ t i :=
  (SixG.U_le_K i i).trans (sixH_h4_K_le_D hS)

theorem sixH_h4_U_le_P₁ (hS : SCSetting L K n φ t i) : U φ i ≤ P₁ φ t i :=
  (sixH_h4_U_le_Mhat hS).trans (sixH_h3_Mhat_le_P₁ hS)

theorem sixH_h4_normal (hS : SCSetting L K n φ t i) (h1 : H1Concl φ t i) :
    ((U φ i).subgroupOf (P₁ φ t i)).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  have hc : (n : G) * (g : G) = (g : G) * n :=
    sixH_U_central_Tplus h1 n hn g (sixH_h3_P₁_le_Tplus g.2)
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  rw [← hc, mul_inv_cancel_right]
  exact hn

theorem sixH_h4_T₁_le (hS : SCSetting L K n φ t i) (h1 : H1Concl φ t i) (h3 : H3Concl φ t i)
    (h4a : H4aConcl φ t i) : T₁ φ t i ≤ normalizer (Mhat φ t i i : Set G) := by
  intro g hg
  have hgD : g ∈ normalizer (D φ t i : Set G) := NextCores.T₁_le_Dn hS.fc i hg
  have hgT : g ∈ Tplus φ t i := Subgroup.mem_sup_left (Subgroup.mem_sup_left hg)
  have hU : ∀ u ∈ U φ i, g * u * g⁻¹ ∈ U φ i := fun u hu => by
    rw [← sixH_U_central_Tplus h1 u hu g hgT, mul_inv_cancel_right]
    exact hu
  obtain ⟨f, hf⟩ : ∃ f : G →* G, ∀ m, f m = g * m * g⁻¹ :=
    ⟨(MulAut.conj g).toMonoidHom, fun m => rfl⟩
  have hfinj : Function.Injective f := fun a b hab => by
    rw [hf, hf] at hab
    exact mul_left_cancel (mul_right_cancel hab)
  obtain ⟨E, hE⟩ : ∃ E : Subgroup G, E = (Mhat φ t i i).map f := ⟨_, rfl⟩
  have hmemE : ∀ x, x ∈ E ↔ ∃ m ∈ Mhat φ t i i, g * m * g⁻¹ = x := by
    intro x
    rw [hE, Subgroup.mem_map]
    simp only [hf]
  have hcard : Nat.card E = Nat.card (Mhat φ t i i) := by
    rw [hE]
    exact Subgroup.card_map_of_injective hfinj
  have hEP : E ≤ P₁ φ t i := by
    intro x hx
    obtain ⟨m, hm, rfl⟩ := (hmemE x).mp hx
    exact FullCenter.conj_mem_pCore_map hgD (sixH_h3_Mhat_le_P₁ hS hm)
  have hEel : ∀ x ∈ E, ∀ y ∈ E, x * y * x⁻¹ * y⁻¹ ∈ U φ i ∧ x * x ∈ U φ i := by
    intro x hx y hy
    obtain ⟨a, ha, rfl⟩ := (hmemE x).mp hx
    obtain ⟨b, hb, rfl⟩ := (hmemE y).mp hy
    obtain ⟨hc, hs⟩ := sixH_h4_he1 h3 a ha b hb
    refine ⟨?_, ?_⟩
    · have e : g * a * g⁻¹ * (g * b * g⁻¹) * (g * a * g⁻¹)⁻¹ * (g * b * g⁻¹)⁻¹
          = g * (a * b * a⁻¹ * b⁻¹) * g⁻¹ := by group
      rw [e]
      exact hU _ hc
    · have e : g * a * g⁻¹ * (g * a * g⁻¹) = g * (a * a) * g⁻¹ := by group
      rw [e]
      exact hU _ hs
  rcases sixH_h4_classify hS h1 h3 h4a E hEP hEel with hEM | hED
  · have hEq : E = Mhat φ t i i := Subgroup.eq_of_le_of_card_ge hEM hcard.ge
    refine Subgroup.mem_normalizer_iff.mpr fun h => ⟨fun hh => hEM ((hmemE _).mpr ⟨h, hh, rfl⟩),
      fun hh => ?_⟩
    have hh' : g * h * g⁻¹ ∈ E := hEq ▸ hh
    obtain ⟨m, hm, hmh⟩ := (hmemE _).mp hh'
    have hmh' : m = h := mul_left_cancel (mul_right_cancel hmh)
    rw [← hmh']
    exact hm
  · exact absurd (hcard ▸ Subgroup.card_le_of_le hED) (not_le.mpr (sixH_h4_card_D_lt hS))

theorem sixH_h4 (hS : SCSetting L K n φ t i) (hM2 : ∀ x ∈ Mc φ t i, x * x ∈ U φ i)
    (h1 : H1Concl φ t i) (h3 : H3Concl φ t i) (h4a : H4aConcl φ t i) : H4Concl φ t i := by
  have hnorm : ((U φ i).subgroupOf (P₁ φ t i)).Normal := sixH_h4_normal hS h1
  refine ⟨⟨hnorm, ?_⟩, sixH_h4_T₁_le hS h1 h3 h4a⟩
  intro E
  exact SixG.maximal_map_iff (sixH_h4_U_le_P₁ hS) le_rfl (sixH_h4_U_le_Mhat hS)
    (sixH_h4_U_le_D hS) (sixH_h3_Mhat_le_P₁ hS) (sixH_h4_D_le_P₁ hS) (sixH_h4_he1 h3)
    (sixH_h4_he2 hS h1 h3) (fun E hEP hE => sixH_h4_classify hS h1 h3 h4a E hEP hE)
    (sixH_h4_not_M_le_D hS) (sixH_h4_not_D_le_M hS) E

end Steps

end SingleCommParts

end CFSG.LocalAnalysis.SymplecticFourStandard
