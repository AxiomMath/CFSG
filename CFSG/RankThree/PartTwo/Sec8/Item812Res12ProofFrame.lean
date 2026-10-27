module

public import CFSG.RankThree.PartTwo.Sec8.Item812Res5ProofA9
public import CFSG.RankThree.PartTwo.Sec8.Item812Res5ProofSp62
public import CFSG.RankThree.PartTwo.Sec8.Item8KFacts3ProofSp62
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoIIISp62
public import CFSG.GroupTheory.QuasisimpleCommutingProductBound
public import CFSG.RankThree.PartTwo.Sec8.Item812Res5ProofWreath

public section

namespace CFSG.RankThree.PartTwo.Sec8

open Equiv Equiv.Perm Subgroup
open CFSG.RankThree.PartTwo.Sec4.Item434Kit CFSG.RankThree.PartTwo.Sec4.Item434AltPerm
open CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII
open CFSG.Assembly.RankThreeEven (projSp)

namespace Item812Res12

@[expose] def FrameProp {H : Type*} [Group H] (z : Fin 3 → H) : Prop :=
  ∀ (S K : Subgroup H) (x : Fin 3 → ZMod 3), S ≤ baseA z → Nat.card S = 9 →
    vecElt z x ∉ S → Group.IsPerfect K → S ≤ K → K ≤ Subgroup.centralizer {vecElt z x} →
    ∃ k : Fin 3, x k ≠ 0 ∧ (∀ i, i ≠ k → x i = 0) ∧ ∀ w, vecElt z w ∈ S → w k = 0

@[expose] def blockPt (k : Fin 3) : Fin 9 :=
  ⟨3 * k.val, by omega⟩

set_option maxRecDepth 100000 in
theorem vecPerm_blockPt_iff : ∀ (x : Fin 3 → ZMod 3) (k : Fin 3),
    vecPerm 9 x (blockPt k) = blockPt k ↔ x k = 0 := by
  decide +kernel

theorem card_le_three_of_coords {H : Type*} [Group H] {z : Fin 3 → H} {t : H}
    (hf : WreathFacts z t) {S : Subgroup H} (hSA : S ≤ baseA z) {k l : Fin 3} (hkl : k ≠ l)
    (hS : ∀ w, vecElt z w ∈ S → w k = 0 ∧ w l = 0) : Nat.card S ≤ 3 := by
  classical
  set T : Finset H := (Finset.univ.filter fun w : Fin 3 → ZMod 3 => w k = 0 ∧ w l = 0).image
    (vecElt z) with hTdef
  have hT3 : T.card = 3 := by
    rw [hTdef, Finset.card_image_of_injective _ (fun a b hab => vecElt_injective hf hab)]
    exact Item8KFacts3.card_filter_coord_two k l hkl
  have hST : (S : Set H) ⊆ T := by
    intro s hs
    obtain ⟨w, rfl⟩ := (mem_baseA_iff hf).mp (hSA hs)
    rw [hTdef, Finset.coe_image]
    exact ⟨w, by simpa using hS w hs, rfl⟩
  have h1 := Set.ncard_le_ncard hST (Finset.finite_toSet T)
  rw [Set.ncard_coe_finset, hT3, ← Nat.card_coe_set_eq] at h1
  exact h1

theorem exists_single_of_vanish {H : Type*} [Group H] {z : Fin 3 → H} {t : H}
    (hf : WreathFacts z t) {S : Subgroup H} (hSA : S ≤ baseA z) (hS9 : Nat.card S = 9)
    {x : Fin 3 → ZMod 3} (hx0 : x ≠ 0) (hvan : ∀ k, x k ≠ 0 → ∀ w, vecElt z w ∈ S → w k = 0) :
    ∃ k : Fin 3, x k ≠ 0 ∧ (∀ i, i ≠ k → x i = 0) ∧ ∀ w, vecElt z w ∈ S → w k = 0 := by
  rcases Item8KFacts3.coords_cases x with ⟨h0, h1, h2⟩ | ⟨k, hk, hx⟩ | ⟨l, hl, hx⟩ |
      ⟨h0, h1, h2⟩
  · exfalso
    apply hx0
    funext i
    fin_cases i <;> assumption
  · exact ⟨k, hk, hx, hvan k hk⟩
  · exfalso
    have hl1 : l + 1 ≠ l := by fin_cases l <;> decide
    have hl2 : l + 2 ≠ l := by fin_cases l <;> decide
    have h12 : l + 1 ≠ l + 2 := by fin_cases l <;> decide
    have h := card_le_three_of_coords hf hSA h12 fun w hw =>
      ⟨hvan _ (hx _ hl1) w hw, hvan _ (hx _ hl2) w hw⟩
    omega
  · exfalso
    have h := card_le_three_of_coords hf hSA (show (0 : Fin 3) ≠ 1 by decide) fun w hw =>
      ⟨hvan 0 h0 w hw, hvan 1 h1 w hw⟩
    omega

theorem frame_perm9 {S K : Subgroup (Perm (Fin 9))} {x : Fin 3 → ZMod 3}
    (hSA : S ≤ baseA Item812Res5.zPerm9) (hS9 : Nat.card S = 9) (huS : vecPerm 9 x ∉ S)
    (hK : Group.IsPerfect K) (hSK : S ≤ K) (hKu : K ≤ Subgroup.centralizer {vecPerm 9 x}) :
    ∃ k : Fin 3, x k ≠ 0 ∧ (∀ i, i ≠ k → x i = 0) ∧ ∀ w, vecPerm 9 w ∈ S → w k = 0 := by
  classical
  have hf := Item812Res5.wreathFacts_perm9
  have hu3 : vecPerm 9 x ^ 3 = 1 := by
    rw [← Item812Res5.vecElt_zPerm9]
    exact (isElemAbelian_baseA hf).2 _ (vecElt_mem_baseA hf x)
  have hfix := Item8KFacts3.fixes_support_of_isPerfect (by simp) hu3 hK hKu
  have hvan : ∀ k, x k ≠ 0 → ∀ w, vecElt Item812Res5.zPerm9 w ∈ S → w k = 0 := by
    intro k hk w hw
    rw [Item812Res5.vecElt_zPerm9] at hw
    have hmov : blockPt k ∈ (vecPerm 9 x).support := by
      rw [mem_support]
      exact fun h => hk ((vecPerm_blockPt_iff x k).mp h)
    exact (vecPerm_blockPt_iff w k).mp (hfix _ (hSK hw) _ hmov)
  have hx0 : x ≠ 0 := by
    rintro rfl
    apply huS
    have h1 : vecPerm 9 (0 : Fin 3 → ZMod 3) = 1 := by
      rw [← Item812Res5.vecElt_zPerm9]
      simp [vecElt]
    rw [h1]
    exact S.one_mem
  obtain ⟨k, hk, hxk, hSk⟩ := exists_single_of_vanish hf hSA hS9 hx0 hvan
  exact ⟨k, hk, hxk, fun w hw => hSk w (by rw [Item812Res5.vecElt_zPerm9]; exact hw)⟩

theorem coe_vecElt_zA9 (x : Fin 3 → ZMod 3) :
    ((vecElt Item812Res5.zA9 x : alternatingGroup (Fin 9)) : Perm (Fin 9)) = vecPerm 9 x := by
  simp [vecElt, Item812Res5.zA9, Item812Res5.zPerm9, vecPerm]

theorem frameProp_A9 : FrameProp Item812Res5.zA9 := by
  intro S K x hSA hS9 huS hK hSK hKu
  set f : alternatingGroup (Fin 9) →* Perm (Fin 9) := (alternatingGroup (Fin 9)).subtype with hfd
  have hfi : Function.Injective f := (alternatingGroup (Fin 9)).subtype_injective
  have hfv : ∀ w, f (vecElt Item812Res5.zA9 w) = vecPerm 9 w := coe_vecElt_zA9
  have hSA' : S.map f ≤ baseA Item812Res5.zPerm9 := by
    rintro _ ⟨s, hs, rfl⟩
    obtain ⟨w, rfl⟩ := (mem_baseA_iff Item812Res5.wreathFacts_A9).mp (hSA hs)
    rw [hfv, ← Item812Res5.vecElt_zPerm9]
    exact vecElt_mem_baseA Item812Res5.wreathFacts_perm9 w
  have hS9' : Nat.card (S.map f) = 9 := by rw [card_map_of_injective hfi, hS9]
  have huS' : vecPerm 9 x ∉ S.map f := by
    rintro ⟨s, hs, hsx⟩
    apply huS
    have : s = vecElt Item812Res5.zA9 x := hfi (by rw [hsx, hfv])
    rwa [← this]
  have hK' : Group.IsPerfect (K.map f) := @Group.IsPerfect.map _ _ _ _ _ f hK
  have hKu' : K.map f ≤ Subgroup.centralizer {vecPerm 9 x} := by
    rintro _ ⟨y, hy, rfl⟩
    have h1 := hKu hy
    rw [mem_centralizer_singleton_iff] at h1 ⊢
    rw [← hfv, ← map_mul, ← map_mul, h1]
  obtain ⟨k, hk, hxk, hSk⟩ := frame_perm9 hSA' hS9' huS' hK' (map_mono hSK) hKu'
  exact ⟨k, hk, hxk, fun w hw => hSk w ⟨_, hw, hfv w⟩⟩

theorem frameProp_zH : FrameProp zH :=
  fun _ _ _ hSA hS9 huS hK hSK hKu =>
    Item8KFacts3.coord_eq_zero_of_perfect hSA hS9 huS hK hSK hKu

section Shift

variable {H : Type*} [Group H] {z : Fin 3 → H} {t₀ : H}

theorem conj_pow_vecElt (hf : WreathFacts z t₀) (m : ℕ) (v : Fin 3 → ZMod 3) :
    t₀ ^ m * vecElt z v * (t₀ ^ m)⁻¹ = vecElt z (Item8KFacts3.rotV^[m] v) := by
  induction m generalizing v with
  | zero => simp
  | succ m ih =>
    rw [Function.iterate_succ_apply', pow_succ', mul_inv_rev,
      show t₀ * t₀ ^ m * vecElt z v * ((t₀ ^ m)⁻¹ * t₀⁻¹) =
        t₀ * (t₀ ^ m * vecElt z v * (t₀ ^ m)⁻¹) * t₀⁻¹ by group, ih, conj_vecElt hf]
    rfl

theorem conj_mul_pow_vecElt (hf : WreathFacts z t₀) (v w : Fin 3 → ZMod 3) (m : ℕ) :
    vecElt z v * t₀ ^ m * vecElt z w * (vecElt z v * t₀ ^ m)⁻¹ =
      vecElt z (Item8KFacts3.rotV^[m] w) := by
  rw [mul_inv_rev, show vecElt z v * t₀ ^ m * vecElt z w * ((t₀ ^ m)⁻¹ * (vecElt z v)⁻¹) =
      vecElt z v * (t₀ ^ m * vecElt z w * (t₀ ^ m)⁻¹) * (vecElt z v)⁻¹ by group,
    conj_pow_vecElt hf]
  have hcomm : vecElt z v * vecElt z (Item8KFacts3.rotV^[m] w) =
      vecElt z (Item8KFacts3.rotV^[m] w) * vecElt z v := by
    rw [← vecElt_add hf, ← vecElt_add hf, add_comm]
  rw [hcomm, mul_inv_cancel_right]

theorem exists_smul_of_mem_zpowers (hf : WreathFacts z t₀) {x : Fin 3 → ZMod 3} {y : H}
    (hy : y ∈ zpowers (vecElt z x)) : ∃ n : ZMod 3, y = vecElt z (n • x) := by
  obtain ⟨m, rfl⟩ := mem_zpowers_iff.mp hy
  refine ⟨(m : ZMod 3), ?_⟩
  have h1 : vecElt z x = vecHom hf (Multiplicative.ofAdd x) := rfl
  rw [h1, ← map_zpow, ← ofAdd_zsmul]
  show vecElt z (m • x) = vecElt z ((m : ZMod 3) • x)
  congr 1
  funext i
  simp [zsmul_eq_mul]

theorem exists_smul_add_of_mem_sup [Finite H] (hf : WreathFacts z t₀) {x y : Fin 3 → ZMod 3}
    {g : H} (hg : g ∈ zpowers (vecElt z x) ⊔ zpowers (vecElt z y)) :
    ∃ n m : ZMod 3, g = vecElt z (n • x + m • y) := by
  have hc : ∀ a ∈ zpowers (vecElt z x), ∀ b ∈ zpowers (vecElt z y), a * b = b * a := by
    intro a ha b hb
    obtain ⟨n, rfl⟩ := exists_smul_of_mem_zpowers hf ha
    obtain ⟨m, rfl⟩ := exists_smul_of_mem_zpowers hf hb
    rw [← vecElt_add hf, ← vecElt_add hf, add_comm]
  have hg' : g ∈ ((zpowers (vecElt z x) ⊔ zpowers (vecElt z y) : Subgroup H) : Set H) := hg
  rw [(CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ hc).2] at hg'
  obtain ⟨a, ha, b, hb, rfl⟩ := hg'
  obtain ⟨n, rfl⟩ := exists_smul_of_mem_zpowers hf ha
  obtain ⟨m, rfl⟩ := exists_smul_of_mem_zpowers hf hb
  exact ⟨n, m, (vecElt_add hf _ _).symm⟩

theorem mem_of_coord_eq_zero (hf : WreathFacts z t₀) {S : Subgroup H} (hSA : S ≤ baseA z)
    (hS9 : Nat.card S = 9) {k : Fin 3} (hSk : ∀ w, vecElt z w ∈ S → w k = 0)
    {w : Fin 3 → ZMod 3} (hw : w k = 0) : vecElt z w ∈ S := by
  classical
  set T : Finset H := (Finset.univ.filter fun w : Fin 3 → ZMod 3 => w k = 0).image (vecElt z)
    with hTdef
  have hT9 : T.card = 9 := by
    rw [hTdef, Finset.card_image_of_injective _ (fun a b hab => vecElt_injective hf hab)]
    exact Item8KFacts3.card_filter_coord k
  have hST : (S : Set H) ⊆ T := by
    intro s hs
    obtain ⟨w', rfl⟩ := (mem_baseA_iff hf).mp (hSA hs)
    rw [hTdef, Finset.coe_image]
    exact ⟨w', by simpa using hSk w' hs, rfl⟩
  have hSeq : (S : Set H) = T := by
    refine Set.eq_of_subset_of_ncard_le hST ?_ (Finset.finite_toSet T)
    rw [Set.ncard_coe_finset, hT9, ← Nat.card_coe_set_eq]
    exact hS9.ge
  have h1 : vecElt z w ∈ (T : Set H) := by
    rw [hTdef, Finset.coe_image]
    exact ⟨w, by simp [hw], rfl⟩
  rw [← hSeq] at h1
  exact h1

set_option maxRecDepth 100000 in
theorem shift_check : ∀ j : Fin 3, j ≠ 0 → ∀ k : Fin 3, ∀ e : ZMod 3, e ≠ 0 →
    (∀ n : ZMod 3, Item8KFacts3.rotV^[(j : ℕ)] (Pi.single k e) ≠ n • Pi.single k e) ∧
    (∀ n m : ZMod 3,
      Item8KFacts3.rotV^[(j : ℕ)] (Item8KFacts3.rotV^[(j : ℕ)] (Pi.single k e)) ≠
        n • Pi.single k e + m • Item8KFacts3.rotV^[(j : ℕ)] (Pi.single k e)) ∧
    ∃ w : Fin 3 → ZMod 3, w k = 0 ∧ Item8KFacts3.rotV^[(j : ℕ)] w k ≠ 0 := by
  decide +kernel

theorem shift_of_frame [Finite H] (hf : WreathFacts z t₀)
    (hW : Nat.card (wreathW z t₀) = 3 ^ (Nat.card H).factorization 3)
    (h81 : Nat.card (wreathW z t₀) = 81) (hfr : FrameProp z)
    {E P S K : Subgroup H} {u t : H} (hE : CFSG.Assembly.IsElemAbelian 3 E)
    (hE27 : Nat.card E = 27) (hEP : E ≤ P) (hP : IsPGroup 3 P) (htP : t ∈ P) (htE : t ∉ E)
    (hSE : S ≤ E) (hS9 : Nat.card S = 9) (huE : u ∈ E) (huS : u ∉ S)
    (hK : Group.IsPerfect K) (hSK : S ≤ K) (hKu : K ≤ Subgroup.centralizer {u}) :
    t * u * t⁻¹ ∉ zpowers u ∧
      t ^ 2 * u * (t ^ 2)⁻¹ ∉ zpowers u ⊔ zpowers (t * u * t⁻¹) ∧
      ∃ s ∈ S, t * s * t⁻¹ ∉ S := by
  classical
  obtain ⟨g, hg⟩ := Item812Res5.exists_map_conj_le_wreathW hW hP
  set c : H →* H := (MulAut.conj g⁻¹).toMonoidHom with hc
  have hcinj : Function.Injective c := (MulAut.conj g⁻¹).injective
  have hEA : E.map c = baseA z :=
    eq_baseA_of_le_wreathW hf h81 ((map_mono hEP).trans hg)
      (Item812Res5.isElemAbelian_map_hom c hE) (by rw [card_map_of_injective hcinj, hE27])
  have hcE : ∀ y ∈ E, c y ∈ baseA z := fun y hy => hEA ▸ mem_map_of_mem c hy
  obtain ⟨v, j, hvj⟩ := mem_wreathW hf (hg (mem_map_of_mem c htP))
  have hj : j ≠ 0 := by
    rintro rfl
    apply htE
    have h1 : c t ∈ E.map c := by
      rw [hEA, hvj, Fin.val_zero, pow_zero, mul_one]
      exact vecElt_mem_baseA hf v
    obtain ⟨y, hy, hyt⟩ := h1
    rwa [← hcinj hyt]
  have hconj : ∀ y ∈ E, ∀ w, c y = vecElt z w →
      c (t * y * t⁻¹) = vecElt z (Item8KFacts3.rotV^[(j : ℕ)] w) := by
    intro y _ w hyw
    rw [map_mul, map_mul, map_inv, hyw, hvj, conj_mul_pow_vecElt hf]
  obtain ⟨x, hx⟩ := (mem_baseA_iff hf).mp (hcE u huE)
  have hSA : S.map c ≤ baseA z := hEA ▸ map_mono hSE
  have hS9' : Nat.card (S.map c) = 9 := by rw [card_map_of_injective hcinj, hS9]
  have huS' : vecElt z x ∉ S.map c := by
    rintro ⟨s, hs, hsx⟩
    rw [hx] at hsx
    exact huS (hcinj hsx ▸ hs)
  have hK' : Group.IsPerfect (K.map c) := @Group.IsPerfect.map _ _ _ _ _ c hK
  have hKu' : K.map c ≤ Subgroup.centralizer {vecElt z x} := by
    rintro _ ⟨y, hy, rfl⟩
    have h1 := hKu hy
    rw [mem_centralizer_singleton_iff] at h1 ⊢
    rw [hx, ← map_mul, ← map_mul, h1]
  obtain ⟨k, hk, hxk, hSk⟩ := hfr _ _ x hSA hS9' huS' hK' (map_mono hSK) hKu'
  have hxs : x = Pi.single k (x k) := by
    funext i
    by_cases hik : i = k
    · subst hik
      simp
    · rw [hxk i hik, Pi.single_eq_of_ne hik]
  obtain ⟨h1, h2, w, hwk, hwr⟩ := shift_check j hj k (x k) hk
  rw [← hxs] at h1 h2
  have hcu1 : c (t * u * t⁻¹) = vecElt z (Item8KFacts3.rotV^[(j : ℕ)] x) :=
    hconj u huE x hx.symm
  have hu1E : t * u * t⁻¹ ∈ E := by
    have hvt : vecElt z (Item8KFacts3.rotV^[(j : ℕ)] x) ∈ E.map c := by
      rw [hEA]
      exact vecElt_mem_baseA hf _
    obtain ⟨y, hy, hyc⟩ := hvt
    rw [← hcu1] at hyc
    rwa [← hcinj hyc]
  refine ⟨?_, ?_, ?_⟩
  ·
    intro hmem
    have h3 := mem_map_of_mem c hmem
    rw [MonoidHom.map_zpowers, hcu1, ← hx] at h3
    obtain ⟨n, hn⟩ := exists_smul_of_mem_zpowers hf h3
    exact h1 n (vecElt_injective hf hn)
  ·
    intro hmem
    have h3 := mem_map_of_mem c hmem
    have e2 : t ^ 2 * u * (t ^ 2)⁻¹ = t * (t * u * t⁻¹) * t⁻¹ := by
      rw [sq, mul_inv_rev]
      simp only [mul_assoc]
    rw [Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers, hcu1, ← hx, e2,
      hconj _ hu1E _ hcu1] at h3
    obtain ⟨n, m, hnm⟩ := exists_smul_add_of_mem_sup hf h3
    exact h2 n m (vecElt_injective hf hnm)
  ·
    have hSk' : ∀ w', vecElt z w' ∈ S.map c → w' k = 0 := hSk
    obtain ⟨s, hs, hsw⟩ := mem_of_coord_eq_zero hf hSA hS9' hSk' hwk
    refine ⟨s, hs, fun hts => hwr ?_⟩
    apply hSk'
    rw [← hconj s (hSE hs) w hsw]
    exact mem_map_of_mem c hts

theorem shift_pullback {M N : Type*} [Group M] [Group N] (f : N →* M) {S : Subgroup N}
    {u t : N}
    (hM : f t * f u * (f t)⁻¹ ∉ zpowers (f u) ∧
      f t ^ 2 * f u * (f t ^ 2)⁻¹ ∉ zpowers (f u) ⊔ zpowers (f t * f u * (f t)⁻¹) ∧
      ∃ s ∈ S.map f, f t * s * (f t)⁻¹ ∉ S.map f) :
    t * u * t⁻¹ ∉ zpowers u ∧ t ^ 2 * u * (t ^ 2)⁻¹ ∉ zpowers u ⊔ zpowers (t * u * t⁻¹) ∧
      ∃ s ∈ S, t * s * t⁻¹ ∉ S := by
  obtain ⟨h1, h2, h3⟩ := hM
  refine ⟨fun h => h1 ?_, fun h => h2 ?_, ?_⟩
  · have := mem_map_of_mem f h
    rwa [MonoidHom.map_zpowers, map_mul, map_mul, map_inv] at this
  · have := mem_map_of_mem f h
    rwa [Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers, map_mul, map_mul,
      map_inv, map_mul, map_mul, map_inv, map_pow] at this
  · obtain ⟨_, ⟨s, hs, rfl⟩, hns⟩ := h3
    refine ⟨s, hs, fun h => hns ?_⟩
    have := mem_map_of_mem f h
    rwa [map_mul, map_mul, map_inv] at this

theorem shift_pushforward {M N : Type*} [Group M] [Group N] (f : N →* M)
    (hf : Function.Injective f) {S : Subgroup N} {u t : N}
    (hN : t * u * t⁻¹ ∉ zpowers u ∧ t ^ 2 * u * (t ^ 2)⁻¹ ∉ zpowers u ⊔ zpowers (t * u * t⁻¹) ∧
      ∃ s ∈ S, t * s * t⁻¹ ∉ S) :
    f t * f u * (f t)⁻¹ ∉ zpowers (f u) ∧
      f t ^ 2 * f u * (f t ^ 2)⁻¹ ∉ zpowers (f u) ⊔ zpowers (f t * f u * (f t)⁻¹) ∧
      ∃ s ∈ S.map f, f t * s * (f t)⁻¹ ∉ S.map f := by
  obtain ⟨h1, h2, s, hs, h3⟩ := hN
  refine ⟨fun h => h1 ?_, fun h => h2 ?_, f s, mem_map_of_mem f hs, fun h => h3 ?_⟩
  · rw [← MonoidHom.map_zpowers, ← map_inv, ← map_mul, ← map_mul] at h
    exact (mem_map_iff_mem hf).mp h
  · rw [← MonoidHom.map_zpowers, ← map_inv, ← map_mul, ← map_mul, ← MonoidHom.map_zpowers,
      ← Subgroup.map_sup, ← map_pow, ← map_inv, ← map_mul, ← map_mul] at h
    exact (mem_map_iff_mem hf).mp h
  · rw [← map_inv, ← map_mul, ← map_mul] at h
    exact (mem_map_iff_mem hf).mp h

theorem shift_of_mulEquiv {M N : Type*} [Group M] [Group N] [Finite N] {z : Fin 3 → N} {t₀ : N}
    (hf : WreathFacts z t₀)
    (hW : Nat.card (wreathW z t₀) = 3 ^ (Nat.card N).factorization 3)
    (h81 : Nat.card (wreathW z t₀) = 81) (hfr : FrameProp z) (e : M ≃* N)
    {E P S K : Subgroup M} {u t : M} (hE : CFSG.Assembly.IsElemAbelian 3 E)
    (hE27 : Nat.card E = 27) (hEP : E ≤ P) (hP : IsPGroup 3 P) (htP : t ∈ P) (htE : t ∉ E)
    (hSE : S ≤ E) (hS9 : Nat.card S = 9) (huE : u ∈ E) (huS : u ∉ S)
    (hK : Group.IsPerfect K) (hSK : S ≤ K) (hKu : K ≤ Subgroup.centralizer {u}) :
    t * u * t⁻¹ ∉ zpowers u ∧ t ^ 2 * u * (t ^ 2)⁻¹ ∉ zpowers u ⊔ zpowers (t * u * t⁻¹) ∧
      ∃ s ∈ S, t * s * t⁻¹ ∉ S := by
  set f : M →* N := e.toMonoidHom with hfd
  have hfi : Function.Injective f := e.injective
  have hmem : ∀ {y : M} {T : Subgroup M}, f y ∈ T.map f ↔ y ∈ T := fun {y T} =>
    ⟨fun ⟨y', hy', hyy⟩ => hfi hyy ▸ hy', fun hy => mem_map_of_mem f hy⟩
  refine shift_pullback f (shift_of_frame hf hW h81 hfr (E := E.map f) (P := P.map f)
    (K := K.map f) (Item812Res5.isElemAbelian_map_hom f hE)
    (by rw [card_map_of_injective hfi, hE27]) (map_mono hEP) (hP.map f) (hmem.mpr htP)
    (fun h => htE (hmem.mp h)) (map_mono hSE) (by rw [card_map_of_injective hfi, hS9])
    (hmem.mpr huE) (fun h => huS (hmem.mp h)) (@Group.IsPerfect.map _ _ _ _ _ f hK)
    (map_mono hSK) ?_)
  rintro _ ⟨y, hy, rfl⟩
  have h1 := hKu hy
  rw [mem_centralizer_singleton_iff] at h1 ⊢
  change f y * f u = f u * f y
  rw [← map_mul, ← map_mul, h1]

end Shift

end Item812Res12

open Item812Res12 in
theorem kF812E27PerfShift_holds :
    ∀ (M : Type) [Group M] [Finite M],
      (Nonempty (M ≃* alternatingGroup (Fin 9)) ∨ Nonempty (M ≃* projSp 3 (GaloisField 2 1))) →
      ∀ (E P S K : Subgroup M) (u t : M), CFSG.Assembly.IsElemAbelian 3 E → Nat.card E = 27 →
        E ≤ P → IsPGroup 3 P → t ∈ P → t ∉ E → S ≤ E → Nat.card S = 9 → u ∈ E → u ∉ S →
        Group.IsPerfect K → S ≤ K → K ≤ Subgroup.centralizer {u} →
        t * u * t⁻¹ ∉ Subgroup.zpowers u ∧
          t ^ 2 * u * (t ^ 2)⁻¹ ∉ Subgroup.zpowers u ⊔ Subgroup.zpowers (t * u * t⁻¹) ∧
          ∃ s ∈ S, t * s * t⁻¹ ∉ S := by
  intro M _ _ hM E P S K u t hE hE27 hEP hP htP htE hSE hS9 huE huS hK hSK hKu
  rcases hM with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
  · exact shift_of_mulEquiv Item812Res5.wreathFacts_A9 Item812Res5.card_wreathW_A9_eq_pow
      Item812Res5.card_wreathW_A9 frameProp_A9 e hE hE27 hEP hP htP htE hSE hS9 huE huS hK hSK
      hKu
  · exact shift_of_mulEquiv wreathFacts_zH Item812Res5.card_wreathW_zH_eq_pow card_wreathW_zH
      frameProp_zH (e.trans sp62Equiv) hE hE27 hEP hP htP htE hSE hS9 huE huS hK hSK hKu

end CFSG.RankThree.PartTwo.Sec8
