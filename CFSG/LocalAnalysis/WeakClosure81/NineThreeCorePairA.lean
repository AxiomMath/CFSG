module

public import CFSG.LocalAnalysis.WeakClosure81.NineThreeCoreNormal
public import CFSG.LocalAnalysis.WeakClosure81.NineThreeCoreLift
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.CGT.Timmesfeld75 Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G] {V T A K S X : Subgroup G} {p : ℕ} {g x : G}

@[expose] noncomputable def nine3_pair_P (V K : Subgroup G) (g : G) {n : ℕ}
    (B : Fin (n + 1) → Subgroup G) : Fin (n + 1) → Subgroup G :=
  fun k => if k = 0 then nineV1 V K g else B k ⊓ pCoreOf 2 K

theorem nine3_pair_P_disjoint (hc : Nine3Choice V T A K S X p g x) {n : ℕ}
    {B : Fin (n + 1) → Subgroup G} (hB0 : B 0 = V) (hBinj : Function.Injective B)
    (hBΔ : ∀ k, B k ∈ nineDelta V S) :
    ∀ k l, k ≠ l → nine3_pair_P V K g B k ⊓ nine3_pair_P V K g B l = ⊥ := by
  classical
  have hTI : CFSG.CGT.Timmesfeld75.IsTI V := hc.core.hyp7.2.2
  have hconj : ∀ k, ∃ a : G, B k = conjSubgroup V a := fun k => (hBΔ k).1
  choose a ha using hconj
  have hVne : ∀ k, k ≠ 0 → B k ≠ V := by
    intro k hk h
    exact hk (hBinj (h.trans hB0.symm))
  have hdisj : ∀ k l, k ≠ l → (if k = 0 then nineV1 V K g else B k ⊓ pCoreOf 2 K) ⊓
      (if l = 0 then nineV1 V K g else B l ⊓ pCoreOf 2 K) = ⊥ := by
    intro k l hkl
    by_cases hk : k = 0
    · subst hk
      have hl : l ≠ 0 := fun h => hkl h.symm
      simp only [if_pos rfl, if_neg hl]
      rw [eq_bot_iff]
      intro x hx
      have hxV : x ∈ V := hx.1.1
      have hxBl : x ∈ B l := hx.2.1
      rw [ha l] at hxBl
      rcases inf_conjSubgroup_eq_bot_or_eq hTI 1 (a l) with hbot | heq
      · rw [CFSG.Quasithin.conjSubgroup_one] at hbot
        exact Subgroup.mem_bot.mp (by rw [← hbot]; exact ⟨hxV, hxBl⟩)
      · rw [CFSG.Quasithin.conjSubgroup_one] at heq
        exact absurd ((ha l).trans heq.symm) (hVne l hl)
    · by_cases hl : l = 0
      · subst hl
        simp only [if_neg hk, if_pos rfl]
        rw [eq_bot_iff]
        intro x hx
        have hxBk : x ∈ B k := hx.1.1
        have hxV : x ∈ V := hx.2.1
        rw [ha k] at hxBk
        rcases inf_conjSubgroup_eq_bot_or_eq hTI 1 (a k) with hbot | heq
        · rw [CFSG.Quasithin.conjSubgroup_one] at hbot
          exact Subgroup.mem_bot.mp (by rw [← hbot]; exact ⟨hxV, hxBk⟩)
        · rw [CFSG.Quasithin.conjSubgroup_one] at heq
          exact absurd ((ha k).trans heq.symm) (hVne k hk)
      · simp only [if_neg hk, if_neg hl]
        rw [eq_bot_iff]
        intro x hx
        have hxBk : x ∈ B k := hx.1.1
        have hxBl : x ∈ B l := hx.2.1
        rw [ha k] at hxBk
        rw [ha l] at hxBl
        rcases inf_conjSubgroup_eq_bot_or_eq hTI (a k) (a l) with hbot | heq
        · exact Subgroup.mem_bot.mp (by rw [← hbot]; exact ⟨hxBk, hxBl⟩)
        · exact absurd ((ha k).trans (heq.trans (ha l).symm)) (hBinj.ne hkl)
  intro k l hkl
  simpa only [nine3_pair_P] using hdisj k l hkl

theorem nine3_pair_P_le_W (hc : Nine3Choice V T A K S X p g x) {n : ℕ}
    {B : Fin (n + 1) → Subgroup G} (hBΔ : ∀ k, B k ∈ nineDelta V S) (k : Fin (n + 1)) :
    nine3_pair_P V K g B k ≤ nineW V S := by
  by_cases hk : k = 0
  · subst hk
    simp only [nine3_pair_P, if_pos rfl]
    exact le_sup_left.trans hc.nineW0_le_nineW
  · simp only [nine3_pair_P, if_neg hk]
    exact inf_le_left.trans (le_iSup₂_of_le (B k) (hBΔ k) le_rfl)

structure Nine3PairEnum (V K S A : Subgroup G) (g : G) (n : ℕ) (B : Fin (n + 1) → Subgroup G)
    (σ : Equiv.Perm (Fin (n + 1))) (bb : Fin (n + 1) → G) : Prop where
  B0 : B 0 = V
  B1 : B 1 = A
  inj : Function.Injective B
  mem : ∀ k, B k ∈ nineDelta V S
  Ω : ∀ k, k ≠ 0 → B k ∈ nineOmegaIn V K S
  surj : ∀ D ∈ nineOmegaIn V K S, ∃ k, k ≠ 0 ∧ B k = D
  conj : ∀ k, conjSubgroup (B k) g = B (σ k)
  σ0 : σ 0 = 1
  σ1 : σ 1 = 0
  bb_mem : ∀ k, k ≠ 0 → bb k ∈ B k ∧ bb k ∉ pCoreOf 2 K
  bb0 : bb 0 = 1

theorem nine3_pair_rank (hc : Nine3Choice V T A K S X p g x) {U : Subgroup G}
    (hU : U ∈ omegaIn V K (nineE V K)) :
    ∃ i₁ i₂ : ↥(U ⊓ pCoreOf 2 K), i₁ ≠ 1 ∧ i₂ ≠ 1 ∧ i₁ ≠ i₂ := by
  obtain ⟨y, hUy, -, -⟩ := mem_omegaSet.mp hU.1
  have hcardU : Nat.card ↥U = Nat.card ↥V := by
    rw [hUy]; exact card_conjSubgroup' y V
  have hcardV : Nat.card ↥V = 2 ^ rk ↥V :=
    card_eq_two_pow_of_isPGroup (isPGroup_of_isElemAbelian hc.core.hyp7.1)
  have h8 : 8 ≤ Nat.card ↥V := by
    rw [hcardV]
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ rk ↥V := Nat.pow_le_pow_right (by norm_num)
        (Nat.succ_le_iff.mpr hc.core.rk_gt)
  have hrel : (U ⊓ pCoreOf 2 K).relIndex U = 2 := nine3_relIndex_of_mem_omegaIn hc hU
  have hcardT : Nat.card ↥(U ⊓ pCoreOf 2 K) * 2 = Nat.card ↥U := by
    have h1 := Subgroup.card_mul_index ((U ⊓ pCoreOf 2 K).subgroupOf U)
    have h2 : Nat.card ↥((U ⊓ pCoreOf 2 K).subgroupOf U) =
        Nat.card ↥(U ⊓ pCoreOf 2 K) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
    rw [h2, show ((U ⊓ pCoreOf 2 K).subgroupOf U).index = 2 from hrel] at h1
    exact h1
  have h4 : 4 ≤ Nat.card ↥(U ⊓ pCoreOf 2 K) := by
    have h2 : Nat.card ↥(U ⊓ pCoreOf 2 K) * 2 = Nat.card ↥V := hcardT.trans hcardU
    omega
  have hne_bot : U ⊓ pCoreOf 2 K ≠ ⊥ := by
    intro hbot
    have h1 : Nat.card ↥(U ⊓ pCoreOf 2 K) = 1 := by rw [hbot]; simp
    omega
  obtain ⟨x, hx, hx1⟩ :=
    (Subgroup.bot_or_exists_ne_one (U ⊓ pCoreOf 2 K)).resolve_left hne_bot
  let i₁ : ↥(U ⊓ pCoreOf 2 K) := ⟨x, hx⟩
  have hi₁ : i₁ ≠ 1 := fun h => hx1 (Subtype.ext_iff.mp h)
  have hUel : IsElemAbelian 2 U := by
    rw [hUy]; exact isElemAbelian_conjSubgroup' hc.core.hyp7.1 y
  have hi₁sq : i₁ ^ 2 = 1 := by
    apply Subtype.ext
    have := hUel.2 (i₁ : G) i₁.2.1
    simpa [pow_two] using this
  have hcyc2 : Nat.card ↥(Subgroup.zpowers i₁) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime hi₁sq hi₁
  have hcyc_ne_top : Subgroup.zpowers i₁ ≠ ⊤ := by
    intro htop
    have hcard_eq : Nat.card ↥(Subgroup.zpowers i₁) =
        Nat.card ↥(U ⊓ pCoreOf 2 K) := by
      rw [htop, Subgroup.card_top]
    omega
  have hnotle : ¬ (⊤ : Subgroup ↥(U ⊓ pCoreOf 2 K)) ≤ Subgroup.zpowers i₁ :=
    fun hle => hcyc_ne_top (top_le_iff.mp hle)
  obtain ⟨i₂, -, hi₂not⟩ := SetLike.not_le_iff_exists.mp hnotle
  have hi₂1 : i₂ ≠ 1 := fun h => hi₂not (by rw [h]; exact Subgroup.one_mem _)
  have hi₂i₁ : i₂ ≠ i₁ := fun h => hi₂not (by rw [h]; exact Subgroup.mem_zpowers i₁)
  exact ⟨i₁, i₂, hi₁, hi₂1, hi₂i₁.symm⟩

private theorem nine3_pair_list_prod_mem {W : Subgroup G} (l : List G) (f : G → G)
    (h : ∀ x ∈ l, f x ∈ W) : (l.map f).prod ∈ W := by
  induction l with
  | nil => simp
  | cons x l ih =>
      rw [List.map_cons, List.prod_cons]
      exact W.mul_mem (h x (by simp)) (ih fun y hy => h y (by simp [hy]))

private theorem nine3_pair_comm_list {W : Subgroup G}
    (hW : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a) {i : G} (l : List G)
    (hl : ∀ x ∈ l, x ∈ W) (hlc : ∀ x ∈ l, ⁅i, x⁆ ∈ W) :
    ⁅i, l.prod⁆ = (l.map (fun x => ⁅i, x⁆)).prod := by
  induction l with
  | nil => simp
  | cons x l ih =>
      have hxW : x ∈ W := hl x (by simp)
      have hrestW : (l.map (fun x => ⁅i, x⁆)).prod ∈ W :=
        nine3_pair_list_prod_mem l (fun x => ⁅i, x⁆) (fun y hy => hlc y (by simp [hy]))
      have hih : ⁅i, l.prod⁆ = (l.map (fun x => ⁅i, x⁆)).prod :=
        ih (fun y hy => hl y (by simp [hy])) (fun y hy => hlc y (by simp [hy]))
      have hconj : x * (l.map (fun x => ⁅i, x⁆)).prod * x⁻¹ =
          (l.map (fun x => ⁅i, x⁆)).prod := by
        rw [hW x hxW ((l.map (fun x => ⁅i, x⁆)).prod) hrestW]
        group
      rw [List.prod_cons, commutatorElement_mul_right_eq_mul_conj, hih]
      calc ⁅i, x⁆ * x * (l.map (fun x => ⁅i, x⁆)).prod * x⁻¹
          = ⁅i, x⁆ * (x * (l.map (fun x => ⁅i, x⁆)).prod * x⁻¹) := by group
        _ = ⁅i, x⁆ * (l.map (fun x => ⁅i, x⁆)).prod := by rw [hconj]
        _ = (List.map (fun x => ⁅i, x⁆) (x :: l)).prod := by
              rw [List.map_cons, List.prod_cons]

theorem nine3_pair_hs (hc : Nine3Choice V T A K S X p g x)
    (hc' : Nine3Choice V T A K S X p g⁻¹ x) (hI : Nine3IFacts V K S)
    (h35 : Nat.card ↥(nineDelta V S) = 3 ∨ Nat.card ↥(nineDelta V S) = 5) {n : ℕ}
    {B : Fin (n + 1) → Subgroup G} {bb : Fin (n + 1) → G}
    (hBΩ : ∀ k, k ≠ 0 → B k ∈ nineOmegaIn V K S)
    (hsurj : ∀ D ∈ nineOmegaIn V K S, ∃ k, k ≠ 0 ∧ B k = D)
    (hbb : ∀ k, k ≠ 0 → bb k ∈ B k ∧ bb k ∉ pCoreOf 2 K) (hbb0 : bb 0 = 1)
    {j : G} (hj : j ∈ conjSubgroup (nineI V K) g) :
    ∃ b ∈ nineZ V K S, ∃ ε : Fin (n + 1) → Bool, ε 0 = false ∧
      (∃ j₀ ∈ nineI V K, b = j₀ *
        ((List.finRange (n + 1)).map fun k => if ε k then bb k else 1).prod) ∧
      (∀ h ∈ nineH V K, ⁅b⁻¹ * j, h⁆ ∈ nineI V K) ∧
      (∀ i ∈ nineI V K, ⁅b⁻¹ * j, i⁆ = 1) ∧
      ∀ i ∈ nineI V K, ⁅i, j⁆ =
        ((List.finRange (n + 1)).map (fun k => if ε k then ⁅i, bb k⁆ else 1)).prod := by
  obtain ⟨b, hbZ, hbH, hbI⟩ := nine3_exists_lift hc hc' hI h35 hj
  obtain ⟨j₀, hj₀, ε, hε0, hb_eq⟩ := nine3_Z_normal_form hc hBΩ hsurj hbb hbb0 hbZ
  have hj₀I : j₀ ∈ nineI V K := by
    change j₀ ∈ ⨆ U ∈ omegaIn V K (nineE V K), U ⊓ pCoreOf 2 K
    exact iSup₂_le (fun B hB =>
      le_iSup₂_of_le (f := fun U (_ : U ∈ omegaIn V K (nineE V K)) => U ⊓ pCoreOf 2 K)
        B ⟨hB.1, hB.2.trans hc.core.S_le_K⟩ le_rfl) hj₀
  refine ⟨b, hbZ, ε, hε0, ⟨j₀, hj₀I, hb_eq⟩, hbH, hbI, ?_⟩
  intro i hi
  have hj₀Z : j₀ ∈ nineZ V K S :=
    iSup₂_le (fun B hB => (inf_le_left : B ⊓ pCoreOf 2 K ≤ B).trans
      (le_iSup₂_of_le B hB le_rfl)) hj₀
  have hj₀W : j₀ ∈ nineW V S := by
    rw [hc.core.nineW_eq]; exact Subgroup.mem_sup_right hj₀Z
  have hij0 : ⁅i, j₀⁆ = 1 :=
    commutatorElement_eq_one_iff_mul_comm.mpr
      (CFSG.Open.IsElemAbelian.comm hI.abelian hi hj₀I)
  have hbbW : ∀ k, bb k ∈ nineW V S := by
    intro k
    by_cases hk : k = 0
    · subst hk; rw [hbb0]; exact (nineW V S).one_mem
    · exact (le_iSup₂_of_le (B k)
        (hc.core.mem_nineDelta_iff.mpr (Or.inr (hBΩ k hk))) le_rfl :
          B k ≤ nineW V S) (hbb k hk).1
  have hbb_comm_W : ∀ k, ⁅i, bb k⁆ ∈ nineW V S := by
    intro k
    by_cases hk : k = 0
    · subst hk; rw [hbb0, commutatorElement_one_right]; exact (nineW V S).one_mem
    · have hmem : ⁅i, bb k⁆ ∈ ⁅nineI V K, B k⁆ :=
        Subgroup.commutator_mem_commutator hi (hbb k hk).1
      rw [hI.comm (B k) (hBΩ k hk)] at hmem
      exact (le_iSup₂_of_le (B k)
        (hc.core.mem_nineDelta_iff.mpr (Or.inr (hBΩ k hk))) le_rfl :
          B k ≤ nineW V S) hmem.1
  let Plist : List G := (List.finRange (n + 1)).map (fun k => if ε k then bb k else 1)
  have hPl : ∀ x ∈ Plist, x ∈ nineW V S := by
    intro x hx
    obtain ⟨k, -, hk⟩ := List.mem_map.mp hx
    rw [← hk]
    by_cases hε : ε k = true
    · rw [if_pos hε]; exact hbbW k
    · rw [if_neg hε]; exact (nineW V S).one_mem
  have hPlc : ∀ x ∈ Plist, ⁅i, x⁆ ∈ nineW V S := by
    intro x hx
    obtain ⟨k, -, hk⟩ := List.mem_map.mp hx
    rw [← hk]
    by_cases hε : ε k = true
    · rw [if_pos hε]; exact hbb_comm_W k
    · rw [if_neg hε, commutatorElement_one_right]; exact (nineW V S).one_mem
  have hPcomm : ⁅i, Plist.prod⁆ = (Plist.map (fun x => ⁅i, x⁆)).prod :=
    nine3_pair_comm_list (fun a ha b hb => hc.core.nineW_mul_comm ha hb) Plist hPl hPlc
  have hPcommW : ⁅i, Plist.prod⁆ ∈ nineW V S := by
    rw [hPcomm]
    exact nine3_pair_list_prod_mem Plist (fun x => ⁅i, x⁆) hPlc
  have hji : ⁅i, b⁻¹ * j⁆ = 1 := by
    have h := hbI i hi
    rw [← commutatorElement_inv] at h
    exact inv_eq_one.mp h
  have hijb : ⁅i, j⁆ = ⁅i, b⁆ := by
    have h1 : j = b * (b⁻¹ * j) := by group
    rw [h1, commutatorElement_mul_right_eq_mul_conj, hji, mul_one]
    group
  have hibb : ⁅i, b⁆ = ⁅i, Plist.prod⁆ := by
    rw [hb_eq, commutatorElement_mul_right_eq_mul_conj, hij0, one_mul]
    rw [hc.core.nineW_mul_comm hj₀W hPcommW]
    group
  have hmap : Plist.map (fun x => ⁅i, x⁆) =
      (List.finRange (n + 1)).map (fun k => if ε k then ⁅i, bb k⁆ else 1) := by
    simp only [Plist, List.map_map]
    apply List.map_congr_left
    intro k _
    cases hε : ε k <;> simp [hε]
  rw [hijb, hibb, hPcomm, hmap]

end CFSG.LocalAnalysis.WeakClosure81
