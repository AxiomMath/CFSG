module

public import CFSG.Quasithin.Background.E3Prop
public import CFSG.Quasithin.SteinbergBSWeakClosureParameters
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase
open Subgroup

variable {G : Type} [Group G] [Finite G]

@[expose] def InCalU (M X : Subgroup G) : Prop := UC22.UniqueMax M X

theorem exists_maxTwoLocal_ge {H : Subgroup G} (hH : IsTwoLocal H) :
    ∃ N : Subgroup G, rankThreeIsMaxTwoLocal N ∧ H ≤ N := by
  classical
  set S : Set (Subgroup G) := {M | IsTwoLocal M ∧ H ≤ M} with hS
  obtain ⟨M, ⟨hM, hHM⟩, hmax⟩ :=
    Set.exists_max_image S (fun M => Nat.card M) (Set.toFinite S) ⟨H, hH, le_rfl⟩
  refine ⟨M, ⟨hM, fun K hK hMK => ?_⟩, hHM⟩
  have hKS : K ∈ S := ⟨hK, hHM.trans hMK⟩
  exact (Subgroup.eq_of_le_of_card_ge hMK (hmax K hKS)).symm

theorem InCalU.mono {M X Y : Subgroup G} (hM : rankThreeIsMaxTwoLocal M) (hX : InCalU M X)
    (hXY : X ≤ Y) (hYM : Y ≤ M) : InCalU M Y := by
  change UC22.calMOf Y = {M}
  have hX' : UC22.calMOf X = {M} := hX
  refine Set.Subset.antisymm (fun N hN => ?_) (Set.singleton_subset_iff.2 ⟨hM, hYM⟩)
  have hNX : N ∈ UC22.calMOf X := ⟨hN.1, hXY.trans hN.2⟩
  rwa [hX'] at hNX

theorem normalizer_le_of_inCalU {M X R : Subgroup G} (hX : InCalU M X)
    (hXR : X ≤ Subgroup.normalizer (R : Set G)) (hRne : R ≠ ⊥) (hR2 : IsPGroup 2 R) :
    Subgroup.normalizer (R : Set G) ≤ M := by
  have hloc : IsTwoLocal (Subgroup.normalizer (R : Set G)) := ⟨R, hRne, hR2, rfl⟩
  obtain ⟨N, hN, hle⟩ := exists_maxTwoLocal_ge hloc
  have hNX : N ∈ UC22.calMOf X := ⟨hN, hXR.trans hle⟩
  have hX' : UC22.calMOf X = {M} := hX
  rw [hX'] at hNX
  have hNM : N = M := Set.mem_singleton_iff.1 hNX
  rwa [hNM] at hle

theorem wClos_eq_wClos_succ {V : Subgroup G} (hV : IsElemAbelian 2 V) (i : ℕ) (S : Subgroup G)
    (hi : i + 1 < rk ↥V) :
    E3.wClos V i S = E3.wClos V i (E3.wClos V (i + 1) S) := by
  have hd : Nat.card V = 2 ^ rk ↥V :=
    card_eq_two_pow_of_isPGroup (B2F.isPGroup_of_isElemAbelian hV)
  refine le_antisymm ?_ (E3.wClos_mono (E3.wClos_le (i + 1) S))
  refine E3.wClos_le_of_forall fun A hA => E3.le_wClos ?_
  exact ⟨(E3.le_wClos hA).trans (SteinbergBS.wClos_le_wClos hV hd (Nat.le_succ i) hi S), hA.2⟩

theorem cClos_anti {V : Subgroup G} (hV : IsElemAbelian 2 V) {i j : ℕ} (hij : i ≤ j)
    (hjd : j < rk ↥V) (S : Subgroup G) : E3.cClos V j S ≤ E3.cClos V i S := by
  have hd : Nat.card V = 2 ^ rk ↥V :=
    card_eq_two_pow_of_isPGroup (B2F.isPGroup_of_isElemAbelian hV)
  unfold E3.cClos
  exact inf_le_inf_left S
    (Subgroup.centralizer_le (SteinbergBS.wClos_le_wClos hV hd hij hjd S))

theorem centerOf_wClos_le_cClos {V : Subgroup G} (hV : IsElemAbelian 2 V) {i j : ℕ}
    (hij : i ≤ j) (hjd : j < rk ↥V) (S : Subgroup G) :
    centerOf (E3.wClos V j S) ≤ E3.cClos V i S := by
  have hd : Nat.card V = 2 ^ rk ↥V :=
    card_eq_two_pow_of_isPGroup (B2F.isPGroup_of_isElemAbelian hV)
  rw [E3.cClos]
  refine le_inf (inf_le_left.trans (E3.wClos_le j S)) ?_
  exact inf_le_right.trans
    (Subgroup.centralizer_le (SteinbergBS.wClos_le_wClos hV hd hij hjd S))

theorem centerOf_wClos_le_cClos_self {V : Subgroup G} (j : ℕ) (S : Subgroup G) :
    centerOf (E3.wClos V j S) ≤ E3.cClos V j S := by
  rw [E3.cClos]
  exact le_inf (inf_le_left.trans (E3.wClos_le j S)) inf_le_right

theorem six_fifteen_one {V S : Subgroup G} (hV : IsElemAbelian 2 V) {i : ℕ} (hi1 : 1 ≤ i)
    (hid : i < rk ↥V) :
    Subgroup.normalizer (E3.wClos V i S : Set G) ≤
        Subgroup.normalizer (E3.wClos V (i - 1) S : Set G) ∧
      Subgroup.centralizer (E3.cClos V (i - 1) S : Set G) ≤
        Subgroup.centralizer (E3.cClos V i S : Set G) := by
  have hsub : i - 1 + 1 = i := by omega
  constructor
  · have h := E3.normalizer_le_normalizer_wClos (V := V) (i := i - 1) (X := E3.wClos V i S)
    have heq := wClos_eq_wClos_succ hV (i - 1) S (by omega)
    rw [hsub] at heq
    rwa [← heq] at h
  · exact Subgroup.centralizer_le (cClos_anti hV (i := i - 1) (j := i) (by omega) hid S)

private theorem normalizer_wClos_anti_aux {V S : Subgroup G} (hV : IsElemAbelian 2 V)
    (i : ℕ) : ∀ t : ℕ, i + t < rk ↥V →
      Subgroup.normalizer (E3.wClos V (i + t) S : Set G) ≤
        Subgroup.normalizer (E3.wClos V i S : Set G) := by
  intro t
  induction t with
  | zero => intro _; exact le_rfl
  | succ t ih =>
    intro ht
    have h1 : Subgroup.normalizer (E3.wClos V (i + t + 1) S : Set G) ≤
        Subgroup.normalizer (E3.wClos V (i + t) S : Set G) := by
      have h := (six_fifteen_one (S := S) hV (i := i + t + 1) (by omega) (by omega)).1
      simpa [show i + t + 1 - 1 = i + t by omega] using h
    exact h1.trans (ih (by omega))

theorem normalizer_wClos_anti {V S : Subgroup G} (hV : IsElemAbelian 2 V) {i j : ℕ}
    (hij : i ≤ j) (hjd : j < rk ↥V) :
    Subgroup.normalizer (E3.wClos V j S : Set G) ≤
      Subgroup.normalizer (E3.wClos V i S : Set G) := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hij
  exact normalizer_wClos_anti_aux hV i t hjd

theorem six_fifteen_two' {V M S : Subgroup G} (hV : IsElemAbelian 2 V)
    (hM : rankThreeIsMaxTwoLocal M) (hS2 : IsPGroup 2 S) (hW0 : E3.wClos V 0 S ≠ ⊥)
    {i : ℕ} (hid : i < rk ↥V)
    (hU : InCalU M (M ⊓ Subgroup.centralizer (E3.cClos V i S : Set G))) :
    (∀ j : ℕ, j < rk ↥V → Subgroup.centralizer (E3.cClos V j S : Set G) ≤ M) ∧
      (∀ j : ℕ, i ≤ j → j < rk ↥V →
        Subgroup.normalizer (E3.wClos V j S : Set G) ≤ M) ∧
      (∀ j : ℕ, j ≤ i → Subgroup.centralizer (E3.cClos V j S : Set G) ≤
        Subgroup.centralizer (E3.cClos V i S : Set G)) := by
  have hd : Nat.card V = 2 ^ rk ↥V :=
    card_eq_two_pow_of_isPGroup (B2F.isPGroup_of_isElemAbelian hV)
  have hW0le : ∀ j : ℕ, j < rk ↥V → E3.wClos V 0 S ≤ E3.wClos V j S := fun j hj =>
    SteinbergBS.wClos_le_wClos hV hd (Nat.zero_le j) hj S
  have hWj_ne : ∀ j : ℕ, j < rk ↥V → E3.wClos V j S ≠ ⊥ := by
    intro j hj hbot
    exact hW0 (le_bot_iff.1 (hbot ▸ hW0le j hj))
  have hWj2 : ∀ j : ℕ, IsPGroup 2 (E3.wClos V j S) := fun j => hS2.to_le (E3.wClos_le j S)
  have hkey : ∀ j : ℕ, i ≤ j → j < rk ↥V →
      Subgroup.normalizer (centerOf (E3.wClos V j S) : Set G) ≤ M ∧
        Subgroup.centralizer (E3.cClos V j S : Set G) ≤ M := by
    intro j hij hj
    have hZj : centerOf (E3.wClos V j S) ≠ ⊥ :=
      E3.centerOf_ne_bot_of_isPGroup (hWj2 j) (hWj_ne j hj)
    have hZj2 : IsPGroup 2 (centerOf (E3.wClos V j S)) := (hWj2 j).to_le inf_le_left
    have hZjC : centerOf (E3.wClos V j S) ≤ E3.cClos V i S :=
      centerOf_wClos_le_cClos hV hij hj S
    have hle1 : M ⊓ Subgroup.centralizer (E3.cClos V i S : Set G) ≤
        M ⊓ Subgroup.centralizer (centerOf (E3.wClos V j S) : Set G) :=
      inf_le_inf_left M (Subgroup.centralizer_le hZjC)
    have hUj : InCalU M (M ⊓ Subgroup.centralizer (centerOf (E3.wClos V j S) : Set G)) :=
      InCalU.mono hM hU hle1 inf_le_left
    have hNM : M ⊓ Subgroup.centralizer (centerOf (E3.wClos V j S) : Set G) ≤
        Subgroup.normalizer (centerOf (E3.wClos V j S) : Set G) :=
      inf_le_right.trans (Subgroup.centralizer_le_normalizer _)
    have hNZ : Subgroup.normalizer (centerOf (E3.wClos V j S) : Set G) ≤ M :=
      normalizer_le_of_inCalU hUj hNM hZj hZj2
    refine ⟨hNZ, ?_⟩
    exact (Subgroup.centralizer_le (centerOf_wClos_le_cClos_self j S)).trans
      ((Subgroup.centralizer_le_normalizer _).trans hNZ)
  refine ⟨?_, ?_, ?_⟩
  · intro j hj
    by_cases hji : i ≤ j
    · exact (hkey j hji hj).2
    · push Not at hji
      have hji' : j ≤ i := le_of_lt hji
      exact (Subgroup.centralizer_le (cClos_anti hV hji' hid S)).trans (hkey i le_rfl hid).2
  · intro j hij hj
    exact (E3.normalizer_le_normalizer_centerOf (E3.wClos V j S)).trans (hkey j hij hj).1
  · intro j hji
    exact Subgroup.centralizer_le (cClos_anti hV hji hid S)

theorem six_fifteen_three {V M S : Subgroup G} (hV : IsElemAbelian 2 V)
    (hM : rankThreeIsMaxTwoLocal M) (hS2 : IsPGroup 2 S) (hW0 : E3.wClos V 0 S ≠ ⊥)
    {i : ℕ} (hid : i < rk ↥V)
    (hU : InCalU M (M ⊓ Subgroup.normalizer (E3.wClos V i S : Set G))) :
    (∀ j : ℕ, j < rk ↥V → Subgroup.normalizer (E3.wClos V j S : Set G) ≤ M) ∧
      (∀ j : ℕ, j ≤ i → Subgroup.centralizer (E3.cClos V (i - j) S : Set G) ≤ M) := by
  have hd : Nat.card V = 2 ^ rk ↥V :=
    card_eq_two_pow_of_isPGroup (B2F.isPGroup_of_isElemAbelian hV)
  have hW0le : ∀ j : ℕ, j < rk ↥V → E3.wClos V 0 S ≤ E3.wClos V j S := fun j hj =>
    SteinbergBS.wClos_le_wClos hV hd (Nat.zero_le j) hj S
  have hWj_ne : ∀ j : ℕ, j < rk ↥V → E3.wClos V j S ≠ ⊥ := by
    intro j hj hbot
    exact hW0 (le_bot_iff.1 (hbot ▸ hW0le j hj))
  have hWj2 : ∀ j : ℕ, IsPGroup 2 (E3.wClos V j S) := fun j => hS2.to_le (E3.wClos_le j S)
  have hZi : centerOf (E3.wClos V i S) ≠ ⊥ :=
    E3.centerOf_ne_bot_of_isPGroup (hWj2 i) (hWj_ne i hid)
  have hZi2 : IsPGroup 2 (centerOf (E3.wClos V i S)) := (hWj2 i).to_le inf_le_left
  have hle1 : M ⊓ Subgroup.normalizer (E3.wClos V i S : Set G) ≤
      M ⊓ Subgroup.normalizer (centerOf (E3.wClos V i S) : Set G) :=
    inf_le_inf_left M (E3.normalizer_le_normalizer_centerOf _)
  have hUZi : InCalU M (M ⊓ Subgroup.normalizer (centerOf (E3.wClos V i S) : Set G)) :=
    InCalU.mono hM hU hle1 inf_le_left
  have hNZi : Subgroup.normalizer (centerOf (E3.wClos V i S) : Set G) ≤ M :=
    normalizer_le_of_inCalU hUZi inf_le_right hZi hZi2
  have hNWi : Subgroup.normalizer (E3.wClos V i S : Set G) ≤ M :=
    (E3.normalizer_le_normalizer_centerOf _).trans hNZi
  have hCi : Subgroup.centralizer (E3.cClos V i S : Set G) ≤ M :=
    (Subgroup.centralizer_le (centerOf_wClos_le_cClos_self i S)).trans
      ((Subgroup.centralizer_le_normalizer _).trans hNZi)
  refine ⟨?_, ?_⟩
  · intro j hj
    by_cases hji : i ≤ j
    · exact (normalizer_wClos_anti hV hji hj).trans hNWi
    · push Not at hji
      have hji' : j ≤ i := le_of_lt hji
      have hNM : M ⊓ Subgroup.normalizer (E3.wClos V i S : Set G) =
          Subgroup.normalizer (E3.wClos V i S : Set G) := inf_eq_right.2 hNWi
      have hle : M ⊓ Subgroup.normalizer (E3.wClos V i S : Set G) ≤
          Subgroup.normalizer (E3.wClos V j S : Set G) := by
        rw [hNM]
        exact normalizer_wClos_anti hV hji' hid
      exact normalizer_le_of_inCalU hU hle (hWj_ne j hj) (hWj2 j)
  · intro j hji
    have hle : E3.cClos V i S ≤ E3.cClos V (i - j) S := cClos_anti hV (by omega) hid S
    exact (Subgroup.centralizer_le hle).trans hCi

theorem e3_19_of_inE {V H S : Subgroup G} (hV : IsElemAbelian 2 V) (hS : IsSylowIn 2 S H)
    {i j : ℕ} (hInE : E1.InE j H) (hij : i + j < E3.sParam hV) :
    (H ⊓ Subgroup.centralizer (E3.cClos V (i + j) S : Set G)) ⊔
      (H ⊓ Subgroup.normalizer (E3.wClos V i S : Set G)) = H := by
  refine le_antisymm (sup_le inf_le_left inf_le_left) ?_
  have hEF := (E1.inE_iff_inEFor hS).1 hInE (E3.gammaSet V i H) (E3.isInvColl_gammaSet hV i H)
  rw [E3.weakClosure_gammaSet hS.le] at hEF
  have hE : E1.eGen j H S (E3.gammaSet V i H) ≤
      (H ⊓ Subgroup.centralizer (E3.cClos V (i + j) S : Set G)) ⊔
        (H ⊓ Subgroup.normalizer (E3.wClos V i S : Set G)) := by
    refine iSup₂_le fun A hA => iSup_le fun hAS => iSup₂_le fun K hK => ?_
    have hAΓ : A ∈ E3.gammaSet V i S := ⟨hAS, hA.2⟩
    have hSK : IsSylowIn 2 (S ⊓ K) K := hK.2.2.1
    have hKH : K ≤ H := hK.1
    have hKeq : K = (S ⊓ K) ⊔ twoResidual K := (sup_twoResidual_eq hSK).symm
    have hcomm := E3.e3_19_comm hV hS hij hAΓ hK
    have hSN : S ≤ Subgroup.normalizer (E3.wClos V i S : Set G) :=
      Subgroup.le_normalizer.trans (E3.normalizer_le_normalizer_wClos S)
    have h1 : S ⊓ K ≤ H ⊓ Subgroup.normalizer (E3.wClos V i S : Set G) :=
      le_inf (inf_le_right.trans hKH) (inf_le_left.trans hSN)
    have h2 : twoResidual K ≤ H ⊓ Subgroup.centralizer (E3.cClos V (i + j) S : Set G) :=
      le_inf ((twoResidual_le K).trans hKH) (Subgroup.commutator_eq_bot_iff_le_centralizer.1 hcomm)
    rw [hKeq]
    exact sup_le (h1.trans le_sup_right) (h2.trans le_sup_left)
  calc H = E1.eGen j H S (E3.gammaSet V i H) ⊔
        (H ⊓ Subgroup.normalizer (E3.wClos V i S : Set G)) := hEF.symm
    _ ≤ _ := sup_le hE le_sup_right

theorem six_fifteen_four {V M H S : Subgroup G} (hV : IsElemAbelian 2 V)
    (hM : rankThreeIsMaxTwoLocal M) (hS : IsSylowIn 2 S H) {k : ℕ} (hk : 1 ≤ k)
    (hH : E1.InE k H) (hW0 : E3.wClos V 0 S ≠ ⊥) (hgt : k + 1 < E3.sParam hV)
    (hcond : ∀ i : ℕ, i ≤ k →
      InCalU M (M ⊓ Subgroup.normalizer (E3.wClos V i S : Set G)) ∨
        InCalU M (M ⊓ Subgroup.centralizer (E3.cClos V (i + 1) S : Set G))) :
    H ≤ M := by
  by_contra hHM
  have hsV : E3.sParam hV ≤ rk ↥V := E3.sParam_le_rk hV
  have hS2 : IsPGroup 2 S := hS.isPGroup
  have hkV : k < rk ↥V := by omega
  have hfac0 := e3_19_of_inE hV hS (i := 0) (j := k) hH (by omega)
  have hfac1 := e3_19_of_inE hV hS (i := 1) (j := k) hH (by omega)
  have hstep1 : ¬ InCalU M (M ⊓ Subgroup.centralizer (E3.cClos V 1 S : Set G)) := by
    intro hU1
    have h2 := six_fifteen_two' hV hM hS2 hW0 (i := 1) (by omega) hU1
    have hC : Subgroup.centralizer (E3.cClos V (1 + k) S : Set G) ≤ M := h2.1 (1 + k) (by omega)
    have hN : Subgroup.normalizer (E3.wClos V 1 S : Set G) ≤ M := h2.2.1 1 le_rfl (by omega)
    apply hHM
    rw [← hfac1]
    exact sup_le (inf_le_right.trans hC) (inf_le_right.trans hN)
  have hstep2 : InCalU M (M ⊓ Subgroup.normalizer (E3.wClos V 0 S : Set G)) := by
    rcases hcond 0 (Nat.zero_le k) with h | h
    · exact h
    · exact absurd h hstep1
  have h3 := six_fifteen_three hV hM hS2 hW0 (i := 0) (by omega) hstep2
  have hN0 : Subgroup.normalizer (E3.wClos V 0 S : Set G) ≤ M := h3.1 0 (by omega)
  have hCk_not : ¬ Subgroup.centralizer (E3.cClos V k S : Set G) ≤ M := by
    intro hCk
    apply hHM
    rw [← hfac0]
    exact sup_le (by simpa using inf_le_right.trans hCk) (by simpa using inf_le_right.trans hN0)
  have hstep3 : ¬ InCalU M (M ⊓ Subgroup.centralizer (E3.cClos V (k + 1) S : Set G)) := by
    intro hU
    have h2 := six_fifteen_two' hV hM hS2 hW0 (i := k + 1) (by omega) hU
    have hCk1 : Subgroup.centralizer (E3.cClos V (k + 1) S : Set G) ≤ M := h2.1 (k + 1) (by omega)
    have hmono : Subgroup.centralizer (E3.cClos V k S : Set G) ≤
        Subgroup.centralizer (E3.cClos V (k + 1) S : Set G) :=
      Subgroup.centralizer_le (cClos_anti hV (Nat.le_succ k) (by omega) S)
    exact hCk_not (hmono.trans hCk1)
  have hstep4 : InCalU M (M ⊓ Subgroup.normalizer (E3.wClos V k S : Set G)) := by
    rcases hcond k le_rfl with h | h
    · exact h
    · exact absurd h hstep3
  have h3' := six_fifteen_three hV hM hS2 hW0 (i := k) hkV hstep4
  exact hCk_not (by simpa using h3'.2 0 (Nat.zero_le k))

end CFSG.LocalAnalysis.WeakClosure81
