module

public import CFSG.LocalAnalysis.WeakClosure81.SixNine
public import CFSG.LocalAnalysis.WeakClosure81.SevenOne
public import CFSG.Quasithin.Background.E3Gen
public import CFSG.Quasithin.Background.E3Weak
public import CFSG.Quasithin.Background.E3Basic
public import CFSG.Quasithin.Background.E3OffenderB
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsWeakClosure
public import CFSG.LieType.BorelTits.Basic
public import CFSG.CGT.Timmesfeld75.Cfg214Gen
public import CFSG.CGT.Timmesfeld75.L2Real
public import CFSG.LargeExtraspecial.S9TIXC
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.InvolutionCountingOrderFormula
public import CFSG.LocalAnalysis.WeakClosure81.SixSix
public import CFSG.Quasithin.Background.B6
public import CFSG.Quasithin.Background.B6Example
public import CFSG.Quasithin.Background.B6Offenders
public import CFSG.Quasithin.Background.E3Cent

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.CGT.Timmesfeld75
  CFSG.LocalAnalysis.UniquenessCase.PartTwo Subgroup

variable {G : Type} [Group G] [Finite G]

theorem conj_inf_pCoreOf_le_normalizer {H T A : Subgroup G}
    (hTH : T ≤ H) (hQT : pCoreOf 2 H ≤ T) (hAH : A ≤ H)
    (hAel : IsElemAbelian 2 A) (hTI : IsTI A) (hrk : 2 < rk ↥A)
    (hAO : ¬ A ≤ pCoreOf 2 H) (hk : E3.mQuot A (A ⊓ pCoreOf 2 H) ≤ 2)
    (hN : IsPGroup 2 ↥(H ⊓ normalizer (A : Set G)))
    (hC : IsPGroup 2 ↥(H ⊓ centralizer (E3.cClos A 2 T : Set G))) :
    ∀ g ∈ H, conjSubgroup (A ⊓ pCoreOf 2 H) g ≤ normalizer (A : Set G) := by
  set Q : Subgroup G := pCoreOf 2 H with hQ
  set B : Subgroup G := A ⊓ Q with hB
  set W : Subgroup G := E3.wClos A 2 Q with hW
  set Y : Subgroup G := H ⊓ Subgroup.centralizer (W : Set G) with hY
  set C : Subgroup G := E3.cClos A 2 Q with hCQ
  have hA2 : IsPGroup 2 A := CFSG.Quasithin.B2F.isPGroup_of_isElemAbelian hAel
  have hk' : E3.mQuot A B ≤ 2 := hk
  have hQT' : Q ≤ T := hQT
  have hBW : B ≤ W := by
    rw [hB, hW]
    exact E3.le_wClos_of_mQuot_le_self hAel inf_le_right inf_le_left hk' hrk
  have hBne : B ≠ ⊥ := by
    intro hbot
    have h1 : E3.mQuot A B = rk ↥A := by rw [hbot, E3.mQuot_bot_eq_rk]
    omega
  have hHQ : H ≤ Subgroup.normalizer (Q : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf (r := 2) H
  have hHW : H ≤ Subgroup.normalizer (W : Set G) :=
    hHQ.trans (E3.normalizer_le_normalizer_wClos (V := A) (i := 2) Q)
  obtain ⟨b, hbB, hb1⟩ : ∃ b ∈ B, b ≠ 1 := by
    rcases Subgroup.bot_or_exists_ne_one B with hbot | h
    · exact absurd hbot hBne
    · exact h
  have hbA : b ∈ A := (Subgroup.mem_inf.mp hbB).1
  have hbW : b ∈ W := hBW hbB
  have hY2 : IsPGroup 2 ↥Y := by
    have hYle : Y ≤ H ⊓ Subgroup.normalizer (A : Set G) := by
      intro y hy
      refine ⟨hy.1, ?_⟩
      have hyb : b * y = y * b := (Subgroup.mem_centralizer_iff.mp hy.2) b hbW
      have hyC : y ∈ Subgroup.centralizer ({b} : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro z hz
        rw [Set.mem_singleton_iff] at hz
        subst hz
        exact hyb
      exact centralizer_le_normalizer_of_isTI hTI hbA hb1 hyC
    exact hN.to_le hYle
  have hHNW : H ≤ Subgroup.normalizer
      (Subgroup.centralizer (W : Set G) : Set G) := by
    intro h hh
    rw [← conjSubgroup_eq_iff_mem_normalizer, E3.conjSubgroup_centralizer,
      (conjSubgroup_eq_iff_mem_normalizer).2 (hHW hh)]
  have hHNY : H ≤ Subgroup.normalizer (Y : Set G) := by
    intro h hh
    rw [← conjSubgroup_eq_iff_mem_normalizer]
    rw [hY, E3.conjSubgroup_inf,
      (conjSubgroup_eq_iff_mem_normalizer).2 (Subgroup.le_normalizer (H := H) hh),
      E3.conjSubgroup_centralizer,
      (conjSubgroup_eq_iff_mem_normalizer).2 (hHW hh)]
  have hYQ : Y ≤ Q :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer (r := 2) (N := Y) (H := H)
      inf_le_left hHNY hY2
  have hCN : C ≤ Subgroup.normalizer (A : Set G) := by
    intro c hc
    have hcW : c ∈ Subgroup.centralizer (W : Set G) := hc.2
    have hcb : b * c = c * b := (Subgroup.mem_centralizer_iff.mp hcW) b hbW
    have hcCb : c ∈ Subgroup.centralizer ({b} : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      subst hz
      exact hcb
    exact centralizer_le_normalizer_of_isTI hTI hbA hb1 hcCb
  have hWn : W ≤ Subgroup.normalizer (A : Set G) := by
    by_contra hWn
    have hAZ : A ⊓ Subgroup.centralizer (W : Set G) = ⊥ := by
      by_contra hne
      rcases Subgroup.bot_or_exists_ne_one
        (A ⊓ Subgroup.centralizer (W : Set G)) with hbot | ⟨e, he, he1⟩
      · exact hne hbot
      · have hWCe : W ≤ Subgroup.centralizer ({e} : Set G) := by
          intro w hw
          rw [Subgroup.mem_centralizer_iff]
          intro z hz
          rw [Set.mem_singleton_iff] at hz
          subst hz
          exact ((Subgroup.mem_centralizer_iff.mp he.2) w hw).symm
        exact hWn (hWCe.trans (centralizer_le_normalizer_of_isTI hTI he.1 he1))
    have hAC : A ≤ Subgroup.centralizer (C : Set G) := by
      intro a ha
      rw [Subgroup.mem_centralizer_iff]
      intro c hc
      have haN : a ∈ Subgroup.normalizer
          (Subgroup.centralizer (W : Set G) : Set G) := by
        rw [← conjSubgroup_eq_iff_mem_normalizer, E3.conjSubgroup_centralizer,
          (conjSubgroup_eq_iff_mem_normalizer).2 (hHW (hAH ha))]
      have h1 : a * c * a⁻¹ ∈ Subgroup.centralizer (W : Set G) :=
        (Subgroup.mem_normalizer_iff.mp haN c).mp hc.2
      have h2 : a * c * a⁻¹ * c⁻¹ ∈ Subgroup.centralizer (W : Set G) :=
        Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ hc.2)
      have h3 : c * a⁻¹ * c⁻¹ ∈ A :=
        (Subgroup.mem_normalizer_iff.mp (hCN hc) a⁻¹).mp (Subgroup.inv_mem _ ha)
      have h4 : a * c * a⁻¹ * c⁻¹ ∈ A := by
        have := Subgroup.mul_mem _ ha h3
        convert this using 1
        group
      have h5 : a * c * a⁻¹ * c⁻¹ = 1 := by
        have hmem : a * c * a⁻¹ * c⁻¹ ∈
            A ⊓ Subgroup.centralizer (W : Set G) := ⟨h4, h2⟩
        rwa [hAZ, Subgroup.mem_bot] at hmem
      have h6 : a * c * a⁻¹ = c := by
        have : a * c * a⁻¹ = (a * c * a⁻¹ * c⁻¹) * c := by group
        rw [this, h5, one_mul]
      calc c * a = (a * c * a⁻¹) * a := by rw [h6]
        _ = a * c := by group
    have hC2le : E3.cClos A 2 T ≤ C := by
      rw [hCQ]
      intro x hx
      have hxT : x ∈ T := hx.1
      have hxw : x ∈ Subgroup.centralizer (E3.wClos A 2 T : Set G) := hx.2
      have hxH : x ∈ H := hTH hxT
      have hxW : x ∈ Subgroup.centralizer (W : Set G) := by
        rw [Subgroup.mem_centralizer_iff] at hxw ⊢
        intro w hw
        exact hxw w (E3.wClos_mono (V := A) (i := 2) hQT' hw)
      exact ⟨hYQ ⟨hxH, hxW⟩, hxW⟩
    obtain ⟨y, hyH, hy⟩ :=
      exists_not_isPGroup_sup_conj_of_not_le_pCore hAH hA2 hAO
    have hAyH : conjSubgroup A y ≤ H := by
      have hHconj : conjSubgroup H y = H :=
        (conjSubgroup_eq_iff_mem_normalizer).2
          (Subgroup.le_normalizer (H := H) hyH)
      rw [← hHconj]
      exact E3.conjSubgroup_mono_left y hAH
    have hCin : conjSubgroup C y = C := by
      rw [hCQ, ← E3.cClos_conj (V := A) (i := 2) Q y,
        (conjSubgroup_eq_iff_mem_normalizer).2 (hHQ hyH)]
    have hAyC : conjSubgroup A y ≤ Subgroup.centralizer (C : Set G) := by
      have h := E3.conjSubgroup_mono_left y hAC
      rwa [E3.conjSubgroup_centralizer, hCin] at h
    have hC2sub : (E3.cClos A 2 T : Set G) ⊆ (C : Set G) := fun x hx => hC2le hx
    have hsup : A ⊔ conjSubgroup A y ≤
        H ⊓ Subgroup.centralizer (E3.cClos A 2 T : Set G) :=
      sup_le (le_inf hAH (hAC.trans (Subgroup.centralizer_le hC2sub)))
        (le_inf hAyH (hAyC.trans (Subgroup.centralizer_le hC2sub)))
    exact hy (hC.to_le hsup)
  intro g hg
  have hBg : conjSubgroup B g ≤ W := by
    have h1 : conjSubgroup B g ≤ conjSubgroup W g := E3.conjSubgroup_mono_left g hBW
    have h2 : conjSubgroup W g = W :=
      (conjSubgroup_eq_iff_mem_normalizer).2 (hHW hg)
    rwa [h2] at h1
  exact hBg.trans hWn

theorem inf_pCoreOf_le_nVSub {H A : Subgroup G}
    (hfb : ∀ g ∈ H, conjSubgroup (A ⊓ pCoreOf 2 H) g ≤ normalizer (A : Set G))
    {h : G} (hh : h ∈ H) : A ⊓ pCoreOf 2 H ≤ nVSub A h := by
  intro b hb
  rw [mem_nVSub]
  refine ⟨hb.1, ?_⟩
  rw [← E3.conjSubgroup_normalizer]
  rw [mem_conjSubgroup_iff]
  refine hfb h⁻¹ (Subgroup.inv_mem _ hh) ?_
  rw [mem_conjSubgroup_iff]
  rwa [show h⁻¹ * (h * b * h⁻¹) * h⁻¹⁻¹ = b by group]

theorem conj_inf_pCoreOf_le_bSub {H A : Subgroup G}
    (hfb : ∀ g ∈ H, conjSubgroup (A ⊓ pCoreOf 2 H) g ≤ normalizer (A : Set G))
    {h : G} (hh : h ∈ H) : conjSubgroup (A ⊓ pCoreOf 2 H) h ≤ bSub A h := by
  intro x hx
  rw [mem_bSub]
  exact ⟨E3.conjSubgroup_mono_left h inf_le_left hx, hfb h hh hx⟩

theorem inCalO_of_conj_inf_pCoreOf_le {H A : Subgroup G} {n : ℕ}
    (hAel : IsElemAbelian 2 A) (hk : E3.mQuot A (A ⊓ pCoreOf 2 H) ≤ n)
    (hfb : ∀ g ∈ H, conjSubgroup (A ⊓ pCoreOf 2 H) g ≤ normalizer (A : Set G))
    {h : G} (hh : h ∈ H)
    (hX : ¬ IsPGroup 2 (A ⊔ conjSubgroup A h : Subgroup G)) :
    InCalO n (normalizer (A : Set G)) ⊥ A h := by
  have hA2 : IsPGroup 2 A := CFSG.Quasithin.B2F.isPGroup_of_isElemAbelian hAel
  have hB0nV : A ⊓ pCoreOf 2 H ≤ nVSub A h := inf_pCoreOf_le_nVSub hfb hh
  have hB0b : conjSubgroup (A ⊓ pCoreOf 2 H) h ≤ bSub A h :=
    conj_inf_pCoreOf_le_bSub hfb hh
  unfold InCalO OFirst ODual
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩
  · exact not_conjSubgroup_le_normalizer_of_not_isPGroup hA2 le_rfl le_rfl hX
  · have hle : A ⊓ pCoreOf 2 H ≤
        conjSubgroup (Subgroup.normalizer (A : Set G)) h := by
      rw [E3.conjSubgroup_normalizer]
      exact fun x hx => (hB0nV hx).2
    exact (E3.mQuot_mono hle).trans hk
  · intro hbot
    exact absurd hbot (by simp)
  · exact not_le_conjSubgroup_of_not_isPGroup hA2 le_rfl rfl hX
  · have hle : conjSubgroup (A ⊓ pCoreOf 2 H) h ≤
        Subgroup.normalizer (A : Set G) :=
      fun x hx => (mem_bSub.mp (hB0b hx)).2
    calc E3.mQuot (conjSubgroup A h) (Subgroup.normalizer (A : Set G))
        ≤ E3.mQuot (conjSubgroup A h) (conjSubgroup (A ⊓ pCoreOf 2 H) h) :=
          E3.mQuot_mono hle
      _ = E3.mQuot A (A ⊓ pCoreOf 2 H) :=
          E3.mQuot_conjSubgroup A (A ⊓ pCoreOf 2 H) h
      _ ≤ n := hk
  · intro hbot
    exact absurd hbot (by simp)

end CFSG.LocalAnalysis.WeakClosure81
