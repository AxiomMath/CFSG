module

public import CFSG.Quasithin.Background.HPair
public import CFSG.Quasithin.EmptyFaithful.SmithD391Decomp
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsModule

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
variable {W : Type} [CommGroup W] [Finite W]

private theorem s16h_e3_isInv_sSup {Γ : Type*} [Group Γ] {Q : Type*} [CommGroup Q]
    [MulDistribMulAction Γ Q] {Λ : Subgroup Γ} {S : Set (Subgroup Q)}
    (h : ∀ J ∈ S, XMod.IsInv ↥Λ J) : XMod.IsInv ↥Λ (sSup S) := by
  rw [sSup_eq_iSup']
  exact XMod.isInv_iSup fun J => h J J.2

private def s16h_e3_homComp {Γ : Type*} [Group Γ] {Q : Type*} [CommGroup Q]
    [MulDistribMulAction Γ Q] (Λ : Subgroup Γ) (I : Subgroup Q) : Subgroup Q :=
  sSup {K : Subgroup Q | XMod.IsIrr ↥Λ K ∧ XMod.Iso ↥Λ K I}

private theorem s16h_e3_le_homComp {Γ : Type*} [Group Γ] {Q : Type*} [CommGroup Q]
    [MulDistribMulAction Γ Q] {Λ : Subgroup Γ} {I : Subgroup Q}
    (hI : XMod.IsIrr ↥Λ I) : I ≤ s16h_e3_homComp Λ I :=
  le_sSup ⟨hI, XMod.Iso.refl I⟩

private theorem s16h_e3_le_homComp_of_iso {Γ : Type*} [Group Γ] {Q : Type*} [CommGroup Q]
    [MulDistribMulAction Γ Q] {Λ : Subgroup Γ} {I J : Subgroup Q} (hJ : XMod.IsIrr ↥Λ J)
    (h : XMod.Iso ↥Λ J I) : J ≤ s16h_e3_homComp Λ I :=
  le_sSup ⟨hJ, h⟩

private theorem s16h_e3_iso_of_le_homComp {Γ : Type*} [Group Γ] {Q : Type*} [CommGroup Q]
    [MulDistribMulAction Γ Q] {Λ : Subgroup Γ} {I J : Subgroup Q} (hI : XMod.IsIrr ↥Λ I)
    (hJ : XMod.IsIrr ↥Λ J) (h : J ≤ s16h_e3_homComp Λ I) : XMod.Iso ↥Λ J I := by
  rw [s16h_e3_homComp, sSup_eq_iSup'] at h
  obtain ⟨K, hK⟩ := CFSG.Quasithin.SmithD391.exists_iso_of_le_iSup
    (S := fun K : {K : Subgroup Q // XMod.IsIrr ↥Λ K ∧ XMod.Iso ↥Λ K I} => (K : Subgroup Q))
    (fun K => K.2.1) hJ h
  exact hK.trans K.2.2

private theorem s16h_e3_homComp_inf_sSup_eq_bot {Γ : Type*} [Group Γ] {Q : Type*}
    [CommGroup Q] [Finite Q] [MulDistribMulAction Γ Q] {Λ : Subgroup Γ} {I : Subgroup Q}
    (hI : XMod.IsIrr ↥Λ I) (S : Set (Subgroup Q)) (hS : ∀ J ∈ S, XMod.IsIrr ↥Λ J)
    (hSI : ∀ J ∈ S, ¬ XMod.Iso ↥Λ J I) :
    s16h_e3_homComp Λ I ⊓ sSup S = ⊥ := by
  by_contra hne
  have hinv : XMod.IsInv ↥Λ (s16h_e3_homComp Λ I ⊓ sSup S) :=
    (s16h_e3_isInv_sSup (Λ := Λ) (S := {K | XMod.IsIrr ↥Λ K ∧ XMod.Iso ↥Λ K I})
      (fun J hJ => hJ.1.1)).inf
      (s16h_e3_isInv_sSup (Λ := Λ) (S := S) fun J hJ => (hS J hJ).1)
  obtain ⟨K, hKle, hKirr⟩ := CFSG.Quasithin.SmithD391.exists_isIrr_le hinv hne
  have hK1 : K ≤ s16h_e3_homComp Λ I := hKle.trans inf_le_left
  have hK2 : K ≤ sSup S := hKle.trans inf_le_right
  have hKI : XMod.Iso ↥Λ K I := s16h_e3_iso_of_le_homComp hI hKirr hK1
  rw [sSup_eq_iSup'] at hK2
  obtain ⟨L, hL⟩ := CFSG.Quasithin.SmithD391.exists_iso_of_le_iSup
    (S := fun L : S => (L : Subgroup Q)) (fun L => hS L L.2) hKirr hK2
  exact hSI L L.2 ((XMod.Iso.symm hKirr.1 hL).trans hKI)

private theorem s16h_e3_eq_of_iso_of_iSup {Γ : Type*} [Group Γ] {Q : Type*} [CommGroup Q]
    [Finite Q] [MulDistribMulAction Γ Q] {Λ : Subgroup Γ} {ι : Type*} {S : ι → Subgroup Q}
    (hS : ∀ m, XMod.IsIrr ↥Λ (S m)) {k : ι} {J : Subgroup Q} (hJ : XMod.IsIrr ↥Λ J)
    (hJiso : XMod.Iso ↥Λ J (S k)) (hnot : ∀ m, m ≠ k → ¬ XMod.Iso ↥Λ (S m) (S k))
    (hJle : J ≤ ⨆ m, S m) : J = S k := by
  classical
  set T : Set (Subgroup Q) := {K | XMod.IsIrr ↥Λ K ∧ ¬ XMod.Iso ↥Λ K (S k)} with hT
  have hbot : s16h_e3_homComp Λ (S k) ⊓ sSup T = ⊥ :=
    s16h_e3_homComp_inf_sSup_eq_bot (Λ := Λ) (hS k) T
      (fun K hK => hK.1) (fun K hK => hK.2)
  have hP : (⨆ (m : {m // m ≠ k}), S m) ≤ sSup T := by
    apply iSup_le
    intro m
    exact le_sSup (show S m ∈ T from ⟨hS m, hnot m m.2⟩)
  have hsplit : (⨆ m, S m) = S k ⊔ ⨆ (m : {m // m ≠ k}), S m := by
    apply le_antisymm
    · apply iSup_le
      intro m
      by_cases hm : m = k
      · rw [hm]; exact le_sup_left
      · exact le_sup_of_le_right (le_iSup (fun m : {m // m ≠ k} => S m) ⟨m, hm⟩)
    · exact sup_le (le_iSup S k) (iSup_le fun m => le_iSup S m)
  have hJle' : J ≤ S k ⊔ ⨆ (m : {m // m ≠ k}), S m := by
    rw [← hsplit]; exact hJle
  have hJhc : J ≤ s16h_e3_homComp Λ (S k) := s16h_e3_le_homComp_of_iso hJ hJiso
  have hSkhc : S k ≤ s16h_e3_homComp Λ (S k) := s16h_e3_le_homComp (hS k)
  have hJK : J ≤ S k := by
    intro j hj
    have hjhc : j ∈ s16h_e3_homComp Λ (S k) := hJhc hj
    obtain ⟨a, ha, b, hb, hab⟩ := Subgroup.mem_sup.mp (hJle' hj)
    have hahc : a ∈ s16h_e3_homComp Λ (S k) := hSkhc ha
    have hbhc : b ∈ s16h_e3_homComp Λ (S k) := by
      have hbeq : b = a⁻¹ * j := by rw [← hab]; group
      rw [hbeq]
      exact (s16h_e3_homComp Λ (S k)).mul_mem
        ((s16h_e3_homComp Λ (S k)).inv_mem hahc) hjhc
    have hbT : b ∈ sSup T := hP hb
    have hmem : b ∈ s16h_e3_homComp Λ (S k) ⊓ sSup T := ⟨hbhc, hbT⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    rw [← hab, hmem, mul_one]
    exact ha
  rcases (hS k).2.2 J hJ.1 bot_le hJK with h | h
  · exact absurd h hJ.2.1.ne'
  · exact h

private theorem s16h_e3_pair_isInv_of_commSub_eq {L : Subgroup (MulAut W)} {X : Subgroup W}
    (h : commSub X L = X) : H.Pair.IsInv L X := by
  intro l hl w hw
  have hmem : l w * w⁻¹ ∈ X := by
    rw [← h]
    exact Subgroup.subset_closure ⟨l, hl, w, hw, rfl⟩
  have h1 : l w = (l w * w⁻¹) * w := by group
  rw [h1]
  exact X.mul_mem hmem hw

private theorem s16h_e3_pair_isInv_xmod {L : Subgroup (MulAut W)} {X : Subgroup W}
    (h : H.Pair.IsInv L X) : XMod.IsInv ↥L X :=
  fun a x hx => h a a.2 x hx

private theorem s16h_e3_pair_isIrr_xmod {L : Subgroup (MulAut W)} {X : Subgroup W}
    (hInv : XMod.IsInv ↥L X) (h : H.Pair.IsIrr L X) : XMod.IsIrr ↥L X :=
  ⟨hInv, ⟨bot_lt_iff_ne_bot.mpr h.1,
    fun U hUi _ hU => h.2 U hU fun l hl x hx => hUi ⟨l, hl⟩ x hx⟩⟩

private theorem s16h_e3_pair_iso_xmod {L : Subgroup (MulAut W)} {X Y : Subgroup W}
    (h : H.Pair.IsoMod L X Y) : XMod.Iso ↥L X Y := by
  obtain ⟨e, he⟩ := h
  refine ⟨e, fun a l l' hl => ?_⟩
  have hl' : (a : MulAut W) (l : W) = (l' : W) := hl
  have hmem : (a : MulAut W) (l : W) ∈ X := hl'.symm ▸ l'.2
  have h1 := he (a : MulAut W) a.2 l hmem
  have hsub : (⟨(a : MulAut W) (l : W), hmem⟩ : ↥X) = l' := Subtype.ext hl'
  rw [hsub] at h1
  exact h1.symm

private theorem s16h_e3_xmod_iso_pair {L : Subgroup (MulAut W)} {X Y : Subgroup W}
    (h : XMod.Iso ↥L X Y) : H.Pair.IsoMod L X Y := by
  obtain ⟨e, he⟩ := h
  refine ⟨e, fun l hl w hw => ?_⟩
  have h1 := he (⟨l, hl⟩ : ↥L) w ⟨l w, hw⟩ rfl
  exact h1.symm

private theorem s16h_e3_fixV_eq_bot_of_pair_iso {L : Subgroup (MulAut W)} {X Y : Subgroup W}
    (hfixY : Y ⊓ fixV L = ⊥) (h : H.Pair.IsoMod L X Y) : X ⊓ fixV L = ⊥ := by
  obtain ⟨e, he⟩ := h
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hxX, hxfix⟩ := Subgroup.mem_inf.mp hx
  have hmemY : (e ⟨x, hxX⟩ : W) ∈ Y := (e ⟨x, hxX⟩).2
  have hfix_e : (e ⟨x, hxX⟩ : W) ∈ fixV L := by
    intro l hl
    have hx' : l x ∈ X := by simpa only [hxfix l hl] using hxX
    have h1 := he l hl ⟨x, hxX⟩ hx'
    have hsub : (⟨l x, hx'⟩ : ↥X) = ⟨x, hxX⟩ := Subtype.ext (hxfix l hl)
    rw [hsub] at h1
    exact h1.symm
  have hmem : (e ⟨x, hxX⟩ : W) ∈ Y ⊓ fixV L := ⟨hmemY, hfix_e⟩
  rw [hfixY, Subgroup.mem_bot] at hmem
  have hx1 : (⟨x, hxX⟩ : ↥X) = 1 := e.injective (by rw [map_one]; exact Subtype.ext hmem)
  simpa using congrArg Subtype.val hx1

private theorem s16h_e3_fin3_eq_of_ne {i j k m : Fin 3} (hij : i ≠ j) (hik : i ≠ k)
    (hjk : j ≠ k) (hmk : m ≠ k) (hmi : m ≠ i) : m = j := by
  apply Fin.ext
  have hmk' : m.val ≠ k.val := fun h => hmk (Fin.ext h)
  have hmi' : m.val ≠ i.val := fun h => hmi (Fin.ext h)
  have hij' : i.val ≠ j.val := fun h => hij (Fin.ext h)
  have hik' : i.val ≠ k.val := fun h => hik (Fin.ext h)
  have hjk' : j.val ≠ k.val := fun h => hjk (Fin.ext h)
  have hm : m.val < 3 := m.isLt
  have hi : i.val < 3 := i.isLt
  have hj : j.val < 3 := j.isLt
  have hk : k.val < 3 := k.isLt
  omega

theorem s16h_e3_eq_of_iso_of_irr {L : Subgroup (MulAut W)} {I : Fin 3 → Subgroup W}
    {i j k : Fin 3} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hirr : ∀ m, I m ∈ irrSet L) (hfix : ∀ m, I m ⊓ fixV L = ⊥)
    (hind : ∀ m, I m ⊓ (⊥ ⊔ ⨆ (n : Fin 3) (_ : n ≠ m), I n) ≤ ⊥)
    (hU : (⊥ ⊔ ⨆ m, I m) = commSub ⊤ L)
    (hnotik : ¬ H.Pair.IsoMod L (I k) (I i)) (hnotjk : ¬ H.Pair.IsoMod L (I k) (I j))
    {J : Subgroup W} (hJ : J ∈ irrSet L) (hJiso : H.Pair.IsoMod L J (I k)) :
    J = I k := by
  have hInv : ∀ m, H.Pair.IsInv L (I m) := fun m =>
    s16h_e3_pair_isInv_of_commSub_eq (hirr m).1
  have hIrrPair : ∀ m, H.Pair.IsIrr L (I m) := by
    intro m
    have h := (hirr m).2
    rw [hfix m] at h
    exact ⟨h.1.ne', fun U hU hUi => h.2.2.2 U hUi bot_le hU⟩
  have hInvX : ∀ m, XMod.IsInv ↥L (I m) := fun m => s16h_e3_pair_isInv_xmod (hInv m)
  have hIrrX : ∀ m, XMod.IsIrr ↥L (I m) :=
    fun m => s16h_e3_pair_isIrr_xmod (hInvX m) (hIrrPair m)
  have hfixJ : J ⊓ fixV L = ⊥ := s16h_e3_fixV_eq_bot_of_pair_iso (hfix k) hJiso
  have hJPairInv : H.Pair.IsInv L J := s16h_e3_pair_isInv_of_commSub_eq hJ.1
  have hJIrrOn := hJ.2
  rw [hfixJ] at hJIrrOn
  have hJPair : H.Pair.IsIrr L J :=
    ⟨hJIrrOn.1.ne', fun U hU hUi => hJIrrOn.2.2.2 U hUi bot_le hU⟩
  have hJXInv : XMod.IsInv ↥L J := s16h_e3_pair_isInv_xmod hJPairInv
  have hJX : XMod.IsIrr ↥L J := s16h_e3_pair_isIrr_xmod hJXInv hJPair
  have hJisoX : XMod.Iso ↥L J (I k) := s16h_e3_pair_iso_xmod hJiso
  have hnotikX : ¬ XMod.Iso ↥L (I i) (I k) := fun h =>
    hnotik (s16h_e3_xmod_iso_pair (XMod.Iso.symm (hInvX i) h))
  have hnotjkX : ¬ XMod.Iso ↥L (I j) (I k) := fun h =>
    hnotjk (s16h_e3_xmod_iso_pair (XMod.Iso.symm (hInvX j) h))
  have hnot : ∀ m, m ≠ k → ¬ XMod.Iso ↥L (I m) (I k) := by
    intro m hm
    by_cases hmi : m = i
    · subst hmi; exact hnotikX
    · have hmj : m = j := s16h_e3_fin3_eq_of_ne hij hik hjk hm hmi
      subst hmj; exact hnotjkX
  have hJleU : J ≤ commSub ⊤ L := by
    calc J = commSub J L := hJ.1.symm
      _ ≤ commSub ⊤ L := commSub_mono le_top le_rfl
  have hJle : J ≤ ⨆ m : Fin 3, I m := by
    have h := hJleU
    rw [← hU] at h
    simpa only [bot_sup_eq] using h
  exact s16h_e3_eq_of_iso_of_iSup hIrrX hJX hJisoX hnot hJle

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
