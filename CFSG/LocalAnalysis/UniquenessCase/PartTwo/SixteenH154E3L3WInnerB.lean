module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3L3WInnerA
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3L3CoordP
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2Irr
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenT7Proof
import CFSG.Quasithin.Vol2.Ch10SecABasicAut
import CFSG.GH74.KGH
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs
public import CFSG.Quasithin.Background.B5Part3
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3L3CoordHA
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3L3CoordHB

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.H.Pair CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22

variable {Q : Type} [CommGroup Q] [Finite Q]

private theorem s16h_e3_l3_pair_isInv_of_commSub_eq {W : Type*} [CommGroup W]
    {L : Subgroup (MulAut W)} {X : Subgroup W} (h : commSub X L = X) : H.Pair.IsInv L X := by
  intro l hl w hw
  have hmem : l w * w⁻¹ ∈ X := by
    rw [← h]
    exact Subgroup.subset_closure ⟨l, hl, w, hw, rfl⟩
  have h1 : l w = (l w * w⁻¹) * w := by group
  rw [h1]
  exact X.mul_mem hmem hw

private theorem s16h_e3_l3_pair_isInv_xmod {W : Type*} [CommGroup W]
    {L : Subgroup (MulAut W)} {X : Subgroup W} (h : H.Pair.IsInv L X) : XMod.IsInv ↥L X :=
  fun a x hx => h a a.2 x hx

private theorem s16h_e3_l3_pair_isIrr_xmod {W : Type*} [CommGroup W]
    {L : Subgroup (MulAut W)} {X : Subgroup W} (hInv : XMod.IsInv ↥L X)
    (h : H.Pair.IsIrr L X) : XMod.IsIrr ↥L X :=
  ⟨hInv, ⟨bot_lt_iff_ne_bot.mpr h.1,
    fun U hUi _ hU => h.2 U hU fun l hl x hx => hUi ⟨l, hl⟩ x hx⟩⟩

private theorem s16h_e3_l3_pair_iso_xmod {W : Type*} [CommGroup W]
    {L : Subgroup (MulAut W)} {X Y : Subgroup W} (h : H.Pair.IsoMod L X Y) :
    XMod.Iso ↥L X Y := by
  obtain ⟨e, he⟩ := h
  refine ⟨e, fun a l l' hl => ?_⟩
  have hl' : (a : MulAut W) (l : W) = (l' : W) := hl
  have hmem : (a : MulAut W) (l : W) ∈ X := hl'.symm ▸ l'.2
  have h1 := he (a : MulAut W) a.2 l hmem
  have hsub : (⟨(a : MulAut W) (l : W), hmem⟩ : ↥X) = l' := Subtype.ext hl'
  rw [hsub] at h1
  exact h1.symm

private theorem s16h_e3_l3_xmod_iso_pair {W : Type*} [CommGroup W]
    {L : Subgroup (MulAut W)} {X Y : Subgroup W} (h : XMod.Iso ↥L X Y) :
    H.Pair.IsoMod L X Y := by
  obtain ⟨e, he⟩ := h
  refine ⟨e, fun l hl w hw => ?_⟩
  have h1 := he (⟨l, hl⟩ : ↥L) w ⟨l w, hw⟩ rfl
  exact h1.symm

private theorem s16h_e3_l3_xmod_isInv_of_irrSet {W : Type*} [CommGroup W]
    {L : Subgroup (MulAut W)} {X : Subgroup W} (hirr : X ∈ irrSet L) : XMod.IsInv ↥L X :=
  s16h_e3_l3_pair_isInv_xmod (s16h_e3_l3_pair_isInv_of_commSub_eq hirr.1)

private theorem s16h_e3_l3_xmod_isIrr_of_irrSet {W : Type*} [CommGroup W]
    {L : Subgroup (MulAut W)} {X : Subgroup W} (hirr : X ∈ irrSet L)
    (hfix : X ⊓ fixV L = ⊥) : XMod.IsIrr ↥L X := by
  have hInv : H.Pair.IsInv L X := s16h_e3_l3_pair_isInv_of_commSub_eq hirr.1
  have hIrr : H.Pair.IsIrr L X := by
    have h := hirr.2
    rw [hfix] at h
    exact ⟨h.1.ne', fun U hU hUi => h.2.2.2 U hUi bot_le hU⟩
  exact s16h_e3_l3_pair_isIrr_xmod (s16h_e3_l3_pair_isInv_xmod hInv) hIrr

private theorem s16h_e3_l3_isoMod_trans {W : Type*} [CommGroup W]
    {L : Subgroup (MulAut W)} {A B C : Subgroup W} (hB : H.Pair.IsInv L B)
    (h : H.Pair.IsoMod L A B) (h' : H.Pair.IsoMod L B C) : H.Pair.IsoMod L A C := by
  obtain ⟨e, he⟩ := h
  obtain ⟨e', he'⟩ := h'
  refine ⟨e.trans e', fun l hl w hw => ?_⟩
  have h2 := he' l hl (e w) (hB l hl _ (e w).2)
  have hsub : e ⟨l w, hw⟩ = ⟨l ((e w : W)), hB l hl _ (e w).2⟩ := Subtype.ext (he l hl w hw)
  show ((e' (e ⟨l w, hw⟩) : ↥C) : W) = l (((e' (e w) : ↥C)) : W)
  rw [hsub]
  exact h2

private theorem s16h_e3_l3_binaryNaturalSL_map_conj {W : Type} [CommGroup W]
    {H : Subgroup (MulAut W)} {U Z : Subgroup W} {d a : ℕ}
    (hnat : BinaryNaturalSL H U Z d a) (σ : MulAut W) :
    BinaryNaturalSL (H.map (MulAut.conj σ).toMonoidHom) (U.map σ.toMonoidHom)
      (Z.map σ.toMonoidHom) d a := by
  unfold BinaryNaturalSL at hnat ⊢
  obtain ⟨K, hKf, hKfin, hKcard, hreal⟩ := hnat
  refine ⟨K, hKf, hKfin, hKcard, ?_⟩
  unfold FFModel.Realizes at hreal ⊢
  obtain ⟨π, hπ⟩ := hreal
  exact ⟨(CFSG.Quasithin.Vol2.Ch10.SecA.conjEquivMap H σ).toMonoidHom.comp π,
    CFSG.Quasithin.Vol2.Ch10.SecA.realizesVia_map_conj hπ σ⟩

theorem s16h_e3_l3_exists_twist_stable_natural (hQ : ∀ q : Q, q ^ 2 = 1)
    {L : Subgroup (MulAut Q)} (hL : IsPSL 3 2 1 ↥L)
    (hsum : SumOfNat (fun H A B => BinaryNaturalSL H A B 3 1) L (⊤ : Subgroup Q) ⊥ 3)
    {τ : MulAut Q} (hτ : τ ∈ normalizer (L : Set (MulAut Q))) :
    ∃ V : Subgroup Q, (∀ x ∈ L, ∀ v ∈ V, x v ∈ V) ∧ Nat.card ↥V = 8 ∧
      (∃ x ∈ L, ∃ v ∈ V, x v ≠ v) ∧ H.Pair.IsoMod L (V.map τ.toMonoidHom) V := by
  have hL3 : IsL3 ↥L 1 := CFSG.GH74.lieModel_of_statedClassicalModel (by decide) hL
  obtain ⟨I, -, hind, hsup, hnat⟩ := hsum
  have hLmap : L.map (MulAut.conj τ).toMonoidHom = L := by
    simpa using (Subgroup.mem_normalizer_iff_map_conj_eq).mp hτ
  have hirr : ∀ i : Fin 3, I i ∈ irrSet L := fun i =>
    s16c167_mem_irrSet_ln (by norm_num) (hnat i)
  have hfix : ∀ i : Fin 3, I i ⊓ fixV L = ⊥ := fun i =>
    s16c167_inf_fixV_eq_bot_of_binaryNaturalSL (by norm_num) (hnat i)
  have hcard : ∀ i : Fin 3, Nat.card ↥(I i) = 8 := fun i => s15_T7_card_eight (hnat i)
  have hne : ∀ i : Fin 3, I i ≠ ⊥ := fun i => by
    have h := (hirr i).2
    rw [hfix i] at h
    exact h.1.ne'
  have hnt : ∀ i : Fin 3, ∃ x ∈ L, ∃ v ∈ I i, x v ≠ v := fun i => by
    by_contra hcon
    have hle : I i ≤ fixV L := by
      intro v hv
      rw [mem_fixV]
      intro x hx
      by_contra hne'
      exact hcon ⟨x, hx, v, hv, hne'⟩
    have hbot : I i = ⊥ := by
      rw [eq_bot_iff]
      calc I i ≤ I i ⊓ fixV L := le_inf le_rfl hle
        _ = ⊥ := hfix i
    exact hne i hbot
  have hnatτ : ∀ i : Fin 3, BinaryNaturalSL L ((I i).map τ.toMonoidHom) ⊥ 3 1 := fun i => by
    have h := s16h_e3_l3_binaryNaturalSL_map_conj (hnat i) τ
    rw [hLmap, Subgroup.map_bot] at h
    exact h
  have hirrτ : ∀ i : Fin 3, (I i).map τ.toMonoidHom ∈ irrSet L := fun i =>
    s16c167_mem_irrSet_ln (by norm_num) (hnatτ i)
  have hfixτ : ∀ i : Fin 3, ((I i).map τ.toMonoidHom) ⊓ fixV L = ⊥ := fun i =>
    s16c167_inf_fixV_eq_bot_of_binaryNaturalSL (by norm_num) (hnatτ i)
  have hInvXi : ∀ i : Fin 3, XMod.IsInv ↥L (I i) := fun i =>
    s16h_e3_l3_xmod_isInv_of_irrSet (hirr i)
  have hIrrXi : ∀ i : Fin 3, XMod.IsIrr ↥L (I i) := fun i =>
    s16h_e3_l3_xmod_isIrr_of_irrSet (hirr i) (hfix i)
  have hIrrXτ : ∀ i : Fin 3, XMod.IsIrr ↥L ((I i).map τ.toMonoidHom) := fun i =>
    s16h_e3_l3_xmod_isIrr_of_irrSet (hirrτ i) (hfixτ i)
  have hcomm : commSub (⊤ : Subgroup Q) L = ⊤ := by
    apply le_antisymm le_top
    calc (⊤ : Subgroup Q) = ⊥ ⊔ ⨆ i : Fin 3, I i := hsup.symm
      _ ≤ commSub (⊤ : Subgroup Q) L := by
        apply sup_le bot_le
        apply iSup_le
        intro i
        have hi : I i ≤ commSub (I i) L := by rw [(hirr i).1]
        exact hi.trans (commSub_mono le_top le_rfl)
  have hU : (⊥ ⊔ ⨆ m : Fin 3, I m) = commSub (⊤ : Subgroup Q) L := hsup.trans hcomm.symm
  have hInvPair : ∀ m : Fin 3, H.Pair.IsInv L (I m) := fun m =>
    s16h_e3_l3_pair_isInv_of_commSub_eq (hirr m).1
  have hInvPairτ : ∀ m : Fin 3, H.Pair.IsInv L ((I m).map τ.toMonoidHom) := fun m =>
    s16h_e3_l3_pair_isInv_of_commSub_eq (hirrτ m).1
  have key1 : ∀ i j : Fin 3, i ≠ j → ∃ k : Fin 3, i ≠ k ∧ j ≠ k := by decide
  have key2 : ∀ i j k m : Fin 3, i ≠ j → i ≠ k → j ≠ k → m ≠ i → m ≠ j → m = k := by
    intro i j k m hij hik hjk hmi hmj
    simp only [ne_eq, Fin.ext_iff] at hij hik hjk hmi hmj ⊢
    omega
  obtain ⟨i, j, hij, hiso⟩ := s16h_e3_l3_two_iso hL3 hnat
  obtain ⟨k, hik, hjk⟩ := key1 i j hij
  by_cases hex : ∃ m : Fin 3, H.Pair.IsoMod L ((I m).map τ.toMonoidHom) (I m)
  · obtain ⟨m, hm⟩ := hex
    exact ⟨I m, hInvPair m, hcard m, hnt m, hm⟩
  · have hno : ∀ m : Fin 3, ¬ H.Pair.IsoMod L ((I m).map τ.toMonoidHom) (I m) :=
      fun m hm => hex ⟨m, hm⟩
    have hno' : ∀ m : Fin 3, ¬ H.Pair.IsoMod L (I m) ((I m).map τ.toMonoidHom) :=
      fun m hm => hno m (H.Pair.IsoMod.symm (hInvPair m) hm)
    by_cases hk : H.Pair.IsoMod L (I k) (I i)
    ·
      have hall : ∀ m : Fin 3, H.Pair.IsoMod L (I i) (I m) := by
        intro m
        by_cases hmi : m = i
        · subst hmi
          exact ⟨MulEquiv.refl _, fun l _ w _ => rfl⟩
        by_cases hmj : m = j
        · subst hmj
          exact hiso
        have hmk : m = k := key2 i j k m hij hik hjk hmi hmj
        rw [hmk]
        exact H.Pair.IsoMod.symm (hInvPair k) hk
      have hallX : ∀ m : Fin 3, XMod.Iso ↥L (I i) (I m) := fun m =>
        s16h_e3_l3_pair_iso_xmod (hall m)
      have hisoX : ∀ m n : Fin 3, XMod.Iso ↥L (I m) (I n) := fun m n =>
        (XMod.Iso.symm (hInvXi i) (hallX m)).trans (hallX n)
      have hJU : (I i).map τ.toMonoidHom ≤ ⨆ m : Fin 3, I m := by
        have htop : (⨆ m : Fin 3, I m) = ⊤ :=
          (bot_sup_eq (⨆ m : Fin 3, I m)).symm.trans hsup
        rw [htop]
        exact le_top
      have hJisoX : XMod.Iso ↥L ((I i).map τ.toMonoidHom) (I i) :=
        CFSG.Quasithin.B5.iso_of_irr_le_iSup (L := L) I hIrrXi hisoX i (hIrrXτ i) hJU
      exact ⟨I i, hInvPair i, hcard i, hnt i, s16h_e3_l3_xmod_iso_pair hJisoX⟩
    ·
      have hk' : ¬ H.Pair.IsoMod L (I i) (I k) := fun h =>
        hk (H.Pair.IsoMod.symm (hInvPair i) h)
      let Jf : Fin 3 → Subgroup Q :=
        Fin.cons (I i) (Fin.cons (I k) (fun _ : Fin 1 => (I i).map τ.toMonoidHom))
      have hJ0 : Jf 0 = I i := rfl
      have hJ1 : Jf 1 = I k := rfl
      have hJ2 : Jf 2 = (I i).map τ.toMonoidHom := rfl
      have hJnat : ∀ t : Fin 3, BinaryNaturalSL L (Jf t) ⊥ 3 1 := by
        intro t
        fin_cases t
        · exact hnat i
        · exact hnat k
        · exact hnatτ i
      obtain ⟨a, b, hab, hisoJ⟩ := s16h_e3_l3_two_iso hL3 hJnat
      have hab' : (a = 1 ∧ b = 2) ∨ (a = 2 ∧ b = 1) := by
        fin_cases a <;> fin_cases b
        · exact (hab rfl).elim
        · exact (hk' hisoJ).elim
        · exact (hno' i hisoJ).elim
        · exact (hk hisoJ).elim
        · exact (hab rfl).elim
        · exact Or.inl ⟨rfl, rfl⟩
        · exact (hno i hisoJ).elim
        · exact Or.inr ⟨rfl, rfl⟩
        · exact (hab rfl).elim
      have hik' : H.Pair.IsoMod L ((I i).map τ.toMonoidHom) (I k) := by
        obtain ⟨ha, hb⟩ | ⟨ha, hb⟩ := hab'
        · rw [ha, hb] at hisoJ
          have h : H.Pair.IsoMod L (I k) ((I i).map τ.toMonoidHom) := by
            simpa only [hJ1, hJ2] using hisoJ
          exact H.Pair.IsoMod.symm (hInvPair k) h
        · rw [ha, hb] at hisoJ
          exact by simpa only [hJ1, hJ2] using hisoJ
      have hkj : ¬ H.Pair.IsoMod L (I k) (I j) := fun h =>
        hk (s16h_e3_l3_isoMod_trans (hInvPair j) h (H.Pair.IsoMod.symm (hInvPair i) hiso))
      have hjk' : H.Pair.IsoMod L ((I j).map τ.toMonoidHom) (I k) := by
        have hmap := s16h_e3_isoMod_map hτ hiso
        have hsymm : H.Pair.IsoMod L ((I j).map τ.toMonoidHom) ((I i).map τ.toMonoidHom) :=
          H.Pair.IsoMod.symm (hInvPairτ i) hmap
        exact s16h_e3_l3_isoMod_trans (hInvPairτ i) hsymm hik'
      have hJeq : (I i).map τ.toMonoidHom = I k :=
        s16h_e3_eq_of_iso_of_irr hij hik hjk hirr hfix hind hU hk hkj (hirrτ i) hik'
      have hJ'eq : (I j).map τ.toMonoidHom = I k :=
        s16h_e3_eq_of_iso_of_irr hij hik hjk hirr hfix hind hU hk hkj (hirrτ j) hjk'
      have hIij : I i = I j := by
        have h : (I i).map τ.toMonoidHom = (I j).map τ.toMonoidHom := by rw [hJeq, hJ'eq]
        exact Subgroup.map_injective τ.injective h
      have hle : I i ≤ ⊥ := by
        have hmem : I i ≤ I i ⊓ (⊥ ⊔ ⨆ (n : Fin 3) (_ : n ≠ i), I n) := by
          refine le_inf le_rfl ?_
          rw [hIij]
          exact le_sup_of_le_right ((le_iSup (fun _ : j ≠ i => I j) (Ne.symm hij)).trans
            (le_iSup (fun n : Fin 3 => ⨆ (_ : n ≠ i), I n) j))
        exact hmem.trans (hind i)
      exact (hne i (le_bot_iff.mp hle)).elim

theorem s16h_e3_normalizer_inner_of_sumOfNat (hQ : ∀ q : Q, q ^ 2 = 1)
    {L : Subgroup (MulAut Q)} (hL : IsPSL 3 2 1 ↥L)
    (hsum : SumOfNat (fun H A B => BinaryNaturalSL H A B 3 1) L (⊤ : Subgroup Q) ⊥ 3)
    {τ : MulAut Q} (hτ : τ ∈ normalizer (L : Set (MulAut Q))) :
    ∃ γ ∈ L, ∀ l ∈ L, τ * l * τ⁻¹ = γ * l * γ⁻¹ := by
  obtain ⟨V, hVinv, hcard, hnt, hiso⟩ :=
    s16h_e3_l3_exists_twist_stable_natural hQ hL hsum hτ
  exact s16h_e3_inner_of_twist_stable hQ hL hVinv hcard hnt hτ hiso

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
