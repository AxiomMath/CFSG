module

public import CFSG.LocalAnalysis.StandardType.GGNbrWeylTypeDefs
public import CFSG.LocalAnalysis.StandardType.GGStdPosC24Signed
import CFSG.LocalAnalysis.StandardType.GGRCSignedCoxeterB
import CFSG.LocalAnalysis.StandardType.GGSpJoinSignedPermGen
import CFSG.LocalAnalysis.StandardType.GGNbrTableBExcInduced

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB
open CFSG.StandardType.SpCoord CFSG.StandardType.SpJoin
open Multiplicative

private lemma ggWTSgn_toPerm_sgnAut {p k : ℕ} (i : Fin k) :
    MulAut.toPerm (Fin k → Multiplicative (ZMod p)) (sgnAut i) = coordInv k p i := by
  ext v; rfl

private lemma ggWTSgn_toPerm_permAut {p k : ℕ} (σ : Equiv.Perm (Fin k)) :
    MulAut.toPerm (Fin k → Multiplicative (ZMod p)) (permAut σ) = coordPerm k p σ := by
  ext v; rfl

private lemma ggWTSgn_toPerm_injective {p k : ℕ} :
    Function.Injective (MulAut.toPerm (Fin k → Multiplicative (ZMod p))) := by
  intro a b h
  exact MulEquiv.ext fun v =>
    congrArg (fun e : Equiv.Perm (Fin k → Multiplicative (ZMod p)) => e v) h

private lemma ggWTSgn_fin_ne_succ {k : ℕ} {i : Fin k} (hi : i.val + 1 < k) :
    i ≠ ⟨i.val + 1, hi⟩ := by
  intro hh
  have h2 : i.val = i.val + 1 := by
    have := congrArg Fin.val hh
    simpa using this
  omega

private lemma ggWTSgn_isRefl_sgnAut {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {k : ℕ}
    {L' : Type} [Group L'] {A : Subgroup (MulAut L')}
    (Θ : (Fin k → Multiplicative (ZMod p)) ≃* ↥A) (i : Fin k) :
    GGIsReflection p (MulAut.congr Θ (sgnAut i)) :=
  ⟨by rw [← map_pow, sgnAut_sq, map_one],
    (ggIsPseudoReflection_congr Θ (pow_sub_one_eq_one_of_sq hp hp2 (sgnAut_sq i))
      (card_fix_sgnAut hp hp2 i)).2⟩

private lemma ggWTSgn_isRefl_permAut_swap {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {k : ℕ}
    {L' : Type} [Group L'] {A : Subgroup (MulAut L')}
    (Θ : (Fin k → Multiplicative (ZMod p)) ≃* ↥A) {a b : Fin k} (hab : a ≠ b) :
    GGIsReflection p (MulAut.congr Θ (permAut (Equiv.swap a b))) :=
  ⟨by rw [← map_pow, permAut_swap_sq, map_one],
    (ggIsPseudoReflection_congr Θ
      (pow_sub_one_eq_one_of_sq hp hp2 (permAut_swap_sq a b))
      (card_fix_permAut_swap hp hp2 hab)).2⟩

theorem ggTorusWeylTypeW_of_signedEltSC {p r : ℕ} {R : Type} [Group R] {I : Set (MulAut R)}
    (hp : p.Prime) (hp2 : p ≠ 2) (hZ : Subgroup.center R = ⊥)
    (hIp : ∀ φ ∈ I, φ ^ p = 1 → φ ∈ Set.range (MulAut.conj : R →* MulAut R))
    (hcp : GGCenterPrime p R) (h : GGTorusSignedEltSC p R) : GGTorusWeylTypeW p r R I := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  intro L' _ _ ψ A hA
  obtain ⟨hψ, hker, hperf, hAe, hAI, hr, h3, hsc⟩ :=
    NbrTableBExc.ggTorusTBGroup_pow (I := I) hA
  obtain ⟨k, Θ, hk, hW, hS, hP, hN⟩ := exists_signedModelSC (I := {φ | φ ∈ I ∧ φ ^ p = 1})
    hp hp2 (fun φ hφ => hIp φ hφ.1 hφ.2) hZ hcp h hψ hker hperf hAe hAI h3 hsc
  let V := Fin k → Multiplicative (ZMod p)
  let Φ : MulAut V ≃* MulAut ↥A := MulAut.congr Θ
  let Gens : Set (MulAut V) :=
    Set.range (fun i : Fin k => sgnAut i) ∪
      Set.range (fun x : {x : Fin k × Fin k // x.1 ≠ x.2} =>
        permAut (Equiv.swap x.1.1 x.1.2))
  set H : Subgroup (MulAut V) := Subgroup.closure Gens with hH
  set Aut : Subgroup (MulAut ↥A) :=
    ggAutomizer (MulAut.conj : L' →* MulAut L').range A with hAut
  have hgen_mem : ∀ α ∈ Gens, Φ α ∈ Aut := by
    intro α hα
    rcases hα with ⟨i, rfl⟩ | ⟨⟨⟨a, b⟩, hab⟩, rfl⟩
    · obtain ⟨n, hn, hnα⟩ := hS i
      rw [← hnα, hAut]
      exact ggConjAut_mem_ggAutomizer (H := (MulAut.conj : L' →* MulAut L').range) ⟨n, rfl⟩ hn
    · obtain ⟨n, hn, hnα⟩ := hP (Equiv.swap a b)
      rw [← hnα, hAut]
      exact ggConjAut_mem_ggAutomizer (H := (MulAut.conj : L' →* MulAut L').range) ⟨n, rfl⟩ hn
  have hmapΦ : H.map Φ.toMonoidHom = Aut := by
    apply le_antisymm
    · rw [hH, Subgroup.map_le_iff_le_comap]
      exact (Subgroup.closure_le _).mpr (fun α hα => hgen_mem α hα)
    · intro φ hφ
      obtain ⟨g, hgH, hg, hφg⟩ := eq_ggConjAut_of_mem_ggAutomizer hφ
      obtain ⟨n, rfl⟩ := hgH
      have hsp : IsSignedPerm ⇑(Φ.symm φ) := by
        rw [hφg]; exact hN n hg
      have hmemH : Φ.symm φ ∈ H :=
        mem_of_isSignedPerm
          (fun i => Subgroup.subset_closure (Or.inl ⟨i, rfl⟩))
          (fun a b hab => Subgroup.subset_closure (Or.inr ⟨⟨(a, b), hab⟩, rfl⟩))
          hsp
      exact Subgroup.mem_map.mpr ⟨Φ.symm φ, hmemH, by simp⟩
  have hmapPerm : H.map (MulAut.toPerm V) = spSignedGroup k p := by
    rw [hH, MonoidHom.map_closure]
    apply le_antisymm
    · refine (Subgroup.closure_le _).mpr ?_
      rintro x ⟨α, hα, rfl⟩
      rcases hα with ⟨i, rfl⟩ | ⟨⟨⟨a, b⟩, hab⟩, rfl⟩
      · rw [ggWTSgn_toPerm_sgnAut]; exact coordInv_mem_spSignedGroup i
      · rw [ggWTSgn_toPerm_permAut]; exact coordPerm_mem_spSignedGroup (Equiv.swap a b)
    · rw [spSignedGroup]
      refine (Subgroup.closure_le _).mpr ?_
      rintro x ⟨i, rfl⟩
      by_cases hi : i.val + 1 < k
      · rw [spReflPerm_of_lt k p i hi]
        refine Subgroup.subset_closure ⟨permAut (Equiv.swap i ⟨i.val + 1, hi⟩), ?_, ?_⟩
        · exact Or.inr ⟨⟨(i, ⟨i.val + 1, hi⟩), ggWTSgn_fin_ne_succ hi⟩, rfl⟩
        · rw [ggWTSgn_toPerm_permAut]
      · rw [spReflPerm_of_not_lt k p i hi]
        refine Subgroup.subset_closure ⟨sgnAut i, Or.inl ⟨i, rfl⟩, ?_⟩
        rw [ggWTSgn_toPerm_sgnAut]
  let isoHSp : H ≃* ↥(spSignedGroup k p) :=
    (Subgroup.equivMapOfInjective H (MulAut.toPerm V) ggWTSgn_toPerm_injective).trans
      (MulEquiv.subgroupCongr hmapPerm)
  let isoHAut : H ≃* Aut :=
    (Subgroup.equivMapOfInjective H Φ.toMonoidHom Φ.injective).trans
      (MulEquiv.subgroupCongr hmapΦ)
  have isoHSp_apply : ∀ h : H, (↑(isoHSp h) : Equiv.Perm V) = MulAut.toPerm V ↑h := by
    intro h
    change (↑((Subgroup.equivMapOfInjective H (MulAut.toPerm V)
        ggWTSgn_toPerm_injective).trans (MulEquiv.subgroupCongr hmapPerm) h) : Equiv.Perm V) =
      MulAut.toPerm V ↑h
    rw [MulEquiv.trans_apply, MulEquiv.subgroupCongr_apply]
    rfl
  have isoHAut_apply : ∀ h : H, (↑(isoHAut h) : MulAut ↥A) = Φ ↑h := by
    intro h
    change (↑((Subgroup.equivMapOfInjective H Φ.toMonoidHom Φ.injective).trans
        (MulEquiv.subgroupCongr hmapΦ) h) : MulAut ↥A) = Φ ↑h
    rw [MulEquiv.trans_apply, MulEquiv.subgroupCongr_apply]
    rfl
  obtain ⟨e, he⟩ := ggRC_coxeterB_equiv_spSigned (p := p) hp2 (k := k) (by omega)
  let f : (CoxeterMatrix.B k).Group ≃* Aut := (e.trans isoHSp.symm).trans isoHAut
  let g : Fin k → MulAut V := fun i =>
    if hi : i.val + 1 < k then permAut (Equiv.swap i ⟨i.val + 1, hi⟩) else sgnAut i
  have hg_toPerm : ∀ i, MulAut.toPerm V (g i) = spReflPerm k p i := by
    intro i
    by_cases hi : i.val + 1 < k
    · rw [show g i = permAut (Equiv.swap i ⟨i.val + 1, hi⟩) from by
        simp only [g, dif_pos hi], ggWTSgn_toPerm_permAut, spReflPerm_of_lt k p i hi]
    · rw [show g i = sgnAut i from by simp only [g, dif_neg hi],
        ggWTSgn_toPerm_sgnAut, spReflPerm_of_not_lt k p i hi]
  have hg_mem : ∀ i, g i ∈ H := by
    intro i
    rw [hH]
    refine Subgroup.subset_closure ?_
    by_cases hi : i.val + 1 < k
    · refine Or.inr ⟨⟨(i, ⟨i.val + 1, hi⟩), ?_⟩, ?_⟩
      · exact ggWTSgn_fin_ne_succ hi
      · show permAut (Equiv.swap i ⟨i.val + 1, hi⟩) = g i
        simp only [g, dif_pos hi]
    · refine Or.inl ⟨i, ?_⟩
      show sgnAut i = g i
      simp only [g, dif_neg hi]
  have hf_simple : ∀ i, (f ((CoxeterMatrix.B k).simple i) : MulAut ↥A) = Φ (g i) := by
    intro i
    have hei : e ((CoxeterMatrix.B k).simple i) =
        ⟨spReflPerm k p i, spReflPerm_mem_spSignedGroup k p i⟩ := Subtype.ext (he i)
    have hsymm : isoHSp.symm ⟨spReflPerm k p i, spReflPerm_mem_spSignedGroup k p i⟩ =
        ⟨g i, hg_mem i⟩ := by
      rw [MulEquiv.symm_apply_eq]
      apply Subtype.ext
      rw [isoHSp_apply]
      exact (hg_toPerm i).symm
    calc (f ((CoxeterMatrix.B k).simple i) : MulAut ↥A)
        = ↑(isoHAut (isoHSp.symm (e ((CoxeterMatrix.B k).simple i)))) := by
          simp only [f, MulEquiv.trans_apply]
      _ = ↑(isoHAut (isoHSp.symm ⟨spReflPerm k p i,
            spReflPerm_mem_spSignedGroup k p i⟩)) := by rw [hei]
      _ = ↑(isoHAut ⟨g i, hg_mem i⟩) := by rw [hsymm]
      _ = Φ (g i) := isoHAut_apply ⟨g i, hg_mem i⟩
  refine ⟨Fin k, CoxeterMatrix.B k, f, ?_, ?_, ?_⟩
  · refine Or.inl ⟨k, Equiv.refl (Fin k), by omega, Or.inr (Or.inl ⟨by omega, ?_⟩)⟩
    exact (CoxeterMatrix.ext (Matrix.ext fun _ _ => rfl)).symm
  · have hcard : Nat.card ↥Aut = Nat.card ↥(spSignedGroup k p) :=
      Nat.card_congr (isoHAut.symm.trans isoHSp).toEquiv
    have hle := two_pow_mul_factorial_le_card_spSignedGroup (n := k) hp hp2
    have h48 : 48 ≤ Nat.card ↥Aut := by
      rw [hcard]
      calc 48 = 2 ^ 3 * Nat.factorial 3 := by norm_num [Nat.factorial]
        _ ≤ 2 ^ k * Nat.factorial k := Nat.mul_le_mul (Nat.pow_le_pow_right (by norm_num) hk)
            (Nat.factorial_le hk)
        _ ≤ Nat.card ↥(spSignedGroup k p) := hle
    omega
  · intro i
    rw [hf_simple i]
    by_cases hi : i.val + 1 < k
    · rw [show g i = permAut (Equiv.swap i ⟨i.val + 1, hi⟩) from by
        simp only [g, dif_pos hi]]
      obtain ⟨n, hn, hnα⟩ := hP (Equiv.swap i ⟨i.val + 1, hi⟩)
      refine ⟨n, hn, hW n hn, hnα.symm, ?_⟩
      exact ggWTSgn_isRefl_permAut_swap hp hp2 Θ
        (ggWTSgn_fin_ne_succ hi)
    · rw [show g i = sgnAut i from by simp only [g, dif_neg hi]]
      obtain ⟨n, hn, hnα⟩ := hS i
      refine ⟨n, hn, hW n hn, hnα.symm, ?_⟩
      exact ggWTSgn_isRefl_sgnAut hp hp2 Θ i

end CFSG.StandardType

end
