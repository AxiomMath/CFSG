module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDegDefs
import CFSG.LocalAnalysis.StandardType.GGQTwoDegFrame
import CFSG.LocalAnalysis.StandardType.GGQTwoDegLastAux

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.Blueprint CFSG.Open

variable {G : Type} [Group G] [Finite G]

theorem qTwoDeg_not_span_of_last_row
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hcfg : GGSecFiveRouteCfg 3 B Bs x L D J 𝒦)
    {k : QTwoRowKind} {m d c : ℕ} (hrow : QTwoRowData k m d c Bs L x) (hk : k = .psuFull)
    {ι : Type} {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hP : GGCoxeterPres 3 (ggAutomizerJoin L Bs 𝒦) M e)
    {N : ℕ} (hN : 6 ≤ N) {e' : Fin (N - 1) ≃ ι}
    (hM : M = (CoxeterMatrix.A (N - 1)).reindex e')
    (hNm : N = m + 1) : False := by
  classical
  subst hk
  obtain ⟨-, hc⟩ := hrow.dc.2.2.2.2 rfl
  have h3m : 3 ∣ m := hrow.dvd (by decide)
  have hN3 : ¬ 3 ∣ N := by omega
  have hBs := hrow.elemAb
  have hNT : GGNoTransvection 3 Bs := hcfg.1.2.2.2.1
  have hle : ggAutomizerJoin L Bs 𝒦 ≤ ggAutomizer (⊤ : Subgroup G) Bs := by
    unfold ggAutomizerJoin
    refine sup_le (ggAutomizer_mono Bs le_top) ?_
    exact iSup₂_le fun K _ => ggAutomizer_mono Bs le_top
  have hind : ∀ φ ∈ ggAutomizerJoin L Bs 𝒦, φ ∈ ggInduced (⊤ : Subgroup G) Bs :=
    fun φ hφ => mem_ggAutomizer_iff.mp (hle hφ)
  have hW : GGWeylOfType 3 (CoxeterMatrix.A (N - 1)) (ggAutomizerJoin L Bs 𝒦) := by
    subst hM
    exact GGWeylOfType.of_reindex ⟨e, hP.2⟩
  obtain ⟨V, hVadd, hVmod, ⟨ιV⟩⟩ := exists_ggLinData (p := 3) hBs
  letI := hVadd
  letI := hVmod
  obtain ⟨e₂, h, α, hα, hrefl, hpair⟩ :=
    qTwoDegLastAux_datum hNT hind (r := N - 1) (by omega) hW ιV
  have hlin : LinearIndependent (ZMod 3) h :=
    qTwoDegLastAux_linearIndependent (by omega) h α hpair
  have hP₂ : ∀ i : Fin (N - 1), GGIsReflection 3
      ((e₂ ((CoxeterMatrix.A (N - 1)).simple i) : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) :=
    fun i => ggIsReflection_of_eq_reflection (by norm_num) ιV (hα i) (hrefl i)
  obtain ⟨ρ, hρ, hρgen⟩ := qTwoDegFrame_perm_equiv (e' := Equiv.refl (Fin (N - 1))) hP₂
    (by omega) (by ext i j; rfl)
  obtain ⟨ω, hω⟩ := qTwoDegFrame_stabilizer hBs ρ hρ le_sup_left (by omega) hrow.weyl hNm
  let last : Fin N := ⟨N - 1, by omega⟩
  let E : Equiv.Perm (Fin N) →* MulAut ↥Bs :=
    (ggAutomizerJoin L Bs 𝒦).subtype.comp ρ.toMonoidHom
  let w : Equiv.Perm (Fin N) := Equiv.swap ω last
  have hstab : MulAction.stabilizer (Equiv.Perm (Fin N)) ω =
      (MulAction.stabilizer (Equiv.Perm (Fin N)) last).map (MulAut.conj w).toMonoidHom := by
    have := MulAction.stabilizer_smul_eq_stabilizer_map_conj w last
    simpa [w, Equiv.Perm.smul_def] using this
  have hAL : ggAutomizer L Bs = ((MulAction.stabilizer (Equiv.Perm (Fin N)) last).map E).map
      (MulAut.conj (E w)).toMonoidHom := by
    rw [hω, hstab, Subgroup.map_map, Subgroup.map_map]
    congr 1
    refine MonoidHom.ext fun x => ?_
    show E (w * x * w⁻¹) = E w * E x * (E w)⁻¹
    rw [map_mul, map_mul, map_inv]
  have hcomm := hrow.comm
  rw [hAL, qTwoDegLastAux_card_commSpace_conj] at hcomm
  let S : Finset (Fin (N - 1)) := Finset.univ.filter fun i => i.val + 2 < N
  have hScard : S.card = N - 2 := by
    have himg : S.image (fun i : Fin (N - 1) => i.val) = Finset.range (N - 2) := by
      ext j
      simp only [S, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_range]
      constructor
      · rintro ⟨i, hi, rfl⟩
        omega
      · intro hj
        have hjN : j < N - 1 := by omega
        refine ⟨⟨j, hjN⟩, ?_, rfl⟩
        have : (⟨j, hjN⟩ : Fin (N - 1)).val = j := rfl
        rw [this]
        omega
    rw [← Finset.card_image_of_injective S Fin.val_injective, himg, Finset.card_range]
  have hS : ∀ i ∈ S, ((e₂ ((CoxeterMatrix.A (N - 1)).simple i) :
      ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) ∈
      (MulAction.stabilizer (Equiv.Perm (Fin N)) last).map E := by
    intro i hi
    have hi2 : i.val + 2 < N := by simpa [S] using hi
    have hi1 : i.val + 1 < N := by omega
    have hgen : ((e₂ ((CoxeterMatrix.A (N - 1)).simple i) :
        ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) =
        ((ρ (Equiv.swap ⟨i.val, by omega⟩ ⟨i.val + 1, hi1⟩) :
          ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) := by
      simpa using (hρgen i.val hi1).symm
    rw [hgen]
    refine Subgroup.mem_map.mpr ⟨Equiv.swap ⟨i.val, by omega⟩ ⟨i.val + 1, hi1⟩, ?_, rfl⟩
    rw [MulAction.mem_stabilizer_iff, Equiv.Perm.smul_def]
    exact Equiv.swap_apply_of_ne_of_ne
      (by intro h; have hv := congrArg Fin.val h; simp [last] at hv; omega)
      (by intro h; have hv := congrArg Fin.val h; simp [last] at hv; omega)
  have hge := qTwoDegLastAux_card_commSpace_ge ιV h hlin α hα
    (fun i => ((e₂ ((CoxeterMatrix.A (N - 1)).simple i) : ↥(ggAutomizerJoin L Bs 𝒦)) :
      MulAut ↥Bs)) hrefl _ S hS
  rw [hcomm, hScard, hc] at hge
  have : 3 ^ (N - 2) ≤ 3 ^ (m - 2) := hge
  have hlt : 3 ^ (m - 2) < 3 ^ (N - 2) :=
    Nat.pow_lt_pow_right (by norm_num) (by omega)
  omega

end CFSG.StandardType.QTwo

end
