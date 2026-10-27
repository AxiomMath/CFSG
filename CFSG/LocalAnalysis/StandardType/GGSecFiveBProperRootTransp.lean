module

public import CFSG.LocalAnalysis.StandardType.GGTableBUnitDvdAct
public import CFSG.LocalAnalysis.StandardType.GGTableBStdSub
public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallUnitDvdBlock
public import CFSG.LocalAnalysis.StandardType.GGOneFiveDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.ClassicalGroups.UnitaryFlag

variable {G : Type} [Group G] {L Bs : Subgroup G} {F : Type} [Field F] {f d : ℕ}
  {φ : ↥(unitarySU 2 f F d) →* ↥L}

private lemma phi_permSU_swap_mul_self (hK : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 f F) {s t : Fin d} :
    (φ (LineU.permSU hK (Equiv.swap s t)) : G) *
      (φ (LineU.permSU hK (Equiv.swap s t)) : G) = 1 := by
  have hPP : LineU.permSU hK (Equiv.swap s t) * LineU.permSU hK (Equiv.swap s t) = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_one, LineU.coe_permSU, ← map_mul,
      Equiv.swap_mul_self, map_one]
  have h1 : (φ (LineU.permSU hK (Equiv.swap s t)) : ↥L) *
      (φ (LineU.permSU hK (Equiv.swap s t)) : ↥L) = 1 := by
    rw [← map_mul, hPP, map_one]
  simpa only [Subgroup.coe_mul, Subgroup.coe_one] using congrArg (Subtype.val : ↥L → G) h1

private lemma exists_conjN_diag (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hK : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 f F) {s t : Fin d} {b : ↥Bs}
    {u : Fin d → F} (hu : LineU.ActsDiagU φ (ggGamma L hN b) u) :
    ∃ E : ↥(unitarySU 2 f F d),
      ((E : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) =
        Matrix.diagonal (fun k => u (Equiv.swap s t k) * (u k)⁻¹) ∧
      (b : G) * (φ (LineU.permSU hK (Equiv.swap s t)) : G) * (b : G)⁻¹ =
        (φ (LineU.permSU hK (Equiv.swap s t)) : G) * (φ E : G) := by
  obtain ⟨D, hD, hDu, hact⟩ := hu
  let P : ↥(unitarySU 2 f F d) := LineU.permSU hK (Equiv.swap s t)
  let E : ↥(unitarySU 2 f F d) := P⁻¹ * LineU.conjN D hD P
  have hEmat : ((E : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) =
      Matrix.diagonal (fun k => u (Equiv.swap s t k) * (u k)⁻¹) := by
    have hEcoe : ((E : GL (Fin d) F)) =
        (CFSG.RankThree.Classical.permGL (Equiv.swap s t))⁻¹ * D *
          CFSG.RankThree.Classical.permGL (Equiv.swap s t) * D⁻¹ := by
      simp only [E, P, Subgroup.coe_mul, Subgroup.coe_inv, LineU.coe_conjN, LineU.coe_permSU]
      group
    rw [hEcoe]
    simp only [Units.val_mul]
    have hconj := LineU.permMatrix_conj_diag (σ := (Equiv.swap s t)⁻¹) u
    rw [inv_inv] at hconj
    rw [hDu, LineU.coe_permGL_matrix, LineU.coe_permGL_inv_matrix, hconj,
      LineU.coe_inv_diag hDu, Matrix.diagonal_mul_diagonal]
  have hbc : ggGamma L hN b (φ P) = φ P * φ E := by
    rw [hact P, ← map_mul]
    congr 1
    apply Subtype.ext
    simp only [E, P, Subgroup.coe_mul, Subgroup.coe_inv, LineU.coe_conjN]
    group
  refine ⟨E, hEmat, ?_⟩
  have hcoe := congrArg (Subtype.val : ↥L → G) hbc
  rw [ggGamma_coe] at hcoe
  simpa only [P, Subgroup.coe_mul] using hcoe

private lemma conj_eq_of_diag_action
    (hK : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 f F) {s t : Fin d} {b : ↥Bs}
    {E : ↥(unitarySU 2 f F d)}
    (heq : (b : G) * (φ (LineU.permSU hK (Equiv.swap s t)) : G) * (b : G)⁻¹ =
      (φ (LineU.permSU hK (Equiv.swap s t)) : G) * (φ E : G)) :
    (φ (LineU.permSU hK (Equiv.swap s t)) : G) * (b : G) *
      (φ (LineU.permSU hK (Equiv.swap s t)) : G)⁻¹ = (φ E : G) * (b : G) := by
  have hgg := phi_permSU_swap_mul_self (L := L) (φ := φ) hK (s := s) (t := t)
  have hinv : (φ (LineU.permSU hK (Equiv.swap s t)) : G)⁻¹ =
      (φ (LineU.permSU hK (Equiv.swap s t)) : G) := inv_eq_of_mul_eq_one_right hgg
  have hbP : (b : G) * (φ (LineU.permSU hK (Equiv.swap s t)) : G) =
      (φ (LineU.permSU hK (Equiv.swap s t)) : G) * (φ E : G) * (b : G) := by
    calc (b : G) * (φ (LineU.permSU hK (Equiv.swap s t)) : G)
        = (b : G) * (φ (LineU.permSU hK (Equiv.swap s t)) : G) * (b : G)⁻¹ * (b : G) := by
          group
      _ = ((φ (LineU.permSU hK (Equiv.swap s t)) : G) * (φ E : G)) * (b : G) := by rw [heq]
  calc (φ (LineU.permSU hK (Equiv.swap s t)) : G) * (b : G) *
        (φ (LineU.permSU hK (Equiv.swap s t)) : G)⁻¹
      = (φ (LineU.permSU hK (Equiv.swap s t)) : G) * (b : G) *
          (φ (LineU.permSU hK (Equiv.swap s t)) : G) := by rw [hinv]
    _ = (φ (LineU.permSU hK (Equiv.swap s t)) : G) *
          ((b : G) * (φ (LineU.permSU hK (Equiv.swap s t)) : G)) := by group
    _ = (φ (LineU.permSU hK (Equiv.swap s t)) : G) *
          (((φ (LineU.permSU hK (Equiv.swap s t)) : G) * (φ E : G)) * (b : G)) := by
        rw [hbP]
    _ = ((φ (LineU.permSU hK (Equiv.swap s t)) : G) *
          (φ (LineU.permSU hK (Equiv.swap s t)) : G)) * (φ E : G) * (b : G) := by group
    _ = (φ E : G) * (b : G) := by rw [hgg]; group

private lemma diag_eq_of_conj_eq (hM : UnitTB.Model φ)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G)) (hd : 3 ≤ d) {s t : Fin d}
    {b : ↥Bs} {u : Fin d → F} (hu : LineU.ActsDiagU φ (ggGamma L hN b) u)
    (hfix : (φ (LineU.permSU hM.field (Equiv.swap s t)) : G) * (b : G) *
      (φ (LineU.permSU hM.field (Equiv.swap s t)) : G)⁻¹ = (b : G)) :
    u s = u t := by
  obtain ⟨E, hEmat, heq1⟩ := exists_conjN_diag (s := s) (t := t) hN hM.field hu
  have hge := conj_eq_of_diag_action hM.field (s := s) (t := t) heq1
  have hphiE : (φ E : ↥L) = 1 := by
    apply Subtype.ext
    have h2 : (φ E : G) * (b : G) = 1 * (b : G) := by
      rw [← hge, hfix, one_mul]
    simpa only [Subgroup.coe_one] using mul_right_cancel h2
  obtain ⟨c, hc⟩ := hM.ker E hphiE
  have hent : ∀ k, u (Equiv.swap s t k) * (u k)⁻¹ = c := by
    intro k
    have hk := congrFun (congrFun (hEmat.symm.trans hc) k) k
    simpa only [Matrix.diagonal_apply_eq] using hk
  obtain ⟨k, hks, hkt⟩ := LineU.exists_not_mem_two hd s t
  have hck : c = 1 := by
    have h := hent k
    rw [Equiv.swap_apply_of_ne_of_ne hks hkt, mul_inv_cancel₀ (hu.ne_zero k)] at h
    exact h.symm
  have hs := hent s
  rw [Equiv.swap_apply_left, hck] at hs
  exact ((mul_inv_eq_one₀ (hu.ne_zero s)).mp hs).symm

private lemma conj_eq_of_diag_eq (hK : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 f F)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G)) {s t : Fin d} {b : ↥Bs} {u : Fin d → F}
    (hu : LineU.ActsDiagU φ (ggGamma L hN b) u) (hut : u s = u t) :
    (φ (LineU.permSU hK (Equiv.swap s t)) : G) * (b : G) *
      (φ (LineU.permSU hK (Equiv.swap s t)) : G)⁻¹ = (b : G) := by
  obtain ⟨E, hEmat, heq1⟩ := exists_conjN_diag (s := s) (t := t) hN hK hu
  have hge := conj_eq_of_diag_action hK (s := s) (t := t) heq1
  have hdiag1 : (fun k => u (Equiv.swap s t k) * (u k)⁻¹) = fun _ => (1 : F) := by
    funext k
    by_cases hks : k = s
    · rw [hks, Equiv.swap_apply_left, ← hut, mul_inv_cancel₀ (hu.ne_zero s)]
    · by_cases hkt : k = t
      · rw [hkt, Equiv.swap_apply_right, hut, mul_inv_cancel₀ (hu.ne_zero t)]
      · rw [Equiv.swap_apply_of_ne_of_ne hks hkt, mul_inv_cancel₀ (hu.ne_zero k)]
  have hE1 : E = 1 := by
    apply Subtype.ext
    apply Units.ext
    rw [hEmat, hdiag1, Matrix.diagonal_one]
    simp only [Subgroup.coe_one, Units.val_one]
  rw [hge, hE1, map_one, Subgroup.coe_one, one_mul]

private lemma conj_mem_centralizer (hK : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 f F)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G)) {p : ℕ} (hBs : IsElemAbelian p Bs)
    (hdiag : ∀ a ∈ (ggGamma L hN).range, ∃ u : Fin d → F, LineU.ActsDiagU φ a u)
    {s t : Fin d} {b : G} (hb : b ∈ Bs) :
    (φ (LineU.permSU hK (Equiv.swap s t)) : G) * b *
      (φ (LineU.permSU hK (Equiv.swap s t)) : G)⁻¹ ∈ Subgroup.centralizer (Bs : Set G) := by
  obtain ⟨u, hu⟩ := hdiag (ggGamma L hN ⟨b, hb⟩)
    (MonoidHom.mem_range.mpr ⟨⟨b, hb⟩, rfl⟩)
  obtain ⟨E, hEmat, heq1⟩ := exists_conjN_diag (s := s) (t := t) hN hK hu
  have hge := conj_eq_of_diag_action hK (s := s) (t := t) heq1
  rw [hge, Subgroup.mem_centralizer_iff]
  intro c hc
  obtain ⟨v, hv⟩ := hdiag (ggGamma L hN ⟨c, hc⟩)
    (MonoidHom.mem_range.mpr ⟨⟨c, hc⟩, rfl⟩)
  have hfix := hv.fix_of_diagonal E hEmat
  have hfixG : c * (φ E : G) * c⁻¹ = (φ E : G) := by
    have := congrArg (Subtype.val : ↥L → G) hfix
    rw [ggGamma_coe] at this
    exact this
  have hcE : c * (φ E : G) = (φ E : G) * c := by
    calc c * (φ E : G) = c * (φ E : G) * c⁻¹ * c := by group
      _ = (φ E : G) * c := by rw [hfixG]
  have hbc : b * c = c * b := CFSG.Open.IsElemAbelian.comm hBs hb hc
  calc c * ((φ E : G) * b) = (c * (φ E : G)) * b := by group
    _ = ((φ E : G) * c) * b := by rw [hcE]
    _ = (φ E : G) * (c * b) := by group
    _ = (φ E : G) * (b * c) := by rw [← hbc]
    _ = ((φ E : G) * b) * c := by group

private lemma conj_mem_of_mem (hK : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 f F)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G)) {p : ℕ} (hBs : IsElemAbelian p Bs)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hdiag : ∀ a ∈ (ggGamma L hN).range, ∃ u : Fin d → F, LineU.ActsDiagU φ a u)
    {s t : Fin d} {b : G} (hb : b ∈ Bs) :
    (φ (LineU.permSU hK (Equiv.swap s t)) : G) * b *
      (φ (LineU.permSU hK (Equiv.swap s t)) : G)⁻¹ ∈ Bs := by
  have hcen := conj_mem_centralizer hK hN hBs hdiag (s := s) (t := t) hb
  have hpow : ((φ (LineU.permSU hK (Equiv.swap s t)) : G) * b *
      (φ (LineU.permSU hK (Equiv.swap s t)) : G)⁻¹) ^ p = 1 := by
    rw [conj_pow, hBs.2 b hb, mul_one, mul_inv_cancel]
  exact hSC _ hcen hpow

private lemma conj_mem_normalizer (hK : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 f F)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G)) {p : ℕ} (hBs : IsElemAbelian p Bs)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hdiag : ∀ a ∈ (ggGamma L hN).range, ∃ u : Fin d → F, LineU.ActsDiagU φ a u)
    {s t : Fin d} :
    (φ (LineU.permSU hK (Equiv.swap s t)) : G) ∈
      Subgroup.normalizer (Bs : Set G) := by
  have hforward : ∀ b ∈ Bs,
      (φ (LineU.permSU hK (Equiv.swap s t)) : G) * b *
        (φ (LineU.permSU hK (Equiv.swap s t)) : G)⁻¹ ∈ Bs := fun b hb =>
    conj_mem_of_mem hK hN hBs hSC hdiag (s := s) (t := t) hb
  have hgg := phi_permSU_swap_mul_self (L := L) (φ := φ) hK (s := s) (t := t)
  have hinv : (φ (LineU.permSU hK (Equiv.swap s t)) : G)⁻¹ =
      (φ (LineU.permSU hK (Equiv.swap s t)) : G) := inv_eq_of_mul_eq_one_right hgg
  rw [Subgroup.mem_normalizer_iff]
  intro c
  constructor
  · exact hforward c
  · intro hc
    have hy := hforward _ hc
    have hcc : (φ (LineU.permSU hK (Equiv.swap s t)) : G) *
        ((φ (LineU.permSU hK (Equiv.swap s t)) : G) * c *
          (φ (LineU.permSU hK (Equiv.swap s t)) : G)⁻¹) *
        (φ (LineU.permSU hK (Equiv.swap s t)) : G)⁻¹ = c := by
      calc (φ (LineU.permSU hK (Equiv.swap s t)) : G) *
            ((φ (LineU.permSU hK (Equiv.swap s t)) : G) * c *
              (φ (LineU.permSU hK (Equiv.swap s t)) : G)⁻¹) *
            (φ (LineU.permSU hK (Equiv.swap s t)) : G)⁻¹
          = ((φ (LineU.permSU hK (Equiv.swap s t)) : G) *
              (φ (LineU.permSU hK (Equiv.swap s t)) : G)) * c *
              ((φ (LineU.permSU hK (Equiv.swap s t)) : G)⁻¹ *
                (φ (LineU.permSU hK (Equiv.swap s t)) : G)⁻¹) := by group
        _ = c := by rw [hinv, hgg]; group
    rwa [hcc] at hy

theorem exists_native_transposition {p : ℕ} (hM : UnitTB.Model φ) (hd : 3 ≤ d)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G)) (hBs : IsElemAbelian p Bs)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hdiag : ∀ a ∈ (ggGamma L hN).range, ∃ t : Fin d → F, LineU.ActsDiagU φ a t)
    {s t : Fin d} (hst : s ≠ t) :
    ∃ g ∈ L, g ∈ Subgroup.normalizer (Bs : Set G) ∧ g ≠ 1 ∧ g ^ 2 = 1 ∧
      ∀ b : ↥Bs, (g * b * g⁻¹ = b ↔
        ∀ σ : Fin d → Fˣ, SmallU.ActsU φ (ggGamma L hN b) σ → σ s = σ t) := by
  let P := LineU.permSU hM.field (Equiv.swap s t)
  let g : G := (φ P : ↥L)
  have hgL : g ∈ L := (φ P).2
  have hgg : g * g = 1 :=
    phi_permSU_swap_mul_self (L := L) (φ := φ) hM.field (s := s) (t := t)
  have hg2 : g ^ 2 = 1 := by rw [pow_two]; exact hgg
  have hg1 : g ≠ 1 := by
    intro hg
    have hphi : (φ P : ↥L) = 1 := by
      apply Subtype.ext
      simpa only [g, Subgroup.coe_one] using hg
    obtain ⟨c, hc⟩ := hM.ker P hphi
    have hPmat : ((P : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) =
        (Equiv.swap s t).permMatrix F := by
      simp only [P]
      rw [LineU.coe_permSU, LineU.coe_permGL_matrix, Equiv.swap_inv]
    have h1 : ((P : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) s t = 1 := by
      rw [hPmat, CFSG.RankThree.Classical.permMatrix_apply']
      simp [Equiv.swap_apply_left]
    have h0 : ((P : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) s t = 0 := by
      rw [hc, Matrix.diagonal_apply_ne _ hst]
    rw [h0] at h1
    exact zero_ne_one h1
  have hnorm : g ∈ Subgroup.normalizer (Bs : Set G) :=
    conj_mem_normalizer hM.field hN hBs hSC hdiag (s := s) (t := t)
  refine ⟨g, hgL, hnorm, hg1, hg2, fun b => ?_⟩
  constructor
  · intro hfix σ hσ
    have hu : LineU.ActsDiagU φ (ggGamma L hN b) (fun k => (σ k : F)) := hσ.actsDiagU
    have heq := diag_eq_of_conj_eq hM hN hd hu (by simpa only [g, P] using hfix)
    exact Units.ext heq
  · intro hσeq
    obtain ⟨u, hu⟩ := hdiag (ggGamma L hN b) (MonoidHom.mem_range.mpr ⟨b, rfl⟩)
    obtain ⟨σ, hσu, hσ⟩ := SmallU.ActsU.of_actsDiagU hu
    have hst_eq : σ s = σ t := hσeq σ hσ
    have hut : u s = u t := by
      rw [← hσu s, ← hσu t, hst_eq]
    simpa only [g, P] using conj_eq_of_diag_eq (s := s) (t := t) hM.field hN hu hut

end CFSG.StandardType

end
