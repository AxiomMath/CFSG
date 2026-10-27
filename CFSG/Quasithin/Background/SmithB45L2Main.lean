module

public import CFSG.Quasithin.Background.SmithB45L2Class
public import CFSG.Quasithin.Background.SmithB45L2Row
public import CFSG.Quasithin.Background.SmithB45Families

public section

namespace CFSG.Quasithin

open CFSG.QuasithinUnique.Setup.SL2Modules CFSG.QuasithinUnique.Setup.Layer
  CFSG.QuasithinUnique.Setup.Layer.Actor CFSG.Quasithin.JonesParshall CFSG.Quasithin.B45L2
open scoped MatrixGroups

namespace B45L2

section Main

variable {V : Type} [CommGroup V] [Finite V] {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
  [Finite W] {F : Type} [Field F] [Fintype F] [CharP F 2] {L : Subgroup (MulAut V)}

omit [Finite V] [Finite W] [Fintype F] [CharP F 2] in
theorem repOf_nontrivial (θ : V ≃* Multiplicative W) (θL : ↥L ≃* SL(2, F)) :
    ∃ g, repOf θ θL g ≠ 1 := by
  have hne : (uElt (1 : F) : SL(2, F)) ≠ 1 := fun h =>
    one_ne_zero (uElt_injective (h.trans uElt_zero.symm))
  exact ⟨uElt 1, fun h => hne (repOf_injective θ θL (h.trans (map_one _).symm))⟩

omit [Finite V] [Finite W] [Fintype F] [CharP F 2] in
theorem toAdd_act (θ : V ≃* Multiplicative W) (θL : ↥L ≃* SL(2, F)) (l : ↥L) (v : V) :
    Multiplicative.toAdd (θ ((l : MulAut V) v)) =
      repOf θ θL (θL l) (Multiplicative.toAdd (θ v)) := by
  rw [repOf_theta, B42L2.toAdd_binPsi]

omit [Finite W] in
theorem qhat_le_one_of_natural (hV : ∀ v : V, v ^ 2 = 1) {n : ℕ} (hn : 1 ≤ n)
    (hF : Fintype.card F = 2 ^ n) {G : Subgroup (MulAut V)} (hLG : L ≤ G)
    (hirr : XMod.IsIrrSec ↥L (⊥ : Subgroup V) ⊤) (θ : V ≃* Multiplicative W)
    (θL : ↥L ≃* SL(2, F)) (hD : Nat.card (EndRing (repOf θ θL)) = 2 ^ n)
    (hdim : Module.finrank (EndRing (repOf θ θL)) W = 2) :
    qhatOf G ≤ ((1 : ℚ) : WithTop ℚ) := by
  have : Finite W := Finite.of_equiv V (θ.toEquiv.trans Multiplicative.toAdd)
  have : Fact (repOf θ θL).IsIrreducible := ⟨repOf_isIrreducible θ θL hirr⟩
  obtain ⟨φ, hφ⟩ := exists_natural_iso hn hF (repOf θ θL) (repOf_nontrivial θ θL) hD hdim
  refine natural_qhat_le_one hV hn hF hLG θL (θ.trans (AddEquiv.toMultiplicative φ))
    fun l v => ?_
  show φ (Multiplicative.toAdd (θ ((l : MulAut V) v))) = _
  rw [toAdd_act θ θL, hφ]
  rfl

omit [Finite W] in
theorem orthRow_of_orthogonal (hV : ∀ v : V, v ^ 2 = 1) {s : ℕ} (hs : 1 ≤ s)
    (hF : Fintype.card F = 2 ^ (2 * s)) {G : Subgroup (MulAut V)} (hLG : L ≤ G)
    (hirr : XMod.IsIrrSec ↥L (⊥ : Subgroup V) ⊤) (θ : V ≃* Multiplicative W)
    (θL : ↥L ≃* SL(2, F)) (hD : Nat.card (EndRing (repOf θ θL)) = 2 ^ s)
    (hdim : Module.finrank (EndRing (repOf θ θL)) W = 4) :
    BinaryOrthogonalFour L ⊤ ⊥ s ∧ qOf G ≤ ((2 : ℚ) : WithTop ℚ) ∧
      qhatOf G ≤ ((3 / 2 : ℚ) : WithTop ℚ) := by
  have : Finite W := Finite.of_equiv V (θ.toEquiv.trans Multiplicative.toAdd)
  have : Fact (repOf θ θL).IsIrreducible := ⟨repOf_isIrreducible θ θL hirr⟩
  obtain ⟨j, β, hβ⟩ := orth_iso hs hF (repOf θ θL) (repOf_nontrivial θ θL) hD hdim
  refine orth_row hV hs hF hLG (θL.trans (fieldAutEquiv j))
    (θ.trans (AddEquiv.toMultiplicative β)) fun l v => ?_
  show β (Multiplicative.toAdd (θ ((l : MulAut V) v))) = _
  rw [toAdd_act θ θL, hβ]
  rfl

end Main

end B45L2

theorem asB45L2Even_holds : AsB45L2Even := by
  intro V _ _ hV G L hHyp hP h1 h2
  obtain ⟨hZ, f, hf, hmodel⟩ := hP
  obtain ⟨F, _, _, hF, ⟨θL⟩⟩ := B42L2.exists_sl2_of_model hZ hmodel
  have : CharP F 2 := charP_two_of_card_eq hF
  obtain ⟨hLG, -, -, -⟩ := FFC.b4hyp_data hHyp
  obtain ⟨A, hA2, -, hAr⟩ := kq_le_iff.mp h2
  have hoff := (rAV_le_two_iff hV hA2).mp hAr
  have hAN : A ≤ Subgroup.normalizer (L : Set (MulAut V)) :=
    hA2.le.trans (B42L2.le_normalizer_of_b4Hyp hHyp)
  obtain ⟨W, _, _, _, ⟨θ⟩⟩ := exists_binModel_of_binary (V := V) fun v => by
    rw [← pow_two]
    exact hV v
  rcases twoF_class_of_offender hHyp.2.2.2 (by omega) hF θL hAN hA2.ne_bot hA2.isElemAbelian2
      hoff θ with ⟨hD, hdim⟩ | ⟨s, hfs, hD, hdim⟩
  · exact absurd (B45L2.qhat_le_one_of_natural hV (by omega) hF hLG hHyp.2.2.2 θ θL hD hdim)
      (not_le.mpr h1)
  · have hs : 1 ≤ s := by omega
    obtain ⟨hO, hq, hqh⟩ := B45L2.orthRow_of_orthogonal hV hs (by rw [hF, hfs]) hLG hHyp.2.2.2
      θ θL hD hdim
    exact Or.inl (Or.inr (Or.inl ⟨s, hs, hO, hq, hqh⟩))

theorem asB45Alt5_holds : AsB45Alt5 := by
  classical
  intro V _ _ hV G L hHyp hP h1 _
  obtain ⟨hZ, -, hmodel⟩ := hP
  obtain ⟨F, _, _, hF, ⟨θL⟩⟩ := B42L2.exists_sl2_of_model hZ hmodel
  have hF4 : Fintype.card F = 4 := by rw [hF]; norm_num
  have : CharP F 2 := charP_two_of_card_eq hF
  obtain ⟨hLG, -, -, -⟩ := FFC.b4hyp_data hHyp
  obtain ⟨W, _, _, _, ⟨θ⟩⟩ := exists_binModel_of_binary (V := V) fun v => by
    rw [← pow_two]
    exact hV v
  set ρ := repOf θ θL with hρ
  have hirr : ρ.IsIrreducible := repOf_isIrreducible θ θL hHyp.2.2.2
  have : Fact ρ.IsIrreducible := ⟨hirr⟩
  have hnt := B45L2.repOf_nontrivial θ θL
  let _ : Fintype (Projectivization F (Fin 2 → F)) := Fintype.ofFinite _
  have hW16 : Nat.card W = 16 := by
    obtain ⟨hcases, -, -, -, -, h16a, h16b⟩ :=
      irreducible_binary_SL2_four_module_production hF4 ρ hirr
    rcases hcases with ⟨φ, hφ⟩ | ⟨φ, -⟩ | ⟨φ, -⟩
    · exfalso
      obtain ⟨g, hg⟩ := hnt
      apply hg
      apply LinearMap.ext
      intro w
      exact φ.injective (hφ g w)
    · rw [Nat.card_congr φ.toEquiv, h16a]
    · rw [Nat.card_congr φ.toEquiv, h16b]
  obtain ⟨d, hd1, hDcard, hdesc⟩ :=
    binary_SL2_irreducible_Frobenius_descent (n := 2) (by norm_num) hF ρ hnt
  have hfinD : Finite (EndRing ρ) := finite_endRing ρ
  have : Module.Finite (EndRing ρ) W := Module.Finite.of_finite
  obtain ⟨E, hEF, hEfin, hEchar, ιF, ιD, J, hJne, hJn, -, -, hdim⟩ :=
    hdesc (Module.finBasis (EndRing ρ) W)
  have hJ2 : J.card ≤ 2 := by
    calc J.card ≤ (Finset.range 2).card :=
          Finset.card_le_card (fun i hi => Finset.mem_range.mpr (hJn i hi))
      _ = 2 := Finset.card_range 2
  have hJ1 : 1 ≤ J.card := Finset.card_pos.mpr hJne
  have hWd : 2 ^ (d * 2 ^ J.card) = 2 ^ 4 := by
    rw [pow_mul, ← hDcard, ← hdim, ← natCard_eq_pow_finrank (ρ := ρ), hW16]
    norm_num
  have hexp : d * 2 ^ J.card = 4 := Nat.pow_right_injective le_rfl hWd
  rcases (by omega : J.card = 1 ∨ J.card = 2) with hJ | hJ
  ·
    exfalso
    rw [hJ] at hexp hdim
    exact absurd (B45L2.qhat_le_one_of_natural hV (by norm_num) hF hLG hHyp.2.2.2 θ θL
      (by rw [hDcard]; congr 1; omega) hdim) (not_le.mpr h1)
  ·
    rw [hJ] at hexp hdim
    obtain ⟨hO, hq, hqh⟩ := B45L2.orthRow_of_orthogonal hV le_rfl (by rw [hF]) hLG
      hHyp.2.2.2 θ θL (by rw [hDcard]; congr 1; omega) hdim
    exact Or.inl (Or.inr (Or.inl ⟨1, le_rfl, hO, hq, hqh⟩))

end CFSG.Quasithin
