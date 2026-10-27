module

public import CFSG.LocalAnalysis.StandardType.GGSixLinearModelCoords
public import CFSG.LocalAnalysis.StandardType.GGLinearSemisimple
public import CFSG.Timmesfeld.Orders.Classical
public import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.SectionRank.ClassicalOdd
public import CFSG.LocalAnalysis.SectionRank.EvenCover.LinearStep
public import CFSG.LocalAnalysis.SectionRank.SporadicCover
public import CFSG.Sporadic.M23.M23Group
public import CFSG.Sporadic.Th.F2Spec

public section

namespace CFSG.StandardType

open CFSG.Assembly Matrix CFSG.SeitzReduction.LinearPilot

namespace LinModel

theorem pow_three_dvd_ordA {n q : ℕ} (hn : 2 ≤ n) : q ^ 3 ∣ CFSG.Open.ordA n q := by
  unfold CFSG.Open.ordA
  have hg : Nat.gcd (n + 1) (q - 1) ∣ ∏ i ∈ Finset.Icc 2 (n + 1), (q ^ i - 1) := by
    refine (Nat.gcd_dvd_right _ _).trans ((?_ : q - 1 ∣ q ^ 2 - 1).trans
      (Finset.dvd_prod_of_mem (fun i => q ^ i - 1) (by simp; omega : 2 ∈ Finset.Icc 2 (n + 1))))
    simpa only [one_pow] using Nat.sub_dvd_pow_sub_pow q 1 2
  rw [Nat.mul_div_assoc _ hg]
  refine Dvd.dvd.mul_right (pow_dvd_pow q ?_) _
  exact (Nat.le_div_iff_mul_le (by norm_num)).mpr (by nlinarith)

theorem toNat_sq_sub_neg_one_sq (q : ℕ) :
    (((q : ℤ) ^ 2 - (-1 : ℤ) ^ 2).toNat) = (q + 1) * (q - 1) := by
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · simp
  · have h : ((q : ℤ) ^ 2 - (-1 : ℤ) ^ 2) = (((q + 1) * (q - 1) : ℕ) : ℤ) := by
      push_cast [Nat.cast_sub hq]
      ring
    rw [h, Int.toNat_natCast]

theorem pow_three_dvd_ordTwistedA {n q : ℕ} (hn : 2 ≤ n) : q ^ 3 ∣ CFSG.Open.ordTwistedA n q := by
  unfold CFSG.Open.ordTwistedA
  have hg : Nat.gcd (n + 1) (q + 1) ∣
      ∏ i ∈ Finset.Icc 2 (n + 1), (((q : ℤ) ^ i - (-1 : ℤ) ^ i).toNat) := by
    refine (Nat.gcd_dvd_right _ _).trans ?_
    have h2 := Finset.dvd_prod_of_mem (fun i => (((q : ℤ) ^ i - (-1 : ℤ) ^ i).toNat))
      (by simp; omega : 2 ∈ Finset.Icc 2 (n + 1))
    refine Dvd.dvd.trans ?_ h2
    rw [toNat_sq_sub_neg_one_sq]
    exact Dvd.intro _ rfl
  rw [Nat.mul_div_assoc _ hg]
  refine Dvd.dvd.mul_right (pow_dvd_pow q ?_) _
  exact (Nat.le_div_iff_mul_le (by norm_num)).mpr (by nlinarith)

theorem pow_three_dvd_card_of_ggTypeAk {G : Type} [Group G] {f : ℕ} {K : Subgroup G}
    (h : GGTypeAk f K) :
    1 ≤ f ∧ (2 ^ f) ^ 3 ∣ Nat.card (↥K ⧸ Subgroup.center ↥K) := by
  obtain ⟨m', hm', hL | hU⟩ := h
  · rcases hL with ⟨-, hcl⟩ | ⟨hn, -⟩ | ⟨hn, -⟩ | ⟨hn, -⟩
    · refine ⟨hcl.1.2.1, ?_⟩
      rw [(CFSG.Timmesfeld.card_statedClassicalModel_two hcl).1 rfl]
      exact pow_three_dvd_ordA (by omega)
    all_goals omega
  · rcases hU with ⟨-, hcl⟩ | ⟨hn, -⟩ | ⟨hn, -⟩ | ⟨hn, -⟩
    · refine ⟨hcl.1.2.1, ?_⟩
      rw [(CFSG.Timmesfeld.card_statedClassicalModel_two hcl).2.1 rfl]
      exact pow_three_dvd_ordTwistedA (by omega)
    all_goals omega

theorem card_blockSpecialLinear_le {n : ℕ} {F : Type} [Field F] [Finite F]
    {I : Finset (Fin n)} (hI : I.card ≤ 2) :
    Nat.card (blockSpecialLinear (K := F) I) ≤ Nat.card F * (Nat.card F ^ 2 - 1) := by
  rw [← range_blockEmbed,
    ← Nat.card_congr (MonoidHom.ofInjective (blockEmbed_injective (K := F) I)).toEquiv,
    Nat.card_congr (reindexSpecialLinear (K := F) I.equivFin).toEquiv]
  have hq : 2 ≤ Nat.card F := Finite.one_lt_card
  have hq3 : 1 ≤ Nat.card F * (Nat.card F ^ 2 - 1) := by
    have : 4 ≤ Nat.card F ^ 2 := by nlinarith
    exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  rcases (by omega : I.card = 0 ∨ I.card = 1 ∨ I.card = 2) with h | h | h
  · rw [h]
    have h1 : Nat.card (Matrix.SpecialLinearGroup (Fin 0) F) = 1 := by
      rw [Nat.card_eq_one_iff_unique]
      exact ⟨inferInstance, inferInstance⟩
    rw [h1]
    exact hq3
  · rw [h, CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq le_rfl]
    simpa using hq3
  · rw [h, CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (by norm_num)]
    simp

theorem range_conj_comp {G : Type*} [Group G] {m : ℕ} {F : Type} [Field F]
    {ψ : Matrix.SpecialLinearGroup (Fin (m + 1)) F →* G} {g : G}
    (hg : g ∈ Subgroup.normalizer (ψ.range : Set G)) :
    ((MulAut.conj g).toMonoidHom.comp ψ).range = ψ.range := by
  ext x
  constructor
  · rintro ⟨u, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hg (ψ u)).mp ⟨u, rfl⟩
  · intro hx
    have h1 : g⁻¹ * x * g ∈ ψ.range :=
      (Subgroup.mem_normalizer_iff.mp hg (g⁻¹ * x * g)).mpr
        (by rwa [show g * (g⁻¹ * x * g) * g⁻¹ = x by group])
    obtain ⟨u, hu⟩ := h1
    refine ⟨u, ?_⟩
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hu]
    group

end LinModel

theorem ggLinearTypeAkTripleInput_holds : GGLinearTypeAkTripleInput := by
  intro G _ _ m f ψ hker hC b d hb g hg K hK hKA
  set ψ' := (MulAut.conj g).toMonoidHom.comp ψ with hψ'
  have hrange : ψ'.range = ψ.range := LinModel.range_conj_comp hg
  have hker' : ψ'.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin (m + 1))
      (GaloisField 2 f)) := by
    intro u hu
    apply hker
    rw [MonoidHom.mem_ker] at hu ⊢
    simpa [hψ'] using hu
  have hb' : (g * b * g⁻¹, InnerDiagA.diagGL d) ∈ LinFusion.ggInducedPairs ψ' := by
    intro u
    have h1 := LinFusion.mem_ggInducedPairs.mp hb u
    simp only [hψ', MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [← h1]
    group
  have hK' : IsComponentOf K (ψ'.range ⊓
      Subgroup.centralizer (Set.range fun _ : Unit => g * b * g⁻¹)) := by
    rw [hrange, Set.range_const]
    exact hK
  obtain ⟨i, hi⟩ := LinSemisimple.exists_eq_map_blockSpecialLinear_of_isComponentOf hker'
    (d := fun _ : Unit => d) (b := fun _ => g * b * g⁻¹) (fun _ => hb') hK'
  set I := LinSemisimple.eigClass (fun _ : Unit => d) i with hI
  by_cases h3 : 2 < I.card
  · obtain ⟨j₁, hj₁, j₂, hj₂, j₃, hj₃, h12, h13, h23⟩ := Finset.two_lt_card.mp h3
    have e1 := LinSemisimple.mem_eigClass.mp hj₁ ()
    have e2 := LinSemisimple.mem_eigClass.mp hj₂ ()
    have e3 := LinSemisimple.mem_eigClass.mp hj₃ ()
    exact ⟨j₁, j₂, j₃, h12, h13, h23, e1.trans e2.symm, e1.trans e3.symm⟩
  · exfalso
    obtain ⟨hf, hdvd⟩ := LinModel.pow_three_dvd_card_of_ggTypeAk hKA
    have hF : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
    have h1 : Nat.card (↥K ⧸ Subgroup.center ↥K) ≤ Nat.card K :=
      Nat.le_of_dvd Nat.card_pos (Subgroup.card_quotient_dvd_card _)
    have h2 : Nat.card K ≤ Nat.card (blockSpecialLinear (K := GaloisField 2 f) I) := by
      rw [hi]
      exact Nat.le_of_dvd Nat.card_pos (Subgroup.card_map_dvd _ _)
    have h3' := LinModel.card_blockSpecialLinear_le (F := GaloisField 2 f) (I := I) (by omega)
    rw [hF] at h3'
    have h4 : (2 ^ f) ^ 3 ≤ Nat.card (↥K ⧸ Subgroup.center ↥K) := Nat.le_of_dvd Nat.card_pos hdvd
    have hq : 2 ≤ 2 ^ f := by
      calc 2 = 2 ^ 1 := (pow_one 2).symm
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
    have hlt : 2 ^ f * ((2 ^ f) ^ 2 - 1) < (2 ^ f) ^ 3 := by
      have hsq : 1 ≤ (2 ^ f) ^ 2 := Nat.one_le_pow _ _ (by omega)
      calc 2 ^ f * ((2 ^ f) ^ 2 - 1) < 2 ^ f * (2 ^ f) ^ 2 :=
            Nat.mul_lt_mul_of_pos_left (by omega) (by omega)
        _ = (2 ^ f) ^ 3 := by ring
    omega

end CFSG.StandardType
