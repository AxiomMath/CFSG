module

import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.ASetSummands
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.Om4mSummand
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KNatOm4mA.Basic
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC56Fix
import CFSG.Quasithin.Background.RonanE42Small
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs
public import CFSG.Quasithin.Background.B1Coprime
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22 Subgroup

variable {W : Type} [CommGroup W]

theorem not_mem_aSet_of_le_stabSub [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {H : Subgroup (MulAut W)} {I₁ I₂ : Subgroup W} {k : ℕ} (h₁ : I₁ ⊓ I₂ = ⊥)
    (h₁' : I₁ ⊔ I₂ = ⊤) (h₁inv : StableUnder H I₁)
    (h₁faith : ∀ g ∈ H, (∀ v ∈ I₁, g v = v) → g = 1)
    (h₁S : ∃ S : Subgroup (MulAut W), S ≤ H ∧ IsPGroup 2 S ∧ Nat.card ↥(I₁ ⊓ fixV S) ≤ 2 ^ k)
    (h₁a : E3.aParam (autSub (normalizer (H : Set (MulAut W))) I₁) ≤ k)
    (h₂ne : I₂ ≠ ⊥) (h₂inv : StableUnder H I₂)
    (h₂irr : ∀ J, StableUnder H J → J ≤ I₂ → J = ⊥ ∨ J = I₂)
    {A : Subgroup (MulAut W)} (hA : A ∈ E3.aSet (k + 1) (normalizer (H : Set (MulAut W))))
    (hAI : A ≤ stabSub I₁) : False := by
  by_cases hAU : autSub A I₁ = ⊥
  ·
    have htriv : ∀ a ∈ A, ∀ v ∈ I₁, a v = v := by
      intro a ha v hv
      have h1 : resHom I₁ ⟨a, hAI ha⟩ ∈ autSub A I₁ := mem_autSub.mpr ⟨⟨a, hAI ha⟩, ha, rfl⟩
      rw [hAU, Subgroup.mem_bot] at h1
      exact congrArg Subtype.val (DFunLike.congr_fun h1 ⟨v, hv⟩)
    have hcomm : ∀ a ∈ A, ∀ h ∈ H, a * h = h * a := by
      intro a ha h hh
      have hc : a * h * a⁻¹ * h⁻¹ ∈ H :=
        H.mul_mem ((Subgroup.mem_normalizer_iff.mp (hA.1 ha) h).mp hh) (H.inv_mem hh)
      have hc1 : a * h * a⁻¹ * h⁻¹ = 1 := h₁faith _ hc fun v hv => by
        have hhv : h⁻¹ v ∈ I₁ := h₁inv _ (H.inv_mem hh) v hv
        rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.mul_apply,
          htriv _ (A.inv_mem ha) _ hhv, MulAut.apply_inv_self, htriv a ha v hv]
      exact mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp hc1)
    obtain ⟨S, hSH, hS2, hScard⟩ := h₁S
    obtain ⟨v₀, hv₀I₂, hv₀1, hv₀S⟩ :=
      B1.exists_fixed_ne_one hW hS2 (fun s hs m hm => h₂inv s (hSH hs) m hm) h₂ne
    have hv₀A : v₀ ∉ fixV A := by
      intro hv
      have hst : StableUnder H (fixV A) := fun h hh x hx => mem_fixV.2 fun a ha => by
        rw [← MulAut.mul_apply, hcomm a ha h hh, MulAut.mul_apply, mem_fixV.1 hx a ha]
      have hle : I₁ ≤ fixV A := fun v hv => mem_fixV.2 fun a ha => htriv a ha v hv
      rcases eq_or_eq_top_of_le h₁' h₂inv h₂irr hst hle with h | h
      · have h3 : v₀ ∈ I₁ ⊓ I₂ := ⟨h ▸ hv, hv₀I₂⟩
        rw [h₁] at h3
        exact hv₀1 (Subgroup.mem_bot.mp h3)
      · apply hA.2.1
        rw [eq_bot_iff]
        intro a ha
        rw [Subgroup.mem_bot]
        ext w
        exact mem_fixV.1 (h ▸ Subgroup.mem_top w) a ha
    have hmemI : ∀ a ∈ A, a v₀ * v₀⁻¹ ∈ I₁ ⊓ fixV S := by
      intro a ha
      refine ⟨?_, mem_fixV.2 fun s hs => ?_⟩
      · let φ : W →* W :=
          { toFun := fun w => a w * w⁻¹
            map_one' := by simp
            map_mul' := fun x y => by
              simp only [map_mul, mul_inv]
              simp only [mul_assoc, mul_left_comm, mul_comm] }
        have hφ : ∀ w, φ w = a w * w⁻¹ := fun w => rfl
        have hC'st : StableUnder H (I₁.comap φ) := fun h hh w hw => by
          change φ (h w) ∈ I₁
          have hah : a (h w) = h (a w) := by
            have h1 := congrArg (fun f : MulAut W => f w) (hcomm a ha h hh)
            simpa [MulAut.mul_apply] using h1
          rw [hφ, hah, ← map_inv, ← map_mul]
          exact h₁inv h hh _ hw
        have hC'I : I₁ ≤ I₁.comap φ := fun v hv => by
          change φ v ∈ I₁
          rw [hφ, htriv a ha v hv, mul_inv_cancel]
          exact I₁.one_mem
        rcases eq_or_eq_top_of_le h₁' h₂inv h₂irr hC'st hC'I with h | h
        · have haa : a (a v₀) = v₀ := by
            rw [← MulAut.mul_apply, ← sq, hA.2.2.1.2 a ha, MulAut.one_apply]
          have hw : a v₀ * v₀⁻¹ ∈ I₁.comap φ := by
            change φ (a v₀ * v₀⁻¹) ∈ I₁
            rw [hφ, map_mul, map_inv, haa, mul_inv_rev, inv_inv, ← sq, hW]
            exact I₁.one_mem
          rw [h] at hw
          exact hw
        · have hv : v₀ ∈ I₁.comap φ := h ▸ Subgroup.mem_top v₀
          exact hv
      · have hsa : s (a v₀) = a (s v₀) := by
          have h1 := congrArg (fun f : MulAut W => f v₀) (hcomm a ha s (hSH hs))
          simpa [MulAut.mul_apply] using h1.symm
        rw [map_mul, map_inv, hsa, hv₀S s hs]
    have hk1 := le_mQuot_stabAt_of_mem_aSet hA hv₀A
    have hk2 := two_pow_mQuot_stabAt_le hA.2.2.1 hmemI
    have h3 : 2 ^ (k + 1) ≤ 2 ^ k :=
      (Nat.pow_le_pow_right (by norm_num) hk1).trans (hk2.trans hScard)
    have h4 : 2 ^ k < 2 ^ (k + 1) := Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self k)
    omega
  ·
    have h1 := E3.le_aParam_of_mem_aSet (Nat.succ_pos k) (autSub_mem_aSet hA hAI hAU)
    omega

theorem kNatOm4mATwo_holds :
    ∀ (W : Type) [CommGroup W] [Finite W] (H X : Subgroup (MulAut W)) (k : ℕ),
      IsOmegaMinus ↥H 4 k → SumOfNat (fun H U Z => NatOmegaMinus H U Z 4 k) H ⊤ ⊥ 2 → H ≤ X →
        X ≤ normalizer (H : Set (MulAut W)) → E3.aParam X ≤ k := by
  intro W _ _ H X k hΩ hsum _hHX hXN
  obtain ⟨I, -, hind, hsup, hnat⟩ := hsum
  have h01 : I 0 ⊓ I 1 = ⊥ := by
    refine le_bot_iff.mp (le_trans (inf_le_inf_left _ ?_) (hind 0))
    exact le_sup_of_le_right (le_iSup₂_of_le (f := fun j (_ : j ≠ 0) => I j) 1 (by decide)
      le_rfl)
  have htop : I 0 ⊔ I 1 = ⊤ := by
    rw [← hsup, bot_sup_eq]
    refine le_antisymm (sup_le (le_iSup I 0) (le_iSup I 1)) (iSup_le fun i => ?_)
    fin_cases i
    · exact le_sup_left
    · exact le_sup_right
  have hW : ∀ w : W, w ^ 2 = 1 := by
    intro w
    have hw : w ∈ I 0 ⊔ I 1 := htop ▸ Subgroup.mem_top w
    obtain ⟨y, hy, z, hz, rfl⟩ := Subgroup.mem_sup.mp hw
    rw [mul_pow, sq_eq_one_of_natOmegaMinus (hnat 0) y hy,
      sq_eq_one_of_natOmegaMinus (hnat 1) z hz, one_mul]
  have hk : 1 ≤ k := one_le_of_natOmegaMinus_sec (hnat 0)
  apply RonanE42.aParam_le_of_aSet_empty
  intro A hA
  have hAN : A ∈ E3.aSet (k + 1) (normalizer (H : Set (MulAut W))) := E3.aSet_mono hXN hA
  obtain ⟨g, hgH, hg⟩ := exists_conj_le_stabSub hW h01 htop (ne_bot_of_natOmegaMinus (hnat 0))
    (stableUnder_of_natOmegaMinus (hnat 0)) (eq_bot_or_eq_of_natOmegaMinus (hnat 0))
    (ne_bot_of_natOmegaMinus (hnat 1)) (stableUnder_of_natOmegaMinus (hnat 1))
    (eq_bot_or_eq_of_natOmegaMinus (hnat 1)) (by omega) hAN hAN.1
  have hgN : g ∈ normalizer (H : Set (MulAut W)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      rw [hgH h hh, mul_inv_cancel_right]
      exact hh
    · intro hh
      have h1 : g * h * g⁻¹ * g = g * h := by rw [inv_mul_cancel_right]
      have h2 : g⁻¹ * (g * h * g⁻¹) * g = h := by group
      have h3 := hgH _ hh
      rw [← h2, mul_assoc, ← h3, ← mul_assoc, inv_mul_cancel, one_mul]
      exact hh
  have hA' : A.map (MulAut.conj g).toMonoidHom ∈
      E3.aSet (k + 1) (normalizer (H : Set (MulAut W))) := by
    refine E3.aSet_mono ?_ (NatOm4mA.conj_mem_aSet hAN g)
    rintro _ ⟨x, hx, rfl⟩
    exact (normalizer _).mul_mem ((normalizer _).mul_mem hgN hx) ((normalizer _).inv_mem hgN)
  rcases hg with hg | hg
  · exact not_mem_aSet_of_le_stabSub hW h01 htop (stableUnder_of_natOmegaMinus (hnat 0))
      (eq_one_of_natOmegaMinus (hnat 0)) (exists_card_inf_fixV_le_of_natOmegaMinus (hnat 0))
      (aParam_autSub_normalizer_le_of_natOmegaMinus hΩ (hnat 0))
      (ne_bot_of_natOmegaMinus (hnat 1)) (stableUnder_of_natOmegaMinus (hnat 1))
      (eq_bot_or_eq_of_natOmegaMinus (hnat 1)) hA' hg
  · exact not_mem_aSet_of_le_stabSub hW (by rw [inf_comm]; exact h01)
      (by rw [sup_comm]; exact htop) (stableUnder_of_natOmegaMinus (hnat 1))
      (eq_one_of_natOmegaMinus (hnat 1)) (exists_card_inf_fixV_le_of_natOmegaMinus (hnat 1))
      (aParam_autSub_normalizer_le_of_natOmegaMinus hΩ (hnat 1))
      (ne_bot_of_natOmegaMinus (hnat 0)) (stableUnder_of_natOmegaMinus (hnat 0))
      (eq_bot_or_eq_of_natOmegaMinus (hnat 0)) hA' hg

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5
