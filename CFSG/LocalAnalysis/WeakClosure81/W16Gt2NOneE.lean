module

public import CFSG.LocalAnalysis.WeakClosure81.W16Gt2NOneC
public import CFSG.LocalAnalysis.WeakClosure81.W16Gt2NOneB
public import CFSG.LocalAnalysis.WeakClosure81.W16Gt2NOneZ
public import CFSG.LocalAnalysis.WeakClosure81.W16Gt2NOneAbsB
public import CFSG.LocalAnalysis.WeakClosure81.W16Gt2CoprimeAction
public import CFSG.Quasithin.Background.G10Basic

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11
open Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace Cfg1620

variable {M V₀ V U S R H : Subgroup G} {g : G} {B : Subgroup G}

theorem isCyclic_of_inverted (h1 : W16One G) (h5 : W16Five G) (h15 : W16Fifteen G)
    (hS : Std15 G) (c : Cfg1620 M V₀ V U S R H g B)
    (Mo : ModDataE H (conjClosure (U ⊔ V₀) H)) (hn : E3.mQuot V (U ⊔ V₀) = 1)
    {t : LGL 2 Mo.W} (ht : t ∈ Mo.img V) (ht1 : t ≠ 1) {O : Subgroup (LGL 2 Mo.W)}
    (hOH : O ≤ Mo.img H) (hOodd : Odd (Nat.card O)) {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    (hOp : IsPGroup p O) (hab : ∀ a ∈ O, ∀ b ∈ O, a * b = b * a)
    (hinv : ∀ a ∈ O, t * a * t⁻¹ = a⁻¹) : IsCyclic ↥O := by
  by_contra hnc
  refine ht1 (NOne.eq_one_of_noncyclic_inverted hp hOp hab hnc hinv (X := Mo.sp V₀) ?_ ?_)
  · intro w
    obtain ⟨e, heI, rfl⟩ := Mo.ι_surj w
    obtain ⟨v₁, hv₁V, hρv₁⟩ := Mo.mem_img.1 ht
    have hv₁c : (v₁ : G) ∈ conjSubgroup V 1 := by
      rw [conjSubgroup_one]
      exact hv₁V
    have hmem : ⁅(v₁ : G), e⁆ ∈ ⁅conjSubgroup V 1, conjClosure (U ⊔ V₀) H⁆ :=
      Subgroup.commutator_mem_commutator hv₁c heI
    have hcomm : ⁅(v₁ : G), e⁆ ∈ V₀ := by
      have h2 := comm_conj_conjClosure_le h1 hS c (h := 1) H.one_mem hmem
      rwa [conjSubgroup_one] at h2
    have hI : ⁅(v₁ : G), e⁆ ∈ conjClosure (U ⊔ V₀) H := by
      have hnorm := le_normalizer_conjClosure (U ⊔ V₀) H v₁.2
      have hvi : (v₁ : G) * e * (v₁ : G)⁻¹ ∈ conjClosure (U ⊔ V₀) H :=
        (Subgroup.mem_normalizer_iff.1 hnorm e).1 heI
      have heq : ⁅(v₁ : G), e⁆ = ((v₁ : G) * e * (v₁ : G)⁻¹) * e⁻¹ := by
        rw [commutatorElement_def]
      rw [heq]
      exact (conjClosure (U ⊔ V₀) H).mul_mem hvi ((conjClosure (U ⊔ V₀) H).inv_mem heI)
    have hval : t (Mo.ι e) - Mo.ι e = Mo.ι ⁅(v₁ : G), e⁆ := by
      rw [← hρv₁, ← Mo.ι_commutator v₁.2 heI]
    rw [hval]
    exact Mo.mem_sp.2 ⟨⁅(v₁ : G), e⁆, ⟨hcomm, hI⟩, rfl⟩
  · intro a ha ha1 w hw haw
    exact eq_zero_of_apply_eq h1 h5 h15 hS c Mo hn ht ht1 (hOH ha) ha1
      (Odd.of_dvd_nat hOodd (Subgroup.orderOf_dvd_natCard O ha)) (hinv a ha) hw haw

theorem eq_of_invariant_img (h1 : W16One G) (h5 : W16Five G) (h15 : W16Fifteen G)
    (hS : Std15 G) (c : Cfg1620 M V₀ V U S R H g B)
    (Mo : ModDataE H (conjClosure (U ⊔ V₀) H)) (hn : E3.mQuot V (U ⊔ V₀) = 1)
    {t : LGL 2 Mo.W} (ht : t ∈ Mo.img V) (ht1 : t ≠ 1) {O N : Subgroup (LGL 2 Mo.W)}
    (hOH : O ≤ Mo.img H) (hOodd : Odd (Nat.card O)) (hNO : N ≤ O)
    (hNR : ∀ r ∈ Mo.img R, ∀ n ∈ N, r * n * r⁻¹ ∈ N) (hnc : ∃ x ∈ N, t * x ≠ x * t) :
    N = O := by
  refine NOne.eq_of_invariant_of_not_commute (Hh := Mo.img H) (R := Mo.img R)
    (Mo.isPGroup_img c.sylow.isPGroup) ((Mo.img_mono c.V_le_R) ht) ?_ hOH hOodd ?_ hNO hNR hnc
  · simpa [pow_two] using (Mo.isElemAbelian_img c.cex.hyp.h6.elemAbelian).2 t ht
  · intro y hy hy1 hyo hty
    exact img_eq_sup_zpowers h1 h5 h15 hS c Mo hn ht ht1 hy hy1 hyo hty

section Certified


theorem img_conjClosure_eq_img_L (h1 : W16One G) (h5 : W16Five G) (h15 : W16Fifteen G)
    (hS : Std15 G) (c : Cfg1620 M V₀ V U S R H g B)
    (Mo : ModDataE H (conjClosure (U ⊔ V₀) H)) (hn : E3.mQuot V (U ⊔ V₀) = 1)
    (hμ : 2 < mBar M V₀ V c.cex.hyp.h6.elemAbelian) :
    Mo.img (conjClosure V H) = Mo.img (V ⊔ conjSubgroup V g) := by
  have hcardV : Nat.card ↥(Mo.img V) = 2 := card_img_eq_two h1 h5 h15 hS c Mo hn
  haveI : Nontrivial ↥(Mo.img V) := by
    rw [← Finite.one_lt_card_iff_nontrivial]
    omega
  obtain ⟨t₀, ht0⟩ := exists_ne (1 : ↥(Mo.img V))
  let t : LGL 2 Mo.W := t₀
  have ht : t ∈ Mo.img V := t₀.2
  have ht1 : t ≠ 1 := fun h => ht0 (Subtype.ext h)
  obtain ⟨O, hOK, hOodd, hOn, hKO⟩ := exists_odd_normal_img h1 h5 h15 hS c Mo hn hμ ht ht1
  have hOH : O ≤ Mo.img H := hOK.trans (Mo.img_mono (conjClosure_le_H c))
  have hRH : R ≤ H := c.mem.1
  have hRO : ∀ r ∈ Mo.img R, ∀ o ∈ O, r * o * r⁻¹ ∈ O :=
    fun r hr o ho => hOn r ((Mo.img_mono hRH) hr) o ho
  have hmin : ∀ N : Subgroup (LGL 2 Mo.W), N ≤ O →
      (∀ r ∈ Mo.img R, ∀ n ∈ N, r * n * r⁻¹ ∈ N) →
      (∃ x ∈ N, t * x ≠ x * t) → N = O :=
    fun N hNO hNR hnc => eq_of_invariant_img h1 h5 h15 hS c Mo hn ht ht1 hOH hOodd hNO hNR hnc
  have hRt : ∀ r ∈ Mo.img R, r * t = t * r := by
    intro r hr
    have hRM : R ≤ H ⊓ M := le_inf c.mem.1 (c.sylow.le.trans (cTilde_le_M M V₀ V))
    exact img_commute_of_mem_inf h1 h5 h15 hS c Mo hn ((Mo.img_mono hRM) hr) ht
  have ht2 : t * t = 1 := by
    simpa [pow_two] using (Mo.isElemAbelian_img c.cex.hyp.h6.elemAbelian).2 t ht
  obtain ⟨k, hk, hkt, hkL⟩ := exists_mem_img_conjClosure_conj_ne h1 h5 h15 hS c Mo hn ht ht1
  have hnc : ∃ o ∈ O, t * o ≠ o * t := NOne.exists_not_commute_of_ne hKO ⟨k, hk, hkt⟩
  have hR2 : IsPGroup 2 (Mo.img R) := Mo.isPGroup_img c.sylow.isPGroup
  obtain ⟨p, hpprime, hp2, hOp⟩ := NOne.exists_isPGroup_of_minimal hR2 hOodd hRO hmin hnc
  haveI : Fact p.Prime := ⟨hpprime⟩
  have hab : ∀ a ∈ O, ∀ b ∈ O, a * b = b * a :=
    NOne.commute_of_isPGroup (isConjClosure_img h1 h5 h15 hS c Mo hn ht ht1)
      (Mo.img_mono c.mem.1) hOK hOn hOp hmin hnc
      (fun z hz hzc => eq_one_of_comm_img h1 h5 h15 hS c Mo hn hz hzc)
  have hinv : ∀ o ∈ O, t * o * t⁻¹ = o⁻¹ :=
    NOne.inv_eq_of_commute ((Mo.img_mono c.V_le_R) ht) ht2 hRt hOodd hRO hab hmin hnc
  have hcyc : IsCyclic ↥O :=
    isCyclic_of_inverted h1 h5 h15 hS c Mo hn ht ht1 hOH hOodd hp2 hOp hab hinv
  have hKeq : Mo.img (conjClosure V H)
      = Subgroup.zpowers t ⊔ Subgroup.zpowers (k⁻¹ * t * k) :=
    NOne.eq_zpowers_sup_of_isCyclic hKO ht2 hOodd hRO hcyc hinv hmin hk hkt
  have hVH : V ≤ H := c.V_le_R.trans c.mem.1
  have hVgH : conjSubgroup V g ≤ H :=
    (conjSubgroup_le_conjClosure_of_mem c.g_mem.1 le_rfl).trans (conjClosure_le_H c)
  calc Mo.img (conjClosure V H)
      = Subgroup.zpowers t ⊔ Subgroup.zpowers (k⁻¹ * t * k) := hKeq
    _ = Mo.img V ⊔ Mo.img (conjSubgroup V g) := by
        rw [img_eq_zpowers h1 h5 h15 hS c Mo hn ht ht1, hkL]
    _ = Mo.img (V ⊔ conjSubgroup V g) := (Mo.img_sup hVH hVgH).symm

end Certified

end Cfg1620

end CFSG.LocalAnalysis.WeakClosure81
