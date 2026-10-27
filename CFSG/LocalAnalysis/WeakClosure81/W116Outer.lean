module

public import CFSG.LocalAnalysis.WeakClosure81.W115Gen
public import CFSG.Quasithin.Background.HM22Out
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4RowFstarLift
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKU43RedA
public import CFSG.RankThree.PartOne.S11d.OutAbstract

public section

namespace CFSG.LocalAnalysis.WeakClosure81.W115

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

theorem w116_outer_ge
    {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w ^ 2 = 1) {Y L : Subgroup (MulAut W)}
    (hLY : L ≤ Y) (hnorm : (L.subgroupOf Y).Normal) (hF : Fstar Y = L)
    (hq : IsQuasisimple ↥L) (hZ : Nat.card (Subgroup.center ↥L) = 3)
    (hSp : IsSpor (↥L ⧸ Subgroup.center ↥L) .M22) (hirr : IsIrrOn L ⊤ ⊥)
    {s : MulAut W} (hsY : s ∈ Y) (hsL : s ∉ L) (hs2 : orderOf s = 2) :
    4 ≤ rkIdx (fixV (Subgroup.zpowers s)) := by
  have hsN : s ∈ Subgroup.normalizer (L : Set (MulAut W)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro l
    constructor
    · intro hl
      have h := hnorm.conj_mem (⟨l, hLY hl⟩ : ↥Y) (Subgroup.mem_subgroupOf.mpr hl)
        (⟨s, hsY⟩ : ↥Y)
      simpa using Subgroup.mem_subgroupOf.mp h
    · intro hl
      have h := hnorm.conj_mem (⟨s * l * s⁻¹, hLY hl⟩ : ↥Y) (Subgroup.mem_subgroupOf.mpr hl)
        (⟨s⁻¹, Y.inv_mem hsY⟩ : ↥Y)
      have h' : s⁻¹ * (s * l * s⁻¹) * s ∈ L := by
        simpa using Subgroup.mem_subgroupOf.mp h
      rwa [show s⁻¹ * (s * l * s⁻¹) * s = l from by group] at h'
  let α : MulAut ↥L := L.normalizerMonoidHom ⟨s, hsN⟩
  have hZnt : Nontrivial ↥(Subgroup.center ↥L) := by
    rw [← Finite.one_lt_card_iff_nontrivial, hZ]
    norm_num
  obtain ⟨z0, hz0ne⟩ := exists_ne (1 : ↥(Subgroup.center ↥L))
  let z : MulAut W := ((z0 : ↥L) : MulAut W)
  have hzL : z ∈ L := (z0 : ↥L).2
  have hz1 : z ≠ 1 := by
    intro h
    apply hz0ne
    apply Subtype.ext
    apply Subtype.ext
    simpa [z] using h
  have hzc : ∀ h ∈ L, h * z = z * h := by
    intro h hh
    have hmem := Subgroup.mem_center_iff.mp (z0.2) (⟨h, hh⟩ : ↥L)
    simpa [z] using congrArg (fun a : ↥L => (a : MulAut W)) hmem
  have hz3 : z ^ 3 = 1 := by
    have h := (pow_card_eq_one' : z0 ^ Nat.card ↥(Subgroup.center ↥L) = 1)
    rw [hZ] at h
    simpa [z] using congrArg (fun a : ↥(Subgroup.center ↥L) => ((a : ↥L) : MulAut W)) h
  have hfpf : ∀ w : W, z w = w → w = 1 := fun w hw =>
    s16ku43_center_fixes_only_one hirr hzL hzc hz1 hw
  have hqOpen : CFSG.Open.IsQuasisimple ↥L := ⟨hq.1.commutator_eq_top, hq.2.1⟩
  have hαouter : ∀ k : ↥L, α ≠ MulAut.conj k := by
    intro k hk
    apply hsL
    have hxY : (k : MulAut W)⁻¹ * s ∈ Y := Y.mul_mem (Y.inv_mem (hLY k.2)) hsY
    have hxcent : (k : MulAut W)⁻¹ * s ∈
        Subgroup.centralizer (L : Set (MulAut W)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro l hl
      have h1 : α ⟨l, hl⟩ = MulAut.conj k ⟨l, hl⟩ := by rw [hk]
      have h2 : ((α ⟨l, hl⟩ : ↥L) : MulAut W) =
          ((MulAut.conj k ⟨l, hl⟩ : ↥L) : MulAut W) := congrArg Subtype.val h1
      dsimp only [α] at h2
      rw [Subgroup.normalizerMonoidHom_apply_apply_coe] at h2
      have h2' : s * l * s⁻¹ = (k : MulAut W) * l * (k : MulAut W)⁻¹ := by
        simpa [MulAut.conj_apply] using h2
      calc l * ((k : MulAut W)⁻¹ * s)
          = (k : MulAut W)⁻¹ * ((k : MulAut W) * l * (k : MulAut W)⁻¹) * s := by group
        _ = (k : MulAut W)⁻¹ * (s * l * s⁻¹) * s := by rw [← h2']
        _ = ((k : MulAut W)⁻¹ * s) * l := by group
    have hxL : (k : MulAut W)⁻¹ * s ∈ L :=
      CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Row.mem_of_mem_centralizer_of_fstar_eq
        hLY hF hxY hxcent
    have hs_eq : s = k * ((k : MulAut W)⁻¹ * s) := by group
    rw [hs_eq]
    exact L.mul_mem k.2 hxL
  have hαinv : α ⟨z, hzL⟩ = (⟨z, hzL⟩ : ↥L)⁻¹ :=
    CFSG.Quasithin.H.Mathieu.M22Link.kg82HatM22Out_holds
      (↥L) hqOpen hZ hSp α hαouter ⟨z, hzL⟩ (by simpa [z] using z0.2)
  have hsz : s * z * s⁻¹ = z⁻¹ := by
    have h := congrArg (fun a : ↥L => (a : MulAut W)) hαinv
    dsimp only [α] at h
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe] at h
    simpa [z] using h
  have hle := w115_rk_le_two_mul_rkIdx_of_inv hW hz3 hfpf hsz
  have h10 := w116_ten_le_rk hW hZ hSp
  omega

end CFSG.LocalAnalysis.WeakClosure81.W115
