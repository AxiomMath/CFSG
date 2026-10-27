module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154CritExcZ3S3
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154CritExcZ3Burn

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup

theorem s16h_not_three_dvd_of_torus {W : Type} [CommGroup W] [Finite W]
    (hcard : Nat.card W = 64) {l : MulAut W} (hl : orderOf l = 3)
    (hfpf : ∀ w : W, l w = w → w = 1) {D J : Subgroup (MulAut W)} (hD : IsElemAbelian 3 D)
    (hD27 : 27 ≤ Nat.card ↥D) (hJl : J ≤ centralizer ({l} : Set (MulAut W)))
    (hDJ : D ≤ normalizer (J : Set (MulAut W)))
    (hJgen : ∃ X : Set (MulAut W), (∀ g ∈ X, g ^ 2 = 1) ∧ J = closure X)
    (hJ3 : ∀ y ∈ J, y ^ 3 = 1 → y ∈ zpowers l) : ¬ 3 ∣ Nat.card ↥J := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set K : Subgroup (MulAut W) := J ⊔ D with hKdef
  have hDK : D ≤ K := by rw [hKdef]; exact le_sup_right
  have hJK : J ≤ K := by rw [hKdef]; exact le_sup_left
  have hDp : IsPGroup 3 D := fun x => ⟨1, by
    rw [pow_one]
    exact Subtype.ext (by simpa using hD.2 x.1 x.2)⟩
  obtain ⟨P, hPK, hDP⟩ := exists_isSylowIn_ge (G := MulAut W) 3 hDK hDp
  have hKJ : K ≤ normalizer (J : Set (MulAut W)) := by
    rw [hKdef]
    exact sup_le J.le_normalizer hDJ
  have hJnorm : (J.subgroupOf K).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hJK).mpr hKJ
  have hS : IsSylowIn 3 (P ⊓ J) J := hPK.inf_normal hJK hJnorm
  have hDS : D ≤ normalizer ((P ⊓ J : Subgroup (MulAut W)) : Set (MulAut W)) := by
    rw [Subgroup.le_normalizer_iff]
    intro d hd s hs
    rw [Subgroup.mem_inf] at hs ⊢
    obtain ⟨hsP, hsJ⟩ := hs
    exact ⟨P.mul_mem (P.mul_mem (hDP hd) hsP) (P.inv_mem (hDP hd)),
      (Subgroup.mem_set_normalizer_iff.mp (hDJ hd) s).mp hsJ⟩
  have hSle : (P ⊓ J : Subgroup (MulAut W)) ≤ zpowers l :=
    s16h_le_zpowers_of_torus hcard hl hfpf
      (hPK.isPGroup.to_le (inf_le_left : (P ⊓ J : Subgroup (MulAut W)) ≤ P))
      (fun y hy hy3 => hJ3 y (hS.le hy) hy3) hD hD27 hDS
  have hcen : ∀ s ∈ (P ⊓ J : Subgroup (MulAut W)), ∀ j ∈ J, s * j = j * s := by
    intro s hs j hj
    have hsl : s ∈ zpowers l := hSle hs
    have hlj : l ∈ centralizer ({j} : Set (MulAut W)) :=
      Subgroup.mem_centralizer_singleton_iff.mpr
        ((Subgroup.mem_centralizer_iff.mp (hJl hj)) l (Set.mem_singleton l))
    exact Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.zpowers_le.mpr hlj hsl)
  exact s16h_not_dvd_of_central_sylow (H := MulAut W) Nat.prime_three (by norm_num)
    hS hcen hJgen

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
