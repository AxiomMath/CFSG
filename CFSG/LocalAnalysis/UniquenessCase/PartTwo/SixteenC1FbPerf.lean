module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1KitDefs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1FbPerfA

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

private lemma s16c1_eq_one_or_eq_of_card_two {W : Type*} [Group W] {R : Subgroup W}
    (hR : Nat.card R = 2) : ∃ c : W, c ≠ 1 ∧ ∀ y ∈ R, y = 1 ∨ y = c := by
  obtain ⟨y, hyne, hyuniq⟩ := (Nat.card_eq_two_iff' (1 : ↥R)).mp hR
  refine ⟨(y : W), ?_, ?_⟩
  · intro h
    exact hyne (Subtype.ext h)
  · intro w hw
    by_cases hw1 : w = 1
    · exact Or.inl hw1
    · right
      have hw' : (⟨w, hw⟩ : ↥R) ≠ 1 := by
        intro h
        exact hw1 (congrArg Subtype.val h)
      exact congrArg Subtype.val (hyuniq ⟨w, hw⟩ hw')

section Module

variable {W : Type} [CommGroup W]

theorem s16c1_transvection_of_central {H : Subgroup (MulAut W)} [Finite W] (hirr : OmegaIrr H)
    (hW : Nat.card W = 64) (hexp : ∀ w : W, w * w = 1) {z : W} (hz : z ≠ 1)
    (hP : Nat.card (ptCent H z) = 960) {n : MulAut W} (hn : n ≠ 1) (hn2 : n * n = 1)
    (hcomm : ∀ p ∈ ptCent H z, p * n = n * p) :
    ∃ c : W, c ≠ 1 ∧ ∀ w : W, n w = w ∨ n w = w * c := by
  let f : W →* W := MonoidHom.mk' (fun w => w * (n w)⁻¹) (by
    intro a b
    rw [map_mul, mul_inv_rev]
    ac_rfl)
  have hf : ∀ w : W, f w = w * (n w)⁻¹ := fun _ => rfl
  have hnnu : ∀ w : W, n (n w) = w := by
    intro w
    have h := congrArg (fun m : MulAut W => m w) hn2
    simpa [MulAut.mul_apply, MulAut.one_apply] using h
  have hKstab : StableUnder (ptCent H z) f.ker := by
    intro x hx u hu
    rw [MonoidHom.mem_ker] at hu ⊢
    rw [hf] at hu ⊢
    have hxu : x (n u) = n (x u) := by
      have h := congrArg (fun m : MulAut W => m u) (hcomm x hx)
      simpa [MulAut.mul_apply] using h
    have hu' : u = n u := mul_inv_eq_one.mp hu
    have hnxu : n (x u) = x u := by rw [← hxu, ← hu']
    rw [hnxu, mul_inv_cancel]
  have hRstab : StableUnder (ptCent H z) f.range := by
    intro x hx y hy
    rw [MonoidHom.mem_range] at hy ⊢
    obtain ⟨u, rfl⟩ := hy
    refine ⟨x u, ?_⟩
    simp only [hf]
    have hxu : x (n u) = n (x u) := by
      have h := congrArg (fun m : MulAut W => m u) (hcomm x hx)
      simpa [MulAut.mul_apply] using h
    rw [map_mul, map_inv, hxu]
  have hKmem := hirr z hz hP f.ker hKstab
  have hRmem := hirr z hz hP f.range hRstab
  have hcard : Nat.card f.ker * Nat.card f.range = 64 := by
    rw [Subgroup.card_ker_mul_card_range, hW]
  have hRle : f.range ≤ f.ker := by
    intro y hy
    rw [MonoidHom.mem_range] at hy
    obtain ⟨u, rfl⟩ := hy
    rw [MonoidHom.mem_ker]
    change (f u) * (n (f u))⁻¹ = 1
    have hnf : n (f u) = f u := by
      change n (u * (n u)⁻¹) = u * (n u)⁻¹
      rw [map_mul, map_inv, hnnu]
      rw [show u⁻¹ = u from mul_eq_one_iff_inv_eq.mp (hexp u),
        show (n u)⁻¹ = n u from mul_eq_one_iff_inv_eq.mp (hexp (n u)), mul_comm]
    rw [hnf, mul_inv_cancel]
  have hle : Nat.card f.range ≤ Nat.card f.ker :=
    Subgroup.card_le_of_le (H := f.range) (K := f.ker) hRle
  have hKne : Nat.card f.ker ≠ 64 := by
    intro hcard64
    have htop : f.ker = ⊤ :=
      Subgroup.eq_top_of_card_eq (H := f.ker) (by rw [hcard64, hW])
    apply hn
    apply MulEquiv.ext
    intro w
    have hw : f w = 1 := by
      rw [← MonoidHom.mem_ker, htop]
      trivial
    have hwn : n w = w := (mul_inv_eq_one.mp (by simpa [hf] using hw)).symm
    simpa using hwn
  have hK32 : Nat.card f.ker = 32 := by
    rcases hKmem with h | h | h | h <;> rcases hRmem with h' | h' | h' | h' <;>
      simp only [h, h'] at hcard hle hKne ⊢ <;> omega
  have hR2 : Nat.card f.range = 2 := by
    rcases hKmem with h | h | h | h <;> rcases hRmem with h' | h' | h' | h' <;>
      simp only [h, h'] at hcard hle hKne ⊢ <;> omega
  obtain ⟨c, hc1, hc⟩ := s16c1_eq_one_or_eq_of_card_two hR2
  refine ⟨c, hc1, ?_⟩
  intro w
  have hw : f w ∈ f.range := MonoidHom.mem_range.mpr ⟨w, rfl⟩
  rcases hc (f w) hw with h | h
  · left
    exact (mul_inv_eq_one.mp (by simpa [hf] using h)).symm
  · right
    have hnu : (n w)⁻¹ = n w := mul_eq_one_iff_inv_eq.mp (hexp (n w))
    have hh : w * n w = c := by
      rw [← hnu]
      simpa [hf] using h
    calc n w = (w * w) * n w := by rw [hexp w, one_mul]
      _ = w * (w * n w) := by rw [mul_assoc]
      _ = w * c := by rw [hh]

theorem s16c1_perfect_of_kit {H : Subgroup (MulAut W)} [Finite W] (hirr : OmegaIrr H)
    (hnt : OmegaNoTrans H) (hW : Nat.card W = 64) (hexp : ∀ w : W, w * w = 1) {z : W}
    (hz : z ≠ 1) (hP : IsE16A5 ↥(ptCent H z)) :
    ⁅ptCent H z, ptCent H z⁆ = ptCent H z := by
  by_contra hperf
  have hXcard : Nat.card ↥(ptCent H z) = 960 := s16c1_card_of_isE16A5 hP
  haveI hXfin : Finite ↥(ptCent H z) :=
    Nat.finite_of_card_ne_zero (by rw [hXcard]; norm_num)
  have hnp : commutator ↥(ptCent H z) ≠ ⊤ := by
    intro hc
    exact hperf ((Subgroup.isPerfect_iff (H := ptCent H z)).mp
      (Group.isPerfect_def.mpr hc))
  obtain ⟨N, hNnorm, hN, hA⟩ := hP
  haveI := hNnorm
  have hcent : N ≤ Subgroup.center ↥(ptCent H z) :=
    s16c1_central_of_not_perfect N hN hA hnp
  obtain ⟨e⟩ := hN
  have hNcard : Nat.card ↥N = 16 := by
    rw [Nat.card_congr e.toEquiv,
      Nat.card_congr (Multiplicative.toAdd : Multiplicative (Fin 4 → ZMod 2) ≃ (Fin 4 → ZMod 2)),
      Nat.card_fun, Nat.card_fin, Nat.card_zmod]
    norm_num
  haveI hNfin : Finite ↥N := Nat.finite_of_card_ne_zero (by rw [hNcard]; norm_num)
  have hNne : N ≠ ⊥ :=
    (Subgroup.one_lt_card_iff_ne_bot (H := N)).mp (by rw [hNcard]; norm_num)
  obtain ⟨n', hn'⟩ := (Subgroup.ne_bot_iff_exists_ne_one (H := N)).mp hNne
  let n : MulAut W := ((n' : ↥(ptCent H z)) : MulAut W)
  have hn : n ≠ 1 := by
    intro h
    exact hn' (Subtype.ext (Subtype.ext h))
  have hnH : n ∈ H := (Subgroup.mem_inf.mp (n' : ↥(ptCent H z)).2).1
  have hsq : ∀ m : Multiplicative (Fin 4 → ZMod 2), m * m = 1 := by
    intro m
    apply Multiplicative.ext
    change Multiplicative.toAdd m + Multiplicative.toAdd m = 0
    ext i
    exact CharTwo.add_self_eq_zero _
  have hn2' : n' * n' = 1 := by
    apply e.injective
    rw [map_mul, map_one, hsq]
  have hn2 : n * n = 1 := by
    have h := congrArg (fun g : ↥N => ((g : ↥(ptCent H z)) : MulAut W)) hn2'
    simpa [n] using h
  have hcomm : ∀ p ∈ ptCent H z, p * n = n * p := by
    intro p hp
    have hc := Subgroup.mem_center_iff.mp (hcent n'.2) (⟨p, hp⟩ : ↥(ptCent H z))
    simpa [n] using congrArg Subtype.val hc
  obtain ⟨c, hc1, htrans⟩ :=
    s16c1_transvection_of_central hirr hW hexp hz hXcard hn hn2 hcomm
  exact hn (hnt n hnH c hc1 htrans)

end Module

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
