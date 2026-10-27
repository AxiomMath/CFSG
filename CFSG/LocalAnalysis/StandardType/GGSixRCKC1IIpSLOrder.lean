module

public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.GroupTheory.SpecificGroups.Alternating
import CFSG.HardMathSupport.Solomon.Coordinator.L3C143AltFin

public section

namespace CFSG.StandardType.RCKC1

private theorem rckIIp_odd_two_pow_sub_one {q : ℕ} (hq : 1 ≤ q) : Odd (2 ^ q - 1) := by
  have hpos : 0 < 2 ^ (q - 1) := pow_pos (by norm_num) _
  have hsplit : 2 ^ q = 2 * 2 ^ (q - 1) := by
    have hq' : q = (q - 1) + 1 := by omega
    conv_lhs => rw [hq']
    rw [pow_succ, mul_comm]
  have hnot : ¬ 2 ∣ 2 ^ q - 1 := by
    rw [hsplit]
    exact Nat.two_not_dvd_two_mul_sub_one hpos
  rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
  exact hnot

private theorem rckIIp_odd_finsetProd {ι : Type*} (s : Finset ι) {f : ι → ℕ}
    (h : ∀ i ∈ s, Odd (f i)) : Odd (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact odd_one
  | insert a s ha ih =>
      rw [Finset.prod_insert ha]
      exact (h a (Finset.mem_insert_self a s)).mul
        (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

private theorem rckIIp_two_pow_mul_odd_eq {a b u v : ℕ} (hu : Odd u) (hv : Odd v)
    (heq : 2 ^ a * u = 2 ^ b * v) : a = b := by
  rcases le_total a b with hab | hab
  · have h : u = 2 ^ (b - a) * v := by
      refine Nat.mul_left_cancel (n := 2 ^ a) (pow_pos (by norm_num) a) ?_
      rw [heq, ← mul_assoc, ← pow_add, Nat.add_sub_of_le hab]
    by_contra hne
    have hdvd : 2 ∣ u := by
      rw [h]
      exact dvd_mul_of_dvd_left (dvd_pow_self 2 (by omega)) v
    exact hu.not_two_dvd_nat hdvd
  · have h : v = 2 ^ (a - b) * u := by
      refine Nat.mul_left_cancel (n := 2 ^ b) (pow_pos (by norm_num) b) ?_
      rw [← heq, ← mul_assoc, ← pow_add, Nat.add_sub_of_le hab]
    by_contra hne
    have hdvd : 2 ∣ v := by
      rw [h]
      exact dvd_mul_of_dvd_left (dvd_pow_self 2 (by omega)) u
    exact hv.not_two_dvd_nat hdvd

private theorem rckIIp_center_two_eq_bot (F : Type*) [Field F] [CharP F 2] :
    Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) = ⊥ := by
  rw [← CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars_eq_center 2 F]
  rw [eq_bot_iff]
  intro A hA
  rw [Subgroup.mem_bot]
  obtain ⟨c, hc, hAc⟩ :=
    (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.mem_scalars
      (n := 2) (K := F)).mp hA
  have hc1 : c = 1 := by
    apply Units.ext
    have hcF : ((c : F)) ^ 2 = 1 := by
      have h := congrArg (fun u : Fˣ => (u : F)) hc
      simpa using h
    rcases sq_eq_one_iff.mp hcF with h | h
    · exact h
    · rw [CharTwo.neg_eq] at h
      exact h
  refine Subtype.ext ?_
  rw [hAc, hc1]
  simp

private theorem rckIIp_card_center_three_four :
    Nat.card (Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 2))) = 3 := by
  have hcardF : Nat.card (GaloisField 2 2) = 4 := by
    rw [GaloisField.card (p := 2) (n := 2) (by norm_num)]
    norm_num
  have hcard_units : Nat.card (GaloisField 2 2)ˣ = 3 := by
    rw [Nat.card_units, hcardF]
  have hroots : rootsOfUnity 3 (GaloisField 2 2) = ⊤ := by
    rw [eq_top_iff]
    intro u hu
    rw [mem_rootsOfUnity]
    have h := pow_card_eq_one' (G := (GaloisField 2 2)ˣ) (x := u)
    rwa [hcard_units] at h
  rw [Nat.card_congr (Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity'
    (n := Fin 3) (R := GaloisField 2 2) 0).toEquiv]
  change Nat.card ↥(rootsOfUnity 3 (GaloisField 2 2)) = 3
  rw [hroots, Subgroup.card_top, hcard_units]

private theorem rckIIp_card_range {X : Type} [Group X] {G : Type} [Group G] (π : G →* X)
    (hA8 : Nonempty ((↥π.range ⧸ Subgroup.center ↥π.range) ≃* alternatingGroup (Fin 8))) :
    Nat.card ↥π.range = 20160 * Nat.card (Subgroup.center ↥π.range) := by
  obtain ⟨eA⟩ := hA8
  have hA8card : Nat.card (alternatingGroup (Fin 8)) = 20160 := by
    have h := two_mul_nat_card_alternatingGroup (α := Fin 8)
    rw [Nat.card_perm, Nat.card_fin] at h
    have h8 : (8 : ℕ).factorial = 40320 := by decide
    omega
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup
    (Subgroup.center ↥π.range)
  rw [Nat.card_congr eA.toEquiv, hA8card] at h
  exact h

private theorem rckIIp_order_eq {X : Type} [Group X] {k h : ℕ} (hh : 1 ≤ h)
    (π : Matrix.SpecialLinearGroup (Fin (k + 1)) (GaloisField 2 h) →* X)
    (hker : π.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin (k + 1)) (GaloisField 2 h)))
    (hodd : Odd (Nat.card (Subgroup.center ↥π.range)))
    (hA8 : Nonempty ((↥π.range ⧸ Subgroup.center ↥π.range) ≃* alternatingGroup (Fin 8))) :
    h * ((k + 1) * k / 2) = 6 := by
  classical
  let F := GaloisField 2 h
  let G := Matrix.SpecialLinearGroup (Fin (k + 1)) F
  let J := ↥π.range
  let ZJ := Subgroup.center J
  have hcardF : Nat.card F = 2 ^ h := GaloisField.card (p := 2) (n := h) (by omega)
  have hGker : Nat.card G = Nat.card J * Nat.card π.ker := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup π.ker
    rw [h, Nat.card_congr (QuotientGroup.quotientKerEquivRange π).toEquiv]
  have hcardJ : Nat.card J = 20160 * Nat.card ZJ := rckIIp_card_range π hA8
  have hZGodd : Odd (Nat.card (Subgroup.center G)) := by
    have hdvd := CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_scalars_dvd
      (K := F) (n := k + 1) (by omega)
    rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars_eq_center (k + 1) F] at hdvd
    have hoddF : Odd (Nat.card F - 1) := by
      rw [hcardF]
      exact rckIIp_odd_two_pow_sub_one hh
    exact hoddF.of_dvd_nat hdvd
  have hkerodd : Odd (Nat.card π.ker) := hZGodd.of_dvd_nat (Subgroup.card_dvd_of_le hker)
  have hG6 : Nat.card G = 2 ^ 6 * (315 * Nat.card ZJ * Nat.card π.ker) := by
    rw [hGker, hcardJ]
    ring
  have hoddG : Odd (315 * Nat.card ZJ * Nat.card π.ker) := by
    have h315 : Odd 315 := by norm_num
    exact (h315.mul hodd).mul hkerodd
  have hGpow : Nat.card G = 2 ^ (h * ((k + 1) * k / 2)) *
      ∏ j ∈ Finset.Icc 2 (k + 1), ((2 ^ h) ^ j - 1) := by
    rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (K := F) (n := k + 1)
      (by omega), hcardF,
      show (k + 1) * ((k + 1) - 1) / 2 = (k + 1) * k / 2 from by rw [Nat.add_sub_cancel],
      pow_mul]
  have hprododd : Odd (∏ j ∈ Finset.Icc 2 (k + 1), ((2 ^ h) ^ j - 1)) := by
    refine rckIIp_odd_finsetProd _ ?_
    intro j hj
    rw [Finset.mem_Icc] at hj
    rw [← pow_mul]
    exact rckIIp_odd_two_pow_sub_one (Nat.mul_pos (by omega) (by omega))
  have h6 := rckIIp_two_pow_mul_odd_eq hoddG hprododd (by rw [← hG6, hGpow])
  exact h6.symm

theorem rckIIp_eq_three_one_of_alt_eight {X : Type} [Group X] {k h : ℕ} (hh : 1 ≤ h)
    (π : Matrix.SpecialLinearGroup (Fin (k + 1)) (GaloisField 2 h) →* X)
    (hker : π.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin (k + 1)) (GaloisField 2 h)))
    (hodd : Odd (Nat.card (Subgroup.center ↥π.range)))
    (hA8 : Nonempty ((↥π.range ⧸ Subgroup.center ↥π.range) ≃* alternatingGroup (Fin 8))) :
    k = 3 ∧ h = 1 := by
  classical
  have hval : h * ((k + 1) * k / 2) = 6 := rckIIp_order_eq hh π hker hodd hA8
  have hk3 : k ≤ 3 := by
    by_contra hk
    have hk4 : 4 ≤ k := by omega
    have hMle : (k + 1) * k / 2 ≤ 6 := by
      have h1 : 1 * ((k + 1) * k / 2) ≤ h * ((k + 1) * k / 2) :=
        Nat.mul_le_mul_right _ hh
      omega
    have hmul : (k + 1) * k ≤ 12 := by
      have h2dvd : 2 ∣ (k + 1) * k := by
        rw [mul_comm]
        exact Nat.two_dvd_mul_add_one k
      have h2 : (k + 1) * k = 2 * ((k + 1) * k / 2) := (Nat.mul_div_cancel' h2dvd).symm
      rw [h2]
      omega
    have h20 : 20 ≤ (k + 1) * k := by
      calc 20 = 5 * 4 := by norm_num
        _ ≤ (k + 1) * k := Nat.mul_le_mul (by omega) hk4
    omega
  have hk_cases : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
  obtain rfl | rfl | rfl | rfl := hk_cases
  · omega
  ·
    have hh6 : h = 6 := by omega
    subst h
    let F := GaloisField 2 6
    let G := Matrix.SpecialLinearGroup (Fin 2) F
    let J := ↥π.range
    let ZJ := Subgroup.center J
    have : Finite J := Finite.of_surjective π.rangeRestrict π.rangeRestrict_surjective
    have hcenter : Subgroup.center G = ⊥ := rckIIp_center_two_eq_bot F
    have hkerbot : π.ker = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      have hx' : x ∈ Subgroup.center G := hker hx
      rwa [hcenter] at hx'
    have hinj : Function.Injective π := (MonoidHom.ker_eq_bot_iff π).mp hkerbot
    have hbij : Function.Bijective π.rangeRestrict := by
      refine ⟨fun x y hxy => hinj (congrArg Subtype.val hxy), ?_⟩
      rintro ⟨y, hy⟩
      obtain ⟨x, rfl⟩ := hy
      exact ⟨x, rfl⟩
    let e : G ≃* J := MulEquiv.ofBijective π.rangeRestrict hbij
    have hZJbot : ZJ = ⊥ := by
      have hmap := Subgroup.map_center_eq e
      rw [hcenter, Subgroup.map_bot] at hmap
      exact hmap.symm
    have hcardZJ : Nat.card ZJ = 1 := by
      rw [hZJbot, Subgroup.card_bot]
    have hGJ : Nat.card G = Nat.card J := Nat.card_congr e.toEquiv
    have hcardJ : Nat.card J = 20160 * Nat.card ZJ := rckIIp_card_range π hA8
    have hcardG : Nat.card G = 262080 := by
      rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (K := F) (n := 2)
        (by norm_num), GaloisField.card (p := 2) (n := 6) (by norm_num)]
      norm_num
    have hJ20160 : Nat.card J = 20160 := by
      rw [hcardJ, hcardZJ, mul_one]
    omega
  ·
    have hh2 : h = 2 := by omega
    subst h
    let F := GaloisField 2 2
    let G := Matrix.SpecialLinearGroup (Fin 3) F
    let J := ↥π.range
    let ZJ := Subgroup.center J
    have : Finite J := Finite.of_surjective π.rangeRestrict π.rangeRestrict_surjective
    have : Nonempty ZJ := ⟨1⟩
    have hcardF4 : Nat.card F = 4 := by
      rw [GaloisField.card (p := 2) (n := 2) (by norm_num)]
      norm_num
    have hZJpos : 0 < Nat.card ZJ := Nat.card_pos
    have hcardJ : Nat.card J = 20160 * Nat.card ZJ := rckIIp_card_range π hA8
    have hcardquotJ : Nat.card (J ⧸ ZJ) = 20160 := by
      have h := Subgroup.card_eq_card_quotient_mul_card_subgroup ZJ
      rw [hcardJ] at h
      exact (Nat.eq_of_mul_eq_mul_right hZJpos h).symm
    have hcardSL3 : Nat.card (Matrix.SpecialLinearGroup (Fin 3) F) = 60480 := by
      rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (K := F) (n := 3)
        (by norm_num), hcardF4]
      decide +kernel
    have hcardZ : Nat.card (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars 3 F) = 3 := by
      rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars_eq_center 3 F]
      exact rckIIp_card_center_three_four
    have hcardPSL : Nat.card (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 F) =
        20160 := by
      rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_projectiveSL (n := 3) (K := F),
        hcardSL3, hcardZ]
    let f : G →* (J ⧸ ZJ) := (QuotientGroup.mk' ZJ).comp π.rangeRestrict
    have hf_surj : Function.Surjective f := by
      intro y
      obtain ⟨y', rfl⟩ := QuotientGroup.mk'_surjective ZJ y
      obtain ⟨x, hx⟩ := y'.2
      refine ⟨x, ?_⟩
      change QuotientGroup.mk' ZJ (π.rangeRestrict x) = QuotientGroup.mk' ZJ y'
      rw [show π.rangeRestrict x = y' from Subtype.ext hx]
    have hZG_le : Subgroup.center G ≤ f.ker := by
      intro z hz
      rw [MonoidHom.mem_ker]
      change QuotientGroup.mk' ZJ (π.rangeRestrict z) = 1
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_center_iff]
      intro y
      obtain ⟨g, hg⟩ := y.2
      rw [show y = π.rangeRestrict g from Subtype.ext hg.symm]
      apply Subtype.ext
      change π g * π z = π z * π g
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz g]
    have hle : CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars 3 F ≤ f.ker := by
      rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars_eq_center 3 F]
      exact hZG_le
    let fbar : (G ⧸ CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars 3 F) →* (J ⧸ ZJ) :=
      QuotientGroup.lift (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars 3 F) f hle
    have hfbar_surj : Function.Surjective fbar :=
      QuotientGroup.lift_surjective_of_surjective
        (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars 3 F) f hf_surj hle
    have hbij : Function.Bijective fbar :=
      hfbar_surj.bijective_of_nat_card_le (by rw [hcardPSL, hcardquotJ])
    obtain ⟨ebar⟩ : Nonempty
        ((G ⧸ CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars 3 F) ≃* (J ⧸ ZJ)) :=
      ⟨MulEquiv.ofBijective fbar hbij⟩
    obtain ⟨eA⟩ := hA8
    exfalso
    exact CFSG.HardMathSupport.Solomon.Coordinator.false_of_projectiveSL_alt_eight
      (F := F) hcardF4 (ebar.trans eA)
  ·
    have hh1 : h = 1 := by omega
    exact ⟨rfl, hh1⟩

end CFSG.StandardType.RCKC1
