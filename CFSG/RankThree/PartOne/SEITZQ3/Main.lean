module

public import CFSG.RankThree.PartOne.SEITZQ3.Plane
public import CFSG.RankThree.PartOne.SEITZQ3.Norm
public import CFSG.RankThree.PartOne.SEITZQ3.SUConj
public import CFSG.RankThree.PartOne.SEITZQ1.AmbientPlane
public import CFSG.RankThree.PartTwo.Sec21.ReeF4Cent2Proof
public import CFSG.RankThree.PartTwo.Sec8.Item8KFacts3ProofReeConj

public noncomputable section

namespace CFSG.RankThree.PartOne.SEITZQ3

open Matrix CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.RankThree.PartOne.KLR CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne.SEITZQ1
open scoped MatrixGroups

section Generic

open CFSG.RankThree.PartOne.SEITZ3

variable {S Γ : Type*} [Group S] [Group Γ]

private theorem cj_cj_mul (E : Subgroup Γ) (g h : Γ) : cj (cj E g) h = cj E (h * g) := by
  ext x
  simp only [mem_cj, _root_.mul_inv_rev, mul_assoc]

private theorem map_cj (φ : S →* Γ) (E : Subgroup S) (g : S) :
    (cj E g).map φ = cj (E.map φ) (φ g) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [mem_cj]
    exact ⟨g⁻¹ * y * g, mem_cj.1 hy, by simp [mul_assoc]⟩
  · intro hx
    obtain ⟨e, he, hex⟩ := mem_cj.1 hx
    refine ⟨g * e * g⁻¹, mem_cj.2 ?_, ?_⟩
    · have : g⁻¹ * (g * e * g⁻¹) * g = e := by group
      rw [this]
      exact he
    · have : x = φ g * φ e * (φ g)⁻¹ := by rw [hex]; group
      rw [this]
      simp

private theorem comm_of_mem_cj {E : Subgroup Γ} {g : Γ}
    (h : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) :
    ∀ x ∈ cj E g, ∀ y ∈ cj E g, x * y = y * x := by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
  rw [← map_mul, ← map_mul, h a ha b hb]

private theorem exists_cj_eq_map_of_plane [Finite Γ]
    (Ψ : S →* Γ) (hΨ : Function.Injective Ψ) (y₀ : Γ) (hy₀ : orderOf y₀ = 3)
    (hcent : Subgroup.centralizer ({y₀} : Set Γ) = Ψ.range)
    (hconj : ∀ y y' : Γ, orderOf y = 3 → orderOf y' = 3 → ∃ g : Γ, g * y * g⁻¹ = y')
    (hbound : ∀ W : Subgroup Γ, (∀ x ∈ W, ∀ y ∈ W, x * y = y * x) → (∀ x ∈ W, x ^ 3 = 1) →
      Nat.card W ≤ 9)
    (Dg : S → Prop) (hDg1 : Dg 1) (hDgmul : ∀ x y, Dg x → Dg y → Dg (x * y))
    (hDgcomm : ∀ x y, Dg x → Dg y → x * y = y * x)
    (hdiag : ∀ F₀ : Subgroup S, (∀ x ∈ F₀, ∀ y ∈ F₀, x * y = y * x) → (∀ x ∈ F₀, x ^ 3 = 1) →
      ∃ P : S, ∀ x ∈ F₀, Dg (P⁻¹ * x * P))
    (E : Subgroup S) (hEDg : ∀ x ∈ E, Dg x) (hEexp : ∀ x ∈ E, x ^ 3 = 1)
    (hEcard : Nat.card E = 3 ^ 2)
    (F : Subgroup Γ) (hFp : ∀ x ∈ F, x ^ 3 = 1) (hFc : Nat.card F = 3 ^ 2) :
    ∃ c : Γ, cj F c = E.map Ψ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hFcomm : ∀ x ∈ F, ∀ y ∈ F, x * y = y * x := by
    have hF := IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) (G := F) hFc
    intro x hx y hy
    exact congrArg Subtype.val (hF.is_comm.comm (⟨x, hx⟩ : F) ⟨y, hy⟩)
  obtain ⟨y, hyF, hy1⟩ : ∃ y ∈ F, y ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hbot : F = ⊥ := (Subgroup.eq_bot_iff_forall F).2 hcon
    rw [hbot, Subgroup.card_bot] at hFc
    norm_num at hFc
  have hyord : orderOf y = 3 := orderOf_eq_prime (hFp y hyF) hy1
  obtain ⟨g, hg⟩ := hconj y y₀ hyord hy₀
  have hy₀F₁ : y₀ ∈ cj F g := by
    rw [mem_cj]
    have : g⁻¹ * y₀ * g = y := by rw [← hg]; group
    rw [this]
    exact hyF
  have hF₁comm : ∀ x ∈ cj F g, ∀ z ∈ cj F g, x * z = z * x := comm_of_mem_cj hFcomm
  have hF₁le : cj F g ≤ Ψ.range := by
    intro x hx
    rw [← hcent, Subgroup.mem_centralizer_singleton_iff]
    exact hF₁comm x hx y₀ hy₀F₁
  have hF₀map : ((cj F g).comap Ψ).map Ψ = cj F g := Subgroup.map_comap_eq_self hF₁le
  have hF₀comm : ∀ x ∈ (cj F g).comap Ψ, ∀ z ∈ (cj F g).comap Ψ, x * z = z * x := by
    intro x hx z hz
    apply hΨ
    rw [map_mul, map_mul]
    exact hF₁comm _ hx _ hz
  have hF₀exp : ∀ x ∈ (cj F g).comap Ψ, x ^ 3 = 1 := by
    intro x hx
    apply hΨ
    rw [map_pow, map_one]
    exact pow_eq_one_of_mem_cj hFp (Subgroup.mem_comap.1 hx)
  obtain ⟨P, hP⟩ := hdiag _ hF₀comm hF₀exp
  let W : Subgroup S :=
    { carrier := {x | Dg x ∧ x ^ 3 = 1}
      mul_mem' := by
        rintro a b ⟨ha, ha1⟩ ⟨hb, hb1⟩
        refine ⟨hDgmul a b ha hb, ?_⟩
        rw [(show Commute a b from hDgcomm a b ha hb).mul_pow, ha1, hb1, one_mul]
      one_mem' := ⟨hDg1, one_pow 3⟩
      inv_mem' := by
        rintro a ⟨ha, ha1⟩
        refine ⟨?_, by rw [inv_pow, ha1, inv_one]⟩
        have h3 : a * (a * a) = 1 := by rw [← pow_three]; exact ha1
        rw [← eq_inv_of_mul_eq_one_right h3]
        exact hDgmul a a ha ha }
  have hWΓcomm : ∀ x ∈ W.map Ψ, ∀ y ∈ W.map Ψ, x * y = y * x := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, hDgcomm a b ha.1 hb.1]
  have hWΓexp : ∀ x ∈ W.map Ψ, x ^ 3 = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    rw [← map_pow, ha.2, map_one]
  have hWΓcard : Nat.card (W.map Ψ) ≤ 9 := hbound _ hWΓcomm hWΓexp
  have hEW : E ≤ W := fun x hx => ⟨hEDg x hx, hEexp x hx⟩
  have hEcardΓ : Nat.card (E.map Ψ) = 9 := by
    rw [Subgroup.card_map_of_injective hΨ, hEcard]
    norm_num
  have hEmap : E.map Ψ = W.map Ψ :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.map_mono hEW) (by rw [hEcardΓ]; exact hWΓcard)
  have hF₂W : cj ((cj F g).comap Ψ) P⁻¹ ≤ W := by
    intro x hx
    refine ⟨?_, pow_eq_one_of_mem_cj hF₀exp hx⟩
    have hx' := mem_cj.1 hx
    rw [inv_inv] at hx'
    have h1 := hP _ hx'
    have e : P⁻¹ * (P * x * P⁻¹) * P = x := by group
    rwa [e] at h1
  have hF₂card : Nat.card ((cj ((cj F g).comap Ψ) P⁻¹).map Ψ) = 9 := by
    rw [map_cj, hF₀map, card_cj, card_cj, hFc]
    norm_num
  have hF₂map : (cj ((cj F g).comap Ψ) P⁻¹).map Ψ = W.map Ψ :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.map_mono hF₂W) (by rw [hF₂card]; exact hWΓcard)
  refine ⟨Ψ P⁻¹ * g, ?_⟩
  rw [hEmap, ← hF₂map, map_cj, hF₀map, cj_cj_mul]

end Generic

section Diag

variable {f : ℕ} {K' : Type} [Field K']

private theorem sudiag_one : ∀ i j : Fin 3, i ≠ j →
    (((1 : unitarySU 2 f K' 3) : GL (Fin 3) K') : Matrix (Fin 3) (Fin 3) K') i j = 0 := by
  intro i j hij
  simp [Matrix.one_apply_ne hij]

private theorem sudiag_mul {x y : unitarySU 2 f K' 3}
    (hx : ∀ i j : Fin 3, i ≠ j → ((x : GL (Fin 3) K') : Matrix (Fin 3) (Fin 3) K') i j = 0)
    (hy : ∀ i j : Fin 3, i ≠ j → ((y : GL (Fin 3) K') : Matrix (Fin 3) (Fin 3) K') i j = 0) :
    ∀ i j : Fin 3, i ≠ j →
      (((x * y : unitarySU 2 f K' 3) : GL (Fin 3) K') : Matrix (Fin 3) (Fin 3) K') i j = 0 := by
  intro i j hij
  rw [Subgroup.coe_mul, Units.val_mul, Matrix.mul_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases hk : i = k
  · subst hk
    rw [hy i j hij, mul_zero]
  · rw [hx i k hk, zero_mul]

private theorem sudiag_comm {x y : unitarySU 2 f K' 3}
    (hx : ∀ i j : Fin 3, i ≠ j → ((x : GL (Fin 3) K') : Matrix (Fin 3) (Fin 3) K') i j = 0)
    (hy : ∀ i j : Fin 3, i ≠ j → ((y : GL (Fin 3) K') : Matrix (Fin 3) (Fin 3) K') i j = 0) :
    x * y = y * x := by
  apply Subtype.ext
  apply Units.ext
  have hA : ((x : GL (Fin 3) K') : Matrix (Fin 3) (Fin 3) K').IsDiag := fun i j hij => hx i j hij
  have hB : ((y : GL (Fin 3) K') : Matrix (Fin 3) (Fin 3) K').IsDiag := fun i j hij => hy i j hij
  show ((x : GL (Fin 3) K') : Matrix (Fin 3) (Fin 3) K') * ((y : GL (Fin 3) K') :
      Matrix (Fin 3) (Fin 3) K') = ((y : GL (Fin 3) K') : Matrix (Fin 3) (Fin 3) K') *
        ((x : GL (Fin 3) K') : Matrix (Fin 3) (Fin 3) K')
  rw [← hA.diagonal_diag, ← hB.diagonal_diag, Matrix.diagonal_mul_diagonal,
    Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  exact mul_comm _ _

end Diag


section Model

open CFSG.RankThree.PartTwo.Sec8.ReeF4Cent2Proof CFSG.RankThree.PartOne.KF4
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootDiagUnit)


variable {m : ℕ} {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime]
  {L : Type} [Field L] [Algebra K L] [IsAlgClosure K L] [IsAlgClosed L] [CharP L 2]
  {K' : Type} [Field K']

private theorem exists_cent_of_model (hK : Nat.card K = 2 ^ (2 * m + 1))
    (D : ReeFrameData K L m) (h : UnitaryFieldData 2 (2 * m + 1) K') (ι : K' →+* L) {ω' : K'}
    (hω' : ω' ^ 2 + ω' + 1 = 0) (hbar : h.bar ω' = ω' + 1)
    (Ψ : unitarySU 2 (2 * m + 1) K' 3 →* ReeTag.F4.reeGamma K m)
    (hΨ : ∀ u, thetaGamma L m (Ψ u) =
      q1C (ι ω') * q1Psi0 D.isFrob (q1SUToSL h ι u) * (q1C (ι ω'))⁻¹) :
    Function.Injective Ψ ∧ ∃ y₀ : ReeTag.F4.reeGamma K m, orderOf y₀ = 3 ∧
      Subgroup.centralizer ({y₀} : Set (ReeTag.F4.reeGamma K m)) = Ψ.range := by
  classical
  have hFrq : ∀ c, D.Frq c = c ^ 2 ^ (2 * m + 1) := frq_eq_pow D hK
  have : Finite K' := h.finite
  have hω : ι ω' ^ 2 + ι ω' + 1 = 0 := by
    rw [← map_pow, ← map_add, ← map_one ι, ← map_add, hω', map_zero]
  have hω0 : ι ω' ≠ 0 := by
    intro h0
    rw [h0] at hω
    norm_num at hω
  set ω : Lˣ := Units.mk0 (ι ω') hω0 with hωdef
  have hω3 : ω ^ 3 = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one]
    linear_combination (ι ω' - 1) * hω
  have hω1 : ω ≠ 1 := by
    intro h1
    have h1' : ι ω' = 1 := by rw [← Units.val_mk0 hω0, ← hωdef, h1, Units.val_one]
    rw [h1'] at hω
    have h3 : (3 : L) = 0 := by linear_combination hω
    have h2 : (2 : L) = 0 := CharTwo.two_eq_zero
    have : (1 : L) = 0 := by linear_combination h3 - h2
    exact one_ne_zero this
  have hωω : (ω * ω)⁻¹ = ω := by
    rw [inv_eq_iff_mul_eq_one, ← pow_three', hω3]
  have hFr : ∀ c, D.Frq (ι c) = ι (h.bar c) := fun c => by
    rw [frq_eq_pow D hK, UnitaryFieldData.bar_apply, map_pow]
  have hj : Function.Injective (q1SUToSL h ι) := by
    rw [injective_iff_map_eq_one]
    intro u hu
    have hm : ((u : GL (Fin 3) K') : Matrix (Fin 3) (Fin 3) K').map ι = 1 := by
      rw [← coe_q1SUToSL h ι, hu]
      rfl
    have hm' : ((u : GL (Fin 3) K') : Matrix (Fin 3) (Fin 3) K') = 1 :=
      Matrix.map_injective ι.injective (hm.trans (Matrix.map_one ι ι.map_zero ι.map_one).symm)
    exact Subtype.ext (Units.ext hm')
  have hΨinj : Function.Injective Ψ := by
    rw [injective_iff_map_eq_one]
    intro u hu
    have h1 := (hΨ u).symm
    rw [hu, map_one, mul_inv_eq_one, mul_eq_left] at h1
    have h2 : q1SUToSL h ι u = 1 := q1Psi0_injective D.isFrob (by rw [h1, map_one])
    exact hj (by rw [h2, map_one])
  refine ⟨hΨinj, ?_⟩
  obtain ⟨x₀, hx₀⟩ := exists_scalar_unitarySU h hω' hbar
  have hjx₀ : q1SUToSL h ι x₀ = diag2 ω ω := by
    apply Subtype.ext
    rw [coe_q1SUToSL, hx₀, coe_diag2, Matrix.scalar_apply, Matrix.diagonal_map ι.map_zero]
    congr 1
    funext k
    fin_cases k
    · rfl
    · rfl
    · show ι ω' = (((ω * ω)⁻¹ : Lˣ) : L)
      rw [hωω, hωdef, Units.val_mk0]
  set d := rootDiagUnit ReeTag.F4.tag (fun _ => ω * ω) with hd
  have hψd : q1Psi0 D.isFrob (q1SUToSL h ι x₀) = d := by
    rw [hjx₀, q1Psi0_scalar D.isFrob hω3]
  set y₀ := Ψ x₀ with hy₀
  have hθy₀ : thetaGamma L m y₀ = q1C (ι ω') * d * (q1C (ι ω'))⁻¹ := by rw [hΨ x₀, hψd]
  have hx₀c : ∀ u : unitarySU 2 (2 * m + 1) K' 3, u * x₀ = x₀ * u := by
    intro u
    apply Subtype.ext
    apply Units.ext
    change ((u : GL (Fin 3) K') : Matrix (Fin 3) (Fin 3) K') * ((x₀ : GL (Fin 3) K') :
      Matrix (Fin 3) (Fin 3) K') = ((x₀ : GL (Fin 3) K') : Matrix (Fin 3) (Fin 3) K') *
        ((u : GL (Fin 3) K') : Matrix (Fin 3) (Fin 3) K')
    rw [hx₀]
    exact (Matrix.scalar_commute ω' (fun _ => Commute.all _ _) _).symm
  have hord : orderOf y₀ = 3 := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    rw [hy₀, orderOf_injective Ψ hΨinj x₀]
    refine orderOf_eq_prime ?_ ?_
    · have h3 : q1SUToSL h ι (x₀ ^ 3) = 1 := by
        rw [map_pow, hjx₀]
        apply Subtype.ext
        rw [Matrix.SpecialLinearGroup.coe_pow, coe_diag2, Matrix.diagonal_pow,
          Matrix.SpecialLinearGroup.coe_one, ← Matrix.diagonal_one]
        congr 1
        funext k
        fin_cases k
        · show (ω : L) ^ 3 = 1
          rw [← Units.val_pow_eq_pow_val, hω3, Units.val_one]
        · show (ω : L) ^ 3 = 1
          rw [← Units.val_pow_eq_pow_val, hω3, Units.val_one]
        · show (((ω * ω)⁻¹ : Lˣ) : L) ^ 3 = 1
          rw [← Units.val_pow_eq_pow_val, show ((ω * ω)⁻¹) ^ 3 = (ω ^ 3)⁻¹ ^ 2 by group, hω3,
            inv_one, one_pow, Units.val_one]
      exact hj (h3.trans (map_one _).symm)
    · intro h1
      apply hω1
      have h2 := congrArg (q1SUToSL h ι) h1
      rw [hjx₀, map_one] at h2
      have h3 := congrArg (fun A : SL(3, L) => (A : Matrix (Fin 3) (Fin 3) L) 0 0) h2
      simp only [coe_diag2, Matrix.SpecialLinearGroup.coe_one, Matrix.diagonal_apply_eq,
        Matrix.one_apply_eq] at h3
      exact Units.ext h3
  refine ⟨y₀, hord, ?_⟩
  have hω2 : orderOf (ω * ω) = 3 := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    refine orderOf_eq_prime ?_ ?_
    · rw [← sq, ← pow_mul, show 2 * 3 = 3 * 2 by rfl, pow_mul, hω3, one_pow]
    · intro h1
      apply hω1
      calc ω = ω ^ 3 * (ω * ω)⁻¹ := by rw [hωω, hω3, one_mul]
        _ = 1 := by rw [h1, hω3, inv_one, one_mul]
  have hstab := rootCharStabilizer_const_subset (L := L) hω2
  have hker := rootCharKernel_const_subset (L := L) hω2 (q1Par_cases m)
  apply le_antisymm
  · intro γ hγ
    rw [Subgroup.mem_centralizer_singleton_iff] at hγ
    set v := thetaGamma L m γ with hv
    set c := q1C (ι ω') with hc
    have hvadj : v ∈ adjointGroup ReeTag.F4.tag L := thetaGamma_mem_adjointGroup L γ
    have hcadj : c ∈ adjointGroup ReeTag.F4.tag L := q1C_mem_adjoint (ι ω')
    have hzR : c⁻¹ * v * c ∈ twistedFixed D.F (q1N L m) :=
      conj_mem_twistedFixed D.F hcadj (q1C_fext D.isFrob hω) hvadj (D.fext_theta γ)
    have hvy : v * thetaGamma L m y₀ = thetaGamma L m y₀ * v := by
      rw [hv, ← map_mul, ← map_mul, hγ]
    rw [hθy₀] at hvy
    have hzd : (c⁻¹ * v * c) * d = d * (c⁻¹ * v * c) := by
      calc (c⁻¹ * v * c) * d = c⁻¹ * (v * (c * d * c⁻¹)) * c := by group
        _ = c⁻¹ * ((c * d * c⁻¹) * v) * c := by rw [hvy]
        _ = d * (c⁻¹ * v * c) := by group
    have hzT : c⁻¹ * v * c ∈ toralCentralizer ReeTag.F4.tag L (fun _ => ω * ω) :=
      ⟨hzR.1, Subgroup.mem_centralizer_singleton_iff.2 hzd⟩
    have hzΦ : c⁻¹ * v * c ∈ (frameProd D.isFrob).range :=
      sup_le (torusGroup_le_range D.isFrob) (rootSpan_le_range D.isFrob)
        (CFSG.RankThree.PartOne.KE.toralCentralizer_le_sup_rootSpan_of_stab hstab
          (fun α hα => isRoot_of_mem_a2a2Roots hα)
          (fun α hα => neg_mem_a2a2Roots (q1Par_cases m) hα) hker hzT)
    obtain ⟨⟨g, h'⟩, hgh⟩ := hzΦ
    rw [frameProd_apply] at hgh
    have hfix : twistMap D.F (q1N L m) (q1Rho L g * q1PsiRho D.F m h') =
        q1Rho L g * q1PsiRho D.F m h' := by
      rw [hgh]
      exact hzR.2
    obtain ⟨g', hg', hzg'⟩ := exists_q1Psi0_of_twist_fixed D.isFrob D.Frq hFrq g h' hfix
    have hrange : ∀ c : L, D.Frq (D.Frq c) = c → ∃ x, ι x = c := by
      intro c hc2
      refine exists_eq_of_pow_card_eq ι ?_
      rw [h.card, show 2 * (2 * m + 1) = (2 * m + 1) * 2 by ring, pow_mul, sq, pow_mul,
        ← hFrq, ← hFrq, hc2]
    obtain ⟨u, hu⟩ := exists_q1SUToSL_eq_of_fixed h ι D.Frq hFr hrange hg'
    refine ⟨u, thetaGamma_injective (K := K) L (a := m) ?_⟩
    rw [hΨ u, hu, ← hzg', hgh, hv]
    group
  · rintro _ ⟨u, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, hy₀, ← map_mul, ← map_mul, hx₀c u]

private theorem exists_gen_of_model (hm : 1 ≤ m) (hK : Nat.card K = 2 ^ (2 * m + 1))
    (D : ReeFrameData K L m) (h : UnitaryFieldData 2 (2 * m + 1) K') (ι : K' →+* L) {ω' : K'}
    (hω' : ω' ^ 2 + ω' + 1 = 0) (hbar : h.bar ω' = ω' + 1)
    (Ψ : unitarySU 2 (2 * m + 1) K' 3 →* ReeTag.F4.reeGamma K m)
    (hΨ : ∀ u, thetaGamma L m (Ψ u) =
      q1C (ι ω') * q1Psi0 D.isFrob (q1SUToSL h ι u) * (q1C (ι ω'))⁻¹)
    (hΨinj : Function.Injective Ψ) :
    ∃ E : Subgroup (unitarySU 2 (2 * m + 1) K' 3),
      (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) ∧ (∀ x ∈ E, x ^ 3 = 1) ∧ Nat.card E = 3 ^ 2 ∧
      (∀ x ∈ E, ∀ i j : Fin 3, i ≠ j →
        ((x : GL (Fin 3) K') : Matrix (Fin 3) (Fin 3) K') i j = 0) ∧
      Subgroup.closure (CFSG.RankThree.PartOne.SEITZ3.cenGen (E.map Ψ)) = ⊤ := by
  classical
  have hω : ι ω' ^ 2 + ι ω' + 1 = 0 := by
    rw [← map_pow, ← map_add, ← map_one ι, ← map_add, hω', map_zero]
  have hpq : 3 ∣ 2 ^ (2 * m + 1) + 1 :=
    CFSG.RankThree.PartTwo.Sec8.ReeF4Cent2Proof.three_dvd_two_pow_odd_add_one m
  have hq : 2 ^ (2 * m + 1) ≠ 2 := by
    have : 2 ^ 3 ≤ 2 ^ (2 * m + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  obtain ⟨E'', hcomm, hexp, hcard, hdiag, x₁, hx₁E, hx₁1, z, hz, hx₁z⟩ := q3_plane h hpq
  refine ⟨E'', hcomm, hexp, hcard, hdiag, ?_⟩
  let EΓ : Subgroup (ReeTag.F4.reeGamma K m) := E''.map Ψ
  have hexpΓ : ∀ x ∈ EΓ, x ^ 3 = 1 := by
    rintro _ ⟨u, hu, rfl⟩
    rw [← map_pow, hexp u hu, map_one]
  have hcardΓ : Nat.card EΓ = 3 ^ 2 := by
    rw [Subgroup.card_map_of_injective hΨinj, hcard]
  set DΓ := Subgroup.closure (CFSG.RankThree.PartOne.SEITZ3.cenGen EΓ) with hDΓ
  have hmem : ∀ k x : ReeTag.F4.reeGamma K m, x ∈ EΓ → x ≠ 1 → k * x = x * k → k ∈ DΓ :=
    fun k x hx hx1 hkx => Subgroup.subset_closure ⟨x, hx, hx1, hkx⟩
  have hSU : ∀ u : unitarySU 2 (2 * m + 1) K' 3, Ψ u ∈ DΓ := by
    intro u
    have hcl := CFSG.RankThree.PartOne.CTP.closure_centralizers_unitarySU_of_dvd_add_one (n := 2)
      h Nat.prime_three hpq hq E'' hcomm hexp hcard
    have hu : u ∈ Subgroup.closure {g | ∃ x ∈ E'', x ≠ 1 ∧ g * x = x * g} := by
      rw [hcl]
      exact Subgroup.mem_top u
    have h2 := Subgroup.mem_map_of_mem Ψ hu
    rw [MonoidHom.map_closure] at h2
    refine (Subgroup.closure_le _).2 ?_ h2
    rintro _ ⟨g, ⟨x, hx, hx1, hgx⟩, rfl⟩
    refine hmem (Ψ g) (Ψ x) ⟨x, hx, rfl⟩ (fun h1 => hx1 (hΨinj (by rw [h1, map_one]))) ?_
    rw [← map_mul, ← map_mul, hgx]
  obtain ⟨g, hg⟩ := q1_exists_g D hω
  have hT : ∀ x ∈ EΓ, (q1C (ι ω'))⁻¹ * thetaGamma L m x * q1C (ι ω') ∈
      torusGroup ReeTag.F4.tag L := by
    rintro _ ⟨u, hu, rfl⟩
    rw [hΨ u, show (q1C (ι ω'))⁻¹ * (q1C (ι ω') * q1Psi0 D.isFrob (q1SUToSL h ι u) *
      (q1C (ι ω'))⁻¹) * q1C (ι ω') = q1Psi0 D.isFrob (q1SUToSL h ι u) by group]
    refine q1Psi0_mem_torusGroup D.isFrob _ fun i k hik => ?_
    rw [coe_q1SUToSL, Matrix.map_apply, hdiag u hu i k hik, map_zero]
  have hnorm := q3_conj_mem hK EΓ hT hexpΓ hcardΓ g hg
  have hcjE : CFSG.RankThree.PartOne.SEITZ3.cj EΓ g = EΓ := by
    refine Subgroup.eq_of_le_of_card_ge ?_ (by rw [CFSG.RankThree.PartOne.SEITZ3.card_cj])
    rintro _ ⟨y, hy, rfl⟩
    exact hnorm y hy
  have hconj : ∀ y ∈ DΓ, g * y * g⁻¹ ∈ DΓ := by
    intro y hy
    have h2 : Subgroup.closure (CFSG.RankThree.PartOne.SEITZ3.cenGen
        (CFSG.RankThree.PartOne.SEITZ3.cj EΓ g)) =
        (Subgroup.closure (CFSG.RankThree.PartOne.SEITZ3.cenGen EΓ)).map
          (MulAut.conj g).toMonoidHom :=
      CFSG.RankThree.PartOne.SEITZ3.closure_cenGen_cj EΓ g
    rw [hcjE] at h2
    have h3 : (MulAut.conj g).toMonoidHom y ∈
        (Subgroup.closure (CFSG.RankThree.PartOne.SEITZ3.cenGen EΓ)).map
          (MulAut.conj g).toMonoidHom := Subgroup.mem_map_of_mem _ hy
    rw [← h2] at h3
    exact h3
  have hM0 : ReeTag.F4.reeLocalBlock K m ⟨0, by decide⟩ ≤
      DΓ.map (ReeTag.F4.reeGamma K m).subtype := by
    intro y hy
    have hyΓ : y ∈ ReeTag.F4.reeGamma K m := by
      have hle : ReeTag.F4.reeLocalBlock K m ⟨0, by decide⟩ ≤ ReeTag.F4.reeGamma K m :=
        sup_le inf_le_right inf_le_right
      exact hle hy
    have hd : ((q1SUToSL h ι x₁ : SL(3, L)) : Matrix (Fin 3) (Fin 3) L) =
        Matrix.diagonal ![ι z, 1, (ι z)⁻¹] := by
      rw [coe_q1SUToSL, hx₁z, Matrix.diagonal_map ι.map_zero]
      congr 1
      funext i
      fin_cases i <;> simp [map_inv₀]
    have hc := q1_commute_localBlock D (ι ω') (Ψ x₁) (q1SUToSL h ι x₁) (ι z)
      ((map_ne_zero ι).2 hz) hd (hΨ x₁) y hy
    exact ⟨⟨y, hyΓ⟩, hmem ⟨y, hyΓ⟩ (Ψ x₁) ⟨x₁, hx₁E, rfl⟩
      (fun h1 => hx₁1 (hΨinj (by rw [h1, map_one]))) (Subtype.ext hc.symm), rfl⟩
  obtain ⟨u, hu⟩ := q1_exists_letters h hω' hbar
  have hu' : ∀ k, q1SUToSL h ι (u k) = q1TvProd (ι ω') (q1LetterDec k) :=
    fun k => q1SUToSL_letter h ι hω' (u k) k (hu k)
  have hpar : q1Par m = if (m % 2 == 1) then 3 else 0 := by
    rcases Nat.mod_two_eq_zero_or_one m with h0 | h1
    · simp [q1Par, h0]
    · simp [q1Par, h1]
  have hlet := q1_letters_eq D hω (m % 2 == 1) hpar (f4Ev_pow_two_pow hω m) Ψ
    (q1SUToSL h ι) hΨ u hu' g hg
  have hprod : ∀ tgt : Bool, ((q1Letters tgt).map fun x =>
      if x.1 then g * Ψ (u x.2) * g⁻¹ else Ψ (u x.2)).prod ∈ DΓ := by
    intro tgt
    refine list_prod_mem fun y hy => ?_
    obtain ⟨⟨side, k⟩, -, rfl⟩ := List.mem_map.1 hy
    cases side
    · exact hSU (u k)
    · exact hconj _ (hSU (u k))
  have hB : LargeReeInvolution.sylowB m K 1 0 ∈ DΓ.map (ReeTag.F4.reeGamma K m).subtype := by
    have h1 : ((((q1Letters true).map fun x => if x.1 then g * Ψ (u x.2) * g⁻¹ else
        Ψ (u x.2)).prod : ReeTag.F4.reeGamma K m) : ModGL ReeTag.F4.tag K) ∈
        DΓ.map (ReeTag.F4.reeGamma K m).subtype := Subgroup.mem_map_of_mem _ (hprod true)
    rwa [hlet true] at h1
  have hn : LargeReeInvolution.weylTwo K ∈ DΓ.map (ReeTag.F4.reeGamma K m).subtype := by
    have h1 : ((((q1Letters false).map fun x => if x.1 then g * Ψ (u x.2) * g⁻¹ else
        Ψ (u x.2)).prod : ReeTag.F4.reeGamma K m) : ModGL ReeTag.F4.tag K) ∈
        DΓ.map (ReeTag.F4.reeGamma K m).subtype := Subgroup.mem_map_of_mem _ (hprod false)
    rwa [hlet false] at h1
  have hDE := reeGamma_le_of_localBlock_zero hK (DΓ.map (ReeTag.F4.reeGamma K m).subtype)
    hM0 hB hn
  rw [eq_top_iff]
  intro γ _
  obtain ⟨δ, hδ, hδγ⟩ := hDE γ.2
  have hδ' : δ = γ := Subtype.ext hδγ
  rwa [← hδ']

end Model

theorem reeGamma_closure_cenGen_eq_top_three {m : ℕ} (hm : 1 ≤ m) {K : Type} [Field K]
    [Finite K] [CharP K ReeTag.F4.prime] (hK : Nat.card K = 2 ^ (2 * m + 1))
    (F : Subgroup (ReeTag.F4.reeGamma K m)) (hFp : ∀ x ∈ F, x ^ 3 = 1)
    (hFc : Nat.card F = 3 ^ 2) :
    Subgroup.closure (CFSG.RankThree.PartOne.SEITZ3.cenGen F) = ⊤ := by
  classical
  have : Finite (ReeTag.F4.reeGamma K m) := Subtype.finite
  let L := AlgebraicClosure K
  have : CharP L 2 := charP_of_injective_algebraMap (algebraMap K L).injective 2
  obtain ⟨D⟩ := reeFrameData_nonempty (K := K) (L := L) hK
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let K' := GaloisField 2 (2 * (2 * m + 1))
  have hK' : Nat.card K' = 2 ^ (2 * (2 * m + 1)) := GaloisField.card 2 _ (by omega)
  have h : UnitaryFieldData 2 (2 * m + 1) K' := ⟨Nat.prime_two, by omega, hK'⟩
  let _ : Algebra (ZMod 2) L := ZMod.algebra L 2
  have : Algebra.IsAlgebraic (ZMod 2) K' := Algebra.IsAlgebraic.of_finite (ZMod 2) K'
  let ι : K' →+* L := (IsAlgClosed.lift (R := ZMod 2) (S := K') (M := L)).toRingHom
  obtain ⟨ω', hω', hbar⟩ := q1_exists_omega h (odd_two_mul_add_one m)
  have hω : ι ω' ^ 2 + ι ω' + 1 = 0 := by
    rw [← map_pow, ← map_add, ← map_one ι, ← map_add, hω', map_zero]
  have hFr : ∀ c, D.Frq (ι c) = ι (h.bar c) := fun c => by
    rw [frq_eq_pow D hK, UnitaryFieldData.bar_apply, map_pow]
  obtain ⟨Ψ, hΨ⟩ := q1_exists_hom D hK hω (q1SUToSL h ι) (q1SUToSL_fixed h ι D.Frq hFr)
  obtain ⟨hΨinj, y₀, hy₀, hcent⟩ := exists_cent_of_model hK D h ι hω' hbar Ψ hΨ
  obtain ⟨E, hEcomm, hEexp, hEcard, hEdiag, hEgen⟩ :=
    exists_gen_of_model hm hK D h ι hω' hbar Ψ hΨ hΨinj
  have hpq : 3 ∣ 2 ^ (2 * m + 1) + 1 :=
    CFSG.RankThree.PartTwo.Sec8.ReeF4Cent2Proof.three_dvd_two_pow_odd_add_one m
  obtain ⟨c, hc⟩ := exists_cj_eq_map_of_plane Ψ hΨinj y₀ hy₀ hcent
    (fun y y' hy hy' => CFSG.RankThree.PartTwo.Sec8.Item8KFacts3Ree.reeGamma_orderThree_conj m K
      hK y y' hy hy')
    (fun W hWc hWe => CFSG.RankThree.PartTwo.Sec21.ReeF4ThreeLocalProof.card_le_nine_of_reeGamma m K
      hK W ⟨⟨⟨fun a b => Subtype.ext (hWc a a.2 b b.2)⟩⟩, hWe⟩)
    (fun x : unitarySU 2 (2 * m + 1) K' 3 => ∀ i j : Fin 3, i ≠ j →
      ((x : GL (Fin 3) K') : Matrix (Fin 3) (Fin 3) K') i j = 0)
    sudiag_one (fun x y hx hy => sudiag_mul hx hy) (fun x y hx hy => sudiag_comm hx hy)
    (fun F₀ hc he => exists_conj_diag_of_three h hpq F₀ hc he)
    E hEdiag hEexp hEcard F hFp hFc
  have hF : F = CFSG.RankThree.PartOne.SEITZ3.cj (E.map Ψ) c⁻¹ := by
    rw [← hc, CFSG.RankThree.PartOne.SEITZ3.cj_cj]
  rw [hF, CFSG.RankThree.PartOne.SEITZ3.closure_cenGen_cj, hEgen]
  exact Subgroup.map_top_of_surjective _ (MulAut.conj c⁻¹).surjective

end CFSG.RankThree.PartOne.SEITZQ3
