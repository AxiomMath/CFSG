module

public import CFSG.RankThree.PartTwo.Sec4.Item413Eigen
import CFSG.RankThree.PartTwo.Census.Classical.Bridges
public import CFSG.RankThree.PartTwo.Sec4.Item413AutGen
public import CFSG.RankThree.PartTwo.Sec4.Item47CasesEven

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG Matrix
open CFSG.Assembly.RankThreeEven (projSL projSU projSp projImage sympForm)

theorem card_le_of_surjective_of_ker {S Q : Type*} [Group S] [Group Q] [Finite S] (ρ : S →* Q)
    (hρ : Function.Surjective ρ) {m : ℕ} (hm : Nat.Coprime m 3)
    (hker : ∀ s, ρ s = 1 → s ^ m = 1) {N : ℕ}
    (hN : ∀ P : Subgroup S, (∀ x ∈ P, ∀ y ∈ P, x * y = y * x) → (∀ x ∈ P, x ^ 3 = 1) →
      Nat.card P ≤ N)
    (E : Subgroup Q) (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hexp : ∀ x ∈ E, x ^ 3 = 1) :
    Nat.card E ≤ N := by
  have : Finite Q := Finite.of_surjective ρ hρ
  set Et := E.comap ρ
  have hdvd : Nat.card E ∣ Nat.card Et := by
    have h := Subgroup.card_map_dvd (H := Et) ρ
    rwa [Subgroup.map_comap_eq_self_of_surjective hρ] at h
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hEp : IsPGroup 3 E := fun g => ⟨1, Subtype.ext (by simpa using hexp g g.2)⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hEp
  obtain ⟨P⟩ : Nonempty (Sylow 3 Et) := inferInstance
  have hP : 3 ^ k ∣ Nat.card P := P.pow_dvd_card_of_pow_dvd_card (hk ▸ hdvd)
  set Q' : Subgroup S := (P : Subgroup Et).map Et.subtype
  have hQcard : Nat.card Q' = Nat.card P :=
    Subgroup.card_map_of_injective Et.subtype_injective
  have hQp : IsPGroup 3 Q' := P.isPGroup'.map Et.subtype
  have htriv : ∀ s ∈ Q', ρ s = 1 → s = 1 := by
    intro s hs h1
    obtain ⟨n, hn⟩ := hQp ⟨s, hs⟩
    have hn' : s ^ (3 ^ n) = 1 := by simpa using congrArg Subtype.val hn
    have h := pow_gcd_eq_one.mpr ⟨hker s h1, hn'⟩
    rwa [Nat.Coprime.pow_right n hm, pow_one] at h
  have hQE : ∀ s ∈ Q', ρ s ∈ E := by
    rintro _ ⟨t, -, rfl⟩
    exact t.2
  have hQcomm : ∀ s ∈ Q', ∀ t ∈ Q', s * t = t * s := by
    intro s hs t ht
    have h := htriv (s * t * s⁻¹ * t⁻¹)
      (Q'.mul_mem (Q'.mul_mem (Q'.mul_mem hs ht) (Q'.inv_mem hs)) (Q'.inv_mem ht)) (by
        rw [map_mul, map_mul, map_mul, map_inv, map_inv, hcomm _ (hQE s hs) _ (hQE t ht)]
        group)
    calc s * t = s * t * s⁻¹ * t⁻¹ * (t * s) := by group
      _ = t * s := by rw [h, one_mul]
  have hQexp : ∀ s ∈ Q', s ^ 3 = 1 := fun s hs =>
    htriv _ (Q'.pow_mem hs 3) (by rw [map_pow, hexp _ (hQE s hs)])
  have hle := hN Q' hQcomm hQexp
  rw [hQcard] at hle
  rw [hk]
  exact (Nat.le_of_dvd Nat.card_pos hP).trans hle

section ProjImage

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K] [Finite K]

theorem card_le_of_projImage (H : Subgroup (GL ι K)) (hs : IsSimpleGroup (projImage H)) {m : ℕ}
    (hm : Nat.Coprime m 3)
    (hscal : ∀ c : Kˣ, GeneralLinearGroup.scalar ι c ∈ H → c ^ m = 1) {N : ℕ} (hN1 : 1 ≤ N)
    (hN : ∀ P : Subgroup (GL ι K), P ≤ H → (∀ x ∈ P, ∀ y ∈ P, x * y = y * x) →
      (∀ x ∈ P, x ^ 3 = 1) → Nat.card P ≤ N)
    (B : Subgroup (projImage H ⧸ Subgroup.center (projImage H)))
    (hB : CFSG.Assembly.IsElemAbelian 3 B) : Nat.card B ≤ N := by
  classical
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center (projImage H)) with hZ | hZ
  · set π₀ : H →* projImage H := (ProjGenLinGroup.mk).subgroupMap H
    set ρ := (QuotientGroup.mk' (Subgroup.center (projImage H))).comp π₀
    have hρ : Function.Surjective ρ :=
      (QuotientGroup.mk'_surjective _).comp ((ProjGenLinGroup.mk).subgroupMap_surjective H)
    refine card_le_of_surjective_of_ker ρ hρ hm ?_ (fun P hPc hPe => ?_) B
      (fun x hx y hy => congrArg Subtype.val (hB.1.1.comm ⟨x, hx⟩ ⟨y, hy⟩))
      (fun x hx => hB.2 x hx)
    · intro s hs
      rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hZ,
        Subgroup.mem_bot] at hs
      have hs' : ProjGenLinGroup.mk (s : GL ι K) = 1 := congrArg Subtype.val hs
      rw [ProjGenLinGroup.mk_eq_one, GeneralLinearGroup.center_eq_range_scalar] at hs'
      obtain ⟨c, hc⟩ := hs'
      have hcm := hscal c (hc ▸ s.2)
      apply Subtype.ext
      rw [Subgroup.coe_pow, Subgroup.coe_one, ← hc, ← map_pow, hcm, map_one]
    · have := hN (P.map H.subtype) (by rintro _ ⟨x, -, rfl⟩; exact x.2)
        (by
          rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
          rw [← map_mul, ← map_mul, hPc x hx y hy])
        (by
          rintro _ ⟨x, hx, rfl⟩
          rw [← map_pow, hPe x hx, map_one])
      rwa [Subgroup.card_map_of_injective H.subtype_injective] at this
  · have : Subsingleton (projImage H ⧸ Subgroup.center (projImage H)) := by
      constructor
      intro a b
      induction a using QuotientGroup.induction_on with
      | H a =>
        induction b using QuotientGroup.induction_on with
        | H b =>
          rw [QuotientGroup.eq, hZ]
          exact Subgroup.mem_top _
    calc Nat.card B = 1 := Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, inferInstance⟩
      _ ≤ N := hN1

omit [Finite K] in
theorem form_of_mem_closure {M : Matrix ι ι K} {A : GL ι K}
    (hA : A ∈ Subgroup.closure {A : GL ι K | (A : Matrix ι ι K)ᵀ * M * A = M}) :
    (A : Matrix ι ι K)ᵀ * M * A = M := by
  induction hA using Subgroup.closure_induction with
  | mem x hx => exact hx
  | one => simp
  | mul x y _ _ hx hy =>
    calc ((x * y : GL ι K) : Matrix ι ι K)ᵀ * M * ((x * y : GL ι K) : Matrix ι ι K) =
        (y : Matrix ι ι K)ᵀ * ((x : Matrix ι ι K)ᵀ * M * x) * y := by
          rw [Units.val_mul, Matrix.transpose_mul]
          simp only [Matrix.mul_assoc]
      _ = M := by rw [hx, hy]
  | inv x _ hx =>
    calc ((x⁻¹ : GL ι K) : Matrix ι ι K)ᵀ * M * ((x⁻¹ : GL ι K) : Matrix ι ι K) =
        ((x⁻¹ : GL ι K) : Matrix ι ι K)ᵀ * ((x : Matrix ι ι K)ᵀ * M * x) *
          ((x⁻¹ : GL ι K) : Matrix ι ι K) := by rw [hx]
      _ = ((x : Matrix ι ι K) * ((x⁻¹ : GL ι K) : Matrix ι ι K))ᵀ * M *
          ((x : Matrix ι ι K) * ((x⁻¹ : GL ι K) : Matrix ι ι K)) := by
          rw [Matrix.transpose_mul]
          simp only [Matrix.mul_assoc]
      _ = M := by
          rw [← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.transpose_one,
            Matrix.one_mul, Matrix.mul_one]

end ProjImage

theorem card_le_27_of_det {K : Type} [Field K] [Finite K] (h3 : (3 : K) ≠ 0)
    (P : Subgroup (GL (Fin 4) K)) (hcomm : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x)
    (hexp : ∀ x ∈ P, x ^ 3 = 1) (hdet : ∀ x ∈ P, (x : Matrix (Fin 4) (Fin 4) K).det = 1) :
    Nat.card P ≤ 27 := by
  have := card_le_of_det_eq_one h3 0 P hcomm hexp hdet
  simpa using this

theorem pow_four_of_det_scalar {K : Type} [Field K] {c : Kˣ}
    (h : ((GeneralLinearGroup.scalar (Fin 4) c : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).det =
      1) : c ^ 4 = 1 := by
  have h' : GeneralLinearGroup.det (GeneralLinearGroup.scalar (Fin 4) c) = 1 :=
    Units.ext (by rw [GeneralLinearGroup.val_det_apply, h, Units.val_one])
  rwa [GeneralLinearGroup.det_scalar, Fintype.card_fin] at h'

theorem rankL4_holds : ∀ (p : ℕ) [Fact p.Prime], 3 < p → p % 3 = 2 →
    CFSG.pRank 3 (projSL 4 (GaloisField p 1) ⧸
      Subgroup.center (projSL 4 (GaloisField p 1))) ≤ 3 := by
  intro p _ hp3 _
  set F := GaloisField p 1
  have hF : Nat.card F = p ^ 1 := GaloisField.card p 1 (by norm_num)
  have h3 : (3 : F) ≠ 0 := three_ne_zero_of_card Fact.out (by omega) hF
  have hs : IsSimpleGroup (projSL 4 F) := by
    have := CFSG.BenderSuzuki.External.huppert_II_6_13 (K := F) 4 (by norm_num)
      (Or.inl (by norm_num)) (Or.inl (by norm_num))
    exact (projSLEquivPSLn 4 F).isSimpleGroup
  refine pRank_three_le_of_card_le fun B hB =>
    card_le_of_projImage (GeneralLinearGroup.det : GL (Fin 4) F →* Fˣ).ker hs (m := 4)
      (by norm_num) (fun c hc => ?_) (by norm_num) (fun P hPH hcomm hexp => ?_) B hB
  · apply pow_four_of_det_scalar
    have := congrArg Units.val (MonoidHom.mem_ker.mp hc)
    rwa [GeneralLinearGroup.val_det_apply] at this
  · refine card_le_27_of_det h3 P hcomm hexp fun x hx => ?_
    have := congrArg Units.val (MonoidHom.mem_ker.mp (hPH hx))
    rwa [GeneralLinearGroup.val_det_apply] at this

theorem det_of_mem_closure_su {n : ℕ} {K : Type} [Field K] (q : ℕ) {A : GL (Fin n) K}
    (hA : A ∈ Subgroup.closure {A : GL (Fin n) K | GeneralLinearGroup.det A = 1 ∧
      ((A : Matrix (Fin n) (Fin n) K).map (· ^ q))ᵀ * (A : Matrix (Fin n) (Fin n) K) = 1}) :
    (A : Matrix (Fin n) (Fin n) K).det = 1 := by
  have hle : Subgroup.closure {A : GL (Fin n) K | GeneralLinearGroup.det A = 1 ∧
      ((A : Matrix (Fin n) (Fin n) K).map (· ^ q))ᵀ * (A : Matrix (Fin n) (Fin n) K) = 1} ≤
      (GeneralLinearGroup.det : GL (Fin n) K →* Kˣ).ker :=
    (Subgroup.closure_le _).mpr fun B hB => hB.1
  have := congrArg Units.val (MonoidHom.mem_ker.mp (hle hA))
  rwa [GeneralLinearGroup.val_det_apply] at this

theorem pRank_projSU_four_le (p f : ℕ) [Fact p.Prime] (hp3 : p ≠ 3) (hf : 1 ≤ f) :
    CFSG.pRank 3 (projSU 4 p f ⧸ Subgroup.center (projSU 4 p f)) ≤ 3 := by
  set F := GaloisField p (2 * f)
  have hF : Nat.card F = p ^ (2 * f) := GaloisField.card p (2 * f) (by omega)
  have h3 : (3 : F) ≠ 0 := three_ne_zero_of_card Fact.out hp3 hF
  have hs : IsSimpleGroup (projSU 4 p f) := by
    have := CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU F p f
      (by rw [hF, ← pow_mul, mul_comm]) 4 (by norm_num) (by
        intro h
        exact absurd (Prod.mk.inj h).1 (by norm_num))
    exact (projSUEquivStatedProj 4 p f).isSimpleGroup
  refine pRank_three_le_of_card_le fun B hB =>
    card_le_of_projImage (Subgroup.closure {A : GL (Fin 4) F | GeneralLinearGroup.det A = 1 ∧
      ((A : Matrix (Fin 4) (Fin 4) F).map (· ^ (p ^ f)))ᵀ * (A : Matrix (Fin 4) (Fin 4) F) = 1})
      hs (m := 4) (by norm_num) (fun c hc => pow_four_of_det_scalar (det_of_mem_closure_su _ hc))
      (by norm_num)
      (fun P hPH hcomm hexp =>
        card_le_27_of_det h3 P hcomm hexp fun x hx => det_of_mem_closure_su _ (hPH hx)) B hB

theorem rankU4_holds : ∀ (p : ℕ) [Fact p.Prime], 3 < p → p % 3 = 1 →
    CFSG.pRank 3 (projSU 4 p 1 ⧸ Subgroup.center (projSU 4 p 1)) ≤ 3 :=
  fun p _ hp3 _ => pRank_projSU_four_le p 1 (by omega) le_rfl

theorem rankU4Even_holds : ∀ n : ℕ, 1 ≤ n →
    CFSG.pRank 3 (projSU 4 2 n ⧸ Subgroup.center (projSU 4 2 n)) ≤ 3 := by
  intro n hn
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact pRank_projSU_four_le 2 n (by norm_num) hn

theorem det_sympForm_ne_zero (n : ℕ) (K : Type) [Field K] : (sympForm n K).det ≠ 0 := by
  have h : sympForm n K * (-sympForm n K) = 1 := by
    rw [sympForm, Matrix.mul_neg, Matrix.fromBlocks_multiply]
    simp [Matrix.fromBlocks_neg, ← Matrix.fromBlocks_one]
  exact (Matrix.isUnit_det_of_right_inverse h).ne_zero

theorem sq_of_scalar_mem_closure_sp {n : ℕ} (hn : 1 ≤ n) {K : Type} [Field K] {c : Kˣ}
    (hc : GeneralLinearGroup.scalar (Fin n ⊕ Fin n) c ∈ Subgroup.closure
      {A : GL (Fin n ⊕ Fin n) K | (A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)ᵀ *
        sympForm n K * (A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) = sympForm n K}) :
    c ^ 2 = 1 := by
  have h := form_of_mem_closure hc
  have h' := congrFun (congrFun h (Sum.inl ⟨0, hn⟩)) (Sum.inr ⟨0, hn⟩)
  rw [GeneralLinearGroup.coe_scalar] at h'
  simp [Matrix.scalar_apply, Matrix.diagonal_transpose, Matrix.diagonal_mul, Matrix.mul_diagonal,
    sympForm] at h'
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, Units.val_one, sq]
  exact h'

theorem card_sq_le_of_mem_closure_sp {n : ℕ} {K : Type} [Field K] [Finite K] (h3 : (3 : K) ≠ 0)
    (P : Subgroup (GL (Fin n ⊕ Fin n) K))
    (hP : P ≤ Subgroup.closure {A : GL (Fin n ⊕ Fin n) K |
      (A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)ᵀ * sympForm n K *
        (A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) = sympForm n K})
    (hcomm : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x) (hexp : ∀ x ∈ P, x ^ 3 = 1) :
    Nat.card P ^ 2 ≤ 3 ^ (2 * n) := by
  have := card_sq_le_of_form h3 P hcomm hexp (sympForm n K) (det_sympForm_ne_zero n K)
    fun x hx => form_of_mem_closure (hP hx)
  simpa [Fintype.card_sum, two_mul] using this

theorem rankSp4_holds : ∀ (p : ℕ) [Fact p.Prime], 3 < p →
    CFSG.pRank 3 (projSp 2 (GaloisField p 1) ⧸
      Subgroup.center (projSp 2 (GaloisField p 1))) ≤ 3 := by
  intro p _ hp3
  set F := GaloisField p 1
  have hF : Nat.card F = p ^ 1 := GaloisField.card p 1 (by norm_num)
  have h3 : (3 : F) ≠ 0 := three_ne_zero_of_card Fact.out (by omega) hF
  have hs : IsSimpleGroup (projSp 2 F) := by
    have := CFSG.ClassicalGroups.Symplectic.isSimpleGroup_statedProj_statedSp F 2 (by norm_num)
      (Or.inl (Or.inr (by rw [hF, pow_one]; omega)))
    exact (CFSG.RankThree.PartTwo.Census.statedProjEquivProjImage
      (CFSG.Assembly.LowTwoRank.StatedSp 2 F)).symm.isSimpleGroup
  refine pRank_three_le_of_card_le fun B hB =>
    card_le_of_projImage _ hs (m := 2) (by norm_num) (fun c hc => sq_of_scalar_mem_closure_sp
      (by norm_num) hc) (by norm_num) (fun P hPH hcomm hexp => ?_) B hB
  have h := card_sq_le_of_mem_closure_sp h3 P hPH hcomm hexp
  norm_num at h
  nlinarith

theorem rankSp62_holds :
    CFSG.pRank 3 (projSp 3 (GaloisField 2 1) ⧸
      Subgroup.center (projSp 3 (GaloisField 2 1))) ≤ 3 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set F := GaloisField 2 1
  have hF : Nat.card F = 2 ^ 1 := GaloisField.card 2 1 (by norm_num)
  have h3 : (3 : F) ≠ 0 := three_ne_zero_of_card Fact.out (by norm_num) hF
  have hs : IsSimpleGroup (projSp 3 F) := by
    have := CFSG.ClassicalGroups.Symplectic.isSimpleGroup_statedProj_statedSp F 3 (by norm_num)
      (Or.inr (Or.inr ⟨by rw [hF]; norm_num, le_rfl⟩))
    exact (CFSG.RankThree.PartTwo.Census.statedProjEquivProjImage
      (CFSG.Assembly.LowTwoRank.StatedSp 3 F)).symm.isSimpleGroup
  refine pRank_three_le_of_card_le fun B hB =>
    card_le_of_projImage _ hs (m := 2) (by norm_num) (fun c hc => sq_of_scalar_mem_closure_sp
      (by norm_num) hc) (by norm_num) (fun P hPH hcomm hexp => ?_) B hB
  have h := card_sq_le_of_mem_closure_sp h3 P hPH hcomm hexp
  norm_num at h
  nlinarith

end CFSG.RankThree.PartTwo.Sec4
