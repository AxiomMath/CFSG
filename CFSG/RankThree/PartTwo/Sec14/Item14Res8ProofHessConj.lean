module

public import CFSG.RankThree.PartTwo.Sec14.Item14Res8ProofTypeOne
public import CFSG.RankThree.PartTwo.Sec14.Item14Res8ProofHessModel
public import CFSG.RankThree.PartTwo.Sec4.Statements
import CFSG.RankThree.PartTwo.Sec16.Item169StepsProofHess
import CFSG.RankThree.PartTwo.Sec13.Item138NMod9
import CFSG.RankThree.PartTwo.Sec19.Step1915WProofLie3K
import CFSG.RankThree.PartTwo.Sec19.Step1919NarrowRank
import CFSG.RankThree.PartTwo.Sec17.Item17Res7ProofL3Aut

public section

namespace CFSG.RankThree.PartTwo.Sec14.Res8Hess

open Matrix CFSG.RankThree.PartTwo.Sec4 CFSG.LocalAnalysis.ComponentInitial
open CFSG.RankThree.PartTwo.Sec17.Proof17Res7
open CFSG.Assembly.RankThreeEven (projImage)
open CFSG.Assembly.LowTwoRank (StatedScalars)

theorem exists_pair_of_card_nine {M : Type} [Group M] [Finite M] {E : Subgroup M}
    (hEe : CFSG.Assembly.IsElemAbelian 3 E) (hE9 : Nat.card E = 9) :
    ∃ e₁ ∈ E, e₁ ≠ 1 ∧ ∃ e₂ ∈ E, e₂ ∉ Subgroup.zpowers e₁ := by
  obtain ⟨⟨e₁, he₁⟩, he₁1⟩ : ∃ x : E, x ≠ 1 := by
    have : Nontrivial E := Finite.one_lt_card_iff_nontrivial.mp (by rw [hE9]; norm_num)
    exact exists_ne 1
  refine ⟨e₁, he₁, fun h => he₁1 (Subtype.ext h), ?_⟩
  by_contra hcon
  push Not at hcon
  have hle : E ≤ Subgroup.zpowers e₁ := hcon
  have h1 := Subgroup.card_le_of_le hle
  rw [hE9, Nat.card_zpowers] at h1
  have h2 : orderOf e₁ ∣ 3 := orderOf_dvd_of_pow_eq_one (hEe.2 e₁ he₁)
  have h3 := Nat.le_of_dvd (by norm_num) h2
  omega

theorem eq_sup_zpowers_of_card_nine {M : Type} [Group M] [Finite M] {E : Subgroup M}
    (hE9 : Nat.card E = 9) {e₁ e₂ : M} (he₁ : e₁ ∈ E) (he₂ : e₂ ∈ E) (ho : orderOf e₂ = 3)
    (hn : e₂ ∉ Subgroup.zpowers e₁) (hcomm : e₁ * e₂ = e₂ * e₁) (ho1 : orderOf e₁ = 3) :
    E = Subgroup.zpowers e₁ ⊔ Subgroup.zpowers e₂ := by
  have hle : Subgroup.zpowers e₁ ⊔ Subgroup.zpowers e₂ ≤ E :=
    sup_le (Subgroup.zpowers_le.mpr he₁) (Subgroup.zpowers_le.mpr he₂)
  refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  rw [hE9, Sec19.Step1919NarrowRank.card_sup_zpowers_of_orderOf _ ho hn (by
    rintro _ ⟨k, rfl⟩
    exact ((Commute.zpow_left hcomm k).eq)), Nat.card_zpowers, ho1]

variable {K : Type} [Field K] {p f : ℕ} {π : Bool}

theorem exists_conjM'_of_transitive (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    (hπ : π = false → UnitaryFieldData p f K) {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1)
    {dM cM : projImage (slPi π 3 (p ^ f) K)}
    (hdM : (dM : ProjGenLinGroup (Fin 3) K) = ProjGenLinGroup.mk (diagTau hτ))
    (hcM : (cM : ProjGenLinGroup (Fin 3) K) = ProjGenLinGroup.mk (cycThree : GL (Fin 3) K))
    {E : Subgroup (projImage (slPi π 3 (p ^ f) K))} (hEe : CFSG.Assembly.IsElemAbelian 3 E)
    (hE9 : Nat.card E = 9)
    (htr : ∀ y₀ ∈ E, y₀ ≠ 1 → ∀ y₁ ∈ E, y₁ ≠ 1 →
      ∃ w ∈ Subgroup.normalizer (E : Set (projImage (slPi π 3 (p ^ f) K))), w * y₀ * w⁻¹ = y₁) :
    ∃ (g : GL (Fin 3) K) (hg : g ∈ glPi π 3 (p ^ f) K),
      E = (Subgroup.zpowers dM ⊔ Subgroup.zpowers cM).map (conjM' hπ hg).toMonoidHom := by
  have := hK.finite
  have : Finite (ProjGenLinGroup (Fin 3) K) := by
    unfold ProjGenLinGroup
    infer_instance
  have hq' : π = false → ModThree false (p ^ f) := fun h => by subst h; exact hq
  obtain ⟨e₁, he₁, he₁1, e₂, he₂, he₂n⟩ := exists_pair_of_card_nine hEe hE9
  have he₂1 : e₂ ≠ 1 := fun h => he₂n (h ▸ one_mem _)
  have hcube := hasCubeOneLift_of_transitive hK hEe hE9 htr
  obtain ⟨y₁, hy₁, hy₁e, hy₁3⟩ := hcube e₁ he₁ he₁1
  obtain ⟨y₂, hy₂, hy₂e, hy₂3⟩ := hcube e₂ he₂ he₂1
  have hcomm : e₁ * e₂ = e₂ * e₁ :=
    congrArg Subtype.val (hEe.1.is_comm.comm ⟨e₁, he₁⟩ ⟨e₂, he₂⟩)
  have hy₁Z : y₁ ∉ zPi π 3 (p ^ f) K := by
    intro hz
    apply he₁1
    apply Subtype.ext
    rw [← hy₁e, OneMemClass.coe_one, ProjGenLinGroup.mk_eq_one,
      GeneralLinearGroup.center_eq_range_scalar]
    exact (Subgroup.mem_inf.mp ((zPi_eq hπ hq' hτ hτ1) ▸ hz)).2
  have hy₁o : orderOf y₁ = 3 := by
    refine orderOf_eq_prime hy₁3 fun h1 => hy₁Z ?_
    rw [h1]
    exact one_mem _
  obtain ⟨g₁, hg₁, hg₁y⟩ := rank3II_4_10_three hK hq hτ hτ1 hy₁ hy₁Z hy₁o
  obtain ⟨ζ, hζ⟩ := exists_conj_of_comm hcomm hy₁e hy₂e
  have hζ3 : (ζ : K) ^ 3 = 1 := by
    have h := congrArg Units.val (pow_three_eq_one_of_conj_eq_scalar_mul hζ)
    rwa [Units.val_pow_eq_pow_val, Units.val_one] at h
  have hsc : ∀ (u : Kˣ) (A : GL (Fin 3) K),
      A * GeneralLinearGroup.scalar (Fin 3) u = GeneralLinearGroup.scalar (Fin 3) u * A :=
    fun u A => (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar u A).eq
  have hζ1 : (ζ : K) ≠ 1 := by
    intro hζ1
    have hζ1' : ζ = 1 := Units.ext hζ1
    rw [hζ1', map_one, one_mul] at hζ
    have hc12 : y₁ * y₂ = y₂ * y₁ := by
      calc y₁ * y₂ = y₁ * y₂ * y₁⁻¹ * y₁ := by group
        _ = y₂ * y₁ := by rw [hζ]
    set N : Matrix (Fin 3) (Fin 3) K :=
      ((g₁⁻¹ * y₂ * g₁ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) with hN
    have hND : N * diagonal ![τ, τ ^ 2, 1] = diagonal ![τ, τ ^ 2, 1] * N := by
      have e1 : g₁⁻¹ * y₂ * g₁ * diagTau hτ = diagTau hτ * (g₁⁻¹ * y₂ * g₁) := by
        rw [← hg₁y]
        calc g₁⁻¹ * y₂ * g₁ * (g₁⁻¹ * y₁ * g₁) = g₁⁻¹ * (y₂ * y₁) * g₁ := by group
          _ = g₁⁻¹ * (y₁ * y₂) * g₁ := by rw [hc12]
          _ = g₁⁻¹ * y₁ * g₁ * (g₁⁻¹ * y₂ * g₁) := by group
      have := congrArg (fun x : GL (Fin 3) K => (x : Matrix (Fin 3) (Fin 3) K)) e1
      simp only [Units.val_mul (g₁⁻¹ * y₂ * g₁) (diagTau hτ),
        Units.val_mul (diagTau hτ) (g₁⁻¹ * y₂ * g₁), coe_diagTau_eq_diagonal] at this
      exact this
    have hNdiag := Sec16.ProofHess.eq_diagonal_of_commute hτ hτ1 hND
    have hN3 : N ^ 3 = 1 := by
      have h1 : (g₁⁻¹ * y₂ * g₁) ^ 3 = 1 := by
        rw [show g₁⁻¹ * y₂ * g₁ = g₁⁻¹ * y₂ * g₁⁻¹⁻¹ by rw [inv_inv], conj_pow, hy₂3]
        group
      rw [hN, ← Units.val_pow_eq_pow_val, h1, Units.val_one]
    have hcub : ∀ i, (N i i) ^ 3 = 1 := by
      intro i
      have h := congrFun (congrFun hN3 i) i
      rw [hNdiag, diagonal_pow, diagonal_apply_eq, Matrix.one_apply_eq] at h
      simpa using h
    have hdetN : N.det = 1 := by
      rw [hN, Units.val_mul, Units.val_mul, det_mul, det_mul, ((mem_slPi_iff hπ).mp hy₂).2,
        mul_one, ← det_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, det_one]
    have habc : N 0 0 * N 1 1 * N 2 2 = 1 := by
      have h := hdetN
      rw [hNdiag, det_diagonal, Fin.prod_univ_three] at h
      exact h
    obtain ⟨i, hi⟩ := Sec16.ProofHess.exists_eq_smul_pow_of_diag hτ hτ1 (hcub 0) (hcub 1) habc
    obtain ⟨c, hc⟩ : ∃ c : K, c = N 2 2 := ⟨_, rfl⟩
    have hNeq : N = c • (diagonal ![τ, τ ^ 2, 1]) ^ i := by
      rw [hc, ← hi, hNdiag]
      congr 1
      funext l
      fin_cases l <;> rfl
    have hy₂eq : (y₂ : Matrix (Fin 3) (Fin 3) K) =
        c • ((y₁ ^ i : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
      have h1 : (y₂ : Matrix (Fin 3) (Fin 3) K) =
          (g₁ : Matrix (Fin 3) (Fin 3) K) * N *
            ((g₁⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
        rw [hN, Units.val_mul, Units.val_mul, ← mul_assoc, ← mul_assoc, ← Units.val_mul,
          mul_inv_cancel, Units.val_one, one_mul, mul_assoc, ← Units.val_mul, mul_inv_cancel,
          Units.val_one, mul_one]
      have h2 : ((y₁ ^ i : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
          (g₁ : Matrix (Fin 3) (Fin 3) K) * (diagonal ![τ, τ ^ 2, 1]) ^ i *
            ((g₁⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
        have hy : y₁ = g₁ * diagTau hτ * g₁⁻¹ := by rw [← hg₁y]; group
        rw [hy, conj_pow, Units.val_mul, Units.val_mul, Units.val_pow_eq_pow_val,
          coe_diagTau_eq_diagonal]
      rw [h1, hNeq, h2, Matrix.mul_smul, Matrix.smul_mul]
    have hmk : ProjGenLinGroup.mk y₂ = ProjGenLinGroup.mk (y₁ ^ i) := mk_eq_of_coe_eq_smul hy₂eq
    apply he₂n
    have : e₂ = e₁ ^ i := by
      apply Subtype.ext
      rw [← hy₂e, hmk, map_pow, hy₁e, Subgroup.coe_pow]
    rw [this]
    exact pow_mem (Subgroup.mem_zpowers e₁) i
  have hD : g₁⁻¹ * (y₁ * 1) * g₁ = diagTau hτ := by rw [mul_one]; exact hg₁y
  have hζc : (ζ : K) = τ ∨ (ζ : K) = τ ^ 2 := by
    rcases eq_one_or_eq_tau_or_eq_tau_sq hτ hτ1 hζ3 with h | h | h
    · exact absurd h hζ1
    · exact Or.inl h
    · exact Or.inr h
  obtain ⟨g, hg, hgc, hgd⟩ : ∃ g ∈ glPi π 3 (p ^ f) K,
      (g⁻¹ * y₂ * g = cycThree ∨ g⁻¹ * y₂⁻¹ * g = cycThree) ∧ g⁻¹ * (y₁ * 1) * g = diagTau hτ := by
    rcases hζc with h | h
    · obtain ⟨g, hg, hgc, hgd⟩ := exists_heis_normal_form hK hq hτ hτ1 hy₂ hg₁ (one_mem _) hD h hζ
      exact ⟨g, hg, Or.inl hgc, hgd⟩
    · have hζ' : y₁ * y₂⁻¹ * y₁⁻¹ = GeneralLinearGroup.scalar (Fin 3) ζ⁻¹ * y₂⁻¹ := by
        calc y₁ * y₂⁻¹ * y₁⁻¹ = (y₁ * y₂ * y₁⁻¹)⁻¹ := by group
          _ = (GeneralLinearGroup.scalar (Fin 3) ζ * y₂)⁻¹ := by rw [hζ]
          _ = y₂⁻¹ * GeneralLinearGroup.scalar (Fin 3) ζ⁻¹ := by rw [_root_.mul_inv_rev, map_inv]
          _ = _ := by rw [hsc]
      have hτζ : ((ζ⁻¹ : Kˣ) : K) = τ := by
        rw [Units.val_inv_eq_inv_val, h]
        exact inv_eq_of_mul_eq_one_right (by rw [← pow_succ, hτ])
      obtain ⟨g, hg, hgc, hgd⟩ :=
        exists_heis_normal_form hK hq hτ hτ1 (inv_mem hy₂) hg₁ (one_mem _) hD hτζ hζ'
      exact ⟨g, hg, Or.inr hgc, hgd⟩
  rw [mul_one] at hgd
  refine ⟨g, hg, ?_⟩
  set γ := conjM' hπ hg with hγ
  have hγd : γ dM = e₁ := by
    apply Subtype.ext
    rw [coe_conjM', hdM, ← map_inv, ← map_mul, ← map_mul, ← hy₁e, ← hgd]
    congr 1
    group
  have hγc : γ cM = e₂ ∨ γ cM = e₂⁻¹ := by
    rcases hgc with h | h
    · left
      apply Subtype.ext
      rw [coe_conjM', hcM, ← map_inv, ← map_mul, ← map_mul, ← hy₂e, ← h]
      congr 1
      group
    · right
      apply Subtype.ext
      rw [coe_conjM', hcM, ← map_inv, ← map_mul, ← map_mul, Subgroup.coe_inv, ← hy₂e, ← map_inv,
        ← h]
      congr 1
      group
  have ho₁ : orderOf e₁ = 3 :=
    orderOf_eq_prime (hEe.2 e₁ he₁) he₁1
  have ho₂ : orderOf e₂ = 3 :=
    orderOf_eq_prime (hEe.2 e₂ he₂) he₂1
  rw [eq_sup_zpowers_of_card_nine hE9 he₁ he₂ ho₂ he₂n hcomm ho₁, Subgroup.map_sup,
    MonoidHom.map_zpowers, MonoidHom.map_zpowers]
  change Subgroup.zpowers e₁ ⊔ Subgroup.zpowers e₂ = Subgroup.zpowers (γ dM) ⊔
    Subgroup.zpowers (γ cM)
  rw [hγd]
  rcases hγc with h | h
  · rw [h]
  · rw [h, Subgroup.zpowers_inv]

theorem exists_hessian_equiv {X : Type} [Group X] [Finite X] {p e : ℕ} [Fact p.Prime]
    (he : 1 ≤ e) (hiso : Sec4.IsoLThreePi X p e) {E : Subgroup X}
    (hEe : CFSG.Assembly.IsElemAbelian 3 E) (hE9 : Nat.card E = 9)
    (htr : ∀ y₀ ∈ E, y₀ ≠ 1 → ∀ y₁ ∈ E, y₁ ≠ 1 →
      ∃ w ∈ Subgroup.normalizer (E : Set X), w * y₀ * w⁻¹ = y₁) :
    ∃ (π : Bool) (K : Type) (_ : Field K), PiField π p e K ∧ ModThree π (p ^ e) ∧
      ∃ (τ : K) (hτ : τ ^ 3 = 1), τ ≠ 1 ∧ ∃ dM cM : projImage (slPi π 3 (p ^ e) K),
        (dM : ProjGenLinGroup (Fin 3) K) = ProjGenLinGroup.mk (diagTau hτ) ∧
        (cM : ProjGenLinGroup (Fin 3) K) = ProjGenLinGroup.mk (cycThree : GL (Fin 3) K) ∧
        dM * cM = cM * dM ∧ orderOf dM = 3 ∧ orderOf cM = 3 ∧ cM ∉ Subgroup.zpowers dM ∧
        ∃ Φ : projImage (slPi π 3 (p ^ e) K) ≃* X,
          (Subgroup.zpowers dM ⊔ Subgroup.zpowers cM).map Φ.toMonoidHom = E := by
  obtain ⟨π, K, _, hK, hq, ⟨ψ⟩⟩ := Sec13.exists_projImage_model he hiso
  have hπ : π = false → UnitaryFieldData p e K := fun h => by subst h; exact hK.unitary
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  obtain ⟨dM, cM, hdM, hcM, hdc, hdo, hco, hcd⟩ :=
    Sec19.Step1915WProof.exists_heisPair hK hq hτ hτ1
  have := hK.finite
  have : Finite (ProjGenLinGroup (Fin 3) K) := by
    unfold ProjGenLinGroup
    infer_instance
  have hEψ : CFSG.Assembly.IsElemAbelian 3 (E.map ψ.toMonoidHom) :=
    CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_map 3 ψ.toMonoidHom E hEe
  have hEψ9 : Nat.card (E.map ψ.toMonoidHom) = 9 := by
    rw [Subgroup.card_map_of_injective ψ.injective, hE9]
  have htrψ : ∀ y₀ ∈ E.map ψ.toMonoidHom, y₀ ≠ 1 → ∀ y₁ ∈ E.map ψ.toMonoidHom, y₁ ≠ 1 →
      ∃ w ∈ Subgroup.normalizer ((E.map ψ.toMonoidHom : Subgroup _) : Set _),
        w * y₀ * w⁻¹ = y₁ := by
    rintro _ ⟨y₀, hy₀, rfl⟩ hy₀1 _ ⟨y₁, hy₁, rfl⟩ hy₁1
    have hy₀1' : y₀ ≠ 1 := fun h => hy₀1 (by rw [h, map_one])
    have hy₁1' : y₁ ≠ 1 := fun h => hy₁1 (by rw [h, map_one])
    obtain ⟨w, hw, hwy⟩ := htr y₀ hy₀ hy₀1' y₁ hy₁ hy₁1'
    refine ⟨ψ w, ?_, ?_⟩
    · rw [← Subgroup.map_equiv_normalizer_eq]
      exact ⟨w, hw, rfl⟩
    · change ψ w * ψ y₀ * (ψ w)⁻¹ = ψ y₁
      rw [← map_inv, ← map_mul, ← map_mul, hwy]
  obtain ⟨g, hg, hgE⟩ := exists_conjM'_of_transitive hK hq hπ hτ hτ1 hdM hcM hEψ hEψ9 htrψ
  refine ⟨π, K, inferInstance, hK, hq, τ, hτ, hτ1, dM, cM, hdM, hcM, hdc, hdo, hco, hcd,
    (conjM' hπ hg).trans ψ.symm, ?_⟩
  have h1 : (Subgroup.zpowers dM ⊔ Subgroup.zpowers cM).map
      ((conjM' hπ hg).trans ψ.symm).toMonoidHom =
      ((Subgroup.zpowers dM ⊔ Subgroup.zpowers cM).map (conjM' hπ hg).toMonoidHom).map
        ψ.symm.toMonoidHom := by
    rw [Subgroup.map_map]
    rfl
  rw [h1, ← hgE, Subgroup.map_map]
  have h2 : ψ.symm.toMonoidHom.comp ψ.toMonoidHom = MonoidHom.id X :=
    MonoidHom.ext fun x => ψ.symm_apply_apply x
  rw [h2, Subgroup.map_id]

theorem le_thetaC_of_transitive {X : Type} [Group X] [Finite X] {p e : ℕ} [Fact p.Prime]
    (he : 1 ≤ e) (hp3 : 3 < p) (hiso : Sec4.IsoLThreePi X p e) {E : Subgroup X}
    (hEe : CFSG.Assembly.IsElemAbelian 3 E) (hE9 : Nat.card E = 9)
    (htr : ∀ y₀ ∈ E, y₀ ≠ 1 → ∀ y₁ ∈ E, y₁ ≠ 1 →
      ∃ w ∈ Subgroup.normalizer (E : Set X), w * y₀ * w⁻¹ = y₁)
    {Y : Subgroup X} (hY3 : ¬ 3 ∣ Nat.card Y) (hEY : E ≤ Subgroup.normalizer (Y : Set X)) :
    ∃ x ∈ E, x ≠ 1 ∧ Y ≤ thetaC x := by
  obtain ⟨π, K, _, hK, hq, τ, hτ, hτ1, dM, cM, hdM, hcM, hdc, hdo, hco, hcd, Φ, hΦE⟩ :=
    exists_hessian_equiv he hiso hEe hE9 htr
  have hp2 : p ≠ 2 := by omega
  have := hK.finite
  have : Finite (ProjGenLinGroup (Fin 3) K) := by
    unfold ProjGenLinGroup
    infer_instance
  set Ê := Subgroup.zpowers dM ⊔ Subgroup.zpowers cM with hÊ
  have hΦE' : ∀ w ∈ Ê, Φ w ∈ E := fun w hw => hΦE ▸ ⟨w, hw, rfl⟩
  set Y' := Y.map Φ.symm.toMonoidHom with hY'
  have hY'3 : ¬ 3 ∣ Nat.card Y' := by
    rw [hY', Subgroup.card_map_of_injective Φ.symm.injective]
    exact hY3
  have hÊY' : Ê ≤ Subgroup.normalizer (Y' : Set (projImage (slPi π 3 (p ^ e) K))) := by
    intro w hw
    refine Subgroup.mem_normalizer_fintype fun x hx => ?_
    obtain ⟨y, hy, rfl⟩ := hx
    refine ⟨Φ w * y * (Φ w)⁻¹, (Subgroup.mem_normalizer_iff.mp (hEY (hΦE' w hw)) y).mp hy, ?_⟩
    change Φ.symm (Φ w * y * (Φ w)⁻¹) = w * Φ.symm y * w⁻¹
    rw [map_mul, map_mul, map_inv, MulEquiv.symm_apply_apply]
  obtain ⟨b, hbÊ, hb1, hY'b⟩ := le_thetaC_model hK hp2 hτ hτ1 hq hdM hcM hdc hdo hco hcd hY'3
    hÊY'
  refine ⟨Φ b, hΦE' b hbÊ, fun h => hb1 (Φ.injective (by rw [h, map_one])), fun y hy => ?_⟩
  have h1 : Φ.symm y ∈ thetaC b := hY'b ⟨y, hy, rfl⟩
  have h2 : Φ (Φ.symm y) ∈ (thetaC b).map Φ.toMonoidHom := ⟨_, h1, rfl⟩
  rw [thetaC_map_equiv, MulEquiv.apply_symm_apply] at h2
  exact h2

theorem autCent_of_transitive {X : Type} [Group X] [Finite X] {p : ℕ} [Fact p.Prime]
    (hp3 : 3 < p) (hiso : Sec4.IsoLThreePi X p 1) {E : Subgroup X}
    (hEe : CFSG.Assembly.IsElemAbelian 3 E) (hE9 : Nat.card E = 9)
    (htr : ∀ y₀ ∈ E, y₀ ≠ 1 → ∀ y₁ ∈ E, y₁ ≠ 1 →
      ∃ w ∈ Subgroup.normalizer (E : Set X), w * y₀ * w⁻¹ = y₁)
    (α : MulAut X) (hα : ∀ b ∈ E, α b = b) : ∃ b ∈ E, α = MulAut.conj b := by
  obtain ⟨π, K, _, hK, hq, τ, hτ, hτ1, dM, cM, hdM, hcM, -, -, -, -, Φ, hΦE⟩ :=
    exists_hessian_equiv le_rfl hiso hEe hE9 htr
  set Ê := Subgroup.zpowers dM ⊔ Subgroup.zpowers cM with hÊ
  have hΦE' : ∀ w ∈ Ê, Φ w ∈ E := fun w hw => hΦE ▸ ⟨w, hw, rfl⟩
  set β := (Φ.trans α).trans Φ.symm with hβ
  have hfix : ∀ w ∈ Ê, β w = w := by
    intro w hw
    rw [hβ, MulEquiv.trans_apply, MulEquiv.trans_apply, hα _ (hΦE' w hw),
      MulEquiv.symm_apply_apply]
  obtain ⟨m, j, hmj⟩ := autCent_projImage hK hq hp3 hτ hτ1 hdM hcM β
    (hfix dM (Subgroup.mem_sup_left (Subgroup.mem_zpowers dM)))
    (hfix cM (Subgroup.mem_sup_right (Subgroup.mem_zpowers cM)))
  refine ⟨Φ (dM ^ m * cM ^ j), hΦE' _ (mul_mem (pow_mem (Subgroup.mem_sup_left
    (Subgroup.mem_zpowers dM)) m) (pow_mem (Subgroup.mem_sup_right (Subgroup.mem_zpowers cM)) j)),
    ?_⟩
  exact eq_conj_of_transport Φ α hmj

end CFSG.RankThree.PartTwo.Sec14.Res8Hess
