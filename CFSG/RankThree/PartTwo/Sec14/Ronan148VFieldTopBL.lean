module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148VFieldTopB
import CFSG.RankThree.PartTwo.Sec4.Ronan148VLinFpf
import CFSG.RankThree.PartTwo.Sec4.Ronan148VElation
public import CFSG.RankThree.PartTwo.Sec14.Ronan148VFieldTopA
import CFSG.RankThree.PartTwo.Sec4.Ronan148VLinB

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148V

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.RankThree.PartTwo.Sec4 (diagTau cycThree diagUnits)
open scoped commutatorElement

theorem exists_twist_of_model {X : Type} [Group X] [Finite X] {J K E : Subgroup X} {σ z : X}
    {P : Type} [Group P] (hσN : σ ∈ Subgroup.normalizer (J : Set X))
    (hKC : K ≤ Subgroup.centralizer ({σ} : Set X)) (hEJ : E ≤ J)
    (hEC : E ≤ Subgroup.centralizer ({σ} : Set X)) (hEc : IsMulCommutative ↥E) (hz : z ∈ E)
    (ψ : ↥J ≃* P) (θ : MulAut P)
    (hψ : ∀ y : ↥J, ψ (J.normalizerMonoidHom ⟨σ, hσN⟩ y) = θ (ψ y))
    (A : Subgroup P) (hA3 : ¬ 3 ∣ Nat.card A) (hAθ : ∀ a ∈ A, θ a ∈ A)
    (hAE : ∀ e (he : e ∈ E), ∀ a ∈ A, ψ ⟨e, hEJ he⟩ * a * (ψ ⟨e, hEJ he⟩)⁻¹ ∈ A)
    (hfpf : ∀ a ∈ A, a * ψ ⟨z, hEJ hz⟩ = ψ ⟨z, hEJ hz⟩ * a → a = 1)
    (hne : ∃ u ∈ A, u ≠ 1 ∧ θ (ψ ⟨z, hEJ hz⟩ * u * (ψ ⟨z, hEJ hz⟩)⁻¹) = u) :
    ∃ V : Subgroup X, V ≤ J ⊓ Subgroup.centralizer ({σ * z} : Set X) ∧ ¬ 3 ∣ Nat.card V ∧
      Subgroup.zpowers σ ⊔ E ≤ Subgroup.normalizer (V : Set X) ∧
      ¬ ⁅V, Subgroup.zpowers σ ⊔ E⁆ ≤ K := by
  set α := J.normalizerMonoidHom ⟨σ, hσN⟩ with hα
  have hαapp : ∀ x : ↥J, ((α x : ↥J) : X) = σ * x * σ⁻¹ := fun x =>
    Sec4.normalizerMonoidHom_apply_coe hσN x
  set A' : Subgroup X := (A.comap ψ.toMonoidHom).map J.subtype with hA'
  have hmem : ∀ x : ↥J, (x : X) ∈ A' ↔ ψ x ∈ A := by
    intro x
    constructor
    · rintro ⟨y, hy, hyx⟩
      have : y = x := Subtype.ext hyx
      rw [← this]
      exact hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  have hA'J : A' ≤ J := Subgroup.map_subtype_le _
  set zJ : ↥J := ⟨z, hEJ hz⟩ with hzJ
  refine exists_twist_of_fpf hKC hz hEC hEc hA'J ?_ ?_ ?_ ?_
  · rw [hA', Subgroup.card_map_of_injective J.subtype_injective]
    exact fun h => hA3 (h.trans (Subgroup.card_comap_dvd_of_injective A ψ.toMonoidHom
      ψ.injective))
  · have hnorm : ∀ g : X,
        (∀ x : ↥J, ψ x ∈ A → ∃ hg : g * x * g⁻¹ ∈ J, ψ ⟨g * x * g⁻¹, hg⟩ ∈ A) →
        g ∈ Subgroup.normalizer (A' : Set X) := by
      intro g hg
      apply Subgroup.mem_normalizer_fintype
      intro h hh
      have hhJ : h ∈ J := hA'J hh
      obtain ⟨hgJ, hgA⟩ := hg ⟨h, hhJ⟩ ((hmem ⟨h, hhJ⟩).mp hh)
      exact (hmem ⟨_, hgJ⟩).mpr hgA
    refine sup_le (Subgroup.zpowers_le.mpr (hnorm σ fun x hx => ⟨(α x).2, ?_⟩)) fun e he =>
      hnorm e fun x hx => ⟨J.mul_mem (J.mul_mem (hEJ he) x.2) (J.inv_mem (hEJ he)), ?_⟩
    · have : (⟨σ * x * σ⁻¹, (α x).2⟩ : ↥J) = α x := Subtype.ext (hαapp x).symm
      rw [this, hψ]
      exact hAθ _ hx
    · have : (⟨e * x * e⁻¹, J.mul_mem (J.mul_mem (hEJ he) x.2) (J.inv_mem (hEJ he))⟩ : ↥J) =
          ⟨e, hEJ he⟩ * x * (⟨e, hEJ he⟩ : ↥J)⁻¹ := rfl
      rw [this, map_mul, map_mul, map_inv]
      exact hAE e he _ hx
  · intro a ha hac
    have haJ : a ∈ J := hA'J ha
    have h1 := hfpf _ ((hmem ⟨a, haJ⟩).mp ha) (by
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext hac)
    have : (⟨a, haJ⟩ : ↥J) = 1 := ψ.injective (h1.trans (map_one ψ).symm)
    exact congrArg Subtype.val this
  · obtain ⟨u, huA, hu1, hufix⟩ := hne
    obtain ⟨uJ, rfl⟩ := ψ.surjective u
    refine ⟨uJ, (hmem uJ).mpr huA, fun h => hu1 (by rw [show uJ = 1 from Subtype.ext h, map_one]),
      ?_⟩
    have h1 : α (zJ * uJ * zJ⁻¹) = uJ := by
      apply ψ.injective
      rw [hψ, map_mul ψ, map_mul ψ, map_inv ψ]
      exact hufix
    have h2 := congrArg Subtype.val h1
    rw [hαapp, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv] at h2
    have h3 : σ * (z * (uJ : X) * z⁻¹) * σ⁻¹ = uJ := h2
    calc (uJ : X) * (σ * z) = σ * (z * uJ * z⁻¹) * σ⁻¹ * (σ * z) := by rw [h3]
      _ = σ * z * uJ := by group

section Certificates


theorem exists_twist_of_odd_linear {X : Type} [Group X] [Finite X] {J K E R : Subgroup X}
    {σ z : X} {n : ℕ} (hn : 1 ≤ n) (hJ : Sec4.IsoLThreePi ↥J 2 (3 * n))
    (hq : 2 ^ (3 * n) % 3 = 1) (hind : KFacts.InducesStdKind J σ .field) (hσ3 : σ ^ 3 = 1)
    (hKJ : K ≤ J) (hKC : K ≤ Subgroup.centralizer ({σ} : Set X))
    (hK : Sec4.IsoLThreePi ↥K 2 n) (hEJ : E ≤ J) (hEC : E ≤ Subgroup.centralizer ({σ} : Set X))
    (hEc : IsMulCommutative ↥E) (hE3 : ∀ x ∈ E, x ^ 3 = 1) (hz : z ∈ E) (hz1 : z ≠ 1)
    (hodd : ¬ 2 ∣ Nat.card ↥(J ⊓ Subgroup.centralizer ({z} : Set X)))
    (hRK : R ≤ K ⊓ Subgroup.centralizer ({z} : Set X)) (hR3 : ¬ 3 ∣ Nat.card R)
    (hRN : Subgroup.zpowers σ ⊔ E ≤ Subgroup.normalizer (R : Set X))
    (hRc : R = ⁅R, Subgroup.zpowers σ ⊔ E⁆) (hR1 : R ≠ ⊥) :
    ∃ V : Subgroup X, V ≤ J ⊓ Subgroup.centralizer ({σ * z} : Set X) ∧ ¬ 3 ∣ Nat.card V ∧
      Subgroup.zpowers σ ⊔ E ≤ Subgroup.normalizer (V : Set X) ∧
      ¬ ⁅V, Subgroup.zpowers σ ⊔ E⁆ ≤ K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hσN : σ ∈ Subgroup.normalizer (J : Set X) := KFacts.InducesStdKind.mem_normalizer hind
  obtain ⟨χ, ρ, hρ, hχ⟩ := exists_fieldAut_model_linear hn hJ hq hind hσ3 hσN hKJ hKC hK
  set F := GaloisField 2 (3 * n) with hFdef
  have hF : Nat.card F = 2 ^ (3 * n) := GaloisField.card 2 (3 * n) (by omega)
  set α := J.normalizerMonoidHom ⟨σ, hσN⟩ with hα
  have hαapp : ∀ x : ↥J, ((α x : ↥J) : X) = σ * x * σ⁻¹ := fun x =>
    Sec4.normalizerMonoidHom_apply_coe hσN x
  have hzσ : z * σ = σ * z := Subgroup.mem_centralizer_singleton_iff.mp (hEC hz)
  have hEcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hEc.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hcommJ : ∀ a b : ↥J, (a : X) * b = b * a → χ a * χ b = χ b * χ a := by
    intro a b hab
    rw [← map_mul, ← map_mul]
    exact congrArg χ (Subtype.ext hab)
  have hαfix : ∀ y : ↥J, (y : X) * σ = σ * y → α y = y := by
    intro y hy
    apply Subtype.ext
    rw [hαapp, ← hy, mul_inv_cancel_right]
  have hRJ : R ≤ J := (hRK.trans inf_le_left).trans hKJ
  have hsc : ∀ (u : Fˣ) (A : GL (Fin 3) F),
      A * GeneralLinearGroup.scalar (Fin 3) u = GeneralLinearGroup.scalar (Fin 3) u * A :=
    fun u A => (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar u A).eq
  set zJ : ↥J := ⟨z, hEJ hz⟩ with hzJ
  have hz3' : χ zJ ^ 3 = 1 := by
    rw [← map_pow]
    have : zJ ^ 3 = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact hE3 z hz)
    rw [this, map_one]
  have hz1' : χ zJ ≠ 1 := by
    intro h1
    apply hz1
    have : zJ = 1 := χ.injective (h1.trans (map_one χ).symm)
    exact congrArg Subtype.val this
  have hinv : ∀ t : projectiveSL 3 F, t ^ 2 = 1 → t * χ zJ = χ zJ * t → t = 1 := by
    intro t ht2 htz
    obtain ⟨tJ, rfl⟩ := χ.surjective t
    have htJ2 : tJ ^ 2 = 1 := χ.injective (by rw [map_pow, ht2, map_one])
    have htJz : (tJ : X) * z = z * tJ := by
      have h1 : tJ * zJ = zJ * tJ := χ.injective (by rw [map_mul, map_mul, htz])
      exact congrArg Subtype.val h1
    by_contra h1
    apply hodd
    have hmem : (tJ : X) ∈ J ⊓ Subgroup.centralizer ({z} : Set X) :=
      ⟨tJ.2, Subgroup.mem_centralizer_singleton_iff.mpr htJz⟩
    have ho : orderOf (⟨tJ, hmem⟩ : ↥(J ⊓ Subgroup.centralizer ({z} : Set X))) = 2 := by
      apply orderOf_eq_prime
      · apply Subtype.ext
        have := congrArg Subtype.val htJ2
        simpa using this
      · intro h2
        apply h1
        have : (tJ : X) = 1 := congrArg Subtype.val h2
        rw [show tJ = 1 from Subtype.ext this, map_one]
    rw [← ho]
    exact orderOf_dvd_natCard _
  obtain ⟨Z, hZ, hT1⟩ := Sec4.Ronan148V.exists_type1_lift hn hF hq hz3' hz1' hinv
  obtain ⟨τ, hτ, hτ1, ζ, hζ, g, -, hD⟩ := hT1
  have hK' : Sec4.PiField true 2 (3 * n) F := ⟨Nat.prime_two, by omega, hF⟩
  have hqt : Sec4.ModThree true (2 ^ (3 * n)) := hq
  obtain ⟨ξ, -, rfl⟩ := Sec4.exists_scalar_of_mem_zPi hK' hqt hτ hτ1 hζ
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    norm_num at hτ
  have hρ3 := Sec4.Ronan148V.apply_apply_apply_of_orderOf_eq_three hρ
  have hρτ : ρ τ = τ := by
    have h3 : (ρ τ) ^ 3 = 1 := by rw [← map_pow, hτ, map_one]
    rcases Sec4.eq_one_or_eq_tau_or_eq_tau_sq hτ hτ1 h3 with h | h | h
    · exfalso
      apply hτ1
      apply ρ.injective
      rw [h, map_one]
    · exact h
    · exfalso
      have h4 : τ ^ 4 = τ := by rw [show 4 = 3 + 1 by rfl, pow_add, hτ, one_mul, pow_one]
      have h2 : ρ (ρ τ) = τ := by
        rw [h, map_pow, h, ← pow_mul]
        exact h4
      have h5 := hρ3 τ
      rw [h2, h] at h5
      apply hτ1
      have : τ * (τ - 1) = 0 := by linear_combination h5
      exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hτ0)
  set Zg := Matrix.SpecialLinearGroup.toGL Z with hZg
  set τu := Units.mk0 τ hτ0 with hτu
  have hτu3 : τu ^ 3 = 1 := Units.ext (by
    rw [Units.val_pow_eq_pow_val, hτu, Units.val_mk0, hτ, Units.val_one])
  obtain ⟨x, hxE, X', hX', hZX⟩ : ∃ (x : X) (hxE : x ∈ E), ∃ X' : SpecialLinearGroup (Fin 3) F,
      proj 3 F X' = χ ⟨x, hEJ hxE⟩ ∧
      Zg * Matrix.SpecialLinearGroup.toGL X' * Zg⁻¹ =
        GeneralLinearGroup.scalar (Fin 3) τu * Matrix.SpecialLinearGroup.toGL X' := by
    by_contra hno
    push Not at hno
    have hEdiag : ∀ e (he : e ∈ E), ∀ e' : SpecialLinearGroup (Fin 3) F,
        proj 3 F e' = χ ⟨e, hEJ he⟩ → ∃ a b c : Fˣ,
          g⁻¹ * Matrix.SpecialLinearGroup.toGL e' * g = diagUnits a b c := by
      intro e he e' he'
      have hcomm : proj 3 F e' * proj 3 F Z = proj 3 F Z * proj 3 F e' := by
        rw [he', hZ]
        exact hcommJ _ _ (hEcomm e he z hz)
      obtain ⟨k, hk, ν, hν, hconj, a, b, c, habc⟩ :=
        Sec4.Ronan148V.exists_cycThree_pow_mul_of_commute hτ hτ1 ⟨ξ, rfl⟩ hD hcomm
      have h1 := Sec4.Ronan148V.conj_eq_inv_scalar_mul hconj
      rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2) with rfl | rfl | rfl
      · exact ⟨a, b, c, by rw [habc, pow_zero, one_mul]⟩
      · exfalso
        have hν' : ν = τu ^ 2 := Units.ext (by
          rw [hν, Units.val_pow_eq_pow_val, hτu, Units.val_mk0])
        have hi : (τu ^ 2)⁻¹ = τu := inv_eq_of_mul_eq_one_right (by rw [← pow_succ, hτu3])
        apply hno e he e' he'
        rw [h1, hν', hi]
      · exfalso
        have hν' : ν = τu := Units.ext (by
          rw [hν, hτu, Units.val_mk0]
          calc τ ^ (2 * 2) = τ ^ 3 * τ := by ring
            _ = τ := by rw [hτ, one_mul])
        rw [hν'] at h1
        apply hno e⁻¹ (E.inv_mem he) e'⁻¹ (by rw [map_inv, he', ← map_inv]; rfl)
        rw [map_inv]
        calc Zg * (Matrix.SpecialLinearGroup.toGL e')⁻¹ * Zg⁻¹ =
            (Zg * Matrix.SpecialLinearGroup.toGL e' * Zg⁻¹)⁻¹ := by group
          _ = (GeneralLinearGroup.scalar (Fin 3) τu⁻¹ * Matrix.SpecialLinearGroup.toGL e')⁻¹ := by
            rw [h1]
          _ = GeneralLinearGroup.scalar (Fin 3) τu * (Matrix.SpecialLinearGroup.toGL e')⁻¹ := by
            rw [_root_.mul_inv_rev, map_inv, inv_inv, hsc]
    have hcop : Nat.Coprime (Nat.card R) 3 :=
      Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hR3)
    have hcent : Subgroup.zpowers σ ⊔ E ≤ Subgroup.centralizer (R : Set X) := by
      refine sup_le (Subgroup.zpowers_le.mpr ?_) fun e he => ?_
      · rw [Subgroup.mem_centralizer_iff]
        intro r hr
        exact Subgroup.mem_centralizer_singleton_iff.mp (hKC (hRK hr).1)
      · rw [Subgroup.mem_centralizer_iff]
        intro r hr
        obtain ⟨e', he'⟩ := proj_surjective 3 F (χ ⟨e, hEJ he⟩)
        obtain ⟨r', hr'⟩ := proj_surjective 3 F (χ ⟨r, hRJ hr⟩)
        obtain ⟨a, b, c, h1⟩ := hEdiag e he e' he'
        have hrZ : proj 3 F r' * proj 3 F Z = proj 3 F Z * proj 3 F r' := by
          rw [hr', hZ]
          exact hcommJ _ _ (Subgroup.mem_centralizer_singleton_iff.mp (hRK hr).2)
        have hrM : proj 3 F r' ^ Nat.card R = 1 := by
          rw [hr', ← map_pow]
          have : (⟨r, hRJ hr⟩ : ↥J) ^ Nat.card R = 1 := by
            apply Subtype.ext
            have h := congrArg Subtype.val (pow_card_eq_one' (G := R) (x := ⟨r, hr⟩))
            rw [SubmonoidClass.coe_pow] at h
            rw [Subgroup.coe_pow]
            exact h
          rw [this, map_one]
        obtain ⟨a', b', c', h2⟩ :=
          Sec4.Ronan148V.exists_diagUnits_of_commute hτ hτ1 ⟨ξ, rfl⟩ hD hrZ hcop hrM
        have h3 := Sec4.Ronan148V.commute_of_conj_diagUnits h2 h1
        have h4 : r' * e' = e' * r' := by
          apply Subtype.ext
          rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
          have := congrArg (fun A : GL (Fin 3) F => (A : Matrix (Fin 3) (Fin 3) F)) h3
          simp only [Units.val_mul] at this
          exact this
        have h5 : χ ⟨r, hRJ hr⟩ * χ ⟨e, hEJ he⟩ = χ ⟨e, hEJ he⟩ * χ ⟨r, hRJ hr⟩ := by
          rw [← hr', ← he', ← map_mul, h4, map_mul]
        have h6 : (⟨r, hRJ hr⟩ : ↥J) * ⟨e, hEJ he⟩ = ⟨e, hEJ he⟩ * ⟨r, hRJ hr⟩ :=
          χ.injective (by rw [map_mul, map_mul]; exact h5)
        exact congrArg Subtype.val h6
    have hbot : ⁅R, Subgroup.zpowers σ ⊔ E⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.le_centralizer_iff]
      exact hcent
    exact hR1 (by rw [hRc, hbot])
  have hy₂ : Matrix.SpecialLinearGroup.toGL X' ∈ Sec4.slPi true 3 (2 ^ (3 * n)) F :=
    (Sec4.mem_slPi_true _).mpr (Matrix.SpecialLinearGroup.det_coe X')
  obtain ⟨g₂, -, hg₂c, hg₂d⟩ := Sec4.exists_heis_normal_form hK' hqt hτ hτ1 hy₂
    (Sec4.mem_glPi_true _ g) ⟨ξ, rfl⟩ hD (ζ := τu) (Units.val_mk0 hτ0) hZX
  set χ₁ : ↥J ≃* projectiveSL 3 F := χ.trans (conjAut 3 F g₂⁻¹) with hχ₁
  set h₀ : GL (Fin 3) F := g₂⁻¹ * GeneralLinearGroup.map (ρ : F →+* F) g₂ with hh₀
  have hχ₁app : ∀ y, χ₁ y = conjAut 3 F g₂⁻¹ (χ y) := fun y => rfl
  have hscal : ∀ (u : Fˣ) (A : GL (Fin 3) F),
      conjAut 3 F (A * GeneralLinearGroup.scalar (Fin 3) u) = conjAut 3 F A := by
    intro u A
    rw [map_mul, conjAut_scalar, mul_one]
  have e1 : g₂⁻¹ * (Zg * GeneralLinearGroup.scalar (Fin 3) ξ) * g₂ =
      (g₂⁻¹ * Zg * g₂) * GeneralLinearGroup.scalar (Fin 3) ξ := by
    calc g₂⁻¹ * (Zg * GeneralLinearGroup.scalar (Fin 3) ξ) * g₂ =
        g₂⁻¹ * Zg * (GeneralLinearGroup.scalar (Fin 3) ξ * g₂) := by group
      _ = g₂⁻¹ * Zg * (g₂ * GeneralLinearGroup.scalar (Fin 3) ξ) := by rw [← hsc ξ g₂]
      _ = _ := by group
  have hcz : MulAut.conj (χ₁ zJ) = conjAut 3 F (diagTau hτ) := by
    rw [hχ₁app, ← hZ, Sec4.Ronan148V.conj_conjAut_proj, inv_inv, ← hg₂d, e1, hscal]
  set xJ : ↥J := ⟨x, hEJ hxE⟩ with hxJ
  have hcx : MulAut.conj (χ₁ xJ) = conjAut 3 F cycThree := by
    rw [hχ₁app, ← hX', Sec4.Ronan148V.conj_conjAut_proj, inv_inv, hg₂c]
  have hθ : ∀ y : ↥J, χ₁ (α y) = conjAut 3 F h₀ (fieldAut 3 F ρ (χ₁ y)) := by
    intro y
    have e : conjAut 3 F h₀ * fieldAut 3 F ρ =
        conjAut 3 F g₂⁻¹ * fieldAut 3 F ρ * conjAut 3 F g₂ := by
      rw [hh₀, map_mul, mul_assoc, mul_assoc, fieldAut_mul_conjAut]
    have e2 : χ y = conjAut 3 F g₂ (χ₁ y) := by
      rw [hχ₁app, ← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]
    rw [hχ₁app, hχ, e2]
    exact (congrArg (fun φ : MulAut (projectiveSL 3 F) => φ (χ₁ y)) e).symm
  have hxσ : x * σ = σ * x := Subgroup.mem_centralizer_singleton_iff.mp (hEC hxE)
  have hcomm_of : ∀ (y : ↥J) (M : GL (Fin 3) F), (y : X) * σ = σ * y →
      MulAut.conj (χ₁ y) = conjAut 3 F M →
      GeneralLinearGroup.map (ρ : F →+* F) M = M →
      conjAut 3 F h₀ * conjAut 3 F M = conjAut 3 F M * conjAut 3 F h₀ := by
    intro y M hyσ hyM hMρ
    have hθy : conjAut 3 F h₀ (fieldAut 3 F ρ (χ₁ y)) = χ₁ y := by rw [← hθ, hαfix y hyσ]
    have h1 := Sec4.Ronan148V.mul_conj_eq_conj_mul (conjAut 3 F h₀ * fieldAut 3 F ρ) (χ₁ y)
    rw [MulAut.mul_apply, hθy, hyM] at h1
    have hfM := Sec4.Ronan148V.fieldAut_mul_conjAut_of_map_eq ρ hMρ
    have h2 : conjAut 3 F h₀ * conjAut 3 F M * fieldAut 3 F ρ =
        conjAut 3 F M * conjAut 3 F h₀ * fieldAut 3 F ρ := by
      rw [mul_assoc, ← hfM, ← mul_assoc, h1, mul_assoc]
    exact mul_right_cancel h2
  have hHd := hcomm_of zJ (diagTau hτ) hzσ hcz (Sec4.Ronan148V.map_diagTau hτ ρ hρτ)
  have hHc := hcomm_of xJ cycThree hxσ hcx (Sec4.Ronan148V.map_cycThree ρ)
  set RP : Subgroup (projectiveSL 3 F) := (R.subgroupOf J).map χ₁.toMonoidHom with hRP
  have hmemRP : ∀ p, p ∈ RP → ∃ y : ↥J, (y : X) ∈ R ∧ χ₁ y = p := by
    rintro p ⟨y, hy, rfl⟩
    exact ⟨y, hy, rfl⟩
  have hRP3 : ¬ 3 ∣ Nat.card RP := by
    rw [hRP, Subgroup.card_map_of_injective χ₁.injective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRJ).toEquiv]
    exact hR3
  have hRP1 : RP ≠ ⊥ := by
    intro hbot
    apply hR1
    rw [eq_bot_iff]
    intro r hr
    have hmem : χ₁ ⟨r, hRJ hr⟩ ∈ RP := ⟨⟨r, hRJ hr⟩, hr, rfl⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    have h1 : (⟨r, hRJ hr⟩ : ↥J) = 1 := χ₁.injective (hmem.trans (map_one χ₁).symm)
    rw [Subgroup.mem_bot]
    exact congrArg Subtype.val h1
  have hRPd : ∀ p ∈ RP, conjAut 3 F (diagTau hτ) p = p := by
    intro p hp
    obtain ⟨y, hy, rfl⟩ := hmemRP p hp
    rw [← hcz, MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    have hyz : (y : X) * z = z * y := Subgroup.mem_centralizer_singleton_iff.mp (hRK hy).2
    change z * (y : X) * z⁻¹ = y
    rw [← hyz, mul_inv_cancel_right]
  have hRPθ : ∀ p ∈ RP, conjAut 3 F h₀ (fieldAut 3 F ρ p) = p := by
    intro p hp
    obtain ⟨y, hy, rfl⟩ := hmemRP p hp
    rw [← hθ, hαfix y (Subgroup.mem_centralizer_singleton_iff.mp (hKC (hRK hy).1))]
  have hRPc : ∀ p ∈ RP, conjAut 3 F cycThree p ∈ RP := by
    intro p hp
    obtain ⟨y, hy, rfl⟩ := hmemRP p hp
    rw [← hcx, MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul]
    refine ⟨xJ * y * xJ⁻¹, ?_, rfl⟩
    change x * (y : X) * x⁻¹ ∈ R
    exact (Subgroup.mem_normalizer_iff.mp (hRN (Subgroup.mem_sup_right hxE)) y).mp hy
  obtain ⟨A, hA3, hAθ, hAM, hAfpf, u, huA, hu1, hufix⟩ :=
    Sec4.Ronan148V.exists_fpf_subgroup hτ hτ1 hn hF hq hρ hρτ hHd hHc RP hRP3 hRP1 hRPd hRPθ
      hRPc
  refine exists_twist_of_model hσN hKC hEJ hEC hEc hz χ₁ (conjAut 3 F h₀ * fieldAut 3 F ρ) hθ A
    hA3 hAθ ?_ ?_ ⟨u, huA, hu1, ?_⟩
  · intro e he a ha
    obtain ⟨e', he'⟩ := proj_surjective 3 F (χ₁ ⟨e, hEJ he⟩)
    have hconj : MulAut.conj (χ₁ ⟨e, hEJ he⟩) =
        conjAut 3 F (Matrix.SpecialLinearGroup.toGL e') := by
      rw [← he', Sec4.Ronan148V.conjAut_toGL]
    have hc : ∀ y : ↥J, (y : X) ∈ E → MulAut.conj (χ₁ ⟨e, hEJ he⟩) * MulAut.conj (χ₁ y) =
        MulAut.conj (χ₁ y) * MulAut.conj (χ₁ ⟨e, hEJ he⟩) := by
      intro y hy
      rw [← map_mul, ← map_mul, ← map_mul, ← map_mul]
      congr 2
      apply Subtype.ext
      exact hEcomm e he y hy
    have hcd := hc zJ hz
    have hcc := hc xJ hxE
    rw [hcz, hconj] at hcd
    rw [hcx, hconj] at hcc
    have := hAM _ hcd hcc a ha
    rw [← hconj, MulAut.conj_apply] at this
    exact this
  · intro a ha hac
    apply hAfpf a ha
    rw [← hcz, MulAut.conj_apply, ← hac, mul_inv_cancel_right]
  · rw [← MulAut.conj_apply, hcz]
    exact hufix

theorem kf148FieldTopTwistROdd_of_oddU (h : KF148FieldTopTwistROddU) :
    KF148FieldTopTwistROdd := by
  intro X _ _ J K E σ n hn hJ hind hσ3 hKJ hKC hKs hK hEJ hEC hEc hE3 z hz hz1 hodd R hRK hR3
    hRN hRc hR1
  have h0 : 2 ^ (3 * n) % 3 ≠ 0 := by
    intro h0
    have h3 : 3 ∣ 2 ^ (3 * n) := Nat.dvd_of_mod_eq_zero h0
    have := Nat.prime_three.dvd_of_dvd_pow h3
    norm_num at this
  rcases (by omega : 2 ^ (3 * n) % 3 = 1 ∨ 2 ^ (3 * n) % 3 = 2) with hq | hq
  · exact exists_twist_of_odd_linear hn hJ hq hind hσ3 hKJ hKC hK hEJ hEC hEc hE3 hz hz1 hodd hRK
      hR3 hRN hRc hR1
  · exact h X J K E σ n hn hJ hind hσ3 hKJ hKC hKs hK hEJ hEC hEc hE3 z hz hz1 hodd hq R hRK hR3
      hRN hRc hR1

theorem kf148FieldTopTwistR_of_oddU (h : KF148FieldTopTwistROddU) :
    KF148FieldTopTwistR :=
  kf148FieldTopTwistR_of_odd (kf148FieldTopTwistROdd_of_oddU h)

end Certificates

end CFSG.RankThree.PartTwo.Sec14.Ronan148V
