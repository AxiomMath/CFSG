module

public import CFSG.RankThree.PartOne.S11c.Sec66PSU
public import CFSG.RankThree.PartOne.CTP.StdCenter
public import CFSG.RankThree.PartOne.S12.AmbientTransport
public import CFSG.RankThree.PartOne.S12.Equivariance

public section

namespace CFSG.RankThree.PartOne.CTP

open Matrix CFSG CFSG.RankThree.PartOne CFSG.RankThree.PartOne.Sec66T
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)

theorem exists_descent {f : ℕ} {F : Type} [Field F] (hF : UnitaryFieldData 2 f F)
    (hgcd : Nat.gcd 3 (2 ^ f + 1) = 1) (hq : ¬(3 = 3 ∧ 2 ^ f = 2))
    (a₀ : MulAut (primeFormP hF ((1 : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)))
    (ha5 : a₀ ^ 5 = 1)
    (hnin : a₀ ∉ innerAut (primeFormP hF ((1 : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F))) :
    ∃ (σ : F ≃+* F) (θ : MulAut (primeFormP hF ((1 : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F))),
      orderOf σ = 5 ∧
      θ⁻¹ * a₀ * θ = primeFormFieldHom hF (isPrimeFormGram_one (n := 3)) σ := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hC1 : IsPrimeFormGram (1 : GL (Fin 3) F) := isPrimeFormGram_one
  have hn3 : 3 ≤ 3 := le_refl 3
  set σ := primeFormFieldFactor hF hC1 hn3 hq a₀ with hσ
  have hσp : σ ^ 5 = 1 := by rw [hσ, ← map_pow, ha5, map_one]
  have hσ1 : σ ≠ 1 := by
    intro hσ1
    apply hnin
    have hαD : a₀ ∈ primeFormD hF ((1 : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
      rw [← ker_primeFormFieldFactor hF hC1 hn3 hq]
      exact hσ1
    exact mem_innerAut_of_mem_D hF hn3 hq Nat.prime_five (by rw [hgcd]; norm_num) hαD ha5
  have hσord : orderOf σ = 5 := orderOf_eq_prime hσp hσ1
  have hord : orderOf a₀ = 5 := by
    refine orderOf_eq_prime ha5 ?_
    intro h1
    apply hσ1
    rw [hσ, h1, map_one]
  obtain ⟨-, -, -, -, -, M, hMconj⟩ :=
    CFSG.RankThree.UnitaryDescent.unitary_prime_semilinear_field_descent hF hn3 hq
      Nat.prime_five (by norm_num) (by norm_num) a₀ hord σ rfl hσord
  exact ⟨σ, primeFormConjHom hF ((1 : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) M, hσord,
    hMconj⟩

theorem even_of_five_dvd {f : ℕ} (h : 5 ∣ 2 ^ f + 1) : Even f := by
  have h4 : 2 ^ f % 5 = 4 := by omega
  have hmod : 2 ^ f % 5 = 2 ^ (f % 4) % 5 := by
    conv_lhs => rw [← Nat.div_add_mod f 4, pow_add, pow_mul, Nat.mul_mod, Nat.pow_mod]
    norm_num
  have h2 : f % 4 = 2 := by
    have hlt : f % 4 < 4 := Nat.mod_lt _ (by norm_num)
    interval_cases hr : f % 4 <;> simp_all
  exact ⟨f / 2, by omega⟩

section SU

variable {f : ℕ} {F : Type} [Field F] (hF : UnitaryFieldData 2 f F)

theorem normOneScalars_one_eq_bot (hgcd : Nat.gcd 3 (2 ^ f + 1) = 1) :
    normOneScalars hF (gramSU hF ((1 : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) 3 = ⊥ := by
  rw [← Subgroup.card_eq_one, CFSG.RankThree.Classical.card_normOneScalars_one hF (by norm_num),
    hgcd]

@[expose] noncomputable def suEquivP (hgcd : Nat.gcd 3 (2 ^ f + 1) = 1) :
    gramSU hF ((1 : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) ≃*
      primeFormP hF ((1 : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) :=
  MulEquiv.ofBijective (QuotientGroup.mk' _)
    ⟨by
      rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk']
      exact normOneScalars_one_eq_bot hF hgcd, QuotientGroup.mk'_surjective _⟩

theorem suEquivP_apply (hgcd : Nat.gcd 3 (2 ^ f + 1) = 1)
    (g : gramSU hF ((1 : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) :
    suEquivP hF hgcd g = (g : primeFormP hF ((1 : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) :=
  rfl

theorem suEquivP_field (hgcd : Nat.gcd 3 (2 ^ f + 1) = 1) (φ : F ≃+* F)
    (g : gramSU hF ((1 : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) :
    suEquivP hF hgcd (primeFormFieldSU hF (isPrimeFormGram_one (n := 3)) φ g) =
      primeFormFieldHom hF (isPrimeFormGram_one (n := 3)) φ (suEquivP hF hgcd g) :=
  (primeFormFieldAut_mk hF (isPrimeFormGram_one (n := 3)) φ g).symm

end SU

section PreStd

variable {G : Type} [Group G]

structure PreStd (c : G) (f₀ : ℕ) (I : Subgroup G) where
  F : Type
  [fld : Field F]
  [fin : Finite F]
  hF : UnitaryFieldData 2 (5 * f₀) F
  σ : F ≃+* F
  σ_order : orderOf σ = 5
  Ψ : ↥I →* GL (Fin 3) F
  Ψ_inj : Function.Injective Ψ
  Ψ_range : Ψ.range = unitarySU 2 (5 * f₀) F 3
  Ψ_c : ∀ (x : ↥I) (hx : c * (x : G) * c⁻¹ ∈ I), Ψ ⟨c * x * c⁻¹, hx⟩ = glAut σ (Ψ x)

attribute [instance] PreStd.fld PreStd.fin

theorem exists_preStd [Finite G]
    (hGA : CFSG.Open.GriessAllModelsStatement)
    {c : G} {f₀ : ℕ} {I : Subgroup G} (hdvd5 : 5 ∣ 2 ^ f₀ + 1)
    (hmodel : StatedClassicalModel (I ⧸ Subgroup.center I) .PSU 3 2 (5 * f₀))
    (hperf : Group.IsPerfect I) (hc : c ∈ Subgroup.normalizer (I : Set G)) (hc5 : c ^ 5 = 1)
    (hout : c ∉ I ⊔ Subgroup.centralizer (I : Set G)) : Nonempty (PreStd c f₀ I) := by
  have hfe : Even f₀ := even_of_five_dvd hdvd5
  have hQe : Even (5 * f₀) := hfe.mul_left 5
  have hZ : Subgroup.center I = ⊥ := psuThree_center_trivial hGA hQe hperf hmodel
  have hIm : StatedClassicalModel I .PSU 3 2 (5 * f₀) :=
    statedClassicalModel_of_equiv
      ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot) hmodel
  obtain ⟨F, _, _, hF, -, hq, ⟨eI⟩⟩ := psu_prime_form_model hIm
  have hgcd : Nat.gcd 3 (2 ^ (5 * f₀) + 1) = 1 := coprime_three_two_pow_add_one hQe
  set a₀ : MulAut (primeFormP hF ((1 : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) :=
    MulAut.congr eI (conjAut I c hc) with ha₀
  have hca5 : conjAut I c hc ^ 5 = 1 := by
    unfold conjAut
    rw [← map_pow]
    have : (⟨c, hc⟩ : Subgroup.normalizer (I : Set G)) ^ 5 = 1 := Subtype.ext (by simpa using hc5)
    rw [this, map_one]
  have ha5 : a₀ ^ 5 = 1 := by
    rw [ha₀, ← map_pow, hca5, map_one]
  have hnin : a₀ ∉ innerAut (primeFormP hF ((1 : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) := by
    intro h
    rw [ha₀, mem_innerAut_congr] at h
    obtain ⟨y, hy⟩ := h
    apply hout
    have hyx : ∀ x : ↥I, (y : G) * x * (y : G)⁻¹ = c * x * c⁻¹ := fun x => by
      have := congrArg (fun φ : MulAut ↥I => ((φ x : ↥I) : G)) hy
      simpa [MulAut.conj_apply, Equivariance.coe_conjAut hc] using this
    have hz : (y : G)⁻¹ * c ∈ Subgroup.centralizer (I : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have h1 := hyx ⟨x, hx⟩
      have h2 : (y : G)⁻¹ * c * x = x * ((y : G)⁻¹ * c) := by
        have h3 : c * x = (y : G) * x * (y : G)⁻¹ * c := by
          rw [h1]
          group
        calc (y : G)⁻¹ * c * x = (y : G)⁻¹ * (c * x) := by group
          _ = (y : G)⁻¹ * ((y : G) * x * (y : G)⁻¹ * c) := by rw [h3]
          _ = x * ((y : G)⁻¹ * c) := by group
      exact h2.symm
    have hc' : c = (y : G) * ((y : G)⁻¹ * c) := by group
    rw [hc']
    exact mul_mem (Subgroup.mem_sup_left y.2) (Subgroup.mem_sup_right hz)
  obtain ⟨σ, θ, hσ, hθ⟩ := exists_descent hF hgcd hq a₀ ha5 hnin
  let eI₁ : ↥I ≃* primeFormP hF ((1 : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) :=
    eI.trans θ.symm
  have hkey : ∀ x : ↥I, eI₁ (conjAut I c hc x) =
      primeFormFieldHom hF (isPrimeFormGram_one (n := 3)) σ (eI₁ x) := by
    intro x
    rw [← hθ]
    show θ.symm (eI (conjAut I c hc x)) = θ.symm (a₀ (θ (θ.symm (eI x))))
    rw [MulEquiv.apply_symm_apply, ha₀, MulAut.congr_apply]
    simp
  let φ : ↥I ≃* gramSU hF ((1 : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) :=
    eI₁.trans (suEquivP hF hgcd).symm
  refine ⟨⟨F, hF, σ, hσ, (gramSU hF ((1 : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)).subtype.comp
    φ.toMonoidHom, ?_, ?_, ?_⟩⟩
  · exact Subtype.val_injective.comp φ.injective
  · ext g
    constructor
    · rintro ⟨x, rfl⟩
      rw [unitarySU_eq_gramSU hF 3]
      exact (φ x).2
    · intro hg
      rw [unitarySU_eq_gramSU hF 3] at hg
      exact ⟨φ.symm ⟨g, hg⟩, by simp⟩
  · intro x hx
    have hxe : (⟨c * (x : G) * c⁻¹, hx⟩ : ↥I) = conjAut I c hc x :=
      Subtype.ext (Equivariance.coe_conjAut hc x).symm
    have h1 : φ ⟨c * (x : G) * c⁻¹, hx⟩ =
        primeFormFieldSU hF (isPrimeFormGram_one (n := 3)) σ (φ x) := by
      apply (suEquivP hF hgcd).injective
      rw [suEquivP_field, hxe]
      show (suEquivP hF hgcd) ((suEquivP hF hgcd).symm (eI₁ (conjAut I c hc x))) = _
      rw [MulEquiv.apply_symm_apply, hkey]
      show _ = primeFormFieldHom hF (isPrimeFormGram_one (n := 3)) σ
        ((suEquivP hF hgcd) ((suEquivP hF hgcd).symm (eI₁ x)))
      rw [MulEquiv.apply_symm_apply]
    show ((φ ⟨c * (x : G) * c⁻¹, hx⟩ : gramSU hF _) : GL (Fin 3) F) = glAut σ (φ x : GL (Fin 3) F)
    rw [h1]
    rfl

end PreStd

end CFSG.RankThree.PartOne.CTP
