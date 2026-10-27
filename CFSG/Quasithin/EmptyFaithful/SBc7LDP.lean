module

public import CFSG.Quasithin.EmptyFaithful.SBc7Hyp
public import CFSG.Quasithin.EmptyFaithful.SBc7Cent
public import CFSG.Quasithin.EmptyFaithful.SBd5Perf

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

namespace SBc7

section Data

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}

theorem case12_data (c : Ctx15331 T Mc M V₁ V₂ Yp I L t) (hout : Outcome31 T V₁ I L)
    (hcase : IsC134Case 1 I (Sgp153 T V₁) L ∨ IsC134Case 2 I (Sgp153 T V₁) L) :
    ∃ (k : ℕ) (F : Type) (_ : Field F) (_ : Fintype F)
      (α : ↥L →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F))
      (β : ↥(c134Q I L) →* Multiplicative (Fin k → Fin 3 → F)),
      0 < k ∧ Fintype.card F = 2 ∧ Function.Surjective α ∧ α.ker = CFSG.pCore 2 ↥L ∧
        Function.Surjective β ∧ β.ker = ⊥ ∧ L ≤ Subgroup.normalizer (c134Q I L : Set G) ∧
        ∀ (a : ↥L) (u v : ↥(c134Q I L)), (v : G) = a * u * a⁻¹ → ∀ i : Fin k,
          Multiplicative.toAdd (β v) i =
            ((α a : Matrix.GeneralLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec
              (Multiplicative.toAdd (β u) i) := by
  obtain ⟨k, hk, n, F, hF, hFin, α, hcard, hmod, hsum⟩ : ∃ k : ℕ, (k = 1 ∨ k = 2) ∧ ∃ (n : ℕ)
      (F : Type) (_ : Field F) (_ : Fintype F)
      (α : ↥L →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F)),
      Fintype.card F = 2 ^ n ∧ IsModO2Surj L α ∧
      IsSumOfNaturalModulesVia L (c134Q I L) ⊥ α false k := by
    rcases hcase with h1 | h2
    · change IsC134Case1 I (Sgp153 T V₁) L at h1
      obtain ⟨-, n, F, hF, hFin, hcard, hsec⟩ := h1
      obtain ⟨α, hα, hαk, hsum⟩ :=
        (isNaturalSection_iff_isSumOfNaturalModules_one _ _ bot_le).1 hsec
      exact ⟨1, Or.inl rfl, n, F, hF, hFin, α, hcard, ⟨hα, hαk⟩, hsum⟩
    · change IsC134Case2 I (Sgp153 T V₁) L at h2
      obtain ⟨⟨n, F, hF, hFin, α, hcard, hmod, hsum⟩, -⟩ := h2
      exact ⟨2, Or.inr rfl, n, F, hF, hFin, α, hcard, hmod, hsum⟩
  have hF2 : Fintype.card F = 2 := card_field_eq_two c hout hcard hmod
  obtain ⟨hLQ, -, β, hβs, hβk, hβe⟩ := hsum
  refine ⟨k, F, hF, hFin, α, β, ?_, hF2, hmod.1, hmod.2, hβs, ?_, hLQ, fun a u v h i => ?_⟩
  · rcases hk with rfl | rfl <;> norm_num
  · rw [hβk, Subgroup.bot_subgroupOf]
  · simpa [moduleAct] using hβe a u v h i

end Data


section Main

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}

theorem exists_three_element (c : Ctx15330 T Mc M V₁ V₂ Yp I L t) :
    ∃ y ∈ Yp, y ∉ pCoreOf 2 L ∧ ∃ j : ℕ, orderOf y = 3 ^ j := by
  have c25 : Ctx15325L T Mc M V₁ V₂ Yp I L t := c.toCtx15328.toCtx15327.toCtx15325L
  have hF : Facts15325 T Mc M V₁ V₂ Yp I := c25.facts
  by_contra h
  apply not_Yp_le_pCoreOf c
  rw [hF.yp_eq]
  unfold oPrimeResidualOf
  refine (Subgroup.closure_le _).2 fun x hx => ?_
  by_contra hxn
  obtain ⟨⟨hxM, hxI⟩, j, hj⟩ := hx
  apply h
  refine ⟨x, ?_, hxn, j, hj⟩
  rw [hF.yp_eq]
  unfold oPrimeResidualOf
  exact Subgroup.subset_closure ⟨⟨hxM, hxI⟩, j, hj⟩

theorem commutator_centralizer_le_pCoreOf (c : Ctx15331 T Mc M V₁ V₂ Yp I L t)
    (hout : Outcome31 T V₁ I L)
    (hcase : IsC134Case 1 I (Sgp153 T V₁) L ∨ IsC134Case 2 I (Sgp153 T V₁) L) :
    ⁅L, I ⊓ Subgroup.centralizer (Yp : Set G)⁆ ≤ pCoreOf 2 L := by
  obtain ⟨k, F, hFfield, hFin, α, β, hk, hF2, hαs, hαk, hβs, hβk, hLQ, hβe⟩ :=
    case12_data c hout hcase
  have c25 : Ctx15325L T Mc M V₁ V₂ Yp I L t := c.toCtx15328.toCtx15327.toCtx15325L
  have hsyl : IsSylowTwoOf (Sgp153 T V₁) I := c25.facts.sylow
  have hLc : L ∈ cComp I := S153D.mem_cComp_of_mem_cComp_thompsonJ c25.conc.1
  have hLI : L ≤ I := le_of_mem_cComp hLc
  have hIL : I ≤ Subgroup.normalizer (L : Set G) := c.c27.normal
  have hYL : Yp ≤ L := c.c27.Yp_le
  have hβi : Function.Injective β := (MonoidHom.ker_eq_bot_iff β).1 hβk
  let act : ↥L → Matrix (Fin 3) (Fin 3) F := fun l =>
    ((α l : Matrix.GeneralLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)
  have hsurj : ∀ g : Matrix.SpecialLinearGroup (Fin 3) F, ∃ l : ↥L,
      act l = (g : Matrix (Fin 3) (Fin 3) F) := SBd5.act_surj hαs
  let α' : ↥L →* Matrix.SpecialLinearGroup (Fin 3) F :=
    (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 F).symm.toMonoidHom.comp α
  have hα'mat : ∀ l : ↥L, ((α' l : Matrix.SpecialLinearGroup (Fin 3) F) :
      Matrix (Fin 3) (Fin 3) F) = act l := fun l => by
    have h : α l = CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 F (α' l) := by
      simp [α']
    show _ = ((α l : Matrix.GeneralLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)
    rw [h]
    rfl
  have hα's : Function.Surjective α' := fun g => by
    obtain ⟨l, hl⟩ := hαs (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 F g)
    exact ⟨l, by simp [α', hl]⟩
  have hα'k : ∀ l : ↥L, α' l = 1 ↔ (l : G) ∈ pCoreOf 2 L := fun l => by
    constructor
    · intro h
      have h1 : α l = 1 := by
        have := congrArg (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 F) h
        simpa [α'] using this
      have h2 : l ∈ α.ker := h1
      rw [hαk] at h2
      exact (AppC.mem_pCore_iff_mem_blockQ l).1 h2
    · intro h
      have h2 : l ∈ CFSG.pCore 2 ↥L := (AppC.mem_pCore_iff_mem_blockQ l).2 h
      rw [← hαk] at h2
      have h1 : α l = 1 := h2
      simp [α', h1]
  have hIQ : I ≤ Subgroup.normalizer (c134Q I L : Set G) := fun x hx =>
    SBd5.mem_normalizer_commutator_of (le_normalizer_pCoreOf 2 I hx) (hIL hx)
  have hQsyl : IsSylowTwoOf (Sgp153 T V₁ ⊓ L) L := B6.isSylowTwoOf_inf_normal hsyl hLI hIL
  have hSN : Sgp153 T V₁ ≤ Subgroup.normalizer (Yp : Set G) := Sgp_le_normalizer_Yp c.toCtx15330
  let Ybar : Subgroup (Matrix.SpecialLinearGroup (Fin 3) F) := (Yp.subgroupOf L).map α'
  let Tbar : Subgroup (Matrix.SpecialLinearGroup (Fin 3) F) :=
    ((Sgp153 T V₁ ⊓ L).subgroupOf L).map α'
  have hTbar : IsSylowTwoOf Tbar ⊤ :=
    SBc5.isSylowTwoOf_map_surjective α' hα's (SBc5.isSylowTwoOf_subgroupOf_top hQsyl)
  have hN : ∀ τ ∈ Tbar, ∀ y ∈ Ybar, τ * y * τ⁻¹ ∈ Ybar := by
    rintro _ ⟨s, hs, rfl⟩ _ ⟨y, hy, rfl⟩
    refine ⟨s * y * s⁻¹, ?_, by simp⟩
    show (s : G) * (y : G) * (s : G)⁻¹ ∈ Yp
    exact (Subgroup.mem_normalizer_iff.mp (hSN hs.1) (y : G)).mp hy
  obtain ⟨y₁, hy₁Y, hy₁n, j, hj⟩ := exists_three_element c.toCtx15330
  have hy₁L : y₁ ∈ L := hYL hy₁Y
  set σ : Matrix.SpecialLinearGroup (Fin 3) F := α' ⟨y₁, hy₁L⟩ with hσdef
  have hσY : σ ∈ Ybar := ⟨⟨y₁, hy₁L⟩, hy₁Y, rfl⟩
  have hσ1 : σ ≠ 1 := fun h => hy₁n ((hα'k _).1 h)
  have hσ3 : σ ^ 3 = 1 := by
    have h1 : σ ^ (3 ^ j) = 1 := by
      have : (⟨y₁, hy₁L⟩ : ↥L) ^ (3 ^ j) = 1 := by
        apply Subtype.ext
        rw [← hj]
        exact pow_orderOf_eq_one y₁
      rw [hσdef, ← map_pow, this, map_one]
    have hF2' : Nat.card F = 2 ^ 1 := by rw [Nat.card_eq_fintype_card, hF2]; norm_num
    have hcard : Nat.card (Matrix.SpecialLinearGroup (Fin 3) F) = 168 := by
      rw [card_SL3_eq hF2']
      norm_num
    have h2 : orderOf σ ∣ 3 ^ j := orderOf_dvd_of_pow_eq_one h1
    have h3 : orderOf σ ∣ 168 := hcard ▸ orderOf_dvd_natCard σ
    obtain ⟨i, hi, hio⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 h2
    have hi1 : i ≤ 1 := by
      by_contra hcon
      have : 3 ^ 2 ∣ 3 ^ i := Nat.pow_dvd_pow 3 (by omega)
      rw [← hio] at this
      have := this.trans h3
      omega
    have : orderOf σ ∣ 3 := by
      rw [hio]
      interval_cases i <;> simp
    exact orderOf_dvd_iff_pow_eq_one.1 this
  rw [Subgroup.commutator_le]
  intro l hl d hd
  have hdI : d ∈ I := hd.1
  have hdY : d ∈ Subgroup.centralizer (Yp : Set G) := hd.2
  have hker : ∀ (u : ↥(c134Q I L)) (hu : d * u * d⁻¹ ∈ c134Q I L),
      β ⟨d * u * d⁻¹, hu⟩ = 1 ↔ β u = 1 := by
    intro u hu
    constructor
    · intro h
      have h1 : (⟨d * u * d⁻¹, hu⟩ : ↥(c134Q I L)) = 1 := hβi (by rw [h, map_one])
      have h2 : d * (u : G) * d⁻¹ = 1 := congrArg Subtype.val h1
      have h3 : (u : G) = 1 := by
        have := congrArg (fun z => d⁻¹ * z * d) h2
        simpa [mul_assoc] using this
      have : u = 1 := Subtype.ext h3
      rw [this, map_one]
    · intro h
      have h1 : u = 1 := hβi (by rw [h, map_one])
      have : (⟨d * u * d⁻¹, hu⟩ : ↥(c134Q I L)) = 1 := by
        apply Subtype.ext
        simp [h1]
      rw [this, map_one]
  obtain ⟨A, hA⟩ := SBd6.twist_matrix hF2 hk act hsurj β hβs hLQ hβe (hIQ hdI) (hIL hdI) hker
  have hAcent : ∀ y ∈ Ybar, y * A = A * y := by
    rintro _ ⟨y, hy, rfl⟩
    have hyd : d * (y : G) * d⁻¹ = (y : G) := by
      have := Subgroup.mem_centralizer_iff.mp hdY (y : G) hy
      calc d * (y : G) * d⁻¹ = ((y : G) * d) * d⁻¹ := by rw [this]
        _ = (y : G) := by group
    have hl' : d * ((y : ↥L) : G) * d⁻¹ ∈ L := by rw [hyd]; exact y.2
    have h1 := hA y hl'
    have h2 : (⟨d * (y : G) * d⁻¹, hl'⟩ : ↥L) = y := Subtype.ext hyd
    rw [h2] at h1
    apply Subtype.ext
    simpa [Matrix.SpecialLinearGroup.coe_mul, hα'mat] using h1
  have hA1 : A = 1 := eq_one_of_centralizes hF2 hTbar hN hσY hσ3 hσ1 hAcent
  have hl' : d * l * d⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp (hIL hdI) l).mp hl
  have h3 := hA ⟨l, hl⟩ hl'
  rw [hA1] at h3
  have h4 : α' ⟨d * l * d⁻¹, hl'⟩ = α' ⟨l, hl⟩ := by
    apply Subtype.ext
    simpa [hα'mat] using h3
  have h5 : α' (⟨d * l * d⁻¹, hl'⟩ * (⟨l, hl⟩ : ↥L)⁻¹) = 1 := by
    rw [map_mul, map_inv, h4, mul_inv_cancel]
  have h6 : d * l * d⁻¹ * l⁻¹ ∈ pCoreOf 2 L := (hα'k _).1 h5
  have h7 : ⁅l, d⁆ = (d * l * d⁻¹ * l⁻¹)⁻¹ := by
    rw [commutatorElement_def]
    group
  rw [h7]
  exact (pCoreOf 2 L).inv_mem h6

end Main

end SBc7

end CFSG.Quasithin
