module

public import CFSG.Quasithin.Vol2.Ch8Sec2L828TSixB2
public import CFSG.Quasithin.Vol2.Ch8Sec2L828TSixLem
public import CFSG.Quasithin.Vol2.Ch8Sec2L828TStep3Final
public import CFSG.Quasithin.Vol2.Ch8Sec2L828TSixB1

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.E3 CFSG.Quasithin.H
open CFSG.Quasithin.H13.L828T
open scoped IsMulCommutative commutatorElement

section SixB3

variable {G : Type} [Group G] [Finite G]

theorem s828_reflection {I P : Subgroup G} [(P.subgroupOf I).Normal]
    (e : ↥I ⧸ P.subgroupOf I ≃* DihedralGroup 5) {v : ↥I} (hvP : (v : G) ∉ P)
    (hv2 : (v : G) ^ 2 = 1) : ∃ b : ZMod 5, e (QuotientGroup.mk v) = DihedralGroup.sr b := by
  classical
  have hvsq : (e (QuotientGroup.mk v)) ^ 2 = 1 := by
    have h1 : v ^ 2 = 1 := Subtype.ext (by simpa using hv2)
    rw [← map_pow, ← QuotientGroup.mk_pow, h1]
    simp
  rcases hd : e (QuotientGroup.mk v) with a | b
  · exfalso
    rw [hd, pow_two, DihedralGroup.r_mul_r, DihedralGroup.one_def] at hvsq
    have ha : a + a = 0 := DihedralGroup.r.inj hvsq
    have key : ∀ a : ZMod 5, a + a = 0 → a = 0 := by decide
    have ha0 : a = 0 := key a ha
    rw [ha0] at hd
    have h1 : e (QuotientGroup.mk v) = 1 := by rw [hd]; rfl
    have h2 : (QuotientGroup.mk v : ↥I ⧸ P.subgroupOf I) = 1 := (e.map_eq_one_iff).mp h1
    exact hvP (Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff v).mp h2))
  · exact ⟨b, rfl⟩

theorem s828_eps_diag {E : Type*} [AddCommGroup E] {K : Type} [Field K] [Finite K]
    (hK4 : Nat.card K = 4) (Γ : Set (AddMonoid.End E)) (κ : Subring.centralizer Γ ≃+* K)
    {X : Type*} [Group X] (ρ : X →* AddMonoid.End (E × E))
    (hρ : ∀ x, ∀ γ ∈ Γ, ρ x * diagEnd γ = diagEnd γ * ρ x) {y v : X} (hy5 : y ^ 5 = 1)
    (hy1 : ρ y ≠ 1) (hvy : ρ (v * y * v⁻¹ * y) = 1) :
    ∃ τ : K, τ ^ 2 + τ + 1 = 0 ∧
      ρ y + ρ y⁻¹ = diagEnd ((κ.symm τ : Subring.centralizer Γ) : AddMonoid.End E) := by
  obtain ⟨f, hf1, hf2⟩ := exists_hom_gl2' Γ K κ ρ hρ
  have hfy1 : f y ≠ 1 := fun h => hy1 ((hf1 y).mp h)
  have hfy5 : (f y) ^ 5 = 1 := by rw [← map_pow, hy5, map_one]
  have hs : f v * f y * (f v)⁻¹ = (f y)⁻¹ := by
    have h1 : f (v * y * v⁻¹ * y) = 1 := (hf1 _).mpr hvy
    rw [map_mul, map_mul, map_mul, map_inv] at h1
    exact eq_inv_of_mul_eq_one_left h1
  obtain ⟨τ, hτ, hmat⟩ := L828SixLem.gl2_trace_five hK4 (f y) (f v) hfy5 hfy1 hs
  refine ⟨τ, hτ, ?_⟩
  refine eq_diag_of_matrix_scalar Γ K κ ρ hρ f hf2 (x := y) (x' := y⁻¹) ?_
  rw [map_inv]
  exact hmat

theorem comm_add_of_conj_pm {R : Type*} [Ring R] {u u' b b' : R} (huu : u * u' = 1)
    (huu' : u' * u = 1) (hbb : b * b' = 1) (hb'b : b' * b = 1)
    (h : u * b * u' * b' = 1 ∨ u * b * u' * b = 1) : u * (b + b') = (b + b') * u := by
  have hc12 : (u * b * u') * (u * b' * u') = 1 := by
    calc (u * b * u') * (u * b' * u') = u * b * (u' * u) * b' * u' := by simp only [mul_assoc]
      _ = u * (b * b') * u' := by rw [huu', mul_one]; simp only [mul_assoc]
      _ = 1 := by rw [hbb, mul_one, huu]
  have hsum : u * (b + b') * u' = b + b' := by
    rw [mul_add, add_mul]
    rcases h with h | h
    · have e1 : u * b * u' = b := by
        calc u * b * u' = u * b * u' * (b' * b) := by rw [hb'b, mul_one]
          _ = (u * b * u' * b') * b := by simp only [mul_assoc]
          _ = b := by rw [h, one_mul]
      have e2 : u * b' * u' = b' := by
        calc u * b' * u' = (b' * b) * (u * b' * u') := by rw [hb'b, one_mul]
          _ = b' * (b * (u * b' * u')) := by simp only [mul_assoc]
          _ = b' * ((u * b * u') * (u * b' * u')) := by rw [e1]
          _ = b' := by rw [hc12, mul_one]
      rw [e1, e2]
    · have e1 : u * b * u' = b' := by
        calc u * b * u' = u * b * u' * (b * b') := by rw [hbb, mul_one]
          _ = (u * b * u' * b) * b' := by simp only [mul_assoc]
          _ = b' := by rw [h, one_mul]
      have e2 : u * b' * u' = b := by
        calc u * b' * u' = (b * b') * (u * b' * u') := by rw [hbb, one_mul]
          _ = b * (b' * (u * b' * u')) := by simp only [mul_assoc]
          _ = b * ((u * b * u') * (u * b' * u')) := by rw [e1]
          _ = b := by rw [hc12, mul_one]
      rw [e1, e2, add_comm]
  calc u * (b + b') = u * (b + b') * (u' * u) := by rw [huu', mul_one]
    _ = (u * (b + b') * u') * u := by simp only [mul_assoc]
    _ = (b + b') * u := by rw [hsum]

theorem scalar_contra' {R D : Type*} [Ring R] [Field D] (d : D →+* R) (hd : Function.Injective d)
    (hchar : (2 : D) = 0) (ζ τ : D) (hζ3 : ζ ^ 3 = 1) (hζ1 : ζ ≠ 1) (hτ : τ ^ 2 + τ + 1 = 0)
    (t t' : R) (htt1 : t * t' = 1) (htt2 : t' * t = 1) (h1 : t * d ζ = d (ζ ^ 2) * t)
    (h2 : t * d τ = d τ * t) : False := by
  have hinv : ζ⁻¹ = ζ ^ 2 := by
    refine inv_eq_of_mul_eq_one_right ?_
    rw [← pow_succ']
    exact hζ3
  refine L828SixLem.scalar_contra d hd hchar ζ τ hζ3 hζ1 hτ ⟨t, t', htt1, htt2⟩ ?_ ?_
  · show t * d ζ * t' = d ζ⁻¹
    rw [h1, hinv, mul_assoc, htt1, mul_one]
  · show t * d τ * t' = d τ
    rw [h2, mul_assoc, htt1, mul_one]

theorem s828_sixB_tau {T L I H : Subgroup G} {h : G} {k : ℕ} [IsMulCommutative ↥(fsuV T I)]
    (c : S828Ctx T L I H h k) {K : Type} [Field K] [Finite K] (hK4 : Nat.card K = 4)
    (κ : ↥(commutant ((ch82B (fsuV T I) h).subgroupOf (fsuV T I))
        ((ch82U (fsuV T I) h).subgroupOf (fsuV T I))
        ((autOn (ch82LU L (ch82U (fsuV T I) h)) (fsuV T I) : Subgroup (MulAut ↥(fsuV T I))) :
          Set (MulAut ↥(fsuV T I)))) ≃+* K)
    (eI : E2.StarQuot (fsuM T L ⊓ ch82I (fsuV T I) h) (ch82I (fsuV T I) h) ≃*
      DihedralGroup 5)
    (ρ : ↥(Subgroup.normalizer (pCoreOf 2 (ch82I (fsuV T I) h) : Set G) ⊓
          Subgroup.normalizer (ch82U (fsuV T I) h : Set G)) →*
        AddMonoid.End (QB (fsuV T I) (ch82B (fsuV T I) h) (ch82U (fsuV T I) h) ×
          QB (fsuV T I) (ch82B (fsuV T I) h) (ch82U (fsuV T I) h)))
    (hker : ∀ g : ↥(Subgroup.normalizer (pCoreOf 2 (ch82I (fsuV T I) h) : Set G) ⊓
          Subgroup.normalizer (ch82U (fsuV T I) h : Set G)),
        ρ g = 1 ↔ ∀ p ∈ pCoreOf 2 (ch82I (fsuV T I) h),
          (g : G) * p * (g : G)⁻¹ * p⁻¹ ∈ ch82U (fsuV T I) h)
    (hcomm : ∀ (i : ↥(Subgroup.normalizer (pCoreOf 2 (ch82I (fsuV T I) h) : Set G) ⊓
          Subgroup.normalizer (ch82U (fsuV T I) h : Set G)))
          (_ : (i : G) ∈ ch82I (fsuV T I) h)
          (γ : AddMonoid.End (QMod ((ch82B (fsuV T I) h).subgroupOf (fsuV T I))
            ((ch82U (fsuV T I) h).subgroupOf (fsuV T I)))),
        γ ∈ indSet ((ch82B (fsuV T I) h).subgroupOf (fsuV T I))
          ((ch82U (fsuV T I) h).subgroupOf (fsuV T I))
          ((autOn (ch82LU L (ch82U (fsuV T I) h)) (fsuV T I) : Subgroup (MulAut ↥(fsuV T I))) :
            Set (MulAut ↥(fsuV T I))) →
        ρ i * diagEnd γ = diagEnd γ * ρ i)
    (t : ↥(Subgroup.normalizer (pCoreOf 2 (ch82I (fsuV T I) h) : Set G) ⊓
          Subgroup.normalizer (ch82U (fsuV T I) h : Set G)))
    (htI : (t : G) ∈ Subgroup.normalizer (ch82I (fsuV T I) h : Set G)) (ht2 : (t : G) ^ 2 = 1) :
    ∃ τ : K, τ ^ 2 + τ + 1 = 0 ∧
      ρ t * diagEnd ((κ.symm τ : ↥(commutant ((ch82B (fsuV T I) h).subgroupOf (fsuV T I))
        ((ch82U (fsuV T I) h).subgroupOf (fsuV T I))
        ((autOn (ch82LU L (ch82U (fsuV T I) h)) (fsuV T I) : Subgroup (MulAut ↥(fsuV T I))) :
          Set (MulAut ↥(fsuV T I))))) : AddMonoid.End (QMod
            ((ch82B (fsuV T I) h).subgroupOf (fsuV T I))
            ((ch82U (fsuV T I) h).subgroupOf (fsuV T I)))) =
        diagEnd ((κ.symm τ : ↥(commutant ((ch82B (fsuV T I) h).subgroupOf (fsuV T I))
          ((ch82U (fsuV T I) h).subgroupOf (fsuV T I))
          ((autOn (ch82LU L (ch82U (fsuV T I) h)) (fsuV T I) : Subgroup (MulAut ↥(fsuV T I))) :
            Set (MulAut ↥(fsuV T I))))) : AddMonoid.End (QMod
              ((ch82B (fsuV T I) h).subgroupOf (fsuV T I))
              ((ch82U (fsuV T I) h).subgroupOf (fsuV T I)))) * ρ t := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hkerI : kerIn (fsuM T L ⊓ ch82I (fsuV T I) h) (ch82I (fsuV T I) h) =
      pCoreOf 2 (ch82I (fsuV T I) h) := by
    obtain ⟨-, -, -, -, -, -, -, hkerI, -⟩ := id c.hC
    exact hkerI
  have hJ2 : IsPGroup 2 ↥(pCoreOf 2 (ch82I (fsuV T I) h)) :=
    CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  haveI hNP : ((pCoreOf 2 (ch82I (fsuV T I) h)).subgroupOf (ch82I (fsuV T I) h)).Normal := by
    rw [← hkerI]
    infer_instance
  let e' : ↥(ch82I (fsuV T I) h) ⧸ (pCoreOf 2 (ch82I (fsuV T I) h)).subgroupOf
      (ch82I (fsuV T I) h) ≃* DihedralGroup 5 :=
    (QuotientGroup.quotientMulEquivOfEq (by rw [hkerI])).trans eI
  obtain ⟨y, hy5, j, hj, hye⟩ := L828Dih.exists_five_elt hJ2 e'
  have hVP := s828_V_not_le_P c 5 (by norm_num) eI
  obtain ⟨v, hvV, hvP⟩ := Set.not_subset.mp hVP
  have hvJ : v ∈ ch82I (fsuV T I) h := (le_sup_left : fsuV T I ≤ ch82I (fsuV T I) h) hvV
  have hv2 : v ^ 2 = 1 := c.hV.2 _ hvV
  obtain ⟨b, hb⟩ := s828_reflection e' (v := ⟨v, hvJ⟩) hvP hv2
  have hIN2 := s828_I_norm_PU c
  let ρI : ↥(ch82I (fsuV T I) h) →* AddMonoid.End (QB (fsuV T I) (ch82B (fsuV T I) h)
      (ch82U (fsuV T I) h) × QB (fsuV T I) (ch82B (fsuV T I) h) (ch82U (fsuV T I) h)) :=
    ρ.comp (Subgroup.inclusion hIN2)
  have hρIker : ∀ i : ↥(ch82I (fsuV T I) h),
      ρI i = 1 ↔ (i : G) ∈ pCoreOf 2 (ch82I (fsuV T I) h) := by
    intro i
    show ρ (Subgroup.inclusion hIN2 i) = 1 ↔ _
    rw [hker]
    constructor
    · intro hh'
      exact c.hfaith i i.2 hh'
    · intro hi p hp
      exact c.hP2 _ hi p hp
  have hρIcomm : ∀ i : ↥(ch82I (fsuV T I) h), ∀ γ ∈ indSet
      ((ch82B (fsuV T I) h).subgroupOf (fsuV T I)) ((ch82U (fsuV T I) h).subgroupOf (fsuV T I))
      ((autOn (ch82LU L (ch82U (fsuV T I) h)) (fsuV T I) : Subgroup (MulAut ↥(fsuV T I))) :
        Set (MulAut ↥(fsuV T I))),
      ρI i * diagEnd γ = diagEnd γ * ρI i := fun i γ hγ =>
    hcomm (Subgroup.inclusion hIN2 i) i.2 γ hγ
  have hyP : (y : G) ∉ pCoreOf 2 (ch82I (fsuV T I) h) := by
    intro hy
    have h1 : (QuotientGroup.mk y : ↥(ch82I (fsuV T I) h) ⧸
        (pCoreOf 2 (ch82I (fsuV T I) h)).subgroupOf (ch82I (fsuV T I) h)) = 1 :=
      (QuotientGroup.eq_one_iff y).mpr (Subgroup.mem_subgroupOf.mpr hy)
    rw [h1, map_one, DihedralGroup.one_def] at hye
    exact hj (DihedralGroup.r.inj hye).symm
  have hy1 : ρI y ≠ 1 := fun h1 => hyP ((hρIker y).mp h1)
  have hvyP : ((⟨v, hvJ⟩ * y * (⟨v, hvJ⟩ : ↥(ch82I (fsuV T I) h))⁻¹ * y :
      ↥(ch82I (fsuV T I) h)) : G) ∈ pCoreOf 2 (ch82I (fsuV T I) h) := by
    have h1 : e' (QuotientGroup.mk (⟨v, hvJ⟩ * y * (⟨v, hvJ⟩ : ↥(ch82I (fsuV T I) h))⁻¹ * y)) =
        1 := by
      simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv, map_mul, map_inv, hb, hye]
      have key : ∀ b j : ZMod 5, DihedralGroup.sr b * DihedralGroup.r j *
          (DihedralGroup.sr b)⁻¹ * DihedralGroup.r j = 1 := by decide
      exact key b j
    have h2 := (e'.map_eq_one_iff).mp h1
    exact Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp h2)
  have hvy : ρI (⟨v, hvJ⟩ * y * (⟨v, hvJ⟩ : ↥(ch82I (fsuV T I) h))⁻¹ * y) = 1 :=
    (hρIker _).mpr hvyP
  obtain ⟨τ, hτ, hε⟩ := s828_eps_diag hK4
    (indSet ((ch82B (fsuV T I) h).subgroupOf (fsuV T I))
      ((ch82U (fsuV T I) h).subgroupOf (fsuV T I))
      ((autOn (ch82LU L (ch82U (fsuV T I) h)) (fsuV T I) : Subgroup (MulAut ↥(fsuV T I))) :
        Set (MulAut ↥(fsuV T I))))
    κ ρI hρIcomm hy5 hy1 hvy
  refine ⟨τ, hτ, ?_⟩
  have hdc := L828Dih.dihedral_conj e' htI t.2.1 ht2 hj hye
  have hρyinv : ρI y⁻¹ = ρ ((Subgroup.inclusion hIN2 y)⁻¹) := by
    show ρ (Subgroup.inclusion hIN2 y⁻¹) = _
    rw [map_inv]
  have hker1 : ∀ g : ↥(Subgroup.normalizer (pCoreOf 2 (ch82I (fsuV T I) h) : Set G) ⊓
      Subgroup.normalizer (ch82U (fsuV T I) h : Set G)),
      (g : G) ∈ pCoreOf 2 (ch82I (fsuV T I) h) → ρ g = 1 := fun g hg =>
    (hker g).mpr fun p hp => c.hP2 _ hg p hp
  have hρy : ρI y = ρ (Subgroup.inclusion hIN2 y) := rfl
  have hcom : ρ t * (ρI y + ρI y⁻¹) = (ρI y + ρI y⁻¹) * ρ t := by
    rw [hρy, hρyinv]
    refine comm_add_of_conj_pm (u' := ρ t⁻¹) ?_ ?_ ?_ ?_ ?_
    · rw [← map_mul, mul_inv_cancel, map_one]
    · rw [← map_mul, inv_mul_cancel, map_one]
    · rw [← map_mul, mul_inv_cancel, map_one]
    · rw [← map_mul, inv_mul_cancel, map_one]
    · rcases hdc with hd | hd
      · left
        have h1 := hker1 (t * Subgroup.inclusion hIN2 y * t⁻¹ * (Subgroup.inclusion hIN2 y)⁻¹) hd
        simpa only [map_mul] using h1
      · right
        have h1 := hker1 (t * Subgroup.inclusion hIN2 y * t⁻¹ * Subgroup.inclusion hIN2 y) hd
        simpa only [map_mul] using h1
  rw [hε] at hcom
  exact hcom

theorem step828SixB_holds (hE214 : ASInputs.AS_E_2_14)
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (hmod : StmtFSUModule) (h711n : Stmt7_1_1_normal) (hcard : Mathieu.StmtH13Card)
    (hLU : HLU82) (h825 : Stmt8_2_5) (h827 : Step827)
    (hMB0 : MB0_828) (hMB2 : MB2_828) (hMB3 : MB3_828) (hMB4 : MB4_828)
    (hSyl : Sylow822VB_828) : Step828SixB := by
  intro G _ _ T L I hyp h731 h821 hc hrow H h k hH hh hC hr eIne hTX
  obtain ⟨eI⟩ := eIne
  classical
  have c := s828_ctx hE214 h37 h38 h39 hmod h711n hcard hLU h825 h827 hMB0 hMB3 hSyl hyp h731
    h821 hrow hH hh hC
  obtain ⟨hTI, hTP⟩ := s828_T_norm_I c eI hTX
  obtain ⟨ρ, -, -, -, hker, hdiag, hcomm⟩ := s828_rho c
  obtain ⟨t, ζ, htT, ht2, hζ3, hζ1, hrel⟩ :=
    s828_exists_t_zeta hMB3 hMB4 hcard hyp hrow hr c hTP ρ hdiag
  obtain ⟨K, hKf, hKfin, hK4, ⟨κ⟩⟩ := s828_mb2_field4_G hMB2 hcard c (Or.inr hr)
  obtain ⟨τ, hτ, hcomτ⟩ := s828_sixB_tau c hK4 κ eI ρ hker hcomm t (hTI htT) ht2
  have hchar : (2 : K) = 0 := by
    haveI : Fintype K := Fintype.ofFinite K
    have hc4 : Fintype.card K = 4 := by rw [← Nat.card_eq_fintype_card]; exact hK4
    have h4 : ((Fintype.card K : ℕ) : K) = 0 := FiniteField.cast_card_eq_zero K
    rw [hc4] at h4
    have h4' : (4 : K) = 0 := by exact_mod_cast h4
    have h22 : (2 : K) * 2 = 0 := by linear_combination h4'
    rcases mul_eq_zero.mp h22 with h2 | h2 <;> exact h2
  let d : K →+* AddMonoid.End (QB (fsuV T I) (ch82B (fsuV T I) h) (ch82U (fsuV T I) h) ×
      QB (fsuV T I) (ch82B (fsuV T I) h) (ch82U (fsuV T I) h)) :=
    diagRing.comp ((Subring.subtype _).comp κ.symm.toRingHom)
  have hdinj : Function.Injective d := diagRing_injective.comp
    (Subtype.val_injective.comp κ.symm.injective)
  have hζK3 : (κ ζ) ^ 3 = 1 := by rw [← map_pow, hζ3, map_one]
  have hζK1 : κ ζ ≠ 1 := fun h1 => hζ1 (κ.injective (by rw [h1, map_one]))
  have htt1 : ρ t * ρ t⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  have htt2 : ρ t⁻¹ * ρ t = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
  refine scalar_contra' d hdinj hchar (κ ζ) τ hζK3 hζK1 hτ (ρ t) (ρ t⁻¹) htt1 htt2 ?_ ?_
  · have e1 : d (κ ζ) = diagEnd ((ζ : _) : AddMonoid.End (QMod
        ((ch82B (fsuV T I) h).subgroupOf (fsuV T I))
        ((ch82U (fsuV T I) h).subgroupOf (fsuV T I)))) := by
      show diagEnd (((κ.symm (κ ζ) : _)) : AddMonoid.End (QMod
        ((ch82B (fsuV T I) h).subgroupOf (fsuV T I))
        ((ch82U (fsuV T I) h).subgroupOf (fsuV T I)))) = _
      rw [κ.symm_apply_apply]
    have e2 : d ((κ ζ) ^ 2) = diagEnd ((ζ ^ 2 : _) : AddMonoid.End (QMod
        ((ch82B (fsuV T I) h).subgroupOf (fsuV T I))
        ((ch82U (fsuV T I) h).subgroupOf (fsuV T I)))) := by
      show diagEnd (((κ.symm ((κ ζ) ^ 2) : _)) : AddMonoid.End (QMod
        ((ch82B (fsuV T I) h).subgroupOf (fsuV T I))
        ((ch82U (fsuV T I) h).subgroupOf (fsuV T I)))) = _
      rw [← map_pow, κ.symm_apply_apply]
    rw [e1, e2]
    exact hrel
  · exact hcomτ

end SixB3

end CFSG.Quasithin.H13
