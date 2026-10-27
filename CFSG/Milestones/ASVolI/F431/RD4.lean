module

public import CFSG.Milestones.ASVolI.F431.RA35Gen
public import CFSG.Milestones.ASVolI.F48.Small.D42
public import CFSG.Quasithin.Vol2.GoldschmidtF431D3NF
import all CFSG.Milestones.ASVolI.F4
import all CFSG.Milestones.ASVolI.F4Conjugacy
public import CFSG.Milestones.ASVolI.F431.A42D4

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.ASVolI.ChF CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13.F431
  CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion CFSG.Quasithin.D4Hex
  CFSG.LargeExtraspecial.S63

section DSide

set_option linter.unusedSectionVars false


theorem burnsideF4r_d4_conj_t {x : D} (hx1 : x ≠ 1) (hx2 : x * x = 1) (hxz : ¬ IsConj d4z x)
    (hC : Subgroup.centralizer ({x} : Set D) ≤ d4N) : ∃ g ∈ d4N, g * d4t * g⁻¹ = x := by
  have hord : orderOf x = 2 := orderOf_eq_prime (by rw [pow_two]; exact hx2) hx1
  rcases d4_F431LieI.classes x hord with h | h
  · exact absurd h hxz
  obtain ⟨g, hg⟩ := isConj_iff.mp h
  refine ⟨g, ?_, hg⟩
  have hfix : ∀ c ∈ d4Ct, c • (g⁻¹ • (0 : Fin 2457)) = g⁻¹ • (0 : Fin 2457) := by
    intro c hc
    have hc' : c * d4t = d4t * c :=
      Subgroup.mem_centralizer_singleton_iff.mp (d4Ct_le_centralizer hc)
    have hgc : g * c * g⁻¹ ∈ Subgroup.centralizer ({x} : Set D) := by
      rw [Subgroup.mem_centralizer_singleton_iff, ← hg]
      calc g * c * g⁻¹ * (g * d4t * g⁻¹) = g * (c * d4t) * g⁻¹ := by group
        _ = g * (d4t * c) * g⁻¹ := by rw [hc']
        _ = g * d4t * g⁻¹ * (g * c * g⁻¹) := by group
    have hN := hC hgc
    rw [mem_d4N_iff, smul_line_zero_iff] at hN
    calc c • (g⁻¹ • (0 : Fin 2457)) = g⁻¹ • ((g * c * g⁻¹) • (0 : Fin 2457)) := by
          rw [smul_smul, smul_smul]
          congr 1
          group
      _ = g⁻¹ • (0 : Fin 2457) := by rw [hN]
  have h0 := eq_zero_of_fix_d4Ct _ hfix
  have hgi : g⁻¹ ∈ d4N := by
    rw [mem_d4N_iff, smul_line_zero_iff]
    exact h0
  simpa using d4N.inv_mem hgi

end DSide

theorem burnsideF4r_map_equiv_eq {A B : Type} [Group A] [Group B] (ψ : A ≃* B) {P : Subgroup A}
    {Q : Subgroup B} (h : ∀ c, c ∈ P ↔ ψ c ∈ Q) : P.map ψ.toMonoidHom = Q := by
  ext y
  rw [Subgroup.mem_map_equiv, h, MulEquiv.apply_symm_apply]

theorem burnsideF4r_cent_conj_le {M : Type} [Group M] {R : Subgroup M} {a T : M} (ha : a ∈ R)
    (h : Subgroup.centralizer ({T} : Set M) ≤ R) :
    Subgroup.centralizer ({a * T * a⁻¹} : Set M) ≤ R := by
  intro y hy
  rw [Subgroup.mem_centralizer_singleton_iff] at hy
  have h1 : a⁻¹ * y * a ∈ Subgroup.centralizer ({T} : Set M) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc a⁻¹ * y * a * T = a⁻¹ * (y * (a * T * a⁻¹)) * a := by group
      _ = a⁻¹ * ((a * T * a⁻¹) * y) * a := by rw [hy]
      _ = T * (a⁻¹ * y * a) := by group
  have h2 := h h1
  have e : y = a * (a⁻¹ * y * a) * a⁻¹ := by group
  rw [e]
  exact R.mul_mem (R.mul_mem ha h2) (R.inv_mem ha)

section Ident

set_option linter.unusedSectionVars false


variable {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}

theorem burnsideF4r_d4_ident (hyp : HypF_4_4 .D4tw 2 1 Gp M₁ M₂) (hs : IsSimpleGroup D)
    {K : Type} [Field K] [Finite K] [CharP K 2] (σ : K ≃+* K) (hσ3 : ∀ c, σ (σ (σ c)) = c)
    (hK : Nat.card K = (2 ^ 1) ^ 3) (hσq : ∀ c, σ.toRingHom c = c ^ (2 ^ 1))
    (φ : D4q.Struct.Cm σ ≃* ↥Gp)
    (hP1 : M₁.subgroupOf Gp = (D4q.Struct.Pst0 σ).map φ.toMonoidHom)
    (hP2 : M₂.subgroupOf Gp = (D4q.Struct.Pst1 σ).map φ.toMonoidHom) :
    ∃ χ : D ≃* ↥Gp, burnsideF48_img χ d4H = Gp ⊓ M₁ ∧ burnsideF48_img χ d4N = Gp ⊓ M₂ ∧
      χ d4z = φ (D4q.Loc.zC σ) := by
  classical
  haveI : Finite E := hyp.finite
  haveI : Finite D := finite_D
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hD' : IsLieOverTwo .trialityD4 0 1 ↥Gp := burnsideF48_lieModel_D4 hyp.model
  obtain ⟨ε₀⟩ := nonempty_equiv_trialityGroup8 ↥Gp hD'
  have hP := burnsideF48_parabolics_of_compat ChF.nativeChartCompatibility hyp
  obtain ⟨χ, -, hε⟩ := burnsideF48_identify ε₀.symm (burnsideF48s_d42_isLieParabolics hs) hP
  have hφ1 : ∀ c, ((φ c : ↥Gp) : E) ∈ M₁ ↔ c ∈ D4q.Struct.Pst0 σ := by
    intro c
    have h : φ c ∈ M₁.subgroupOf Gp ↔ φ c ∈ (D4q.Struct.Pst0 σ).map φ.toMonoidHom := by
      rw [hP1]
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply] at h
    exact h
  have hφ2 : ∀ c, ((φ c : ↥Gp) : E) ∈ M₂ ↔ c ∈ D4q.Struct.Pst1 σ := by
    intro c
    have h : φ c ∈ M₂.subgroupOf Gp ↔ φ c ∈ (D4q.Struct.Pst1 σ).map φ.toMonoidHom := by
      rw [hP2]
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply] at h
    exact h
  set ψ : D4q.Struct.Cm σ ≃* D := φ.trans χ.symm with hψdef
  have hχ : ∀ {Q : Subgroup D} {M : Subgroup E}, burnsideF48_img χ Q = Gp ⊓ M →
      ∀ c, ((φ c : ↥Gp) : E) ∈ M ↔ ψ c ∈ Q := by
    intro Q M h c
    rw [burnsideF48s_d42_mem_iff χ h (φ c)]
    rfl
  have hBor : (D4q.Struct.Pst0 σ ⊓ D4q.Struct.Pst1 σ).map ψ.toMonoidHom = d4B := by
    apply burnsideF4r_map_equiv_eq
    intro c
    show c ∈ D4q.Struct.Pst0 σ ⊓ D4q.Struct.Pst1 σ ↔ ψ c ∈ d4H ⊓ d4N
    rw [Subgroup.mem_inf, Subgroup.mem_inf, ← hφ1, ← hφ2]
    rcases hε with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [hχ h1, hχ h2]
    · rw [hχ h1, hχ h2, and_comm]
  have hU : (D4q.Struct.Ust σ).map ψ.toMonoidHom = d4U := by
    have h1 := CFSG.Quasithin.H13.F431.pCoreOf_map_of_injective ψ.toMonoidHom ψ.injective
      (D4q.Struct.Pst0 σ ⊓ D4q.Struct.Pst1 σ)
    rw [hBor, burnsideF4gD4Inv_pCore_B σ (le_refl 1) hK hσq, ← normalizer_d4U_eq_d4B hs,
      burnsideF4gD4Inv_pCoreOf_normalizer d4_sylow] at h1
    exact h1.symm
  have hzψ : ψ (D4q.Loc.zC σ) = d4z := by
    have hz := burnsideF4gD4Inv_z_ctr σ hσ3 (le_refl 1) hK hσq
    rw [burnsideF4gD4Inv_pCore_B σ (le_refl 1) hK hσq] at hz
    have hcomm : ∀ u ∈ d4U, ψ (D4q.Loc.zC σ) * u = u * ψ (D4q.Loc.zC σ) := by
      intro u hu
      rw [← hU] at hu
      obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.mp hu
      have hvz : v * D4q.Loc.zC σ = D4q.Loc.zC σ * v := (Subgroup.mem_centralizer_iff.mp hz.2) v hv
      show ψ (D4q.Loc.zC σ) * ψ v = ψ v * ψ (D4q.Loc.zC σ)
      rw [← map_mul, ← map_mul, hvz]
    rcases centralizer_d4U hs hcomm with h | h
    · exact absurd (ψ.injective (h.trans (map_one ψ).symm)) (D4q.Loc.zC_ne_one σ)
    · exact h
  rcases hε with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · refine ⟨χ, h1, h2, ?_⟩
    rw [← hzψ]
    show χ (χ.symm (φ (D4q.Loc.zC σ))) = φ (D4q.Loc.zC σ)
    exact MulEquiv.apply_symm_apply _ _
  · exfalso
    apply not_d4H_le_d4N
    intro y hy
    have hyc : y * d4z = d4z * y := Subgroup.mem_centralizer_singleton_iff.mp hy
    have hc : ψ.symm y ∈ D4q.Struct.Pst0 σ := by
      apply D4q.Loc.cent_zC σ hσ3
      rw [Subgroup.mem_centralizer_singleton_iff]
      apply ψ.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply, hzψ]
      exact hyc
    have := (hχ h2 (ψ.symm y)).mp ((hφ1 _).mpr hc)
    rwa [MulEquiv.apply_symm_apply] at this

end Ident

section Main

set_option linter.unusedSectionVars false


variable {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E} {Y : Type} [Group Y]
  {β : Cpl M₁ M₂ Y} {M : Type} [Group M] {ε : Y →* M} {z : M} {f : ℕ}

theorem burnsideF4r_d4_tconj {K : Type} [Field K] [Finite K] [CharP K 2] (σ : K ≃+* K)
    (hσ3 : ∀ c, σ (σ (σ c)) = c) (φ : D4q.Struct.Cm σ ≃* ↥Gp)
    (hP2 : M₂.subgroupOf Gp = (D4q.Struct.Pst1 σ).map φ.toMonoidHom) (χ : D ≃* ↥Gp)
    (hχ2 : burnsideF48_img χ d4N = Gp ⊓ M₂) (hχz : χ d4z = φ (D4q.Loc.zC σ)) :
    ∃ g ∈ d4N, χ (g * d4t * g⁻¹) = φ (D4q.Loc.tC σ hσ3) := by
  set t' : D := χ.symm (φ (D4q.Loc.tC σ hσ3)) with ht'def
  have hχt' : χ t' = φ (D4q.Loc.tC σ hσ3) := MulEquiv.apply_symm_apply _ _
  have hχM2 : ∀ x : D, ((χ x : ↥Gp) : E) ∈ M₂ ↔ x ∈ d4N := fun x => by
    rw [burnsideF48s_d42_mem_iff χ hχ2 (χ x), MulEquiv.symm_apply_apply]
  have ht'1 : t' ≠ 1 := by
    intro h0
    apply D4q.Loc.tC_ne_one σ hσ3
    apply φ.injective
    rw [← hχt', h0, map_one, map_one]
  have ht'2 : t' * t' = 1 := by
    rw [ht'def, ← map_mul, ← map_mul, D4q.Loc.tC_mul_self σ hσ3, map_one, map_one]
  have hCt' : Subgroup.centralizer ({t'} : Set D) ≤ d4N := by
    intro y hy
    rw [Subgroup.mem_centralizer_singleton_iff] at hy
    have h1 : φ.symm (χ y) ∈
        Subgroup.centralizer ({D4q.Loc.tC σ hσ3} : Set (D4q.Struct.Cm σ)) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      apply φ.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply, ← hχt', ← map_mul, ← map_mul, hy]
    have h2 := D4q.Loc.cent_tC σ hσ3 h1
    have h3 : ((φ (φ.symm (χ y)) : ↥Gp) : E) ∈ M₂ := by
      have h : φ (φ.symm (χ y)) ∈ M₂.subgroupOf Gp := by
        rw [hP2]
        exact ⟨_, h2, rfl⟩
      exact h
    rw [MulEquiv.apply_symm_apply] at h3
    exact (hχM2 y).mp h3
  have ht'z : ¬ IsConj d4z t' := by
    intro h
    obtain ⟨g, hg⟩ := isConj_iff.mp h
    apply burnsideF4gD4Inv_not_conj σ hσ3
    refine isConj_iff.mpr ⟨φ.symm (χ g), ?_⟩
    apply φ.injective
    rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, ← hχz, ← hχt', ← hg, map_mul,
      map_mul, map_inv]
  obtain ⟨g, hgN, hgt⟩ := burnsideF4r_d4_conj_t ht'1 ht'2 ht'z hCt'
  exact ⟨g, hgN, by rw [hgt]; exact hχt'⟩

theorem burnsideF4r_d4_zbar (hyp : HypF_4_31 .D4tw f Gp M₁ M₂ β ε z) (hs : IsSimpleGroup D)
    (χ : D ≃* ↥Gp) (hχ1 : burnsideF48_img χ d4H = Gp ⊓ M₁)
    (hχ2 : burnsideF48_img χ d4N = Gp ⊓ M₂) :
    ∃ h : ((χ d4z : ↥Gp) : E) ∈ M₁, burnsideF4d_bOne β ε ⟨_, h⟩ = z := by
  haveI : Finite D := finite_D
  have hχM1 : ∀ x : D, ((χ x : ↥Gp) : E) ∈ M₁ ↔ x ∈ d4H := fun x => by
    rw [burnsideF48s_d42_mem_iff χ hχ1 (χ x), MulEquiv.symm_apply_apply]
  have hχM2 : ∀ x : D, ((χ x : ↥Gp) : E) ∈ M₂ ↔ x ∈ d4N := fun x => by
    rw [burnsideF48s_d42_mem_iff χ hχ2 (χ x), MulEquiv.symm_apply_apply]
  obtain ⟨xb, hxS, hxz, hx1, -⟩ := burnsideF4r_zbar hyp (by decide)
  have hχB : burnsideF48_img χ d4B = Gp ⊓ (M₁ ⊓ M₂) := by
    ext y
    rw [burnsideF48_mem_img_iff]
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hx' : x ∈ d4H ⊓ d4N := hx
      exact ⟨(χ x).2, (hχM1 x).mpr hx'.1, (hχM2 x).mpr hx'.2⟩
    · rintro ⟨hy, hy1, hy2⟩
      refine ⟨χ.symm ⟨y, hy⟩, ?_, by rw [MulEquiv.apply_symm_apply]⟩
      show χ.symm ⟨y, hy⟩ ∈ d4H ⊓ d4N
      refine ⟨(hχM1 _).mp ?_, (hχM2 _).mp ?_⟩
      · rw [MulEquiv.apply_symm_apply]
        exact hy1
      · rw [MulEquiv.apply_symm_apply]
        exact hy2
  have hSU : pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) = burnsideF48_img χ d4U := by
    rw [← hχB, burnsideF48_img, burnsideF48_img,
      CFSG.Quasithin.H13.F431.pCoreOf_map_of_injective _ Gp.subtype_injective,
      CFSG.Quasithin.H13.F431.pCoreOf_map_of_injective _ χ.injective,
      ← normalizer_d4U_eq_d4B hs, burnsideF4gD4Inv_pCoreOf_normalizer d4_sylow]
  have hxG : (xb : E) ∈ Gp := (CFSG.LieType.BorelTits.pCoreOf_le 2 _ hxS.1).1
  have hxχ : ((χ d4z : ↥Gp) : E) = (xb : E) := by
    set w : D := χ.symm ⟨xb, hxG⟩ with hwdef
    have hcomm : ∀ u ∈ d4U, w * u = u * w := by
      intro u hu
      have hu' : ((χ u : ↥Gp) : E) ∈ pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) := by
        rw [hSU, burnsideF48_mem_img]
        exact hu
      have e1 : ((χ u : ↥Gp) : E) * (xb : E) = (xb : E) * ((χ u : ↥Gp) : E) :=
        (Subgroup.mem_centralizer_iff.mp hxS.2) _ hu'
      apply χ.injective
      apply Subtype.ext
      rw [map_mul, map_mul, hwdef, MulEquiv.apply_symm_apply]
      exact e1.symm
    rcases centralizer_d4U hs hcomm with h | h
    · exfalso
      apply hx1
      have e2 : (⟨xb, hxG⟩ : ↥Gp) = 1 := by
        rw [← MulEquiv.apply_symm_apply χ ⟨xb, hxG⟩, ← hwdef, h, map_one]
      have e3 : (xb : E) = 1 := congrArg Subtype.val e2
      exact Subtype.ext e3
    · rw [← h, hwdef, MulEquiv.apply_symm_apply]
  refine ⟨(hχM1 d4z).mpr d4z_mem_d4H, ?_⟩
  rw [← hxz, burnsideF4j_bM_eq_bOne]
  congr 1
  exact Subtype.ext hxχ

theorem burnsideF4r_d4_cent_top (hyp : HypF_4_31 .D4tw f Gp M₁ M₂ β ε z) (hGp : Gp = ⊤)
    (χ : D ≃* ↥Gp) (hχ1 : burnsideF48_img χ d4H = Gp ⊓ M₁)
    (hχ2 : burnsideF48_img χ d4N = Gp ⊓ M₂) (hz1 : ((χ d4z : ↥Gp) : E) ∈ M₁)
    (hzb : burnsideF4d_bOne β ε ⟨_, hz1⟩ = z) {g : D} (hgN : g ∈ d4N)
    (ht : ((χ (g * d4t * g⁻¹) : ↥Gp) : E) ∈ M₂) :
    Subgroup.centralizer ({burnsideF4d_bTwo β ε ⟨_, ht⟩} : Set M) ≤ MiTwo β ε := by
  haveI := hyp.finite_M
  have hχM1 : ∀ x : D, ((χ x : ↥Gp) : E) ∈ M₁ ↔ x ∈ d4H := fun x => by
    rw [burnsideF48s_d42_mem_iff χ hχ1 (χ x), MulEquiv.symm_apply_apply]
  have hχM2 : ∀ x : D, ((χ x : ↥Gp) : E) ∈ M₂ ↔ x ∈ d4N := fun x => by
    rw [burnsideF48s_d42_mem_iff χ hχ2 (χ x), MulEquiv.symm_apply_apply]
  obtain ⟨b1, hb1⟩ : ∃ b1 : ↥d4H →* M, ∀ x (hx : x ∈ d4H),
      b1 ⟨x, hx⟩ = burnsideF4d_bOne β ε ⟨((χ x : ↥Gp) : E), (hχM1 x).mpr hx⟩ :=
    ⟨(burnsideF4d_bOne β ε).comp (((Gp.subtype.comp χ.toMonoidHom).comp d4H.subtype).codRestrict
      M₁ (fun x => (hχM1 x).mpr x.2)), fun x hx => rfl⟩
  obtain ⟨b2, hb2⟩ : ∃ b2 : ↥d4N →* M, ∀ x (hx : x ∈ d4N),
      b2 ⟨x, hx⟩ = burnsideF4d_bTwo β ε ⟨((χ x : ↥Gp) : E), (hχM2 x).mpr hx⟩ :=
    ⟨(burnsideF4d_bTwo β ε).comp (((Gp.subtype.comp χ.toMonoidHom).comp d4N.subtype).codRestrict
      M₂ (fun x => (hχM2 x).mpr x.2)), fun x hx => rfl⟩
  have C : F431Comp d4H d4N b1 b2 :=
    { inj₁ := by
        rintro ⟨a, ha⟩ ⟨b, hb⟩ hab
        rw [hb1, hb1] at hab
        have h1 := congrArg Subtype.val (burnsideF4j_bOne_injective hyp hab)
        exact Subtype.ext (χ.injective (Subtype.ext h1))
      inj₂ := by
        rintro ⟨a, ha⟩ ⟨b, hb⟩ hab
        rw [hb2, hb2] at hab
        have h1 := congrArg Subtype.val (burnsideF4j_bTwo_injective hyp hab)
        exact Subtype.ext (χ.injective (Subtype.ext h1))
      agree := fun x h1 h2 => by
        rw [hb1, hb2]
        exact burnsideF4j_bOne_eq_bTwo β ε _ _ _ }
  have hz' : amalgamMap b1 b2 d4z = z := by
    rw [amalgamMap_of_mem₁ b1 b2 d4z_mem_d4H, hb1]
    exact hzb
  have hMi1 : MiOne β ε = (burnsideF4d_bOne β ε).range := (MonoidHom.range_comp _ _).symm
  have hMi2 : MiTwo β ε = (burnsideF4d_bTwo β ε).range := (MonoidHom.range_comp _ _).symm
  have hrange1 : MiOne β ε ≤ b1.range := by
    rw [hMi1]
    rintro _ ⟨⟨e, he⟩, rfl⟩
    have heG : e ∈ Gp := by rw [hGp]; exact Subgroup.mem_top e
    have hx : χ.symm ⟨e, heG⟩ ∈ d4H := by
      rw [← hχM1, MulEquiv.apply_symm_apply]
      exact he
    refine ⟨⟨_, hx⟩, ?_⟩
    rw [hb1]
    congr 1
    apply Subtype.ext
    show ((χ (χ.symm ⟨e, heG⟩) : ↥Gp) : E) = e
    rw [MulEquiv.apply_symm_apply]
  have hrange2 : b2.range ≤ MiTwo β ε := by
    rw [hMi2]
    rintro _ ⟨⟨x, hx⟩, rfl⟩
    rw [hb2]
    exact MonoidHom.mem_range.mpr ⟨_, rfl⟩
  have hloc := d4_localCent_comp C (by rw [hz']; exact hyp.hb.trans hrange1)
  have htN : d4t ∈ d4N := d4U_le_d4B.trans inf_le_right d4t_mem_d4U
  rw [amalgamMap_of_mem₂ b1 b2 C.agree htN] at hloc
  have hconj : burnsideF4d_bTwo β ε ⟨_, ht⟩ =
      b2 ⟨g, hgN⟩ * b2 ⟨d4t, htN⟩ * (b2 ⟨g, hgN⟩)⁻¹ := by
    rw [← map_inv, ← map_mul, ← map_mul]
    exact (hb2 _ _).symm
  rw [hconj]
  exact (burnsideF4r_cent_conj_le (MonoidHom.mem_range.mpr ⟨⟨g, hgN⟩, rfl⟩) hloc).trans hrange2

theorem burnsideF4r_d4_cent_ext (hyp : HypF_4_31 .D4tw f Gp M₁ M₂ β ε z) (hGp : Gp ≠ ⊤)
    (hD' : IsLieOverTwo .trialityD4 0 1 ↥Gp) (hs : IsSimpleGroup D)
    (χ : D ≃* ↥Gp) (hχ1 : burnsideF48_img χ d4H = Gp ⊓ M₁)
    (hχ2 : burnsideF48_img χ d4N = Gp ⊓ M₂) (hz1 : ((χ d4z : ↥Gp) : E) ∈ M₁)
    (hzb : burnsideF4d_bOne β ε ⟨_, hz1⟩ = z) {g : D} (hgN : g ∈ d4N)
    (ht : ((χ (g * d4t * g⁻¹) : ↥Gp) : E) ∈ M₂) :
    Subgroup.centralizer ({burnsideF4d_bTwo β ε ⟨_, ht⟩} : Set M) ≤ MiTwo β ε := by
  haveI := hyp.finite_M
  haveI := hyp.amalgam.finite
  haveI : Finite D := finite_D
  haveI : Gp.Normal := hyp.amalgam.normal
  have hχM1 : ∀ x : D, ((χ x : ↥Gp) : E) ∈ M₁ ↔ x ∈ d4H := fun x => by
    rw [burnsideF48s_d42_mem_iff χ hχ1 (χ x), MulEquiv.symm_apply_apply]
  have hχM2 : ∀ x : D, ((χ x : ↥Gp) : E) ∈ M₂ ↔ x ∈ d4N := fun x => by
    rw [burnsideF48s_d42_mem_iff χ hχ2 (χ x), MulEquiv.symm_apply_apply]
  obtain ⟨hcA, -⟩ := d4_card_aut hD'
  have hcardE := burnsideF48s_d42_card_E hcA χ hyp.amalgam.centralizer_trivial hGp
  have hinj := burnsideF48s_d42_conjHom_injective Gp χ.symm hyp.amalgam.centralizer_trivial
  haveI : Finite (MulAut D) := Nat.finite_of_card_ne_zero (by
    rw [← hcardE]
    exact Nat.card_pos.ne')
  obtain ⟨cE, hcE⟩ : ∃ cE : E ≃* MulAut D, ∀ e, cE e = burnsideF48s_d42_conjHom Gp χ.symm e :=
    ⟨MulEquiv.ofBijective _ (hinj.bijective_of_nat_card_le hcardE.ge), fun e => rfl⟩
  have hcE1 : ∀ e, e ∈ M₁ ↔ cE e ∈ autStab d4H := fun e => by
    rw [hcE]
    exact burnsideF48s_d42_mem_autStab_iff χ hχ1 (d4_hHH hs) hyp.amalgam.split inf_le_left e
  have hcE2 : ∀ e, e ∈ M₂ ↔ cE e ∈ autStab d4N := fun e => by
    rw [hcE]
    exact burnsideF48s_d42_mem_autStab_iff χ hχ2 (d4_hNN hs) hyp.amalgam.split inf_le_right e
  have hcEχ : ∀ y : D, cE ((χ y : ↥Gp) : E) = MulAut.conj y := by
    intro y
    refine MulEquiv.ext fun x => ?_
    have h1 := burnsideF48s_d42_conjHom_apply Gp χ.symm ((χ y : ↥Gp) : E) x
    rw [MulEquiv.symm_symm] at h1
    rw [hcE]
    apply χ.injective
    apply Subtype.ext
    rw [h1, MulAut.conj_apply, map_mul, map_mul, map_inv]
    rfl
  have hsymm : ∀ α : MulAut D, cE (cE.symm α) = α := fun α => MulEquiv.apply_symm_apply _ _
  obtain ⟨b1, hb1⟩ : ∃ b1 : ↥(autStab d4H) →* M, ∀ α (hα : α ∈ autStab d4H),
      b1 ⟨α, hα⟩ = burnsideF4d_bOne β ε ⟨cE.symm α, (hcE1 _).mpr (by rw [hsymm]; exact hα)⟩ :=
    ⟨(burnsideF4d_bOne β ε).comp ((cE.symm.toMonoidHom.comp (autStab d4H).subtype).codRestrict M₁
      (fun α => (hcE1 _).mpr (by
        show cE (cE.symm (α : MulAut D)) ∈ autStab d4H
        rw [hsymm]
        exact α.2))), fun α hα => rfl⟩
  obtain ⟨b2, hb2⟩ : ∃ b2 : ↥(autStab d4N) →* M, ∀ α (hα : α ∈ autStab d4N),
      b2 ⟨α, hα⟩ = burnsideF4d_bTwo β ε ⟨cE.symm α, (hcE2 _).mpr (by rw [hsymm]; exact hα)⟩ :=
    ⟨(burnsideF4d_bTwo β ε).comp ((cE.symm.toMonoidHom.comp (autStab d4N).subtype).codRestrict M₂
      (fun α => (hcE2 _).mpr (by
        show cE (cE.symm (α : MulAut D)) ∈ autStab d4N
        rw [hsymm]
        exact α.2))), fun α hα => rfl⟩
  have C : F431Comp (autStab d4H) (autStab d4N) b1 b2 :=
    { inj₁ := by
        rintro ⟨a, ha⟩ ⟨b, hb⟩ hab
        rw [hb1, hb1] at hab
        have h1 := congrArg Subtype.val (burnsideF4j_bOne_injective hyp hab)
        exact Subtype.ext (cE.symm.injective h1)
      inj₂ := by
        rintro ⟨a, ha⟩ ⟨b, hb⟩ hab
        rw [hb2, hb2] at hab
        have h1 := congrArg Subtype.val (burnsideF4j_bTwo_injective hyp hab)
        exact Subtype.ext (cE.symm.injective h1)
      agree := fun x h1 h2 => by
        rw [hb1, hb2]
        exact burnsideF4j_bOne_eq_bTwo β ε _ _ _ }
  have hd3z : d3z ∈ autStab d4H := by
    rw [d3z, ← hcEχ, ← hcE1]
    exact hz1
  have hz' : amalgamMap b1 b2 d3z = z := by
    rw [amalgamMap_of_mem₁ b1 b2 hd3z, hb1, ← hzb]
    congr 1
    apply Subtype.ext
    show cE.symm d3z = ((χ d4z : ↥Gp) : E)
    rw [d3z, ← hcEχ, MulEquiv.symm_apply_apply]
  have hMi1 : MiOne β ε = (burnsideF4d_bOne β ε).range := (MonoidHom.range_comp _ _).symm
  have hMi2 : MiTwo β ε = (burnsideF4d_bTwo β ε).range := (MonoidHom.range_comp _ _).symm
  have hrange1 : MiOne β ε ≤ b1.range := by
    rw [hMi1]
    rintro _ ⟨⟨e, he⟩, rfl⟩
    refine ⟨⟨cE e, (hcE1 e).mp he⟩, ?_⟩
    rw [hb1]
    congr 1
    apply Subtype.ext
    show cE.symm (cE e) = e
    rw [MulEquiv.symm_apply_apply]
  have hrange2 : b2.range ≤ MiTwo β ε := by
    rw [hMi2]
    rintro _ ⟨⟨x, hx⟩, rfl⟩
    rw [hb2]
    exact MonoidHom.mem_range.mpr ⟨_, rfl⟩
  have hCU : ∀ x : D, (∀ u ∈ d4U, x * u = u * x) → x = 1 ∨ x = d4z :=
    fun x hx => centralizer_d4U hs hx
  have hodd' : ¬ 2 ∣ (MulAut.conj : D →* MulAut D).range.index := by
    rw [d4_conj_index hD']
    decide
  have hloc := d3_localCent_comp hs hCU hodd' (d4_card_aut_dvd hD') C
    (by rw [hz']; exact hyp.hb.trans hrange1)
  have htN : d3t ∈ autStab d4N := by
    rw [d3t, ← hcEχ, ← hcE2]
    exact (hχM2 d4t).mpr (d4U_le_d4B.trans inf_le_right d4t_mem_d4U)
  have hgA : MulAut.conj g ∈ autStab d4N := by
    rw [← hcEχ, ← hcE2]
    exact (hχM2 g).mpr hgN
  rw [amalgamMap_of_mem₂ b1 b2 C.agree htN] at hloc
  have hconj : burnsideF4d_bTwo β ε ⟨_, ht⟩ =
      b2 ⟨MulAut.conj g, hgA⟩ * b2 ⟨d3t, htN⟩ * (b2 ⟨MulAut.conj g, hgA⟩)⁻¹ := by
    rw [← map_inv, ← map_mul, ← map_mul, hb2]
    congr 1
    apply Subtype.ext
    show ((χ (g * d4t * g⁻¹) : ↥Gp) : E) = cE.symm (MulAut.conj g * d3t * (MulAut.conj g)⁻¹)
    rw [d3t, ← map_inv, ← map_mul, ← map_mul, ← hcEχ, MulEquiv.symm_apply_apply]
  rw [hconj]
  exact (burnsideF4r_cent_conj_le (MonoidHom.mem_range.mpr ⟨⟨MulAut.conj g, hgA⟩, rfl⟩)
    hloc).trans hrange2

theorem burnsideF4r_A42_D4 (hyp : HypF_4_31 .D4tw f Gp M₁ M₂ β ε z) (hf : f < 2) :
    ∃ t : ↥M₂, (t : E) ∈ pCoreOf 2 (Gp ⊓ M₂) ∧ IsShortRootInv .D4tw Gp M₁ M₂ (t : E) ∧
      Subgroup.centralizer ({epsG β ε (f2 (c := β) t)} : Set M) ≤ MiTwo β ε := by
  classical
  haveI := hyp.finite_M
  haveI := hyp.amalgam.finite
  have hf1 : 1 ≤ f := hyp.amalgam.model.2.1
  obtain rfl : f = 1 := by omega
  obtain ⟨chart, hm⟩ := hyp.amalgam.lie_amalgam
  obtain ⟨K, _, _, _, σ, hσ3, -, hK, hσq, φ, hP1, hP2, hS⟩ := burnsideF4m_A42_chart_D4 chart hm
  have hD' : IsLieOverTwo .trialityD4 0 1 ↥Gp := burnsideF48_lieModel_D4 hyp.amalgam.model
  have hs : IsSimpleGroup D := d4_isSimpleGroup hD'
  obtain ⟨χ, hχ1, hχ2, hχz⟩ := burnsideF4r_d4_ident hyp.amalgam hs σ hσ3 hK hσq φ hP1 hP2
  have htP : D4q.Loc.tC σ hσ3 ∈ D4q.Struct.Pst1 σ :=
    CFSG.LieType.BorelTits.pCoreOf_le 2 _ (burnsideF4gD4Inv_t_core σ hσ3)
  have ht : ((φ (D4q.Loc.tC σ hσ3) : ↥Gp) : E) ∈ M₂ := by
    have h : φ (D4q.Loc.tC σ hσ3) ∈ M₂.subgroupOf Gp := by
      rw [hP2]
      exact ⟨_, htP, rfl⟩
    exact h
  refine ⟨⟨_, ht⟩, ?_, ?_, ?_⟩
  ·
    have hGM : Gp ⊓ M₂ = ((D4q.Struct.Pst1 σ).map φ.toMonoidHom).map Gp.subtype := by
      rw [← hP2, Subgroup.subgroupOf_map_subtype, inf_comm]
    show ((φ (D4q.Loc.tC σ hσ3) : ↥Gp) : E) ∈ pCoreOf 2 (Gp ⊓ M₂)
    rw [hGM, CFSG.Quasithin.H13.F431.pCoreOf_map_of_injective _ Gp.subtype_injective,
      CFSG.Quasithin.H13.F431.pCoreOf_map_of_injective _ φ.injective]
    exact ⟨φ (D4q.Loc.tC σ hσ3), ⟨D4q.Loc.tC σ hσ3, burnsideF4gD4Inv_t_core σ hσ3, rfl⟩, rfl⟩
  ·
    obtain ⟨b, hbS, hb1⟩ := burnsideF4gD4Inv_S_ne σ hσ3
    obtain ⟨c, hc⟩ := isConj_iff.mp (burnsideF4gD4Inv_S_conj σ hσ3 b hbS hb1)
    have ht1 : D4q.Loc.tC σ hσ3 ≠ 1 := D4q.Loc.tC_ne_one σ hσ3
    refine ⟨1, chart, hm, (φ (D4q.Loc.tC σ hσ3)).2, ?_, ?_,
      fun h => absurd h (by decide), ((φ c : ↥Gp) : E), (φ c).2, ?_⟩
    · intro h
      have h1 : φ (D4q.Loc.tC σ hσ3) = φ 1 := by
        rw [map_one]
        exact Subtype.ext h
      exact ht1 (φ.injective h1)
    · show ((φ (D4q.Loc.tC σ hσ3) * φ (D4q.Loc.tC σ hσ3) : ↥Gp) : E) = 1
      rw [← map_mul, D4q.Loc.tC_mul_self σ hσ3, map_one]
      rfl
    · rw [if_pos rfl, hS]
      refine ⟨φ b, ⟨b, hbS, rfl⟩, ?_⟩
      show (φ b : E) = (φ c : E) * (φ (D4q.Loc.tC σ hσ3) : E) * ((φ c : E))⁻¹
      rw [← hc]
      simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]
  ·
    obtain ⟨g, hgN, hgt⟩ := burnsideF4r_d4_tconj σ hσ3 φ hP2 χ hχ2 hχz
    obtain ⟨hz1, hzb⟩ := burnsideF4r_d4_zbar hyp hs χ hχ1 hχ2
    have ht' : ((χ (g * d4t * g⁻¹) : ↥Gp) : E) ∈ M₂ := by rw [hgt]; exact ht
    have hbt : epsG β ε (f2 (c := β) ⟨_, ht⟩) = burnsideF4d_bTwo β ε ⟨_, ht'⟩ := by
      show burnsideF4d_bTwo β ε ⟨_, ht⟩ = _
      congr 1
      apply Subtype.ext
      exact (congrArg Subtype.val hgt).symm
    rw [hbt]
    by_cases hGp : Gp = ⊤
    · exact burnsideF4r_d4_cent_top hyp hGp χ hχ1 hχ2 hz1 hzb hgN ht'
    · exact burnsideF4r_d4_cent_ext hyp hGp hD' hs χ hχ1 hχ2 hz1 hzb hgN ht'

end Main

end CFSG.ASVolI
