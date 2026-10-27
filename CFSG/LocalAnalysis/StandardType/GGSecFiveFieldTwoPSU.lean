module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveFieldTwoCommon
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.FEPSU
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.BlockModelSelfDualPSU
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.BlockModelDualPairPSU
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.CompPSU
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.StepA2
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.IDPSU
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.GeoWittSU
public import CFSG.LocalAnalysis.StandardType.GGSelectedPSUModel
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeIRGTyLabelAux
public import CFSG.LocalAnalysis.StandardType.GGSixTCLiftGroup
public import CFSG.LieType.Steinberg.CentralExt.SUTwo
public import CFSG.LocalAnalysis.StandardType.GGSecFiveFieldTwoPSUChart

public section

namespace CFSG.StandardType

namespace FieldTwoPSU

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal
  CFSG.StandardType.ClassicalPosition CFSG.StandardType.S2MathFi1035Pos
open scoped Matrix

abbrev ftF (g : ℕ) : Type := GaloisField 2 (2 * (g + 1))

noncomputable abbrev ftσ (g : ℕ) : ftF g ≃+* ftF g :=
  CFSG.LieType.BorelTits.unitaryInvolution (ftF g) 2 (g + 1)

theorem card_ftF (g : ℕ) : Nat.card (ftF g) = (2 ^ (g + 1)) ^ 2 :=
  card_galoisField_two_mul 2 (g + 1) (by omega)

private theorem odd_card_sub_one {K : Type} {f : ℕ} (hc : Nat.card K = (2 ^ f) ^ 2) (hf : 1 ≤ f) :
    Odd (Nat.card K - 1) := by
  have hpowF : Nat.card K = 2 * 2 ^ (2 * f - 1) := by
    calc Nat.card K = (2 ^ f) ^ 2 := hc
      _ = 2 ^ (f * 2) := by rw [pow_mul]
      _ = 2 ^ (2 * f) := by rw [mul_comm f 2]
      _ = 2 * 2 ^ (2 * f - 1) := by
            conv_lhs => rw [show 2 * f = (2 * f - 1) + 1 by omega]
            rw [pow_add, pow_one]
            ring
  rw [hpowF]
  refine ⟨2 ^ (2 * f - 1) - 1, ?_⟩
  have hX : 1 ≤ 2 ^ (2 * f - 1) := Nat.one_le_two_pow
  omega

private theorem odd_orderOf_lift {K : Type} [Field K] [Finite K] [CharP K 2] {f n : ℕ}
    (hc : Nat.card K = (2 ^ f) ^ 2) (hn : 3 ≤ n) (hf : 1 ≤ f) {X : Type} [Group X]
    (ψ : ↥(Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution K 2 f) n) →* X)
    (hψ : ψ.ker ≤ Subgroup.center _) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {d : X}
    (hdp : d ^ p = 1) {s : GL (Fin n) K}
    (hs : IsGLLift (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution K 2 f) n).subtype
      ψ s d) :
    Odd (orderOf s) := by
  have : Fintype K := Fintype.ofFinite K
  have hsp : IsGLLift (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution K 2 f) n).subtype
      ψ (s ^ p) 1 := by
    have h := hs.pow p
    rwa [hdp] at h
  obtain ⟨c, hc_eq⟩ := isGLLift_unique_PSU hc n ψ hψ hsp isGLLift_one
  have hsmat : (s : Matrix (Fin n) (Fin n) K) ^ p = Matrix.scalar (Fin n) c := by
    have h := hc_eq
    rw [inv_one, one_mul] at h
    simpa only [Units.val_pow_eq_pow_val] using h
  have hcne : c ≠ 0 := by
    have hunit : IsUnit ((s : Matrix (Fin n) (Fin n) K) ^ p) := IsUnit.pow p ⟨s, rfl⟩
    have hm : IsUnit ((Matrix.scalar (Fin n) c : Matrix (Fin n) (Fin n) K).det) := by
      rw [← hsmat]
      exact (Matrix.isUnit_iff_isUnit_det
        (A := (s : Matrix (Fin n) (Fin n) K) ^ p)).mp hunit
    have hdet : (Matrix.scalar (Fin n) c : Matrix (Fin n) (Fin n) K).det = c ^ n := by
      rw [Matrix.scalar_apply, Matrix.det_diagonal]
      simp [Finset.prod_const, Fintype.card_fin]
    rw [hdet] at hm
    have hn0 : n ≠ 0 := by omega
    exact ((isUnit_pow_iff (a := c) (n := n) hn0).mp hm).ne_zero
  let u : Kˣ := Units.mk0 c hcne
  have hspu : s ^ p = Matrix.GeneralLinearGroup.scalar (Fin n) u := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, hsmat, Matrix.GeneralLinearGroup.coe_scalar]
    rfl
  have hpow1 : s ^ (p * orderOf u) = 1 := by
    rw [pow_mul, hspu, ← map_pow, pow_orderOf_eq_one, map_one]
  have hdvd : orderOf s ∣ p * orderOf u := orderOf_dvd_iff_pow_eq_one.mpr hpow1
  have hoddF : Odd (Nat.card K - 1) := odd_card_sub_one hc hf
  have hu_pow : u ^ (Nat.card K - 1) = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one, Nat.card_eq_fintype_card]
    exact FiniteField.pow_card_sub_one_eq_one (u : K) (Units.ne_zero u)
  have hodd_u : Odd (orderOf u) :=
    Odd.of_dvd_nat hoddF (orderOf_dvd_iff_pow_eq_one.mpr hu_pow)
  have hodd_p : Odd p := hp.odd_of_ne_two hp2
  exact Odd.of_dvd_nat (Nat.odd_mul.mpr ⟨hodd_p, hodd_u⟩) hdvd

theorem exists_lift_component {X : Type} [Group X] [Finite X] (n g : ℕ) (hn : 3 ≤ n)
    (ψ : ↥(Unitary.SU (ftσ g) n) →* X) (hψ : ψ.ker ≤ Subgroup.center _)
    {x : X} (hxN : x ∈ Subgroup.normalizer (ψ.range : Set X))
    (hdiag : GGPsiInnerDiag (Unitary.rootDatum (card_ftF g) n) ψ x) (hx3 : x ^ 3 = 1)
    {L : Subgroup X} (hL : IsComponentOf L (ψ.range ⊓ Subgroup.centralizer {x})) :
    ∃ (s : GL (Fin n) (ftF g)) (L' : Subgroup ↥(Unitary.SU (ftσ g) n)),
      L'.map ψ = L ∧
      IsComponentOf L' ((Subgroup.centralizer ({s} : Set (GL (Fin n) (ftF g)))).comap
        (Unitary.SU (ftσ g) n).subtype) ∧
      Odd (orderOf s) ∧
      Unitary.conjTr (ftσ g) (s : Matrix (Fin n) (Fin n) (ftF g)) * Unitary.antidiag n *
        (s : Matrix (Fin n) (Fin n) (ftF g)) = Unitary.antidiag n := by
  obtain ⟨s, hsU, hsl⟩ := exists_isGLLift_PSU (card_ftF g) n hn ψ hψ hxN hdiag
  have hodd : Odd (orderOf s) :=
    odd_orderOf_lift (card_ftF g) hn (by omega) ψ hψ Nat.prime_three (by norm_num) hx3 hsl
  have hcentD : Subgroup.centralizer (Subgroup.zpowers x : Set X) =
      Subgroup.centralizer ({x} : Set X) := by
    rw [Subgroup.zpowers_eq_closure x]
    exact Subgroup.centralizer_closure ({x} : Set X)
  have hJ : IsComponentOf L (ψ.range ⊓ Subgroup.centralizer (Subgroup.zpowers x : Set X)) := by
    rw [hcentD]
    exact hL
  let P : GL (Fin n) (ftF g) → Prop := fun s' => ∃ k : ℤ, s' = s ^ k
  let T : Set (GL (Fin n) (ftF g)) :=
    {s' | P s' ∧ ∃ d ∈ Subgroup.zpowers x,
      IsGLLift ((Unitary.SU (ftσ g) n).subtype) ψ s' d}
  have hlift : ∀ d ∈ Subgroup.zpowers x,
      ∃ s', P s' ∧ IsGLLift ((Unitary.SU (ftσ g) n).subtype) ψ s' d := by
    intro d hd
    rw [Subgroup.mem_zpowers_iff] at hd
    obtain ⟨k, hk⟩ := hd
    rw [← hk]
    exact ⟨s ^ k, ⟨k, rfl⟩, hsl.zpow_of_injective (Subgroup.subtype_injective _) k⟩
  obtain ⟨L', hL'comp, hL'map⟩ :=
    StepA.exists_isComponentOf_comap_lift_of_isGLLift ((Unitary.SU (ftσ g) n).subtype)
      (Subgroup.subtype_injective _) ψ hψ P hJ hlift
  have hcentT : Subgroup.centralizer ({s} : Set (GL (Fin n) (ftF g))) =
      Subgroup.centralizer T := by
    apply le_antisymm
    · intro y hy
      have hcomm : Commute s y :=
        (Subgroup.mem_centralizer_iff.mp hy) s (Set.mem_singleton s)
      rw [Subgroup.mem_centralizer_iff]
      intro t ht
      obtain ⟨⟨k, rfl⟩, -⟩ := ht
      exact (hcomm.zpow_left k).eq
    · intro y hy
      rw [Subgroup.mem_centralizer_iff] at hy ⊢
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      rw [hh]
      exact hy s ⟨⟨1, by rw [zpow_one]⟩, x,
        Subgroup.mem_zpowers_iff.mpr ⟨1, by rw [zpow_one]⟩, hsl⟩
  refine ⟨s, L', hL'map, ?_, hodd, hsU⟩
  rw [hcentT]
  exact hL'comp

theorem form_mulVec_single {K : Type*} [Field K] (σ : K ≃+* K) {n r : ℕ}
    (J : Matrix (Fin n) (Fin n) K) (M : Matrix (Fin n) (Fin r) K) (a b : Fin r) :
    Matrix.vecMul (fun i => σ ((M *ᵥ Pi.single a 1) i)) J ⬝ᵥ (M *ᵥ Pi.single b 1) =
      (Matrix.transpose (M.map σ.toRingHom) * J * M) a b := by
  simp only [Matrix.mulVec_single_one, Matrix.col_apply, Matrix.vecMul, dotProduct,
    Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, RingEquiv.toRingHom_eq_coe,
    RingHom.coe_coe, Finset.sum_mul]

theorem form_smul_smul {K : Type*} [Field K] (σ : K ≃+* K) {n : ℕ}
    (J : Matrix (Fin n) (Fin n) K) (α β : K) (v w : Fin n → K) :
    Matrix.vecMul (fun i => σ ((α • v) i)) J ⬝ᵥ (β • w) =
      σ α * β * (Matrix.vecMul (fun i => σ (v i)) J ⬝ᵥ w) := by
  have h1 : (fun i => σ ((α • v) i)) = σ α • (fun i => σ (v i)) := by
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, map_mul]
  rw [h1, Matrix.smul_vecMul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]
  ring

section Cert


theorem selfDual_of_component {X : Type} [Group X] [Finite X] (n g : ℕ)
    (ψ : ↥(Unitary.SU (ftσ g) n) →* X) (hψ : ψ.ker ≤ Subgroup.center _)
    {lab : LargeEvenLabel} (hl : LargeEvenInLambda2 lab) (hn1 : lab.n = 1)
    (hne : lab ≠ ⟨.twD, 2, 1⟩) {L : Subgroup X}
    (hM : MarkedModel lab (↥L ⧸ Subgroup.center ↥L))
    (s : GL (Fin n) (ftF g)) (L' : Subgroup ↥(Unitary.SU (ftσ g) n)) (hL'L : L'.map ψ = L)
    (hL' : IsComponentOf L' ((Subgroup.centralizer ({s} : Set (GL (Fin n) (ftF g)))).comap
      (Unitary.SU (ftσ g) n).subtype))
    (hodd : Odd (orderOf s))
    (hsU : Unitary.conjTr (ftσ g) (s : Matrix (Fin n) (Fin n) (ftF g)) * Unitary.antidiag n *
      (s : Matrix (Fin n) (Fin n) (ftF g)) = Unitary.antidiag n) :
    g = 0 ∧ ∃ (r : ℕ) (ι : (ggU .PSU r (g + 1)).K →* ↥(Unitary.SU (ftσ g) n))
      (U : Matrix (Fin n) (Fin r) (ftF g)) (Lm : Matrix (Fin r) (Fin n) (ftF g))
      (e : Matrix (Fin n) (Fin n) (ftF g)),
      4 ≤ r ∧ Function.Injective ι ∧ ι.range = L' ∧ U * Lm = e ∧ Lm * U = 1 ∧
      (∀ y : ↥(Unitary.SU (ftσ g) r),
        ((ι y : GL (Fin n) (ftF g)) : Matrix (Fin n) (Fin n) (ftF g)) =
          U * ((y : GL (Fin r) (ftF g)) : Matrix (Fin r) (Fin r) (ftF g)) * Lm + (1 - e)) ∧
      Matrix.transpose (U.map (ftσ g).toRingHom) *
          (Unitary.antidiag n : Matrix (Fin n) (Fin n) (ftF g)) * U =
        (Unitary.antidiag r : Matrix (Fin r) (Fin r) (ftF g)) ∧
      Matrix.transpose (e.map (ftσ g).toRingHom) *
          (Unitary.antidiag n : Matrix (Fin n) (Fin n) (ftF g)) =
        (Unitary.antidiag n : Matrix (Fin n) (Fin n) (ftF g)) * e := by
  classical
  set S : Set (GL (Fin n) (ftF g)) := {s} with hSdef
  have hS : ∀ a ∈ S, ∀ b ∈ S, Commute a b := by
    intro a ha b hb
    rw [hSdef, Set.mem_singleton_iff] at ha hb
    rw [ha, hb]
  have hSU : ∀ a ∈ S, Unitary.conjTr (ftσ g) (a : Matrix (Fin n) (Fin n) (ftF g)) *
      Unitary.antidiag n * (a : Matrix (Fin n) (Fin n) (ftF g)) = Unitary.antidiag n := by
    intro a ha
    rw [hSdef, Set.mem_singleton_iff] at ha
    rw [ha]
    exact hsU
  have hoddS : ∀ a ∈ S, Odd (orderOf a) := by
    intro a ha
    rw [hSdef, Set.mem_singleton_iff] at ha
    rw [ha]
    exact hodd
  obtain ⟨ε, hε, hJε⟩ :=
    exists_isComponentOf_glBlockCentralizer_PSU (F := ftF g) (f := g + 1) n S hS hL'
  obtain ⟨e, he, heε, hsplit⟩ := exists_isPrimIdemIn_of_isPrimAdjIdemIn_PSU n g S hSU hS hε
  by_cases hdeg : 2 ≤ blockDegree (Algebra.adjoin (ftF g) (Units.val '' S)) e
  · exfalso
    obtain ⟨t', m, f', ht', hlt, hLM, -⟩ :=
      ggSixLSevenFieldExtCaseCl_PSU (card_ftF g) n ψ hψ S hSU hS hoddS hε hJε he heε hdeg
    rw [hL'L] at hLM
    obtain ⟨hf1, -, -⟩ := fieldTwo_typeDet hl hn1 hne hM (ht'.imp_right Or.inl) hLM
    omega
  have hdeg' : blockDegree (Algebra.adjoin (ftF g) (Units.val '' S)) e < 2 := by omega
  rcases hsplit with hee | ⟨-, hpair, hεeq⟩
  ·
    subst hee
    have hadj : formAdj (ftσ g).toRingHom (Unitary.antidiag n) e = e := hε.2.2.2.1
    obtain ⟨r, ι, U, Lm, hι, hrange, hgood, hUL, hLU, hform, hiso, hadjm⟩ :=
      exists_blockModel_selfDual_PSU_matrix n g S hS he hadj hdeg' hJε
    have hrange' : (ψ.comp ι).range = L := by
      rw [MonoidHom.range_comp, hrange, hL'L]
    have hker' : (ψ.comp ι).ker ≤ Subgroup.center (ggU .PSU r (g + 1)).K := by
      intro y hy
      exact Subgroup.comap_center_le_center hι (hψ hy)
    rcases hgood with ⟨hr3, hr3'⟩ | ⟨hr2, hq4⟩
    · have hadm : StatedLieAdmissible .PSU r 2 (g + 1) :=
        ⟨Nat.prime_two, by omega, hr3, fun h => hr3' ⟨(Prod.mk.inj h).1, (Prod.mk.inj h).2⟩⟩
      have hLM := RCKRP.irg_lieModel_quot (Or.inr (Or.inl rfl)) hadm (ψ.comp ι) hrange' hker'
      obtain ⟨hg1, -, -⟩ := fieldTwo_typeDet hl hn1 hne hM (Or.inr (Or.inl rfl)) hLM
      have hg0 : g = 0 := by omega
      subst hg0
      refine ⟨rfl, r, ι, U, Lm, e, ?_, hι, hrange, hUL, hLU, hform, hiso, hadjm⟩
      by_contra h4
      exact hr3' ⟨by omega, by norm_num⟩
    ·
      exfalso
      subst hr2
      obtain ⟨ζ, hζ0, hζ⟩ := CFSG.LieType.BorelTits.exists_unitaryInvolution_eq_neg (card_ftF g)
      have hk : Nat.card (CFSG.LieType.Steinberg.fixedSubfield (ftF g) 2 (g + 1)) = 2 ^ (g + 1) :=
        CFSG.LieType.Steinberg.card_fixedSubfield (card_ftF g)
      have hG : Nat.card (GaloisField 2 (g + 1)) = 2 ^ (g + 1) :=
        GaloisField.card 2 (g + 1) (by omega)
      let e₂ : GaloisField 2 (g + 1) ≃+* CFSG.LieType.Steinberg.fixedSubfield (ftF g) 2 (g + 1) :=
        CFSG.ClassicalInvolution.Upgrade.fieldIsoOfCard (hG.trans hk.symm)
      let χ : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 (g + 1)) →*
          ↥(Unitary.SU (ftσ g) 2) :=
        (CFSG.LieType.Steinberg.hypEquiv hζ0 hζ).toMonoidHom.comp
          (Matrix.SpecialLinearGroup.map e₂.toRingHom)
      have hmap_inj := SelectedRoot.slMap_injective e₂
      have hmap_surj := SelectedRoot.slMap_surjective e₂
      have hχinj : Function.Injective χ :=
        (CFSG.LieType.Steinberg.hypEquiv hζ0 hζ).injective.comp hmap_inj
      have hχsurj : Function.Surjective χ :=
        (CFSG.LieType.Steinberg.hypEquiv hζ0 hζ).surjective.comp hmap_surj
      let ι' : ↥(Unitary.SU (ftσ g) 2) →* ↥(Unitary.SU (ftσ g) n) := ι
      let φ : (ggU .PSL 2 (g + 1)).K →* X := (ψ.comp ι').comp χ
      have hφr : φ.range = L := by
        change ((ψ.comp ι').comp χ).range = L
        rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr hχsurj, ← MonoidHom.range_eq_map]
        exact hrange'
      have hφk : φ.ker ≤ Subgroup.center (ggU .PSL 2 (g + 1)).K := by
        intro y hy
        exact Subgroup.comap_center_le_center hχinj (hker' hy)
      have h4 : 4 ≤ 2 ^ (g + 1) := hq4
      have hadm : StatedLieAdmissible .PSL 2 2 (g + 1) := by
        refine ⟨Nat.prime_two, by omega, le_rfl, fun h => ?_, fun h => ?_⟩
        · have := (Prod.mk.inj h).2; omega
        · have := (Prod.mk.inj h).2; omega
      have hLM := RCKRP.irg_lieModel_quot (Or.inl rfl) hadm φ hφr hφk
      obtain ⟨hg1, -, -⟩ := fieldTwo_typeDet hl hn1 hne hM (Or.inl rfl) hLM
      have hg0 : g = 0 := by omega
      subst hg0
      norm_num at h4
  ·
    exfalso
    rw [hεeq] at hJε
    obtain ⟨k, ι, -, hcen, hrange, -⟩ :=
      exists_blockModelClosure_dualPair_PSU_explicitModel n g S hSU hS he hpair hdeg' hJε
    have hrange' : (ψ.comp ι).range = L := by
      rw [MonoidHom.range_comp, hrange, hL'L]
    have hker' : (ψ.comp ι).ker ≤ Subgroup.center (ggU .PSL (k + 1) (2 * (g + 1))).K := by
      intro y hy
      exact hcen y (hψ hy)
    rcases Nat.eq_zero_or_pos k with hk0 | hk1
    ·
      subst hk0
      have hsub :
          Subsingleton (Matrix.SpecialLinearGroup (Fin 1) (GaloisField 2 (2 * (g + 1)))) := by
        constructor
        intro a b
        have ha :
            (a : Matrix (Fin 1) (Fin 1) (GaloisField 2 (2 * (g + 1)))) default default = 1 := by
          have h := Matrix.SpecialLinearGroup.det_coe a
          rwa [Matrix.det_unique] at h
        have hb :
            (b : Matrix (Fin 1) (Fin 1) (GaloisField 2 (2 * (g + 1)))) default default = 1 := by
          have h := Matrix.SpecialLinearGroup.det_coe b
          rwa [Matrix.det_unique] at h
        ext i j
        rw [Subsingleton.elim i default, Subsingleton.elim j default, ha, hb]
      have hbot : L' = ⊥ := by
        rw [← hrange, eq_bot_iff]
        rintro _ ⟨y, rfl⟩
        have hy : y = 1 := @Subsingleton.elim _ hsub y 1
        rw [hy, map_one]
        exact Subgroup.one_mem _
      have hsimple := hL'.2.2.2
      subst hbot
      have : Subsingleton ↥(⊥ : Subgroup ↥(Unitary.SU (ftσ g) n)) := inferInstance
      exact (not_nontrivial_iff_subsingleton.mpr inferInstance) hsimple.toNontrivial
    · have h4 : 4 ≤ 2 ^ (2 * (g + 1)) := by
        calc (4 : ℕ) = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ (2 * (g + 1)) := Nat.pow_le_pow_right (by norm_num) (by omega)
      have hadm : StatedLieAdmissible .PSL (k + 1) 2 (2 * (g + 1)) := by
        refine ⟨Nat.prime_two, by omega, by omega, fun h => ?_, fun h => ?_⟩
        · have := (Prod.mk.inj h).2; omega
        · have := (Prod.mk.inj h).2; omega
      have hLM := RCKRP.irg_lieModel_quot (Or.inl rfl) hadm (ψ.comp ι) hrange' hker'
      obtain ⟨hf1, -, -⟩ := fieldTwo_typeDet hl hn1 hne hM (Or.inl rfl) hLM
      omega

theorem ggSecFiveQTwoFieldTwoSelectedAt_PSU : GGSecFiveQTwoFieldTwoSelectedAt .PSU := by
  intro G _ _ B Bs x L D J hC hq n f ψ hpres hdiag
  obtain ⟨⟨hadm, -⟩, ⟨hrange, hker⟩, -, -⟩ := hpres
  obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by have := hadm.2.1; omega⟩
  have hn : 3 ≤ n := hadm.2.2.1
  let ψ₀ : ↥(Unitary.SU (ftσ g) n) →* G := ψ
  have hψ : ψ₀.ker ≤ Subgroup.center _ := hker
  have hdiag' : GGPsiInnerDiag (Unitary.rootDatum (card_ftF g) n) ψ₀ x := hdiag
  obtain ⟨ζ, hζ⟩ := Unitary.exists_traceZero_ne_zero (card_ftF g)
  have hgen : ⨆ γ ∈ (Unitary.rootDatum (card_ftF g) n).roots,
      (Unitary.rootDatum (card_ftF g) n).rootGroup γ = ⊤ :=
    (Unitary.isCTGroupDatum (card_ftF g) n (by omega) ζ hζ).iSup_eq_top
  have hxN := mem_normalizer_of_ggPsiInnerDiag hgen hdiag'
  have hsstar := hC.1.2.2.2.2.2.2.1
  have hx3 : x ^ 3 = 1 := hsstar.1.1.2 x hsstar.2.1
  have hL : IsComponentOf L (ψ₀.range ⊓ Subgroup.centralizer {x}) := by
    change IsComponentOf L (ψ.range ⊓ Subgroup.centralizer {x})
    rw [hrange]
    exact hC.isComponentOf_ggG0_inf
  obtain ⟨s, L', hL'L, hL', hodd, hsU⟩ := exists_lift_component n g hn ψ₀ hψ hxN hdiag' hx3 hL
  obtain ⟨lab, hl, hn1, hne, -, hM⟩ := hC.exists_markedModel_of_qTwo hq
  obtain ⟨hg0, r, ι, U, Lm, e, hr4, hι, hιr, hUL, hLU, hform, hiso, hadjm⟩ :=
    selfDual_of_component n g ψ₀ hψ hl hn1 hne hM s L' hL'L hL' hodd hsU
  subst hg0
  have hn4 : 4 ≤ n := by
    by_contra h4
    have h3 : n = 3 := by omega
    exact hadm.2.2.2 (by rw [h3]; norm_num)
  have hrangeL : (ψ₀.comp ι).range = L := by rw [MonoidHom.range_comp, hιr, hL'L]
  have hkerL : (ψ₀.comp ι).ker ≤ Subgroup.center (ggU .PSU r (0 + 1)).K := by
    intro y hy
    exact Subgroup.comap_center_le_center hι (hψ hy)
  have hr0 : (⟨0, by omega⟩ : Fin r) ≠ Fin.rev ⟨0, by omega⟩ := by
    intro h
    have := congrArg Fin.val h
    simp only [Fin.val_rev] at this
    omega
  have hn0 : (⟨0, by omega⟩ : Fin n) ≠ Fin.rev ⟨0, by omega⟩ := by
    intro h
    have := congrArg Fin.val h
    simp only [Fin.val_rev] at this
    omega
  set v : Fin n → ftF 0 := U *ᵥ Pi.single (⟨0, by omega⟩ : Fin r) 1 with hvdef
  set w : Fin n → ftF 0 := U *ᵥ Pi.single (Fin.rev (⟨0, by omega⟩ : Fin r)) 1 with hwdef
  have hantidiag : ∀ a b : Fin r, (Unitary.antidiag r : Matrix (Fin r) (Fin r) (ftF 0)) a b =
      if b = Fin.rev a then 1 else 0 := fun a b => rfl
  have hv : Matrix.vecMul (fun i => ftσ 0 (v i)) (Unitary.antidiag n) ⬝ᵥ v = 0 := by
    rw [hvdef, form_mulVec_single, hiso, hantidiag, if_neg hr0]
  have hw : Matrix.vecMul (fun i => ftσ 0 (w i)) (Unitary.antidiag n) ⬝ᵥ w = 0 := by
    rw [hwdef, form_mulVec_single, hiso, hantidiag, if_neg]
    intro h
    exact hr0 (by rw [Fin.rev_rev] at h; exact h.symm)
  have hvw : Matrix.vecMul (fun i => ftσ 0 (v i)) (Unitary.antidiag n) ⬝ᵥ w = 1 := by
    rw [hvdef, hwdef, form_mulVec_single, hiso, hantidiag, if_pos rfl]
  obtain ⟨u₀, α, β, hα0, -, hu0, hu1⟩ :=
    Geo.exists_su_mulVec_single_eq_smul (card_ftF 0) hn0 v w hv hw hvw
  rw [hvdef] at hu0
  rw [hwdef] at hu1
  have hF4 : Nat.card (ftF 0) = 4 := by rw [card_ftF]; norm_num
  have hα3 : α ^ 3 = 1 := by
    have := Fintype.ofFinite (ftF 0)
    have h := FiniteField.pow_card_sub_one_eq_one α hα0
    rwa [← Nat.card_eq_fintype_card, hF4] at h
  have hσα : ftσ 0 α = α ^ 2 := by
    rw [CFSG.LieType.BorelTits.unitaryInvolution_apply]
    norm_num
  have hα : ftσ 0 α * α = 1 := by rw [hσα, ← pow_succ, hα3]
  have hu₀ := (Unitary.mem_SU.mp u₀.2).2
  have hiso_u : Matrix.transpose (((u₀ : GL (Fin n) (ftF 0)) : Matrix (Fin n) (Fin n) (ftF 0)).map
      (ftσ 0).toRingHom) * (Unitary.antidiag n : Matrix (Fin n) (Fin n) (ftF 0)) *
      ((u₀ : GL (Fin n) (ftF 0)) : Matrix (Fin n) (Fin n) (ftF 0)) =
      (Unitary.antidiag n : Matrix (Fin n) (Fin n) (ftF 0)) := hu₀
  have hαβ : ftσ 0 α * β = 1 := by
    have h := form_mulVec_single (ftσ 0) (Unitary.antidiag n)
      ((u₀ : GL (Fin n) (ftF 0)) : Matrix (Fin n) (Fin n) (ftF 0)) ⟨0, by omega⟩
      (Fin.rev ⟨0, by omega⟩)
    rw [hiso_u, hu0, hu1, form_smul_smul, ← hvdef, ← hwdef, hvw, mul_one] at h
    rw [h]
    show (Unitary.antidiag n : Matrix (Fin n) (Fin n) (ftF 0)) ⟨0, _⟩ (Fin.rev ⟨0, _⟩) = 1
    exact if_pos rfl
  have hβ : β = α := by
    have hσ0 : ftσ 0 α ≠ 0 := (map_ne_zero (ftσ 0)).mpr hα0
    exact mul_left_cancel₀ hσ0 (hαβ.trans hα.symm)
  rw [hβ] at hu1
  obtain ⟨γ, model₀, hm₀⟩ := SelectedRoot.exists_selectedModel_PSU_chart (card_ftF 0) hn4
  obtain ⟨δ, model₁, hm₁⟩ := SelectedRoot.exists_selectedModel_PSU_chart (card_ftF 0) hr4
  have hk : Nat.card (CFSG.LieType.Steinberg.fixedSubfield (ftF 0) 2 (0 + 1)) = 2 ^ (0 + 1) :=
    CFSG.LieType.Steinberg.card_fixedSubfield (card_ftF 0)
  have hG1 : Nat.card (GaloisField 2 1) = 2 ^ (0 + 1) := by
    rw [GaloisField.card 2 1 one_ne_zero]
  let e₁ : GaloisField 2 1 ≃+* CFSG.LieType.Steinberg.fixedSubfield (ftF 0) 2 (0 + 1) :=
    CFSG.ClassicalInvolution.Upgrade.fieldIsoOfCard (hG1.trans hk.symm)
  have hu : ((u₀ : GL (Fin n) (ftF 0)) : Matrix (Fin n) (Fin n) (ftF 0)) *
      (((u₀⁻¹ : ↥(Unitary.SU (ftσ 0) n)) : GL (Fin n) (ftF 0)) : Matrix (Fin n) (Fin n) (ftF 0)) =
      1 := by
    rw [← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one, Units.val_one]
  have hpt : ∀ A : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 1),
      (MulAut.conj u₀) ((model₀.congrField e₁).phi A) = ι ((model₁.congrField e₁).phi A) := by
    intro A
    rw [SelectedRoot.SelectedSL2Model.congrField_phi_apply,
      SelectedRoot.SelectedSL2Model.congrField_phi_apply, MulAut.conj_apply]
    apply Subtype.ext
    apply Units.ext
    rw [hform]
    simp only [Subgroup.coe_mul, Units.val_mul]
    rw [hm₀, hm₁]
    exact conj_embM_eq (ftσ 0) (by omega) (by omega) U Lm e hUL hLU hiso hadjm _ _ hu hiso_u α
      hα hu0 hu1 _
  refine ⟨.PSU, r, ψ₀.comp ι, ?_, ?_, hkerL, hrangeL, γ, δ, model₀.congrField e₁,
    model₁.congrField e₁, u₀, ?_⟩
  · exact ⟨Nat.prime_two, le_rfl, by omega, fun h => by have := (Prod.mk.inj h).1; omega⟩
  · show 2 ≤ r / 2
    omega
  · congr 1
    ext A
    exact congrArg ψ₀ (hpt A)

end Cert

end FieldTwoPSU

end CFSG.StandardType

end
