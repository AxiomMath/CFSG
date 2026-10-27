module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveFieldTwoPSL
public import CFSG.LocalAnalysis.StandardType.GGSecFiveFieldTwoPSU
public import CFSG.LocalAnalysis.StandardType.GGSecFiveFieldTwoSpChart
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeF1PSp
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeSmall
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.BlockModelSelfDualPSp
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.BlockModelSelfDualTwoPSp
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.BlockModelDualPairPSp
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.BlockDegreeOneGFTwo
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.GeoPSpRoot
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotTorus
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockSympTypes
public import CFSG.Quasithin.Vol2.Ch7Prop711Grp
import all CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIpFPSpCases

public section

namespace CFSG.StandardType

namespace FieldTwoPSp

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal
  CFSG.StandardType.ClassicalPosition
open CFSG.LieType.Steinberg (sl2Lower)
open CFSG.StandardType.RankOneXfer (sl2UpperUniSub)
open scoped Matrix

theorem not_isSolvable_of_isComponentOf {X : Type} [Group X] {J H : Subgroup X}
    (hJ : IsComponentOf J H) : ¬ Group.IsSolvable J := by
  obtain ⟨-, -, hperf, hsimple⟩ := hJ
  have : Nontrivial (↥J ⧸ Subgroup.center ↥J) := hsimple.toNontrivial
  have : Nontrivial J :=
    Function.Surjective.nontrivial (QuotientGroup.mk'_surjective (Subgroup.center J))
  have : Group.IsPerfect J := Group.IsPerfect.mk hperf
  exact Group.IsPerfect.not_isSolvable J

theorem isSolvable_range {A B : Type*} [Group A] [Group B] (ι : A →* B)
    [Group.IsSolvable A] : Group.IsSolvable ι.range :=
  Group.isSolvable_of_surjective (f := ι.rangeRestrict) ι.rangeRestrict_surjective

private theorem isPerfect_of_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    [hB : Group.IsPerfect B] : Group.IsPerfect A := by
  rw [Group.isPerfect_def] at hB ⊢
  have h1 : (commutator B).map e.symm.toMonoidHom = commutator A := by
    unfold commutator
    rw [Subgroup.map_commutator, Subgroup.map_top_of_surjective e.symm.toMonoidHom
      e.symm.surjective]
  rw [hB] at h1
  rw [← h1, Subgroup.map_top_of_surjective e.symm.toMonoidHom e.symm.surjective]

theorem injective_of_center {A B : Type*} [Group A] [Group B] (ι : A →* B)
    (hcent : ∀ y, ι y ∈ Subgroup.center B → y ∈ Subgroup.center A)
    (hZ : Subgroup.center A = ⊥) : Function.Injective ι := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro y hy
  rw [← hZ]
  exact hcent y (by rw [MonoidHom.mem_ker.mp hy]; exact Subgroup.one_mem _)

private theorem J_mul_J {n : ℕ} {F : Type} [Field F] [CharP F 2] :
    (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) *
      Matrix.fromBlocks 0 1 (-1) 0 = 1 := by
  rw [Matrix.fromBlocks_multiply]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> simp [Matrix.one_apply, CharTwo.neg_eq]

section Cert


theorem isEmpty_A6 {X : Type} [Group X] {n f : ℕ}
    (ψ : ↥(CFSG.Open.StatedSp n (GaloisField 2 f)) →* X) (hψ : ψ.ker ≤ Subgroup.center _)
    {lab : LargeEvenLabel} (hnb : lab.tag ≠ .B2der)
    {L' : Subgroup ↥(CFSG.Open.StatedSp n (GaloisField 2 f))}
    (hM : MarkedModel lab (↥(L'.map ψ) ⧸ Subgroup.center ↥(L'.map ψ))) :
    IsEmpty (↥L' ≃* alternatingGroup (Fin 6)) := by
  refine ⟨fun ξ => ?_⟩
  have hinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    exact hψ.trans (CFSG.SeitzReduction.SymplecticPilot.center_statedSp_eq_bot n).le
  let ξL : ↥(L'.map ψ) ≃* alternatingGroup (Fin 6) :=
    (L'.equivMapOfInjective ψ hinj).symm.trans ξ
  have hZA : Subgroup.center (alternatingGroup (Fin 6)) = ⊥ :=
    alternatingGroup.center_eq_bot (by norm_num)
  have h1 := Subgroup.map_center_eq ξL
  rw [hZA] at h1
  have hZ : Subgroup.center ↥(L'.map ψ) = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective _ ξL.injective).mp h1
  have hcard : Nat.card (↥(L'.map ψ) ⧸ Subgroup.center ↥(L'.map ψ)) = 360 := by
    rw [Nat.card_congr ((QuotientGroup.quotientMulEquivOfEq hZ).trans
      QuotientGroup.quotientBot).toEquiv, Nat.card_congr ξL.toEquiv, nat_card_alternatingGroup,
      Nat.card_fin]
    decide
  exact ggMarkedModel_card_ne_three_sixty hnb hM hcard

theorem selfDual_one {X : Type} [Group X] {n f : ℕ} (hf : 1 ≤ f)
    (ψ : ↥(CFSG.Open.StatedSp n (GaloisField 2 f)) →* X) (hψ : ψ.ker ≤ Subgroup.center _)
    {lab : LargeEvenLabel} (hl : LargeEvenInLambda2 lab) (hn1 : lab.n = 1)
    (hne : lab ≠ ⟨.twD, 2, 1⟩) (hnb : lab.tag ≠ .B2der)
    (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f))) (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f))
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) e =
      e) (hdeg : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 2)
    {L' : Subgroup ↥(CFSG.Open.StatedSp n (GaloisField 2 f))}
    (hJe : IsComponentOf L'
      ⁅glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S e,
        glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S e⁆)
    (hM : MarkedModel lab (↥(L'.map ψ) ⧸ Subgroup.center ↥(L'.map ψ))) :
    f = 1 ∧ ∃ (r : ℕ) (ι : (ggU .PSp r f).K →* ↥(CFSG.Open.StatedSp n (GaloisField 2 f)))
      (β₀ : Fin (ggU .PSp r f).D.rank → ℤ),
      3 ≤ r ∧ Function.Injective ι ∧ GGLongRoot (ggU .PSp r f).D β₀ ∧ ι.range = L' ∧
      ∃ v w : (Fin n ⊕ Fin n) → GaloisField 2 f,
        v ⬝ᵥ (Matrix.fromBlocks 0 1 (-1) 0 :
          Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) *ᵥ w = 1 ∧
        (((ggU .PSp r f).D.rootGroup β₀).map ι).map
            (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype =
          matTransvGroup v ((Matrix.fromBlocks 0 1 (-1) 0 :
            Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) *ᵥ v) ∧
        (((ggU .PSp r f).D.rootGroup (-β₀)).map ι).map
            (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype =
          matTransvGroup w ((Matrix.fromBlocks 0 1 (-1) 0 :
            Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) *ᵥ w) := by
  obtain ⟨r, ι, β₀, -, hlong, hcent, hrange, v, w, hvw, hX, hX'⟩ :=
    exists_blockModel_selfDual_PSp_explicit n f S hS he hadj hdeg hJe (isEmpty_A6 ψ hψ hnb hM)
  have hinj : Function.Injective ι :=
    injective_of_center ι hcent (CFSG.SeitzReduction.SymplecticPilot.center_statedSp_eq_bot r)
  have hns := not_isSolvable_of_isComponentOf hJe
  have hq : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  let eL : (ggU .PSp r f).K ≃* ↥L' :=
    (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)
  have hrange' : (ψ.comp ι).range = L'.map ψ := by rw [MonoidHom.range_comp, hrange]
  have hker' : (ψ.comp ι).ker ≤ Subgroup.center (ggU .PSp r f).K := fun y hy =>
    Subgroup.comap_center_le_center hinj (hψ hy)
  have hsol : Group.IsSolvable (ggU .PSp r f).K → False := fun h =>
    hns (Group.isSolvable_of_surjective (f := eL.toMonoidHom) eL.surjective)
  have hf1 : f = 1 := by
    by_contra hf1
    have hq4 : 4 ≤ 2 ^ f := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) (by omega)
    rcases Nat.lt_or_ge r 2 with hr2 | hr2
    · rcases Nat.lt_or_ge r 1 with hr1 | hr1
      · exact hsol (CFSG.AGLEmbedding.LeviBlock.spFlag_isSolvable_Sp (Or.inl (by omega)))
      ·
        obtain rfl : r = 1 := by omega
        obtain ⟨χ⟩ := RCKRP.rckRP_nonempty_mulEquiv_PSL_two_PSp_one (f := f) hf
        let φ : (ggU .PSL 2 f).K →* X := (ψ.comp ι).comp χ.toMonoidHom
        have hφr : φ.range = L'.map ψ := by
          rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr χ.surjective,
            ← MonoidHom.range_eq_map, hrange']
        have hφk : φ.ker ≤ Subgroup.center (ggU .PSL 2 f).K := fun y hy =>
          Subgroup.comap_center_le_center χ.injective (hker' hy)
        have hadm : StatedLieAdmissible .PSL 2 2 f :=
          ⟨Nat.prime_two, hf, le_rfl, fun h => by have := (Prod.mk.inj h).2; omega,
            fun h => by have := (Prod.mk.inj h).2; omega⟩
        have hLM := RCKRP.irg_lieModel_quot (Or.inl rfl) hadm φ hφr hφk
        exact hf1 (fieldTwo_typeDet hl hn1 hne hM (Or.inl rfl) hLM).1
    · have hadm : StatedLieAdmissible .PSp r 2 f :=
        ⟨Nat.prime_two, hf, hr2, fun h => by have := (Prod.mk.inj h).2; omega⟩
      have hLM := RCKRP.irg_lieModel_quot (Or.inr (Or.inr (Or.inl rfl))) hadm (ψ.comp ι)
        hrange' hker'
      exact hf1 (fieldTwo_typeDet hl hn1 hne hM (Or.inr (Or.inr (Or.inl rfl))) hLM).1
  subst hf1
  have hq2 : Nat.card (GaloisField 2 1) = 2 := by rw [hq]; norm_num
  refine ⟨rfl, r, ι, β₀, ?_, hinj, hlong, hrange, v, w, hvw, hX, hX'⟩
  by_contra hr3
  rcases Nat.lt_or_ge r 2 with hr2 | hr2
  · refine hsol (CFSG.AGLEmbedding.LeviBlock.spFlag_isSolvable_Sp ?_)
    rcases Nat.lt_or_ge r 1 with h | h
    · exact Or.inl (by omega)
    · exact Or.inr ⟨by omega, hq2⟩
  ·
    obtain rfl : r = 2 := by omega
    obtain ⟨-, -, hperf, -⟩ := hJe
    have : Group.IsPerfect L' := Group.IsPerfect.mk hperf
    have : Group.IsPerfect (ggU .PSp 2 1).K := isPerfect_of_mulEquiv eL
    exact CFSG.Quasithin.H13.Prop711.not_isPerfect_statedSp_two hq2 this

theorem exists_PSL_two_of_PSU_two {X : Type} [Group X] {f' : ℕ} (hf' : 1 ≤ f')
    (π : (ggU .PSU 2 f').K →* X) :
    ∃ φ : (ggU .PSL 2 f').K →* X, φ.range = π.range ∧
      (π.ker ≤ Subgroup.center (ggU .PSU 2 f').K →
        φ.ker ≤ Subgroup.center (ggU .PSL 2 f').K) := by
  obtain ⟨g, rfl⟩ : ∃ g, f' = g + 1 := ⟨f' - 1, by omega⟩
  have hcard := CFSG.LieType.Universal.card_galoisField_two_mul 2 (g + 1) (by omega)
  obtain ⟨ζ, hζ0, hζ⟩ := CFSG.LieType.BorelTits.exists_unitaryInvolution_eq_neg hcard
  have hk := CFSG.LieType.Steinberg.card_fixedSubfield hcard
  have hG : Nat.card (GaloisField 2 (g + 1)) = 2 ^ (g + 1) :=
    GaloisField.card 2 (g + 1) (by omega)
  let e₂ : GaloisField 2 (g + 1) ≃+*
      CFSG.LieType.Steinberg.fixedSubfield (GaloisField 2 (2 * (g + 1))) 2 (g + 1) :=
    CFSG.ClassicalInvolution.Upgrade.fieldIsoOfCard (hG.trans hk.symm)
  let χ : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 (g + 1)) →*
      ↥(Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2
        (g + 1)) 2) :=
    (CFSG.LieType.Steinberg.hypEquiv hζ0 hζ).toMonoidHom.comp
      (Matrix.SpecialLinearGroup.map e₂.toRingHom)
  have hχinj : Function.Injective χ :=
    (CFSG.LieType.Steinberg.hypEquiv hζ0 hζ).injective.comp (SelectedRoot.slMap_injective e₂)
  have hχsurj : Function.Surjective χ :=
    (CFSG.LieType.Steinberg.hypEquiv hζ0 hζ).surjective.comp (SelectedRoot.slMap_surjective e₂)
  let π' : ↥(Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution
      (GaloisField 2 (2 * (g + 1))) 2 (g + 1)) 2) →* X := π
  let φ : (ggU .PSL 2 (g + 1)).K →* X := π'.comp χ
  refine ⟨φ, ?_, fun hk' y hy => Subgroup.comap_center_le_center hχinj (hk' hy)⟩
  change (π'.comp χ).range = π.range
  rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr hχsurj, ← MonoidHom.range_eq_map]
  rfl

theorem selfDual_two {X : Type} [Group X] {n f : ℕ} (hf : 1 ≤ f)
    (ψ : ↥(CFSG.Open.StatedSp n (GaloisField 2 f)) →* X) (hψ : ψ.ker ≤ Subgroup.center _)
    {lab : LargeEvenLabel} (hl : LargeEvenInLambda2 lab) (hn1 : lab.n = 1)
    (hne : lab ≠ ⟨.twD, 2, 1⟩)
    (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ CFSG.Open.StatedSp n (GaloisField 2 f))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f))
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) e =
      e)
    (hdeg₁ : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hdeg₂ : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 4)
    {L' : Subgroup ↥(CFSG.Open.StatedSp n (GaloisField 2 f))}
    (hJe : IsComponentOf L'
      ⁅glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S e,
        glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S e⁆)
    (hM : MarkedModel lab (↥(L'.map ψ) ⧸ Subgroup.center ↥(L'.map ψ))) :
    f = 1 ∧ ∃ (r : ℕ) (ι : (ggU .PSU r (max f 1)).K →* ↥(CFSG.Open.StatedSp n (GaloisField 2 f)))
      (β₀ : Fin (ggU .PSU r (max f 1)).D.rank → ℤ),
      4 ≤ r ∧ Function.Injective ι ∧ GGLongRoot (ggU .PSU r (max f 1)).D β₀ ∧ ι.range = L' ∧
      ∃ a₁ a₂ b₁ b₂ : (Fin n ⊕ Fin n) → GaloisField 2 f, ShortPairs a₁ a₂ b₁ b₂ ∧
        (((ggU .PSU r (max f 1)).D.rootGroup β₀).map ι).map
            (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype =
          altSiegelGroup (Matrix.fromBlocks 0 1 (-1) 0 :
            Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) a₁ a₂ ∧
        (((ggU .PSU r (max f 1)).D.rootGroup (-β₀)).map ι).map
            (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype =
          altSiegelGroup (Matrix.fromBlocks 0 1 (-1) 0 :
            Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) b₁ b₂ := by
  obtain ⟨r, ι, β₀, -, hlong, -, hrange, ⟨hinj, hr2, hnq⟩, a₁, a₂, b₁, b₂, h₁, h₂, h₃, hX, hX'⟩ :=
    exists_blockModel_selfDualTwo_PSp_explicit_inj n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe
  have hP : ShortPairs a₁ a₂ b₁ b₂ := ⟨h₁, h₂, h₃⟩
  have hmax : max f 1 = f := max_eq_left hf
  have hrange' : (ψ.comp ι).range = L'.map ψ := by rw [MonoidHom.range_comp, hrange]
  have hker' : (ψ.comp ι).ker ≤ Subgroup.center (ggU .PSU r (max f 1)).K := fun y hy =>
    Subgroup.comap_center_le_center hinj (hψ hy)
  have hf1 : f = 1 := by
    by_contra hf1
    have hq4 : 4 ≤ 2 ^ max f 1 := by
      rw [hmax]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) (by omega)
    rcases Nat.lt_or_ge r 3 with hr3 | hr3
    ·
      obtain rfl : r = 2 := by omega
      obtain ⟨φ, hφr, hφk⟩ := exists_PSL_two_of_PSU_two (le_max_right f 1) (ψ.comp ι)
      have hadm : StatedLieAdmissible .PSL 2 2 (max f 1) :=
        ⟨Nat.prime_two, le_max_right f 1, le_rfl, fun h => by have := (Prod.mk.inj h).2; omega,
          fun h => by have := (Prod.mk.inj h).2; omega⟩
      have hLM := RCKRP.irg_lieModel_quot (Or.inl rfl) hadm φ (hφr.trans hrange') (hφk hker')
      have := (fieldTwo_typeDet hl hn1 hne hM (Or.inl rfl) hLM).1
      omega
    · have hadm : StatedLieAdmissible .PSU r 2 (max f 1) :=
        ⟨Nat.prime_two, le_max_right f 1, hr3, fun h => by have := (Prod.mk.inj h).2; omega⟩
      have hLM := RCKRP.irg_lieModel_quot (Or.inr (Or.inl rfl)) hadm (ψ.comp ι) hrange' hker'
      have := (fieldTwo_typeDet hl hn1 hne hM (Or.inr (Or.inl rfl)) hLM).1
      omega
  subst hf1
  have hr4 : 4 ≤ r := by
    rcases hnq with h | h
    · exact absurd (by norm_num) h
    · exact h
  exact ⟨rfl, r, ι, β₀, hr4, hinj, hlong, hrange, a₁, a₂, b₁, b₂, hP, hX, hX'⟩

theorem dualPair_one_false {X : Type} [Group X] {n f : ℕ} (hf : 1 ≤ f)
    (ψ : ↥(CFSG.Open.StatedSp n (GaloisField 2 f)) →* X) (hψ : ψ.ker ≤ Subgroup.center _)
    {lab : LargeEvenLabel} (hl : LargeEvenInLambda2 lab) (hn1 : lab.n = 1)
    (hne : lab ≠ ⟨.twD, 2, 1⟩)
    (s : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) (hs : s ∈ CFSG.Open.StatedSp n (GaloisField 2 f))
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' {s})) e)
    (hpair : formAdj (RingHom.id (GaloisField 2 f))
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) e ≠
      e)
    (hdeg : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' {s})) e < 2)
    {L' : Subgroup ↥(CFSG.Open.StatedSp n (GaloisField 2 f))}
    (hJe : IsComponentOf L'
      ⁅glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) {s}
        (e + formAdj (RingHom.id (GaloisField 2 f)) (Matrix.fromBlocks 0 1 (-1) 0 :
          Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) e),
        glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) {s}
          (e + formAdj (RingHom.id (GaloisField 2 f)) (Matrix.fromBlocks 0 1 (-1) 0 :
            Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) e)⁆)
    (hM : MarkedModel lab (↥(L'.map ψ) ⧸ Subgroup.center ↥(L'.map ψ))) : False := by
  have hSU : ∀ t ∈ ({s} : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f))),
      t ∈ CFSG.Open.StatedSp n (GaloisField 2 f) := by
    intro t ht
    rw [Set.mem_singleton_iff] at ht
    rw [ht]
    exact hs
  have hS : ∀ t ∈ ({s} : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f))),
      ∀ t' ∈ ({s} : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f))), Commute t t' := by
    intro t ht t' ht'
    rw [Set.mem_singleton_iff] at ht ht'
    rw [ht, ht']
  obtain ⟨k, ι, -, -, -, hcent, hrange, -⟩ :=
    exists_blockModel_dualPair_PSp_explicit n f {s} hSU hS he hpair hdeg hJe
  have hns := not_isSolvable_of_isComponentOf hJe
  have hrange' : (ψ.comp ι).range = L'.map ψ := by rw [MonoidHom.range_comp, hrange]
  have hker' : (ψ.comp ι).ker ≤ Subgroup.center (ggU .PSL (k + 1) f).K := fun y hy =>
    hcent y (hψ hy)
  have hf1 : f = 1 := by
    by_contra hf1
    have hq4 : 4 ≤ 2 ^ f := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) (by omega)
    rcases Nat.eq_zero_or_pos k with hk0 | hk1
    ·
      subst hk0
      have hsub : Subsingleton (Matrix.SpecialLinearGroup (Fin 1) (GaloisField 2 f)) := by
        constructor
        intro a b
        have ha : (a : Matrix (Fin 1) (Fin 1) (GaloisField 2 f)) default default = 1 := by
          have h := Matrix.SpecialLinearGroup.det_coe a
          rwa [Matrix.det_unique] at h
        have hb : (b : Matrix (Fin 1) (Fin 1) (GaloisField 2 f)) default default = 1 := by
          have h := Matrix.SpecialLinearGroup.det_coe b
          rwa [Matrix.det_unique] at h
        ext i j
        rw [Subsingleton.elim i default, Subsingleton.elim j default, ha, hb]
      have hsolA : Group.IsSolvable (ggU .PSL (0 + 1) f).K := by
        have : Subsingleton (ggU .PSL (0 + 1) f).K := hsub
        infer_instance
      have : Group.IsSolvable ι.range := @isSolvable_range _ _ _ _ ι hsolA
      exact hns (hrange ▸ this)
    · have hadm : StatedLieAdmissible .PSL (k + 1) 2 f :=
        ⟨Nat.prime_two, hf, by omega, fun h => by have := (Prod.mk.inj h).2; omega,
          fun h => by have := (Prod.mk.inj h).2; omega⟩
      have hLM := RCKRP.irg_lieModel_quot (Or.inl rfl) hadm (ψ.comp ι) hrange' hker'
      exact hf1 (fieldTwo_typeDet hl hn1 hne hM (Or.inl rfl) hLM).1
  subst hf1
  have hJ : IsUnit (Matrix.fromBlocks 0 1 (-1) 0 :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 1)).det :=
    Matrix.isUnit_det_of_left_inverse J_mul_J
  exact hpair (formAdj_eq_self_of_blockDegree_lt_two_gf2 hJ
    (CFSG.Open.StatedAPI.mem_statedSp_iff.mp hs) he hdeg)

theorem fieldExt_false {X : Type} [Group X] {n f : ℕ} (hf : 1 ≤ f)
    (ψ : ↥(CFSG.Open.StatedSp n (GaloisField 2 f)) →* X) (hψ : ψ.ker ≤ Subgroup.center _)
    {lab : LargeEvenLabel} (hl : LargeEvenInLambda2 lab) (hn1 : lab.n = 1)
    (hne : lab ≠ ⟨.twD, 2, 1⟩)
    (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ CFSG.Open.StatedSp n (GaloisField 2 f))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {ε e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (hε : IsPrimAdjIdemIn (RingHom.id (GaloisField 2 f))
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f))
      (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) ε)
    {L' : Subgroup ↥(CFSG.Open.StatedSp n (GaloisField 2 f))}
    (hJe : IsComponentOf L'
      ⁅glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S ε,
        glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S ε⁆)
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e) (heε : e * ε = e)
    (hdeg : (e = ε ∧ 4 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e) ∨
      (e ≠ ε ∧ 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e))
    (hM : MarkedModel lab (↥(L'.map ψ) ⧸ Subgroup.center ↥(L'.map ψ))) : False := by
  obtain ⟨t', m', f', hlt, ht', hLM⟩ :=
    RCKC1.rckIIp_PSp_component_model_PSL_or_PSU hf ψ hψ S hSU hS hodd hε hJe he heε hdeg
  have := (fieldTwo_typeDet hl hn1 hne hM (ht'.imp_right Or.inl) hLM).1
  omega

theorem ggSecFiveQTwoFieldTwoSelectedAt_PSp : GGSecFiveQTwoFieldTwoSelectedAt .PSp := by
  intro G _ _ B Bs x L D J hC hq n f ψ hpres hdiag
  obtain ⟨⟨hadm, -⟩, ⟨hrange, hker⟩, -, -⟩ := hpres
  have hf : 1 ≤ f := hadm.2.1
  have hn : 2 ≤ n := hadm.2.2.1
  let ψ₀ : ↥(CFSG.Open.StatedSp n (GaloisField 2 f)) →* G := ψ
  have hψ : ψ₀.ker ≤ Subgroup.center _ := hker
  have hgen : ⨆ γ ∈ (ggU .PSp n f).D.roots, (ggU .PSp n f).D.rootGroup γ = ⊤ :=
    (Symplectic.isCTGroupDatum n (GaloisField 2 f)).iSup_eq_top
  have hxN := mem_normalizer_of_ggPsiInnerDiag hgen hdiag
  have hsstar := hC.1.2.2.2.2.2.2.1
  have hx3 : x ^ 3 = 1 := hsstar.1.1.2 x hsstar.2.1
  have hL : IsComponentOf L (ψ.range ⊓ Subgroup.centralizer {x}) := by
    rw [hrange]
    exact hC.isComponentOf_ggG0_inf
  obtain ⟨s, hs, -, hsodd, ε, hε, ⟨e, he, heε, hcase⟩, L', hL'comp, hL'map⟩ :=
    RCKRP.rckF1_PSp Nat.prime_three (by norm_num) hx3 hf ψ rfl hker hxN hdiag hL
  obtain ⟨lab, hl, hn1, hne, hnb, hM⟩ := hC.exists_markedModel_of_qTwo hq
  rw [← hL'map] at hM
  have hSU : ∀ a ∈ ({s} : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f))),
      a ∈ CFSG.Open.StatedSp n (GaloisField 2 f) := by
    intro a ha
    rw [Set.mem_singleton_iff] at ha
    rw [ha]
    exact hs
  have hS : ∀ a ∈ ({s} : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f))),
      ∀ b ∈ ({s} : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f))), Commute a b := by
    intro a ha b hb
    rw [Set.mem_singleton_iff] at ha hb
    rw [ha, hb]
  have hoddS : ∀ a ∈ ({s} : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f))), Odd (orderOf a) := by
    intro a ha
    rw [Set.mem_singleton_iff] at ha
    rw [ha]
    exact hsodd
  rcases hcase with rfl | ⟨hne', hpair, hεeq⟩
  · have hadj := hε.2.2.2.1
    by_cases hdeg2 : blockDegree (Algebra.adjoin (GaloisField 2 f)
        (Units.val '' ({s} : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f))))) e < 2
    ·
      obtain ⟨hf1, r, ι, β₀, hr3, hinj, hlong, hιr, v, w, hvw, hX, hX'⟩ :=
        selfDual_one hf ψ₀ hψ hl hn1 hne hnb _ hS he hadj hdeg2 hL'comp hM
      subst hf1
      have hvw' : CFSG.RankThree.Classical.spForm n (GaloisField 2 1) v w = 1 := by
        rw [CFSG.RankThree.Classical.spForm_apply]
        exact hvw
      let c := CFSG.LieType.SeitzGeneration.RootPair.spSL2Hom hvw'
      have hcU : (sl2UpperUniSub (GaloisField 2 1)).map c =
          ((ggU .PSp r 1).D.rootGroup β₀).map ι := by
        apply Subgroup.map_injective (Subgroup.subtype_injective _)
        rw [spSL2Hom_sl2Upper_map hvw', hX]
      have hcL : ∀ t, c (sl2Lower t) ∈ ι.range := by
        intro t
        have hmem := spSL2Hom_sl2Lower_mem hvw' t
        rw [← hX'] at hmem
        obtain ⟨y, hy, hyc⟩ := Subgroup.mem_map.mp hmem
        obtain ⟨z, -, rfl⟩ := Subgroup.mem_map.mp hy
        exact ⟨z, Subgroup.subtype_injective _ hyc⟩
      obtain ⟨β, hβ, -, u, hu, -⟩ :=
        exists_conj_rootGroup_eq_matTransvGroup_PSp n (GaloisField 2 1) (by omega) v w hvw
      have hu' : ((ggU .PSp n 1).D.rootGroup β).map (MulAut.conj u).toMonoidHom =
          (sl2UpperUniSub (GaloisField 2 1)).map c := by
        apply Subgroup.map_injective (Subgroup.subtype_injective _)
        rw [spSL2Hom_sl2Upper_map hvw']
        exact hu
      have hβ₀ : β₀ ∈ (ggU .PSp r 1).D.roots := by
        obtain ⟨w', γ₀, hγ₀, -, rfl⟩ := hlong
        exact CFSG.LieType.CurtisTits.weylAction_mem_roots hγ₀ w'
      obtain ⟨model, model', hpt⟩ := exists_models_of_chart (D := (ggU .PSp n 1).D) ι hinj hβ hβ₀
        c (spSL2Hom_injective hvw') hcU hcL u hu'
      refine ⟨.PSp, r, ψ₀.comp ι, ⟨Nat.prime_two, le_rfl, by omega,
        fun h => by have := (Prod.mk.inj h).1; omega⟩, ?_, ?_, ?_, β, β₀, model, model', u, ?_⟩
      · show 2 ≤ r
        omega
      · intro y hy
        exact Subgroup.comap_center_le_center hinj (hψ hy)
      · rw [MonoidHom.range_comp, hιr]
        exact hL'map
      · congr 1
        ext A
        exact congrArg ψ₀ (hpt A)
    · by_cases hdeg4 : blockDegree (Algebra.adjoin (GaloisField 2 f)
          (Units.val '' ({s} : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f))))) e < 4
      ·
        obtain ⟨hf1, r, ι, β₀, hr4, hinj, hlong, hιr, a₁, a₂, b₁, b₂, hP, hX, hX'⟩ :=
          selfDual_two hf ψ₀ hψ hl hn1 hne _ hSU hS hoddS he hadj (by omega) hdeg4 hL'comp hM
        subst hf1
        let ι' : (ggU .PSU r 1).K →* ↥(CFSG.Open.StatedSp n (GaloisField 2 1)) := ι
        let c := shortChart hP
        have hcU : (sl2UpperUniSub (GaloisField 2 1)).map c =
            ((ggU .PSU r 1).D.rootGroup β₀).map ι' := by
          apply Subgroup.map_injective (Subgroup.subtype_injective _)
          rw [shortChart_sl2Upper_map hP]
          exact hX.symm
        have hcL : ∀ t, c (sl2Lower t) ∈ ι'.range := by
          intro t
          have hmem := shortChart_sl2Lower_mem hP t
          rw [← hX'] at hmem
          obtain ⟨y, hy, hyc⟩ := Subgroup.mem_map.mp hmem
          obtain ⟨z, -, rfl⟩ := Subgroup.mem_map.mp hy
          exact ⟨z, Subgroup.subtype_injective _ hyc⟩
        obtain ⟨β, hβ, -, u, hu, -⟩ :=
          exists_conj_rootGroup_eq_altSiegelGroup_PSp n (GaloisField 2 1) hn a₁ a₂ b₁ b₂ hP.1
            hP.2.1 hP.2.2
        have hu' : ((ggU .PSp n 1).D.rootGroup β).map (MulAut.conj u).toMonoidHom =
            (sl2UpperUniSub (GaloisField 2 1)).map c := by
          apply Subgroup.map_injective (Subgroup.subtype_injective _)
          rw [shortChart_sl2Upper_map hP]
          exact hu
        have hβ₀ : β₀ ∈ (ggU .PSU r 1).D.roots := by
          obtain ⟨w', γ₀, hγ₀, -, rfl⟩ := hlong
          exact CFSG.LieType.CurtisTits.weylAction_mem_roots hγ₀ w'
        obtain ⟨model, model', hpt⟩ := exists_models_of_chart (D := (ggU .PSp n 1).D) ι' hinj hβ
          hβ₀ c (shortChart_injective hP) hcU hcL u hu'
        refine ⟨.PSU, r, ψ₀.comp ι', ⟨Nat.prime_two, le_rfl, by omega,
          fun h => by have := (Prod.mk.inj h).1; omega⟩, ?_, ?_, ?_, β, β₀, model, model', u, ?_⟩
        · show 2 ≤ r / 2
          omega
        · intro y hy
          exact Subgroup.comap_center_le_center hinj (hψ hy)
        · rw [MonoidHom.range_comp, hιr]
          exact hL'map
        · congr 1
          ext A
          exact congrArg ψ₀ (hpt A)
      · exact (fieldExt_false hf ψ₀ hψ hl hn1 hne _ hSU hS hoddS hε hL'comp he heε
          (Or.inl ⟨rfl, by omega⟩) hM).elim
  · exfalso
    by_cases hdeg2 : blockDegree (Algebra.adjoin (GaloisField 2 f)
        (Units.val '' ({s} : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f))))) e < 2
    · rw [hεeq] at hL'comp
      exact dualPair_one_false hf ψ₀ hψ hl hn1 hne s hs he hpair hdeg2 hL'comp hM
    · exact fieldExt_false hf ψ₀ hψ hl hn1 hne _ hSU hS hoddS hε hL'comp he heε
        (Or.inr ⟨hne', by omega⟩) hM

theorem ggSecFiveQTwoFieldTwoSelectedInput_of_POmega_exc
    (hPlus : GGSecFiveQTwoFieldTwoSelectedAt .POmegaPlus)
    (hMinus : GGSecFiveQTwoFieldTwoSelectedAt .POmegaMinus)
    (hEx : ∀ t, GGExcFive t → GGSecFiveQTwoFieldTwoSelectedAt t) :
    GGSecFiveQTwoFieldTwoSelectedInput := by
  refine ggSecFiveQTwoFieldTwoSelectedInput_of_classical_exc (fun t ht => ?_) hEx
  rcases ht with rfl | rfl | rfl | rfl | rfl
  · exact FieldTwoPSL.ggSecFiveQTwoFieldTwoSelectedAt_PSL
  · exact FieldTwoPSU.ggSecFiveQTwoFieldTwoSelectedAt_PSU
  · exact ggSecFiveQTwoFieldTwoSelectedAt_PSp
  · exact hPlus
  · exact hMinus

end Cert

end FieldTwoPSp

end CFSG.StandardType

end
