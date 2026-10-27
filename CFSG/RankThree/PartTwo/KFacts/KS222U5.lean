module

public import CFSG.RankThree.PartTwo.Sec21.Item222ProofStatements
public import CFSG.RankThree.PartTwo.Sec21.KS21U4TorusLines
public import CFSG.RankThree.PartOne.KF.R6LeviA
public import CFSG.RankThree.PartOne.KF.R56Final
import CFSG.RankThree.PartTwo.Sec21.Item222ProofStar

public section

namespace CFSG.RankThree.PartTwo.Sec21.U5Lines

open Matrix CFSG CFSG.RankThree
open CFSG.LieType.Universal.Unitary (SU)
open CFSG.LieType.BorelTits (unitaryInvolution unitaryInvolution_involutive)
open CFSG.Assembly.RankThreeEven (projSL projSU)
open CFSG.Assembly.LowTwoRank (StatedClassicalModel StatedProj StatedSU)
open CFSG.RankThree.PartOne (suQ isCentralPQuot_suQ)
open CFSG.RankThree.PartOne.KFU (dvec5 diagU diagU_one permGL permGL_mem_SU permGL_conj_diagU
  mem_torus6_iff bA6 coe_bA6 b6 coe_b6 su3Emb su3Emb_injective suBlock6 suBlock6_injective
  perfectResidual_centralizer_bA6 perfectResidual_centralizer_b6 card_center_SU_three
  card_center_SL_two statedModel_SU_three exists_conj_into_d8Tor_su d8Comb_five
  card_center_mulEquiv IsCentralPQuot map_inSubgroup_perfectResidual)

theorem exists_eq_zpowers_of_card_three {M : Type*} [Group M] {X : Subgroup M}
    (hX : Nat.card X = 3) : ∃ y ∈ X, y ≠ 1 ∧ y ^ 3 = 1 ∧ X = Subgroup.zpowers y := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Finite X := Nat.finite_of_card_ne_zero (by rw [hX]; norm_num)
  have : Nontrivial X := Finite.one_lt_card_iff_nontrivial.mp (by rw [hX]; norm_num)
  obtain ⟨z, hz⟩ := exists_ne (1 : X)
  have hz3 : z ^ 3 = 1 := by
    have h := pow_card_eq_one' (G := X) (x := z)
    rwa [hX] at h
  refine ⟨z, z.2, fun h => hz (Subtype.ext h), by simpa using congrArg Subtype.val hz3, ?_⟩
  apply le_antisymm
  · intro w hw
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp
      (mem_zpowers_of_prime_card hX hz (g' := ⟨w, hw⟩))
    exact Subgroup.mem_zpowers_iff.mpr ⟨k, by simpa using congrArg Subtype.val hk⟩
  · exact Subgroup.zpowers_le.mpr z.2

theorem perm₁_rev : ∀ i : Fin 5,
    (Equiv.swap (0 : Fin 5) 1 * Equiv.swap 3 4 : Equiv.Perm (Fin 5)) (Fin.rev i) =
      Fin.rev ((Equiv.swap (0 : Fin 5) 1 * Equiv.swap 3 4 : Equiv.Perm (Fin 5)) i) := by decide

theorem perm₂_rev : ∀ i : Fin 5, (Equiv.swap (1 : Fin 5) 3) (Fin.rev i) =
    Fin.rev ((Equiv.swap (1 : Fin 5) 3) i) := by decide

variable {K : Type} [Field K]

theorem conj_perm₁ (a : Kˣ) :
    permGL (Equiv.swap (0 : Fin 5) 1 * Equiv.swap 3 4) * diagU (dvec5 a 1) *
      (permGL (Equiv.swap (0 : Fin 5) 1 * Equiv.swap 3 4))⁻¹ =
      (diagU (dvec5 1 a) : GL (Fin 5) K) := by
  have hs : (Equiv.swap (0 : Fin 5) 1 * Equiv.swap 3 4 : Equiv.Perm (Fin 5)).symm =
      Equiv.swap (0 : Fin 5) 1 * Equiv.swap 3 4 := by decide
  rw [permGL_conj_diagU, hs]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem conj_perm₂ (a : Kˣ) :
    permGL (Equiv.swap (1 : Fin 5) 3) * diagU (dvec5 a a⁻¹) *
      (permGL (Equiv.swap (1 : Fin 5) 3))⁻¹ = (diagU (dvec5 a a) : GL (Fin 5) K) := by
  rw [permGL_conj_diagU]
  congr 1
  funext i
  fin_cases i <;> rfl

variable [Finite K] [CharP K 2]

theorem exists_conj_eq_bA6_or_b6 (hK : Nat.card K = (2 ^ 2) ^ 2)
    {x : ↥(SU (unitaryInvolution K 2 2) 5)} (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1) :
    ∃ (h : ↥(SU (unitaryInvolution K 2 2) 5)) (ζ : Kˣ)
      (hζ : unitaryInvolution K 2 2 (ζ : K) = ζ), ζ ≠ 1 ∧ ζ ^ 2 ≠ 1 ∧
        (h * x * h⁻¹ = bA6 (unitaryInvolution K 2 2) ζ hζ ∨
          h * x * h⁻¹ = b6 (unitaryInvolution K 2 2) ζ hζ) := by
  have hμ : Nat.card (rootsOfUnity 3 K) = 3 := U4Lines.card_rootsOfUnity_three even_two hK
  have hfix : ∀ u : Kˣ, u ^ 3 = 1 → unitaryInvolution K 2 2 (u : K) = u := fun u hu =>
    U4Lines.unitaryInvolution_rootsOfUnity even_two ⟨u, (mem_rootsOfUnity 3 u).mpr hu⟩
  have hsq : ∀ u : Kˣ, u ^ 3 = 1 → u ≠ 1 → u ^ 2 ≠ 1 := by
    intro u hu h1 h2
    apply h1
    calc u = u ^ 3 * (u ^ 2)⁻¹ := by group
      _ = 1 := by rw [hu, h2, inv_one, one_mul]
  have hpair : ∀ u v : Kˣ, u ^ 3 = 1 → v ^ 3 = 1 → u ≠ 1 → v ≠ 1 → v = u ∨ v = u⁻¹ := by
    intro u v hu hv hu1 hv1
    have hω : (⟨u, (mem_rootsOfUnity 3 u).mpr hu⟩ : rootsOfUnity 3 K) ≠ 1 :=
      fun h => hu1 (congrArg Subtype.val h)
    rcases U4Lines.eq_one_or_eq_or_eq_inv hμ hω ⟨v, (mem_rootsOfUnity 3 v).mpr hv⟩ with
      h | h | h
    · exact absurd (congrArg Subtype.val h) hv1
    · exact Or.inl (congrArg Subtype.val h)
    · exact Or.inr (congrArg Subtype.val h)
  have hX : ∀ z ∈ Subgroup.zpowers x, z ^ 3 = 1 := by
    intro z hz
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    rw [← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast, hx3,
      _root_.one_zpow]
  obtain ⟨g, hg⟩ := exists_conj_into_d8Tor_su (n := 5) (Or.inr rfl) d8Comb_five hK
    Nat.prime_three (by norm_num) (by norm_num) _ hX
  obtain ⟨a, b, ha, hb, hab⟩ := mem_torus6_iff.mp (hg x (Subgroup.mem_zpowers x))
  let w₁ : ↥(SU (unitaryInvolution K 2 2) 5) :=
    ⟨permGL (Equiv.swap (0 : Fin 5) 1 * Equiv.swap 3 4), permGL_mem_SU _ _ perm₁_rev⟩
  let w₂ : ↥(SU (unitaryInvolution K 2 2) 5) :=
    ⟨permGL (Equiv.swap (1 : Fin 5) 3), permGL_mem_SU _ _ perm₂_rev⟩
  have hconj : ∀ w : ↥(SU (unitaryInvolution K 2 2) 5),
      w * g * x * (w * g)⁻¹ = w * (g * x * g⁻¹) * w⁻¹ := by
    intro w
    group
  by_cases ha1 : a = 1
  · subst ha1
    by_cases hb1 : b = 1
    · subst hb1
      exfalso
      apply hx1
      have h1 : g * x * g⁻¹ = 1 := by
        apply Subtype.ext
        rw [hab]
        have : dvec5 (1 : Kˣ) 1 = 1 := by
          funext i
          fin_cases i <;> simp [dvec5]
        rw [this, diagU_one]
        rfl
      calc x = g⁻¹ * (g * x * g⁻¹) * g := by group
        _ = 1 := by rw [h1]; group
    · refine ⟨g, b, hfix b hb, hb1, hsq b hb hb1, Or.inl (Subtype.ext ?_)⟩
      rw [hab, coe_bA6]
  · by_cases hb1 : b = 1
    · subst hb1
      refine ⟨w₁ * g, a, hfix a ha, ha1, hsq a ha ha1, Or.inl (Subtype.ext ?_)⟩
      rw [hconj, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hab, coe_bA6]
      exact conj_perm₁ a
    · rcases hpair a b ha hb ha1 hb1 with h | h
      · refine ⟨g, a, hfix a ha, ha1, hsq a ha ha1, Or.inr (Subtype.ext ?_)⟩
        rw [hab, h, coe_b6]
      · refine ⟨w₂ * g, a, hfix a ha, ha1, hsq a ha ha1, Or.inr (Subtype.ext ?_)⟩
        rw [hconj, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hab, h, coe_b6]
        exact conj_perm₂ a

theorem perfectResidual_centralizer_cases (hK : Nat.card K = (2 ^ 2) ^ 2)
    {x : ↥(SU (unitaryInvolution K 2 2) 5)} (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1) :
    Nonempty (inSubgroup perfectResidual (Subgroup.centralizer
        ({x} : Set ↥(SU (unitaryInvolution K 2 2) 5))) ≃* SpecialLinearGroup (Fin 2) K) ∨
      Nonempty (inSubgroup perfectResidual (Subgroup.centralizer
        ({x} : Set ↥(SU (unitaryInvolution K 2 2) 5))) ≃*
          ↥(SU (unitaryInvolution K 2 2) 3)) := by
  have hσσ : ∀ c, unitaryInvolution K 2 2 (unitaryInvolution K 2 2 c) = c :=
    unitaryInvolution_involutive hK
  have hK4 : 4 ≤ Nat.card K := by rw [hK]; norm_num
  obtain ⟨h, ζ, hζ, h1, h2, hcase⟩ := exists_conj_eq_bA6_or_b6 hK hx3 hx1
  have hzp : Subgroup.zpowers (h * x * h⁻¹) =
      (Subgroup.zpowers x).map (MulAut.conj h).toMonoidHom := by
    rw [MonoidHom.map_zpowers]
    rfl
  have hmap : inSubgroup perfectResidual (Subgroup.centralizer
      ({h * x * h⁻¹} : Set ↥(SU (unitaryInvolution K 2 2) 5))) =
      (inSubgroup perfectResidual (Subgroup.centralizer
        ({x} : Set ↥(SU (unitaryInvolution K 2 2) 5)))).map (MulAut.conj h).toMonoidHom := by
    have := U4Lines.perfectResidual_conj (Y := ⊤) (Subgroup.mem_top h) (Subgroup.zpowers x)
    rw [← hzp, top_inf_eq, top_inf_eq, Item222Proof.centralizer_zpowers_eq,
      Item222Proof.centralizer_zpowers_eq] at this
    exact this
  have e₁ : inSubgroup perfectResidual (Subgroup.centralizer
      ({x} : Set ↥(SU (unitaryInvolution K 2 2) 5))) ≃*
      inSubgroup perfectResidual (Subgroup.centralizer
        ({h * x * h⁻¹} : Set ↥(SU (unitaryInvolution K 2 2) 5))) :=
    (Subgroup.equivMapOfInjective _ _ (MulAut.conj h).injective).trans
      (MulEquiv.subgroupCongr hmap.symm)
  rcases hcase with heq | heq
  · right
    rw [heq, perfectResidual_centralizer_bA6 hK le_rfl hζ h1 h2] at e₁
    exact ⟨e₁.trans (MonoidHom.ofInjective (su3Emb_injective _)).symm⟩
  · left
    rw [heq, perfectResidual_centralizer_b6 _ hσσ hK4 hζ h1 h2] at e₁
    exact ⟨e₁.trans (MonoidHom.ofInjective (suBlock6_injective _ hσσ)).symm⟩

theorem perfectResidual_centralizer_proj_cases (hK : Nat.card K = (2 ^ 2) ^ 2)
    {y : StatedProj (StatedSU 5 (2 ^ 2) K)} (hy3 : y ^ 3 = 1) (hy1 : y ≠ 1) :
    Nonempty (inSubgroup perfectResidual (Subgroup.centralizer
        ({y} : Set (StatedProj (StatedSU 5 (2 ^ 2) K)))) ≃* SpecialLinearGroup (Fin 2) K) ∨
      Nonempty (inSubgroup perfectResidual (Subgroup.centralizer
        ({y} : Set (StatedProj (StatedSU 5 (2 ^ 2) K)))) ≃*
          ↥(SU (unitaryInvolution K 2 2) 3)) := by
  have hq : IsCentralPQuot 3 (suQ 5 hK) :=
    isCentralPQuot_suQ Nat.prime_three (by norm_num) (by norm_num) (by norm_num) (by norm_num) hK
  obtain ⟨x, hxy, hx3⟩ := hq.exists_lift hy3
  have hx1 : x ≠ 1 := by
    rintro rfl
    exact hy1 (by rw [← hxy, map_one])
  set H := inSubgroup perfectResidual (Subgroup.centralizer
    ({x} : Set ↥(SU (unitaryInvolution K 2 2) 5))) with hH
  have hmap : inSubgroup perfectResidual (Subgroup.centralizer
      ({y} : Set (StatedProj (StatedSU 5 (2 ^ 2) K)))) = H.map (suQ 5 hK) := by
    rw [hH, CFSG.RankThree.PartOne.KFU.map_inSubgroup_perfectResidual, hq.map_centralizer hx3,
      hxy]
  have hiso : Nat.card (Subgroup.center H) = 1 →
      Nonempty (inSubgroup perfectResidual (Subgroup.centralizer
        ({y} : Set (StatedProj (StatedSU 5 (2 ^ 2) K)))) ≃* H) := by
    intro hc
    have hbot : Subgroup.center H = ⊥ := Subgroup.card_eq_one.mp hc
    have hinj : Function.Injective ((suQ 5 hK).subgroupMap H) := by
      rw [injective_iff_map_eq_one]
      intro z hz
      have hz' : (z : ↥(SU (unitaryInvolution K 2 2) 5)) ∈ (suQ 5 hK).ker :=
        MonoidHom.mem_ker.mpr (congrArg Subtype.val hz)
      have hzc : (z : ↥(SU (unitaryInvolution K 2 2) 5)) ∈
          Subgroup.center ↥(SU (unitaryInvolution K 2 2) 5) := hq.central hz'
      have hzH : z ∈ Subgroup.center H := by
        rw [Subgroup.mem_center_iff]
        intro w
        exact Subtype.ext (Subgroup.mem_center_iff.mp hzc w)
      rw [hbot] at hzH
      exact hzH
    exact ⟨(MulEquiv.subgroupCongr hmap).trans
      (MulEquiv.ofBijective _ ⟨hinj, (suQ 5 hK).subgroupMap_surjective H⟩).symm⟩
  rcases perfectResidual_centralizer_cases hK hx3 hx1 with he | he
  · left
    obtain ⟨e⟩ := he
    have hc : Nat.card (Subgroup.center H) = 1 := by
      rw [card_center_mulEquiv e, card_center_SL_two]
    obtain ⟨e'⟩ := hiso hc
    exact ⟨e'.trans e⟩
  · right
    obtain ⟨e⟩ := he
    have hc : Nat.card (Subgroup.center H) = 1 := by
      rw [card_center_mulEquiv e, card_center_SU_three hK le_rfl]
      norm_num
    obtain ⟨e'⟩ := hiso hc
    exact ⟨e'.trans e⟩

theorem statedClassicalModel_SU_three (hK : Nat.card K = (2 ^ 2) ^ 2) :
    StatedClassicalModel ↥(SU (unitaryInvolution K 2 2) 3) .PSU 3 2 2 := by
  have hc : Nat.card (Subgroup.center ↥(SU (unitaryInvolution K 2 2) 3)) = 1 := by
    rw [card_center_SU_three hK le_rfl]
    norm_num
  have hbot := Subgroup.card_eq_one.mp hc
  exact CFSG.LieType.CurtisTits.statedClassicalModel_of_mulEquiv
    ((QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot)
    (statedModel_SU_three hK le_rfl)

end CFSG.RankThree.PartTwo.Sec21.U5Lines

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree
open CFSG.Assembly.RankThreeEven (projSL projSU)
open CFSG.Assembly.LowTwoRank (StatedClassicalModel StatedProj StatedSU)
open U4Lines (mapL card_mapL perfectResidualEquiv)

theorem ks222U5 : KS222U5 := by
  intro G _ _ L ℓ ⟨eL⟩ hℓL hℓ3
  set K := GaloisField 2 (2 * 2) with hKdef
  have hK : Nat.card K = (2 ^ 2) ^ 2 := U4Lines.card_galoisField_two_mul 2 (by norm_num)
  let e₀ : projSU 5 2 2 ≃* StatedProj (StatedSU 5 (2 ^ 2) K) :=
    (MulEquiv.subgroupCongr (Census.projImage_statedSU 5 2 2).symm).trans
      (Census.statedProjEquivProjImage _).symm
  let e : L ≃* ↥(⊤ : Subgroup (StatedProj (StatedSU 5 (2 ^ 2) K))) :=
    (eL.trans e₀).trans Subgroup.topEquiv.symm
  have hX3 : Nat.card (mapL e ℓ) = 3 := by rw [card_mapL e hℓL, hℓ3]
  obtain ⟨y, -, hy1, hy3, hXy⟩ := U5Lines.exists_eq_zpowers_of_card_three hX3
  have hC : (⊤ : Subgroup (StatedProj (StatedSU 5 (2 ^ 2) K))) ⊓
      Subgroup.centralizer (mapL e ℓ : Set (StatedProj (StatedSU 5 (2 ^ 2) K))) =
      Subgroup.centralizer ({y} : Set (StatedProj (StatedSU 5 (2 ^ 2) K))) := by
    rw [top_inf_eq, hXy, Item222Proof.centralizer_zpowers_eq]
  have e₁ := perfectResidualEquiv e hℓL
  rw [hC] at e₁
  rcases U5Lines.perfectResidual_centralizer_proj_cases hK hy3 hy1 with he | he
  · left
    obtain ⟨e₂⟩ := he
    exact ⟨e₁.trans (e₂.trans (projSLTwoEquivSL K).symm)⟩
  · right
    obtain ⟨e₂⟩ := he
    exact CFSG.LieType.CurtisTits.statedClassicalModel_of_mulEquiv (e₁.trans e₂).symm
      (U5Lines.statedClassicalModel_SU_three hK)

end CFSG.RankThree.PartTwo.Sec21
