module

public import CFSG.RankThree.PartTwo.Census.Carrier.G2EvenRank
public import CFSG.LieType.Chevalley.GraphFixedParabolicLevi
public import CFSG.LieType.Chevalley.GraphFixedRankOneImage
public import CFSG.LieType.Chevalley.GraphFixedCompatibleDiagonal
public import CFSG.LieType.Chevalley.GraphFixedD4TorusWords
import CFSG.Blueprint.ChevalleyStrings
public import CFSG.Blueprint.ChevalleyRootArtifact
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
import CFSG.GroupTheory.ElementaryAbelianTransport

public noncomputable section

namespace CFSG.RankThree.PartTwo.Census.Carrier.D4Even

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.Assembly

section Counting

variable {G : Type*} [Group G]

theorem card_le_three_of_threeRankLeOne {X E : Subgroup G} (hX : ThreeRankLeOne X)
    (hEX : E ≤ X) (hE : IsElemAbelian 3 E) : Nat.card E ≤ 3 := by
  by_cases hbot : E = ⊥
  · rw [hbot, Subgroup.card_bot]
    norm_num
  obtain ⟨⟨a, haE⟩, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hbot
  have ha1' : a ≠ 1 := fun h => ha1 (Subtype.ext h)
  have ha3 : a ^ 3 = 1 := hE.2 a haE
  have hle : E ≤ Subgroup.zpowers a := by
    intro b hbE
    have hcomm : a * b = b * a := by
      have := hE.1.is_comm.comm ⟨a, haE⟩ ⟨b, hbE⟩
      exact congrArg Subtype.val this
    have h := hX ⟨a, hEX haE⟩ ⟨b, hEX hbE⟩ (Subtype.ext (by simpa using ha3))
      (Subtype.ext (by simpa using hE.2 b hbE)) (Subtype.ext (by simpa using hcomm))
      (fun h => ha1' (congrArg Subtype.val h))
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 h
    exact Subgroup.mem_zpowers_iff.2 ⟨k, by simpa using congrArg Subtype.val hk⟩
  have hord : orderOf a ≤ 3 := orderOf_le_of_pow_eq_one (by norm_num) ha3
  have hpos : 0 < orderOf a :=
    orderOf_pos_iff.2 (isOfFinOrder_iff_pow_eq_one.2 ⟨3, by norm_num, ha3⟩)
  have : Finite (Subgroup.zpowers a) := by
    refine Nat.finite_of_card_ne_zero ?_
    rw [Nat.card_zpowers]
    exact hpos.ne'
  calc Nat.card E ≤ Nat.card (Subgroup.zpowers a) := Subgroup.card_le_of_le hle
    _ = orderOf a := Nat.card_zpowers a
    _ ≤ 3 := hord

theorem card_le_nine_of_monoidHom {E : Subgroup G} [Finite E] (hE : IsElemAbelian 3 E)
    {K : Type*} [Field K] [Finite K] (φ : E →* Kˣ) (hker : Nat.card φ.ker ≤ 3) :
    Nat.card E ≤ 9 := by
  have hrange : Nat.card φ.range ≤ 3 := by
    obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := φ.range)
    rw [← orderOf_eq_card_of_forall_mem_zpowers hg]
    refine orderOf_le_of_pow_eq_one (by norm_num) ?_
    obtain ⟨e, he⟩ := g.2
    have he3 : e ^ 3 = 1 := Subtype.ext (by simpa using hE.2 e e.2)
    refine Subtype.ext ?_
    rw [Subgroup.coe_pow, ← he, ← map_pow, he3, map_one, Subgroup.coe_one]
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv] at h
  rw [h]
  calc Nat.card φ.range * Nat.card φ.ker ≤ 3 * 3 := Nat.mul_le_mul hrange hker
    _ = 9 := by norm_num

end Counting

section Lines

variable {τ : Tag} {K : Type} [Field K]

theorem rootVec_eq_single {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β) :
    rootVec τ K β = Finsupp.single (Sum.inr ⟨β, hβ⟩) 1 :=
  dite_eq_left hβ

theorem xOp_rootVec_eq_self (i : Fin τ.rank) (c : K) {α : Fin τ.rank → ℤ} (hα : IsRoot τ α)
    (h₁ : α ≠ Pi.single i 1) (h₂ : α ≠ -Pi.single i 1) (hr : ¬ IsRoot τ (α + Pi.single i 1)) :
    xOp τ K i c (rootVec τ K α) = rootVec τ K α := by
  obtain ⟨-, hint⟩ := isRoot_add_smul_single_iff hα i h₁ h₂
  have hp : stringUp τ i α = 0 := by
    by_contra h
    exact hr (by simpa using (hint 1).2 ⟨by omega, by omega⟩)
  rw [rootVec_eq_single hα, xOp, Finsupp.linearCombination_single, one_smul]
  simp only [h₁, h₂, ite_false, hp, zero_add, Finset.sum_range_one, Nat.choose_zero_right,
    Nat.cast_one, pow_zero, mul_one, one_smul, Nat.cast_zero, zero_smul, add_zero]
  exact rootVec_eq_single hα

theorem yOp_rootVec_eq_self (i : Fin τ.rank) (c : K) {α : Fin τ.rank → ℤ} (hα : IsRoot τ α)
    (h₁ : α ≠ Pi.single i 1) (h₂ : α ≠ -Pi.single i 1) (hr : ¬ IsRoot τ (α - Pi.single i 1)) :
    yOp τ K i c (rootVec τ K α) = rootVec τ K α := by
  obtain ⟨-, hint⟩ := isRoot_add_smul_single_iff hα i h₁ h₂
  have hq : stringDown τ i α = 0 := by
    by_contra h
    have h' := (hint (-1)).2 ⟨by omega, by omega⟩
    rw [neg_smul, one_smul, ← sub_eq_add_neg] at h'
    exact hr h'
  rw [rootVec_eq_single hα, yOp, Finsupp.linearCombination_single, one_smul]
  simp only [h₁, h₂, ite_false, hq, zero_add, Finset.sum_range_one, Nat.choose_zero_right,
    Nat.cast_one, pow_zero, mul_one, one_smul, Nat.cast_zero, zero_smul, sub_zero]
  exact rootVec_eq_single hα

@[expose] def vecStab (v : RootModule τ K) : Subgroup (ModGL τ K) where
  carrier := {g | (g : Module.End K (RootModule τ K)) v = v}
  one_mem' := rfl
  mul_mem' {a b} ha hb := by
    change ((a : Module.End K (RootModule τ K)) * b) v = v
    rw [Module.End.mul_apply, show (b : Module.End K (RootModule τ K)) v = v from hb]
    exact ha
  inv_mem' {a} ha := by
    have ha' : (a : Module.End K (RootModule τ K)) v = v := ha
    change ((a⁻¹ : ModGL τ K) : Module.End K (RootModule τ K)) v = v
    conv_lhs => rw [← ha']
    rw [← Module.End.mul_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Module.End.one_apply]

theorem mem_vecStab {v : RootModule τ K} {g : ModGL τ K} :
    g ∈ vecStab v ↔ (g : Module.End K (RootModule τ K)) v = v :=
  Iff.rfl

variable (K) in
@[expose] def leviRoot (A : Set (Fin τ.rank)) : Subgroup (ModGL τ K) :=
  Subgroup.closure {g | ∃ j ∈ A, ∃ c : K, g = xUnit τ K j c ∨ g = yUnit τ K j c}

theorem leviRoot_le_vecStab {A : Set (Fin τ.rank)} {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β)
    (h : ∀ j ∈ A, β ≠ Pi.single j 1 ∧ β ≠ -Pi.single j 1 ∧ ¬ IsRoot τ (β + Pi.single j 1) ∧
      ¬ IsRoot τ (β - Pi.single j 1)) :
    leviRoot K A ≤ vecStab (rootVec τ K β) := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨j, hj, c, rfl | rfl⟩
  · obtain ⟨h₁, h₂, h₃, -⟩ := h j hj
    rw [SetLike.mem_coe, mem_vecStab, coe_xUnit]
    exact xOp_rootVec_eq_self j c hβ h₁ h₂ h₃
  · obtain ⟨h₁, h₂, -, h₄⟩ := h j hj
    rw [SetLike.mem_coe, mem_vecStab, coe_yUnit]
    exact yOp_rootVec_eq_self j c hβ h₁ h₂ h₄

theorem leviRoot_mono {A B : Set (Fin τ.rank)} (h : A ⊆ B) : leviRoot K A ≤ leviRoot K B :=
  Subgroup.closure_mono fun _ ⟨j, hj, c, hc⟩ => ⟨j, h hj, c, hc⟩

theorem parabolicLevi_mono {A B : Set (Fin τ.rank)} (h : A ⊆ B) :
    parabolicLevi τ K A ≤ parabolicLevi τ K B :=
  sup_le_sup_left (leviRoot_mono h) _

theorem closure_le_leviRoot {A : Set (Fin τ.rank)} {j : Fin τ.rank} (hj : j ∈ A) :
    Subgroup.closure (Set.range (xUnit τ K j) ∪ Set.range (yUnit τ K j)) ≤ leviRoot K A := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
  · exact Subgroup.subset_closure ⟨j, hj, c, Or.inl rfl⟩
  · exact Subgroup.subset_closure ⟨j, hj, c, Or.inr rfl⟩

theorem leviRoot_singleton (j : Fin τ.rank) :
    leviRoot K {j} = Subgroup.closure (Set.range (xUnit τ K j) ∪ Set.range (yUnit τ K j)) := by
  refine le_antisymm ((Subgroup.closure_le _).2 ?_) (closure_le_leviRoot rfl)
  rintro _ ⟨j', hj', c, rfl | rfl⟩
  · rw [Set.mem_singleton_iff.1 hj']
    exact Subgroup.subset_closure (Or.inl ⟨c, rfl⟩)
  · rw [Set.mem_singleton_iff.1 hj']
    exact Subgroup.subset_closure (Or.inr ⟨c, rfl⟩)

theorem torusElt_mem_leviRoot {A : Set (Fin τ.rank)} {j : Fin τ.rank} (hj : j ∈ A) (u : Kˣ) :
    torusElt τ K j u ∈ leviRoot K A := by
  obtain ⟨ρ, -, -, hH, -, hrange, -⟩ := exceptional_ordinary_rank_one_central_image τ K j
  refine closure_le_leviRoot hj ?_
  rw [← hrange, ← hH]
  exact ⟨_, rfl⟩

end Lines

section Torus

variable {τ : Tag} {K : Type} [Field K]

theorem torusGroup_le_range : torusGroup τ K ≤ (rootDiagUnitHom τ K).range := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨⟨i, u⟩, rfl⟩
  exact ⟨_, (torusElt_eq_rootDiagUnit i u).symm⟩

theorem rootDiagUnit_inv (b : Fin τ.rank → Kˣ) : rootDiagUnit τ b⁻¹ = (rootDiagUnit τ b)⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [← rootDiagUnit_mul, inv_mul_cancel, rootDiagUnit_one])

theorem leviRoot_le_comap_conj (b : Fin τ.rank → Kˣ) (A : Set (Fin τ.rank)) :
    leviRoot K A ≤ (leviRoot K A).comap (MulAut.conj (rootDiagUnit τ b)).toMonoidHom := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨j, hj, c, rfl | rfl⟩
  · rw [SetLike.mem_coe, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      (root_diagonal_conjugation τ K b).1 j c]
    exact Subgroup.subset_closure ⟨j, hj, _, Or.inl rfl⟩
  · rw [SetLike.mem_coe, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      (root_diagonal_conjugation τ K b).2.1 j c]
    exact Subgroup.subset_closure ⟨j, hj, _, Or.inr rfl⟩

theorem rootDiagUnit_mem_normalizer (b : Fin τ.rank → Kˣ) (A : Set (Fin τ.rank)) :
    rootDiagUnit τ b ∈ Subgroup.normalizer (leviRoot K A : Set (ModGL τ K)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨fun hh => leviRoot_le_comap_conj b A hh, fun hh => ?_⟩
  have h' := leviRoot_le_comap_conj b⁻¹ A hh
  rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, rootDiagUnit_inv,
    inv_inv] at h'
  simpa [mul_assoc] using h'

theorem torusGroup_le_normalizer (A : Set (Fin τ.rank)) :
    torusGroup τ K ≤ Subgroup.normalizer (leviRoot K A : Set (ModGL τ K)) := fun t ht => by
  obtain ⟨b, rfl⟩ := torusGroup_le_range ht
  exact rootDiagUnit_mem_normalizer b A

theorem exists_eq_rootDiagUnit_mul {A : Set (Fin τ.rank)} {g : ModGL τ K}
    (hg : g ∈ parabolicLevi τ K A) :
    ∃ b : Fin τ.rank → Kˣ, ∃ l ∈ leviRoot K A, g = rootDiagUnit τ b * l := by
  have h := Subgroup.coe_mul_of_left_le_normalizer_right _ _ (torusGroup_le_normalizer (K := K) A)
  have hg' : g ∈ ((torusGroup τ K ⊔ leviRoot K A : Subgroup (ModGL τ K)) : Set (ModGL τ K)) := hg
  rw [h] at hg'
  obtain ⟨t, ht, l, hl, rfl⟩ := hg'
  obtain ⟨b, rfl⟩ := torusGroup_le_range ht
  exact ⟨b, l, hl, rfl⟩

theorem rootDiagUnit_mul_apply_rootVec (b : Fin τ.rank → Kˣ) {l : ModGL τ K}
    {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β) (hl : l ∈ vecStab (rootVec τ K β)) :
    ((rootDiagUnit τ b * l : ModGL τ K) : Module.End K (RootModule τ K)) (rootVec τ K β) =
      ((rootChar b β : Kˣ) : K) • rootVec τ K β := by
  rw [Units.val_mul, Module.End.mul_apply, show (l : Module.End K (RootModule τ K))
    (rootVec τ K β) = rootVec τ K β from hl]
  exact rootDiag_rootVec b hβ

end Torus

section Coeff

variable {τ : Tag} {K : Type} [Field K]

@[expose] def lineCoeff {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β) (g : ModGL τ K) : K :=
  (g : Module.End K (RootModule τ K)) (rootVec τ K β) (Sum.inr ⟨β, hβ⟩)

theorem lineCoeff_of_eq {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β) {g : ModGL τ K} {c : K}
    (h : (g : Module.End K (RootModule τ K)) (rootVec τ K β) = c • rootVec τ K β) :
    lineCoeff hβ g = c := by
  rw [lineCoeff, h, rootVec_eq_single hβ, Finsupp.smul_apply, Finsupp.single_eq_same, smul_eq_mul,
    mul_one]

@[expose] def lineHom {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β)
    (E : Subgroup (ModGL τ K))
    (hE : ∀ g ∈ E, ∃ c : K, (g : Module.End K (RootModule τ K)) (rootVec τ K β) =
      c • rootVec τ K β) : E →* K where
  toFun g := lineCoeff hβ g
  map_one' := lineCoeff_of_eq hβ (by simp)
  map_mul' g h := by
    obtain ⟨c, hc⟩ := hE g g.2
    obtain ⟨d, hd⟩ := hE h h.2
    rw [lineCoeff_of_eq hβ hc, lineCoeff_of_eq hβ hd, lineCoeff_of_eq hβ (c := c * d)]
    rw [Subgroup.coe_mul, Units.val_mul, Module.End.mul_apply, hd, map_smul, hc, smul_smul,
      mul_comm]

theorem lineHom_apply {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β) (E : Subgroup (ModGL τ K))
    (hE : ∀ g ∈ E, ∃ c : K, (g : Module.End K (RootModule τ K)) (rootVec τ K β) =
      c • rootVec τ K β) (g : E) :
    ((g : ModGL τ K) : Module.End K (RootModule τ K)) (rootVec τ K β) =
      lineHom hβ E hE g • rootVec τ K β := by
  obtain ⟨c, hc⟩ := hE g g.2
  change _ = lineCoeff hβ (g : ModGL τ K) • _
  rw [lineCoeff_of_eq hβ hc, hc]

end Coeff

section Twist

variable {t : TwistTag} {K : Type} [Field K] {σ : K →+* K}

theorem twistHom_apply_rootVec {g : ModGL t.tag K} {β : Fin t.tag.rank → ℤ} (hβ : IsRoot t.tag β)
    {c : K}
    (h : (g : Module.End K (RootModule t.tag K)) (rootVec t.tag K β) = c • rootVec t.tag K β) :
    ((twistHom t K σ g : ModGL t.tag K) : Module.End K (RootModule t.tag K))
        (rootVec t.tag K (permLattice t.perm β)) =
      σ c • rootVec t.tag K (permLattice t.perm β) := by
  have hP := diagramMap_rootVec t K β hβ
  have hPinv : (((diagramMap t K)⁻¹ : ModGL t.tag K) : Module.End K (RootModule t.tag K))
      (rootVec t.tag K (permLattice t.perm β)) = rootVec t.tag K β := by
    rw [← hP, ← Module.End.mul_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Module.End.one_apply]
  have hσ : entrywise σ (g : Module.End K (RootModule t.tag K)) (rootVec t.tag K β) =
      σ c • rootVec t.tag K β := by
    rw [rootVec_eq_single hβ, entrywise_single, ← rootVec_eq_single hβ, h, rootVec_eq_single hβ,
      Finsupp.smul_single, smul_eq_mul, mul_one, Finsupp.mapRange_single, Finsupp.smul_single,
      smul_eq_mul, mul_one]
  rw [coe_twistHom, Module.End.mul_apply, Module.End.mul_apply, hPinv, hσ, map_smul, hP]

theorem apply_rootVec_permLattice {g : ModGL t.tag K} (hg : g ∈ twistedFixedGroup t K σ)
    {β : Fin t.tag.rank → ℤ} (hβ : IsRoot t.tag β) {c : K}
    (h : (g : Module.End K (RootModule t.tag K)) (rootVec t.tag K β) = c • rootVec t.tag K β) :
    (g : Module.End K (RootModule t.tag K)) (rootVec t.tag K (permLattice t.perm β)) =
      σ c • rootVec t.tag K (permLattice t.perm β) := by
  have h' := twistHom_apply_rootVec (σ := σ) hβ h
  rwa [((mem_twistedFixedGroup_iff_twistHom (t := t) (K := K) (σ := σ)).1 hg).2] at h'

end Twist

section RankOne

variable {τ : Tag} {K : Type} [Field K] [CharP K 2]

theorem eq_one_of_sq_eq_one {x : K} (h : x ^ 2 = 1) : x = 1 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hsq : (x - 1) ^ 2 = 0 := by linear_combination h + (1 - x) * h2
  exact sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 hsq)

theorem injective_of_ker_scalar {G : Type*} [Group G] {ρ : SL2 K →* G}
    (h : ∀ g ∈ ρ.ker, ∃ l : Kˣ, (l : K) ^ 2 = 1 ∧
      (g : Matrix (Fin 2) (Fin 2) K) = (l : K) • (1 : Matrix (Fin 2) (Fin 2) K)) :
    Function.Injective ρ := by
  rw [injective_iff_map_eq_one]
  intro g hg
  obtain ⟨l, hl, hgl⟩ := h g hg
  refine Subtype.ext ?_
  rw [hgl, eq_one_of_sq_eq_one hl, one_smul]
  rfl

theorem threeRankLeOne_leviRoot_singleton (j : Fin τ.rank) :
    ThreeRankLeOne (leviRoot K ({j} : Set (Fin τ.rank))) := by
  obtain ⟨ρ, -, -, -, -, hrange, hker, -⟩ := exceptional_ordinary_rank_one_central_image τ K j
  have hρi := injective_of_ker_scalar hker
  rw [leviRoot_singleton, ← hrange]
  exact ThreeRankLeOne.of_mulEquiv (MonoidHom.ofInjective hρi).symm threeRankLeOne_SL2

end RankOne

theorem IsElemAbelian.mono {G : Type*} [Group G] {E F : Subgroup G} (hFE : F ≤ E)
    (hE : IsElemAbelian 3 E) : IsElemAbelian 3 F := CFSG.Open.IsElemAbelian.mono hE hFE

theorem eq_of_smul_rootVec {τ : Tag} {K : Type} [Field K] {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β)
    {c d : K} (h : c • rootVec τ K β = d • rootVec τ K β) : c = d := by
  have := congrArg (fun v : RootModule τ K => v (Sum.inr ⟨β, hβ⟩)) h
  simpa [rootVec_eq_single hβ] using this

section Middle

local notation "ν" n:max => (⟨n, by decide⟩ : Fin TwistTag.D4.tag.rank)

@[expose] def v4 (a b c d : ℤ) : Fin TwistTag.D4.tag.rank → ℤ := ![a, b, c, d]

theorem not_isRoot_of_not_mem {v : Fin TwistTag.D4.tag.rank → ℤ}
    (h : List.ofFn v ∉ TwistTag.D4.tag.artifactRoots) : ¬ IsRoot TwistTag.D4.tag v :=
  fun hv => h (isRoot_iff_mem_artifactRoots.1 hv)

theorem isRoot_v4_1110 : IsRoot TwistTag.D4.tag (v4 1 1 1 0) :=
  isRoot_iff_mem_artifactRoots.2 (by decide)

theorem isRoot_v4_0111 : IsRoot TwistTag.D4.tag (v4 0 1 1 1) :=
  isRoot_iff_mem_artifactRoots.2 (by decide)

theorem isRoot_v4_1011 : IsRoot TwistTag.D4.tag (v4 1 0 1 1) :=
  isRoot_iff_mem_artifactRoots.2 (by decide)

theorem permLattice_v4_1110 : permLattice TwistTag.D4.perm (v4 1 1 1 0) = v4 0 1 1 1 := by
  decide

theorem permLattice_v4_0111 : permLattice TwistTag.D4.perm (v4 0 1 1 1) = v4 1 0 1 1 := by
  decide

theorem middle_cond_1110 : ∀ j ∈ ({ν 2} : Set (Fin TwistTag.D4.tag.rank)),
    v4 1 1 1 0 ≠ Pi.single j 1 ∧ v4 1 1 1 0 ≠ -Pi.single j 1 ∧
      ¬ IsRoot TwistTag.D4.tag (v4 1 1 1 0 + Pi.single j 1) ∧
      ¬ IsRoot TwistTag.D4.tag (v4 1 1 1 0 - Pi.single j 1) := by
  intro j hj
  rw [Set.mem_singleton_iff] at hj
  subst hj
  exact ⟨by decide, by decide, not_isRoot_of_not_mem (by decide),
    not_isRoot_of_not_mem (by decide)⟩

theorem middle_cond_0111 : ∀ j ∈ ({ν 2} : Set (Fin TwistTag.D4.tag.rank)),
    v4 0 1 1 1 ≠ Pi.single j 1 ∧ v4 0 1 1 1 ≠ -Pi.single j 1 ∧
      ¬ IsRoot TwistTag.D4.tag (v4 0 1 1 1 + Pi.single j 1) ∧
      ¬ IsRoot TwistTag.D4.tag (v4 0 1 1 1 - Pi.single j 1) := by
  intro j hj
  rw [Set.mem_singleton_iff] at hj
  subst hj
  exact ⟨by decide, by decide, not_isRoot_of_not_mem (by decide),
    not_isRoot_of_not_mem (by decide)⟩

theorem middle_cond_1011 : ∀ j ∈ ({ν 2} : Set (Fin TwistTag.D4.tag.rank)),
    v4 1 0 1 1 ≠ Pi.single j 1 ∧ v4 1 0 1 1 ≠ -Pi.single j 1 ∧
      ¬ IsRoot TwistTag.D4.tag (v4 1 0 1 1 + Pi.single j 1) ∧
      ¬ IsRoot TwistTag.D4.tag (v4 1 0 1 1 - Pi.single j 1) := by
  intro j hj
  rw [Set.mem_singleton_iff] at hj
  subst hj
  exact ⟨by decide, by decide, not_isRoot_of_not_mem (by decide),
    not_isRoot_of_not_mem (by decide)⟩

variable {K : Type} [Field K]

theorem rootChar_v4 (b : Fin TwistTag.D4.tag.rank → Kˣ) (p q r s : ℤ) :
    rootChar b (v4 p q r s) = b (ν 0) ^ p * b (ν 1) ^ q * b (ν 2) ^ r * b (ν 3) ^ s := by
  rw [rootChar]
  change ∏ i : Fin 4, b i ^ (v4 p q r s i) = _
  rw [Fin.prod_univ_four]
  rfl

theorem rootDiagUnit_eq_torusElt_two {b : Fin TwistTag.D4.tag.rank → Kˣ}
    (h₁ : rootChar b (v4 1 1 1 0) = 1) (h₂ : rootChar b (v4 0 1 1 1) = 1)
    (h₃ : rootChar b (v4 1 0 1 1) = 1) :
    rootDiagUnit TwistTag.D4.tag b = torusElt TwistTag.D4.tag K (ν 2) (b (ν 0))⁻¹ := by
  rw [rootChar_v4] at h₁ h₂ h₃
  simp only [zpow_one, zpow_zero, mul_one, one_mul] at h₁ h₂ h₃
  have e₁ := congrArg Units.val h₁
  have e₂ := congrArg Units.val h₂
  have e₃ := congrArg Units.val h₃
  simp only [Units.val_mul, Units.val_one] at e₁ e₂ e₃
  have h10 : (b (ν 1) : K) = b (ν 0) := by
    linear_combination (-(b (ν 1) : K)) * e₃ + (b (ν 0) : K) * e₂
  have h30 : (b (ν 3) : K) = b (ν 0) := by
    linear_combination (-(b (ν 3) : K)) * e₁ + (b (ν 0) : K) * e₂
  have h20 : (b (ν 2) : K) * (b (ν 0) : K) ^ 2 = 1 := by
    linear_combination e₁ - ((b (ν 0) : K) * (b (ν 2) : K)) * h10
  have c0 : TwistTag.D4.tag.cartan (ν 2) (ν 0) = -1 := by decide
  have c1 : TwistTag.D4.tag.cartan (ν 2) (ν 1) = -1 := by decide
  have c2 : TwistTag.D4.tag.cartan (ν 2) (ν 2) = 2 := by decide
  have c3 : TwistTag.D4.tag.cartan (ν 2) (ν 3) = -1 := by decide
  rw [torusElt_eq_rootDiagUnit]
  congr 1
  funext j
  refine Units.ext ?_
  fin_cases j
  · rw [c0]
    simp
  · rw [c1]
    simp [h10]
  · rw [c2]
    simp only [zpow_two, Units.val_mul, Units.val_inv_eq_inv_val]
    rw [← mul_inv, ← sq]
    exact eq_inv_of_mul_eq_one_left h20
  · rw [c3]
    simp [h30]

theorem rootChar_eq_one_of_apply {τ' : Tag} {b : Fin τ'.rank → Kˣ} {l : ModGL τ' K}
    {β : Fin τ'.rank → ℤ} (hβ : IsRoot τ' β) (hl : l ∈ vecStab (rootVec τ' K β))
    (h : ((rootDiagUnit τ' b * l : ModGL τ' K) : Module.End K (RootModule τ' K)) (rootVec τ' K β) =
      rootVec τ' K β) :
    rootChar b β = 1 := by
  rw [rootDiagUnit_mul_apply_rootVec b hβ hl] at h
  refine Units.ext ?_
  have h' : ((rootChar b β : Kˣ) : K) • rootVec τ' K β = (1 : K) • rootVec τ' K β := by
    rw [h, one_smul]
  exact eq_of_smul_rootVec hβ h'

variable [Finite K] [CharP K 2]

theorem card_le_nine_middle (σ : K →+* K) {E : Subgroup (ModGL TwistTag.D4.tag K)}
    (hE : IsElemAbelian 3 E) (hEM : E ≤ parabolicLevi TwistTag.D4.tag K {ν 2})
    (hEΓ : E ≤ twistedFixedGroup TwistTag.D4 K σ) : Nat.card E ≤ 9 := by
  have : Finite (Module.End K (RootModule TwistTag.D4.tag K)) := Module.finite_of_finite K
  have hs₀ := leviRoot_le_vecStab (K := K) isRoot_v4_1110 middle_cond_1110
  have hs₁ := leviRoot_le_vecStab (K := K) isRoot_v4_0111 middle_cond_0111
  have hs₂ := leviRoot_le_vecStab (K := K) isRoot_v4_1011 middle_cond_1011
  have hline : ∀ g ∈ E, ∃ c : K, (g : Module.End K (RootModule TwistTag.D4.tag K))
      (rootVec TwistTag.D4.tag K (v4 1 1 1 0)) = c • rootVec TwistTag.D4.tag K (v4 1 1 1 0) := by
    intro g hg
    obtain ⟨b, l, hl, rfl⟩ := exists_eq_rootDiagUnit_mul (hEM hg)
    exact ⟨_, rootDiagUnit_mul_apply_rootVec b isRoot_v4_1110 (hs₀ hl)⟩
  set φ := (lineHom isRoot_v4_1110 E hline).toHomUnits with hφ
  refine card_le_nine_of_monoidHom hE φ ?_
  have hker : φ.ker.map E.subtype ≤ leviRoot K ({ν 2} : Set (Fin TwistTag.D4.tag.rank)) := by
    rintro _ ⟨e, he, rfl⟩
    have h1 : lineHom isRoot_v4_1110 E hline e = 1 := by
      have := congrArg Units.val (MonoidHom.mem_ker.1 he)
      rwa [hφ, MonoidHom.coe_toHomUnits, Units.val_one] at this
    have hv₀ := lineHom_apply isRoot_v4_1110 E hline e
    rw [h1, one_smul] at hv₀
    have hv₁ := apply_rootVec_permLattice (hEΓ e.2) isRoot_v4_1110 (c := 1)
      (by rw [one_smul]; exact hv₀)
    rw [map_one, one_smul, permLattice_v4_1110] at hv₁
    have hv₂ := apply_rootVec_permLattice (hEΓ e.2) isRoot_v4_0111 (c := 1)
      (by rw [one_smul]; exact hv₁)
    rw [map_one, one_smul, permLattice_v4_0111] at hv₂
    obtain ⟨b, l, hl, hel⟩ := exists_eq_rootDiagUnit_mul (hEM e.2)
    rw [hel] at hv₀ hv₁ hv₂
    have hb : rootDiagUnit TwistTag.D4.tag b = torusElt TwistTag.D4.tag K (ν 2) (b (ν 0))⁻¹ :=
      rootDiagUnit_eq_torusElt_two (rootChar_eq_one_of_apply isRoot_v4_1110 (hs₀ hl) hv₀)
        (rootChar_eq_one_of_apply isRoot_v4_0111 (hs₁ hl) hv₁)
        (rootChar_eq_one_of_apply isRoot_v4_1011 (hs₂ hl) hv₂)
    change (e : ModGL TwistTag.D4.tag K) ∈ _
    rw [hel, hb]
    exact mul_mem (torusElt_mem_leviRoot (Set.mem_singleton _) _) hl
  have hEk : IsElemAbelian 3 (φ.ker.map E.subtype) := by
    refine IsElemAbelian.mono (fun x hx => ?_) hE
    obtain ⟨e, -, rfl⟩ := hx
    exact e.2
  rw [← Subgroup.card_map_of_injective (f := E.subtype) Subtype.val_injective]
  exact card_le_three_of_threeRankLeOne (threeRankLeOne_leviRoot_singleton (ν 2)) hker hEk

end Middle

section Outer

local notation "ν" n:max => (⟨n, by decide⟩ : Fin TwistTag.D4.tag.rank)

@[expose] def outerSet : Set (Fin TwistTag.D4.tag.rank) := {ν 0, ν 1, ν 3}

theorem mem_outerSet {j : Fin TwistTag.D4.tag.rank} : j ∈ outerSet ↔ j = ν 0 ∨ j = ν 1 ∨ j = ν 3 :=
  Iff.rfl

theorem isRoot_v4_1121 : IsRoot TwistTag.D4.tag (v4 1 1 2 1) :=
  isRoot_iff_mem_artifactRoots.2 (by decide)

theorem outer_cond : ∀ j ∈ outerSet,
    v4 1 1 2 1 ≠ Pi.single j 1 ∧ v4 1 1 2 1 ≠ -Pi.single j 1 ∧
      ¬ IsRoot TwistTag.D4.tag (v4 1 1 2 1 + Pi.single j 1) ∧
      ¬ IsRoot TwistTag.D4.tag (v4 1 1 2 1 - Pi.single j 1) := by
  intro j hj
  rcases mem_outerSet.1 hj with rfl | rfl | rfl <;>
  exact ⟨by decide, by decide, not_isRoot_of_not_mem (by decide),
    not_isRoot_of_not_mem (by decide)⟩

variable (K : Type) [Field K]

theorem commute_rankOneHom_outer {i j : Fin TwistTag.D4.tag.rank} (hi : i ∈ outerSet)
    (hj : j ∈ outerSet) (hij : i ≠ j) (g g' : SL2 K) :
    Commute (rankOneHom TwistTag.D4 K i g) (rankOneHom TwistTag.D4 K j g') := by
  have h : ∀ k ∈ outerSet, k ∈ TwistTag.D4.orbit ⟨0, by decide⟩ := by
    intro k hk
    rcases mem_outerSet.1 hk with rfl | rfl | rfl <;> decide
  exact commute_rankOneHom (h i hi) (h j hj) hij g g'

@[expose] def outerHom : SL2 K × SL2 K × SL2 K →* ModGL TwistTag.D4.tag K :=
  MonoidHom.noncommCoprod (rankOneHom TwistTag.D4 K (ν 0))
    (MonoidHom.noncommCoprod (rankOneHom TwistTag.D4 K (ν 1)) (rankOneHom TwistTag.D4 K (ν 3))
      fun m n => commute_rankOneHom_outer K (Or.inr (Or.inl rfl)) (Or.inr (Or.inr rfl))
        (by decide) m n)
    fun m n => (commute_rankOneHom_outer K (Or.inl rfl) (Or.inr (Or.inl rfl)) (by decide) m
      n.1).mul_right
      (commute_rankOneHom_outer K (Or.inl rfl) (Or.inr (Or.inr rfl)) (by decide) m n.2)

theorem outerHom_apply (g : SL2 K × SL2 K × SL2 K) :
    outerHom K g = rankOneHom TwistTag.D4 K (ν 0) g.1 *
      (rankOneHom TwistTag.D4 K (ν 1) g.2.1 * rankOneHom TwistTag.D4 K (ν 3) g.2.2) :=
  rfl

theorem leviRoot_outer_le_range : leviRoot K outerSet ≤ (outerHom K).range := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨j, hj, c, rfl | rfl⟩
  · rcases mem_outerSet.1 hj with rfl | rfl | rfl
    · exact ⟨(uSL c, 1, 1), by rw [outerHom_apply]; simp [rankOneHom_uSL]⟩
    · exact ⟨(1, uSL c, 1), by rw [outerHom_apply]; simp [rankOneHom_uSL]⟩
    · exact ⟨(1, 1, uSL c), by rw [outerHom_apply]; simp [rankOneHom_uSL]⟩
  · rcases mem_outerSet.1 hj with rfl | rfl | rfl
    · exact ⟨(vSL c, 1, 1), by rw [outerHom_apply]; simp [rankOneHom_vSL]⟩
    · exact ⟨(1, vSL c, 1), by rw [outerHom_apply]; simp [rankOneHom_vSL]⟩
    · exact ⟨(1, 1, vSL c), by rw [outerHom_apply]; simp [rankOneHom_vSL]⟩

variable [CharP K 2]

theorem rankOneHom_injective (i : Fin TwistTag.D4.tag.rank) :
    Function.Injective (rankOneHom TwistTag.D4 K i) :=
  injective_of_ker_scalar
    (exceptional_ordinary_rank_one_central_image TwistTag.D4.tag K i).choose_spec.2.2.2.2.2.1

theorem eq_one_of_commute_rankOneHom (i : Fin TwistTag.D4.tag.rank) {g : SL2 K}
    (h : ∀ g', Commute (rankOneHom TwistTag.D4 K i g) (rankOneHom TwistTag.D4 K i g')) :
    g = 1 := by
  have hc : g ∈ Subgroup.center (SL2 K) := Subgroup.mem_center_iff.2 fun g' =>
    rankOneHom_injective K i (by rw [map_mul, map_mul]; exact (h g').eq.symm)
  obtain ⟨r, hr, hrg⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hc
  rw [Fintype.card_fin] at hr
  refine Subtype.ext ?_
  rw [← hrg, eq_one_of_sq_eq_one hr]
  rfl

theorem outerHom_injective : Function.Injective (outerHom K) := by
  rw [injective_iff_map_eq_one]
  rintro ⟨g₀, g₁, g₃⟩ h
  rw [outerHom_apply] at h
  have h₀ : g₀ = 1 := by
    refine eq_one_of_commute_rankOneHom K (ν 0) fun g' => ?_
    rw [eq_inv_of_mul_eq_one_left h]
    exact ((commute_rankOneHom_outer K (Or.inl rfl) (Or.inr (Or.inl rfl)) (by decide) g'
      g₁).mul_right (commute_rankOneHom_outer K (Or.inl rfl) (Or.inr (Or.inr rfl)) (by decide)
        g' g₃)).symm.inv_left
  rw [h₀, map_one, one_mul] at h
  have h₁ : g₁ = 1 := by
    refine eq_one_of_commute_rankOneHom K (ν 1) fun g' => ?_
    rw [eq_inv_of_mul_eq_one_left h]
    exact (commute_rankOneHom_outer K (Or.inr (Or.inl rfl)) (Or.inr (Or.inr rfl)) (by decide)
      g' g₃).symm.inv_left
  rw [h₁, map_one, one_mul] at h
  have h₃ : g₃ = 1 := rankOneHom_injective K (ν 3) (h.trans (map_one _).symm)
  rw [h₀, h₁, h₃]
  rfl

omit [CharP K 2] in
theorem twistHom_rankOneHom (σ : K →+* K) (i : Fin TwistTag.D4.tag.rank) (g : SL2 K) :
    twistHom TwistTag.D4 K σ (rankOneHom TwistTag.D4 K i g) =
      rankOneHom TwistTag.D4 K (TwistTag.D4.perm i) (Matrix.SpecialLinearGroup.map σ g) := by
  have h := SL2_hom_ext (φ := (twistHom TwistTag.D4 K σ).comp (rankOneHom TwistTag.D4 K i))
    (ψ := (rankOneHom TwistTag.D4 K (TwistTag.D4.perm i)).comp
      (Matrix.SpecialLinearGroup.map σ))
    (fun s => by
      simp only [MonoidHom.comp_apply, rankOneHom_uSL, twistHom_xUnit, map_uSL])
    (fun u => by
      simp only [MonoidHom.comp_apply, rankOneHom_HSL, twistHom_torusElt, map_HSL])
    (by simp only [MonoidHom.comp_apply, rankOneHom_WSL, twistHom_weylElt_one, map_WSL])
  exact DFunLike.congr_fun h g

theorem perm_zero : TwistTag.D4.perm (ν 0) = ν 1 := by decide
theorem perm_one : TwistTag.D4.perm (ν 1) = ν 3 := by decide
theorem perm_three : TwistTag.D4.perm (ν 3) = ν 0 := by decide

theorem outer_fixed (σ : K →+* K) {g : SL2 K × SL2 K × SL2 K}
    (hg : twistHom TwistTag.D4 K σ (outerHom K g) = outerHom K g) :
    g.2.1 = Matrix.SpecialLinearGroup.map σ g.1 ∧
      g.2.2 = Matrix.SpecialLinearGroup.map σ g.2.1 := by
  have e : twistHom TwistTag.D4 K σ (outerHom K g) =
      outerHom K (Matrix.SpecialLinearGroup.map σ g.2.2, Matrix.SpecialLinearGroup.map σ g.1,
        Matrix.SpecialLinearGroup.map σ g.2.1) := by
    rw [outerHom_apply, outerHom_apply, map_mul, map_mul, twistHom_rankOneHom,
      twistHom_rankOneHom, twistHom_rankOneHom, perm_zero, perm_one, perm_three]
    have hc₁ := commute_rankOneHom_outer K (Or.inl rfl) (Or.inr (Or.inl rfl)) (by decide)
      (Matrix.SpecialLinearGroup.map σ g.2.2) (Matrix.SpecialLinearGroup.map σ g.1)
    have hc₃ := commute_rankOneHom_outer K (Or.inl rfl) (Or.inr (Or.inr rfl)) (by decide)
      (Matrix.SpecialLinearGroup.map σ g.2.2) (Matrix.SpecialLinearGroup.map σ g.2.1)
    dsimp only
    rw [← mul_assoc]
    exact (hc₁.mul_right hc₃).eq.symm
  have h := outerHom_injective K (e.symm.trans hg)
  exact ⟨(congrArg (fun x => x.2.1) h).symm, (congrArg (fun x => x.2.2) h).symm⟩

@[expose] def outerFirst (σ : K →+* K) :
    ↥(leviRoot K outerSet ⊓ twistedFixedGroup TwistTag.D4 K σ) →* SL2 K :=
  (MonoidHom.fst _ _).comp (((MonoidHom.ofInjective (outerHom_injective K)).symm.toMonoidHom).comp
    (Subgroup.inclusion (inf_le_left.trans (leviRoot_outer_le_range K))))

theorem outerFirst_injective (σ : K →+* K) : Function.Injective (outerFirst K σ) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  set y := Subgroup.inclusion (inf_le_left.trans (leviRoot_outer_le_range K)) x with hy
  set g := (MonoidHom.ofInjective (outerHom_injective K)).symm y with hgdef
  have hΦg : outerHom K g = (x : ModGL TwistTag.D4.tag K) := by
    have := (MonoidHom.ofInjective (outerHom_injective K)).apply_symm_apply y
    exact congrArg Subtype.val this
  have hg1 : g.1 = 1 := hx
  have hF : twistHom TwistTag.D4 K σ (outerHom K g) = outerHom K g := by
    rw [hΦg]
    exact ((mem_twistedFixedGroup_iff_twistHom (t := TwistTag.D4) (K := K) (σ := σ)).1
      x.2.2).2
  obtain ⟨h21, h22⟩ := outer_fixed K σ hF
  have hg : g = 1 := by
    have h1' : g.2.1 = 1 := by rw [h21, hg1, map_one]
    have h2' : g.2.2 = 1 := by rw [h22, h1', map_one]
    exact Prod.ext hg1 (Prod.ext h1' h2')
  apply Subtype.ext
  rw [← hΦg, hg, map_one]
  rfl

theorem threeRankLeOne_outer (σ : K →+* K) :
    ThreeRankLeOne ↥(leviRoot K outerSet ⊓ twistedFixedGroup TwistTag.D4 K σ) :=
  ThreeRankLeOne.of_injective (outerFirst_injective K σ) (threeRankLeOne_SL2 (K := K))

end Outer

section Count

local notation "ν" n:max => (⟨n, by decide⟩ : Fin TwistTag.D4.tag.rank)

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem exists_sq_eq_unit (x : Kˣ) : ∃ y : Kˣ, y ^ 2 = x := by
  obtain ⟨r, hr⟩ := isSquare_of_charTwo' (x : K)
  have hr0 : r ≠ 0 := fun h0 => x.ne_zero (by rw [hr, h0, mul_zero])
  exact ⟨Units.mk0 r hr0, Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_mk0, sq, hr])⟩

theorem rootDiagUnit_mem_leviRoot_outer {b : Fin TwistTag.D4.tag.rank → Kˣ}
    (h : rootChar b (v4 1 1 2 1) = 1) : rootDiagUnit TwistTag.D4.tag b ∈ leviRoot K outerSet := by
  rw [rootChar_v4] at h
  simp only [zpow_one] at h
  obtain ⟨u₀, hu₀⟩ := exists_sq_eq_unit (b (ν 0))
  obtain ⟨u₁, hu₁⟩ := exists_sq_eq_unit (b (ν 1))
  obtain ⟨u₃, hu₃⟩ := exists_sq_eq_unit (b (ν 3))
  have hb₂ : b (ν 2) = (u₀ * u₁ * u₃)⁻¹ := by
    have hw : ((u₀ * u₁ * u₃ * b (ν 2) : Kˣ) : K) ^ 2 = 1 := by
      have := congrArg Units.val h
      rw [← hu₀, ← hu₁, ← hu₃] at this
      simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_one, zpow_two] at this ⊢
      linear_combination this
    exact eq_inv_of_mul_eq_one_right (Units.ext (by simpa using eq_one_of_sq_eq_one hw))
  have heq : rootDiagUnit TwistTag.D4.tag b = torusElt TwistTag.D4.tag K (ν 0) u₀ *
      torusElt TwistTag.D4.tag K (ν 1) u₁ * torusElt TwistTag.D4.tag K (ν 3) u₃ := by
    rw [torusElt_eq_rootDiagUnit, torusElt_eq_rootDiagUnit, torusElt_eq_rootDiagUnit,
      ← rootDiagUnit_mul, ← rootDiagUnit_mul]
    congr 1
    funext j
    have c00 : TwistTag.D4.tag.cartan (ν 0) (ν 0) = 2 := by decide
    have c01 : TwistTag.D4.tag.cartan (ν 0) (ν 1) = 0 := by decide
    have c02 : TwistTag.D4.tag.cartan (ν 0) (ν 2) = -1 := by decide
    have c03 : TwistTag.D4.tag.cartan (ν 0) (ν 3) = 0 := by decide
    have c10 : TwistTag.D4.tag.cartan (ν 1) (ν 0) = 0 := by decide
    have c11 : TwistTag.D4.tag.cartan (ν 1) (ν 1) = 2 := by decide
    have c12 : TwistTag.D4.tag.cartan (ν 1) (ν 2) = -1 := by decide
    have c13 : TwistTag.D4.tag.cartan (ν 1) (ν 3) = 0 := by decide
    have c30 : TwistTag.D4.tag.cartan (ν 3) (ν 0) = 0 := by decide
    have c31 : TwistTag.D4.tag.cartan (ν 3) (ν 1) = 0 := by decide
    have c32 : TwistTag.D4.tag.cartan (ν 3) (ν 2) = -1 := by decide
    have c33 : TwistTag.D4.tag.cartan (ν 3) (ν 3) = 2 := by decide
    fin_cases j
    · simp only [Pi.mul_apply]
      rw [c00, c10, c30, zpow_zero, zpow_zero, mul_one, mul_one, ← hu₀]
      rfl
    · simp only [Pi.mul_apply]
      rw [c01, c11, c31, zpow_zero, zpow_zero, mul_one, one_mul, ← hu₁]
      rfl
    · simp only [Pi.mul_apply]
      rw [c02, c12, c32, hb₂, zpow_neg_one, zpow_neg_one, zpow_neg_one, mul_inv, mul_inv]
    · simp only [Pi.mul_apply]
      rw [c03, c13, c33, zpow_zero, zpow_zero, one_mul, one_mul, ← hu₃]
      rfl
  rw [heq]
  refine mul_mem (mul_mem ?_ ?_) ?_
  · exact torusElt_mem_leviRoot (mem_outerSet.2 (Or.inl rfl)) _
  · exact torusElt_mem_leviRoot (mem_outerSet.2 (Or.inr (Or.inl rfl))) _
  · exact torusElt_mem_leviRoot (mem_outerSet.2 (Or.inr (Or.inr rfl))) _

theorem card_le_nine_outer (σ : K →+* K) {E : Subgroup (ModGL TwistTag.D4.tag K)}
    (hE : IsElemAbelian 3 E) (hEM : E ≤ parabolicLevi TwistTag.D4.tag K outerSet)
    (hEΓ : E ≤ twistedFixedGroup TwistTag.D4 K σ) : Nat.card E ≤ 9 := by
  have : Finite (Module.End K (RootModule TwistTag.D4.tag K)) := Module.finite_of_finite K
  have hs := leviRoot_le_vecStab (K := K) isRoot_v4_1121 outer_cond
  have hline : ∀ g ∈ E, ∃ c : K, (g : Module.End K (RootModule TwistTag.D4.tag K))
      (rootVec TwistTag.D4.tag K (v4 1 1 2 1)) = c • rootVec TwistTag.D4.tag K (v4 1 1 2 1) := by
    intro g hg
    obtain ⟨b, l, hl, rfl⟩ := exists_eq_rootDiagUnit_mul (hEM hg)
    exact ⟨_, rootDiagUnit_mul_apply_rootVec b isRoot_v4_1121 (hs hl)⟩
  set φ := (lineHom isRoot_v4_1121 E hline).toHomUnits with hφ
  refine card_le_nine_of_monoidHom hE φ ?_
  have hker : φ.ker.map E.subtype ≤ leviRoot K outerSet ⊓ twistedFixedGroup TwistTag.D4 K σ := by
    rintro _ ⟨e, he, rfl⟩
    have h1 : lineHom isRoot_v4_1121 E hline e = 1 := by
      have := congrArg Units.val (MonoidHom.mem_ker.1 he)
      rwa [hφ, MonoidHom.coe_toHomUnits, Units.val_one] at this
    have hv := lineHom_apply isRoot_v4_1121 E hline e
    rw [h1, one_smul] at hv
    obtain ⟨b, l, hl, hel⟩ := exists_eq_rootDiagUnit_mul (hEM e.2)
    rw [hel] at hv
    have hb := rootDiagUnit_mem_leviRoot_outer
      (rootChar_eq_one_of_apply isRoot_v4_1121 (hs hl) hv)
    refine ⟨?_, hEΓ e.2⟩
    change (e : ModGL TwistTag.D4.tag K) ∈ _
    rw [hel]
    exact mul_mem hb hl
  have hEk : IsElemAbelian 3 (φ.ker.map E.subtype) := by
    refine IsElemAbelian.mono (fun x hx => ?_) hE
    obtain ⟨e, -, rfl⟩ := hx
    exact e.2
  rw [← Subgroup.card_map_of_injective (f := E.subtype) Subtype.val_injective]
  exact card_le_three_of_threeRankLeOne (threeRankLeOne_outer K σ) hker hEk

theorem card_le_nine_of_le_graphFixedParabolicLevi {σ : K →+* K}
    {J : Set (Fin TwistTag.D4.foldedTag.rank)} (hJ : J ≠ Set.univ)
    {E : Subgroup (ModGL TwistTag.D4.tag K)} (hE : IsElemAbelian 3 E)
    (hEL : E ≤ graphFixedParabolicLevi TwistTag.D4 K σ J) : Nat.card E ≤ 9 := by
  have hEΓ : E ≤ twistedFixedGroup TwistTag.D4 K σ :=
    hEL.trans (inf_le_right.trans (graphFixedRootGroup_le TwistTag.D4 K σ))
  have hEM : E ≤ parabolicLevi TwistTag.D4.tag K (TwistTag.D4.orbitUnion J) := hEL.trans inf_le_left
  obtain ⟨a, ha⟩ : ∃ a, a ∉ J := by
    by_contra h
    push Not at h
    exact hJ (Set.eq_univ_of_forall h)
  have horb₀ : ∀ i : Fin TwistTag.D4.tag.rank, i ∈ TwistTag.D4.orbit ⟨0, by decide⟩ →
      i = ν 0 ∨ i = ν 1 ∨ i = ν 3 := by decide
  have horb₁ : ∀ i : Fin TwistTag.D4.tag.rank, i ∈ TwistTag.D4.orbit ⟨1, by decide⟩ → i = ν 2 := by
    decide
  fin_cases a
  · have hsub : TwistTag.D4.orbitUnion J ⊆ {ν 2} := by
      intro i hi
      obtain ⟨c, hcJ, hic⟩ := (TwistTag.mem_orbitUnion _).1 hi
      fin_cases c
      · exact absurd hcJ ha
      · exact horb₁ i hic
    exact card_le_nine_middle σ hE (hEM.trans (parabolicLevi_mono hsub)) hEΓ
  · have hsub : TwistTag.D4.orbitUnion J ⊆ outerSet := by
      intro i hi
      obtain ⟨c, hcJ, hic⟩ := (TwistTag.mem_orbitUnion _).1 hi
      fin_cases c
      · exact horb₀ i hic
      · exact absurd hcJ ha
    exact card_le_nine_outer σ hE (hEM.trans (parabolicLevi_mono hsub)) hEΓ

end Count

end CFSG.RankThree.PartTwo.Census.Carrier.D4Even
