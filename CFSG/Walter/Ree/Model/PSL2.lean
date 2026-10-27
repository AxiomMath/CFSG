module

public import CFSG.Walter.Ree.Model.Cells
public import CFSG.LieType.Chevalley.GraphFixedRankOneImage
public import CFSG.Walter.ReeOrder.JT.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Cardinality
public import CFSG.LieType.Chevalley.RootCommutator

public noncomputable section

namespace CFSG.Walter.Ree.Model

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
open CFSG.LieType.Ree.ReeTag
open scoped MatrixGroups

section Roots

variable {R : Type} [CommRing R]

theorem commute_pinnedX_of_not_isRoot'
    {τ : Tag} {γ δ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ)
    (hδ : IsRoot τ δ) (hne : γ ≠ δ) (hne' : γ ≠ -δ)
    (h : ∀ a b : ℕ, 0 < a → 0 < b → ¬ IsRoot τ (a • γ + b • δ)) (c d : R) :
    Commute (pinnedX τ R γ c) (pinnedX τ R δ d) := by
  obtain ⟨-, hmem, -, -, hF⟩ := root_commutator_formula τ hγ hδ hne hne'
  have hnil : commPairs τ γ δ = [] := List.eq_nil_iff_forall_not_mem.2 fun p hp => by
    obtain ⟨h1, h2, hr⟩ := (hmem p).1 hp
    exact h p.1 p.2 h1 h2 hr
  have hF' := hF R c d
  rw [hnil, List.map_nil, List.prod_nil, ← pinnedX_neg, ← pinnedX_neg, ← commutatorElement_def,
    commutatorElement_eq_one_iff_mul_comm] at hF'
  exact hF'

theorem isRoot_g2Root11 :
    IsRoot G2.tag g2Root11 :=
  RootOps.isRootB_iff.1 (by decide +kernel)

theorem isRoot_g2Root13 :
    IsRoot G2.tag g2Root13 :=
  RootOps.isRootB_iff.1 (by decide +kernel)

theorem g2_not_isRoot_pos
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    ¬ IsRoot G2.tag (a • g2Root11 + b • g2Root13) :=
  forall_not_isRoot_of_check (k := g2I0) (l := g2I0) (by decide) (by decide) (by decide)
    (by decide) (by decide +kernel) a b ha hb

theorem g2_not_isRoot_mixed
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    ¬ IsRoot G2.tag (a • g2Root11 + b • -g2Root13) := by
  intro hr
  have e0 : (a • g2Root11 + b • -g2Root13) g2I0 = (a : ℤ) - b := by
    show a • (1 : ℤ) + b • (-1 : ℤ) = _
    simp only [nsmul_eq_mul, mul_one, mul_neg]
    ring
  have e1 : (a • g2Root11 + b • -g2Root13) g2I1 = (a : ℤ) - 3 * b := by
    show a • (1 : ℤ) + b • (-3 : ℤ) = _
    simp only [nsmul_eq_mul, mul_one, mul_neg]
    ring
  have h0 := RootOps.le_seven_of_isRoot hr g2I0
  have h1 := RootOps.le_seven_of_isRoot hr g2I1
  have h0' := RootOps.le_seven_of_isRoot (IsRoot.neg hr) g2I0
  have h1' := RootOps.le_seven_of_isRoot (IsRoot.neg hr) g2I1
  rw [Pi.neg_apply] at h0' h1'
  rw [e0] at h0 h0'
  rw [e1] at h1 h1'
  have key : ∀ a < 15, ∀ b < 8, 1 ≤ a → 1 ≤ b →
      RootOps.isRootB G2.tag (a • g2Root11 + b • -g2Root13) = false := by
    decide +kernel
  rw [← RootOps.isRootB_iff, key a (by omega) b (by omega) ha hb] at hr
  exact Bool.false_ne_true hr

theorem g2_not_isRoot
    {γ δ : Fin G2.tag.rank → ℤ} (hγ : γ = g2Root11 ∨ γ = -g2Root11)
    (hδ : δ = g2Root13 ∨ δ = -g2Root13) (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    ¬ IsRoot G2.tag (a • γ + b • δ) := by
  have hneg : ∀ v w : Fin G2.tag.rank → ℤ, IsRoot G2.tag (a • -v + b • -w) →
      IsRoot G2.tag (a • v + b • w) := fun v w h => by
    have h' := IsRoot.neg h
    rwa [smul_neg, smul_neg, ← neg_add, neg_neg] at h'
  have hmix : ∀ v w : Fin G2.tag.rank → ℤ, IsRoot G2.tag (a • -v + b • w) →
      IsRoot G2.tag (a • v + b • -w) := fun v w h => by
    have h' := IsRoot.neg h
    rwa [smul_neg, neg_add, neg_neg, ← smul_neg] at h'
  rcases hγ with rfl | rfl <;> rcases hδ with rfl | rfl
  · exact g2_not_isRoot_pos a b ha hb
  · exact g2_not_isRoot_mixed a b ha hb
  · exact fun h => g2_not_isRoot_mixed a b ha hb (hmix _ _ h)
  · exact fun h => g2_not_isRoot_pos a b ha hb (hneg _ _ h)

theorem commute_of_mem_rootSubgroup
    {γ δ : Fin G2.tag.rank → ℤ}
    (hγ : γ = g2Root11 ∨ γ = -g2Root11) (hδ : δ = g2Root13 ∨ δ = -g2Root13)
    {x y : (Module.End R (RootModule G2.tag R))ˣ} (hx : x ∈ rootSubgroup G2.tag R γ)
    (hy : y ∈ rootSubgroup G2.tag R δ) : Commute x y := by
  obtain ⟨c, rfl⟩ := mem_rootSubgroup.1 hx
  obtain ⟨d, rfl⟩ := mem_rootSubgroup.1 hy
  have hrγ : IsRoot G2.tag γ := by
    rcases hγ with rfl | rfl
    exacts [isRoot_g2Root11, IsRoot.neg isRoot_g2Root11]
  have hrδ : IsRoot G2.tag δ := by
    rcases hδ with rfl | rfl
    exacts [isRoot_g2Root13, IsRoot.neg isRoot_g2Root13]
  have hne : γ ≠ δ ∧ γ ≠ -δ := by
    rcases hγ with rfl | rfl <;> rcases hδ with rfl | rfl <;> decide
  exact commute_pinnedX_of_not_isRoot' hrγ hrδ hne.1 hne.2 (g2_not_isRoot hγ hδ) c d

end Roots

theorem commute_of_mem_closure {G : Type*} [Group G] {A B : Set G}
    (h : ∀ x ∈ A, ∀ y ∈ B, Commute x y) {x y : G} (hx : x ∈ Subgroup.closure A)
    (hy : y ∈ Subgroup.closure B) : Commute x y := by
  have hle : Subgroup.closure A ≤ Subgroup.centralizer (Subgroup.closure B : Set G) := by
    refine (Subgroup.closure_le _).2 fun x hx => ?_
    have hle' : Subgroup.closure B ≤ Subgroup.centralizer {x} :=
      (Subgroup.closure_le _).2 fun y hy z hz => by
        rw [Set.mem_singleton_iff] at hz
        subst hz
        exact (h z hx y hy).eq
    exact Subgroup.mem_centralizer_iff.2 fun y hy => (hle' hy x rfl).symm
  exact ((Subgroup.mem_centralizer_iff.1 (hle hx)) _ hy).symm

section RankOne

variable {K : Type} [Field K]

variable (K) in
@[expose] def smallReeRankOne
    (i : Fin ReeTag.G2.tag.rank) : SL2 K →* ModGL ReeTag.G2.tag K :=
  (exceptional_ordinary_rank_one_central_image ReeTag.G2.tag K i).choose

theorem smallReeRankOne_uSL
    (i : Fin G2.tag.rank) (c : K) :
    smallReeRankOne K i (uSL c) = xUnit G2.tag K i c :=
  (exceptional_ordinary_rank_one_central_image G2.tag K i).choose_spec.1 c

theorem smallReeRankOne_vSL
    (i : Fin G2.tag.rank) (c : K) :
    smallReeRankOne K i (vSL c) = yUnit G2.tag K i c :=
  (exceptional_ordinary_rank_one_central_image G2.tag K i).choose_spec.2.1 c

theorem smallReeRankOne_HSL
    (i : Fin G2.tag.rank) (u : Kˣ) :
    smallReeRankOne K i (HSL u) = torusElt G2.tag K i u :=
  (exceptional_ordinary_rank_one_central_image G2.tag K i).choose_spec.2.2.1 u

theorem smallReeRankOne_WSL
    (i : Fin G2.tag.rank) :
    smallReeRankOne K i WSL = weylElt G2.tag K i 1 :=
  (exceptional_ordinary_rank_one_central_image G2.tag K i).choose_spec.2.2.2.1

theorem smallReeRankOne_range
    (i : Fin G2.tag.rank) :
    (smallReeRankOne K i).range =
      Subgroup.closure (Set.range (xUnit G2.tag K i) ∪ Set.range (yUnit G2.tag K i)) :=
  (exceptional_ordinary_rank_one_central_image G2.tag K i).choose_spec.2.2.2.2.1

variable (K) in
@[expose] def smallReeR :
    SL2 K →* ModGL ReeTag.G2.tag K :=
  (MulAut.conj (weylElt ReeTag.G2.tag K g2I0 1)).toMonoidHom.comp (smallReeRankOne K g2I1)

variable (K) in
@[expose] def smallReeS :
    SL2 K →* ModGL ReeTag.G2.tag K :=
  (MulAut.conj (weylElt ReeTag.G2.tag K g2I1 1)).toMonoidHom.comp (smallReeRankOne K g2I0)

theorem smallReeR_apply
    (g : SL2 K) :
    smallReeR K g = weylElt G2.tag K g2I0 1 * smallReeRankOne K g2I1 g *
      (weylElt G2.tag K g2I0 1)⁻¹ :=
  rfl

theorem smallReeS_apply
    (g : SL2 K) :
    smallReeS K g = weylElt G2.tag K g2I1 1 * smallReeRankOne K g2I0 g *
      (weylElt G2.tag K g2I1 1)⁻¹ :=
  rfl

theorem smallReeR_uSL
    (b : K) : smallReeR K (uSL b) = smallReeX K 2 b := by
  rw [smallReeR_apply, smallReeRankOne_uSL]
  exact (pinnedX_eq_of_pinnedData pinnedData_g2Root11 b).symm

theorem smallReeS_uSL
    (b : K) : smallReeS K (uSL b) = smallReeX K 4 b := by
  rw [smallReeS_apply, smallReeRankOne_uSL]
  exact (pinnedX_eq_of_pinnedData pinnedData_g2Root13 b).symm

theorem weylElt_conj_mem_rootSubgroup
    (i : Fin G2.tag.rank) {α : Fin G2.tag.rank → ℤ}
    (hα : IsRoot G2.tag α) {x : ModGL G2.tag K} (hx : x ∈ rootSubgroup G2.tag K α) :
    weylElt G2.tag K i 1 * x * (weylElt G2.tag K i 1)⁻¹ ∈
      rootSubgroup G2.tag K (reflect G2.tag i α) := by
  rw [← map_conj_weylElt_rootSubgroup K i hα]
  exact ⟨x, hx, rfl⟩

theorem xUnit_mem_rootSubgroup
    (i : Fin G2.tag.rank) (c : K) :
    xUnit G2.tag K i c ∈ rootSubgroup G2.tag K (Pi.single i 1) := by
  rw [← pinnedX_single]
  exact Subgroup.subset_closure ⟨c, rfl⟩

theorem yUnit_mem_rootSubgroup
    (i : Fin G2.tag.rank) (c : K) :
    yUnit G2.tag K i c ∈ rootSubgroup G2.tag K (-Pi.single i 1) := by
  rw [← pinnedX_neg_single]
  exact Subgroup.subset_closure ⟨c, rfl⟩

theorem conj_smallReeRankOne_mem_closure
    (i j : Fin G2.tag.rank) (g : SL2 K) :
    weylElt G2.tag K i 1 * smallReeRankOne K j g * (weylElt G2.tag K i 1)⁻¹ ∈
      Subgroup.closure ((rootSubgroup G2.tag K (reflect G2.tag i (Pi.single j 1)) :
        Set (ModGL G2.tag K)) ∪ rootSubgroup G2.tag K (reflect G2.tag i (-Pi.single j 1))) := by
  have hg : smallReeRankOne K j g ∈ (smallReeRankOne K j).range := ⟨g, rfl⟩
  rw [smallReeRankOne_range] at hg
  have hg' : (MulAut.conj (weylElt G2.tag K i 1)).toMonoidHom (smallReeRankOne K j g) ∈
      (Subgroup.closure (Set.range (xUnit G2.tag K j) ∪ Set.range (yUnit G2.tag K j))).map
        (MulAut.conj (weylElt G2.tag K i 1)).toMonoidHom := ⟨_, hg, rfl⟩
  rw [MonoidHom.map_closure] at hg'
  refine Subgroup.closure_mono ?_ hg'
  rintro _ ⟨z, (⟨c, rfl⟩ | ⟨c, rfl⟩), rfl⟩
  · exact Or.inl (weylElt_conj_mem_rootSubgroup i (isRoot_single _ j) (xUnit_mem_rootSubgroup j c))
  · exact Or.inr (weylElt_conj_mem_rootSubgroup i (isRoot_neg_single _ j)
      (yUnit_mem_rootSubgroup j c))

theorem commute_smallReeR_smallReeS
    (g g' : SL2 K) : Commute (smallReeR K g) (smallReeS K g') := by
  have hR := conj_smallReeRankOne_mem_closure (K := K) g2I0 g2I1 g
  have hS := conj_smallReeRankOne_mem_closure (K := K) g2I1 g2I0 g'
  have e1 : reflect G2.tag g2I0 (Pi.single g2I1 1) = g2Root11 := by decide
  have e2 : reflect G2.tag g2I0 (-Pi.single g2I1 1) = -g2Root11 := by decide
  have e3 : reflect G2.tag g2I1 (Pi.single g2I0 1) = g2Root13 := by decide
  have e4 : reflect G2.tag g2I1 (-Pi.single g2I0 1) = -g2Root13 := by decide
  rw [e1, e2] at hR
  rw [e3, e4] at hS
  refine commute_of_mem_closure ?_ hR hS
  rintro x (hx | hx) y (hy | hy)
  · exact commute_of_mem_rootSubgroup (Or.inl rfl) (Or.inl rfl) hx hy
  · exact commute_of_mem_rootSubgroup (Or.inl rfl) (Or.inr rfl) hx hy
  · exact commute_of_mem_rootSubgroup (Or.inr rfl) (Or.inl rfl) hx hy
  · exact commute_of_mem_rootSubgroup (Or.inr rfl) (Or.inr rfl) hx hy

end RankOne

theorem g2Check_psiW :
    constCheck G2.tag 3 (g2WeylWord g2I0 ++ g2WeylWord g2I1 ++ g2WeylWordInv g2I0 ++
      g2WeylWord g2I1 ++ g2WeylWord g2I0 ++ g2WeylWordInv g2I1) g2LongWord = true := by
  decide +kernel

section Psi

variable {K : Type} [Field K] [CharP K G2.prime] {a : ℕ}

variable (K) in
@[expose] def smallReeSigmaHom (a : ℕ) : K →+* K :=
  haveI : CharP K 3 := ‹CharP K ReeTag.G2.prime›
  iterateFrobenius K 3 (a + 1)

theorem smallReeSigmaHom_apply (x : K) : smallReeSigmaHom K a x = smallReeSigma a x := by
  have : CharP K 3 := ‹CharP K G2.prime›
  rw [smallReeSigmaHom, iterateFrobenius_def, smallReeSigma, pow_succ']

variable (K a) in
@[expose] def smallReePsi :
    SL2 K →* ModGL ReeTag.G2.tag K where
  toFun g := smallReeR K g * smallReeS K (Matrix.SpecialLinearGroup.map (smallReeSigmaHom K a) g)
  map_one' := by simp
  map_mul' g h := by
    simp only [map_mul]
    exact (commute_smallReeR_smallReeS h _).mul_mul_mul_comm _ _

theorem smallReePsi_apply
    (g : SL2 K) :
    smallReePsi K a g =
      smallReeR K g * smallReeS K (Matrix.SpecialLinearGroup.map (smallReeSigmaHom K a) g) :=
  rfl

theorem smallReePsi_uSL
    (b : K) : smallReePsi K a (uSL b) = smallReeU a K 0 b 0 := by
  rw [smallReePsi_apply, map_uSL, smallReeR_uSL, smallReeS_uSL, smallReeSigmaHom_apply]
  show _ = smallReeCoord a K 0 b 0
  simp [smallReeCoord, smallReeSigma_zero, smallReeX_zero]
  rfl

theorem smallReePsi_WSL
    {w₀ : WeylGroup G2.tag}
    (hw₀ : ∀ w, (coxeterSystem G2.tag).length w ≤ (coxeterSystem G2.tag).length w₀) :
    smallReePsi K a WSL = canonicalRep (coxeterSystem G2.tag) K w₀ := by
  have h3 : ((3 : ℕ) : K) = 0 := g2_three_eq_zero K
  rw [smallReePsi_apply, map_WSL, smallReeR_apply, smallReeS_apply, smallReeRankOne_WSL,
    smallReeRankOne_WSL, canonicalRep_longest hw₀, weylElt_inv, weylElt_inv,
    weylElt_eq_constPinned, weylElt_eq_constPinned, weylElt_neg_one_eq_constPinned,
    weylElt_neg_one_eq_constPinned, ← constPinned_eq_of_constCheck g2Check_psiW K h3]
  simp only [constPinned_append, mul_assoc]

theorem smallReePsi_HSL
    [Finite K] (hK : Nat.card K = 3 ^ (2 * a + 1)) (r : Kˣ) :
    smallReePsi K a (HSL r) = smallReeH a K (r ^ (3 + 3 * 3 ^ a)) := by
  have hc10 : G2.tag.cartan g2I1 g2I0 = -3 := by decide
  have hc01 : G2.tag.cartan g2I0 g2I1 = -1 := by decide
  set s : Kˣ := Units.map (smallReeSigmaHom K a).toMonoidHom r with hs
  have hsr : (s : K) = (r : K) ^ (3 * 3 ^ a) := by
    rw [hs, Units.coe_map]
    exact smallReeSigmaHom_apply (r : K)
  have hR : smallReeR K (HSL r) = torusElt G2.tag K g2I1 r * torusElt G2.tag K g2I0 (r ^ 3) := by
    rw [smallReeR_apply, smallReeRankOne_HSL, weylElt_one_mul_torusElt_mul_inv, hc10, neg_neg]
    rfl
  have hS : smallReeS K (HSL s) = torusElt G2.tag K g2I0 s * torusElt G2.tag K g2I1 s := by
    rw [smallReeS_apply, smallReeRankOne_HSL, weylElt_one_mul_torusElt_mul_inv, hc01, neg_neg,
      zpow_one]
  have hq : ∀ x : K, x ^ 3 ^ (2 * a + 1) = x := fun x => by
    have := Fintype.ofFinite K
    rw [← hK, Nat.card_eq_fintype_card, FiniteField.pow_card]
  have e0 : r ^ 3 * s = r ^ (3 + 3 * 3 ^ a) := by
    refine Units.ext ?_
    rw [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, hsr, pow_add]
  have e1 : r * s = (r ^ (3 + 3 * 3 ^ a)) ^ 3 ^ a := by
    refine Units.ext ?_
    rw [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, hsr, ← pow_mul,
      show (3 + 3 * 3 ^ a) * 3 ^ a = 3 * 3 ^ a + 3 ^ (2 * a + 1) by ring, pow_add, hq, mul_comm]
  rw [smallReePsi_apply, map_HSL, ← hs, hR, hS]
  show _ = torusElt G2.tag K g2I0 (r ^ (3 + 3 * 3 ^ a)) *
    torusElt G2.tag K g2I1 ((r ^ (3 + 3 * 3 ^ a)) ^ 3 ^ a)
  rw [← e1, ← e0, torusElt_mul, torusElt_mul, torusElt_mul_comm g2I1 g2I0 r (r ^ 3)]
  simp only [mul_assoc, mul_right_inj]
  rw [← mul_assoc, torusElt_mul_comm g2I1 g2I0 r s, mul_assoc]

end Psi

section Structure

variable {K : Type} [Field K] [Finite K] [CharP K G2.prime] {a : ℕ}

omit [Finite K] in
theorem neg_one_ne_one_of_charP : (-1 : K) ≠ 1 := by
  intro h
  have h3 := smallRee_three_eq_zero (K := K)
  have h1 : (1 : K) = 0 := by linear_combination h + h3
  exact one_ne_zero h1

theorem sq_eq_one_of_pow_eq_one (hK : Nat.card K = 3 ^ (2 * a + 1)) {x : K} (hx0 : x ≠ 0)
    (h : x ^ (3 + 3 * 3 ^ a) = 1) : x ^ 2 = 1 := by
  have : CharP K 3 := ‹CharP K G2.prime›
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hq : x ^ 3 ^ (2 * a + 1) = x := by
    have := Fintype.ofFinite K
    rw [← hK, Nat.card_eq_fintype_card, FiniteField.pow_card]
  have hv : x ^ (1 + 3 ^ a) = 1 := by
    have h3 : (x ^ (1 + 3 ^ a) - 1) ^ 3 = 0 := by
      rw [sub_pow_char, one_pow, ← pow_mul, show (1 + 3 ^ a) * 3 = 3 + 3 * 3 ^ a by ring, h,
        sub_self]
    exact sub_eq_zero.1 ((pow_eq_zero_iff (by norm_num)).1 h3)
  have hθ : x ^ 3 ^ a = x⁻¹ := by
    rw [pow_add, pow_one] at hv
    exact eq_inv_of_mul_eq_one_right hv
  have hθθ : (x ^ 3 ^ a) ^ 3 ^ a = x := by rw [hθ, inv_pow, hθ, inv_inv]
  have h3 : x ^ 3 = x := by
    rw [← pow_mul] at hθθ
    calc x ^ 3 = (x ^ (3 ^ a * 3 ^ a)) ^ 3 := by rw [hθθ]
      _ = x := by rw [← pow_mul, show 3 ^ a * 3 ^ a * 3 = 3 ^ (2 * a + 1) by ring, hq]
  have hm : x * (x ^ 2 - 1) = 0 := by linear_combination h3
  rcases mul_eq_zero.1 hm with h0 | h1
  · exact absurd h0 hx0
  · exact sub_eq_zero.1 h1

omit [CharP K G2.prime] in
theorem not_isSquare_neg_one (hK : Nat.card K = 3 ^ (2 * a + 1)) : ¬ IsSquare (-1 : K) := by
  have := Fintype.ofFinite K
  rw [FiniteField.isSquare_neg_one_iff, ← Nat.card_eq_fintype_card, hK, pow_succ, pow_mul,
    Nat.mul_mod, Nat.pow_mod]
  norm_num

omit [Finite K] [CharP K G2.prime] in
theorem uSL_zero : uSL (0 : K) = 1 :=
  SL2_ext (by simp [coe_uSL]) (by simp [coe_uSL]) (by simp [coe_uSL]) (by simp [coe_uSL])

omit [Finite K] [CharP K G2.prime] in
theorem HSL_one : HSL (1 : Kˣ) = 1 :=
  SL2_ext (by simp [coe_HSL]) (by simp [coe_HSL]) (by simp [coe_HSL]) (by simp [coe_HSL])

omit [Finite K] [CharP K G2.prime] in
theorem HSL_neg_one : HSL (-1 : Kˣ) = -1 :=
  SL2_ext (by simp [coe_HSL]) (by simp [coe_HSL]) (by simp [coe_HSL]) (by simp [coe_HSL])

omit [Finite K] in
theorem one_ne_neg_one_SL2 : (1 : SL2 K) ≠ -1 := by
  intro h
  have h' := congrArg (fun g : SL2 K => (g : Matrix (Fin 2) (Fin 2) K) 0 0) h
  simp only [Matrix.SpecialLinearGroup.coe_one, Matrix.SpecialLinearGroup.coe_neg,
    Matrix.one_apply_eq, Matrix.neg_apply] at h'
  exact neg_one_ne_one_of_charP h'.symm

variable (hK : Nat.card K = 3 ^ (2 * a + 1))
include hK

theorem smallReePsi_HSL_mul_uSL
    (u : Kˣ) (b : K) :
    smallReePsi K a (HSL u * uSL b) =
      smallReeH a K (u ^ (3 + 3 * 3 ^ a)) * smallReeU a K 0 b 0 := by
  rw [map_mul, smallReePsi_HSL hK, smallReePsi_uSL]

theorem eq_zero_of_smallReeH_mul_smallReeU_mem
    {s : Kˣ} {b : K}
    (h : smallReeH a K s * smallReeU a K 0 b 0 ∈ G2.reeFixedTorus K a) :
    b = 0 ∧ smallReeU a K 0 b 0 = 1 := by
  have hH : smallReeU a K 0 b 0 ∈ G2.reeFixedTorus K a := by
    have e : smallReeU a K 0 b 0 = (smallReeH a K s)⁻¹ * (smallReeH a K s * smallReeU a K 0 b 0) :=
      by group
    rw [e]
    exact mul_mem (inv_mem (smallReeH_mem hK s)) h
  have h1 := eq_one_of_mem_reeFixedPosUnipotent_of_mem_reeFixedTorus (smallReeU_mem hK 0 b 0) hH
  have h0 : smallReeU a K 0 b 0 = smallReeU a K 0 0 0 := by
    rw [h1]
    exact smallReeCoord_zero.symm
  exact ⟨(smallReeU_inj h0).2.1, h1⟩

variable {w₀ : WeylGroup G2.tag}
  (hw₀ : ∀ w, (coxeterSystem G2.tag).length w ≤ (coxeterSystem G2.tag).length w₀)
include hw₀

theorem smallReePsi_mem
    (g : SL2 K) : smallReePsi K a g ∈ smallReeInvCentralizer a K := by
  refine SL2_induction (p := fun g => smallReePsi K a g ∈ smallReeInvCentralizer a K)
    (fun g g' hg hg' => by rw [map_mul]; exact mul_mem hg hg') (fun b => ?_) (fun r => ?_) ?_ g
  · rw [smallReePsi_uSL]
    exact mem_smallReeInvCentralizer_of_mem_smallReeMidX hK ⟨b, rfl⟩
  · rw [smallReePsi_HSL hK]
    exact smallReeH_mem_smallReeInvCentralizer hK _
  · rw [smallReePsi_WSL hw₀]
    exact canonicalRep_mem_smallReeInvCentralizer hw₀

theorem bigCell_not_mem_reeFixedBorel
    (x z : K) (y : Kˣ) :
    smallReeU a K 0 x 0 * smallReeH a K y * canonicalRep (coxeterSystem G2.tag) K w₀ *
      smallReeU a K 0 z 0 ∉ G2.reeFixedBorel K a := by
  intro hB
  apply canonicalRep_longest_not_mem_reeFixedBorel hK hw₀
  have hx := reeFixedPosUnipotent_le_reeFixedBorel (t := G2) (K := K) (a := a)
    (smallReeU_mem hK 0 x 0)
  have hz := reeFixedPosUnipotent_le_reeFixedBorel (t := G2) (K := K) (a := a)
    (smallReeU_mem hK 0 z 0)
  have hy := reeFixedTorus_le_reeFixedBorel (t := G2) (K := K) (a := a) (smallReeH_mem hK y)
  have e : canonicalRep (coxeterSystem G2.tag) K w₀ =
      (smallReeU a K 0 x 0 * smallReeH a K y)⁻¹ * (smallReeU a K 0 x 0 * smallReeH a K y *
        canonicalRep (coxeterSystem G2.tag) K w₀ * smallReeU a K 0 z 0) *
          (smallReeU a K 0 z 0)⁻¹ := by group
  rw [e]
  exact mul_mem (mul_mem (inv_mem (mul_mem hx hy)) hB) (inv_mem hz)

theorem smallReePsi_not_mem_reeFixedBorel
    {g : SL2 K}
    (hc : (g : Matrix (Fin 2) (Fin 2) K) 1 0 ≠ 0) :
    smallReePsi K a g ∉ G2.reeFixedBorel K a := by
  rw [eq_uSL_mul_HSL_mul_WSL_mul_uSL hc, map_mul, map_mul, map_mul, smallReePsi_uSL,
    smallReePsi_HSL hK, smallReePsi_WSL hw₀, smallReePsi_uSL]
  exact bigCell_not_mem_reeFixedBorel hK hw₀ _ _ _

theorem smallReePsi_eq_one_iff
    (g : SL2 K) : smallReePsi K a g = 1 ↔ g = 1 ∨ g = -1 := by
  constructor
  · intro h
    by_cases hc : (g : Matrix (Fin 2) (Fin 2) K) 1 0 = 0
    · rw [eq_HSL_mul_uSL hc] at h ⊢
      generalize Units.mk0 _ (SL2_apply_zero_zero_ne_zero hc) = u at h ⊢
      generalize (g : Matrix (Fin 2) (Fin 2) K) 0 1 / (g : Matrix (Fin 2) (Fin 2) K) 0 0 = b at h ⊢
      rw [smallReePsi_HSL_mul_uSL hK] at h
      have hmem : smallReeH a K (u ^ (3 + 3 * 3 ^ a)) * smallReeU a K 0 b 0 ∈
          G2.reeFixedTorus K a := by
        rw [h]
        exact one_mem _
      obtain ⟨rfl, h1⟩ := eq_zero_of_smallReeH_mul_smallReeU_mem hK hmem
      rw [h1, mul_one, ← smallReeH_one] at h
      have hu := smallReeH_injective h
      have hu2 : (u : K) ^ 2 = 1 := sq_eq_one_of_pow_eq_one hK u.ne_zero (by
        rw [← Units.val_pow_eq_pow_val, hu, Units.val_one])
      rw [sq] at hu2
      rw [uSL_zero, mul_one]
      rcases mul_self_eq_one_iff.1 hu2 with hu1 | hu1
      · left
        rw [show u = 1 from Units.ext hu1, HSL_one]
      · right
        rw [show u = -1 from Units.ext (by rw [hu1, Units.val_neg, Units.val_one]), HSL_neg_one]
    · exfalso
      exact smallReePsi_not_mem_reeFixedBorel hK hw₀ hc (by rw [h]; exact one_mem _)
  · rintro (rfl | rfl)
    · exact map_one _
    · have hm : Even (3 + 3 * 3 ^ a) := by
        obtain ⟨j, hj⟩ := three_pow_odd a
        exact ⟨3 * j + 3, by omega⟩
      rw [← HSL_neg_one, smallReePsi_HSL hK, hm.neg_one_pow, smallReeH_one]

theorem smallReeH_neg_one_not_mem_range :
    smallReeH a K (-1) ∉ (smallReePsi K a).range := by
  rintro ⟨g, hg⟩
  by_cases hc : (g : Matrix (Fin 2) (Fin 2) K) 1 0 = 0
  · rw [eq_HSL_mul_uSL hc] at hg
    generalize Units.mk0 _ (SL2_apply_zero_zero_ne_zero hc) = u at hg
    generalize (g : Matrix (Fin 2) (Fin 2) K) 0 1 / (g : Matrix (Fin 2) (Fin 2) K) 0 0 = b at hg
    rw [smallReePsi_HSL_mul_uSL hK] at hg
    have hmem : smallReeH a K (u ^ (3 + 3 * 3 ^ a)) * smallReeU a K 0 b 0 ∈
        G2.reeFixedTorus K a := by
      rw [hg]
      exact smallReeH_mem hK (-1)
    obtain ⟨-, h1⟩ := eq_zero_of_smallReeH_mul_smallReeU_mem hK hmem
    rw [h1, mul_one] at hg
    have hu := smallReeH_injective hg
    obtain ⟨j, hj⟩ := three_pow_odd a
    apply not_isSquare_neg_one hK
    refine ⟨(u : K) ^ (3 * j + 3), ?_⟩
    rw [← pow_two, ← pow_mul, show (3 * j + 3) * 2 = 3 + 3 * 3 ^ a by omega,
      ← Units.val_pow_eq_pow_val, hu, Units.val_neg, Units.val_one]
  · exact smallReePsi_not_mem_reeFixedBorel hK hw₀ hc (by
      rw [hg]
      exact reeFixedTorus_le_reeFixedBorel (smallReeH_mem hK (-1)))

theorem card_smallReePsi_ker :
    Nat.card (smallReePsi K a).ker = 2 := by
  have h : ((smallReePsi K a).ker : Set (SL2 K)) = {1, -1} := by
    ext g
    rw [SetLike.mem_coe, MonoidHom.mem_ker, smallReePsi_eq_one_iff hK hw₀, Set.mem_insert_iff,
      Set.mem_singleton_iff]
  rw [← SetLike.coe_sort_coe, h, Nat.card_coe_set_eq, Set.ncard_pair one_ne_neg_one_SL2]

theorem two_mul_card_smallReePsi_range :
    2 * Nat.card (smallReePsi K a).range = 3 ^ (2 * a + 1) * ((3 ^ (2 * a + 1)) ^ 2 - 1) := by
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (smallReePsi K a).ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange (smallReePsi K a)).toEquiv,
    card_smallReePsi_ker hK hw₀, CFSG.GorensteinWalter.sl2_card_formula, hK] at h
  rw [h, mul_comm]

theorem zpowers_sup_range_eq :
    Subgroup.zpowers (smallReeH a K (-1)) ⊔ (smallReePsi K a).range =
      smallReeInvCentralizer a K := by
  set M := Subgroup.zpowers (smallReeH a K (-1)) ⊔ (smallReePsi K a).range
  set L := (smallReePsi K a).range
  have hle : M ≤ smallReeInvCentralizer a K := sup_le
    ((Subgroup.zpowers_le).2 (smallReeH_mem_smallReeInvCentralizer hK (-1)))
    (by rintro _ ⟨g, rfl⟩; exact smallReePsi_mem hK hw₀ g)
  have hq : 1 < (3 ^ (2 * a + 1)) ^ 2 := by
    have := Nat.one_lt_pow (n := 2 * a + 1) (by omega) (by norm_num : 1 < 3)
    nlinarith
  have hCpos : 0 < Nat.card (smallReeInvCentralizer a K) := by
    rw [card_smallReeInvCentralizer hw₀ hK]
    exact Nat.mul_pos (by positivity) (by omega)
  have hCfin : Finite (smallReeInvCentralizer a K) := Nat.finite_of_card_ne_zero hCpos.ne'
  have hMfin : Finite M := Finite.of_injective _ (Subgroup.inclusion_injective hle)
  have hLM : L ≤ M := le_sup_right
  have htM : smallReeH a K (-1) ∈ M := Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
  have hne : Nat.card M ≠ Nat.card L := fun h => smallReeH_neg_one_not_mem_range hK hw₀ (by
    rw [show (smallReePsi K a).range = M from Subgroup.eq_of_le_of_card_ge hLM h.le]
    exact htM)
  obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le hLM
  have hMpos : 0 < Nat.card M := Nat.card_pos
  have hk2 : 2 ≤ k := by
    by_contra hlt
    interval_cases k
    · rw [mul_zero] at hk
      omega
    · rw [mul_one] at hk
      exact hne hk
  have hcard : Nat.card (smallReeInvCentralizer a K) ≤ Nat.card M := by
    rw [card_smallReeInvCentralizer hw₀ hK, ← two_mul_card_smallReePsi_range hK hw₀, hk,
      mul_comm (Nat.card L) k]
    exact Nat.mul_le_mul_right _ hk2
  exact Subgroup.eq_of_le_of_card_ge hle hcard

theorem disjoint_zpowers_range :
    Disjoint (Subgroup.zpowers (smallReeH a K (-1))) (smallReePsi K a).range := by
  rw [Subgroup.disjoint_def]
  intro x hx hxL
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
  have ht2 : smallReeH a K (-1) ^ (2 : ℤ) = 1 := by
    rw [zpow_two]
    exact smallReeH_neg_one_mul_self
  rw [zpow_eq_zpow_emod k ht2] at hxL ⊢
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · rw [h, zpow_zero]
  · rw [h, zpow_one] at hxL
    exact absurd hxL (smallReeH_neg_one_not_mem_range hK hw₀)

theorem zpowers_le_centralizer_range :
    Subgroup.zpowers (smallReeH a K (-1)) ≤
      Subgroup.centralizer ((smallReePsi K a).range : Set (ModGL G2.tag K)) := by
  rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
  rintro _ ⟨g, rfl⟩
  exact Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 (smallReePsi_mem hK hw₀ g)).2

theorem smallReePsi_ker :
    (smallReePsi K a).ker = Subgroup.center (SL2 K) := by
  ext g
  rw [MonoidHom.mem_ker, smallReePsi_eq_one_iff hK hw₀, Matrix.SpecialLinearGroup.mem_center_iff,
    Fintype.card_fin]
  constructor
  · rintro (rfl | rfl)
    · exact ⟨1, one_pow 2, by simp⟩
    · refine ⟨-1, by norm_num, ?_⟩
      rw [Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one, map_neg, map_one]
  · rintro ⟨r, hr, hg⟩
    rw [sq] at hr
    rcases mul_self_eq_one_iff.1 hr with rfl | rfl
    · left
      exact Subtype.ext (by rw [← hg, map_one, Matrix.SpecialLinearGroup.coe_one])
    · right
      exact Subtype.ext (by rw [← hg, map_neg, map_one, Matrix.SpecialLinearGroup.coe_neg,
        Matrix.SpecialLinearGroup.coe_one])

end Structure

theorem small_Ree_involution_centralizer_PSL2_structure
    (a : ℕ) (K : Type) [Field K] [Finite K]
    [CharP K ReeTag.G2.prime] (hK : Nat.card K = 3 ^ (2 * a + 1))
    (w₀ : WeylGroup ReeTag.G2.tag)
    (hw₀ : ∀ w, (coxeterSystem ReeTag.G2.tag).length w ≤
      (coxeterSystem ReeTag.G2.tag).length w₀) :
    ∃ ψ : SL2 K →* ModGL ReeTag.G2.tag K,
      (∀ g, ψ g ∈ smallReeInvCentralizer a K) ∧
      (∀ b : K, ψ (uSL b) = smallReeU a K 0 b 0) ∧
      ψ WSL = canonicalRep (coxeterSystem ReeTag.G2.tag) K w₀ ∧
      (∀ r : Kˣ, ψ (HSL r) = smallReeH a K (r ^ (3 + 3 * 3 ^ a))) ∧
      (∀ g, ψ g = 1 ↔ g = 1 ∨ g = -1) ∧
      ψ.ker = Subgroup.center (SL2 K) ∧
      CFSG.Walter.JT.IsInternalDirectProduct (Subgroup.zpowers (smallReeH a K (-1))) ψ.range
        (smallReeInvCentralizer a K) ∧
      ∃ e : PSL(2, K) ≃* ψ.range,
        ∀ g, (e (QuotientGroup.mk g) : ModGL ReeTag.G2.tag K) = ψ g :=
  ⟨smallReePsi K a, smallReePsi_mem hK hw₀, smallReePsi_uSL, smallReePsi_WSL hw₀,
    smallReePsi_HSL hK, smallReePsi_eq_one_iff hK hw₀, smallReePsi_ker hK hw₀,
    ⟨zpowers_sup_range_eq hK hw₀, disjoint_zpowers_range hK hw₀,
      zpowers_le_centralizer_range hK hw₀⟩,
    (QuotientGroup.quotientMulEquivOfEq (smallReePsi_ker hK hw₀)).symm.trans
      (QuotientGroup.quotientKerEquivRange _), fun _ => rfl⟩

end CFSG.Walter.Ree.Model
