module

public import CFSG.RankThree.PartTwo.Census.Exceptional.Minuscule
public import CFSG.LocalAnalysis.ComponentInitial.CentralSL2Semilinear
public import CFSG.LieType.Steinberg.TwistedE6.Local
public import CFSG.RankThree.PartTwo.Census.Exceptional.Basic

public section

namespace CFSG.RankThree.PartTwo.Census.Exceptional

open CFSG.Assembly.RankThreeEven (localRank)
open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.TwistedE6
  CFSG.RankThree.CentralCover
open scoped MatrixGroups

section Independence


theorem commute_of_commute_zpow {G : Type*} [Group G] {g y : G} (hg : g ^ 3 = 1) {a : ℤ}
    (ha : ¬ (3 : ℤ) ∣ a) (h : Commute y (g ^ a)) : Commute y g := by
  have h3 : (3 : ℤ) ∣ a * a - 1 := by
    have : (3 : ℤ) ∣ a - 1 ∨ (3 : ℤ) ∣ a + 1 := by omega
    rcases this with h1 | h1
    · exact (h1.mul_right (a + 1)).trans (by rw [show (a - 1) * (a + 1) = a * a - 1 by ring])
    · exact (h1.mul_left (a - 1)).trans (by rw [show (a - 1) * (a + 1) = a * a - 1 by ring])
  obtain ⟨m, hm⟩ := h3
  have hg' : g ^ (3 : ℤ) = 1 := by rw [zpow_ofNat]; exact hg
  have e : (g ^ a) ^ a = g := by
    rw [← zpow_mul, show a * a = 1 + 3 * m by omega, zpow_add, zpow_one, zpow_mul, hg',
      one_zpow, mul_one]
  rw [← e]
  exact h.zpow_right a

theorem zpow_eq_one_of_three_dvd {G : Type*} [Group G] {g : G} (hg : g ^ 3 = 1) {a : ℤ}
    (ha : (3 : ℤ) ∣ a) : g ^ a = 1 := by
  obtain ⟨m, rfl⟩ := ha
  rw [zpow_mul, zpow_ofNat, hg, one_zpow]

theorem eq_one_of_mem_closure {G : Type*} [Group G] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : ι → G) (e₀ : G)
    (y : ι → G) (hee : ∀ i j, Commute (e i) (e j)) (he3 : ∀ i, e i ^ 3 = 1)
    (hy : ∀ i j, i ≠ j → Commute (y i) (e j)) (hy₀ : ∀ i, Commute (y i) e₀)
    (hyi : ∀ i, ¬ Commute (y i) (e i)) (h : e₀ ∈ Subgroup.closure (Set.range e)) : e₀ = 1 := by
  set H := Subgroup.closure (Set.range e)
  have hpair : (Set.range e).Pairwise Commute := by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ -
    exact hee i j
  have hHc : IsMulCommutative H := Subgroup.isMulCommutative_closure hpair
  have hcomm : ∀ a b : H, a * b = b * a := fun a b => mul_comm' a b
  let : CommGroup H := { (inferInstance : Group H) with mul_comm := hcomm }
  let e' : ι → H := fun i => ⟨e i, Subgroup.subset_closure ⟨i, rfl⟩⟩
  have hgen : Subgroup.closure (Set.range e') = ⊤ := by
    rw [eq_top_iff, ← Subgroup.closure_closure_coe_preimage (k := Set.range e)]
    refine Subgroup.closure_mono ?_
    rintro x ⟨i, hi⟩
    exact ⟨i, Subtype.ext hi⟩
  obtain ⟨a, ha⟩ := Subgroup.exists_of_mem_closure_range e' ⟨e₀, h⟩
    (hgen ▸ Subgroup.mem_top _)
  have hfac : ∀ i, e' i ^ a i = 1 := by
    intro i
    set C : Subgroup H := (Subgroup.centralizer ({y i} : Set G)).subgroupOf H
    have hC : ∀ j, j ≠ i → e' j ^ a j ∈ C := fun j hj => by
      refine C.zpow_mem ?_ _
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff]
      exact ((hy i j (Ne.symm hj)).eq).symm
    have hC0 : (⟨e₀, h⟩ : H) ∈ C := by
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff]
      exact (hy₀ i).eq.symm
    have hprod : (∏ j ∈ Finset.univ.erase i, e' j ^ a j) ∈ C :=
      Subgroup.prod_mem C fun j hj => hC j (Finset.ne_of_mem_erase hj)
    have hsplit := Finset.mul_prod_erase Finset.univ (fun j => e' j ^ a j) (Finset.mem_univ i)
    have hi : e' i ^ a i ∈ C := by
      have e1 : e' i ^ a i = (⟨e₀, h⟩ : H) * (∏ j ∈ Finset.univ.erase i, e' j ^ a j)⁻¹ := by
        rw [ha, ← hsplit, mul_inv_cancel_right]
      rw [e1]
      exact C.mul_mem hC0 (C.inv_mem hprod)
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff] at hi
    by_cases h3 : (3 : ℤ) ∣ a i
    · exact Subtype.ext (by
        rw [Subgroup.coe_zpow, Subgroup.coe_one]
        exact zpow_eq_one_of_three_dvd (he3 i) h3)
    · exfalso
      refine hyi i (commute_of_commute_zpow (he3 i) h3 ?_)
      have : (((e' i ^ a i : H)) : G) = e i ^ a i := Subgroup.coe_zpow _ _ _
      rw [← this]
      exact hi.symm
  have : (⟨e₀, h⟩ : H) = 1 := by
    rw [ha]
    exact Finset.prod_eq_one fun i _ => hfac i
  exact congrArg Subtype.val this




variable {G : Type} [Group G] [Finite G]

theorem card_add_one_le_localRank_three {ι : Type*} [Fintype ι] [DecidableEq ι] (e : ι → G)
    (e₀ : G) (y : ι → G) (hee : ∀ i j, Commute (e i) (e j)) (he₀ : ∀ i, Commute (e i) e₀)
    (he3 : ∀ i, e i ^ 3 = 1) (he₀3 : e₀ ^ 3 = 1) (he₀1 : e₀ ≠ 1)
    (hy : ∀ i j, i ≠ j → Commute (y i) (e j)) (hy₀ : ∀ i, Commute (y i) e₀)
    (hyi : ∀ i, ¬ Commute (y i) (e i)) {u : G} (hu : orderOf u = 2)
    (heu : ∀ i, Commute (e i) u) (he₀u : Commute e₀ u) :
    Fintype.card ι + 1 ≤ localRank 3 G := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let f : Option ι → G := fun o => o.elim e₀ e
  have hff : ∀ a b, Commute (f a) (f b) := by
    rintro (_ | a) (_ | b)
    · exact Commute.refl _
    · exact (he₀ b).symm
    · exact he₀ a
    · exact hee a b
  have hf3 : ∀ a, f a ^ 3 = 1 := by
    rintro (_ | a)
    · exact he₀3
    · exact he3 a
  have hfu : ∀ a, Commute (f a) u := by
    rintro (_ | a)
    · exact he₀u
    · exact heu a
  have hpair : (Set.range f).Pairwise Commute := by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ -
    exact hff i j
  set Y := Subgroup.closure (Set.range f)
  have hYc : IsMulCommutative Y := Subgroup.isMulCommutative_closure hpair
  have hcomm : ∀ a b : Y, a * b = b * a := fun a b => mul_comm' a b
  let : CommGroup Y := { (inferInstance : Group Y) with mul_comm := hcomm }
  let f' : Option ι → Y := fun i => ⟨f i, Subgroup.subset_closure ⟨i, rfl⟩⟩
  have hgen : Subgroup.closure (Set.range f') = ⊤ := by
    rw [eq_top_iff, ← Subgroup.closure_closure_coe_preimage (k := Set.range f)]
    refine Subgroup.closure_mono ?_
    rintro x ⟨i, hi⟩
    exact ⟨i, Subtype.ext hi⟩
  let S : Option ι → Subgroup Y := fun o => o.elim
    ((Subgroup.closure (Set.range e)).subgroupOf Y)
    (fun i => (Subgroup.centralizer ({y i} : Set G)).subgroupOf Y)
  have hS : ∀ i j, i ≠ j → f' j ∈ S i := by
    rintro (_ | i) (_ | j) hij
    · exact absurd rfl hij
    · exact Subgroup.mem_subgroupOf.2 (Subgroup.subset_closure ⟨j, rfl⟩)
    · exact Subgroup.mem_subgroupOf.2
        (Subgroup.mem_centralizer_singleton_iff.2 (hy₀ i).eq.symm)
    · exact Subgroup.mem_subgroupOf.2 (Subgroup.mem_centralizer_singleton_iff.2
        (hy i j fun h => hij (h ▸ rfl)).eq.symm)
  have hSy : ∀ i, f' i ∉ S i := by
    rintro (_ | i) h
    · exact he₀1 (eq_one_of_mem_closure e e₀ y hee he3 hy hy₀ hyi (Subgroup.mem_subgroupOf.1 h))
    · exact hyi i (Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_subgroupOf.1 h)).symm
  have hSy3 : ∀ i, f' i ^ 3 ∈ S i := fun i => by
    have : f' i ^ 3 = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact hf3 i)
    rw [this]
    exact (S i).one_mem
  have hbound := CFSG.RankThree.Theta.three_pow_card_le_card_ker_pow f' hgen S hS hSy hSy3
  set Ω : Subgroup G := (powMonoidHom 3 : Y →* Y).ker.map Y.subtype with hΩ
  have hΩcard : Nat.card Ω = Nat.card (powMonoidHom 3 : Y →* Y).ker :=
    Subgroup.card_map_of_injective Y.subtype_injective
  have hΩY : Ω ≤ Y := Subgroup.map_subtype_le _
  have hΩc : IsMulCommutative Ω := ⟨⟨fun a b => Subtype.ext
    (show (a : G) * b = b * a from congrArg Subtype.val (hcomm ⟨a, hΩY a.2⟩ ⟨b, hΩY b.2⟩))⟩⟩
  have hΩq : ∀ w ∈ Ω, w ^ 3 = 1 := by
    rintro _ ⟨m, hm, rfl⟩
    exact congrArg Subtype.val (MonoidHom.mem_ker.1 hm)
  have hΩp : IsPGroup 3 Ω := fun w => ⟨1, Subtype.ext (by
    rw [pow_one, Subgroup.coe_pow, hΩq _ w.2, Subgroup.coe_one])⟩
  obtain ⟨r, hr⟩ := hΩp.exists_card_eq
  have hYu : ∀ x ∈ Y, x * u = u * x := by
    intro x hx
    have hle : Y ≤ Subgroup.centralizer ({u} : Set G) := (Subgroup.closure_le _).2 (by
      rintro _ ⟨i, rfl⟩
      exact Subgroup.mem_centralizer_singleton_iff.2 (hfu i).eq)
    exact Subgroup.mem_centralizer_singleton_iff.1 (hle hx)
  have hr' := le_localRank_of_commute_involution Nat.prime_three hu ⟨hΩc, hΩq⟩ hr
    (fun x hx => hYu x (hΩY hx))
  have h3r : 3 ^ (Fintype.card ι + 1) ≤ 3 ^ r := by
    rw [← hr, hΩcard, ← Fintype.card_option]
    exact hbound
  have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).1 h3r
  omega




end Independence

section Generic

variable {τ : Tag} {D : MinData τ} (hV : D.Valid) (k : Type*) [Field k]

theorem simpleSL2_lower (i : Fin τ.rank) (c : k) :
    simpleSL2 hV k i (MinData.Valid.slLower k c) = hV.xm k (-Pi.single i 1) c :=
  hV.endo_injective k (by
    rw [endo_simpleSL2, hV.endo_xm, MinData.Valid.slLower_val, hV.blockOp_lower])

theorem closure_sl2Upper_slLower :
    Subgroup.closure (Set.range (sl2Upper (K := k)) ∪ Set.range (MinData.Valid.slLower k)) = ⊤ :=
  CFSG.LocalAnalysis.ComponentInitial.sl2_closure_upper_lower (K := k)

variable {k} {F : Type*} [Field F] (j : k →+* F)

theorem map_sl2Upper (c : k) :
    Matrix.SpecialLinearGroup.map j (sl2Upper c) = sl2Upper (j c) := by
  ext a b
  rw [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply]
  fin_cases a <;> fin_cases b <;> simp [sl2Upper]

theorem map_slLower (c : k) :
    Matrix.SpecialLinearGroup.map j (MinData.Valid.slLower k c) =
      MinData.Valid.slLower F (j c) := by
  ext a b
  rw [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply]
  fin_cases a <;> fin_cases b <;> simp [MinData.Valid.slLower]

theorem map_sl2Diag (t : kˣ) :
    Matrix.SpecialLinearGroup.map j (sl2Diag t) = sl2Diag (Units.map (j : k →* F) t) := by
  ext a b
  rw [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply]
  fin_cases a <;> fin_cases b <;> simp [sl2Diag]

theorem map_injective_sl {f : k →+* F} :
    Function.Injective (Matrix.SpecialLinearGroup.map (n := Fin 2) f) := by
  intro A B h
  ext a b
  have := congrArg (fun M : SL(2, F) => (M : Matrix (Fin 2) (Fin 2) F) a b) h
  simp only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
    Matrix.map_apply] at this
  exact f.injective this

theorem map_conj_nm_rankOne (i : Fin τ.rank) {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) :
    (hV.rootGroup k γ ⊔ hV.rootGroup k (-γ)).map (MulAut.conj (hV.nm k i)).toMonoidHom ≤
      hV.rootGroup k (reflect τ i γ) ⊔ hV.rootGroup k (-reflect τ i γ) := by
  obtain ⟨σ, -, h⟩ := hV.nm_conj_xm k hγ i
  obtain ⟨σ', -, h'⟩ := hV.nm_conj_xm k (CFSG.LieType.Chevalley.IsRoot.neg hγ) i
  rw [Subgroup.map_sup]
  refine sup_le_sup (map_conj_rootGroup_le hV k h) (map_conj_rootGroup_le hV k (σ := σ')
    fun c => ?_)
  rw [h', CFSG.LieType.Steinberg.Adjoint.reflect_neg]

theorem map_conj_mul {G : Type*} [Group G] (a b : G) (R : Subgroup G) :
    R.map (MulAut.conj (a * b)).toMonoidHom =
      (R.map (MulAut.conj b).toMonoidHom).map (MulAut.conj a).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [mul_assoc]

theorem map_conj_list_rankOne (l : List (Fin τ.rank)) {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) :
    IsRoot τ (l.foldr (reflect τ) γ) ∧
      (hV.rootGroup k γ ⊔ hV.rootGroup k (-γ)).map
          (MulAut.conj (l.map (hV.nm k)).prod).toMonoidHom ≤
        hV.rootGroup k (l.foldr (reflect τ) γ) ⊔ hV.rootGroup k (-l.foldr (reflect τ) γ) := by
  induction l with
  | nil =>
    refine ⟨hγ, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    simpa using hx
  | cons i l ih =>
    obtain ⟨h1, h2⟩ := ih
    refine ⟨IsRoot.reflect i h1, ?_⟩
    rw [List.map_cons, List.prod_cons, map_conj_mul, List.foldr_cons]
    exact (Subgroup.map_mono h2).trans (map_conj_nm_rankOne hV i h1)

end Generic

section Twisted

variable {k : Type*} [Field k] (θ : k →+* k)

theorem sigma_simpleSL2 {a : Fin (Tag.rank .E6)} (ha : rhoPerm a = a) (A : SL(2, k)) :
    sigma k θ (simpleSL2 e6Data_valid k a A) =
      simpleSL2 e6Data_valid k a (Matrix.SpecialLinearGroup.map θ A) := by
  have h : (sigma k θ).comp (simpleSL2 e6Data_valid k a) =
      (simpleSL2 e6Data_valid k a).comp (Matrix.SpecialLinearGroup.map θ) := by
    refine MonoidHom.eq_of_eqOn_dense (closure_sl2Upper_slLower k) ?_
    rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
    · simp only [MonoidHom.comp_apply]
      rw [simpleSL2_upper, sigma_xm_single, ha, map_sl2Upper, simpleSL2_upper]
    · simp only [MonoidHom.comp_apply]
      rw [simpleSL2_lower, sigma_xm_neg_single, ha, map_slLower, simpleSL2_lower]
  exact DFunLike.congr_fun h A

variable {F : Type*} [Field F] (j : F →+* k) (hj : ∀ x, θ (j x) = j x)

@[expose] noncomputable def fixSL2 {a : Fin (Tag.rank .E6)} (ha : rhoPerm a = a) :
    SL(2, F) →* fixedGroup k θ :=
  ((simpleSL2 e6Data_valid k a).comp (Matrix.SpecialLinearGroup.map j)).codRestrict _ fun A => by
    rw [MonoidHom.comp_apply, mem_fixedGroup, sigma_simpleSL2 θ ha]
    congr 1
    ext p q
    rw [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply,
      Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply, hj]

theorem fixSL2_val {a : Fin (Tag.rank .E6)} (ha : rhoPerm a = a) (A : SL(2, F)) :
    (fixSL2 θ j hj ha A : e6Data_valid.minGroup k) =
      simpleSL2 e6Data_valid k a (Matrix.SpecialLinearGroup.map j A) := rfl

theorem fixSL2_injective {a : Fin (Tag.rank .E6)} (ha : rhoPerm a = a) :
    Function.Injective (fixSL2 θ j hj ha) := fun _ _ h =>
  map_injective_sl ((simpleSL2_injective e6Data_valid k a) (congrArg Subtype.val h))

theorem rhoPerm_three : rhoPerm (nd 3) = nd 3 := rfl

@[expose] def te6Roots : Fin 4 → Fin (Tag.rank .E6) → ℤ :=
  ![![0, 0, 0, 1, 0, 0], ![0, 0, 1, 1, 1, 0], ![1, 0, 1, 1, 1, 1], ![1, 2, 2, 3, 2, 1]]

@[expose] def te6Words : Fin 4 → List (Fin (Tag.rank .E6)) :=
  ![[], [nd 2, nd 4], [nd 0, nd 5, nd 2, nd 4],
    [nd 1, nd 3, nd 2, nd 4, nd 3, nd 1, nd 0, nd 5, nd 2, nd 4]]

open CFSG.LieType.Chevalley.RootOps in
theorem te6_check :
    (∀ i, (te6Words i).foldr (reflect .E6) (Pi.single (nd 3) 1) = te6Roots i) ∧
    (∀ i, rho (te6Roots i) = te6Roots i) ∧
    (∀ i, isRootB .E6 (te6Roots i) = true) ∧
    (∀ i j, i ≠ j → te6Roots i + te6Roots j ≠ 0 ∧ te6Roots i - te6Roots j ≠ 0 ∧
      isRootB .E6 (te6Roots i + te6Roots j) = false ∧
      isRootB .E6 (te6Roots i - te6Roots j) = false) ∧
    (∀ i, MinData.toWeight (te6Roots i) (nd 0) = MinData.toWeight (te6Roots i) (nd 5) ∧
      MinData.toWeight (-te6Roots i) (nd 0) = MinData.toWeight (-te6Roots i) (nd 5)) := by
  decide +kernel

@[expose] noncomputable def te6N : Fin 4 → fixedGroup k θ :=
  ![1, nHat θ (nf 2), nHat θ (nf 3) * nHat θ (nf 2),
    nHat θ (nf 0) * nHat θ (nf 1) * nHat θ (nf 2) * nHat θ (nf 1) * nHat θ (nf 0) *
      nHat θ (nf 3) * nHat θ (nf 2)]

omit θ in
theorem nHatE_nf (k : Type*) [Field k] :
    nHatE k (nf 0) = e6Data_valid.nm k (nd 1) ∧ nHatE k (nf 1) = e6Data_valid.nm k (nd 3) ∧
      nHatE k (nf 2) = e6Data_valid.nm k (nd 2) * e6Data_valid.nm k (nd 4) ∧
      nHatE k (nf 3) = e6Data_valid.nm k (nd 0) * e6Data_valid.nm k (nd 5) :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem te6N_val (i : Fin 4) :
    (te6N θ i : e6Data_valid.minGroup k) = ((te6Words i).map (e6Data_valid.nm k)).prod := by
  obtain ⟨h0, h1, h2, h3⟩ := nHatE_nf k
  fin_cases i <;>
    simp [te6N, te6Words, nHat_val, h0, h1, h2, h3, mul_assoc]

@[expose] noncomputable def te6SL2 (i : Fin 4) : SL(2, F) →* fixedGroup k θ :=
  (MulAut.conj (te6N θ i)).toMonoidHom.comp (fixSL2 θ j hj rhoPerm_three)

theorem te6SL2_injective (i : Fin 4) : Function.Injective (te6SL2 θ j hj i) :=
  (MulAut.conj (te6N θ i)).injective.comp (fixSL2_injective θ j hj rhoPerm_three)

theorem te6SL2_mem (i : Fin 4) (A : SL(2, F)) :
    (te6SL2 θ j hj i A : e6Data_valid.minGroup k) ∈
      e6Data_valid.rootGroup k (te6Roots i) ⊔ e6Data_valid.rootGroup k (-te6Roots i) := by
  obtain ⟨-, h⟩ := map_conj_list_rankOne e6Data_valid (k := k) (te6Words i)
    (isRoot_single .E6 (nd 3))
  rw [te6_check.1 i] at h
  refine h ⟨_, simpleSL2_mem e6Data_valid k (nd 3) (Matrix.SpecialLinearGroup.map j A), ?_⟩
  change _ = (te6N θ i : e6Data_valid.minGroup k) * _ * (te6N θ i : e6Data_valid.minGroup k)⁻¹
  rw [te6N_val]
  rfl


open CFSG.LieType.Chevalley.RootOps in
theorem isRoot_te6Roots (i : Fin 4) : IsRoot .E6 (te6Roots i) :=
  isRootB_iff.1 (te6_check.2.2.1 i)

open CFSG.LieType.Chevalley.RootOps in
theorem te6SL2_commute {i i' : Fin 4} (hii : i ≠ i') (A B : SL(2, F)) :
    te6SL2 θ j hj i A * te6SL2 θ j hj i' B = te6SL2 θ j hj i' B * te6SL2 θ j hj i A := by
  obtain ⟨h1, h2, h3, h4⟩ := te6_check.2.2.2.1 i i' hii
  have hnot : ∀ {v : Fin (Tag.rank .E6) → ℤ}, isRootB .E6 v = false → ¬ IsRoot .E6 v :=
    fun hv hr => by
      rw [← isRootB_iff, hv] at hr
      exact Bool.false_ne_true hr
  refine Subtype.ext ?_
  exact (Subgroup.mem_centralizer_iff.1 (rankOne_le_centralizer e6Data_valid k
    (isRoot_te6Roots i) (isRoot_te6Roots i') h1 h2 (hnot h3) (hnot h4)
    (te6SL2_mem θ j hj i A)) _ (te6SL2_mem θ j hj i' B)).symm

theorem te6SL2_central (i : Fin 4) {A : SL(2, F)}
    (hA : te6SL2 θ j hj i A ∈ Subgroup.center (fixedGroup k θ)) : A = 1 := by
  set φ := fixSL2 θ j hj rhoPerm_three with hφ
  have hx : φ A ∈ Subgroup.center (fixedGroup k θ) := by
    rw [Subgroup.mem_center_iff] at hA ⊢
    intro g
    have h := hA (te6N θ i * g * (te6N θ i)⁻¹)
    change _ * (te6N θ i * φ A * (te6N θ i)⁻¹) = (te6N θ i * φ A * (te6N θ i)⁻¹) * _ at h
    have e : te6N θ i * (g * φ A) * (te6N θ i)⁻¹ = te6N θ i * (φ A * g) * (te6N θ i)⁻¹ := by
      calc _ = te6N θ i * g * (te6N θ i)⁻¹ * (te6N θ i * φ A * (te6N θ i)⁻¹) := by group
        _ = _ := h
        _ = _ := by group
    exact mul_left_cancel (mul_right_cancel e)
  have hAc : A ∈ Subgroup.center (SL(2, F)) := by
    rw [Subgroup.mem_center_iff]
    intro B
    apply fixSL2_injective θ j hj rhoPerm_three
    rw [map_mul, map_mul]
    exact Subgroup.mem_center_iff.1 hx (φ B)
  rcases eq_one_or_eq_neg_one_of_mem_center F hAc with h | ⟨h2, rfl⟩
  · exact h
  · exfalso
    have hval : (φ (sl2Diag (-1)) : e6Data_valid.minGroup k) = e6Data_valid.hm k (nd 3) (-1) := by
      rw [hφ, fixSL2_val, map_sl2Diag, simpleSL2_diag]
      congr 1
      ext
      simp
    have hfix : rho (Pi.single (nd 1) 1 : Fin (Tag.rank .E6) → ℤ) = Pi.single (nd 1) 1 := by
      rw [rho_single]
      rfl
    have hc := congrArg Subtype.val (Subgroup.mem_center_iff.1 hx
      (xFixed θ (isRoot_single .E6 (nd 1)) hfix 1 (map_one θ)))
    simp only [Subgroup.coe_mul, xFixed_val, hval] at hc
    have h := e6Data_valid.hm_conj_xm k (isRoot_single .E6 (nd 1)) (nd 3) (-1) 1
    rw [← hc, mul_inv_cancel_right, MinData.toWeight_single,
      show Tag.cartan .E6 (nd 3) (nd 1) = -1 by decide] at h
    have h1 := e6Data_valid.xm_injective k (isRoot_single .E6 (nd 1)) h
    simp only [zpow_neg, zpow_one, inv_neg, inv_one, Units.val_neg, Units.val_one,
      mul_one] at h1
    apply h2
    refine neg_one_eq_one_iff.1 (j.injective ?_)
    rw [map_neg, map_one]
    exact h1.symm

variable (hθ : ∀ c, θ (θ c) = c)

@[expose] noncomputable def te6Torus (t : kˣ) : fixedGroup k θ :=
  ⟨hPairE θ (nd 0) (nd 5) t, hHatE_le_fixedGroup θ hθ (nf 3) (by
    change _ ∈ (hPairE θ (nd 0) (nd 5)).range
    exact ⟨t, rfl⟩)⟩

theorem te6Torus_val (t : kˣ) :
    (te6Torus θ hθ t : e6Data_valid.minGroup k) = hPairE θ (nd 0) (nd 5) t := rfl

theorem hPairE_conj_xm (t : kˣ) {γ : Fin (Tag.rank .E6) → ℤ} (hγ : IsRoot .E6 γ) (c : k) :
    hPairE θ (nd 0) (nd 5) t * e6Data_valid.xm k γ c * (hPairE θ (nd 0) (nd 5) t)⁻¹ =
      e6Data_valid.xm k γ (((t ^ MinData.toWeight γ (nd 0) *
        Units.map (θ : k →* k) t ^ MinData.toWeight γ (nd 5) : kˣ) : k) * c) := by
  have e : ∀ a b x : e6Data_valid.minGroup k, a * b * x * (a * b)⁻¹ = a * (b * x * b⁻¹) * a⁻¹ :=
    fun a b x => by group
  change e6Data_valid.hm k (nd 0) t * e6Data_valid.hm k (nd 5) (Units.map (θ : k →* k) t) *
      e6Data_valid.xm k γ c * (e6Data_valid.hm k (nd 0) t *
        e6Data_valid.hm k (nd 5) (Units.map (θ : k →* k) t))⁻¹ = _
  rw [e, e6Data_valid.hm_conj_xm k hγ, e6Data_valid.hm_conj_xm k hγ, ← mul_assoc,
    ← Units.val_mul]

theorem hPairE_conj_xm_of_eq {t : kˣ} (ht : t * Units.map (θ : k →* k) t = 1)
    {γ : Fin (Tag.rank .E6) → ℤ} (hγ : IsRoot .E6 γ)
    (hw : MinData.toWeight γ (nd 0) = MinData.toWeight γ (nd 5)) (c : k) :
    hPairE θ (nd 0) (nd 5) t * e6Data_valid.xm k γ c * (hPairE θ (nd 0) (nd 5) t)⁻¹ =
      e6Data_valid.xm k γ c := by
  rw [hPairE_conj_xm θ t hγ, ← hw, ← mul_zpow, ht, one_zpow, Units.val_one, one_mul]

theorem te6Torus_commute {t : kˣ} (ht : t * Units.map (θ : k →* k) t = 1) (i : Fin 4)
    (A : SL(2, F)) : te6Torus θ hθ t * te6SL2 θ j hj i A = te6SL2 θ j hj i A * te6Torus θ hθ t := by
  have hle : ∀ {γ : Fin (Tag.rank .E6) → ℤ}, IsRoot .E6 γ →
      MinData.toWeight γ (nd 0) = MinData.toWeight γ (nd 5) →
      e6Data_valid.rootGroup k γ ≤
        Subgroup.centralizer ({hPairE θ (nd 0) (nd 5) t} : Set (e6Data_valid.minGroup k)) := by
    intro γ hγ hw x hx
    obtain ⟨c, rfl⟩ := (e6Data_valid.mem_rootGroup k).1 hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h := hPairE_conj_xm_of_eq θ ht hγ hw c
    rw [mul_inv_eq_iff_eq_mul] at h
    exact h.symm
  have hmem := (sup_le (hle (isRoot_te6Roots i) (te6_check.2.2.2.2 i).1)
    (hle (CFSG.LieType.Chevalley.IsRoot.neg (isRoot_te6Roots i))
      (te6_check.2.2.2.2 i).2)) (te6SL2_mem θ j hj i A)
  rw [Subgroup.mem_centralizer_singleton_iff] at hmem
  exact Subtype.ext hmem.symm

theorem te6Torus_not_mem_center {t : kˣ} (ht : ((t : k)) ^ 2 ≠ 1) :
    te6Torus θ hθ t ∉ Subgroup.center (fixedGroup k θ) := by
  intro hc
  have hne : rho (Pi.single (nd 0) 1 : Fin (Tag.rank .E6) → ℤ) ≠ Pi.single (nd 0) 1 := by
    rw [rho_single]
    decide
  have h := congrArg Subtype.val (Subgroup.mem_center_iff.1 hc
    (xPair θ hθ (isRoot_single .E6 (nd 0)) hne 1))
  simp only [Subgroup.coe_mul, xPair_val, te6Torus_val] at h
  set c' : k := (twistSign (Pi.single (nd 0) 1) : k) * θ 1
  have e : hPairE θ (nd 0) (nd 5) t *
      (e6Data_valid.xm k (Pi.single (nd 0) 1) 1 *
        e6Data_valid.xm k (rho (Pi.single (nd 0) 1)) c') * (hPairE θ (nd 0) (nd 5) t)⁻¹ =
      e6Data_valid.xm k (Pi.single (nd 0) 1) 1 *
        e6Data_valid.xm k (rho (Pi.single (nd 0) 1)) c' := by
    rw [← h, mul_inv_cancel_right]
  have e2 : ∀ a b x : e6Data_valid.minGroup k, a * (x * b) * a⁻¹ = (a * x * a⁻¹) * (a * b * a⁻¹) :=
    fun a b x => by group
  rw [e2, hPairE_conj_xm θ t (isRoot_single .E6 (nd 0)),
    hPairE_conj_xm θ t (isRoot_rho (isRoot_single .E6 (nd 0)))] at e
  have h1 := (xm_mul_xm_rho_inj (isRoot_single .E6 (nd 0)) hne e).1
  rw [MinData.toWeight_single, MinData.toWeight_single,
    show Tag.cartan .E6 (nd 0) (nd 0) = 2 by decide,
    show Tag.cartan .E6 (nd 5) (nd 0) = 0 by decide, zpow_zero, mul_one, mul_one] at h1
  exact ht (by simpa using h1)

theorem te6Torus_pow (t : kˣ) (n : ℕ) : te6Torus θ hθ t ^ n = te6Torus θ hθ (t ^ n) :=
  Subtype.ext (by rw [SubgroupClass.coe_pow, te6Torus_val, te6Torus_val, map_pow])

theorem te6Torus_one : te6Torus θ hθ 1 = 1 :=
  Subtype.ext (by rw [te6Torus_val, map_one]; rfl)

include hθ in
theorem four_le_localRank_three_te6 {G : Type} [Group G] [Finite G]
    (Θ : fixedGroup k θ →* G) (hΘ : ∀ g, Θ g = 1 → g ∈ Subgroup.center (fixedGroup k θ))
    (hinj : ∀ i, Function.Injective (Θ.comp (te6SL2 θ j hj i))) (hF : ringChar F = 2)
    {t : kˣ} (htt : t * Units.map (θ : k →* k) t = 1) (ht3 : t ^ 3 = 1)
    (ht2 : ((t : k)) ^ 2 ≠ 1) : 4 ≤ localRank 3 G := by
  set φ : Fin 4 → SL(2, F) →* G := fun i => Θ.comp (te6SL2 θ j hj i) with hφ
  have hcomm : ∀ i i', i ≠ i' → ∀ A B : SL(2, F), φ i A * φ i' B = φ i' B * φ i A := by
    intro i i' hii A B
    simp only [hφ, MonoidHom.comp_apply, ← map_mul, te6SL2_commute θ j hj hii A B]
  set s := Θ (te6Torus θ hθ t) with hs
  have hsφ : ∀ i A, Commute (φ i A) s := fun i A =>
    (show Commute (te6Torus θ hθ t) (te6SL2 θ j hj i A) from
      te6Torus_commute θ j hj hθ htt i A).symm.map Θ
  have hne : ∀ i : Fin 3, i.castSucc ≠ 3 := fun i h => by
    have := congrArg Fin.val h
    simp at this
    omega
  have h4 := card_add_one_le_localRank_three (ι := Fin 3)
    (fun i => φ i.castSucc (sl2Three F)) s (fun i => φ i.castSucc (sl2Upper 1))
    (fun i i' => by
      by_cases h : i = i'
      · subst h
        exact Commute.refl _
      · exact hcomm _ _ (fun h' => h (Fin.castSucc_injective _ h')) _ _)
    (fun i => hsφ _ _)
    (fun i => by rw [← map_pow, sl2Three_pow_three, map_one])
    (by rw [hs, ← map_pow, te6Torus_pow, ht3, te6Torus_one, map_one])
    (fun h => te6Torus_not_mem_center θ hθ ht2 (hΘ _ h))
    (fun i i' h => hcomm _ _ (fun h' => h (Fin.castSucc_injective _ h')) _ _)
    (fun i => hsφ _ _)
    (fun i h => sl2Three_not_commute _ (hinj _ (by rw [map_mul, map_mul]; exact h.eq.symm)))
    (u := φ 3 (sl2Upper 1))
    (by
      rw [orderOf_injective _ (hinj 3)]
      exact orderOf_sl2Upper_one hF)
    (fun i => hcomm i.castSucc 3 (hne i) (sl2Three F) (sl2Upper 1)) (hsφ 3 (sl2Upper 1)).symm
  rw [Fintype.card_fin] at h4
  exact h4

end Twisted

end CFSG.RankThree.PartTwo.Census.Exceptional
