module

public import CFSG.RankThree.SubgroupLists.ExtraspecialNormal
public import CFSG.LocalAnalysis.ComponentClassification.GeneralizedFitting
public import CFSG.GroupTheory.LocalCores.Components

public section

namespace CFSG.RankThree.SubgroupLists

open Matrix CFSG.RepresentationTheory

variable {K : Type*} [Field K]

theorem not_isTransitiveMonomial_of_perfect {G : Subgroup (GL (Fin 3) K)} [Group.IsPerfect G] :
    ¬ IsTransitiveMonomial G := by
  classical
  rintro ⟨L, hint, hdim, hperm, htrans⟩
  have hinj : Function.Injective L := by
    intro i j hij
    by_contra hne
    have hdisj : Disjoint (L i) (L j) := hint.submodule_iSupIndep.pairwiseDisjoint hne
    rw [hij, disjoint_self] at hdisj
    have := hdim j
    rw [hdisj, finrank_bot] at this
    exact zero_ne_one this
  choose π hπ using hperm
  have hcongr : ∀ (a b : GL (Fin 3) K) (ha : a ∈ G) (hb : b ∈ G), a = b → π a ha = π b hb := by
    rintro a b ha hb rfl
    rfl
  have hmul : ∀ (a b : GL (Fin 3) K) (ha : a ∈ G) (hb : b ∈ G) (i : Fin 3),
      π (a * b) (G.mul_mem ha hb) i = π a ha (π b hb i) := by
    intro a b ha hb i
    apply hinj
    rw [← hπ (a * b) (G.mul_mem ha hb) i, translate_mul, hπ b hb i, hπ a ha]
  have hone : ∀ i, π 1 G.one_mem i = i := by
    intro i
    apply hinj
    rw [← hπ 1 G.one_mem i, translate_one]
  have hinv : ∀ (a : GL (Fin 3) K) (ha : a ∈ G) (i : Fin 3),
      π a⁻¹ (G.inv_mem ha) (π a ha i) = i := by
    intro a ha i
    rw [← hmul, hcongr _ 1 _ G.one_mem (inv_mul_cancel a), hone]
  have hinv' : ∀ (a : GL (Fin 3) K) (ha : a ∈ G) (i : Fin 3),
      π a ha (π a⁻¹ (G.inv_mem ha) i) = i := by
    intro a ha i
    rw [← hmul, hcongr _ 1 _ G.one_mem (mul_inv_cancel a), hone]
  let ρ : G →* Equiv.Perm (Fin 3) :=
    { toFun := fun g =>
        { toFun := π g g.2
          invFun := π (g : GL (Fin 3) K)⁻¹ (G.inv_mem g.2)
          left_inv := fun i => hinv g g.2 i
          right_inv := fun i => hinv' g g.2 i }
      map_one' := Equiv.ext fun i => hone i
      map_mul' := fun a b => Equiv.ext fun i => hmul a b a.2 b.2 i }
  have hsign : ∀ g : G, Equiv.Perm.sign (ρ g) = 1 := fun g =>
    (MonoidHom.mem_ker (f := Equiv.Perm.sign.comp ρ)).mp
      (Abelianization.commutator_subset_ker _ (Group.IsPerfect.mem_commutator (g := g)))
  let ρ' : G →* alternatingGroup (Fin 3) :=
    ρ.codRestrict _ fun g => Equiv.Perm.mem_alternatingGroup.mpr (hsign g)
  have : IsMulCommutative (alternatingGroup (Fin 3)) :=
    alternatingGroup.isMulCommutative_of_card_le_three (by simp)
  have htriv : ∀ g : G, ρ g = 1 := fun g =>
    congrArg Subtype.val (Abelianization.commutator_subset_ker ρ'
      (Group.IsPerfect.mem_commutator (g := g)))
  obtain ⟨g, hg, hg01⟩ := htrans 0 1
  have h0 : π g hg 0 = 0 := congrArg (fun σ : Equiv.Perm (Fin 3) => σ 0) (htriv ⟨g, hg⟩)
  have h := hπ g hg 0
  rw [hg01, h0] at h
  exact absurd (hinj h) (by decide)

theorem map_subtype_conj_mem {σ : Type*} [Fintype σ] [DecidableEq σ]
    {G : Subgroup (GL σ K)} (A : Subgroup G) [hA : A.Normal] :
    ∀ g ∈ G, ∀ x ∈ A.map G.subtype, g * x * g⁻¹ ∈ A.map G.subtype := by
  intro g hg x hx
  obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
  refine Subgroup.mem_map.mpr ⟨_, hA.conj_mem a ha ⟨g, hg⟩, ?_⟩
  simp only [map_mul, map_inv, Subgroup.coe_subtype]

theorem mem_center_of_scalar {G : Subgroup (GL (Fin 3) K)} {x : G} {c : K}
    (hc : ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = Matrix.scalar (Fin 3) c) :
    x ∈ Subgroup.center G := by
  have hz : (x : GL (Fin 3) K) ∈ Subgroup.center (GL (Fin 3) K) :=
    Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.mpr ⟨c, hc.symm⟩
  exact Subgroup.mem_center_iff.mpr fun y => Subtype.ext (Subgroup.mem_center_iff.mp hz y)

theorem not_forall_scalar_of_perfect {G : Subgroup (GL (Fin 3) K)} (A : Subgroup G)
    [Group.IsPerfect A] (hA : A ≠ ⊥) :
    ¬ ∀ x ∈ A.map G.subtype, ∃ c : K, (x : Matrix (Fin 3) (Fin 3) K) = Matrix.scalar (Fin 3) c := by
  intro h
  apply hA
  apply ComponentClassification.Quasisimple.perfect_le_center_eq_bot A
  intro a ha
  obtain ⟨c, hc⟩ := h _ (Subgroup.mem_map_of_mem _ ha)
  exact mem_center_of_scalar hc

theorem fitting_le_scalar [Finite K] {G : Subgroup (GL (Fin 3) K)}
    (hcore : ∀ r : ℕ, r.Prime → ∀ R ≤ G, (∀ g ∈ G, ∀ x ∈ R, g * x * g⁻¹ ∈ R) → IsPGroup r R →
      ∀ x ∈ R, ∃ c : K, (x : Matrix (Fin 3) (Fin 3) K) = Matrix.scalar (Fin 3) c)
    {x : G} (hx : x ∈ ComponentClassification.Fitting.subgroup G) :
    ∃ c : K, ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = Matrix.scalar (Fin 3) c := by
  have hle : ComponentClassification.Fitting.subgroup G ≤
      (Subgroup.center (GL (Fin 3) K)).comap G.subtype := by
    rw [ComponentClassification.PrimeCore.fitting_eq_join]
    refine iSup_le fun r => ?_
    have : (ComponentClassification.PrimeCore.subgroup r.1 G).Normal :=
      ComponentClassification.PrimeCore.normal _ _
    intro y hy
    obtain ⟨c, hc⟩ := hcore r.1 r.2
      ((ComponentClassification.PrimeCore.subgroup r.1 G).map G.subtype)
      (Subgroup.map_subtype_le _) (map_subtype_conj_mem _)
      ((ComponentClassification.PrimeCore.isPGroup _ _).map _) _ (Subgroup.mem_map_of_mem _ hy)
    exact Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.mpr ⟨c, hc.symm⟩
  obtain ⟨c, hc⟩ := Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.mp (hle hx)
  exact ⟨c, hc.symm⟩

theorem exists_component_of_irreducible [Finite K] {G : Subgroup (GL (Fin 3) K)}
    (hG : IsIrreducibleMatrixRep G.subtype)
    (hcore : ∀ r : ℕ, r.Prime → ∀ R ≤ G, (∀ g ∈ G, ∀ x ∈ R, g * x * g⁻¹ ∈ R) → IsPGroup r R →
      ∀ x ∈ R, ∃ c : K, (x : Matrix (Fin 3) (Fin 3) K) = Matrix.scalar (Fin 3) c) :
    ∃ L : Subgroup G, CFSG.Open.IsComponentOf L ⊤ := by
  by_contra hno
  push Not at hno
  have hE : ComponentClassification.Layer.subgroup G = ⊥ :=
    sSup_eq_bot.mpr fun L hL => absurd hL (hno L)
  have hcent : ComponentClassification.GeneralizedFitting.subgroup G ≤ Subgroup.center G := by
    rw [ComponentClassification.GeneralizedFitting.subgroup, hE, sup_bot_eq]
    intro x hx
    obtain ⟨c, hc⟩ := fitting_le_scalar hcore hx
    exact mem_center_of_scalar hc
  have hcomm := ComponentClassification.GeneralizedFitting.commutative_of_le_center G hcent
  have : Group.IsNilpotent (⊤ : Subgroup G) :=
    ComponentClassification.Fitting.nilpotent_of_ambient_commutator_le_center ⊤ fun x _ =>
      Subgroup.mem_center_iff.mpr fun y => mul_comm' y x
  have htop : (⊤ : Subgroup G) ≤ ComponentClassification.Fitting.subgroup G :=
    ComponentClassification.Fitting.maximal ⊤
  apply not_irreducible_of_forall_scalar (by norm_num) _ hG
  intro g hg
  exact fitting_le_scalar hcore (x := ⟨g, hg⟩) (htop (Subgroup.mem_top _))

theorem component_irreducible [Finite K] {G : Subgroup (GL (Fin 3) K)}
    (hnorm : ∀ N : Subgroup (GL (Fin 3) K), (∀ g ∈ G, ∀ x ∈ N, g * x * g⁻¹ ∈ N) →
      IsIrreducibleMatrixRep N.subtype ∨
        ∀ x ∈ N, ∃ c : K, (x : Matrix (Fin 3) (Fin 3) K) = Matrix.scalar (Fin 3) c)
    {L : Subgroup G} (hL : CFSG.Open.IsComponentOf L ⊤) :
    IsIrreducibleMatrixRep (L.map G.subtype).subtype ∧
      ∀ M : Matrix (Fin 3) (Fin 3) K,
        (∀ x ∈ L.map G.subtype, (x : Matrix (Fin 3) (Fin 3) K) * M = M * x) →
          ∃ c : K, M = Matrix.scalar (Fin 3) c := by
  classical
  have : Group.IsPerfect L := ⟨hL.2.2.1⟩
  have hLne : L ≠ ⊥ :=
    (Subgroup.nontrivial_iff_ne_bot L).mp (ComponentClassification.Quasisimple.nontrivial hL.2.2)
  have : (ComponentClassification.Layer.subgroup G).Normal :=
    ComponentClassification.Layer.normal G
  have : Group.IsPerfect (ComponentClassification.Layer.subgroup G) :=
    ComponentClassification.Layer.perfect G
  have hLE : L ≤ ComponentClassification.Layer.subgroup G :=
    ComponentClassification.Layer.component_le hL
  have hEne : ComponentClassification.Layer.subgroup G ≠ ⊥ := by
    intro h
    rw [h, le_bot_iff] at hLE
    exact hLne hLE
  have hEirr : IsIrreducibleMatrixRep
      ((ComponentClassification.Layer.subgroup G).map G.subtype).subtype :=
    (hnorm _ (map_subtype_conj_mem _)).resolve_right (not_forall_scalar_of_perfect _ hEne)
  have : Group.IsPerfect ((ComponentClassification.Layer.subgroup G).map G.subtype) :=
    Group.IsPerfect.map _
  have hLn : (L.subgroupOf (ComponentClassification.Layer.subgroup G)).Normal :=
    ComponentClassification.Layer.normal_component hL
  have hLEn : ∀ g ∈ (ComponentClassification.Layer.subgroup G).map G.subtype,
      ∀ x ∈ L.map G.subtype, g * x * g⁻¹ ∈ L.map G.subtype := by
    intro g hg x hx
    obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.mp hg
    obtain ⟨l, hl, rfl⟩ := Subgroup.mem_map.mp hx
    have hmem : (⟨l, hLE hl⟩ : ComponentClassification.Layer.subgroup G) ∈
        L.subgroupOf (ComponentClassification.Layer.subgroup G) := hl
    have hconj := hLn.conj_mem _ hmem ⟨e, he⟩
    refine Subgroup.mem_map.mpr ⟨_, hconj, ?_⟩
    simp only [Subgroup.coe_subtype, map_mul, map_inv]
  rcases irreducible_or_scalar_or_transitiveMonomial Nat.prime_three hEirr hLEn with h | h | h
  · refine ⟨h, ?_⟩
    rcases scalar_commutant_or_cyclic Nat.prime_three h with hs | ⟨hcyc, -⟩
    · exact fun M hM => hs M hM
    · exfalso
      have : IsMulCommutative (L.map G.subtype) := hcyc.isMulCommutative
      have : Group.IsPerfect (L.map G.subtype) := Group.IsPerfect.map _
      have hbot : L.map G.subtype = ⊥ := Subgroup.eq_bot_of_subsingleton _
      exact hLne ((Subgroup.map_eq_bot_iff_of_injective L G.subtype_injective).mp hbot)
  · exact absurd h (not_forall_scalar_of_perfect L hLne)
  · exact absurd h not_isTransitiveMonomial_of_perfect

theorem component_unique [Finite K] {G : Subgroup (GL (Fin 3) K)}
    (hnorm : ∀ N : Subgroup (GL (Fin 3) K), (∀ g ∈ G, ∀ x ∈ N, g * x * g⁻¹ ∈ N) →
      IsIrreducibleMatrixRep N.subtype ∨
        ∀ x ∈ N, ∃ c : K, (x : Matrix (Fin 3) (Fin 3) K) = Matrix.scalar (Fin 3) c)
    {L₁ L₂ : Subgroup G} (h₁ : CFSG.Open.IsComponentOf L₁ ⊤)
    (h₂ : CFSG.Open.IsComponentOf L₂ ⊤) : L₁ = L₂ := by
  by_contra hne
  have hc := ComponentClassification.LocalComponents.commute_of_ne L₁ L₂ h₁ h₂ hne
  obtain ⟨-, hscal⟩ := component_irreducible hnorm h₁
  have : Group.IsPerfect L₂ := ⟨h₂.2.2.1⟩
  have hL₂ne : L₂ ≠ ⊥ :=
    (Subgroup.nontrivial_iff_ne_bot L₂).mp (ComponentClassification.Quasisimple.nontrivial h₂.2.2)
  apply not_forall_scalar_of_perfect L₂ hL₂ne
  intro x hx
  obtain ⟨l₂, hl₂, rfl⟩ := Subgroup.mem_map.mp hx
  apply hscal
  intro y hy
  obtain ⟨l₁, hl₁, rfl⟩ := Subgroup.mem_map.mp hy
  have hcomm : l₁ * l₂ = l₂ * l₁ := by
    have hmem := Subgroup.commutator_mem_commutator hl₁ hl₂
    rw [hc, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
    exact hmem
  have := congrArg (fun z : G => ((z : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) hcomm
  simpa only [Subgroup.coe_subtype, Subgroup.coe_mul, Units.val_mul] using this

theorem exists_quasisimple_normal_gl3 [Finite K] {G : Subgroup (GL (Fin 3) K)}
    (hG : IsIrreducibleMatrixRep G.subtype)
    (hnorm : ∀ N : Subgroup (GL (Fin 3) K), (∀ g ∈ G, ∀ x ∈ N, g * x * g⁻¹ ∈ N) →
      IsIrreducibleMatrixRep N.subtype ∨
        ∀ x ∈ N, ∃ c : K, (x : Matrix (Fin 3) (Fin 3) K) = Matrix.scalar (Fin 3) c)
    (hcore : ∀ r : ℕ, r.Prime → ∀ R ≤ G, (∀ g ∈ G, ∀ x ∈ R, g * x * g⁻¹ ∈ R) → IsPGroup r R →
      ∀ x ∈ R, ∃ c : K, (x : Matrix (Fin 3) (Fin 3) K) = Matrix.scalar (Fin 3) c) :
    ∃ H ≤ G, (∀ g ∈ G, ∀ x ∈ H, g * x * g⁻¹ ∈ H) ∧ CFSG.IsQuasisimple H ∧
      IsIrreducibleMatrixRep H.subtype ∧
      (∀ M : Matrix (Fin 3) (Fin 3) K, (∀ x ∈ H, (x : Matrix (Fin 3) (Fin 3) K) * M = M * x) →
        ∃ c : K, M = Matrix.scalar (Fin 3) c) ∧
      (∀ x ∈ H, (x : Matrix (Fin 3) (Fin 3) K).det = 1) ∧
      Nat.card (Subgroup.center H) ∣ 3 := by
  classical
  obtain ⟨L, hL⟩ := exists_component_of_irreducible hG hcore
  have hEL : ComponentClassification.Layer.subgroup G = L :=
    le_antisymm (sSup_le fun L' hL' => (component_unique hnorm hL hL').symm.le)
      (ComponentClassification.Layer.component_le hL)
  have : L.Normal := by
    rw [← hEL]
    exact ComponentClassification.Layer.normal G
  obtain ⟨hirr, hscal⟩ := component_irreducible hnorm hL
  have : Group.IsPerfect L := ⟨hL.2.2.1⟩
  have : Group.IsPerfect (L.map G.subtype) := Group.IsPerfect.map _
  have hdet : ∀ x ∈ L.map G.subtype, (x : Matrix (Fin 3) (Fin 3) K).det = 1 := by
    intro x hx
    have h1 := (MonoidHom.mem_ker
      (f := Matrix.GeneralLinearGroup.det.comp (L.map G.subtype).subtype)).mp
      (Abelianization.commutator_subset_ker _
        (Group.IsPerfect.mem_commutator (g := (⟨x, hx⟩ : L.map G.subtype))))
    have h2 := congrArg Units.val h1
    simpa only [MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype,
      Matrix.GeneralLinearGroup.val_det_apply, Units.val_one] using h2
  refine ⟨L.map G.subtype, Subgroup.map_subtype_le _, map_subtype_conj_mem L, ?_, hirr, hscal,
    hdet, ?_⟩
  · have hq : CFSG.IsQuasisimple L := ⟨⟨hL.2.2.1⟩, hL.2.2.2,
      ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian L hL.2.2⟩
    exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (L.equivMapOfInjective G.subtype G.subtype_injective) hq
  · set H := L.map G.subtype with hH
    have hcs : ∀ z : Subgroup.center H, ∃ c : K,
        (((z : H) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = Matrix.scalar (Fin 3) c := by
      intro z
      apply hscal
      intro x hx
      have hzx := Subgroup.mem_center_iff.mp z.2 ⟨x, hx⟩
      have := congrArg (fun w : H => ((w : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) hzx
      simpa only [Subgroup.coe_mul, Units.val_mul] using this
    have hcyc : IsCyclic (Subgroup.center H) :=
      isCyclic_of_forall_scalar (H.subtype.comp (Subgroup.center H).subtype)
        (H.subtype_injective.comp (Subgroup.center H).subtype_injective) hcs
    have hz3 : ∀ z : Subgroup.center H, z ^ 3 = 1 := by
      intro z
      obtain ⟨c, hc⟩ := hcs z
      have hd := hdet _ (z : H).2
      rw [hc] at hd
      have hc3 : c ^ 3 = 1 := by
        simpa [Matrix.scalar_apply, Matrix.det_diagonal, Fin.prod_univ_three, pow_three,
          mul_assoc] using hd
      apply Subtype.ext
      apply Subtype.ext
      apply Units.ext
      simp only [SubmonoidClass.coe_pow, Units.val_pow_eq_pow_val, hc, OneMemClass.coe_one,
        Units.val_one]
      rw [← map_pow, hc3, map_one]
    rw [← IsCyclic.exponent_eq_card]
    exact Monoid.exponent_dvd_of_forall_pow_eq_one hz3

theorem irreducible_gl3_reduction [Finite K] {G : Subgroup (GL (Fin 3) K)}
    (hG : IsIrreducibleMatrixRep G.subtype) :
    (∃ H ≤ G, (∀ g ∈ G, ∀ x ∈ H, g * x * g⁻¹ ∈ H) ∧ IsIrreducibleMatrixRep H.subtype ∧
        IsCyclic H ∧ Nat.card H ∣ Nat.card K ^ 3 - 1 ∧ ¬ Nat.card H ∣ Nat.card K - 1) ∨
      IsTransitiveMonomial G ∨
      (3 ∣ Nat.card K - 1 ∧ ∃ H ≤ G, (∀ g ∈ G, ∀ x ∈ H, g * x * g⁻¹ ∈ H) ∧
        IsIrreducibleMatrixRep H.subtype ∧ Nat.card H = 3 ^ 3 ∧ IsExtraspecialPGroup 3 H) ∨
      (∃ H ≤ G, (∀ g ∈ G, ∀ x ∈ H, g * x * g⁻¹ ∈ H) ∧ CFSG.IsQuasisimple H ∧
        IsIrreducibleMatrixRep H.subtype ∧
        (∀ M : Matrix (Fin 3) (Fin 3) K, (∀ x ∈ H, (x : Matrix (Fin 3) (Fin 3) K) * M = M * x) →
          ∃ c : K, M = Matrix.scalar (Fin 3) c) ∧
        (∀ x ∈ H, (x : Matrix (Fin 3) (Fin 3) K).det = 1) ∧
        Nat.card (Subgroup.center H) ∣ 3) := by
  rcases irreducible_prime_degree_reduction Nat.prime_three hG with h | h | ⟨-, hnorm, habel⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  by_cases hcore : ∀ r : ℕ, r.Prime → ∀ R ≤ G, (∀ g ∈ G, ∀ x ∈ R, g * x * g⁻¹ ∈ R) →
      IsPGroup r R → ∀ x ∈ R, ∃ c : K, (x : Matrix (Fin 3) (Fin 3) K) = Matrix.scalar (Fin 3) c
  · exact Or.inr (Or.inr (Or.inr (exists_quasisimple_normal_gl3 hG hnorm hcore)))
  · push Not at hcore
    obtain ⟨r, hr, R, hRG, hRn, hRp, x, hx, hxs⟩ := hcore
    have : Fact r.Prime := ⟨hr⟩
    obtain ⟨-, h3, H, hHG, hHn, hHirr, hH27, hHex⟩ :=
      normal_pGroup_extraspecial_gl3 hnorm habel hRG hRn hRp ⟨x, hx, hxs⟩
    exact Or.inr (Or.inr (Or.inl ⟨h3, H, hHG, hHn, hHirr, hH27, hHex⟩))

end CFSG.RankThree.SubgroupLists
