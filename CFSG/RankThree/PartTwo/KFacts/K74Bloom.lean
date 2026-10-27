module

public import CFSG.RankThree.PartTwo.KFacts.K74Normal
public import CFSG.RankThree.PartTwo.Toolkit.Bloom
public import Certificates.Certificate8171
public import Certificates.Certificate8172
public import CFSG.Assembly.QuasithinDefs
public import CFSG.Foundations
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.LocalAnalysis.SectionRank.SQT
public import CFSG.RankThree.PartTwo.NotationBlocks

public section

namespace CFSG.RankThree.PartTwo.KFacts

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.SubgroupLists
open scoped Matrix

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] noncomputable def glEquiv :
    GL (Fin 3) (ZMod 3) ≃* ((Fin 3 → ZMod 3) ≃ₗ[ZMod 3] (Fin 3 → ZMod 3)) :=
  Matrix.GeneralLinearGroup.toLin.trans (LinearMap.GeneralLinearGroup.generalLinearEquiv _ _)

theorem glEquiv_apply (g : GL (Fin 3) (ZMod 3)) (v : Fin 3 → ZMod 3) :
    glEquiv g v = (g : Matrix (Fin 3) (Fin 3) (ZMod 3)) *ᵥ v := by
  simp [glEquiv, LinearMap.GeneralLinearGroup.coeFn_generalLinearEquiv]

variable {G : Type} [Group G] {A : Subgroup G}

@[expose] noncomputable def glHom (f : Multiplicative (Fin 3 → ZMod 3) ≃* A) :
    MulAut A →* GL (Fin 3) (ZMod 3) :=
  glEquiv.symm.toMonoidHom.comp (Sec12.coordHom f)

theorem glHom_injective (f : Multiplicative (Fin 3 → ZMod 3) ≃* A) :
    Function.Injective (glHom f) :=
  glEquiv.symm.injective.comp (Sec12.coordHom_injective f)

theorem glEquiv_glHom (f : Multiplicative (Fin 3 → ZMod 3) ≃* A) (σ : MulAut A) :
    glEquiv (glHom f σ) = Sec12.coordHom f σ := by
  simp [glHom]

theorem isIrreducibleOn_map_glHom (f : Multiplicative (Fin 3 → ZMod 3) ≃* A)
    {S : Subgroup (MulAut A)} (hS : Sec21.IsIrreducibleOn S) :
    IsIrreducibleOn (S.map (glHom f)) := by
  intro W hW
  apply irreducible_coordHom f hS W
  rintro _ ⟨σ, hσ, rfl⟩ x hx
  have h := hW _ ⟨σ, hσ, rfl⟩ x hx
  rwa [← glEquiv_apply, glEquiv_glHom] at h

theorem bloomCaseC_of {H : Subgroup (GL (Fin 3) (ZMod 3))} (hH : IsIrreducibleOn H)
    (h4 : 4 ∣ Nat.card H) (hSL : ¬ CFSG.Assembly.LowTwoRank.StatedSL 3 (ZMod 3) ≤ H) :
    Toolkit.BloomCaseC H := by
  rcases (Toolkit.toolkit_clause2 H hH).1 with hA | hB | hC
  · exact absurd (h4.trans (Toolkit.card_dvd_78_of_caseA hA)) (by norm_num)
  · exact absurd (Toolkit.statedSL_le_of_caseB hB) hSL
  · exact hC

theorem neg_one_ne_one_GL : (-1 : GL (Fin 3) (ZMod 3)) ≠ 1 := by
  intro h
  have h1 := Toolkit.det_neg_one_GL
  rw [h, Units.val_one, Matrix.det_one] at h1
  exact absurd h1 (by decide)

theorem commute_of_mem_zpowers_neg_one {z : GL (Fin 3) (ZMod 3)}
    (hz : z ∈ Subgroup.zpowers (-1 : GL (Fin 3) (ZMod 3))) (g : GL (Fin 3) (ZMod 3)) :
    Commute z g := by
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
  exact (Commute.neg_one_left g).zpow_left j

theorem normal_zpowers_neg_one : (Subgroup.zpowers (-1 : GL (Fin 3) (ZMod 3))).Normal := by
  constructor
  intro n hn g
  rw [← (commute_of_mem_zpowers_neg_one hn g).eq, mul_inv_cancel_right]
  exact hn

theorem card_zpowers_neg_one : Nat.card (Subgroup.zpowers (-1 : GL (Fin 3) (ZMod 3))) = 2 := by
  rw [Nat.card_zpowers]
  exact orderOf_eq_prime (by rw [neg_one_sq]) neg_one_ne_one_GL

theorem card_three_torsion_alternating :
    (Finset.univ.filter fun y : alternatingGroup (Fin 4) => y ^ 3 = 1).card = 9 := by
  decide

theorem closure_three_torsion_alternating :
    Subgroup.closure {y : alternatingGroup (Fin 4) | y ^ 3 = 1} = ⊤ := by
  set T := {y : alternatingGroup (Fin 4) | y ^ 3 = 1} with hTdef
  have hT : T.ncard = 9 := by
    rw [Set.ncard_eq_toFinset_card', ← card_three_torsion_alternating]
    congr 1
  have h1 : 9 ≤ Nat.card (Subgroup.closure T) := by
    have h := Set.ncard_le_ncard (Subgroup.subset_closure (k := T))
    rw [hT] at h
    exact h.trans_eq (Nat.card_coe_set_eq _).symm
  have h12 : Nat.card (alternatingGroup (Fin 4)) = 12 := by
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
    rfl
  have h2 : Nat.card (Subgroup.closure T) ∣ 12 := h12 ▸ Subgroup.card_subgroup_dvd_card _
  apply Subgroup.eq_top_of_card_eq
  rw [h12]
  have h3 := Nat.le_of_dvd (by norm_num) h2
  interval_cases h : Nat.card (Subgroup.closure T) <;> simp_all

variable {H : Subgroup (GL (Fin 3) (ZMod 3))}

theorem closure_threeElements_of_caseC (hC : Toolkit.BloomCaseC H) :
    ∃ G₀ : Subgroup (GL (Fin 3) (ZMod 3)), Nonempty (G₀ ≃* alternatingGroup (Fin 4)) ∧
      Subgroup.closure {g | g ∈ H ∧ ∃ k : ℕ, g ^ 3 ^ k = 1} = G₀ := by
  obtain ⟨L, -, -, -, -, -, hdisj, G₀, hG₀N, hidx, ⟨e⟩, hG₀H, hHN⟩ := hC
  refine ⟨G₀, ⟨e⟩, le_antisymm ?_ ?_⟩
  · rw [Subgroup.closure_le]
    rintro g ⟨hgH, k, hk⟩
    have := normal_zpowers_neg_one
    have hg : g ∈ ((Toolkit.monomialDetOne L ⊔ Subgroup.zpowers (-1) :
        Subgroup (GL (Fin 3) (ZMod 3))) : Set (GL (Fin 3) (ZMod 3))) := hHN hgH
    rw [Subgroup.mul_normal, Set.mem_mul] at hg
    obtain ⟨n, hn, m, hm, rfl⟩ := hg
    have hcomm : Commute n m := (commute_of_mem_zpowers_neg_one hm n).symm
    rw [hcomm.mul_pow] at hk
    have hnm : n ^ 3 ^ k = (m ^ 3 ^ k)⁻¹ := eq_inv_of_mul_eq_one_left hk
    have hn1 : n ^ 3 ^ k = 1 := by
      have hmem : n ^ 3 ^ k ∈ Toolkit.monomialDetOne L ⊓ Subgroup.zpowers (-1) :=
        ⟨Subgroup.pow_mem _ hn _, hnm ▸ Subgroup.inv_mem _ (Subgroup.pow_mem _ hm _)⟩
      rw [hdisj] at hmem
      exact hmem
    have hm1 : m = 1 := by
      have hm2 : m ^ 2 = 1 := by
        obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hm
        rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, neg_one_sq, one_zpow]
      have hm3 : m ^ 3 ^ k = 1 := by
        rw [hn1, one_mul] at hk
        exact hk
      have hcop : Nat.gcd 2 (3 ^ k) = 1 :=
        Nat.Coprime.pow_right k (by norm_num : Nat.Coprime 2 3)
      have h := pow_gcd_eq_one.mpr ⟨hm2, hm3⟩
      rwa [hcop, pow_one] at h
    rw [hm1, mul_one]
    have hsq := Subgroup.sq_mem_of_index_two hidx ⟨n, hn⟩
    rw [Subgroup.mem_subgroupOf] at hsq
    obtain ⟨j, hj⟩ : ∃ j, 3 ^ k = 2 * j + 1 :=
      ⟨3 ^ k / 2, by have := Nat.odd_iff.mp (Odd.pow (by decide : Odd 3) : Odd (3 ^ k)); omega⟩
    have hn2 : n ^ (2 * j) ∈ G₀ := by
      rw [pow_mul]
      exact Subgroup.pow_mem _ hsq _
    have h1 : n = (n ^ (2 * j))⁻¹ * n ^ 3 ^ k := by
      rw [hj, pow_succ, ← mul_assoc, inv_mul_cancel, one_mul]
    rw [h1, hn1, mul_one]
    exact Subgroup.inv_mem _ hn2
  · intro x hx
    have hx' : (⟨x, hx⟩ : G₀) = e.symm (e ⟨x, hx⟩) := (e.symm_apply_apply _).symm
    have hcl : e ⟨x, hx⟩ ∈ Subgroup.closure {y : alternatingGroup (Fin 4) | y ^ 3 = 1} := by
      rw [closure_three_torsion_alternating]
      exact Subgroup.mem_top _
    have hmap : (Subgroup.closure {y : alternatingGroup (Fin 4) | y ^ 3 = 1}).map
        (G₀.subtype.comp e.symm.toMonoidHom) ≤
          Subgroup.closure {g | g ∈ H ∧ ∃ k : ℕ, g ^ 3 ^ k = 1} := by
      rw [MonoidHom.map_closure, Subgroup.closure_le]
      rintro _ ⟨y, hy, rfl⟩
      refine Subgroup.subset_closure ⟨hG₀H (e.symm y).2, 1, ?_⟩
      rw [pow_one, MonoidHom.comp_apply, ← map_pow, ← map_pow]
      rw [show y ^ 3 = 1 from hy, map_one, map_one]
    have h := hmap ⟨_, hcl, rfl⟩
    rwa [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, ← hx'] at h

theorem exists_injective_of_caseC (hC : Toolkit.BloomCaseC H) :
    ∃ φ : H →* Multiplicative (ZMod 2) × Equiv.Perm (Fin 4), Function.Injective φ := by
  obtain ⟨L, -, -, -, -, ⟨eN⟩, hdisj, -, -, -, -, -, hHN⟩ := hC
  set N₀ := Toolkit.monomialDetOne L with hN₀
  set Z := Subgroup.zpowers (-1 : GL (Fin 3) (ZMod 3)) with hZ
  let ψ : N₀ × Z →* GL (Fin 3) (ZMod 3) :=
    N₀.subtype.noncommCoprod Z.subtype fun n z => (commute_of_mem_zpowers_neg_one z.2 n).symm
  have hψ : ∀ x : N₀ × Z, ψ x = (x.1 : GL (Fin 3) (ZMod 3)) * x.2 := fun x => rfl
  have hψinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    rintro ⟨n, z⟩ h1
    rw [hψ] at h1
    have hnz : (n : GL (Fin 3) (ZMod 3)) = (z : GL (Fin 3) (ZMod 3))⁻¹ :=
      eq_inv_of_mul_eq_one_left h1
    have hmem : (n : GL (Fin 3) (ZMod 3)) ∈ N₀ ⊓ Z :=
      ⟨n.2, hnz ▸ Subgroup.inv_mem _ z.2⟩
    rw [hdisj, Subgroup.mem_bot] at hmem
    have hz : (z : GL (Fin 3) (ZMod 3)) = 1 := by
      rw [hmem, one_mul] at h1
      exact h1
    exact Prod.ext (Subtype.ext hmem) (Subtype.ext hz)
  have hrange : H ≤ ψ.range := by
    intro g hg
    have := normal_zpowers_neg_one
    have hg' : g ∈ ((N₀ ⊔ Z : Subgroup (GL (Fin 3) (ZMod 3))) : Set (GL (Fin 3) (ZMod 3))) :=
      hHN hg
    rw [Subgroup.mul_normal, Set.mem_mul] at hg'
    obtain ⟨n, hn, z, hz, rfl⟩ := hg'
    exact ⟨(⟨n, hn⟩, ⟨z, hz⟩), rfl⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let eZ : Z ≃* Multiplicative (ZMod 2) := mulEquivOfPrimeCardEq card_zpowers_neg_one (by simp)
  refine ⟨MulEquiv.prodComm.toMonoidHom.comp ((eN.prodCongr eZ).toMonoidHom.comp
    ((MonoidHom.ofInjective hψinj).symm.toMonoidHom.comp (Subgroup.inclusion hrange))), ?_⟩
  simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom]
  exact MulEquiv.prodComm.injective.comp ((eN.prodCongr eZ).injective.comp
    ((MonoidHom.ofInjective hψinj).symm.injective.comp (Subgroup.inclusion_injective hrange)))

@[expose] def RowOne (M : Mat33) : Prop := M 0 0 = 1 ∧ M 0 1 = 0 ∧ M 0 2 = 0

instance (M : Mat33) : Decidable (RowOne M) := by
  unfold RowOne
  infer_instance

theorem eq_one_of_rowOne_conj : ∀ a b c d : ZMod 3,
    RowOne (tr01 * !![1, 0, 0; 0, a, b; 0, c, d] * tr01i) →
    RowOne (tr02 * !![1, 0, 0; 0, a, b; 0, c, d] * tr02i) →
    (!![1, 0, 0; 0, a, b; 0, c, d] : Mat33) = 1 := by
  decide +kernel

theorem unip_facts : ∀ p q : ZMod 3,
    (!![1, -p, -q; 0, 1, 0; 0, 0, 1] : Mat33) * !![1, p, q; 0, 1, 0; 0, 0, 1] = 1 ∧
    (!![1, p, q; 0, 1, 0; 0, 0, 1] : Mat33) * !![1, -p, -q; 0, 1, 0; 0, 0, 1] = 1 := by
  decide

section Axis

variable {V : Type*} [AddCommGroup V] [Module (ZMod 3) V]

theorem exists_basis_adapted [FiniteDimensional (ZMod 3) V]
    (hV : Module.finrank (ZMod 3) V = 3) {u : V} {φ : Module.Dual (ZMod 3) V} (hφu : φ u = 1) :
    ∃ b : Module.Basis (Fin 3) (ZMod 3) V, b 0 = u ∧ ∀ y, b.repr y 0 = φ y := by
  have hu : u ≠ 0 := by
    rintro rfl
    rw [map_zero] at hφu
    exact zero_ne_one hφu
  obtain ⟨b', hb'⟩ := exists_basis_zero_eq hV hu
  obtain ⟨h1, h2⟩ := unip_facts (φ (b' 1)) (φ (b' 2))
  set b := b'.map (ofMat b' h1 h2) with hbdef
  have hbj : ∀ j,
      b j = ∑ i, (!![1, -φ (b' 1), -φ (b' 2); 0, 1, 0; 0, 0, 1] : Mat33) i j • b' i := by
    intro j
    rw [hbdef, Module.Basis.map_apply]
    exact Matrix.toLin_self b' b' _ j
  have hb0 : b 0 = u := by
    rw [hbj, Fin.sum_univ_three]
    simp [hb']
  have hφb : ∀ j, φ (b j) = if j = 0 then 1 else 0 := by
    intro j
    rw [hbj, map_sum, Fin.sum_univ_three]
    fin_cases j <;> simp [hb', hφu]
  refine ⟨b, hb0, fun y => ?_⟩
  conv_rhs => rw [← b.sum_repr y]
  rw [map_sum, Fin.sum_univ_three]
  simp [hφb]

theorem false_of_normal_of_axis [FiniteDimensional (ZMod 3) V]
    (hV : Module.finrank (ZMod 3) V = 3) {G N : Subgroup (V ≃ₗ[ZMod 3] V)} {u : V}
    {φ : Module.Dual (ZMod 3) V} (hφu : φ u = 1)
    (hSL : ∀ g : V ≃ₗ[ZMod 3] V, LinearMap.det (g : V →ₗ[ZMod 3] V) = 1 → g ∈ G)
    (hN1 : N ≠ ⊥) (hNfix : ∀ s ∈ N, s u = u) (hNax : ∀ s ∈ N, ∀ x, φ (s x - x) = 0)
    (hnorm : ∀ g ∈ G, g u = u → ∀ s ∈ N, g * s * g⁻¹ ∈ N) : False := by
  obtain ⟨b, hb0, hbφ⟩ := exists_basis_adapted hV hφu
  have hentry : ∀ (s : V ≃ₗ[ZMod 3] V) i j, matHom b s i j = b.repr (s (b j)) i := by
    intro s i j
    rw [matHom_apply, LinearMap.toMatrix_apply]
    rfl
  have hrow : ∀ s ∈ N, RowOne (matHom b s) := by
    intro s hs
    have h : ∀ j, matHom b s 0 j = b.repr (b j) 0 := by
      intro j
      rw [hentry, hbφ, hbφ]
      have := hNax s hs (b j)
      rw [map_sub, sub_eq_zero] at this
      exact this
    refine ⟨?_, ?_, ?_⟩ <;> rw [h, Module.Basis.repr_self] <;> simp
  obtain ⟨s, hs, hs1⟩ := (Subgroup.bot_or_exists_ne_one N).resolve_left hN1
  obtain ⟨r0, r1, r2⟩ := hrow s hs
  set M := matHom b s with hMdef
  have hcol : M 1 0 = 0 ∧ M 2 0 = 0 := by
    have h : ∀ i, M i 0 = b.repr (b 0) i := by
      intro i
      rw [hMdef, hentry, hb0, hNfix s hs]
    rw [h, h, Module.Basis.repr_self]
    simp
  have hMeta : M = !![1, 0, 0; 0, M 1 1, M 1 2; 0, M 2 1, M 2 2] := by
    have h := Matrix.eta_fin_three M
    rw [r0, r1, r2, hcol.1, hcol.2] at h
    exact h
  obtain ⟨⟨a1, a2, a3, a4, a5, a6⟩, ⟨c1, c2, c3, c4, c5, c6⟩, -, -⟩ := tr_facts
  have hconj : ∀ {T Ti : Mat33} (h1 : T * Ti = 1) (h2 : Ti * T = 1), T.det = 1 → T 0 0 = 1 →
      T 1 0 = 0 → T 2 0 = 0 → RowOne (T * M * Ti) := by
    intro T Ti h1 h2 hdet h00 h10 h20
    have hg : ofMat b h1 h2 ∈ G := hSL _ (by rw [det_ofMat, hdet])
    have hgu : ofMat b h1 h2 u = u := by
      rw [← hb0]
      exact ofMat_apply_zero b h1 h2 h00 h10 h20
    have h := hrow _ (hnorm _ hg hgu s hs)
    rwa [map_mul, map_mul, matHom_ofMat, matHom_ofMat_inv] at h
  have h01 := hconj a1 a2 a3 a4 a5 a6
  have h02 := hconj c1 c2 c3 c4 c5 c6
  rw [hMeta] at h01 h02
  have hM1 := eq_one_of_rowOne_conj _ _ _ _ h01 h02
  rw [← hMeta] at hM1
  exact hs1 (matHom_injective b (by rw [← hMdef, hM1, map_one]))

@[expose] def coordSubspace {G : Type} [Group G] {A : Subgroup G} (f : Multiplicative V ≃* A)
    (B : Subgroup A) : Submodule (ZMod 3) V where
  carrier := {v | f (Multiplicative.ofAdd v) ∈ B}
  add_mem' {v w} hv hw := by
    simp only [Set.mem_ofPred_eq, ofAdd_add, map_mul] at hv hw ⊢
    exact B.mul_mem hv hw
  zero_mem' := by
    simp only [Set.mem_ofPred_eq, ofAdd_zero, map_one]
    exact B.one_mem
  smul_mem' k v hv := by
    simp only [Set.mem_ofPred_eq] at hv ⊢
    have h1 : k • v = k.val • v := by
      rw [← Nat.cast_smul_eq_nsmul (ZMod 3), ZMod.natCast_zmod_val]
    rw [h1, ofAdd_nsmul, map_pow]
    exact B.pow_mem hv _

end Axis

theorem rank3II_13_2_bloom {G : Type} [Group G] {A : Subgroup G} [Finite A]
    (hA : CFSG.Assembly.IsElemAbelian 3 A) (h27 : Nat.card A = 27) {S : Subgroup (MulAut A)}
    (hirr : Sec21.IsIrreducibleOn S) (h4 : 4 ∣ Nat.card S) {c : A} {B : Subgroup A}
    (hcB : c ∉ B) {N : Subgroup (MulAut A)} (hN1 : N ≠ ⊥) (hNfix : ∀ n ∈ N, n c = c)
    (hNB : ∀ n ∈ N, ∀ x : A, n x * x⁻¹ ∈ B)
    (hnorm : ∀ σ ∈ S, σ c = c → ∀ n ∈ N, σ * n * σ⁻¹ ∈ N) :
    Nonempty (Subgroup.closure {σ : MulAut A | σ ∈ S ∧ ∃ k : ℕ, σ ^ 3 ^ k = 1} ≃*
        alternatingGroup (Fin 4)) ∧
      ∃ φ : S →* Multiplicative (ZMod 2) × Equiv.Perm (Fin 4), Function.Injective φ := by
  obtain ⟨f⟩ := Sec12.exists_coords hA (n := 3) (by rw [h27]; norm_num)
  have hinj := glHom_injective f
  have hHirr := isIrreducibleOn_map_glHom f hirr
  have hcard : Nat.card (S.map (glHom f)) = Nat.card S :=
    (Nat.card_congr (S.equivMapOfInjective _ hinj).toEquiv).symm
  have hSL : ¬ CFSG.Assembly.LowTwoRank.StatedSL 3 (ZMod 3) ≤ S.map (glHom f) := by
    intro hle
    have hV : Module.finrank (ZMod 3) (Fin 3 → ZMod 3) = 3 := Module.finrank_fin_fun (ZMod 3)
    have hcW : Sec12.coordVec f c ∉ coordSubspace f B := by
      intro h
      apply hcB
      have h' : f (Multiplicative.ofAdd (Sec12.coordVec f c)) ∈ B := h
      rwa [Sec12.coordVec, ofAdd_toAdd, MulEquiv.apply_symm_apply] at h'
    obtain ⟨φ, hφu, hφW⟩ := exists_dual_eq_one_of_not_mem hcW
    refine false_of_normal_of_axis hV (G := S.map (Sec12.coordHom f))
      (N := N.map (Sec12.coordHom f)) hφu ?_ ?_ ?_ ?_ ?_
    · intro g hg
      have hlin : Matrix.toLin' ((glEquiv.symm g : GL (Fin 3) (ZMod 3)) :
          Matrix (Fin 3) (Fin 3) (ZMod 3)) =
            (g : (Fin 3 → ZMod 3) →ₗ[ZMod 3] (Fin 3 → ZMod 3)) := by
        refine LinearMap.ext fun v => ?_
        rw [Matrix.toLin'_apply, ← glEquiv_apply, MulEquiv.apply_symm_apply]
        rfl
      have hdet : ((glEquiv.symm g : GL (Fin 3) (ZMod 3)) :
          Matrix (Fin 3) (Fin 3) (ZMod 3)).det = 1 := by
        rw [← LinearMap.det_toLin', hlin]
        exact hg
      obtain ⟨σ, hσ, hσg⟩ := hle (Subgroup.subset_closure hdet)
      refine ⟨σ, hσ, ?_⟩
      rw [← glEquiv_glHom, hσg, MulEquiv.apply_symm_apply]
    · intro h
      apply hN1
      rw [eq_bot_iff]
      intro n hn
      have h1 : Sec12.coordHom f n ∈ N.map (Sec12.coordHom f) := ⟨n, hn, rfl⟩
      rw [h, Subgroup.mem_bot] at h1
      rw [Subgroup.mem_bot]
      exact Sec12.coordHom_injective f (h1.trans (map_one _).symm)
    · rintro _ ⟨n, hn, rfl⟩
      rw [coordHom_coordVec, hNfix n hn]
    · rintro _ ⟨n, hn, rfl⟩ x
      apply hφW
      show f (Multiplicative.ofAdd (Sec12.coordHom f n x - x)) ∈ B
      rw [ofAdd_sub, map_div, Sec12.coordHom_apply, ofAdd_toAdd, MulEquiv.apply_symm_apply,
        div_eq_mul_inv]
      exact hNB n hn _
    · rintro _ ⟨σ, hσ, rfl⟩ hσu _ ⟨n, hn, rfl⟩
      rw [coordHom_coordVec] at hσu
      have hσc : σ c = c := coordVec_injective f hσu
      exact ⟨σ * n * σ⁻¹, hnorm σ hσ hσc n hn, by simp only [map_mul, map_inv]⟩
  have hC := bloomCaseC_of hHirr (hcard ▸ h4) hSL
  obtain ⟨G₀, ⟨e⟩, hcl⟩ := closure_threeElements_of_caseC hC
  obtain ⟨φ, hφ⟩ := exists_injective_of_caseC hC
  refine ⟨⟨?_⟩, φ.comp (S.equivMapOfInjective _ hinj).toMonoidHom, ?_⟩
  · set C := Subgroup.closure {σ : MulAut A | σ ∈ S ∧ ∃ k : ℕ, σ ^ 3 ^ k = 1} with hCdef
    have hCmap : C.map (glHom f) = G₀ := by
      rw [hCdef, MonoidHom.map_closure, ← hcl]
      congr 1
      ext g
      constructor
      · rintro ⟨σ, ⟨hσ, k, hk⟩, rfl⟩
        exact ⟨⟨σ, hσ, rfl⟩, k, by rw [← map_pow, hk, map_one]⟩
      · rintro ⟨⟨σ, hσ, rfl⟩, k, hk⟩
        exact ⟨σ, ⟨hσ, k, hinj (by rw [map_pow, hk, map_one])⟩, rfl⟩
    exact (C.equivMapOfInjective _ hinj).trans ((MulEquiv.subgroupCongr hCmap).trans e)
  · simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom]
    exact hφ.comp (MulEquiv.injective _)

end CFSG.RankThree.PartTwo.KFacts
