module

public import CFSG.LocalAnalysis.UniquenessCase.UC6N588B2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6

open Subgroup CFSG.Open CFSG.ABGLocalTools
open CFSG.RankThree.PartOne (torusWeyl torusIrreducible)
open CFSG.RankThree.PartOne.LinAlg (bsub torusWeylGL wActionGL)
open scoped Matrix

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section Cartan

variable {p : ℕ} [Fact p.Prime] {W : Fin 3 → Submodule (ZMod p) (Fin 3 → ZMod p)}

theorem exists_basis_of_decomp (hW1 : ∀ i, Module.finrank (ZMod p) (W i) = 1) (hWi : iSupIndep W)
    (hWt : (⨆ i, W i) = ⊤) :
    ∃ b : Module.Basis (Fin 3) (ZMod p) (Fin 3 → ZMod p),
      ∀ i (v : Fin 3 → ZMod p), v ∈ W i ↔ ∀ j, j ≠ i → b.repr v j = 0 := by
  classical
  have hne : ∀ i, W i ≠ ⊥ := fun i h => by
    have := hW1 i
    rw [h, finrank_bot] at this
    exact zero_ne_one this
  choose w hw hw0 using fun i => Submodule.exists_mem_ne_zero_of_ne_bot (hne i)
  have hli : LinearIndependent (ZMod p) w := hWi.linearIndependent W hw hw0
  have hspan : ∀ i, W i = Submodule.span (ZMod p) {w i} := by
    intro i
    refine (Submodule.eq_of_le_of_finrank_eq ((Submodule.span_singleton_le_iff_mem _ _).2 (hw i))
      ?_).symm
    rw [hW1 i, finrank_span_singleton (hw0 i)]
  have hsp : ⊤ ≤ Submodule.span (ZMod p) (Set.range w) := by
    rw [← hWt]
    refine iSup_le fun i => ?_
    rw [hspan i]
    exact Submodule.span_mono (Set.singleton_subset_iff.2 (Set.mem_range_self i))
  refine ⟨Module.Basis.mk hli hsp, fun i v => ?_⟩
  have hbi : (Module.Basis.mk hli hsp) '' {i} = {w i} := by
    rw [Set.image_singleton, Module.Basis.mk_apply]
  rw [hspan i, ← hbi, Module.Basis.mem_span_image]
  constructor
  · intro h j hj
    by_contra hc
    exact hj (h (Finsupp.mem_support_iff.2 hc))
  · intro h j hj
    by_contra hc
    exact Finsupp.mem_support_iff.1 hj (h j hc)

theorem exists_diag_mem_cartan (b : Module.Basis (Fin 3) (ZMod p) (Fin 3 → ZMod p))
    (hb : ∀ i (v : Fin 3 → ZMod p), v ∈ W i ↔ ∀ j, j ≠ i → b.repr v j = 0)
    (c : Fin 3 → (ZMod p)ˣ) :
    ∃ d : GL (Fin 3) (ZMod p), d ∈ UCK.cartanOfDecomp p W ∧
      ∀ (v : Fin 3 → ZMod p) j,
        b.repr ((d : Matrix (Fin 3) (Fin 3) (ZMod p)) *ᵥ v) j = (c j : ZMod p) * b.repr v j := by
  let D : (Fin 3 → ZMod p) ≃ₗ[ZMod p] (Fin 3 → ZMod p) :=
    LinearEquiv.piCongrRight fun i => LinearEquiv.smulOfUnit (c i)
  let e := b.equivFun
  let dL : (Fin 3 → ZMod p) ≃ₗ[ZMod p] (Fin 3 → ZMod p) := e.trans (D.trans e.symm)
  have hcoord : ∀ (v : Fin 3 → ZMod p) j,
      b.repr ((CFSG.RankThree.PartOne.LinAlg.toGL dL : GL (Fin 3) (ZMod p)) *ᵥ v) j =
        (c j : ZMod p) * b.repr v j := by
    intro v j
    rw [CFSG.RankThree.PartOne.LinAlg.toGL_mulVec]
    have h1 : e (dL v) = D (e v) := by simp [dL]
    have h2 := congrFun h1 j
    simp only [e, Module.Basis.equivFun_apply, D, LinearEquiv.piCongrRight_apply,
      LinearEquiv.smulOfUnit, Units.smul_def, smul_eq_mul] at h2
    exact h2
  refine ⟨CFSG.RankThree.PartOne.LinAlg.toGL dL, fun i v => ?_, hcoord⟩
  rw [hb, hb]
  refine forall₂_congr fun j _ => ?_
  rw [hcoord, mul_eq_zero]
  simp

theorem decomp_injective (hW1 : ∀ i, Module.finrank (ZMod p) (W i) = 1) (hWi : iSupIndep W) :
    Function.Injective W := by
  intro i j hij
  by_contra hne
  have hdis : Disjoint (W i) (W j) := hWi.pairwiseDisjoint hne
  rw [hij, disjoint_self] at hdis
  have := hW1 j
  rw [hdis, finrank_bot] at this
  exact zero_ne_one this

theorem eq_of_cartan_invariant (h5 : 5 ≤ p) (hW1 : ∀ i, Module.finrank (ZMod p) (W i) = 1)
    (hWi : iSupIndep W) (hWt : (⨆ i, W i) = ⊤) {U : Submodule (ZMod p) (Fin 3 → ZMod p)}
    (hU1 : Module.finrank (ZMod p) U = 1)
    (hU : ∀ d ∈ UCK.cartanOfDecomp p W, ∀ u ∈ U, (d : Matrix (Fin 3) (Fin 3) (ZMod p)) *ᵥ u ∈ U) :
    ∃ j, U = W j := by
  classical
  obtain ⟨b, hb⟩ := exists_basis_of_decomp hW1 hWi hWt
  have hp := (Fact.out : p.Prime)
  have hcast : ∀ a k : ℕ, a < p → k < p → ((a : ZMod p) = (k : ZMod p) ↔ a = k) := by
    intro a k ha hk
    rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hk]
  have hne0 : ∀ k : ℕ, 0 < k → k < p → (k : ZMod p) ≠ 0 := by
    intro k hk hkp h
    have := (hcast k 0 hkp hp.pos).1 (by simpa using h)
    omega
  let c : Fin 3 → (ZMod p)ˣ := fun i => Units.mk0 ((i : ℕ) + 1 : ℕ) (hne0 _ (by omega)
    (by have := i.2; omega))
  have hcinj : ∀ i j : Fin 3, (c i : ZMod p) = c j → i = j := by
    intro i j h
    have h' : (((i : ℕ) + 1 : ℕ) : ZMod p) = (((j : ℕ) + 1 : ℕ) : ZMod p) := h
    rw [hcast _ _ (by have := i.2; omega) (by have := j.2; omega)] at h'
    exact Fin.ext (by omega)
  obtain ⟨d, hdC, hd⟩ := exists_diag_mem_cartan b hb c
  have hU0 : U ≠ ⊥ := fun h => by
    rw [h, finrank_bot] at hU1
    exact zero_ne_one hU1
  obtain ⟨v, hvU, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU0
  have hUspan : U = Submodule.span (ZMod p) {v} :=
    (Submodule.eq_of_le_of_finrank_eq ((Submodule.span_singleton_le_iff_mem _ _).2 hvU)
      (by rw [hU1, finrank_span_singleton hv0])).symm
  have hdv : (d : Matrix (Fin 3) (Fin 3) (ZMod p)) *ᵥ v ∈ Submodule.span (ZMod p) {v} := by
    rw [← hUspan]
    exact hU d hdC v hvU
  obtain ⟨μ, hμ⟩ := Submodule.mem_span_singleton.1 hdv
  have hco : ∀ j, (c j : ZMod p) * b.repr v j = μ * b.repr v j := by
    intro j
    rw [← hd v j, ← hμ, map_smul, Finsupp.smul_apply, smul_eq_mul]
  obtain ⟨j, hj⟩ : ∃ j, b.repr v j ≠ 0 := by
    by_contra hall
    apply hv0
    have : b.repr v = 0 := Finsupp.ext fun k => by
      by_contra hk
      exact hall ⟨k, hk⟩
    simpa using this
  have hμj : μ = c j := (mul_right_cancel₀ hj (hco j)).symm
  refine ⟨j, ?_⟩
  have hvW : v ∈ W j := by
    rw [hb]
    intro k hk
    by_contra hk0
    have h1 := mul_right_cancel₀ hk0 (hco k)
    rw [hμj] at h1
    exact hk (hcinj k j h1)
  rw [hUspan]
  refine Submodule.eq_of_le_of_finrank_eq ((Submodule.span_singleton_le_iff_mem _ _).2 hvW) ?_
  rw [hW1 j, finrank_span_singleton hv0]

theorem map_eq_of_mem_normalizer_cartan (h5 : 5 ≤ p) (hW1 : ∀ i, Module.finrank (ZMod p) (W i) = 1)
    (hWi : iSupIndep W) (hWt : (⨆ i, W i) = ⊤) {g : GL (Fin 3) (ZMod p)}
    (hg : g ∈ normalizer ((UCK.cartanOfDecomp p W : Subgroup (GL (Fin 3) (ZMod p))) :
      Set (GL (Fin 3) (ZMod p)))) (i : Fin 3) :
    ∃ j, (W i).map (Matrix.toLin' (g : Matrix (Fin 3) (Fin 3) (ZMod p))) = W j := by
  refine eq_of_cartan_invariant h5 hW1 hWi hWt ?_ ?_
  · have hinj : Function.Injective (Matrix.toLin' (g : Matrix (Fin 3) (Fin 3) (ZMod p))) := by
      intro u v huv
      have := congrArg (fun t => ((g⁻¹ : GL (Fin 3) (ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)) *ᵥ t)
        huv
      simpa [Matrix.toLin'_apply, Matrix.mulVec_mulVec] using this
    rw [← (Submodule.equivMapOfInjective _ hinj (W i)).finrank_eq, hW1 i]
  · intro d hd u hu
    obtain ⟨v, hv, rfl⟩ := Submodule.mem_map.1 hu
    have hd' : g⁻¹ * d * g⁻¹⁻¹ ∈ UCK.cartanOfDecomp p W :=
      (mem_normalizer_iff.1 (inv_mem hg) d).1 hd
    rw [inv_inv] at hd'
    have hmem : ((g⁻¹ * d * g : GL (Fin 3) (ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)) *ᵥ v ∈ W i :=
      (hd' i v).2 hv
    refine Submodule.mem_map.2 ⟨_, hmem, ?_⟩
    simp [Matrix.toLin'_apply, Matrix.mulVec_mulVec, ← mul_assoc]

end Cartan

theorem fin3_sq_eq_of_pow_four : ∀ π : Fin 3 → Fin 3, Function.Injective π →
    (∀ i, π (π (π (π i))) = i) → ∀ i, π (π i) = i := by decide

theorem fin3_eq_or (i t : Fin 3) : t = i ∨ t = i + 1 ∨ t = i + 2 := by
  revert i t
  decide

theorem fin3_ne (i : Fin 3) : i + 1 ≠ i ∧ i + 2 ≠ i ∧ i + 1 ≠ i + 2 := by
  revert i
  decide

namespace Mz614

variable {G : Type} [Group G] [Finite G] (m : Mz614 G)

section Scalar

variable {y : G} {s : ℕ}

theorem sq_conj_eq_inv (hyB : ∀ b ∈ m.A ⊓ m.L, y * b * y⁻¹ = b ^ s)
    (hs2 : s ^ 2 % m.r = m.r - 1) : ∀ b ∈ m.A ⊓ m.L, y ^ 2 * b * (y ^ 2)⁻¹ = b⁻¹ := by
  intro b hb
  have hbr : b ^ m.r = 1 := m.isElemAbelian_A.2 b hb.1
  have h1 : y ^ 2 * b * (y ^ 2)⁻¹ = b ^ (s ^ 2) := by
    calc y ^ 2 * b * (y ^ 2)⁻¹ = y * (y * b * y⁻¹) * y⁻¹ := by rw [sq, mul_inv_rev]; group
      _ = y * b ^ s * y⁻¹ := by rw [hyB b hb]
      _ = (y * b * y⁻¹) ^ s := (conj_pow).symm
      _ = (b ^ s) ^ s := by rw [hyB b hb]
      _ = b ^ (s ^ 2) := by rw [← pow_mul, sq]
  rw [h1]
  have hord : orderOf b ∣ m.r := orderOf_dvd_of_pow_eq_one hbr
  rw [← pow_mod_orderOf] at hbr ⊢
  have h2 : b ^ (s ^ 2) = b ^ (m.r - 1) := by
    rw [← pow_mod_orderOf b (s ^ 2), ← pow_mod_orderOf b (m.r - 1)]
    congr 1
    have h3 : s ^ 2 % orderOf b = s ^ 2 % m.r % orderOf b := (Nat.mod_mod_of_dvd _ hord).symm
    rw [h3, hs2]
  rw [pow_mod_orderOf, h2]
  have h4 : b ^ (m.r - 1) * b = 1 := by
    rw [← pow_succ, Nat.sub_add_cancel m.hr.one_lt.le]
    exact m.isElemAbelian_A.2 b hb.1
  exact eq_inv_of_mul_eq_one_left h4

theorem sq_mod_ne_one (hs2 : s ^ 2 % m.r = m.r - 1) : s ^ 2 % m.r ≠ 1 := by
  have h3 : 3 ≤ m.r := by
    have := m.hr.two_le
    have := m.d.odd
    omega
  omega

theorem sq_fixed_iff (h620 : m.C620) (h621 : m.C621) (hy : y ∈ m.L ⊓ m.W)
    (hyB : ∀ b ∈ m.A ⊓ m.L, y * b * y⁻¹ = b ^ s) (hs2 : s ^ 2 % m.r = m.r - 1) {a : G}
    (ha : a ∈ m.A) : y ^ 2 * a * (y ^ 2)⁻¹ = a ↔ a ∈ m.Z := by
  have hy2 : y ^ 2 ∈ m.L ⊓ m.W := (m.L ⊓ m.W).pow_mem hy 2
  have hyB2 : ∀ b ∈ m.A ⊓ m.L, y ^ 2 * b * (y ^ 2)⁻¹ = b ^ (s ^ 2) := by
    intro b hb
    calc y ^ 2 * b * (y ^ 2)⁻¹ = y * (y * b * y⁻¹) * y⁻¹ := by rw [sq, mul_inv_rev]; group
      _ = y * b ^ s * y⁻¹ := by rw [hyB b hb]
      _ = (y * b * y⁻¹) ^ s := (conj_pow).symm
      _ = (b ^ s) ^ s := by rw [hyB b hb]
      _ = b ^ (s ^ 2) := by rw [← pow_mul, sq]
  exact (m.scalarTriple h620 h621 hy2 (m.sq_mod_ne_one hs2) hyB2).fixed_iff ha

theorem pow_four_mem_centralizer (h620 : m.C620) (h621 : m.C621) (hy : y ∈ m.L ⊓ m.W)
    (hyB : ∀ b ∈ m.A ⊓ m.L, y * b * y⁻¹ = b ^ s) (hs2 : s ^ 2 % m.r = m.r - 1) :
    y ^ 4 ∈ centralizer (m.A : Set G) := by
  rw [mem_centralizer_iff]
  intro a ha
  obtain ⟨z, hz, b, hb, rfl⟩ :=
    (m.scalarTriple h620 h621 hy (by
      intro h1
      apply m.sq_mod_ne_one hs2
      rw [pow_two, Nat.mul_mod, h1]
      simp [Nat.mod_eq_of_lt m.hr.one_lt]) hyB).exists_mul a ha
  have hz' : y ^ 2 * z * (y ^ 2)⁻¹ = z :=
    (m.sq_fixed_iff h620 h621 hy hyB hs2 (m.Z_le_A hz)).2 hz
  have hb' := m.sq_conj_eq_inv hyB hs2 b hb
  have e : y ^ 4 * (z * b) * (y ^ 4)⁻¹ = z * b := by
    calc y ^ 4 * (z * b) * (y ^ 4)⁻¹
        = y ^ 2 * ((y ^ 2 * z * (y ^ 2)⁻¹) * (y ^ 2 * b * (y ^ 2)⁻¹)) * (y ^ 2)⁻¹ := by group
      _ = y ^ 2 * (z * b⁻¹) * (y ^ 2)⁻¹ := by rw [hz', hb']
      _ = (y ^ 2 * z * (y ^ 2)⁻¹) * (y ^ 2 * b * (y ^ 2)⁻¹)⁻¹ := by group
      _ = z * b := by rw [hz', hb', inv_inv]
  calc z * b * y ^ 4 = (y ^ 4 * (z * b) * (y ^ 4)⁻¹) * y ^ 4 := by rw [e]
    _ = y ^ 4 * (z * b) := by group

theorem mem_of_sq_conj_eq_inv (h620 : m.C620) (h621 : m.C621) (hy : y ∈ m.L ⊓ m.W)
    (hyB : ∀ b ∈ m.A ⊓ m.L, y * b * y⁻¹ = b ^ s) (hs2 : s ^ 2 % m.r = m.r - 1) {a : G}
    (ha : a ∈ m.A) (hinv : y ^ 2 * a * (y ^ 2)⁻¹ = a⁻¹) : a ∈ m.A ⊓ m.L := by
  have hT := m.scalarTriple h620 h621 hy (by
      intro h1
      apply m.sq_mod_ne_one hs2
      rw [pow_two, Nat.mul_mod, h1]
      simp [Nat.mod_eq_of_lt m.hr.one_lt]) hyB
  obtain ⟨z, hz, b, hb, rfl⟩ := hT.exists_mul a ha
  have hz' : y ^ 2 * z * (y ^ 2)⁻¹ = z :=
    (m.sq_fixed_iff h620 h621 hy hyB hs2 (m.Z_le_A hz)).2 hz
  have hb' := m.sq_conj_eq_inv hyB hs2 b hb
  have hzA := m.Z_le_A hz
  have hbA : b ∈ m.A := hb.1
  have e1 : y ^ 2 * (z * b) * (y ^ 2)⁻¹ = z * b⁻¹ := by
    calc y ^ 2 * (z * b) * (y ^ 2)⁻¹ = (y ^ 2 * z * (y ^ 2)⁻¹) * (y ^ 2 * b * (y ^ 2)⁻¹) := by
          group
      _ = z * b⁻¹ := by rw [hz', hb']
  rw [e1] at hinv
  have hc' : b⁻¹ * z⁻¹ = z⁻¹ * b⁻¹ := hT.comm _ (m.A.inv_mem hbA) _ (m.A.inv_mem hzA)
  have h0 : z * b⁻¹ = z⁻¹ * b⁻¹ := by rw [hinv, mul_inv_rev, hc']
  have h1 : z = z⁻¹ := mul_right_cancel h0
  have hz2 : z * z = 1 := by
    calc z * z = z * z⁻¹ := by rw [← h1]
      _ = 1 := mul_inv_cancel z
  have hzr : z ^ m.r = 1 := m.isElemAbelian_A.2 z hzA
  have hz1 : z = 1 := by
    have hodd : Odd m.r := m.hr.odd_of_ne_two m.d.odd
    obtain ⟨k, hk⟩ := hodd
    have h2 : z ^ 2 = 1 := by rw [sq]; exact hz2
    have : z ^ m.r = z := by
      rw [hk, pow_succ, pow_mul, h2, one_pow, one_mul]
    rw [← this, hzr]
  rw [hz1, one_mul]
  exact hb

end Scalar

section Pair

variable [Fact m.r.Prime] (f : Multiplicative (Fin 3 → ZMod m.r) ≃* ↥m.A)

theorem wActionGL_eq_one_iff (w : normalizer (m.A : Set G)) :
    wActionGL f w = 1 ↔ (w : G) ∈ centralizer (m.A : Set G) := by
  rw [CFSG.RankThree.PartOne.LinAlg.wActionGL, MonoidHom.comp_apply,
    ← map_one (CFSG.RankThree.PartOne.LinAlg.coordGL f),
    (CFSG.RankThree.PartOne.LinAlg.coordGL_injective f).eq_iff, ← MonoidHom.mem_ker,
    Subgroup.normalizerMonoidHom_ker, mem_subgroupOf]

theorem map_bsub_conj (w : normalizer (m.A : Set G)) (B : Subgroup G) :
    (bsub f B).map (Matrix.toLin' ((wActionGL f w : GL (Fin 3) (ZMod m.r)) :
        Matrix (Fin 3) (Fin 3) (ZMod m.r))) =
      bsub f (B.map (MulAut.conj (w : G)).toMonoidHom) := by
  ext u
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact (m.mulVec_mem_bsub_conj_iff f w v).2 hv
  · intro hu
    set g := wActionGL f w with hg
    have hgu : ((g : GL (Fin 3) (ZMod m.r)) : Matrix (Fin 3) (Fin 3) (ZMod m.r)) *ᵥ
        (((g⁻¹ : GL (Fin 3) (ZMod m.r)) : Matrix (Fin 3) (Fin 3) (ZMod m.r)) *ᵥ u) = u := by
      rw [Matrix.mulVec_mulVec, ← Matrix.GeneralLinearGroup.coe_mul, mul_inv_cancel,
        Matrix.GeneralLinearGroup.coe_one, Matrix.one_mulVec]
    refine Submodule.mem_map.2 ⟨((g⁻¹ : GL (Fin 3) (ZMod m.r)) :
      Matrix (Fin 3) (Fin 3) (ZMod m.r)) *ᵥ u, ?_, ?_⟩
    · have h := (m.mulVec_mem_bsub_conj_iff f w (B := B)
        (((g⁻¹ : GL (Fin 3) (ZMod m.r)) : Matrix (Fin 3) (Fin 3) (ZMod m.r)) *ᵥ u)).1
      rw [← hg, hgu] at h
      exact h hu
    · rw [Matrix.toLin'_apply]
      exact hgu

theorem bsub_inf (B B' : Subgroup G) : bsub f (B ⊓ B') = bsub f B ⊓ bsub f B' := by
  ext v
  rfl

theorem map_conj_le_A {w : G} (hw : w ∈ m.W) {B : Subgroup G} (hB : B ≤ m.A) :
    B.map (MulAut.conj w).toMonoidHom ≤ m.A := by
  rintro _ ⟨b, hb, rfl⟩
  exact (mem_normalizer_iff.1 hw b).1 (hB hb)

end Pair

theorem exists_pair_of_k322 (hK : UCK.K322) (h69 : R6_9 (dataOfSetup4 m.hS m.hU m.S))
    (h620 : m.C620) (h621 : m.C621) (hr5 : m.r = 5) {y : G} (hy : y ∈ m.L ⊓ m.W) {s : ℕ}
    (hyB : ∀ b ∈ m.A ⊓ m.L, y * b * y⁻¹ = b ^ s) (hs2 : s ^ 2 % m.r = m.r - 1)
    (hne : ¬ m.C623) :
    ∃ Z₂ Z₃ : Subgroup G, Z₂ ≤ m.A ⊓ m.L ∧ Z₃ ≤ m.A ⊓ m.L ∧ Nat.card Z₂ = m.r ∧
      Nat.card Z₃ = m.r ∧ Z₂ ⊓ Z₃ = ⊥ ∧
      (∀ w ∈ m.W, m.Z.map (MulAut.conj w).toMonoidHom = m.Z ∨
        m.Z.map (MulAut.conj w).toMonoidHom = Z₂ ∨ m.Z.map (MulAut.conj w).toMonoidHom = Z₃) ∧
      (∃ w ∈ m.W, m.Z.map (MulAut.conj w).toMonoidHom = Z₂) ∧
      (∃ w ∈ m.W, m.Z.map (MulAut.conj w).toMonoidHom = Z₃) := by
  classical
  haveI : Fact m.r.Prime := ⟨m.hr⟩
  obtain ⟨f⟩ := m.exists_coords_A
  have hs1 : s % m.r ≠ 1 := by
    intro h1
    apply m.sq_mod_ne_one hs2
    rw [pow_two, Nat.mul_mod, h1]
    simp [Nat.mod_eq_of_lt m.hr.one_lt]
  have hirr := m.irredGL3_torusWeylGL f (m.torusIrreducible_A h69 h620 h621 hy hs1 hyB hne)
  have hcard := m.not_dvd_card_torusWeylGL f h69
  have hZ1 := m.finrank_bsub_Z f
  set yW : normalizer (m.A : Set G) := ⟨y, hy.2⟩ with hyW
  set x := wActionGL f yW with hx
  have hxG : x ∈ torusWeylGL f := m.wActionGL_mem f yW
  have hx4 : x ^ 4 = 1 := by
    rw [hx, ← map_pow, m.wActionGL_eq_one_iff]
    simpa [hyW] using m.pow_four_mem_centralizer h620 h621 hy hyB hs2
  have hx2 : ¬ x ^ 2 ^ 1 = 1 := by
    rw [pow_one, hx, ← map_pow, m.wActionGL_eq_one_iff]
    intro hC
    have hAZ : m.A ≤ m.Z := fun a ha => by
      refine (m.sq_fixed_iff h620 h621 hy hyB hs2 ha).1 ?_
      have h1 := mem_centralizer_iff.1 hC a ha
      simp only [hyW, Subgroup.coe_pow] at h1
      rw [← h1]
      group
    have := Subgroup.card_le_of_le hAZ
    rw [m.card_A, m.card_Z] at this
    have h1 := m.hr.one_lt
    have h2 : m.r ^ 1 < m.r ^ 3 := Nat.pow_lt_pow_right h1 (by norm_num)
    rw [pow_one] at h2
    omega
  have hord : orderOf x = 4 := by
    have := orderOf_eq_prime_pow (p := 2) (n := 1) hx2 (by simpa using hx4)
    simpa using this
  have hfix : {v : Fin 3 → ZMod m.r | (((x ^ 2 : GL (Fin 3) (ZMod m.r)) :
      Matrix (Fin 3) (Fin 3) (ZMod m.r)) *ᵥ v = v)} = (bsub f m.Z : Set (Fin 3 → ZMod m.r)) := by
    ext v
    rw [Set.mem_setOf_eq, SetLike.mem_coe, hx, ← map_pow, m.wActionGL_mulVec_eq_iff,
      CFSG.RankThree.PartOne.LinAlg.mem_bsub]
    have h := m.sq_fixed_iff h620 h621 hy hyB hs2 (f (Multiplicative.ofAdd v)).2
    simpa [hyW] using h
  obtain ⟨hcases, -, -⟩ := hK m.r m.d.odd (torusWeylGL f) hirr hcard (bsub f m.Z) hZ1 x hxG
    hord hfix
  rcases hcases with ⟨h7, -⟩ | ⟨h30, -⟩ | ⟨h3, -⟩ | ⟨hncard, Wd, hW1, hWi, hWt, hGN⟩
  · rw [hr5] at h7
    norm_num at h7
  · rw [hr5] at h30
    norm_num at h30
  · rw [hr5] at h3
    norm_num at h3
  have h5 : 5 ≤ m.r := hr5.ge
  have hperm : ∀ g ∈ torusWeylGL f, ∀ i, ∃ j,
      (Wd i).map (Matrix.toLin' (g : Matrix (Fin 3) (Fin 3) (ZMod m.r))) = Wd j :=
    fun g hg i => map_eq_of_mem_normalizer_cartan h5 hW1 hWi hWt (hGN hg) i
  have hWinj := decomp_injective hW1 hWi
  choose π hπ using hperm x hxG
  have hlinj : ∀ g : GL (Fin 3) (ZMod m.r),
      Function.Injective (Matrix.toLin' (g : Matrix (Fin 3) (Fin 3) (ZMod m.r))) := by
    intro g u v huv
    have := congrArg (fun t => ((g⁻¹ : GL (Fin 3) (ZMod m.r)) :
      Matrix (Fin 3) (Fin 3) (ZMod m.r)) *ᵥ t) huv
    simpa [Matrix.toLin'_apply, Matrix.mulVec_mulVec] using this
  have hπinj : Function.Injective π := by
    intro i j h
    apply hWinj
    apply Submodule.map_injective_of_injective (hlinj x)
    rw [hπ, hπ, h]
  have hmul : ∀ (g h : GL (Fin 3) (ZMod m.r)) (U : Submodule (ZMod m.r) (Fin 3 → ZMod m.r)),
      U.map (Matrix.toLin' ((g * h : GL (Fin 3) (ZMod m.r)) : Matrix (Fin 3) (Fin 3) (ZMod m.r))) =
        (U.map (Matrix.toLin' (h : Matrix (Fin 3) (Fin 3) (ZMod m.r)))).map
          (Matrix.toLin' (g : Matrix (Fin 3) (Fin 3) (ZMod m.r))) := by
    intro g h U
    rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.toLin'_mul, Submodule.map_comp]
  have hpow2 : ∀ i, (Wd i).map (Matrix.toLin' ((x ^ 2 : GL (Fin 3) (ZMod m.r)) :
      Matrix (Fin 3) (Fin 3) (ZMod m.r))) = Wd (π (π i)) := by
    intro i
    rw [pow_two, hmul, hπ, hπ]
  have hpow4 : ∀ i, (Wd i).map (Matrix.toLin' ((x ^ 4 : GL (Fin 3) (ZMod m.r)) :
      Matrix (Fin 3) (Fin 3) (ZMod m.r))) = Wd (π (π (π (π i)))) := by
    intro i
    rw [show x ^ 4 = x ^ 2 * x ^ 2 by group, hmul, hpow2, hpow2]
  have hπ4 : ∀ i, π (π (π (π i))) = i := by
    intro i
    apply hWinj
    rw [← hpow4, hx4]
    simp
  have hπ2 := fin3_sq_eq_of_pow_four π hπinj hπ4
  have hx2W : ∀ i, (Wd i).map (Matrix.toLin' ((x ^ 2 : GL (Fin 3) (ZMod m.r)) :
      Matrix (Fin 3) (Fin 3) (ZMod m.r))) = Wd i := fun i => by rw [hpow2, hπ2]
  have hspan : ∀ i, ∃ v ∈ Wd i, v ≠ 0 ∧ Wd i = Submodule.span (ZMod m.r) {v} := by
    intro i
    have hne : Wd i ≠ ⊥ := fun h => by
      have := hW1 i
      rw [h, finrank_bot] at this
      exact zero_ne_one this
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    refine ⟨v, hv, hv0, (Submodule.eq_of_le_of_finrank_eq
      ((Submodule.span_singleton_le_iff_mem _ _).2 hv) ?_).symm⟩
    rw [hW1 i, finrank_span_singleton hv0]
  have hclass : ∀ i, Wd i ≤ bsub f m.Z ∨ Wd i ≤ bsub f (m.A ⊓ m.L) := by
    intro i
    obtain ⟨v, hv, hv0, hsp⟩ := hspan i
    have hx2v : ((x ^ 2 : GL (Fin 3) (ZMod m.r)) : Matrix (Fin 3) (Fin 3) (ZMod m.r)) *ᵥ v ∈
        Wd i := by
      rw [← hx2W i]
      exact Submodule.mem_map_of_mem hv
    rw [hsp] at hx2v
    obtain ⟨μ, hμ⟩ := Submodule.mem_span_singleton.1 hx2v
    have hx4v : ((x ^ 4 : GL (Fin 3) (ZMod m.r)) : Matrix (Fin 3) (Fin 3) (ZMod m.r)) *ᵥ v =
        (μ * μ) • v := by
      rw [show x ^ 4 = x ^ 2 * x ^ 2 by group, Matrix.GeneralLinearGroup.coe_mul,
        ← Matrix.mulVec_mulVec, ← hμ, Matrix.mulVec_smul, ← hμ, smul_smul]
    rw [hx4, Matrix.GeneralLinearGroup.coe_one, Matrix.one_mulVec] at hx4v
    have hμ2 : μ * μ = 1 := by
      have h1 : (μ * μ - 1) • v = 0 := by rw [sub_smul, ← hx4v, one_smul, sub_self]
      rcases smul_eq_zero.1 h1 with h2 | h2
      · exact sub_eq_zero.1 h2
      · exact absurd h2 hv0
    rcases mul_self_eq_one_iff.1 hμ2 with h1 | h1
    · left
      rw [hsp, Submodule.span_singleton_le_iff_mem, ← SetLike.mem_coe, ← hfix]
      show ((x ^ 2 : GL (Fin 3) (ZMod m.r)) : Matrix (Fin 3) (Fin 3) (ZMod m.r)) *ᵥ v = v
      rw [← hμ, h1, one_smul]
    · right
      rw [hsp, Submodule.span_singleton_le_iff_mem, CFSG.RankThree.PartOne.LinAlg.mem_bsub]
      have hneg : ((x ^ 2 : GL (Fin 3) (ZMod m.r)) : Matrix (Fin 3) (Fin 3) (ZMod m.r)) *ᵥ v =
          -v := by
        rw [← hμ, h1, neg_one_smul]
      have h2 := m.coe_f_wActionGL_mulVec f (yW ^ 2) v
      rw [map_pow, ← hx, hneg] at h2
      have h3 : ((f (Multiplicative.ofAdd (-v)) : ↥m.A) : G) =
          ((f (Multiplicative.ofAdd v) : ↥m.A) : G)⁻¹ := by
        rw [ofAdd_neg, map_inv, Subgroup.coe_inv]
      rw [h3] at h2
      refine m.mem_of_sq_conj_eq_inv h620 h621 hy hyB hs2 (f (Multiplicative.ofAdd v)).2 ?_
      simpa [hyW] using h2.symm
  obtain ⟨i₀, hi₀⟩ : ∃ i₀, ¬ Wd i₀ ≤ bsub f (m.A ⊓ m.L) := by
    by_contra hall
    have hle : ∀ i, Wd i ≤ bsub f (m.A ⊓ m.L) := fun i => by
      by_contra h
      exact hall ⟨i, h⟩
    have htop : bsub f (m.A ⊓ m.L) = ⊤ := eq_top_iff.2 (hWt ▸ iSup_le hle)
    have hAL : m.A ⊓ m.L = m.A := (CFSG.RankThree.PartOne.LinAlg.bsub_injective f inf_le_left
      le_rfl).1 (htop.trans (CFSG.RankThree.PartOne.LinAlg.bsub_self f).symm)
    have hc := m.card_A_inf_L h620
    rw [hAL, m.card_A] at hc
    have h1 := m.hr.one_lt
    have : m.r ^ 2 < m.r ^ 3 := Nat.pow_lt_pow_right h1 (by norm_num)
    omega
  have hZW : Wd i₀ = bsub f m.Z := Submodule.eq_of_le_of_finrank_eq ((hclass i₀).resolve_right hi₀)
    (by rw [hW1, hZ1])
  set j := i₀ + 1 with hj
  set k := i₀ + 2 with hk
  have hlineB : ∀ t, t ≠ i₀ → Wd t ≤ bsub f (m.A ⊓ m.L) := by
    intro t ht
    refine (hclass t).resolve_left fun hle => ht (hWinj ?_)
    rw [hZW]
    exact Submodule.eq_of_le_of_finrank_eq hle (by rw [hW1, hZ1])
  have hjk := fin3_ne i₀
  obtain ⟨Z₂, hZ₂A, hbZ₂⟩ := CFSG.RankThree.PartOne.LinAlg.exists_bsub_eq f (Wd j)
  obtain ⟨Z₃, hZ₃A, hbZ₃⟩ := CFSG.RankThree.PartOne.LinAlg.exists_bsub_eq f (Wd k)
  have hcardZ : ∀ (B : Subgroup G) (t : Fin 3), B ≤ m.A → bsub f B = Wd t → Nat.card B = m.r := by
    intro B t hB hbB
    rw [CFSG.RankThree.PartOne.LinAlg.natCard_eq_pow_finrank_bsub f hB, hbB, hW1, pow_one]
  have hZ₂L : Z₂ ≤ m.A ⊓ m.L := (CFSG.RankThree.PartOne.LinAlg.bsub_le_bsub_iff f hZ₂A
    inf_le_left).1 (hbZ₂ ▸ hlineB j hjk.1)
  have hZ₃L : Z₃ ≤ m.A ⊓ m.L := (CFSG.RankThree.PartOne.LinAlg.bsub_le_bsub_iff f hZ₃A
    inf_le_left).1 (hbZ₃ ▸ hlineB k hjk.2.1)
  have hZ₂₃ : Z₂ ⊓ Z₃ = ⊥ := by
    have hdis : Disjoint (Wd j) (Wd k) := hWi.pairwiseDisjoint hjk.2.2
    have h1 : bsub f (Z₂ ⊓ Z₃) = ⊥ := by
      rw [m.bsub_inf f, hbZ₂, hbZ₃]
      exact disjoint_iff.1 hdis
    exact (CFSG.RankThree.PartOne.LinAlg.bsub_injective f (inf_le_left.trans hZ₂A) bot_le).1
      (h1.trans (CFSG.RankThree.PartOne.LinAlg.bsub_bot f).symm)
  have horbit : ∀ w ∈ m.W, ∃ t, bsub f (m.Z.map (MulAut.conj w).toMonoidHom) = Wd t := by
    intro w hw
    obtain ⟨t, ht⟩ := hperm _ (m.wActionGL_mem f ⟨w, hw⟩) i₀
    refine ⟨t, ?_⟩
    rw [← ht, hZW, m.map_bsub_conj f ⟨w, hw⟩ m.Z]
  have hdecide : ∀ (B : Subgroup G), B ≤ m.A → ∀ t : Fin 3, bsub f B = Wd t →
      B = m.Z ∨ B = Z₂ ∨ B = Z₃ := by
    intro B hB t hbt
    rcases fin3_eq_or i₀ t with rfl | rfl | rfl
    · exact Or.inl ((CFSG.RankThree.PartOne.LinAlg.bsub_injective f hB m.Z_le_A).1
        (hbt.trans hZW))
    · exact Or.inr (Or.inl ((CFSG.RankThree.PartOne.LinAlg.bsub_injective f hB hZ₂A).1
        (hbt.trans hbZ₂.symm)))
    · exact Or.inr (Or.inr ((CFSG.RankThree.PartOne.LinAlg.bsub_injective f hB hZ₃A).1
        (hbt.trans hbZ₃.symm)))
  have hS : {U : Submodule (ZMod m.r) (Fin 3 → ZMod m.r) | ∃ g ∈ torusWeylGL f,
      U = (bsub f m.Z).map (Matrix.toLin' (g : Matrix (Fin 3) (Fin 3) (ZMod m.r)))} =
      Set.range Wd := by
    refine Set.eq_of_subset_of_ncard_le ?_ ?_ (Set.toFinite _)
    · rintro U ⟨g, hg, rfl⟩
      obtain ⟨t, ht⟩ := hperm g hg i₀
      exact ⟨t, by rw [← ht, hZW]⟩
    · rw [hncard, Set.ncard_range_of_injective hWinj]
      simp
  have hreach : ∀ t, ∃ w ∈ m.W, bsub f (m.Z.map (MulAut.conj w).toMonoidHom) = Wd t := by
    intro t
    have hmem : Wd t ∈ Set.range Wd := ⟨t, rfl⟩
    rw [← hS] at hmem
    obtain ⟨g, hg, hgt⟩ := hmem
    obtain ⟨w, rfl⟩ := m.exists_of_mem_torusWeylGL f hg
    exact ⟨w, w.2, by rw [← m.map_bsub_conj f w m.Z, hgt]⟩
  refine ⟨Z₂, Z₃, hZ₂L, hZ₃L, hcardZ Z₂ j hZ₂A hbZ₂, hcardZ Z₃ k hZ₃A hbZ₃, hZ₂₃, ?_, ?_, ?_⟩
  · intro w hw
    obtain ⟨t, ht⟩ := horbit w hw
    exact hdecide _ (m.map_conj_le_A hw m.Z_le_A) t ht
  · obtain ⟨w, hw, hwt⟩ := hreach j
    exact ⟨w, hw, (CFSG.RankThree.PartOne.LinAlg.bsub_injective f
      (m.map_conj_le_A hw m.Z_le_A) hZ₂A).1 (hwt.trans hbZ₂.symm)⟩
  · obtain ⟨w, hw, hwt⟩ := hreach k
    exact ⟨w, hw, (CFSG.RankThree.PartOne.LinAlg.bsub_injective f
      (m.map_conj_le_A hw m.Z_le_A) hZ₃A).1 (hwt.trans hbZ₃.symm)⟩

end Mz614

end CFSG.LocalAnalysis.UniquenessCase.UC6
