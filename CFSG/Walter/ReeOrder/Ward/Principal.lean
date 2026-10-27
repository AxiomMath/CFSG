module

public import CFSG.CharacterTheory.BlockBasics.Sections
public import CFSG.CharacterTheory.PSL2Table.BlocksProduct
public import CFSG.CharacterTheory.PSL2Table.BlocksDefect
public import CFSG.Walter.ReeOrder.Ward.Columns
public import CFSG.Walter.ReeOrder.Ward.Eta

public section

open scoped BigOperators Classical

namespace CFSG.Walter.Ward

open CFSG.SmallDefect CFSG.BlockSectionOrthogonality.Helpers CFSG.DirectProduct
open CFSG.PSL2Table CFSG.TwoRankLowerBound.Helpers

theorem exists_maximal_two : ∃ m : Ideal BlocksAlgInt, m.IsMaximal ∧ (2 : BlocksAlgInt) ∈ m := by
  let : Algebra.IsIntegral ℤ ComplexAlgebraicIntegers := complexAlgebraicIntegers_integral
  let P : Ideal ℤ := Ideal.span {(2 : ℤ)}
  have hPprime : P.IsPrime := (Ideal.span_singleton_prime (by norm_num)).mpr Int.prime_two
  have hPbot : P ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    norm_num
  have hPmax : P.IsMaximal := hPprime.isMaximal hPbot
  have hker : RingHom.ker (algebraMap ℤ ComplexAlgebraicIntegers) ≤ P := by
    intro z hz
    rw [RingHom.mem_ker] at hz
    have hz' : (z : ℂ) = 0 := by
      have := congrArg Subtype.val hz
      simpa using this
    have : z = 0 := by exact_mod_cast hz'
    rw [this]
    exact P.zero_mem
  obtain ⟨Q, hQmax, hQ⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral P hker
  have h2 : ((2 : ℤ) : ComplexAlgebraicIntegers) ∈ Q := by
    have h2P : (2 : ℤ) ∈ P := Ideal.subset_span rfl
    rw [← hQ] at h2P
    simpa using h2P
  exact ⟨Q, hQmax, by simpa using h2⟩

theorem inner_eq_of_odd {L : Type} [Group L] [Fintype L] {F F' Φ : L → ℂ}
    (hF : ∀ y : L, Odd (orderOf y) → F y = F' y) (hΦ : ∀ y : L, Even (orderOf y) → Φ y = 0) :
    BlocksInnerProduct F Φ = BlocksInnerProduct F' Φ := by
  unfold BlocksInnerProduct
  congr 1
  refine Finset.sum_congr rfl fun y _ => ?_
  rcases Nat.even_or_odd (orderOf y) with h | h
  · rw [hΦ y h]
    simp
  · rw [hF y h]

namespace WardSetup

variable {G : Type} [Group G] [Fintype G] {L : Type} [Group L] [Fintype L] {q : ℕ} {e : ℤ}
  {IV : Bool} (S : WardSetup G L q e IV)

@[expose] noncomputable def fP (χ : G → ℂ) : L → ℂ :=
  (S.M χ 1 : ℂ) • (1 : L → ℂ) + (S.M χ S.W.θ2 : ℂ) • S.W.θ2 + (S.M χ S.W.θ3 : ℂ) • S.W.θ3 +
    (S.M χ S.W.θ4 : ℂ) • S.W.θ4

@[expose] noncomputable def T0 : Finset (L → ℂ) := {1, S.W.θ2, S.W.θ3, S.W.θ4}

theorem sum_T0 {M : Type*} [AddCommMonoid M] (f : (L → ℂ) → M) :
    ∑ θ ∈ S.T0, f θ = f 1 + f S.W.θ2 + f S.W.θ3 + f S.W.θ4 := by
  obtain ⟨h12, h13, h14, h23, h24, h34⟩ := S.W.principal_ne
  rw [T0, Finset.sum_insert (by simp [h12, h13, h14]), Finset.sum_insert (by simp [h23, h24]),
    Finset.sum_pair h34]
  abel

theorem T0_mem {θ : L → ℂ} (hθ : θ ∈ S.T0) : θ ∈ BlocksIrr L := by
  simp only [T0, Finset.mem_insert, Finset.mem_singleton] at hθ
  rcases hθ with rfl | rfl | rfl | rfl
  exacts [S.W.one_mem, S.W.θ2_mem, S.W.θ3_mem, S.W.θ4_mem]

theorem fP_apply (χ : G → ℂ) (y : L) :
    S.fP χ y = ∑ θ ∈ S.T0, (S.M χ θ : ℂ) * θ y := by
  rw [sum_T0, fP]
  simp

variable (m : Ideal BlocksAlgInt) [hm : m.IsMaximal]

theorem one_ne_sgn : (1 : Subgroup.zpowers S.J → ℂ) ≠ signChar _ := by
  intro h
  have := congrFun h S.Jz
  rw [S.signChar_Jz] at this
  norm_num at this

theorem principal_C (h2 : (2 : BlocksAlgInt) ∈ m) :
    BlocksPrincipalBlock m (Subgroup.centralizer ({S.J} : Set G)) =
      ↑((({1, signChar _} : Finset (Subgroup.zpowers S.J → ℂ)) ×ˢ S.T0).image
        fun p => S.ψ p.1 p.2) := by
  have hZ := principalBlock_prod_card_two m hm h2 S.card_Z L
  rw [S.W.principal m hm h2] at hZ
  ext ψ'
  simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_product,
    Finset.mem_insert, Finset.mem_singleton, T0, Prod.exists]
  constructor
  · intro h
    have h' : ψ' ∘ S.eC ∈ BlocksPrincipalBlock m (Subgroup.zpowers S.J × L) :=
      (CFSG.BrauerThirdMainTheorem.Helpers.principal_comp_equiv_iff m hm S.eC ψ').mpr h
    rw [hZ] at h'
    obtain ⟨ε, hε, θ, hθ, heq⟩ := h'
    refine ⟨ε, θ, ⟨?_, ?_⟩, ?_⟩
    · simpa using hε
    · simpa using hθ
    · funext x
      have := congrFun heq (S.eC.symm x)
      simp only [Function.comp_apply, MulEquiv.apply_symm_apply] at this
      rw [this]
      rfl
  · rintro ⟨ε, θ, ⟨hε, hθ⟩, rfl⟩
    apply (CFSG.BrauerThirdMainTheorem.Helpers.principal_comp_equiv_iff m hm S.eC.symm
      (outerProductCharacter ε θ)).mpr
    rw [hZ]
    refine ⟨ε, ?_, θ, ?_, rfl⟩
    · simpa using hε
    · simpa using hθ

theorem ψ_injOn : Set.InjOn (fun p : (Subgroup.zpowers S.J → ℂ) × (L → ℂ) => S.ψ p.1 p.2)
    ↑(({1, signChar _} : Finset (Subgroup.zpowers S.J → ℂ)) ×ˢ S.T0) := by
  rintro ⟨ε, θ⟩ h ⟨ε', θ'⟩ h' heq
  simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_insert,
    Finset.mem_singleton] at h h'
  simp only at heq
  have hsgn1 : signChar (Subgroup.zpowers S.J) 1 = 1 := by simp [signChar]
  have hθm := S.T0_mem h.2
  have hθm' := S.T0_mem h'.2
  rcases h.1 with rfl | rfl <;> rcases h'.1 with rfl | rfl
  · rw [S.ψ_inj 1 rfl heq]
  · exact absurd heq (S.ψ_one_ne_sgn hθm hθm')
  · exact absurd heq.symm (S.ψ_one_ne_sgn hθm' hθm)
  · rw [S.ψ_inj _ hsgn1 heq]

theorem local_projection (h2 : (2 : BlocksAlgInt) ∈ m) {χ : G → ℂ} (hχ : χ ∈ BlocksIrr G)
    (y : L) (h : S.J * S.κ y ∈ Subgroup.centralizer ({S.J} : Set G)) :
    (∑ᶠ ψ' ∈ BlocksPrincipalBlock m (Subgroup.centralizer ({S.J} : Set G)),
      BlocksInnerProduct (S.res χ) ψ' • ψ') ⟨S.J * S.κ y, h⟩ = S.fP χ y := by
  rw [S.principal_C m h2, finsum_mem_coe_finset, Finset.sum_apply,
    Finset.sum_image (S.ψ_injOn), Finset.sum_product, Finset.sum_pair (S.one_ne_sgn), fP_apply,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun θ hθ => ?_
  have hθm := S.T0_mem hθ
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [S.inner_res_ψ_one hχ hθm, S.inner_res_ψ_sgn hχ hθm, S.ψ_Jκ, S.ψ_Jκ, S.signChar_Jz,
    Pi.one_apply, M]
  push_cast
  ring

omit hm in
theorem global_projection {χ : G → ℂ} (hχ : χ ∈ BlocksIrr G) (x : G) :
    (∑ᶠ ψ'' ∈ BlocksPrincipalBlock m G, BlocksInnerProduct χ ψ'' • ψ'') x =
      if χ ∈ BlocksPrincipalBlock m G then χ x else 0 := by
  have hsub : BlocksPrincipalBlock m G ⊆ BlocksIrr G := fun ψ hψ => hψ.1
  have hfin : (BlocksPrincipalBlock m G).Finite :=
    (CFSG.BrauerThirdMainTheorem.Helpers.irr_finite G).subset hsub
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin, Finset.sum_apply]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_congr rfl fun ψ hψ => by
    rw [blocksInnerProduct_irr hχ (hsub ((Set.Finite.mem_toFinset hfin).mp hψ))]]
  simp only [ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_eq]
  simp only [Set.Finite.mem_toFinset]

theorem smt (h2 : (2 : BlocksAlgInt) ∈ m) {χ : G → ℂ} (hχ : χ ∈ BlocksIrr G) {y : L}
    (hy : Odd (orderOf y)) :
    S.fP χ y = if χ ∈ BlocksPrincipalBlock m G then S.σ χ y else 0 := by
  have : CharP (BlocksAlgInt ⧸ m) 2 := charP_two m hm h2
  have hclass : BlocksIsClassFunction χ :=
    blocksVChar_isClassFunction (AddSubgroup.subset_closure hχ)
  have hsmt := CFSG.BlockBasics.principal_local_section_projection 2 Nat.prime_two m G S.J
    ⟨1, by rw [S.orderOf_J, pow_one]⟩ χ hclass
  have key : ∀ (C : Subgroup G),
      Subgroup.centralizer (Subgroup.zpowers S.J : Set G) = C → ∀ x : C,
        BlocksIsPPart 2 (x : G) S.J →
        (∑ᶠ ψ' ∈ BlocksPrincipalBlock m C, BlocksInnerProduct (fun x : C => χ x) ψ' • ψ') x =
          (∑ᶠ ψ'' ∈ BlocksPrincipalBlock m G, BlocksInnerProduct χ ψ'' • ψ'') x := by
    intro C hC
    subst hC
    intro x hx
    have := congrFun hsmt x
    simp only [Set.indicator, Set.mem_ofPred_eq, hx, ↓reduceIte] at this
    exact this
  have hx : S.J * S.κ y ∈ Subgroup.centralizer ({S.J} : Set G) :=
    Subgroup.mul_mem _ S.J_mem_centralizer (S.κ_mem_centralizer y)
  have hpart : BlocksIsPPart 2 (S.J * S.κ y) S.J := by
    refine ⟨S.κ y, rfl, (S.κ_comm y), ⟨1, by rw [S.orderOf_J, pow_one]⟩, orderOf_pos _, ?_⟩
    rw [S.orderOf_κ]
    exact Nat.coprime_two_right.mpr hy
  have h := key _ (CFSG.BlockBasics.centralizer_zpowers_eq_centralizer_singleton S.J)
    ⟨S.J * S.κ y, hx⟩ hpart
  have hres : (fun x : Subgroup.centralizer ({S.J} : Set G) => χ x) = S.res χ := rfl
  rw [hres, S.local_projection m h2 hχ y hx, global_projection m hχ] at h
  rw [h]
  rfl

theorem inner_fP_Φ1 (χ : G → ℂ) : BlocksInnerProduct (S.fP χ) S.W.Φ1 = S.d1 χ := by
  obtain ⟨i11, -, -, i14, i21, -, -, i24, i31, -, -, i34, i41, -, -, i44⟩ :=
    S.W.inner_principal
  simp only [fP, WardL.Φ1, blocksInnerProduct_add_left, blocksInnerProduct_smul_left,
    blocksInnerProduct_sub_right, blocksInnerProduct_smul_right, WardL.conj_e, i11, i14, i21,
    i24, i31, i34, i41, i44, d1]
  push_cast
  ring

theorem inner_fP_Φ2 (χ : G → ℂ) : BlocksInnerProduct (S.fP χ) S.W.Φ2 = S.d2 χ := by
  obtain ⟨-, i12, -, i14, -, i22, -, i24, -, i32, -, i34, -, i42, -, i44⟩ :=
    S.W.inner_principal
  simp only [fP, WardL.Φ2, blocksInnerProduct_add_left, blocksInnerProduct_smul_left,
    blocksInnerProduct_add_right, blocksInnerProduct_smul_right, map_neg, WardL.conj_e, i12,
    i14, i22, i24, i32, i34, i42, i44, d2]
  push_cast
  ring

theorem inner_fP_Φ3 (χ : G → ℂ) : BlocksInnerProduct (S.fP χ) S.W.Φ3 = S.d3 χ := by
  obtain ⟨-, -, i13, i14, -, -, i23, i24, -, -, i33, i34, -, -, i43, i44⟩ :=
    S.W.inner_principal
  simp only [fP, WardL.Φ3, blocksInnerProduct_add_left, blocksInnerProduct_smul_left,
    blocksInnerProduct_add_right, blocksInnerProduct_smul_right, map_neg, WardL.conj_e, i13,
    i14, i23, i24, i33, i34, i43, i44, d3]
  push_cast
  ring

theorem inner_fP_other (χ : G → ℂ) {θ : L → ℂ} (hθ : θ ∈ S.W.RFam ∨ θ ∈ S.W.SFam) :
    BlocksInnerProduct (S.fP χ) θ = 0 := by
  obtain ⟨a1, a2, a3, a4, -, -, -, -⟩ := S.W.inner_principal_other hθ
  simp only [fP, blocksInnerProduct_add_left, blocksInnerProduct_smul_left, a1, a2, a3, a4]
  ring

theorem d_zero_of_not_principal (h2 : (2 : BlocksAlgInt) ∈ m) {χ : G → ℂ}
    (hχ : χ ∈ BlocksIrr G) (hB : χ ∉ BlocksPrincipalBlock m G) :
    S.d1 χ = 0 ∧ S.d2 χ = 0 ∧ S.d3 χ = 0 := by
  have hodd : ∀ y : L, Odd (orderOf y) → S.fP χ y = (0 : L → ℂ) y := by
    intro y hy
    rw [S.smt m h2 hχ hy, ite_eq_right hB]
    rfl
  have h1 := inner_eq_of_odd hodd (fun y hy => S.W.Φ1_even hy)
  have h2' := inner_eq_of_odd hodd (fun y hy => S.W.Φ2_even hy)
  have h3 := inner_eq_of_odd hodd (fun y hy => S.W.Φ3_even hy)
  rw [S.inner_fP_Φ1, blocksInnerProduct_zero_left] at h1
  rw [S.inner_fP_Φ2, blocksInnerProduct_zero_left] at h2'
  rw [S.inner_fP_Φ3, blocksInnerProduct_zero_left] at h3
  exact ⟨by exact_mod_cast h1, by exact_mod_cast h2', by exact_mod_cast h3⟩

theorem dRS_zero_of_principal (h2 : (2 : BlocksAlgInt) ∈ m) {χ : G → ℂ}
    (hχ : χ ∈ BlocksIrr G) (hB : χ ∈ BlocksPrincipalBlock m G) :
    (∀ θ ∈ S.W.RFam, S.dR χ θ = 0) ∧ (∀ θ ∈ S.W.SFam, S.dS χ θ = 0) := by
  have hodd : ∀ y : L, Odd (orderOf y) → S.σ χ y = S.fP χ y := by
    intro y hy
    rw [S.smt m h2 hχ hy, ite_eq_left hB]
  refine ⟨fun θ hθ => ?_, fun θ hθ => ?_⟩
  · have h := inner_eq_of_odd hodd (fun y hy => S.W.R_even hθ hy)
    rw [S.inner_ΦR hχ hθ, S.inner_fP_other χ (Or.inl hθ)] at h
    exact_mod_cast h
  · have h := inner_eq_of_odd hodd (fun y hy => S.W.ΦS_even hθ hy)
    rw [S.inner_ΦS hχ hθ, WardL.ΦS, blocksInnerProduct_add_right,
      S.inner_fP_other χ (Or.inr hθ), S.inner_fP_other χ (Or.inr (S.W.sbar_mem θ hθ)),
      add_zero] at h
    exact_mod_cast h

end WardSetup

namespace WardSetup

variable {G : Type} [Group G] [Fintype G] {L : Type} [Group L] [Fintype L] {q : ℕ} {e : ℤ}
  {IV : Bool} (S : WardSetup G L q e IV)

theorem principal_rows {χ : G → ℂ} (hχ : χ ∈ BlocksIrr G)
    (h : S.d1 χ ≠ 0 ∨ S.d2 χ ≠ 0 ∨ S.d3 χ ≠ 0) :
    (∀ θ ∈ S.W.RFam, S.dR χ θ = 0) ∧ (∀ θ ∈ S.W.SFam, S.dS χ θ = 0) := by
  obtain ⟨m, hm, h2⟩ := exists_maximal_two
  have hB : χ ∈ BlocksPrincipalBlock m G := by
    by_contra hB
    obtain ⟨h1, h2', h3⟩ := S.d_zero_of_not_principal m h2 hχ hB
    rcases h with h | h | h <;> contradiction
  exact S.dRS_zero_of_principal m h2 hχ hB

end WardSetup

end CFSG.Walter.Ward
