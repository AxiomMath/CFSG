module

public import CFSG.RankThree.PartTwo.Sec21.FF81Sec32

@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81

open CFSG.RankThree.PartTwo.Sec21.FF79
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {b : G} {L : Subgroup G}

theorem FF81Hyp.cubeMulEquiv (h : FF81Hyp b L)
    {b₁ b₂ b₃ : G} (hb₁ : b₁ ∈ L) (hb₂ : b₂ ∈ L) (hb₃ : b₃ ∈ L)
    (hE : IsElemAb 3 3 (Subgroup.closure ({b₁, b₂, b₃} : Set G))) :
    ∃ e : ↥(Subgroup.closure ({b₁, b₂, b₃} : Set G)) ≃*
        Multiplicative (Fin 3 → ZMod 3),
      e ⟨b₁, Subgroup.subset_closure (by simp)⟩ = Multiplicative.ofAdd (Pi.single 0 1) ∧
      e ⟨b₂, Subgroup.subset_closure (by simp)⟩ = Multiplicative.ofAdd (Pi.single 1 1) ∧
      e ⟨b₃, Subgroup.subset_closure (by simp)⟩ = Multiplicative.ofAdd (Pi.single 2 1) := by
  let B : Subgroup G := Subgroup.closure ({b₁, b₂, b₃} : Set G)
  have hB : IsElemAb 3 3 B := hE
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : IsElementaryAbelian 3 ↥B := hB.1
  letI : Module (ZMod 3) (Additive ↥B) := IsElementaryAbelian.isVectorSpace 3
  haveI : Finite (Additive ↥B) := inferInstanceAs (Finite ↥B)
  haveI : Module.Finite (ZMod 3) (Additive ↥B) := Module.Finite.of_finite
  let gen : Fin 3 → ↥B := fun i =>
    match i with
    | 0 => ⟨b₁, Subgroup.subset_closure (by simp)⟩
    | 1 => ⟨b₂, Subgroup.subset_closure (by simp)⟩
    | 2 => ⟨b₃, Subgroup.subset_closure (by simp)⟩
  let v : Fin 3 → Additive ↥B := fun i => Additive.ofMul (gen i)
  have hgen_range : Set.range gen = ((↑) : ↥B → G) ⁻¹' ({b₁, b₂, b₃} : Set G) := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp [gen]
    · intro hx
      simp only [Set.mem_preimage, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with h | h | h
      · exact ⟨0, Subtype.ext h.symm⟩
      · exact ⟨1, Subtype.ext h.symm⟩
      · exact ⟨2, Subtype.ext h.symm⟩
  have htop : Subgroup.closure (Set.range gen) = ⊤ := by
    rw [hgen_range]
    exact Subgroup.closure_closure_coe_preimage
  have hspan : ⊤ ≤ Submodule.span (ZMod 3) (Set.range v) := by
    intro u hu
    clear hu
    obtain ⟨x, rfl⟩ : ∃ y : ↥B, Additive.ofMul y = u := ⟨Additive.toMul u, by simp⟩
    have hx : x ∈ Subgroup.closure (Set.range gen) := by
      rw [htop]
      exact Subgroup.mem_top x
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      simpa [v] using Submodule.subset_span (Set.mem_range_self i)
    | one =>
      exact Submodule.zero_mem (Submodule.span (ZMod 3) (Set.range v))
    | mul y z hy hz ihy ihz =>
      have hsum : Additive.ofMul (y * z) = Additive.ofMul y + Additive.ofMul z := rfl
      rw [hsum]
      exact Submodule.add_mem (Submodule.span (ZMod 3) (Set.range v)) ihy ihz
    | inv y hy ihy =>
      have hneg : Additive.ofMul y⁻¹ = -Additive.ofMul y := rfl
      rw [hneg]
      exact Submodule.neg_mem (Submodule.span (ZMod 3) (Set.range v)) ihy
  have hrank : Module.finrank (ZMod 3) (Additive ↥B) = 3 := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod 3) (V := Additive ↥B)
    have h1 : Nat.card (Additive ↥B) = 3 ^ 3 := hB.2
    rw [h1, Nat.card_zmod] at h
    exact (Nat.pow_right_injective (by norm_num : 2 ≤ 3) h).symm
  have hli : LinearIndependent (ZMod 3) v :=
    linearIndependent_of_top_le_span_of_card_eq_finrank hspan (by rw [hrank]; simp)
  let bs : Module.Basis (Fin 3) (ZMod 3) (Additive ↥B) := Module.Basis.mk hli hspan
  let φ : Additive ↥B ≃ₗ[ZMod 3] (Fin 3 → ZMod 3) := bs.equivFun
  let e : ↥B ≃* Multiplicative (Fin 3 → ZMod 3) :=
    AddEquiv.toMultiplicativeRight φ.toAddEquiv
  have hsingle (i : Fin 3) : e (gen i) = Multiplicative.ofAdd (Pi.single i 1) := by
    change Multiplicative.ofAdd (φ (Additive.ofMul (gen i))) =
      Multiplicative.ofAdd (Pi.single i 1)
    have hi : Additive.ofMul (gen i) = bs i := by simp [bs, v]
    rw [hi]
    congr 1
    funext j
    rw [Module.Basis.equivFun_self]
    simp [Pi.single_apply, eq_comm]
  refine ⟨e, ?_, ?_, ?_⟩
  · simpa [gen] using hsingle 0
  · simpa [gen] using hsingle 1
  · simpa [gen] using hsingle 2

theorem FF81Hyp.B1_irreducible_monomial (h : FF81Hyp b L)
    {b₁ b₂ b₃ : G} (hb₁ : b₁ ∈ L) (hb₂ : b₂ ∈ L) (hb₃ : b₃ ∈ L)
    (hE : IsElemAb 3 3 (Subgroup.closure ({b₁, b₂, b₃} : Set G)))
    {H : Subgroup G} (hHle : H ≤ Subgroup.closure ({b₁, b₂, b₃} : Set G))
    (hHne : H ≠ ⊥)
    {ι₁ ι₂ ι₃ σ₁₂ σ₂₃ γ : G}
    (hι₁ : ι₁ * b₁ * ι₁⁻¹ = b₁⁻¹ ∧ ι₁ * b₂ * ι₁⁻¹ = b₂ ∧ ι₁ * b₃ * ι₁⁻¹ = b₃)
    (hι₂ : ι₂ * b₁ * ι₂⁻¹ = b₁ ∧ ι₂ * b₂ * ι₂⁻¹ = b₂⁻¹ ∧ ι₂ * b₃ * ι₂⁻¹ = b₃)
    (hι₃ : ι₃ * b₁ * ι₃⁻¹ = b₁ ∧ ι₃ * b₂ * ι₃⁻¹ = b₂ ∧ ι₃ * b₃ * ι₃⁻¹ = b₃⁻¹)
    (hσ₁₂ : σ₁₂ * b₁ * σ₁₂⁻¹ = b₂ ∧ σ₁₂ * b₂ * σ₁₂⁻¹ = b₁ ∧ σ₁₂ * b₃ * σ₁₂⁻¹ = b₃)
    (hσ₂₃ : σ₂₃ * b₁ * σ₂₃⁻¹ = b₁ ∧ σ₂₃ * b₂ * σ₂₃⁻¹ = b₃ ∧ σ₂₃ * b₃ * σ₂₃⁻¹ = b₂)
    (hγ : γ * b₁ * γ⁻¹ = b₂ ∧ γ * b₂ * γ⁻¹ = b₃ ∧ γ * b₃ * γ⁻¹ = b₁)
    (hHι₁ : ∀ x ∈ H, ι₁ * x * ι₁⁻¹ ∈ H) (hHι₂ : ∀ x ∈ H, ι₂ * x * ι₂⁻¹ ∈ H)
    (hHι₃ : ∀ x ∈ H, ι₃ * x * ι₃⁻¹ ∈ H)
    (hHσ₁₂ : ∀ x ∈ H, σ₁₂ * x * σ₁₂⁻¹ ∈ H) (hHσ₂₃ : ∀ x ∈ H, σ₂₃ * x * σ₂₃⁻¹ ∈ H)
    (hHγ : ∀ x ∈ H, γ * x * γ⁻¹ ∈ H) :
    H = Subgroup.closure ({b₁, b₂, b₃} : Set G) := by
  let B : Subgroup G := Subgroup.closure ({b₁, b₂, b₃} : Set G)
  obtain ⟨e, hb0, hb1, hb2⟩ := FF81Hyp.cubeMulEquiv h hb₁ hb₂ hb₃ hE
  let gen : Fin 3 → ↥B := fun i =>
    match i with
    | 0 => ⟨b₁, Subgroup.subset_closure (by simp)⟩
    | 1 => ⟨b₂, Subgroup.subset_closure (by simp)⟩
    | 2 => ⟨b₃, Subgroup.subset_closure (by simp)⟩
  have hgen : ∀ i : Fin 3, e (gen i) = Multiplicative.ofAdd (Pi.single i 1) := by
    intro i
    fin_cases i
    · simpa [gen] using hb0
    · simpa [gen] using hb1
    · simpa [gen] using hb2
  have hgen_range : Set.range gen = ((↑) : ↥B → G) ⁻¹' ({b₁, b₂, b₃} : Set G) := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp [gen]
    · intro hx
      simp only [Set.mem_preimage, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with h | h | h
      · exact ⟨0, Subtype.ext h.symm⟩
      · exact ⟨1, Subtype.ext h.symm⟩
      · exact ⟨2, Subtype.ext h.symm⟩
  have htop : Subgroup.closure (Set.range gen) = ⊤ := by
    rw [hgen_range]
    exact Subgroup.closure_closure_coe_preimage
  let flipAdd (i : Fin 3) : (Fin 3 → ZMod 3) →+ (Fin 3 → ZMod 3) :=
    { toFun := fun v j => if j = i then -v j else v j
      map_zero' := by
        funext j
        by_cases hj : j = i
        · subst hj
          simp only [eq_self_iff_true, if_true, Pi.zero_apply]
          exact neg_zero
        · simp [hj]
      map_add' := by
        intro u w
        funext j
        by_cases hj : j = i
        · subst hj
          simp only [eq_self_iff_true, if_true, Pi.add_apply, Pi.neg_apply]
          change -(u j + w j) = -u j + -w j
          calc
            -(u j + w j) = -w j + -u j := neg_add_rev _ _
            _ = -u j + -w j := add_comm _ _
        · simp [hj] }
  let permAdd (σ : Equiv.Perm (Fin 3)) : (Fin 3 → ZMod 3) →+ (Fin 3 → ZMod 3) :=
    { toFun := fun v j => v (σ j)
      map_zero' := rfl
      map_add' := fun u w => rfl }
  have flipAdd_single (i j : Fin 3) :
      flipAdd i (Pi.single j 1) = if j = i then -Pi.single j 1 else Pi.single j 1 := by
    by_cases hji : j = i
    · subst hji
      funext k
      by_cases hk : k = j
      · simp [flipAdd, hk]
      · simp [flipAdd, hk, Pi.single_eq_of_ne hk]
        exact neg_zero.symm
    · funext k
      by_cases hk : k = i
      · subst hk
        simp [flipAdd, Pi.single_eq_of_ne (Ne.symm hji), hji]
        exact neg_zero
      · simp [flipAdd, hk, Pi.single_apply, hji]
  have permAdd_single (σ : Equiv.Perm (Fin 3)) (j : Fin 3) :
      permAdd σ (Pi.single j 1) = Pi.single (σ.symm j) 1 := by
    funext k
    simp [permAdd, Pi.single_apply, Equiv.eq_symm_apply]
  let Kadd : AddSubgroup (Fin 3 → ZMod 3) :=
    { carrier := {u | ∃ x : ↥B, (x : G) ∈ H ∧ e x = Multiplicative.ofAdd u}
      zero_mem' := by
        refine ⟨1, H.one_mem, ?_⟩
        simp
      add_mem' := by
        rintro u v ⟨x, hxH, hxe⟩ ⟨y, hyH, hye⟩
        refine ⟨x * y, H.mul_mem hxH hyH, ?_⟩
        rw [map_mul, hxe, hye]
        rfl
      neg_mem' := by
        rintro u ⟨x, hxH, hxe⟩
        refine ⟨x⁻¹, H.inv_mem hxH, ?_⟩
        rw [map_inv, hxe]
        rfl }
  have hsmul_Kadd : ∀ (c : ZMod 3) {u : Fin 3 → ZMod 3}, u ∈ Kadd → c • u ∈ Kadd := by
    intro c u hu
    have h : c • u = c.val • u := by
      funext i
      change c • u i = c.val • u i
      rw [← Nat.cast_smul_eq_nsmul (ZMod 3) c.val (u i), ZMod.natCast_zmod_val]
    rw [h]
    exact Kadd.nsmul_mem hu c.val
  have memK_iff : ∀ {u : Fin 3 → ZMod 3},
      u ∈ Kadd ↔ ∃ x : ↥B, (x : G) ∈ H ∧ e x = Multiplicative.ofAdd u := by
    intro u
    rfl
  let conjAut (g : G) (hgN : g ∈ Nor B) : MulAut ↥B :=
    Subgroup.normalizerMonoidHom (H := B) ⟨g, hgN⟩
  have conjAut_coe {g : G} (hgN : g ∈ Nor B) (x : ↥B) :
      ((conjAut g hgN x : ↥B) : G) = g * (x : G) * g⁻¹ := by
    change ((Subgroup.normalizerMonoidHom (H := B) ⟨g, hgN⟩) x : G) = g * (x : G) * g⁻¹
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
  have conj_eq {g : G} (hgN : g ∈ Nor B) (c : (Fin 3 → ZMod 3) →+ (Fin 3 → ZMod 3))
      (hc : ∀ j : Fin 3, c (Multiplicative.toAdd (e (gen j))) =
        Multiplicative.toAdd (e (conjAut g hgN (gen j)))) :
      ∀ x : ↥B, c (Multiplicative.toAdd (e x)) =
        Multiplicative.toAdd (e (conjAut g hgN x)) := by
    let F : ↥B →* Multiplicative (Fin 3 → ZMod 3) :=
      e.toMonoidHom.comp (conjAut g hgN).toMonoidHom
    let G' : ↥B →* Multiplicative (Fin 3 → ZMod 3) :=
      (c.toMultiplicative).comp e.toMonoidHom
    have hFG : F = G' := by
      have hEqOn : Set.EqOn F G' (Set.range gen) := by
        rintro y ⟨j, rfl⟩
        simpa [F, G', AddMonoidHom.coe_toMultiplicative] using
          congrArg Multiplicative.ofAdd (hc j).symm
      have h := MonoidHom.eqOn_closure hEqOn
      apply MonoidHom.ext
      intro x
      exact h (by rw [htop]; exact Subgroup.mem_top x)
    intro x
    have hx := congrArg (fun f : ↥B →* Multiplicative (Fin 3 → ZMod 3) => f x) hFG
    simpa [F, G', AddMonoidHom.coe_toMultiplicative] using
      (congrArg Multiplicative.toAdd hx).symm
  have hι₁N : ι₁ ∈ Nor B := by
    refine mem_nor_of_gen ?_
    intro x hx
    rcases hx with rfl | rfl | rfl
    · rw [hι₁.1]; exact B.inv_mem (Subgroup.subset_closure (by simp))
    · rw [hι₁.2.1]; exact Subgroup.subset_closure (by simp)
    · rw [hι₁.2.2]; exact Subgroup.subset_closure (by simp)
  have hι₂N : ι₂ ∈ Nor B := by
    refine mem_nor_of_gen ?_
    intro x hx
    rcases hx with rfl | rfl | rfl
    · rw [hι₂.1]; exact Subgroup.subset_closure (by simp)
    · rw [hι₂.2.1]; exact B.inv_mem (Subgroup.subset_closure (by simp))
    · rw [hι₂.2.2]; exact Subgroup.subset_closure (by simp)
  have hι₃N : ι₃ ∈ Nor B := by
    refine mem_nor_of_gen ?_
    intro x hx
    rcases hx with rfl | rfl | rfl
    · rw [hι₃.1]; exact Subgroup.subset_closure (by simp)
    · rw [hι₃.2.1]; exact Subgroup.subset_closure (by simp)
    · rw [hι₃.2.2]; exact B.inv_mem (Subgroup.subset_closure (by simp))
  have hσ₁₂N : σ₁₂ ∈ Nor B := by
    refine mem_nor_of_gen ?_
    intro x hx
    rcases hx with rfl | rfl | rfl
    · rw [hσ₁₂.1]; exact Subgroup.subset_closure (by simp)
    · rw [hσ₁₂.2.1]; exact Subgroup.subset_closure (by simp)
    · rw [hσ₁₂.2.2]; exact Subgroup.subset_closure (by simp)
  have hσ₂₃N : σ₂₃ ∈ Nor B := by
    refine mem_nor_of_gen ?_
    intro x hx
    rcases hx with rfl | rfl | rfl
    · rw [hσ₂₃.1]; exact Subgroup.subset_closure (by simp)
    · rw [hσ₂₃.2.1]; exact Subgroup.subset_closure (by simp)
    · rw [hσ₂₃.2.2]; exact Subgroup.subset_closure (by simp)
  have hι₁acts : ∀ j : Fin 3,
      flipAdd 0 (Multiplicative.toAdd (e (gen j))) =
        Multiplicative.toAdd (e (conjAut ι₁ hι₁N (gen j))) := by
    intro j
    fin_cases j
    · have hconj : conjAut ι₁ hι₁N (gen 0) = (gen 0)⁻¹ := by
        apply Subtype.ext
        rw [conjAut_coe]
        simpa [gen] using hι₁.1
      rw [hconj, map_inv, hgen 0]
      simp [flipAdd_single]
    · have hconj : conjAut ι₁ hι₁N (gen 1) = gen 1 := by
        apply Subtype.ext
        rw [conjAut_coe]
        simpa [gen] using hι₁.2.1
      rw [hconj, hgen 1]
      simp [flipAdd_single]
    · have hconj : conjAut ι₁ hι₁N (gen 2) = gen 2 := by
        apply Subtype.ext
        rw [conjAut_coe]
        simpa [gen] using hι₁.2.2
      rw [hconj, hgen 2]
      simp [flipAdd_single]
  have hι₂acts : ∀ j : Fin 3,
      flipAdd 1 (Multiplicative.toAdd (e (gen j))) =
        Multiplicative.toAdd (e (conjAut ι₂ hι₂N (gen j))) := by
    intro j
    fin_cases j
    · have hconj : conjAut ι₂ hι₂N (gen 0) = gen 0 := by
        apply Subtype.ext
        rw [conjAut_coe]
        simpa [gen] using hι₂.1
      rw [hconj, hgen 0]
      simp [flipAdd_single]
    · have hconj : conjAut ι₂ hι₂N (gen 1) = (gen 1)⁻¹ := by
        apply Subtype.ext
        rw [conjAut_coe]
        simpa [gen] using hι₂.2.1
      rw [hconj, map_inv, hgen 1]
      simp [flipAdd_single]
    · have hconj : conjAut ι₂ hι₂N (gen 2) = gen 2 := by
        apply Subtype.ext
        rw [conjAut_coe]
        simpa [gen] using hι₂.2.2
      rw [hconj, hgen 2]
      simp [flipAdd_single]
  have hι₃acts : ∀ j : Fin 3,
      flipAdd 2 (Multiplicative.toAdd (e (gen j))) =
        Multiplicative.toAdd (e (conjAut ι₃ hι₃N (gen j))) := by
    intro j
    fin_cases j
    · have hconj : conjAut ι₃ hι₃N (gen 0) = gen 0 := by
        apply Subtype.ext
        rw [conjAut_coe]
        simpa [gen] using hι₃.1
      rw [hconj, hgen 0]
      simp [flipAdd_single]
    · have hconj : conjAut ι₃ hι₃N (gen 1) = gen 1 := by
        apply Subtype.ext
        rw [conjAut_coe]
        simpa [gen] using hι₃.2.1
      rw [hconj, hgen 1]
      simp [flipAdd_single]
    · have hconj : conjAut ι₃ hι₃N (gen 2) = (gen 2)⁻¹ := by
        apply Subtype.ext
        rw [conjAut_coe]
        simpa [gen] using hι₃.2.2
      rw [hconj, map_inv, hgen 2]
      simp [flipAdd_single]
  have hσ₁₂acts : ∀ j : Fin 3,
      permAdd (Equiv.swap 0 1) (Multiplicative.toAdd (e (gen j))) =
        Multiplicative.toAdd (e (conjAut σ₁₂ hσ₁₂N (gen j))) := by
    intro j
    fin_cases j
    · have hconj : conjAut σ₁₂ hσ₁₂N (gen 0) = gen 1 := by
        apply Subtype.ext
        rw [conjAut_coe]
        simpa [gen] using hσ₁₂.1
      have hidx : (Equiv.swap 0 1) (0 : Fin 3) = 1 := by decide
      rw [hconj, hgen 0, hgen 1]
      simp [permAdd_single, hidx, toAdd_ofAdd]
    · have hconj : conjAut σ₁₂ hσ₁₂N (gen 1) = gen 0 := by
        apply Subtype.ext
        rw [conjAut_coe]
        simpa [gen] using hσ₁₂.2.1
      have hidx : (Equiv.swap 0 1) (1 : Fin 3) = 0 := by decide
      rw [hconj, hgen 0, hgen 1]
      simp [permAdd_single, hidx, toAdd_ofAdd]
    · have hconj : conjAut σ₁₂ hσ₁₂N (gen 2) = gen 2 := by
        apply Subtype.ext
        rw [conjAut_coe]
        simpa [gen] using hσ₁₂.2.2
      have hidx : (Equiv.swap 0 1) (2 : Fin 3) = 2 := by decide
      rw [hconj, hgen 2]
      simp [permAdd_single, hidx, toAdd_ofAdd]
  have hσ₂₃acts : ∀ j : Fin 3,
      permAdd (Equiv.swap 1 2) (Multiplicative.toAdd (e (gen j))) =
        Multiplicative.toAdd (e (conjAut σ₂₃ hσ₂₃N (gen j))) := by
    intro j
    fin_cases j
    · have hconj : conjAut σ₂₃ hσ₂₃N (gen 0) = gen 0 := by
        apply Subtype.ext
        rw [conjAut_coe]
        simpa [gen] using hσ₂₃.1
      have hidx : (Equiv.swap 1 2) (0 : Fin 3) = 0 := by decide
      rw [hconj, hgen 0]
      simp [permAdd_single, hidx, toAdd_ofAdd]
    · have hconj : conjAut σ₂₃ hσ₂₃N (gen 1) = gen 2 := by
        apply Subtype.ext
        rw [conjAut_coe]
        simpa [gen] using hσ₂₃.2.1
      have hidx : (Equiv.swap 1 2) (1 : Fin 3) = 2 := by decide
      rw [hconj, hgen 1, hgen 2]
      simp [permAdd_single, hidx, toAdd_ofAdd]
    · have hconj : conjAut σ₂₃ hσ₂₃N (gen 2) = gen 1 := by
        apply Subtype.ext
        rw [conjAut_coe]
        simpa [gen] using hσ₂₃.2.2
      have hidx : (Equiv.swap 1 2) (2 : Fin 3) = 1 := by decide
      rw [hconj, hgen 1, hgen 2]
      simp [permAdd_single, hidx, toAdd_ofAdd]
  have hι₁conj := conj_eq hι₁N (flipAdd 0) hι₁acts
  have hι₂conj := conj_eq hι₂N (flipAdd 1) hι₂acts
  have hι₃conj := conj_eq hι₃N (flipAdd 2) hι₃acts
  have hσ₁₂conj := conj_eq hσ₁₂N (permAdd (Equiv.swap 0 1)) hσ₁₂acts
  have hσ₂₃conj := conj_eq hσ₂₃N (permAdd (Equiv.swap 1 2)) hσ₂₃acts
  have hιKadd : ∀ i : Fin 3, ∀ u ∈ Kadd, flipAdd i u ∈ Kadd := by
    intro i
    fin_cases i
    · intro u hu
      obtain ⟨x, hxH, hxe⟩ := memK_iff.mp hu
      refine memK_iff.mpr ⟨conjAut ι₁ hι₁N x, ?_, ?_⟩
      · simpa [conjAut_coe] using hHι₁ x hxH
      · rw [← ofAdd_toAdd (e (conjAut ι₁ hι₁N x)), ← hι₁conj x, hxe]
        simp
    · intro u hu
      obtain ⟨x, hxH, hxe⟩ := memK_iff.mp hu
      refine memK_iff.mpr ⟨conjAut ι₂ hι₂N x, ?_, ?_⟩
      · simpa [conjAut_coe] using hHι₂ x hxH
      · rw [← ofAdd_toAdd (e (conjAut ι₂ hι₂N x)), ← hι₂conj x, hxe]
        simp
    · intro u hu
      obtain ⟨x, hxH, hxe⟩ := memK_iff.mp hu
      refine memK_iff.mpr ⟨conjAut ι₃ hι₃N x, ?_, ?_⟩
      · simpa [conjAut_coe] using hHι₃ x hxH
      · rw [← ofAdd_toAdd (e (conjAut ι₃ hι₃N x)), ← hι₃conj x, hxe]
        simp
  have hσ₁₂Kadd : ∀ u ∈ Kadd, permAdd (Equiv.swap 0 1) u ∈ Kadd := by
    intro u hu
    obtain ⟨x, hxH, hxe⟩ := memK_iff.mp hu
    refine memK_iff.mpr ⟨conjAut σ₁₂ hσ₁₂N x, ?_, ?_⟩
    · simpa [conjAut_coe] using hHσ₁₂ x hxH
    · rw [← ofAdd_toAdd (e (conjAut σ₁₂ hσ₁₂N x)), ← hσ₁₂conj x, hxe]
      simp
  have hσ₂₃Kadd : ∀ u ∈ Kadd, permAdd (Equiv.swap 1 2) u ∈ Kadd := by
    intro u hu
    obtain ⟨x, hxH, hxe⟩ := memK_iff.mp hu
    refine memK_iff.mpr ⟨conjAut σ₂₃ hσ₂₃N x, ?_, ?_⟩
    · simpa [conjAut_coe] using hHσ₂₃ x hxH
    · rw [← ofAdd_toAdd (e (conjAut σ₂₃ hσ₂₃N x)), ← hσ₂₃conj x, hxe]
      simp
  obtain ⟨xH, hxHne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hHne
  let x : G := xH
  have hxH : x ∈ H := xH.2
  have hxB : x ∈ B := hHle hxH
  let xB : ↥B := ⟨x, hxB⟩
  have hxBne : xB ≠ 1 := by
    intro hx1
    apply hxHne
    apply Subtype.ext
    exact congrArg (fun y : ↥B => (y : G)) hx1
  let v : Fin 3 → ZMod 3 := Multiplicative.toAdd (e xB)
  have hv0 : v ≠ 0 := by
    intro hv
    apply hxBne
    apply e.injective
    change Multiplicative.ofAdd v = e 1
    rw [hv]
    simp
  have hvK : v ∈ Kadd := by
    refine memK_iff.mpr ⟨xB, hxH, ?_⟩
    simp [v]
  obtain ⟨i, hi⟩ : ∃ i : Fin 3, v i ≠ 0 := by
    by_contra h
    apply hv0
    funext j
    by_contra hj
    exact h ⟨j, hj⟩
  have hflipK : flipAdd i v ∈ Kadd := hιKadd i v hvK
  have hdiff : v - flipAdd i v = (2 * v i) • Pi.single i 1 := by
    funext k
    by_cases hk : k = i
    · rw [hk]
      simp [flipAdd]
      exact (sub_neg_eq_add (v i) (v i)).trans (two_mul (v i)).symm
    · simp [flipAdd, hk, Pi.single_eq_of_ne hk]
  have hmem : (2 * v i) • Pi.single i 1 ∈ Kadd := by
    rw [← hdiff]
    exact Kadd.sub_mem hvK hflipK
  have hcoef : (2 * v i : ZMod 3) ≠ 0 := by
    intro hc
    rcases mul_eq_zero.mp hc with h2 | hvi
    · exact (by decide : (2 : ZMod 3) ≠ 0) h2
    · exact hi hvi
  have hsingle : Pi.single i 1 ∈ Kadd := by
    have h := hsmul_Kadd ((2 * v i)⁻¹) hmem
    rwa [smul_smul, inv_mul_cancel₀ hcoef, one_smul] at h
  have hsingle_all : ∀ j : Fin 3, Pi.single j 1 ∈ Kadd := by
    fin_cases i
    · have h01 : Pi.single 1 1 ∈ Kadd := by
        have h := hσ₁₂Kadd _ hsingle
        rw [permAdd_single] at h
        have hidx : (Equiv.swap 0 1) (0 : Fin 3) = 1 := by decide
        simpa [hidx, Fin.mk_zero'] using h
      have h02 : Pi.single 2 1 ∈ Kadd := by
        have h := hσ₂₃Kadd _ h01
        rw [permAdd_single] at h
        have hidx : (Equiv.swap 1 2) (1 : Fin 3) = 2 := by decide
        simpa [hidx, Fin.mk_zero'] using h
      intro j
      fin_cases j
      · exact hsingle
      · exact h01
      · exact h02
    · have h10 : Pi.single 0 1 ∈ Kadd := by
        have h := hσ₁₂Kadd _ hsingle
        rw [permAdd_single] at h
        have hidx : (Equiv.swap 0 1) (1 : Fin 3) = 0 := by decide
        simpa [hidx, Fin.mk_zero'] using h
      have h12 : Pi.single 2 1 ∈ Kadd := by
        have h := hσ₂₃Kadd _ hsingle
        rw [permAdd_single] at h
        have hidx : (Equiv.swap 1 2) (1 : Fin 3) = 2 := by decide
        simpa [hidx, Fin.mk_zero'] using h
      intro j
      fin_cases j
      · exact h10
      · exact hsingle
      · exact h12
    · have h21 : Pi.single 1 1 ∈ Kadd := by
        have h := hσ₂₃Kadd _ hsingle
        rw [permAdd_single] at h
        have hidx : (Equiv.swap 1 2) (2 : Fin 3) = 1 := by decide
        simpa [hidx, Fin.mk_zero'] using h
      have h20 : Pi.single 0 1 ∈ Kadd := by
        have h := hσ₁₂Kadd _ h21
        rw [permAdd_single] at h
        have hidx : (Equiv.swap 0 1) (1 : Fin 3) = 0 := by decide
        simpa [hidx, Fin.mk_zero'] using h
      intro j
      fin_cases j
      · exact h20
      · exact h21
      · exact hsingle
  have hKtop : Kadd = ⊤ := by
    rw [AddSubgroup.eq_top_iff']
    intro u
    have hu : u = ∑ j, u j • Pi.single j 1 := by
      funext k
      rw [Finset.sum_apply]
      rw [Finset.sum_eq_single k
        (fun j _ hjk => by simp [Pi.single_eq_of_ne hjk.symm])
        (fun hk => absurd (Finset.mem_univ k) hk)]
      simp
    rw [hu]
    exact AddSubgroup.sum_mem Kadd fun j _ => hsmul_Kadd (u j) (hsingle_all j)
  refine le_antisymm hHle ?_
  intro y hyB
  let yB : ↥B := ⟨y, hyB⟩
  have hmem : Multiplicative.toAdd (e yB) ∈ Kadd := by
    rw [hKtop]
    exact AddSubgroup.mem_top _
  obtain ⟨z, hzH, hze⟩ := memK_iff.mp hmem
  have hzy : z = yB := by
    apply e.injective
    simpa using hze
  have hyH : (y : G) ∈ H := by
    have h := hzH
    rw [hzy] at h
    simpa using h
  exact hyH

end CFSG.RankThree.PartTwo.Sec21.FF81
