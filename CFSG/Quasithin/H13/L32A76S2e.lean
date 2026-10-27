module

public import CFSG.LocalAnalysis.ComponentClassification.GHarrisGL3
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.SectionRank.Ccomm.Supercritical

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.L32A.S2.E8

open CFSG.Open


section Lin

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

theorem zmod_two_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by
  revert a
  decide

theorem linIndep_triple {a b c : W} (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b)
    (hc : c ∉ Submodule.span (ZMod 2) {a, b}) : LinearIndependent (ZMod 2) ![a, b, c] := by
  refine Fintype.linearIndependent_iff.2 fun g hg => ?_
  rw [Fin.sum_univ_three] at hg
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons] at hg
  have h2 : g 2 = 0 := by
    rcases zmod_two_cases (g 2) with h | h
    · exact h
    · rw [h, one_smul] at hg
      refine absurd ?_ hc
      rw [eq_neg_of_add_eq_zero_right hg]
      exact neg_mem (Submodule.add_mem _
        (Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_insert a {b})))
        (Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_insert_of_mem a rfl))))
  rw [h2, zero_smul, add_zero] at hg
  have h01 : g 0 = 0 ∧ g 1 = 0 := by
    rcases zmod_two_cases (g 0) with h0 | h0 <;>
      rcases zmod_two_cases (g 1) with h1 | h1
    · exact ⟨h0, h1⟩
    · rw [h0, h1, zero_smul, zero_add, one_smul] at hg
      exact absurd hg hb
    · rw [h0, h1, zero_smul, add_zero, one_smul] at hg
      exact absurd hg ha
    · rw [h0, h1, one_smul, one_smul] at hg
      exact absurd ((eq_neg_of_add_eq_zero_left hg).trans (ZModModule.neg_eq_self b)) hab
  intro i
  fin_cases i
  · exact h01.1
  · exact h01.2
  · exact h2

theorem exists_not_mem_span_two (hW : Module.finrank (ZMod 2) W = 3) (a b : W) :
    ∃ c, c ∉ Submodule.span (ZMod 2) {a, b} := by
  classical
  by_contra! h
  have htop : Submodule.span (ZMod 2) {a, b} = ⊤ := eq_top_iff.2 fun x _ => h x
  have h1 := finrank_span_finset_le_card (R := ZMod 2) ({a, b} : Finset W)
  rw [Finset.coe_insert, Finset.coe_singleton, Set.finrank, htop, finrank_top, hW] at h1
  have h2 : ({a, b} : Finset W).card ≤ 2 := Finset.card_le_two
  omega

theorem exists_linEquiv_apply_eq (hW : Module.finrank (ZMod 2) W = 3) {w w' : W}
    (hw : w ≠ 0) (hw' : w' ≠ 0) : ∃ A : W ≃ₗ[ZMod 2] W, A w = w' := by
  by_cases h : w = w'
  · exact ⟨1, h⟩
  obtain ⟨c, hc⟩ := exists_not_mem_span_two hW w w'
  set e := basisOfLinearIndependentOfCardEqFinrank (linIndep_triple hw hw' h hc)
    (by rw [Fintype.card_fin, hW])
  have h0 : e 0 = w := by rw [coe_basisOfLinearIndependentOfCardEqFinrank]; rfl
  have h1 : e 1 = w' := by rw [coe_basisOfLinearIndependentOfCardEqFinrank]; rfl
  have hf : ∀ i, e.constr (ZMod 2) ![e 1, e 0, e 2] (![e 1, e 0, e 2] i) = e i := by
    intro i
    fin_cases i <;> simp [e.constr_basis]
  let A : W ≃ₗ[ZMod 2] W := LinearEquiv.ofInvolutive (e.constr (ZMod 2) ![e 1, e 0, e 2])
    fun x => by
      have hh : (e.constr (ZMod 2) ![e 1, e 0, e 2]) ∘ₗ (e.constr (ZMod 2) ![e 1, e 0, e 2]) =
          LinearMap.id :=
        e.ext fun i => by rw [LinearMap.comp_apply, e.constr_basis, hf, LinearMap.id_apply]
      exact LinearMap.congr_fun hh x
  refine ⟨A, ?_⟩
  rw [← h0, ← h1]
  exact e.constr_basis (ZMod 2) ![e 1, e 0, e 2] 0

end Lin

variable {G : Type*} [Group G] {A : Subgroup G} [Finite A]

theorem exists_coord (hA : IsElemAbelian 2 A) (h8 : Nat.card A = 8) :
    Nonempty (↥A ≃* Multiplicative (Fin 3 → ZMod 2)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary (W := ↥A) (p := 2) (n := 3)
    (fun a b => hA.1.is_comm.comm a b) (fun a => Subtype.ext (hA.2 a a.2)) (by rw [h8]; norm_num)

theorem card_mulAut (hA : IsElemAbelian 2 A) (h8 : Nat.card A = 8) :
    Nat.card (MulAut ↥A) = 168 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e⟩ := exists_coord hA h8
  rw [CFSG.SectionRank.Ccomm.card_mulAut_eq_card_GL e,
    CFSG.ComponentClassification.GHarris.card_GL32_gh]

theorem isSimpleGroup_mulAut (hA : IsElemAbelian 2 A) (h8 : Nat.card A = 8) :
    IsSimpleGroup (MulAut ↥A) := by
  obtain ⟨e⟩ := CFSG.ComponentClassification.GHarris.nonempty_mulAut_equiv_GL32 hA h8
  have := CFSG.ComponentClassification.GHarris.isSimpleGroup_GL32_gh
  exact e.isSimpleGroup

theorem not_comm (hA : IsElemAbelian 2 A) (h8 : Nat.card A = 8) :
    ¬ ∀ a b : MulAut ↥A, a * b = b * a := by
  intro hc
  have := isSimpleGroup_mulAut hA h8
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (MulAut ↥A) := Nat.finite_of_card_ne_zero (by rw [card_mulAut hA h8]; norm_num)
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := MulAut ↥A) 2
    (by rw [card_mulAut hA h8]; norm_num)
  have hN : (Subgroup.zpowers x).Normal := ⟨fun n hn g => by
    rw [hc g n, mul_inv_cancel_right]
    exact hn⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.zpowers x) with h | h
  · rw [Subgroup.zpowers_eq_bot] at h
    rw [h, orderOf_one] at hx
    norm_num at hx
  · have h1 := Nat.card_zpowers x
    rw [h, Subgroup.card_top, card_mulAut hA h8, hx] at h1
    norm_num at h1

theorem commutator_top (hA : IsElemAbelian 2 A) (h8 : Nat.card A = 8) :
    ⁅(⊤ : Subgroup (MulAut ↥A)), (⊤ : Subgroup (MulAut ↥A))⁆ = ⊤ := by
  have := isSimpleGroup_mulAut hA h8
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
    (⁅(⊤ : Subgroup (MulAut ↥A)), (⊤ : Subgroup (MulAut ↥A))⁆) with h | h
  · exfalso
    apply not_comm hA h8
    intro a b
    have hm := Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
    rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hm
    exact hm
  · exact h

theorem eq_bot_of_isPGroup_of_normal (hA : IsElemAbelian 2 A) (h8 : Nat.card A = 8)
    {N : Subgroup (MulAut ↥A)} (hN : N.Normal) (h2 : IsPGroup 2 N) : N = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := isSimpleGroup_mulAut hA h8
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with h | h
  · exact h
  · exfalso
    obtain ⟨k, hk⟩ := h2.exists_card_eq
    rw [h, Subgroup.card_top, card_mulAut hA h8] at hk
    have h3 : 3 ∣ 2 ^ k := hk ▸ (by norm_num : 3 ∣ 168)
    exact absurd ((Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow h3)) (by norm_num)

theorem exists_mulAut_apply_eq (hA : IsElemAbelian 2 A) (h8 : Nat.card A = 8) {x y : ↥A}
    (hx : x ≠ 1) (hy : y ≠ 1) : ∃ α : MulAut ↥A, α x = y := by
  obtain ⟨e⟩ := exists_coord hA h8
  have hne : ∀ z : ↥A, z ≠ 1 → Multiplicative.toAdd (e z) ≠ 0 := fun z hz h => hz (by
    have h1 : e z = 1 := by rw [← ofAdd_toAdd (e z), h, ofAdd_zero]
    exact e.injective (h1.trans (map_one e).symm))
  obtain ⟨f, hf⟩ := exists_linEquiv_apply_eq (W := Fin 3 → ZMod 2) (by simp) (hne x hx) (hne y hy)
  refine ⟨(e.trans (AddEquiv.toMultiplicative f.toAddEquiv)).trans e.symm, ?_⟩
  simp only [MulEquiv.trans_apply, AddEquiv.toMultiplicative_apply_apply,
    LinearEquiv.coe_toAddEquiv]
  show e.symm (Multiplicative.ofAdd (f (Multiplicative.toAdd (e x)))) = y
  rw [hf, ofAdd_toAdd, MulEquiv.symm_apply_apply]

theorem exists_mulAut_apply_ne (hA : IsElemAbelian 2 A) (h8 : Nat.card A = 8) {x : ↥A}
    (hx : x ≠ 1) : ∃ α : MulAut ↥A, α x ≠ x := by
  classical
  obtain ⟨y, hy1, hyx⟩ : ∃ y : ↥A, y ≠ 1 ∧ y ≠ x := by
    by_contra h
    push Not at h
    have hs : Function.Surjective (fun b : Bool => if b then x else (1 : ↥A)) := fun y => by
      by_cases hy : y = 1
      · exact ⟨false, by simp [hy]⟩
      · exact ⟨true, by simp [h y hy]⟩
    have := Nat.card_le_card_of_surjective _ hs
    rw [h8, Nat.card_eq_fintype_card, Fintype.card_bool] at this
    omega
  obtain ⟨α, hα⟩ := exists_mulAut_apply_eq hA h8 hx hy1
  exact ⟨α, by rw [hα]; exact hyx⟩

theorem eq_top_of_invariant (hA : IsElemAbelian 2 A) (h8 : Nat.card A = 8) {B : Subgroup ↥A}
    (hB : B ≠ ⊥) (hinv : ∀ α : MulAut ↥A, ∀ b ∈ B, α b ∈ B) : B = ⊤ := by
  obtain ⟨⟨b, hb⟩, hb1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hB
  have hb1' : b ≠ 1 := fun h => hb1 (Subtype.ext h)
  rw [eq_top_iff]
  intro y _
  by_cases hy : y = 1
  · rw [hy]
    exact B.one_mem
  obtain ⟨α, hα⟩ := exists_mulAut_apply_eq hA h8 hb1' hy
  rw [← hα]
  exact hinv α b hb

theorem card_le_four (hA : IsElemAbelian 2 A) (h8 : Nat.card A = 8) {v : ↥A} (hv : v ≠ 1)
    {S : Subgroup (MulAut ↥A)} (hS : ∀ α ∈ S, ∀ a : ↥A, α a * a⁻¹ = 1 ∨ α a * a⁻¹ = v) :
    Nat.card S ≤ 4 := by
  classical
  have hsq : ∀ a : ↥A, a * a = 1 := fun a => Subtype.ext (by
    simpa [pow_two] using hA.2 a a.2)
  obtain ⟨e'⟩ := exists_coord hA h8
  set s : Fin 3 → (Fin 3 → ZMod 2) := fun i => Pi.single i 1 with hs
  have hs0 : s 0 ≠ 0 := by
    intro h
    have := congrFun h 0
    simp [hs] at this
  have hv' : e'.symm (Multiplicative.ofAdd (s 0)) ≠ 1 := by
    intro h
    apply hs0
    have h1 := congrArg e' h
    rw [MulEquiv.apply_symm_apply, map_one] at h1
    exact (congrArg Multiplicative.toAdd h1).trans (toAdd_one)
  obtain ⟨α₀, hα₀⟩ := exists_mulAut_apply_eq hA h8 hv hv'
  set e : ↥A ≃* Multiplicative (Fin 3 → ZMod 2) := α₀.trans e' with he
  have hev : Multiplicative.toAdd (e v) = s 0 := by
    rw [he, MulEquiv.trans_apply, hα₀, MulEquiv.apply_symm_apply, toAdd_ofAdd]
  let ψ : MulAut ↥A → ((Fin 3 → ZMod 2) ≃+ (Fin 3 → ZMod 2)) := fun α =>
    AddEquiv.toMultiplicative.symm ((e.symm.trans α).trans e)
  have hψ : ∀ α u, ψ α u = Multiplicative.toAdd (e (α (e.symm (Multiplicative.ofAdd u)))) :=
    fun _ _ => rfl
  have hval : ∀ α ∈ S, ∀ u, ψ α u = u ∨ ψ α u = u + s 0 := by
    intro α hα u
    rw [hψ]
    rcases hS α hα (e.symm (Multiplicative.ofAdd u)) with h | h
    · left
      rw [mul_inv_eq_one.mp h, MulEquiv.apply_symm_apply, toAdd_ofAdd]
    · right
      have h1 : α (e.symm (Multiplicative.ofAdd u)) = v * e.symm (Multiplicative.ofAdd u) :=
        mul_inv_eq_iff_eq_mul.mp h
      rw [h1, map_mul, toAdd_mul, hev, MulEquiv.apply_symm_apply, toAdd_ofAdd, add_comm]
  have hfix : ∀ α ∈ S, ψ α (s 0) = s 0 := by
    intro α hα
    have hαv : α v = v := by
      rcases hS α hα v with h | h
      · exact mul_inv_eq_one.mp h
      · exfalso
        have h1 : α v = v * v := mul_inv_eq_iff_eq_mul.mp h
        rw [hsq v, ← map_one α] at h1
        exact hv (α.injective h1)
    rw [hψ, ← hev, ofAdd_toAdd, MulEquiv.symm_apply_apply, hαv]
  let τ : ↥S → Bool × Bool := fun α => (decide (ψ α (s 1) = s 1), decide (ψ α (s 2) = s 2))
  have hτ : Function.Injective τ := by
    rintro ⟨α, hα⟩ ⟨β, hβ⟩ hαβ
    simp only [τ, Prod.mk.injEq, decide_eq_decide] at hαβ
    have hpair : ∀ i, i ≠ 0 → (ψ α (s i) = s i ↔ ψ β (s i) = s i) → ψ α (s i) = ψ β (s i) := by
      intro i _ hi
      have hs0' : s i + s 0 ≠ s i := fun h => hs0 (by simpa using h)
      rcases hval α hα (s i) with h1 | h1 <;> rcases hval β hβ (s i) with h2 | h2
      · rw [h1, h2]
      · exact absurd (h2 ▸ hi.mp h1) hs0'
      · exact absurd (h1 ▸ hi.mpr h2) hs0'
      · rw [h1, h2]
    have hext : ψ α = ψ β := by
      apply AddEquiv.ext
      have h := AddMonoidHom.functions_ext (Fin 3 → ZMod 2) (ψ α).toAddMonoidHom
        (ψ β).toAddMonoidHom fun i x => by
          rcases zmod_two_cases x with rfl | rfl
          · simp
          · show ψ α (s i) = ψ β (s i)
            rcases (show i = 0 ∨ i = 1 ∨ i = 2 by fin_cases i <;> simp) with rfl | rfl | rfl
            · rw [hfix α hα, hfix β hβ]
            · exact hpair 1 (by decide) hαβ.1
            · exact hpair 2 (by decide) hαβ.2
      exact fun u => DFunLike.congr_fun h u
    apply Subtype.ext
    apply MulEquiv.ext
    intro a
    have h := DFunLike.congr_fun hext (Multiplicative.toAdd (e a))
    rw [hψ, hψ, ofAdd_toAdd, MulEquiv.symm_apply_apply] at h
    exact e.injective (Multiplicative.toAdd.injective h)
  have := Nat.card_le_card_of_injective τ hτ
  simpa using this

end CFSG.Quasithin.H13.L32A.S2.E8

end
