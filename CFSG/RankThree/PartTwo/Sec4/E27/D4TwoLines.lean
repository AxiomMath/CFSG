module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LieType.SeitzGeneration.HyperPlaneCube
public import CFSG.RankThree.PartTwo.Sec4.Item4Res6ProofL364Hyper

public section

open CFSG.LieType.Seitz CFSG.LieType.SeitzGeneration CFSG.Open

namespace CFSG.RankThree.PartTwo.Sec4.E27

section TwoLines

variable {K : Type} [Group K] [Finite K]

instance finite_mulAut_e27 : Finite (MulAut K) :=
  Finite.of_injective (fun e : MulAut K => (e : K → K)) DFunLike.coe_injective

theorem mem_seitzHyperGamma_of_fixed {E : Subgroup (MulAut K)} (hE : IsElemAbelian 3 E)
    (hcard : Nat.card E = 27) {f x : MulAut K} (hfE : f ∈ E) (hxE : x ∈ E) (hf1 : f ≠ 1)
    (hx : x ∉ Subgroup.zpowers f) {l : K} (hfl : f l = l) (hxl : x l = l) :
    l ∈ seitzHyperGamma 3 E := by
  have hrel : (Subgroup.closure ({f, x} : Set (MulAut K))).relIndex E = 3 :=
    relIndex_closure_pair_of_not_mem Nat.prime_three hE (by rw [hcard]; norm_num) hfE hxE hf1 hx
  have hle : Subgroup.closure ({f, x} : Set (MulAut K)) ≤ E :=
    (Subgroup.closure_le E).2 (Set.insert_subset_iff.2 ⟨hfE, Set.singleton_subset_iff.2 hxE⟩)
  refine CFSG.RankThree.PartTwo.Sec4.Res6L364.fixedPoints_le_seitzHyperGamma hle hrel ?_
  refine CFSG.RankThree.PartTwo.Sec4.Res6L364.mem_fixedPoints_closure ?_
  intro φ hφ
  rcases hφ with rfl | hφ
  · exact hfl
  · rw [Set.mem_singleton_iff.mp hφ]
    exact hxl

theorem le_seitzHyperGamma_of_fixed_line {E : Subgroup (MulAut K)} (hE : IsElemAbelian 3 E)
    (hcard : Nat.card E = 27) {f : MulAut K} (hfE : f ∈ E) (hf1 : f ≠ 1) {L : Subgroup K}
    (hLf : ∀ l ∈ L, f l = l)
    (hL : L ≤ Subgroup.closure {l | l ∈ L ∧ ∃ x ∈ E, x ∉ Subgroup.zpowers f ∧ x l = l}) :
    L ≤ seitzHyperGamma 3 E := by
  refine hL.trans ((Subgroup.closure_le _).2 ?_)
  rintro l ⟨hl, x, hxE, hx, hxl⟩
  exact mem_seitzHyperGamma_of_fixed hE hcard hfE hxE hf1 hx (hLf l hl) hxl

theorem seitzHyperGamma_eq_top_of_two_fixed_lines {E : Subgroup (MulAut K)}
    (hE : IsElemAbelian 3 E) (hcard : Nat.card E = 27) {f₁ f₂ : MulAut K} (hf₁E : f₁ ∈ E)
    (hf₂E : f₂ ∈ E) (hf₁ : f₁ ≠ 1) (hf₂ : f₂ ≠ 1) {L₁ L₂ : Subgroup K}
    (hL₁f : ∀ l ∈ L₁, f₁ l = l) (hL₂f : ∀ l ∈ L₂, f₂ l = l)
    (hL₁ : L₁ ≤ Subgroup.closure {l | l ∈ L₁ ∧ ∃ x ∈ E, x ∉ Subgroup.zpowers f₁ ∧ x l = l})
    (hL₂ : L₂ ≤ Subgroup.closure {l | l ∈ L₂ ∧ ∃ x ∈ E, x ∉ Subgroup.zpowers f₂ ∧ x l = l})
    (hgen : L₁ ⊔ L₂ = ⊤) : seitzHyperGamma 3 E = ⊤ := by
  rw [eq_top_iff, ← hgen]
  exact sup_le (le_seitzHyperGamma_of_fixed_line hE hcard hf₁E hf₁ hL₁f hL₁)
    (le_seitzHyperGamma_of_fixed_line hE hcard hf₂E hf₂ hL₂f hL₂)

end TwoLines

section Conj

variable {K : Type} [Group K]

theorem seitzHyperGamma_eq_top_of_conj (φ : MulAut K) {E : Subgroup (MulAut K)}
    (h : seitzHyperGamma 3 (E.map (MulAut.congr φ).toMonoidHom) = ⊤) :
    seitzHyperGamma 3 E = ⊤ :=
  CFSG.RankThree.PartTwo.Sec4.Res6L364.seitzHyperGamma_eq_top_of_map φ
    (MulAut.congr φ).toMonoidHom (fun a x => by simp [MulAut.congr_apply])
    (MulAut.congr φ).injective h

theorem stepOK_map (φ : MulAut K) {E : Subgroup (MulAut K)} {f : MulAut K} {L : Subgroup K}
    (h : L ≤ Subgroup.closure {l | l ∈ L ∧ ∃ x ∈ E, x ∉ Subgroup.zpowers f ∧ x l = l}) :
    L.map φ.toMonoidHom ≤ Subgroup.closure {l | l ∈ L.map φ.toMonoidHom ∧
      ∃ x ∈ E.map (MulAut.congr φ).toMonoidHom,
        x ∉ Subgroup.zpowers ((MulAut.congr φ) f) ∧ x l = l} := by
  rintro _ ⟨l, hl, rfl⟩
  have h2 : φ l ∈ (Subgroup.closure {l | l ∈ L ∧ ∃ x ∈ E, x ∉ Subgroup.zpowers f ∧ x l = l}).map
      φ.toMonoidHom := ⟨l, h hl, rfl⟩
  rw [MonoidHom.map_closure] at h2
  refine Subgroup.closure_mono ?_ h2
  rintro _ ⟨l', ⟨hl', x, hxE, hx, hxl⟩, rfl⟩
  refine ⟨⟨l', hl', rfl⟩, MulAut.congr φ x, ⟨x, hxE, rfl⟩, ?_, ?_⟩
  · intro hmem
    apply hx
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hmem
    refine Subgroup.mem_zpowers_iff.mpr ⟨j, ?_⟩
    apply (MulAut.congr φ).injective
    rw [map_zpow, hj]
  · have : (MulAut.congr φ x) (φ l') = φ (x l') := by simp [MulAut.congr_apply]
    show (MulAut.congr φ x) (φ l') = φ l'
    rw [this, hxl]

end Conj

section Zpowers

theorem mem_zpowers_cases_of_pow_three {G : Type*} [Group G] {f : G} (hf3 : f ^ 3 = 1) {x : G}
    (hx : x ∈ Subgroup.zpowers f) : x = 1 ∨ x = f ∨ x = f ^ 2 := by
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  have hj : f ^ j = f ^ (j % 3) := by
    have e : j = 3 * (j / 3) + j % 3 := (Int.mul_ediv_add_emod j 3).symm
    conv_lhs => rw [e]
    rw [zpow_add, zpow_mul, show f ^ (3 : ℤ) = 1 by exact_mod_cast hf3, one_zpow, one_mul]
  have h0 : 0 ≤ j % 3 := Int.emod_nonneg _ (by norm_num)
  have h3 : j % 3 < 3 := Int.emod_lt_of_pos _ (by norm_num)
  have hc : j % 3 = 0 ∨ j % 3 = 1 ∨ j % 3 = 2 := by omega
  rw [hj]
  rcases hc with h | h | h <;> rw [h]
  · left; simp
  · right; left; simp
  · right; right; simp

theorem conj_not_mem_zpowers {K : Type*} [Group K]
    (hinj : Function.Injective (MulAut.conj : K →* MulAut K)) {f : MulAut K} (hf3 : f ^ 3 = 1)
    (hf : ∀ g : K, f ≠ MulAut.conj g) {b : K} (hb : b ≠ 1) :
    (MulAut.conj b : MulAut K) ∉ Subgroup.zpowers f := by
  intro hmem
  rcases mem_zpowers_cases_of_pow_three hf3 hmem with h | h | h
  · exact hb (hinj (by rw [h, map_one]))
  · exact hf b h.symm
  · apply hf (b ^ 2)
    have h4 : f = (f ^ 2) ^ 2 := by
      calc f = f ^ 3 * f := by rw [hf3, one_mul]
        _ = (f ^ 2) ^ 2 := by group
    rw [h4, ← h, map_pow]

theorem comm_of_isElemAbelian {G : Type*} [Group G] {p : ℕ} {E : Subgroup G}
    (hE : IsElemAbelian p E) {x y : G} (hx : x ∈ E) (hy : y ∈ E) : x * y = y * x := by
  haveI := hE.1
  have := congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : E) ⟨y, hy⟩)
  simpa using this

theorem isElemAbelian_comap_of_injective {G H : Type*} [Group G] [Group H] {p : ℕ}
    (f : G →* H) (hf : Function.Injective f) {E : Subgroup H} (hE : IsElemAbelian p E) :
    IsElemAbelian p (E.comap f) := by
  refine ⟨⟨⟨fun a b => Subtype.ext (hf ?_)⟩⟩, fun x hx => hf ?_⟩
  · rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
    exact comm_of_isElemAbelian hE a.2 b.2
  · rw [map_pow, map_one]
    exact hE.2 _ hx

end Zpowers

end CFSG.RankThree.PartTwo.Sec4.E27
