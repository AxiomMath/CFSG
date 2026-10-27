module

public import CFSG.LieType.Seitz.Defs
public import CFSG.Assembly.Defs

public section

namespace CFSG.RankThree.PartTwo.Sec4.Res6L364

open CFSG.LieType.Seitz

theorem mem_fixedPoints_closure {X : Type*} [Group X] {s : Set (MulAut X)} {x : X}
    (h : ∀ φ ∈ s, φ x = x) : x ∈ fixedPoints (Subgroup.closure s) := by
  intro φ hφ
  have hle : Subgroup.closure s ≤ MulAction.stabilizer (MulAut X) x :=
    (Subgroup.closure_le _).mpr fun ψ hψ => by
      rw [SetLike.mem_coe, MulAction.mem_stabilizer_iff]
      exact h ψ hψ
  exact MulAction.mem_stabilizer_iff.mp (hle hφ)

theorem fixedPoints_le_seitzHyperGamma {X : Type*} [Group X] {p : ℕ}
    {E F : Subgroup (MulAut X)} (hFE : F ≤ E) (hF : F.relIndex E = p) :
    fixedPoints F ≤ seitzHyperGamma p E :=
  le_iSup₂_of_le F ⟨hFE, hF⟩ le_rfl

theorem exists_pow_mul_pow_of_mem_closure {G : Type*} [Group G] {a b : G} (hab : a * b = b * a)
    (ha : a ^ 3 = 1) (hb : b ^ 3 = 1) {x : G} (hx : x ∈ Subgroup.closure {a, b}) :
    ∃ i j : Fin 3, x = a ^ (i : ℕ) * b ^ (j : ℕ) := by
  have hc : Commute a b := hab
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | rfl
    · exact ⟨1, 0, by simp⟩
    · exact ⟨0, 1, by simp⟩
  | one => exact ⟨0, 0, by simp⟩
  | mul x y _ _ hx hy =>
    obtain ⟨i, j, rfl⟩ := hx
    obtain ⟨k, l, rfl⟩ := hy
    refine ⟨⟨((i : ℕ) + k) % 3, Nat.mod_lt _ (by norm_num)⟩,
      ⟨((j : ℕ) + l) % 3, Nat.mod_lt _ (by norm_num)⟩, ?_⟩
    simp only
    rw [← pow_eq_pow_mod _ ha, ← pow_eq_pow_mod _ hb, pow_add, pow_add]
    have h1 : b ^ (j : ℕ) * a ^ (k : ℕ) = a ^ (k : ℕ) * b ^ (j : ℕ) :=
      ((hc.pow_pow (k : ℕ) (j : ℕ)).eq).symm
    calc a ^ (i : ℕ) * b ^ (j : ℕ) * (a ^ (k : ℕ) * b ^ (l : ℕ))
        = a ^ (i : ℕ) * (b ^ (j : ℕ) * a ^ (k : ℕ)) * b ^ (l : ℕ) := by group
      _ = a ^ (i : ℕ) * (a ^ (k : ℕ) * b ^ (j : ℕ)) * b ^ (l : ℕ) := by rw [h1]
      _ = a ^ (i : ℕ) * a ^ (k : ℕ) * (b ^ (j : ℕ) * b ^ (l : ℕ)) := by group
  | inv x _ hx =>
    obtain ⟨i, j, rfl⟩ := hx
    refine ⟨⟨(2 * (i : ℕ)) % 3, Nat.mod_lt _ (by norm_num)⟩,
      ⟨(2 * (j : ℕ)) % 3, Nat.mod_lt _ (by norm_num)⟩, ?_⟩
    simp only
    rw [← pow_eq_pow_mod _ ha, ← pow_eq_pow_mod _ hb]
    have hai : (a ^ (i : ℕ))⁻¹ = a ^ (2 * (i : ℕ)) := by
      rw [eq_comm, ← mul_eq_one_iff_eq_inv, ← pow_add,
        show 2 * (i : ℕ) + i = 3 * i by ring, pow_mul, ha, one_pow]
    have hbj : (b ^ (j : ℕ))⁻¹ = b ^ (2 * (j : ℕ)) := by
      rw [eq_comm, ← mul_eq_one_iff_eq_inv, ← pow_add,
        show 2 * (j : ℕ) + j = 3 * j by ring, pow_mul, hb, one_pow]
    rw [mul_inv_rev, hai, hbj]
    exact ((hc.pow_pow _ _).eq).symm

theorem card_closure_pair {G : Type*} [Group G] {E : Subgroup G}
    (hE : CFSG.Assembly.IsElemAbelian 3 E) (h27 : Nat.card E = 27) {a b : G} (ha : a ∈ E)
    (hb : b ∈ E) (ha1 : a ≠ 1) (hb' : b ∉ Subgroup.zpowers a) :
    Nat.card (Subgroup.closure ({a, b} : Set G)) = 9 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hfin : Finite E := Nat.finite_of_card_ne_zero (by rw [h27]; norm_num)
  have hab : a * b = b * a := by
    have := hE.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩
    exact congrArg Subtype.val this
  have ha3 : a ^ 3 = 1 := hE.2 a ha
  have hb3 : b ^ 3 = 1 := hE.2 b hb
  set C := Subgroup.closure ({a, b} : Set G) with hC
  have hCE : C ≤ E := (Subgroup.closure_le _).mpr (by
    intro x hx
    rcases hx with rfl | rfl
    · exact ha
    · exact hb)
  have hfinC : Finite C :=
    Finite.of_injective (Subgroup.inclusion hCE) (Subgroup.inclusion_injective hCE)
  have hle : Nat.card C ≤ 9 := by
    let f : Fin 3 × Fin 3 → G := fun ij => a ^ (ij.1 : ℕ) * b ^ (ij.2 : ℕ)
    have hsub : (C : Set G) ⊆ Set.range f := by
      intro x hx
      obtain ⟨i, j, rfl⟩ := exists_pow_mul_pow_of_mem_closure hab ha3 hb3 hx
      exact ⟨(i, j), rfl⟩
    calc Nat.card C = Nat.card (C : Set G) := rfl
      _ ≤ Nat.card (Set.range f) := Nat.card_mono (Set.finite_range f) hsub
      _ ≤ Nat.card (Fin 3 × Fin 3) := Finite.card_range_le f
      _ = 9 := by simp
  have hza : Nat.card (Subgroup.zpowers a) = 3 := by
    rw [Nat.card_zpowers]; exact orderOf_eq_prime ha3 ha1
  have hzC : Subgroup.zpowers a ≤ C := Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp))
  have hlt : 3 < Nat.card C := by
    rw [← hza]
    refine Subgroup.card_lt_of_lt ?_
    refine lt_of_le_of_ne hzC fun h => hb' ?_
    rw [h]; exact Subgroup.subset_closure (by simp)
  have hdvd : Nat.card C ∣ 27 := h27 ▸ Subgroup.card_dvd_of_le hCE
  have h27' : Nat.card C ∣ 3 ^ 3 := by norm_num; exact hdvd
  obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp h27'
  interval_cases k <;> simp_all

theorem relIndex_closure_pair {G : Type*} [Group G] {E : Subgroup G}
    (hE : CFSG.Assembly.IsElemAbelian 3 E) (h27 : Nat.card E = 27) {a b : G} (ha : a ∈ E)
    (hb : b ∈ E) (ha1 : a ≠ 1) (hb' : b ∉ Subgroup.zpowers a) :
    (Subgroup.closure ({a, b} : Set G)).relIndex E = 3 := by
  have hCE : Subgroup.closure ({a, b} : Set G) ≤ E := (Subgroup.closure_le _).mpr (by
    intro x hx
    rcases hx with rfl | rfl
    · exact ha
    · exact hb)
  have h := Subgroup.relIndex_mul_card (Subgroup.closure ({a, b} : Set G)) E
  rw [inf_of_le_left hCE, card_closure_pair hE h27 ha hb ha1 hb', h27] at h
  omega

theorem mem_seitzHyperGamma_of_pair {X : Type*} [Group X] {E : Subgroup (MulAut X)}
    (hE : CFSG.Assembly.IsElemAbelian 3 E) (h27 : Nat.card E = 27) {a b : MulAut X} (ha : a ∈ E)
    (hb : b ∈ E) (ha1 : a ≠ 1) (hb' : b ∉ Subgroup.zpowers a) {x : X} (hax : a x = x)
    (hbx : b x = x) : x ∈ seitzHyperGamma 3 E := by
  have hCE : Subgroup.closure ({a, b} : Set (MulAut X)) ≤ E := (Subgroup.closure_le _).mpr (by
    intro y hy
    rcases hy with rfl | rfl
    · exact ha
    · exact hb)
  refine fixedPoints_le_seitzHyperGamma hCE (relIndex_closure_pair hE h27 ha hb ha1 hb') ?_
  refine mem_fixedPoints_closure fun φ hφ => ?_
  rcases hφ with rfl | rfl
  · exact hax
  · exact hbx

theorem seitzHyperGamma_eq_top_of_map {X Y : Type*} [Group X] [Group Y] {p : ℕ} (e : X ≃* Y)
    (φ : MulAut X →* MulAut Y) (hφ : ∀ (a : MulAut X) (x : X), φ a (e x) = e (a x))
    (hφi : Function.Injective φ) {E : Subgroup (MulAut X)}
    (h : seitzHyperGamma p (E.map φ) = ⊤) : seitzHyperGamma p E = ⊤ := by
  have hle : seitzHyperGamma p (E.map φ) ≤ (seitzHyperGamma p E).map e.toMonoidHom := by
    refine iSup₂_le fun F' hF' => ?_
    obtain ⟨hF'E, hF'p⟩ := hF'
    set F := F'.comap φ with hF
    have hFE : F ≤ E := by
      intro a ha
      have : φ a ∈ E.map φ := hF'E ha
      obtain ⟨a', ha', hfa⟩ := this
      rw [← hφi hfa]; exact ha'
    have hmap : F.map φ = F' := by
      rw [hF, Subgroup.map_comap_eq, inf_of_le_right (hF'E.trans (Subgroup.map_le_range φ E))]
    have hFp : F.relIndex E = p := by
      rw [← Subgroup.relIndex_map_map_of_injective F E hφi, hmap]; exact hF'p
    intro y hy
    obtain ⟨x, rfl⟩ := e.surjective y
    refine ⟨x, ?_, rfl⟩
    refine fixedPoints_le_seitzHyperGamma hFE hFp ?_
    intro a ha
    have h1 := hy (φ a) (hmap ▸ Subgroup.mem_map_of_mem φ ha)
    rw [hφ] at h1
    exact e.injective h1
  rw [h, top_le_iff] at hle
  rw [eq_top_iff]
  intro x _
  have : e x ∈ (seitzHyperGamma p E).map e.toMonoidHom := by rw [hle]; trivial
  obtain ⟨x', hx', hxx'⟩ := this
  rw [← e.injective hxx']
  exact hx'

end CFSG.RankThree.PartTwo.Sec4.Res6L364
