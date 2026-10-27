module

public import CFSG.LocalAnalysis.StandardType.GGQ2ExtClassicalStatements
public import CFSG.LocalAnalysis.StandardType.GGQ2CensusChainA
public import CFSG.LocalAnalysis.StandardType.GGQ2UnitShapes
public import CFSG.LocalAnalysis.StandardType.GGQ2ClassicalInsideMoved

public section

namespace CFSG.StandardType.GGQ2Frame

open CFSG CFSG.Assembly Module

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace UnitRaw

theorem diff_mem_span_subset {N : ℕ} (hN : 6 ≤ N) {a b x y w : Fin N} (hab : a ≠ b) {s : F}
    (hs : s ≠ 0)
    (h : s • (unitVec N a - unitVec N b) ∈
      Submodule.span F {unitVec N x - unitVec N y, unitVec N y - unitVec N w}) :
    a ∈ ({x, y, w} : Finset (Fin N)) ∧ b ∈ ({x, y, w} : Finset (Fin N)) := by
  classical
  obtain ⟨α, β, hαβ⟩ := Submodule.mem_span_pair.mp h
  have hz : (oneLine N).mkQ (α • (Pi.single x 1 - Pi.single y 1) +
      β • (Pi.single y 1 - Pi.single w 1) - s • (Pi.single a 1 - Pi.single b 1) : W N) = 0 := by
    rw [map_sub, map_add, map_smul, map_smul, map_smul, map_sub, map_sub, map_sub]
    exact sub_eq_zero.mpr hαβ
  obtain ⟨c, hc⟩ := (mem_oneLine _).mp ((Submodule.Quotient.mk_eq_zero _).mp hz)
  have hcoord : ∀ i : Fin N, α * ((Pi.single x 1 : W N) i - (Pi.single y 1 : W N) i) +
      β * ((Pi.single y 1 : W N) i - (Pi.single w 1 : W N) i) -
      s * ((Pi.single a 1 : W N) i - (Pi.single b 1 : W N) i) = c := fun i => by
    have := congrFun hc i
    simpa only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] using this
  obtain ⟨i₀, hi₀⟩ : ∃ i : Fin N, i ∉ ({a, b, x, y, w} : Finset (Fin N)) := by
    by_contra hcon
    push Not at hcon
    have h1 : (Finset.univ : Finset (Fin N)).card ≤ ({a, b, x, y, w} : Finset (Fin N)).card :=
      Finset.card_le_card fun i _ => hcon i
    have h5 : ({a, b, x, y, w} : Finset (Fin N)).card ≤ 5 := Finset.card_le_five
    rw [Finset.card_univ, Fintype.card_fin] at h1
    omega
  have hc0 : c = 0 := by
    have := hcoord i₀
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hi₀
    obtain ⟨h1, h2, h3, h4, h5⟩ := hi₀
    simpa [Pi.single_apply, h1, h2, h3, h4, h5] using this.symm
  have key : ∀ i : Fin N, i ∉ ({x, y, w} : Finset (Fin N)) → i ≠ a ∧ i ≠ b := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hi
    obtain ⟨h1, h2, h3⟩ := hi
    have := hcoord i
    rw [hc0] at this
    constructor
    · rintro rfl
      simp [Pi.single_apply, h1, h2, h3, hab, hs] at this
    · rintro rfl
      simp [Pi.single_apply, h1, h2, h3, hab.symm, hs] at this
  constructor
  · by_contra ha
    exact (key a ha).1 rfl
  · by_contra hb
    exact (key b hb).2 rfl

theorem mem_span_singleton_heart {N : ℕ} {v z : ↥(heart N)} {c : F}
    (h : (z : Vfull N) = c • (v : Vfull N)) : z ∈ Submodule.span F {v} := by
  refine Submodule.mem_span_singleton.mpr ⟨c, Subtype.ext ?_⟩
  simpa using h.symm

theorem exists_overlap {N : ℕ} {a b a' b' x y w : Fin N} (hab : a ≠ b) (hab' : a' ≠ b')
    (hxy : x ≠ y) (hxw : x ≠ w) (hyw : y ≠ w)
    (ha : a ∈ ({x, y, w} : Finset (Fin N))) (hb : b ∈ ({x, y, w} : Finset (Fin N)))
    (ha' : a' ∈ ({x, y, w} : Finset (Fin N))) (hb' : b' ∈ ({x, y, w} : Finset (Fin N)))
    (hne : ({a, b} : Finset (Fin N)) ≠ {a', b'}) :
    ∃ m₁ m₂ m₃ : Fin N, m₁ ≠ m₂ ∧ m₁ ≠ m₃ ∧ m₂ ≠ m₃ ∧ ({a, b} : Finset (Fin N)) = {m₁, m₂} ∧
      ({a', b'} : Finset (Fin N)) = {m₂, m₃} := by
  classical
  have hPcard : ({a, b} : Finset (Fin N)).card = 2 := Finset.card_pair hab
  have hQcard : ({a', b'} : Finset (Fin N)).card = 2 := Finset.card_pair hab'
  have hTcard : ({x, y, w} : Finset (Fin N)).card = 3 :=
    Finset.card_eq_three.mpr ⟨x, y, w, hxy, hxw, hyw, rfl⟩
  have hPT : ({a, b} : Finset (Fin N)) ⊆ {x, y, w} := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl <;> assumption
  have hQT : ({a', b'} : Finset (Fin N)) ⊆ {x, y, w} := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl <;> assumption
  have hunion : (({a, b} : Finset (Fin N)) ∪ {a', b'}).card ≤ 3 :=
    hTcard ▸ Finset.card_le_card (Finset.union_subset hPT hQT)
  have hsum := Finset.card_union_add_card_inter ({a, b} : Finset (Fin N)) {a', b'}
  have hinter1 : (({a, b} : Finset (Fin N)) ∩ {a', b'}).card = 1 := by
    have hge : 1 ≤ (({a, b} : Finset (Fin N)) ∩ {a', b'}).card := by omega
    have hle : (({a, b} : Finset (Fin N)) ∩ {a', b'}).card ≤ 1 := by
      by_contra hcon
      have e1 : ({a, b} : Finset (Fin N)) ∩ {a', b'} = {a, b} :=
        Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by omega)
      have e2 : ({a, b} : Finset (Fin N)) ∩ {a', b'} = {a', b'} :=
        Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by omega)
      exact hne (e1.symm.trans e2)
    omega
  obtain ⟨m₂, hm₂⟩ := Finset.card_eq_one.mp hinter1
  have hmem : m₂ ∈ (({a, b} : Finset (Fin N)) ∩ {a', b'}) := by
    rw [hm₂]
    exact Finset.mem_singleton_self m₂
  have hm₂P : m₂ ∈ ({a, b} : Finset (Fin N)) := (Finset.mem_inter.mp hmem).1
  have hm₂Q : m₂ ∈ ({a', b'} : Finset (Fin N)) := (Finset.mem_inter.mp hmem).2
  have hP' : ∃ m₁, m₁ ≠ m₂ ∧ ({a, b} : Finset (Fin N)) = {m₁, m₂} := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm₂P
    rcases hm₂P with h | h
    · exact ⟨b, fun h' => hab (h.symm.trans h'.symm), by rw [h]; exact Finset.pair_comm a b⟩
    · exact ⟨a, fun h' => hab (h'.trans h), by rw [h]⟩
  have hQ' : ∃ m₃, m₃ ≠ m₂ ∧ ({a', b'} : Finset (Fin N)) = {m₂, m₃} := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm₂Q
    rcases hm₂Q with h | h
    · exact ⟨b', fun h' => hab' (h.symm.trans h'.symm), by rw [h]⟩
    · exact ⟨a', fun h' => hab' (h'.trans h), by rw [h]; exact Finset.pair_comm a' b'⟩
  obtain ⟨m₁, h1ne, hP⟩ := hP'
  obtain ⟨m₃, h3ne, hQ⟩ := hQ'
  refine ⟨m₁, m₂, m₃, h1ne, ?_, h3ne.symm, hP, hQ⟩
  rintro rfl
  have : m₁ ∈ (({a, b} : Finset (Fin N)) ∩ {a', b'}) :=
    Finset.mem_inter.mpr ⟨by rw [hP]; simp, by rw [hQ]; simp⟩
  rw [hm₂] at this
  exact h1ne (Finset.mem_singleton.mp this)

end UnitRaw

theorem extCasesUnitHeart_of_chain : ExtCasesUnitHeart := by
  have hc := unitHeartChainLeaf_holds
  intro N vx hvx0 ℓ hadm _ hocc hcent _ U hU hvxU j _ hjocc hjcent _ _ z hzU hzvx k hcand _
  obtain ⟨-, hkocc, hkcent, -, -⟩ := hcand
  have h3 : 3 ∣ N := hadm.2.1
  have hN6 : 6 ≤ N := by
    have h4 := hadm.1
    obtain ⟨m, rfl⟩ := h3
    omega
  have hz0 : z ≠ 0 := fun h0 => hzvx (h0 ▸ Submodule.zero_mem _)
  obtain ⟨a, b, s, hab, hs, hvab, hℓ⟩ :=
    UnitRaw.heartLineShapes_holds N h3 vx ℓ hvx0 hocc hcent
  obtain ⟨a', b', s', hab', hs', hzab, hk⟩ :=
    UnitRaw.heartLineShapes_holds N h3 z k hz0 hkocc hkcent
  obtain ⟨x, y, w, hxy, hxw, hyw, hj, hUspan⟩ :=
    UnitRaw.heartPlaneShapes_holds N h3 U j hU hjocc hjcent
  have hvx' : s • (UnitRaw.unitVec N a - UnitRaw.unitVec N b) ∈ Submodule.span UnitRaw.F
      {UnitRaw.unitVec N x - UnitRaw.unitVec N y, UnitRaw.unitVec N y - UnitRaw.unitVec N w} := by
    rw [← hvab, ← hUspan]
    exact Submodule.mem_map_of_mem hvxU
  have hz' : s' • (UnitRaw.unitVec N a' - UnitRaw.unitVec N b') ∈ Submodule.span UnitRaw.F
      {UnitRaw.unitVec N x - UnitRaw.unitVec N y, UnitRaw.unitVec N y - UnitRaw.unitVec N w} := by
    rw [← hzab, ← hUspan]
    exact Submodule.mem_map_of_mem hzU
  obtain ⟨ha, hb⟩ := UnitRaw.diff_mem_span_subset hN6 hab hs hvx'
  obtain ⟨ha', hb'⟩ := UnitRaw.diff_mem_span_subset hN6 hab' hs' hz'
  have hne : ({a, b} : Finset (Fin N)) ≠ {a', b'} := by
    intro heq
    apply hzvx
    have hmem_a : a ∈ ({a', b'} : Finset (Fin N)) := by rw [← heq]; simp
    have hmem_b : b ∈ ({a', b'} : Finset (Fin N)) := by rw [← heq]; simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem_a hmem_b
    rcases hmem_a with h1 | h1 <;> rcases hmem_b with h2 | h2
    · exact absurd (h1.trans h2.symm) hab
    · subst h1 h2
      refine UnitRaw.mem_span_singleton_heart (c := s' * s⁻¹) ?_
      rw [hzab, hvab, ← mul_smul, mul_assoc, inv_mul_cancel₀ hs, mul_one]
    · subst h1 h2
      refine UnitRaw.mem_span_singleton_heart (c := -(s' * s⁻¹)) ?_
      rw [hzab, hvab, ← mul_smul, neg_mul, mul_assoc, inv_mul_cancel₀ hs, mul_one, neg_smul,
        ← smul_neg, neg_sub]
    · exact absurd (h1.trans h2.symm) hab
  obtain ⟨m₁, m₂, m₃, h12, h13, h23, hP, hQ⟩ :=
    UnitRaw.exists_overlap hab hab' hxy hxw hyw ha hb ha' hb' hne
  have hℓ' : ℓ = ({m₁, m₂} : Finset (Fin N))ᶜ := by
    rw [hℓ, ← hP, Finset.compl_eq_univ_sdiff]
  have hk' : k = ({m₂, m₃} : Finset (Fin N))ᶜ := by
    rw [hk, ← hQ, Finset.compl_eq_univ_sdiff]
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 3 := ⟨N - 3, by omega⟩
  subst hℓ' hk'
  exact Or.inr (Or.inr (Or.inl (hc n (by omega) m₁ m₂ m₃ h12 h13 h23 vx z hcent hkcent)))

theorem extCasesUnitHeart_holds : ExtCasesUnitHeart :=
  extCasesUnitHeart_of_chain

end CFSG.StandardType.GGQ2Frame

end
