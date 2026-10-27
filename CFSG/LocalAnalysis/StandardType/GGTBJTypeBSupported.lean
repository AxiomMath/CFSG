module

public import CFSG.LocalAnalysis.StandardType.GGTBJTypeBDatum
public import CFSG.LocalAnalysis.StandardType.GGTBJWeylParabolicLE3
public import CFSG.LocalAnalysis.StandardType.GGReflConjSimpleOfClosed
public import CFSG.Permutation.SupportedAdjacent

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Monster.B.Geometry SpCoord
open Multiplicative

namespace TypeBDatum

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem tbS_mem_closure_singleton_eq {E : Type} [Group E] {g t : E}
    (hg : g * g = 1) (ht : t ∈ Subgroup.closure ({g} : Set E)) : t = 1 ∨ t = g := by
  refine Subgroup.closure_induction (p := fun t _ => t = 1 ∨ t = g) ?_ ?_ ?_ ?_ ht
  · intro x hx
    rw [Set.mem_singleton_iff] at hx
    exact Or.inr hx
  · exact Or.inl rfl
  · intro x y hx hy ihx ihy
    rcases ihx with hx1 | hxg <;> rcases ihy with hy1 | hyg
    · exact Or.inl (by simp [hx1, hy1])
    · exact Or.inr (by simp [hx1, hyg])
    · exact Or.inr (by simp [hxg, hy1])
    · exact Or.inl (by rw [hxg, hyg]; exact hg)
  · intro x hx ih
    rcases ih with hx1 | hxg
    · exact Or.inl (by rw [hx1]; exact inv_one)
    · exact Or.inr (by rw [hxg]; exact inv_eq_of_mul_eq_one_right hg)

private theorem tbS_refl_ne_one {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {Bs : Subgroup G} {φ : MulAut ↥Bs} (hr : GGIsReflection p φ) : φ ≠ 1 := by
  haveI : Finite ↥Bs := Finite.of_injective (Subtype.val : ↥Bs → G) Subtype.val_injective
  haveI : Nonempty ↥Bs := ⟨(1 : ↥Bs)⟩
  rintro rfl
  obtain ⟨-, hc⟩ := hr
  simp only [MulAut.one_apply] at hc
  have hc' : Nat.card {b : ↥Bs // True} * p = Nat.card ↥Bs := by simpa using hc
  rw [Nat.card_congr (Equiv.subtypeUnivEquiv fun _ => trivial)] at hc'
  have hpos : 0 < Nat.card ↥Bs := Nat.card_pos
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  nlinarith

private theorem tbS_reflConjSimple_subsingleton {G : Type} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {Bs : Subgroup G} {A : Subgroup (MulAut ↥Bs)} {Λ : Type} [Nonempty Λ]
    (φ : Λ → MulAut ↥Bs) (hA : A = Subgroup.closure (Set.range φ))
    (hrefl : ∀ i, GGIsReflection p (φ i)) (hsub : Subsingleton Λ) :
    GGReflConjSimple p A φ := by
  let i₀ : Λ := Classical.arbitrary Λ
  intro t ht hr
  rw [hA] at ht
  have hrange : Set.range φ = {φ i₀} := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact Set.mem_singleton_iff.mpr (congrArg φ (hsub.allEq i i₀))
    · rintro rfl
      exact ⟨i₀, rfl⟩
  rw [hrange] at ht
  have hg : φ i₀ * φ i₀ = 1 := by
    have h := (hrefl i₀).1
    simpa [pow_two] using h
  have ht' : t = 1 ∨ t = φ i₀ := tbS_mem_closure_singleton_eq hg ht
  rcases ht' with h | h
  · exact absurd h (tbS_refl_ne_one hr)
  · exact ⟨1, Subgroup.one_mem _, i₀, by rw [h]; group⟩

private def tbS_permAutHom (p m : ℕ) :
    Equiv.Perm (Fin m) →* MulAut (Fin m → Multiplicative (ZMod p)) where
  toFun := permAut (p := p)
  map_one' := by
    refine MulEquiv.ext fun f => funext fun i => ?_
    change permAut (p := p) 1 f i = (1 : MulAut (Fin m → Multiplicative (ZMod p))) f i
    simp [permAut_apply]
  map_mul' σ τ := by
    refine MulEquiv.ext fun f => funext fun i => ?_
    change permAut (p := p) (σ * τ) f i =
      (permAut (p := p) σ * permAut (p := p) τ) f i
    simp only [MulAut.mul_apply, permAut_apply, Function.comp_apply]
    rw [mul_inv_rev, Equiv.Perm.mul_apply]

@[simp] private theorem tbS_permAutHom_apply (p m : ℕ) (σ : Equiv.Perm (Fin m)) :
    tbS_permAutHom p m σ = permAut (p := p) σ := rfl

private theorem tbS_conj_permAut_sgnAut {p m : ℕ} (τ : Equiv.Perm (Fin m)) (i : Fin m) :
    MulAut.conj (permAut (p := p) τ) (sgnAut (p := p) i) = sgnAut (p := p) (τ i) := by
  rw [MulAut.conj_apply]
  have hu : ∀ f j, toAdd ((permAut (p := p) τ) f (τ j)) = (1 : ZMod p) * toAdd (f j) := by
    intro f j
    simp only [permAut_apply, Function.comp_apply, Equiv.Perm.coe_inv, Equiv.symm_apply_apply,
      one_mul]
  have h := IsSignedPerm.mul_sgnAut (u := permAut (p := p) τ) hu i
  calc (permAut (p := p) τ : MulAut (Fin m → Multiplicative (ZMod p))) * sgnAut (p := p) i *
        (permAut (p := p) τ)⁻¹
      = sgnAut (p := p) (τ i) * (permAut (p := p) τ * (permAut (p := p) τ)⁻¹) := by
        rw [h, mul_assoc]
    _ = sgnAut (p := p) (τ i) := by rw [mul_inv_cancel, mul_one]

private theorem tbS_conj_permAut_swap {p m : ℕ} (τ : Equiv.Perm (Fin m)) (a b : Fin m) :
    MulAut.conj (permAut (p := p) τ) (permAut (p := p) (Equiv.swap a b)) =
      permAut (p := p) (Equiv.swap (τ a) (τ b)) := by
  rw [MulAut.conj_apply]
  have hperm : τ * Equiv.swap a b * τ⁻¹ = Equiv.swap (τ a) (τ b) := by
    rw [Equiv.mul_swap_eq_swap_mul τ a b]
    group
  have h1 : (permAut (p := p) τ : MulAut (Fin m → Multiplicative (ZMod p))) *
        permAut (p := p) (Equiv.swap a b) * (permAut (p := p) τ)⁻¹ =
      tbS_permAutHom p m (τ * Equiv.swap a b * τ⁻¹) := by
    simp only [← tbS_permAutHom_apply]
    rw [map_mul, map_inv, map_mul]
  rw [h1, hperm, tbS_permAutHom_apply]

private theorem tbS_conj_permAut_signedSupportedAut {p m : ℕ} (τ : Equiv.Perm (Fin m))
    (S : Finset (Fin m)) :
    (signedSupportedAut m p S).map (MulAut.conj (permAut (p := p) τ)).toMonoidHom =
      signedSupportedAut m p (S.image τ) := by
  unfold signedSupportedAut
  rw [MonoidHom.map_closure]
  congr 1
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    rcases hy with hy | hy
    · rcases hy with ⟨i, hiS, rfl⟩
      exact Or.inl ⟨τ i, Finset.mem_image.mpr ⟨i, hiS, rfl⟩, by
        change MulAut.conj (permAut (p := p) τ) (sgnAut (p := p) i) = sgnAut (p := p) (τ i)
        rw [tbS_conj_permAut_sgnAut]⟩
    · rcases hy with ⟨a, haS, b, hbS, hab, rfl⟩
      exact Or.inr ⟨τ a, Finset.mem_image.mpr ⟨a, haS, rfl⟩, τ b,
        Finset.mem_image.mpr ⟨b, hbS, rfl⟩, fun h => hab (τ.injective h), by
        change MulAut.conj (permAut (p := p) τ) (permAut (p := p) (Equiv.swap a b)) =
          permAut (p := p) (Equiv.swap (τ a) (τ b))
        rw [tbS_conj_permAut_swap]⟩
  · rintro (hx | hx)
    · rcases hx with ⟨i, hi, rfl⟩
      obtain ⟨j, hjS, rfl⟩ := Finset.mem_image.mp hi
      exact ⟨sgnAut (p := p) j, Or.inl ⟨j, hjS, rfl⟩, by
        change MulAut.conj (permAut (p := p) τ) (sgnAut (p := p) j) = sgnAut (p := p) (τ j)
        rw [tbS_conj_permAut_sgnAut]⟩
    · rcases hx with ⟨a, ha, b, hb, hab, rfl⟩
      obtain ⟨i, hiS, rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨j, hjS, rfl⟩ := Finset.mem_image.mp hb
      exact ⟨permAut (p := p) (Equiv.swap i j), Or.inr ⟨i, hiS, j, hjS,
        fun h => hab (congrArg τ h), rfl⟩, by
        change MulAut.conj (permAut (p := p) τ) (permAut (p := p) (Equiv.swap i j)) =
          permAut (p := p) (Equiv.swap (τ i) (τ j))
        rw [tbS_conj_permAut_swap]⟩

private theorem tbS_notMem_T_iff {m k : ℕ} (T : Finset (Fin m))
    (hT : T = Finset.univ.filter (fun i : Fin m => i.val < m - k)) (x : Fin m) :
    x ∉ T ↔ m - k ≤ x.val := by
  rw [hT]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt]

private def tbS_lastEquiv (m k : ℕ) (hkm : k ≤ m) (T : Finset (Fin m))
    (hT : T = Finset.univ.filter (fun i : Fin m => i.val < m - k)) :
    Fin k ≃ {j : Fin m // j ∉ T} where
  toFun a := ⟨⟨m - k + a.val, by omega⟩, (tbS_notMem_T_iff T hT _).mpr (by
    show m - k ≤ m - k + a.val
    omega)⟩
  invFun j := ⟨j.1.val - (m - k), by
    have hj : m - k ≤ j.1.val := (tbS_notMem_T_iff T hT j.1).mp j.2
    omega⟩
  left_inv a := by
    apply Fin.ext
    dsimp only
    omega
  right_inv j := by
    apply Subtype.ext
    apply Fin.ext
    dsimp only
    have hj : m - k ≤ j.1.val := (tbS_notMem_T_iff T hT j.1).mp j.2
    omega

private def tbS_tlEquivSucc (m k : ℕ) (hk : 1 ≤ k) (hkm : k ≤ m) :
    Fin ((k - 1) + 1) ≃ ↥(Finset.univ.filter (fun i : Fin m => m - k ≤ i.val)) where
  toFun a := ⟨⟨m - k + a.val, by omega⟩, by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact Nat.le_add_right (m - k) a.val⟩
  invFun j := ⟨j.1.val - (m - k), by
    have hj : m - k ≤ j.1.val := by
      have h := j.2
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h
      exact h
    omega⟩
  left_inv a := by
    apply Fin.ext
    dsimp only
    omega
  right_inv j := by
    apply Subtype.ext
    apply Fin.ext
    dsimp only
    have hj : m - k ≤ j.1.val := by
      have h := j.2
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h
      exact h
    omega

private theorem tbS_B_one_eq_A_one : CoxeterMatrix.B 1 = CoxeterMatrix.A 1 := by
  ext i j
  fin_cases i
  fin_cases j
  simp [CoxeterMatrix.B, CoxeterMatrix.A]

private theorem tbS_parMatrix_B_last {m k : ℕ} (hk : 1 ≤ k) (hkm : k ≤ m)
    (T : Finset (Fin m)) (hT : T = Finset.univ.filter (fun i : Fin m => i.val < m - k)) :
    parMatrix (CoxeterMatrix.B m) {j : Fin m | j ∉ T} =
      (CoxeterMatrix.B k).reindex (tbS_lastEquiv m k hkm T hT) := by
  ext i j
  show (CoxeterMatrix.B m) i.1 j.1 =
    (CoxeterMatrix.B k) ((tbS_lastEquiv m k hkm T hT).symm i)
      ((tbS_lastEquiv m k hkm T hT).symm j)
  rw [show (tbS_lastEquiv m k hkm T hT).symm i = ⟨i.1.val - (m - k), by omega⟩ from Fin.ext rfl,
    show (tbS_lastEquiv m k hkm T hT).symm j = ⟨j.1.val - (m - k), by omega⟩ from Fin.ext rfl]
  simp only [CoxeterMatrix.B, Matrix.of_apply, Fin.ext_iff]
  have hi := i.1.isLt
  have hj := j.1.isLt
  have hi' : m - k ≤ i.1.val := (tbS_notMem_T_iff T hT i.1).mp i.2
  have hj' : m - k ≤ j.1.val := (tbS_notMem_T_iff T hT j.1).mp j.2
  split_ifs <;> omega

private theorem tbS_isWeylMatrix_reindex_B {m k : ℕ} (hk : 1 ≤ k) (hkm : k ≤ m)
    (T : Finset (Fin m)) (hT : T = Finset.univ.filter (fun i : Fin m => i.val < m - k)) :
    GGIsWeylMatrix ((CoxeterMatrix.B k).reindex (tbS_lastEquiv m k hkm T hT)) := by
  by_cases hk1 : k = 1
  · subst hk1
    exact Or.inl ⟨1, tbS_lastEquiv m 1 hkm T hT, le_refl 1,
      Or.inl (by rw [tbS_B_one_eq_A_one])⟩
  · exact Or.inl ⟨k, tbS_lastEquiv m k hkm T hT, hk, Or.inr (Or.inl ⟨by omega, rfl⟩)⟩

private theorem tbS_isWeylMatrixFixed_reindex_B {m k : ℕ} (hk : 1 ≤ k) (hkm : k ≤ m)
    (T : Finset (Fin m)) (hT : T = Finset.univ.filter (fun i : Fin m => i.val < m - k))
    (hk2 : 2 ≤ k) :
    GGIsWeylMatrixFixed ((CoxeterMatrix.B k).reindex (tbS_lastEquiv m k hkm T hT)) :=
  Or.inl ⟨k, tbS_lastEquiv m k hkm T hT, hk, Or.inr (Or.inl ⟨hk2, rfl⟩)⟩

private theorem tbS_permAut_swap_mem {p m k : ℕ} (hk : 1 ≤ k) (hkm : k ≤ m)
    {Q : Subgroup (MulAut (Fin m → Multiplicative (ZMod p)))}
    (hQ : ∀ j : {j : Fin m // m - k ≤ j.val},
      (if h : j.1.val + 1 < m then permAut (p := p) (Equiv.swap j.1 ⟨j.1.val + 1, h⟩)
        else sgnAut (p := p) j.1) ∈ Q)
    {a b : Fin m} (ha : m - k ≤ a.val) (hb : m - k ≤ b.val) (hab : a ≠ b) :
    permAut (p := p) (Equiv.swap a b) ∈ Q := by
  classical
  let Tl := Finset.univ.filter (fun i : Fin m => m - k ≤ i.val)
  have haTl : a ∈ Tl := by
    simp only [Tl, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ha
  have hbTl : b ∈ Tl := by
    simp only [Tl, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hb
  let eTl : Fin ((k - 1) + 1) ≃ ↥Tl := tbS_tlEquivSucc m k hk hkm
  have hfix := CFSG.Permutation.TranspositionCentralizer.fixingSubgroup_compl_eq_closure_adjacent
    Tl eTl
  have hmem : Equiv.swap a b ∈ fixingSubgroup (Equiv.Perm (Fin m)) ((Tl : Set (Fin m))ᶜ) := by
    rw [mem_fixingSubgroup_iff]
    intro y hy
    have hya : y ≠ a := fun h => hy (h ▸ haTl)
    have hyb : y ≠ b := fun h => hy (h ▸ hbTl)
    simp only [Equiv.Perm.smul_def]
    exact Equiv.swap_apply_of_ne_of_ne hya hyb
  have hle : (fixingSubgroup (Equiv.Perm (Fin m)) ((Tl : Set (Fin m))ᶜ)).map
      (tbS_permAutHom p m) ≤ Q := by
    rw [hfix, MonoidHom.map_closure, Subgroup.closure_le]
    rintro x ⟨y, ⟨j, rfl⟩, rfl⟩
    rw [tbS_permAutHom_apply]
    set a' : Fin m := (eTl j.castSucc : Fin m) with ha'def
    set b' : Fin m := (eTl j.succ : Fin m) with hb'def
    have ha'val : a'.val = m - k + j.val := by
      rw [ha'def]
      rfl
    have hb'val : b'.val = m - k + j.val + 1 := by
      rw [hb'def]
      rfl
    have hlt : a'.val + 1 < m := by rw [ha'val]; omega
    let j' : {j : Fin m // m - k ≤ j.val} := ⟨a', by rw [ha'val]; omega⟩
    have hQj := hQ j'
    have hif : (if h : j'.1.val + 1 < m then
        permAut (p := p) (Equiv.swap j'.1 ⟨j'.1.val + 1, h⟩) else sgnAut (p := p) j'.1) =
        permAut (p := p) (Equiv.swap a' ⟨a'.val + 1, hlt⟩) := by
      rw [dif_pos hlt]
    rw [hif] at hQj
    have hb'eq : (⟨a'.val + 1, hlt⟩ : Fin m) = b' := by
      apply Fin.ext
      simp only [ha'val, hb'val]
    rw [hb'eq] at hQj
    exact hQj
  exact hle (Subgroup.mem_map_of_mem (tbS_permAutHom p m) hmem)

private theorem tbS_closure_last_le_signedSupported {p m k : ℕ} (hk : 1 ≤ k) (hkm : k ≤ m) :
    Subgroup.closure (Set.range fun j :
        {j : Fin m // j ∉ Finset.univ.filter (fun i : Fin m => i.val < m - k)} =>
      (if h : j.1.val + 1 < m then permAut (p := p) (Equiv.swap j.1 ⟨j.1.val + 1, h⟩)
        else sgnAut (p := p) j.1)) ≤
      signedSupportedAut m p (Finset.univ.filter (fun i : Fin m => m - k ≤ i.val)) := by
  classical
  let Tl := Finset.univ.filter (fun i : Fin m => m - k ≤ i.val)
  let T := Finset.univ.filter (fun i : Fin m => i.val < m - k)
  rw [Subgroup.closure_le]
  rintro σ ⟨j, rfl⟩
  have hjT : m - k ≤ j.1.val := by
    have h := j.2
    simp only [T, Finset.mem_filter, Finset.mem_univ, true_and] at h
    omega
  have hjTl : j.1 ∈ Tl := by
    simp only [Tl, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hjT
  by_cases hlt : j.1.val + 1 < m
  · simp only []
    rw [dif_pos hlt]
    have hsuccTl : (⟨j.1.val + 1, hlt⟩ : Fin m) ∈ Tl := by
      simp only [Tl, Finset.mem_filter, Finset.mem_univ, true_and]
      omega
    exact Subgroup.subset_closure
      (Or.inr ⟨j.1, hjTl, ⟨j.1.val + 1, hlt⟩, hsuccTl, by
        intro h
        have hh : j.1.val = (⟨j.1.val + 1, hlt⟩ : Fin m).val := congrArg Fin.val h
        rw [show (⟨j.1.val + 1, hlt⟩ : Fin m).val = j.1.val + 1 from rfl] at hh
        omega, rfl⟩)
  · simp only []
    rw [dif_neg hlt]
    exact Subgroup.subset_closure (Or.inl ⟨j.1, hjTl, rfl⟩)

private theorem tbS_signedSupported_last_le_closure {p m k : ℕ} (hk : 1 ≤ k) (hkm : k ≤ m) :
    signedSupportedAut m p (Finset.univ.filter (fun i : Fin m => m - k ≤ i.val)) ≤
      Subgroup.closure (Set.range fun j :
          {j : Fin m // j ∉ Finset.univ.filter (fun i : Fin m => i.val < m - k)} =>
        (if h : j.1.val + 1 < m then permAut (p := p) (Equiv.swap j.1 ⟨j.1.val + 1, h⟩)
          else sgnAut (p := p) j.1)) := by
  classical
  let Tl := Finset.univ.filter (fun i : Fin m => m - k ≤ i.val)
  let T := Finset.univ.filter (fun i : Fin m => i.val < m - k)
  let Q : Subgroup (MulAut (Fin m → Multiplicative (ZMod p))) :=
    Subgroup.closure (Set.range fun j : {j : Fin m // j ∉ T} =>
      (if h : j.1.val + 1 < m then permAut (p := p) (Equiv.swap j.1 ⟨j.1.val + 1, h⟩)
        else sgnAut (p := p) j.1))
  have hQ : ∀ j : {j : Fin m // m - k ≤ j.val},
      (if h : j.1.val + 1 < m then permAut (p := p) (Equiv.swap j.1 ⟨j.1.val + 1, h⟩)
        else sgnAut (p := p) j.1) ∈ Q := by
    intro j
    have hjT : j.1 ∉ T := by
      simp only [T, Finset.mem_filter, Finset.mem_univ, true_and]
      omega
    exact Subgroup.subset_closure ⟨⟨j.1, hjT⟩, rfl⟩
  have hlastT : (⟨m - 1, by omega⟩ : Fin m) ∉ T := by
    simp only [T, Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  have hlastQ : sgnAut (p := p) (⟨m - 1, by omega⟩ : Fin m) ∈ Q := by
    have hmem : (fun j : {j : Fin m // j ∉ T} =>
        (if h : j.1.val + 1 < m then permAut (p := p) (Equiv.swap j.1 ⟨j.1.val + 1, h⟩)
          else sgnAut (p := p) j.1)) ⟨⟨m - 1, by omega⟩, hlastT⟩ ∈ Q :=
      Subgroup.subset_closure ⟨⟨⟨m - 1, by omega⟩, hlastT⟩, rfl⟩
    have hltm : ¬ (⟨m - 1, by omega⟩ : Fin m).val + 1 < m := by
      rw [show (⟨m - 1, by omega⟩ : Fin m).val = m - 1 from rfl]
      omega
    simpa only [dif_neg hltm] using hmem
  rw [signedSupportedAut, Subgroup.closure_le]
  rintro σ (hσ | hσ)
  · rcases hσ with ⟨i, hiTl, rfl⟩
    have hiTl' : m - k ≤ i.val := by
      have h := hiTl
      simp only [Tl, Finset.mem_filter, Finset.mem_univ, true_and] at h
      exact h
    have hperm : permAut (p := p) (Equiv.swap i (⟨m - 1, by omega⟩ : Fin m)) ∈ Q := by
      by_cases hi : i = (⟨m - 1, by omega⟩ : Fin m)
      · rw [hi]
        rw [show Equiv.swap (⟨m - 1, by omega⟩ : Fin m) (⟨m - 1, by omega⟩ : Fin m) =
            (1 : Equiv.Perm (Fin m)) from Equiv.swap_self _]
        rw [← tbS_permAutHom_apply, map_one]
        exact Q.one_mem
      · exact tbS_permAut_swap_mem hk hkm hQ hiTl' (by
          rw [show (⟨m - 1, by omega⟩ : Fin m).val = m - 1 from rfl]; omega) hi
    rw [show sgnAut (p := p) i = sgnAut (p := p)
        (Equiv.swap i (⟨m - 1, by omega⟩ : Fin m) (⟨m - 1, by omega⟩ : Fin m)) by
      rw [Equiv.swap_apply_right]]
    rw [← tbS_conj_permAut_sgnAut (p := p) (Equiv.swap i (⟨m - 1, by omega⟩ : Fin m))
      (⟨m - 1, by omega⟩ : Fin m)]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hperm hlastQ) (Subgroup.inv_mem _ hperm)
  · rcases hσ with ⟨a, haTl, b, hbTl, hab, rfl⟩
    have haTl' : m - k ≤ a.val := by
      have h := haTl
      simp only [Tl, Finset.mem_filter, Finset.mem_univ, true_and] at h
      exact h
    have hbTl' : m - k ≤ b.val := by
      have h := hbTl
      simp only [Tl, Finset.mem_filter, Finset.mem_univ, true_and] at h
      exact h
    exact tbS_permAut_swap_mem hk hkm hQ haTl' hbTl' hab

private theorem tbS_signedSupported_eq_closure_last {p m k : ℕ} (hk : 1 ≤ k) (hkm : k ≤ m) :
    signedSupportedAut m p (Finset.univ.filter (fun i : Fin m => m - k ≤ i.val)) =
      Subgroup.closure (Set.range fun j :
          {j : Fin m // j ∉ Finset.univ.filter (fun i : Fin m => i.val < m - k)} =>
        (if h : j.1.val + 1 < m then permAut (p := p) (Equiv.swap j.1 ⟨j.1.val + 1, h⟩)
          else sgnAut (p := p) j.1)) :=
  le_antisymm (tbS_signedSupported_last_le_closure hk hkm)
    (tbS_closure_last_le_signedSupported hk hkm)

theorem ggTBJTypeB_sideDatum_signedSupported {G : Type} [Group G] [Finite G] {p m : ℕ}
    [Fact p.Prime] (hp2 : p ≠ 2) (hm : 2 ≤ m) {Bs X J : Subgroup G} (hBs : IsElemAbelian p Bs)
    {W₀ : Type} [Group W₀] (Θ : ((Fin m → Multiplicative (ZMod p)) × W₀) ≃* ↥Bs)
    (hX : ggAutomizer X Bs = (signedAut m p).map (liftBs Θ))
    {S : Finset (Fin m)} (hS : 1 ≤ S.card) (hc : 1 ≤ m - S.card) (hc3 : m - S.card ≤ 3)
    (hJ : ggAutomizer J Bs = (signedSupportedAut m p S).map (liftBs Θ)) :
    (m - S.card = 1 → GGResSideDatum p Bs X J) ∧
      (2 ≤ m - S.card → GGResLeviSideDatumLE3 p Bs X J) := by
  classical
  set k : ℕ := S.card with hk
  have hk1 : 1 ≤ k := by omega
  have hkm : k ≤ m := by omega
  let Tl : Finset (Fin m) := Finset.univ.filter (fun i : Fin m => m - k ≤ i.val)
  let T : Finset (Fin m) := Finset.univ.filter (fun i : Fin m => i.val < m - k)
  let eS : Fin k ≃ ↥S := (Finite.equivFinOfCardEq (by rw [Nat.card_eq_finsetCard])).symm
  let first : Fin k ↪ Fin m := eS.toEmbedding.trans (Function.Embedding.subtype (· ∈ S))
  let eTl : Fin k ≃ {j : Fin m // j ∉ T} := tbS_lastEquiv m k hkm T rfl
  let second : Fin k ↪ Fin m :=
    eTl.toEmbedding.trans (Function.Embedding.subtype (fun j : Fin m => j ∉ T))
  obtain ⟨τ, hτ⟩ := Equiv.Perm.exists_smul_eq_embedding first second
  have hτi : ∀ i, τ (first i) = second i := by
    intro i
    have hh := congrArg (fun e : Fin k ↪ Fin m => e i) hτ
    simpa only [Function.Embedding.smul_apply, Equiv.Perm.smul_def, second,
      Function.Embedding.trans_apply, Equiv.coe_toEmbedding,
      Function.Embedding.coe_subtype] using hh
  have himage : S.image τ = Tl := by
    ext x
    constructor
    · intro hx
      obtain ⟨y, hyS, rfl⟩ := Finset.mem_image.mp hx
      have hy : y = first (eS.symm ⟨y, hyS⟩) :=
        (congrArg Subtype.val (Equiv.apply_symm_apply eS ⟨y, hyS⟩)).symm
      have hsec : second (eS.symm ⟨y, hyS⟩) ∈ Tl := by
        have hval : (second (eS.symm ⟨y, hyS⟩)).val =
            m - k + (eS.symm ⟨y, hyS⟩).val := rfl
        simp only [Tl, Finset.mem_filter, Finset.mem_univ, true_and]
        omega
      rw [hy, hτi]
      exact hsec
    · intro hx
      have hx' : m - k ≤ x.val := by
        have h := hx
        simp only [Tl, Finset.mem_filter, Finset.mem_univ, true_and] at h
        exact h
      have hxT : x ∉ T := by
        simp only [T, Finset.mem_filter, Finset.mem_univ, true_and]
        omega
      refine Finset.mem_image.mpr ⟨first (eTl.symm ⟨x, hxT⟩), ?_, ?_⟩
      · exact (eS (eTl.symm ⟨x, hxT⟩)).2
      · rw [hτi]
        exact congrArg Subtype.val (Equiv.apply_symm_apply eTl ⟨x, hxT⟩)
  have hTl_image : Tl.image τ.symm = S := by
    rw [← himage, Finset.image_image]
    simp
  let P : MulAut (Fin m → Multiplicative (ZMod p)) := permAut (p := p) τ.symm
  have hP : P ∈ signedAut m p := by
    refine mem_of_isSignedPerm (H := signedAut m p) ?_ ?_ (isSignedPerm_permAut τ.symm)
    · intro i
      show sgnAut (p := p) i ∈ signedSupportedAut m p Finset.univ
      exact Subgroup.subset_closure (Or.inl ⟨i, Finset.mem_univ i, rfl⟩)
    · intro a b hab
      show permAut (p := p) (Equiv.swap a b) ∈ signedSupportedAut m p Finset.univ
      exact Subgroup.subset_closure
        (Or.inr ⟨a, Finset.mem_univ a, b, Finset.mem_univ b, hab, rfl⟩)
  obtain ⟨V, hV, hVmod, ι, φ, h, α, C, hMC, hlin, hrefl, hpair, ⟨f, hf⟩, hclos, hφeq⟩ :=
    exists_typeB_datum_of_signedAut hp2 hm hBs Θ hX
  letI : AddCommGroup V := hV
  letI : Module (ZMod p) V := hVmod
  let u : MulAut ↥Bs := liftBs Θ P
  have hu : u ∈ ggAutomizer X Bs := by
    rw [hX]
    exact Subgroup.mem_map_of_mem (liftBs Θ) hP
  let U : V ≃ₗ[ZMod p] V := ggLin (p := p) ι u
  let φ' : Fin m → MulAut ↥Bs := fun i => u * φ i * u⁻¹
  let h' : Fin m → V := fun i => U (h i)
  let α' : Fin m → Module.Dual (ZMod p) V := fun i => (α i).comp U.symm.toLinearMap
  let cAut : ggAutomizer X Bs ≃* ggAutomizer X Bs := MulAut.conj ⟨u, hu⟩
  let f' : (CoxeterMatrix.B m).Group ≃* ↥(ggAutomizer X Bs) := f.trans cAut
  have hf' : ∀ i, (f' ((CoxeterMatrix.B m).simple i) : MulAut ↥Bs) = φ' i := by
    intro i
    change u * (f ((CoxeterMatrix.B m).simple i) : MulAut ↥Bs) * u⁻¹ = _
    rw [hf i]
  have hclos' : ggAutomizer X Bs = Subgroup.closure (Set.range φ') := by
    have heq := l05nBL_closure_conj (ggAutomizer X Bs) u hu
    rw [hclos, MonoidHom.map_closure, ← Set.range_comp] at heq
    rw [hclos]
    exact heq.symm
  have hlin' : ∀ i w, ggLin (p := p) ι (φ' i) w = w - α' i w • h' i := by
    intro i w
    exact l05nBL_lin_conj ι u (φ i) (hlin i) w
  have hrefl' : ∀ i, GGIsReflection p (φ' i) := fun i => l05nBL_refl_conj (hrefl i) u
  have hpair' : ∀ i j, α' i (h' j) = (C i j : ZMod p) := by
    intro i j
    change α i (U.symm (U (h j))) = _
    rw [LinearEquiv.symm_apply_apply, hpair]
  have hlast := tbS_signedSupported_eq_closure_last (p := p) (m := m) (k := k) hk1 hkm
  have hJclosure : ggAutomizer J Bs =
      Subgroup.closure (Set.range fun j : {j : Fin m // j ∉ T} => φ' j.1) := by
    rw [hJ]
    have hS' : signedSupportedAut m p S =
        (signedSupportedAut m p Tl).map (MulAut.conj P).toMonoidHom := by
      have hconj := tbS_conj_permAut_signedSupportedAut (p := p) (τ := τ.symm) (S := Tl)
      rw [hTl_image] at hconj
      exact hconj.symm
    rw [hS', Subgroup.map_map]
    have hcomp : (liftBs Θ).comp (MulAut.conj P).toMonoidHom =
        (MulAut.conj u).toMonoidHom.comp (liftBs Θ) := by
      refine MonoidHom.ext fun y => ?_
      change liftBs Θ (P * y * P⁻¹) = u * liftBs Θ y * u⁻¹
      rw [map_mul, map_mul, map_inv]
    rw [hcomp, ← Subgroup.map_map]
    rw [hlast, MonoidHom.map_closure, MonoidHom.map_closure]
    congr 1
    ext x
    constructor
    · rintro ⟨y, ⟨z, ⟨j, rfl⟩, rfl⟩, rfl⟩
      refine ⟨j, ?_⟩
      show φ' j.1 = (MulAut.conj u) (liftBs Θ
        (if h : j.1.val + 1 < m then permAut (p := p) (Equiv.swap j.1 ⟨j.1.val + 1, h⟩)
          else sgnAut (p := p) j.1))
      rw [← hφeq j.1]
      rfl
    · rintro ⟨j, rfl⟩
      refine ⟨liftBs Θ (if h : j.1.val + 1 < m then
          permAut (p := p) (Equiv.swap j.1 ⟨j.1.val + 1, h⟩) else sgnAut (p := p) j.1),
        ⟨(if h : j.1.val + 1 < m then
          permAut (p := p) (Equiv.swap j.1 ⟨j.1.val + 1, h⟩) else sgnAut (p := p) j.1),
          ⟨j, rfl⟩, rfl⟩, ?_⟩
      show (MulAut.conj u) (liftBs Θ
        (if h : j.1.val + 1 < m then permAut (p := p) (Equiv.swap j.1 ⟨j.1.val + 1, h⟩)
          else sgnAut (p := p) j.1)) = φ' j.1
      rw [← hφeq j.1]
      rfl
  have hWM : GGIsWeylMatrix (CoxeterMatrix.B m) :=
    Or.inl ⟨m, Equiv.refl _, by omega,
      Or.inr (Or.inl ⟨hm, (ggCoxeterMatrix_reindex_refl (CoxeterMatrix.B m)).symm⟩)⟩
  have hWMJ : GGIsWeylMatrix (parMatrix (CoxeterMatrix.B m) {j : Fin m | j ∉ T}) := by
    rw [tbS_parMatrix_B_last hk1 hkm T rfl]
    exact tbS_isWeylMatrix_reindex_B hk1 hkm T rfl
  have hRC : GGReflConjSimple p (ggAutomizer J Bs)
      (fun j : {j : Fin m // j ∉ T} => φ' j.1) := by
    by_cases hk1' : k = 1
    · haveI : Nonempty {j : Fin m // j ∉ T} :=
        ⟨⟨⟨m - 1, by omega⟩, by
          simp only [T, Finset.mem_filter, Finset.mem_univ, true_and]
          omega⟩⟩
      have hsub : Subsingleton {j : Fin m // j ∉ T} :=
        ⟨fun a b => Subtype.ext (Fin.ext (by
          have ha : m - 1 ≤ a.1.val := by
            have h := a.2
            simp only [T, Finset.mem_filter, Finset.mem_univ, true_and] at h
            omega
          have hb : m - 1 ≤ b.1.val := by
            have h := b.2
            simp only [T, Finset.mem_filter, Finset.mem_univ, true_and] at h
            omega
          have ha' := a.1.isLt
          have hb' := b.1.isLt
          omega))⟩
      exact tbS_reflConjSimple_subsingleton (fun j : {j : Fin m // j ∉ T} => φ' j.1)
        hJclosure (fun j => hrefl' j.1) hsub
    · have hk2 : 2 ≤ k := by omega
      let Λ := {j : Fin m // j ∉ T}
      let CJ : Matrix Λ Λ ℤ := fun i j => C i.1 j.1
      have hCJ : GGIntCartan (parMatrix (CoxeterMatrix.B m) {j : Fin m | j ∉ T}) CJ := by
        refine ⟨fun i => hMC.1 i.1, fun i j hij => ?_⟩
        have hij' : i.1 ≠ j.1 := fun h => hij (Subtype.ext h)
        have h := hMC.2 i.1 j.1 hij'
        simpa only [parMatrix_apply] using h
      have hWMJfixed : GGIsWeylMatrixFixed (parMatrix (CoxeterMatrix.B m) {j : Fin m | j ∉ T}) := by
        rw [tbS_parMatrix_B_last hk1 hkm T rfl]
        exact tbS_isWeylMatrixFixed_reindex_B hk1 hkm T rfl hk2
      have hFT : TauCeti.IsFiniteType CJ :=
        isFiniteType_of_ggIsWeylMatrixFixed hWMJfixed hCJ
      have hCJ' : GGIntCartan ((CoxeterMatrix.B k).reindex (tbS_lastEquiv m k hkm T rfl)) CJ := by
        rw [← tbS_parMatrix_B_last hk1 hkm T rfl]
        exact hCJ
      have hdet : CJ.det = 2 := by
        rcases hCJ'.eq_or_eq_transpose ((ggIntCartan_B k).reindex (tbS_lastEquiv m k hkm T rfl))
            ((ggAtMostOneMultipleEdge_B k).reindex (tbS_lastEquiv m k hkm T rfl)) with h | h
        · rw [h, Matrix.det_reindex_self, CartanMatrix.B_det (by omega)]
        · rw [h, Matrix.det_transpose, Matrix.det_reindex_self, CartanMatrix.B_det (by omega)]
      have hdetne : ¬ (p : ℤ) ∣ CJ.det := by
        rw [hdet]
        intro hd
        have hp_dvd : p ∣ 2 := by exact_mod_cast hd
        exact hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).mp hp_dvd)
      have hind : LinearIndependent (ZMod p) (fun j : Λ => h' j.1) := by
        refine linearIndependent_of_det_ne_zero (fun j : Λ => h' j.1) (fun j : Λ => α' j.1) ?_
        have hmap : (Matrix.of fun i j : Λ => α' i.1 (h' j.1)) =
            CJ.map (fun x : ℤ => (x : ZMod p)) := by
          ext i j
          simp only [Matrix.of_apply, Matrix.map_apply]
          change α' i.1 (h' j.1) = (C i.1 j.1 : ZMod p)
          exact hpair' i.1 j.1
        rw [hmap, ← Int.cast_det CJ]
        exact fun h0 => hdetne ((ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp h0)
      haveI : Finite ↥Bs := Finite.of_injective (Subtype.val : ↥Bs → G) Subtype.val_injective
      haveI : Finite V := Finite.of_equiv (Additive ↥Bs) ι.toEquiv
      have hclosed : GGReflClosed (fun j : Λ => ggLin (p := p) ι (φ' j.1)) :=
        ggReflClosed_of_indep (p := p) hp2 hFT hCJ (fun j : Λ => h' j.1)
          (fun j : Λ => α' j.1) (fun i j => hpair' i.1 j.1) hind
          (fun j : Λ => ggLin (p := p) ι (φ' j.1)) (fun j v => hlin' j.1 v)
      exact ggReflConjSimple_of_reflClosed (p := p) ι (fun j : Λ => φ' j.1) hJclosure hclosed
  have hTcard : T.card = m - k := by
    have h1 : T.card = Fintype.card {i : Fin m // i.val < m - k} := by
      simp only [Fintype.card_subtype]
      rfl
    rw [h1]
    let ef : {i : Fin m // i.val < m - k} ≃ Fin (m - k) :=
      { toFun := fun i => ⟨i.1.val, i.2⟩
        invFun := fun a => ⟨⟨a.val, lt_of_lt_of_le a.isLt (Nat.sub_le m k)⟩, a.isLt⟩
        left_inv := fun i => by apply Subtype.ext; apply Fin.ext; rfl
        right_inv := fun a => by apply Fin.ext; rfl }
    exact (Fintype.card_congr ef).trans (Fintype.card_fin _)
  have hT1 : 1 ≤ T.card := by rw [hTcard]; omega
  have hT3 : T.card ≤ 3 := by rw [hTcard]; omega
  have hres := ggTBJWeylParabolicLE3 (p := p) (Bs := Bs) (X := X) (J := J)
    (Λ := Fin m) (M := CoxeterMatrix.B m) (C := C)
    (V := V) (ι := ι) (φ := φ') (h := h') (α := α') (f := f')
    hWM hMC hlin' hrefl' hpair' hf' hclos' T hT1 hT3 hJclosure hWMJ hRC
  constructor
  · intro hc1
    have h1 : T.card = 1 := by rw [hTcard]; omega
    obtain ⟨b, hb⟩ := Finset.card_eq_one.mp h1
    exact hres.1 b hb
  · intro hc2
    exact hres.2 (by rw [hTcard]; omega)

end TypeBDatum

end CFSG.StandardType

end
