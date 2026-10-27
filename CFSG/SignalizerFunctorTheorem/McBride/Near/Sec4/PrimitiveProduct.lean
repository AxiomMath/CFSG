module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec4.PermDegBasic
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec4.PermDegProduct

public section

namespace CFSG.SignalizerFunctorTheorem.McBride.Near

universe u v

variable {ι : Type u} {G : ι → Type v} [∀ i, Group (G i)]

theorem eq_bot_of_normal_le_stabilizer {Q : Type*} [Group Q] {Ω : Type*} [MulAction Q Ω]
    [MulAction.IsPretransitive Q Ω] (hfaith : ∀ q : Q, (∀ ω : Ω, q • ω = ω) → q = 1) (a : Ω)
    (N : Subgroup Q) [N.Normal] (hN : N ≤ MulAction.stabilizer Q a) : N = ⊥ := by
  rw [eq_bot_iff]
  intro n hn
  rw [Subgroup.mem_bot]
  refine hfaith n fun ω => ?_
  obtain ⟨q, rfl⟩ := MulAction.exists_smul_eq Q a ω
  have h := hN (Subgroup.Normal.conj_mem inferInstance n hn q⁻¹)
  rw [MulAction.mem_stabilizer_iff, inv_inv] at h
  calc n • q • a = q • (q⁻¹ * n * q) • a := by simp only [mul_smul, smul_inv_smul]
    _ = q • a := by rw [h]

theorem le_normalizer_of_conj {Q : Type*} [Group Q] {X P : Subgroup Q}
    (h : ∀ g ∈ P, ∀ x ∈ X, g * x * g⁻¹ ∈ X) : P ≤ Subgroup.normalizer (X : Set Q) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨h g hg x, fun hx => ?_⟩
  have := h g⁻¹ (inv_mem hg) _ hx
  simpa [mul_assoc] using this

theorem normal_inf_of_sup_eq_top {Q : Type*} [Group Q] {M P T : Subgroup Q} [T.Normal]
    (hMP : M ⊔ P = ⊤) (hcomm : ∀ p ∈ P, ∀ t ∈ T, p * t = t * p) : (M ⊓ T).Normal := by
  refine Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp ?_)
  rw [← hMP]
  refine sup_le (le_normalizer_of_conj fun g hg x hx => ?_)
    (le_normalizer_of_conj fun g hg x hx => ?_)
  · obtain ⟨hxM, hxT⟩ := Subgroup.mem_inf.mp hx
    exact Subgroup.mem_inf.mpr ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hg hxM)
      (Subgroup.inv_mem _ hg), Subgroup.Normal.conj_mem inferInstance x hxT g⟩
  · rw [hcomm g hg x (Subgroup.mem_inf.mp hx).2, mul_inv_cancel_right]
    exact hx

section Primitive

variable {Ω : Type*} [MulAction (∀ i, G i) Ω]

theorem primitive_aux [MulAction.IsPretransitive (∀ i, G i) Ω]
    (hnc : ∀ i, ¬ IsMulCommutative (G i))
    (hfaith : ∀ q : ∀ i, G i, (∀ ω : Ω, q • ω = ω) → q = 1) (a : Ω)
    (hM : IsCoatom (MulAction.stabilizer (∀ i, G i) a)) {i₀ : ι} (hi₀ : ∃ j, j ≠ i₀) :
    Nonempty (MulAction.stabilizer (∀ i, G i) a ≃* G i₀) ∧
      Nonempty (MulAction.stabilizer (∀ i, G i) a ≃* (∀ j : {j // j ≠ i₀}, G j)) := by
  classical
  set M := MulAction.stabilizer (∀ i, G i) a with hMdef
  have hcf : ∀ N : Subgroup (∀ i, G i), N.Normal → N ≤ M → N = ⊥ := fun N _ hN =>
    eq_bot_of_normal_le_stabilizer hfaith a N hN
  let π : (∀ i, G i) →* G i₀ := Pi.evalMonoidHom G i₀
  let ρ : (∀ i, G i) →* (∀ j : {j // j ≠ i₀}, G j) :=
    MonoidHom.pi fun j => Pi.evalMonoidHom G j
  have hnt : ∀ i, ∃ g : G i, g ≠ 1 := fun i => by
    by_contra h
    push Not at h
    exact hnc i (IsMulCommutative.of_comm fun x y => by rw [h x, h y])
  have hπker : ∀ t, t ∈ π.ker ↔ t i₀ = 1 := fun t => MonoidHom.mem_ker
  have hρker : ∀ s, s ∈ ρ.ker ↔ ∀ j, j ≠ i₀ → s j = 1 := fun s => by
    rw [MonoidHom.mem_ker]
    constructor
    · intro h j hj
      exact congrFun h ⟨j, hj⟩
    · intro h
      funext j
      exact h j j.2
  have hcomm : ∀ s ∈ ρ.ker, ∀ t ∈ π.ker, s * t = t * s := by
    intro s hs t ht
    funext i
    by_cases hi : i = i₀
    · subst hi
      simp [(hπker t).mp ht]
    · simp [(hρker s).mp hs i hi]
  have hSne : ρ.ker ≠ ⊥ := by
    obtain ⟨g, hg⟩ := hnt i₀
    intro h
    have hmem : (Pi.mulSingle i₀ g : ∀ i, G i) ∈ ρ.ker :=
      (hρker _).mpr fun j hj => by simp [Pi.mulSingle_eq_of_ne hj]
    rw [h, Subgroup.mem_bot] at hmem
    exact hg (by simpa using congrFun hmem i₀)
  have hTne : π.ker ≠ ⊥ := by
    obtain ⟨j, hj⟩ := hi₀
    obtain ⟨g, hg⟩ := hnt j
    intro h
    have hmem : (Pi.mulSingle j g : ∀ i, G i) ∈ π.ker :=
      (hπker _).mpr (by simp [Pi.mulSingle_eq_of_ne hj.symm])
    rw [h, Subgroup.mem_bot] at hmem
    exact hg (by simpa using congrFun hmem j)
  have hSM : ¬ ρ.ker ≤ M := fun h => hSne (hcf _ inferInstance h)
  have hTM : ¬ π.ker ≤ M := fun h => hTne (hcf _ inferInstance h)
  have hMS : M ⊔ ρ.ker = ⊤ := codisjoint_iff.mp (hM.not_le_iff_codisjoint.mp hSM)
  have hMT : M ⊔ π.ker = ⊤ := codisjoint_iff.mp (hM.not_le_iff_codisjoint.mp hTM)
  have hX1 : M ⊓ π.ker = ⊥ := hcf _ (normal_inf_of_sup_eq_top hMS hcomm) inf_le_left
  have hX2 : M ⊓ ρ.ker = ⊥ :=
    hcf _ (normal_inf_of_sup_eq_top hMT fun t ht s hs => (hcomm s hs t ht).symm) inf_le_left
  refine ⟨⟨MulEquiv.ofBijective (π.comp M.subtype) ⟨?_, ?_⟩⟩,
    ⟨MulEquiv.ofBijective (ρ.comp M.subtype) ⟨?_, ?_⟩⟩⟩
  · rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro m hm
    rw [MonoidHom.mem_ker] at hm
    have : (m : ∀ i, G i) ∈ M ⊓ π.ker := ⟨m.2, hm⟩
    rw [hX1, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.mpr (Subtype.ext this)
  · intro g
    have hmem : (Pi.mulSingle i₀ g : ∀ i, G i) ∈ M ⊔ π.ker := hMT ▸ Subgroup.mem_top _
    obtain ⟨m, hm, t, ht, hmt⟩ := Subgroup.mem_sup_of_normal_right.mp hmem
    refine ⟨⟨m, hm⟩, ?_⟩
    have h1 : π (m * t) = g := by rw [hmt]; simp [π]
    rw [map_mul, MonoidHom.mem_ker.mp ht, mul_one] at h1
    exact h1
  · rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro m hm
    rw [MonoidHom.mem_ker] at hm
    have : (m : ∀ i, G i) ∈ M ⊓ ρ.ker := ⟨m.2, hm⟩
    rw [hX2, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.mpr (Subtype.ext this)
  · intro f
    set q : ∀ i, G i := embSub G (fun i => i ≠ i₀) f with hq
    have hmem : q ∈ M ⊔ ρ.ker := hMS ▸ Subgroup.mem_top _
    obtain ⟨m, hm, s, hs, hms⟩ := Subgroup.mem_sup_of_normal_right.mp hmem
    refine ⟨⟨m, hm⟩, ?_⟩
    have h1 : ρ (m * s) = f := by
      rw [hms]
      funext j
      simp [ρ, hq, embSub_apply_of_pos (fun i => i ≠ i₀) f j.2]
    have h2 : ρ s = 1 := hs
    rw [map_mul, h2, mul_one] at h1
    exact h1

theorem sum_permDeg_le_of_isCoatom [Fintype ι] [∀ i, Finite (G i)] [∀ i, IsSimpleGroup (G i)]
    (hnc : ∀ i, ¬ IsMulCommutative (G i)) [Finite Ω] [MulAction.IsPretransitive (∀ i, G i) Ω]
    (hfaith : ∀ q : ∀ i, G i, (∀ ω : Ω, q • ω = ω) → q = 1) (a : Ω)
    (hM : IsCoatom (MulAction.stabilizer (∀ i, G i) a)) (h2 : 2 ≤ Fintype.card ι) :
    ∑ i, permDeg (G i) ≤ Nat.card Ω := by
  classical
  set M := MulAction.stabilizer (∀ i, G i) a with hMdef
  have hex : ∀ i : ι, ∃ j, j ≠ i := by
    intro i
    by_contra h
    push Not at h
    have : Fintype.card ι ≤ 1 := Fintype.card_le_one_iff.mpr fun x y => (h x).trans (h y).symm
    omega
  obtain ⟨i₀⟩ : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
  have hπ : ∀ i, Nonempty (M ≃* G i) := fun i => (primitive_aux hnc hfaith a hM (hex i)).1
  have hcardG : ∀ i, Nat.card (G i) = Nat.card M := fun i =>
    (Nat.card_congr (hπ i).some.toEquiv).symm
  have hm : 2 ≤ Nat.card M := by
    have : 1 < Nat.card (G i₀) :=
      Finite.one_lt_card_iff_nontrivial.mpr (nontrivial_of_not_isMulCommutative (hnc i₀))
    rw [hcardG i₀] at this
    omega
  obtain ⟨eρ⟩ := (primitive_aux hnc hfaith a hM (hex i₀)).2
  have hP : Nat.card M = Nat.card M ^ Fintype.card {j // j ≠ i₀} := by
    have h1 : Nat.card M = ∏ j : {j // j ≠ i₀}, Nat.card (G j) := by
      rw [Nat.card_congr eρ.toEquiv, Nat.card_pi]
    exact h1.trans (by simp [hcardG])
  have hk : Fintype.card {j // j ≠ i₀} = 1 :=
    Nat.pow_right_injective hm (show Nat.card M ^ Fintype.card {j // j ≠ i₀} = Nat.card M ^ 1 by
      rw [pow_one]; exact hP.symm)
  have hcardι : Fintype.card ι = 2 := by
    have h1 := Fintype.card_subtype_compl (fun j : ι => j = i₀)
    rw [Fintype.card_subtype_eq] at h1
    have h3 : Fintype.card {j // j ≠ i₀} = Fintype.card {x // ¬ x = i₀} := rfl
    omega
  have hQ : Nat.card (∀ i, G i) = Nat.card M ^ 2 := by
    rw [Nat.card_pi]
    simp [hcardG, hcardι]
  have hΩ : Nat.card Ω = Nat.card M := by
    have h1 := M.card_mul_index
    rw [hMdef, MulAction.index_stabilizer_of_transitive] at h1
    rw [hQ, sq] at h1
    have hmpos : 0 < Nat.card M := by omega
    exact Nat.eq_of_mul_eq_mul_left hmpos h1
  have hsum : ∑ i, permDeg (G i) = Fintype.card ι * permDeg M := by
    rw [Finset.sum_congr rfl (fun i _ => (permDeg_congr (hπ i).some).symm)]
    simp
  rw [hsum, hcardι, hΩ]
  have h3 := two_mul_permDeg_le_card (G i₀) (hnc i₀)
  rw [← permDeg_congr (hπ i₀).some, hcardG i₀] at h3
  exact h3

end Primitive

end CFSG.SignalizerFunctorTheorem.McBride.Near
