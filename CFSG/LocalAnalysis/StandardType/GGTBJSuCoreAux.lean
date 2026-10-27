module

public import CFSG.LocalAnalysis.StandardType.GGTBJSuDefs
public import CFSG.LocalAnalysis.StandardType.GGTBRowPermFrameAux

public section

namespace CFSG.StandardType

open CFSG.Assembly Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  UCoord UModel
open CFSG.SectionRank.OddCover (diagHom)

variable {K : Type} [Field K] {n d p : ℕ} [NeZero p] {u : Kˣ}

@[expose] def ggTBJsuC_coordDiffHom (i i₀ : Fin d) : ↥(sumZero d p) →* Multiplicative (ZMod p) where
  toFun f := Multiplicative.ofAdd (crd f i - crd f i₀)
  map_one' := by
    rw [crd_one, crd_one, sub_self, ofAdd_zero]
  map_mul' f g := by
    rw [crd_mul, crd_mul, ← ofAdd_add]
    congr 1
    abel

@[expose] noncomputable def ggTBJsuC_Phi (I : Finset (Fin d)) (i₀ : Fin d) :
    ↥(sumZero d p) →* (↥(I.erase i₀) → Multiplicative (ZMod p)) where
  toFun f := fun i => Multiplicative.ofAdd (crd f i - crd f i₀)
  map_one' := by
    funext i
    rw [crd_one, crd_one, sub_self, ofAdd_zero]
    rfl
  map_mul' f g := by
    funext i
    rw [Pi.mul_apply, crd_mul, crd_mul, ← ofAdd_add]
    congr 1
    abel

@[simp] theorem ggTBJsuC_Phi_apply (I : Finset (Fin d)) (i₀ : Fin d)
    (f : ↥(sumZero d p)) (i : ↥(I.erase i₀)) :
    ggTBJsuC_Phi I i₀ f i = Multiplicative.ofAdd (crd f i - crd f i₀) :=
  rfl

@[expose] def ggTBJsuC_S0 (I : Finset (Fin d)) : Subgroup ↥(sumZero d p) where
  carrier := {f | ∀ i ∈ I, ∀ j ∈ I, crd f i = crd f j}
  one_mem' := by
    intro i _ j _
    rw [crd_one, crd_one]
  mul_mem' := by
    intro f g hf hg i hi j hj
    rw [crd_mul, crd_mul, hf i hi j hj, hg i hi j hj]
  inv_mem' := by
    intro f hf i hi j hj
    rw [crd_inv, crd_inv, hf i hi j hj]

theorem ggTBJsuC_S0_eq_ker {I : Finset (Fin d)} {i₀ : Fin d} (hi₀ : i₀ ∈ I) :
    ggTBJsuC_S0 (p := p) I = (ggTBJsuC_Phi (d := d) (p := p) I i₀).ker := by
  ext f
  constructor
  · intro hf
    change f ∈ (ggTBJsuC_Phi (d := d) (p := p) I i₀).ker
    rw [MonoidHom.mem_ker]
    funext i
    have hi : (i : Fin d) ∈ I.erase i₀ := i.2
    have h := hf i (Finset.mem_of_mem_erase hi) i₀ hi₀
    rw [ggTBJsuC_Phi_apply, h, sub_self, ofAdd_zero]
    rfl
  · intro hf
    change f ∈ (ggTBJsuC_Phi (d := d) (p := p) I i₀).ker at hf
    rw [MonoidHom.mem_ker] at hf
    intro i hi j hj
    have key : ∀ k ∈ I.erase i₀, crd f k = crd f i₀ := by
      intro k hk
      have h := congrFun hf ⟨k, hk⟩
      rw [ggTBJsuC_Phi_apply] at h
      have h0 : crd f k - crd f i₀ = 0 := Multiplicative.ofAdd.injective (h.trans (ofAdd_zero).symm)
      exact sub_eq_zero.mp h0
    have hi' : crd f i = crd f i₀ := by
      by_cases hii : i = i₀
      · rw [hii]
      · exact key i (Finset.mem_erase.mpr ⟨hii, hi⟩)
    have hj' : crd f j = crd f i₀ := by
      by_cases hjj : j = i₀
      · rw [hjj]
      · exact key j (Finset.mem_erase.mpr ⟨hjj, hj⟩)
    exact hi'.trans hj'.symm

theorem ggTBJsuC_card_target {I : Finset (Fin d)} {i₀ : Fin d} (hi₀ : i₀ ∈ I) :
    Nat.card (↥(I.erase i₀) → Multiplicative (ZMod p)) = p ^ (I.card - 1) := by
  rw [Nat.card_fun, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
  congr 1
  change Nat.card (↑(I.erase i₀) : Set (Fin d)) = I.card - 1
  rw [Nat.card_coe_set_eq, Set.ncard_coe_finset, Finset.card_erase_of_mem hi₀]

theorem ggTBJsuC_card_S0_ge {I : Finset (Fin d)} (hp : p.Prime) (hne : I.Nonempty) :
    p ^ (d - I.card) ≤ Nat.card ↥(ggTBJsuC_S0 (p := p) I) := by
  have hpos : 1 ≤ I.card := Finset.card_pos.mpr hne
  obtain ⟨i₀, hi₀⟩ := hne
  let Φ := ggTBJsuC_Phi (d := d) (p := p) I i₀
  have hcard := Subgroup.card_ker_mul_card_range Φ
  rw [← ggTBJsuC_S0_eq_ker hi₀] at hcard
  have hle' : Nat.card Φ.range ≤ p ^ (I.card - 1) := by
    calc Nat.card Φ.range ≤ Nat.card (↥(I.erase i₀) → Multiplicative (ZMod p)) :=
          Subgroup.card_le_card_group Φ.range
      _ = p ^ (I.card - 1) := ggTBJsuC_card_target hi₀
  rw [ggTBRowPerm_card_sumZero'] at hcard
  have hdI : I.card ≤ d := by simpa using Finset.card_le_univ I
  have hcard_eq : p ^ (d - 1) = p ^ (d - I.card) * p ^ (I.card - 1) := by
    rw [← pow_add]
    congr 1
    omega
  have h_eq : p ^ (d - I.card) * p ^ (I.card - 1) =
      Nat.card Φ.range * Nat.card ↥(ggTBJsuC_S0 (p := p) I) := by
    rw [← hcard_eq]
    rw [mul_comm (Nat.card Φ.range) (Nat.card ↥(ggTBJsuC_S0 (p := p) I))]
    rw [← hcard]
  have hle_mul : p ^ (I.card - 1) * p ^ (d - I.card) ≤
      p ^ (I.card - 1) * Nat.card ↥(ggTBJsuC_S0 (p := p) I) := by
    rw [mul_comm]
    rw [h_eq]
    exact Nat.mul_le_mul_right _ hle'
  exact Nat.le_of_mul_le_mul_left hle_mul (pow_pos hp.pos _)

theorem ggTBJsuC_ker_coordDiffHom {i j : Fin d} (hij : i ≠ j) :
    (ggTBJsuC_coordDiffHom (d := d) (p := p) i j).ker =
      {f : ↥(sumZero d p) | permAutV (Equiv.swap i j) f = f} := by
  ext f
  constructor
  · intro hf
    change f ∈ (ggTBJsuC_coordDiffHom (d := d) (p := p) i j).ker at hf
    rw [MonoidHom.mem_ker] at hf
    have h : (Multiplicative.ofAdd (crd f i - crd f j) : Multiplicative (ZMod p)) = 1 := by
      simpa [ggTBJsuC_coordDiffHom] using hf
    have h0 : crd f i - crd f j = 0 := Multiplicative.ofAdd.injective (h.trans (ofAdd_zero).symm)
    have heq : crd f i = crd f j := sub_eq_zero.mp h0
    refine ext_crd fun k => ?_
    rw [crd_permAutV, Equiv.swap_inv]
    by_cases hk : k = i
    · rw [hk, Equiv.swap_apply_left]
      exact heq.symm
    · by_cases hk' : k = j
      · rw [hk', Equiv.swap_apply_right]
        exact heq
      · rw [Equiv.swap_apply_of_ne_of_ne hk hk']
  · intro hf
    change f ∈ (ggTBJsuC_coordDiffHom (d := d) (p := p) i j).ker
    rw [MonoidHom.mem_ker]
    have heq : crd f i = crd f j := by
      have h := congrArg (fun g => crd g i) hf
      rw [crd_permAutV, Equiv.swap_inv, Equiv.swap_apply_left] at h
      exact h.symm
    change Multiplicative.ofAdd (crd f i - crd f j) = 1
    rw [heq, sub_self, ofAdd_zero]

theorem ggTBJsuC_card_range_coordDiffHom {i j : Fin d} (hp : p.Prime) (hp2 : p ≠ 2) (hij : i ≠ j) :
    Nat.card (ggTBJsuC_coordDiffHom (d := d) (p := p) i j).range = p := by
  let δ := ggTBJsuC_coordDiffHom (d := d) (p := p) i j
  have h2 : δ (rootV i j) = Multiplicative.ofAdd (2 : ZMod p) := by
    change Multiplicative.ofAdd (crd (rootV i j) i - crd (rootV i j) j) = _
    rw [crd_rootV_left hij, crd_rootV_right hij]
    norm_num
  have hne : δ (rootV i j) ≠ 1 := by
    rw [h2]
    intro h
    have h' : (2 : ZMod p) = 0 := Multiplicative.ofAdd.injective (h.trans (ofAdd_zero).symm)
    have hdvd : ¬ p ∣ 2 := by
      intro hd
      have h2p : p = 2 := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp hd
      exact hp2 h2p
    have h'' : ((2 : ℕ) : ZMod p) = 0 := by simpa using h'
    rw [ZMod.natCast_eq_zero_iff] at h''
    exact hdvd h''
  have hmem : Multiplicative.ofAdd (2 : ZMod p) ∈ δ.range := by
    rw [← h2]
    exact ⟨rootV i j, rfl⟩
  have hcard_target : Nat.card (Multiplicative (ZMod p)) = p := by
    rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
  have hdvd : Nat.card δ.range ∣ p := by
    have h := Subgroup.card_subgroup_dvd_card δ.range
    rwa [hcard_target] at h
  have hne_card : Nat.card δ.range ≠ 1 := by
    intro h1
    have hbot : δ.range = ⊥ := by
      rw [Subgroup.eq_bot_iff_card]
      exact h1
    have hmem' := hmem
    rw [hbot] at hmem'
    have h1' : Multiplicative.ofAdd (2 : ZMod p) = 1 := by
      simpa using hmem'
    exact hne (h2.trans h1')
  have h := (Nat.dvd_prime hp).mp hdvd
  cases h with
  | inl h1 => exact absurd h1 hne_card
  | inr hp_eq => exact hp_eq

theorem ggTBJsuC_card_fix_permAutV_swap {i j : Fin d} (hp : p.Prime) (hp2 : p ≠ 2) (hij : i ≠ j) :
    Nat.card {f : ↥(sumZero d p) // permAutV (Equiv.swap i j) f = f} * p = p ^ (d - 1) := by
  let δ := ggTBJsuC_coordDiffHom (d := d) (p := p) i j
  have hker : δ.ker = {f : ↥(sumZero d p) | permAutV (Equiv.swap i j) f = f} :=
    ggTBJsuC_ker_coordDiffHom hij
  have hcard := Subgroup.card_ker_mul_card_range δ
  have hcard_eq : Nat.card ↥δ.ker =
      Nat.card {f : ↥(sumZero d p) | permAutV (Equiv.swap i j) f = f} := by
    apply Nat.card_congr
    exact Equiv.subtypeEquiv (Equiv.refl _) (fun f => Iff.of_eq (congrArg (fun s => s f) hker))
  rw [hcard_eq] at hcard
  have hrange : Nat.card δ.range = p := ggTBJsuC_card_range_coordDiffHom hp hp2 hij
  rw [hrange, ggTBRowPerm_card_sumZero'] at hcard
  exact hcard
