module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenInvolutions
public import CFSG.Quasithin.Background.F7TwoInvG2Root
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8G2LeviA2
public import CFSG.LocalAnalysis.EvenBN.G2.Torus

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.ComponentClassification.UnbalancedCatalog
open CFSG.Quasithin.F7Two.G2Ev CFSG.ComponentClassification.RankTwoExceptional
open scoped commutatorElement


local notation "RA2" => CFSG.LieType.RootSystem.roots
  (CFSG.LieType.Universal.SpecialLinear.isFiniteType_A 2) (∅ : Set (Fin 2))

section Aux

set_option linter.unusedSectionVars false

variable {K : Type} [Field K] [CharP K 2]

private theorem commutatorElement_mem_subgp {G : Type*} [Group G] (H : Subgroup G) {x y : G}
    (hx : x ∈ H) (hy : y ∈ H) : ⁅x, y⁆ ∈ H := by
  rw [commutatorElement_def]
  exact H.mul_mem (H.mul_mem (H.mul_mem hx hy) (H.inv_mem hx)) (H.inv_mem hy)

private theorem comm_rootElt_a_b (s t : K) :
    ⁅rootElt K g2a s, rootElt K g2b t⁆ = rootElt K g2c (s * t) :=
  Subtype.ext (comm_a_b s t)

private theorem comm_rootElt_long {α β : Fin 2 → ℤ} (hα : α ∈ RA2) (hβ : β ∈ RA2)
    (h : α + β ∈ RA2) (s t : K) :
    ⁅rootElt K (a2Long α) s, rootElt K (a2Long β) t⁆ = rootElt K (a2Long (α + β)) (s * t) := by
  have hne : α + β ≠ 0 := by
    intro h0
    rw [h0, mem_rootsA2] at h
    revert h
    decide
  exact Subtype.ext ((commutator_a2Long hα hβ hne s t).1 h)

private theorem comm_rootElt_c_nb (s t : K) :
    ⁅rootElt K g2c s, rootElt K (-g2b) t⁆ = rootElt K g2a (s * t) := by
  have h := comm_rootElt_long (K := K) (α := ![1, 1]) (β := ![0, -1])
    (by rw [mem_rootsA2]; decide) (by rw [mem_rootsA2]; decide) (by rw [mem_rootsA2]; decide) s t
  rwa [a2Long_c, a2Long_nb, show (![1, 1] + ![0, -1] : Fin 2 → ℤ) = ![1, 0] by decide,
    a2Long_a] at h

private theorem comm_rootElt_na_c (s t : K) :
    ⁅rootElt K (-g2a) s, rootElt K g2c t⁆ = rootElt K g2b (s * t) := by
  have h := comm_rootElt_long (K := K) (α := ![-1, 0]) (β := ![1, 1])
    (by rw [mem_rootsA2]; decide) (by rw [mem_rootsA2]; decide) (by rw [mem_rootsA2]; decide) s t
  rwa [a2Long_na, a2Long_c, show (![-1, 0] + ![1, 1] : Fin 2 → ℤ) = ![0, 1] by decide,
    a2Long_b] at h

private theorem comm_rootElt_b_nc (s t : K) :
    ⁅rootElt K g2b s, rootElt K (-g2c) t⁆ = rootElt K (-g2a) (s * t) := by
  have h := comm_rootElt_long (K := K) (α := ![0, 1]) (β := ![-1, -1])
    (by rw [mem_rootsA2]; decide) (by rw [mem_rootsA2]; decide) (by rw [mem_rootsA2]; decide) s t
  rwa [a2Long_b, a2Long_nc, show (![0, 1] + ![-1, -1] : Fin 2 → ℤ) = ![-1, 0] by decide,
    a2Long_na] at h

private theorem comm_rootElt_nc_a (s t : K) :
    ⁅rootElt K (-g2c) s, rootElt K g2a t⁆ = rootElt K (-g2b) (s * t) := by
  have h := comm_rootElt_long (K := K) (α := ![-1, -1]) (β := ![1, 0])
    (by rw [mem_rootsA2]; decide) (by rw [mem_rootsA2]; decide) (by rw [mem_rootsA2]; decide) s t
  rwa [a2Long_nc, a2Long_a, show (![-1, -1] + ![1, 0] : Fin 2 → ℤ) = ![0, -1] by decide,
    a2Long_nb] at h

private theorem comm_rootElt_nb_na (s t : K) :
    ⁅rootElt K (-g2b) s, rootElt K (-g2a) t⁆ = rootElt K (-g2c) (s * t) := by
  have h := comm_rootElt_long (K := K) (α := ![0, -1]) (β := ![-1, 0])
    (by rw [mem_rootsA2]; decide) (by rw [mem_rootsA2]; decide) (by rw [mem_rootsA2]; decide) s t
  rwa [a2Long_nb, a2Long_na, show (![0, -1] + ![-1, 0] : Fin 2 → ℤ) = ![-1, -1] by decide,
    a2Long_nc] at h

private theorem rootElt_mul_mem_of_comm {H : Subgroup ↥(adjointGroup .G2 K)}
    {α β γ : Fin Tag.G2.rank → ℤ}
    (hc : ∀ s t : K, ⁅rootElt K α s, rootElt K β t⁆ = rootElt K γ (s * t))
    {s t : K} (hs : rootElt K α s ∈ H) (ht : rootElt K β t ∈ H) :
    rootElt K γ (s * t) ∈ H := by
  rw [← hc]
  exact commutatorElement_mem_subgp H hs ht

private def LongParam (H : Subgroup ↥(adjointGroup .G2 K)) (t : K) : Prop :=
  rootElt K g2a t ∈ H ∧ rootElt K (-g2a) t ∈ H ∧ rootElt K g2b t ∈ H ∧
    rootElt K (-g2b) t ∈ H ∧ rootElt K g2c t ∈ H ∧ rootElt K (-g2c) t ∈ H

private theorem longParam_of_base {H : Subgroup ↥(adjointGroup .G2 K)} {w : K}
    (ha : rootElt K g2a 1 ∈ H) (hb : rootElt K g2b 1 ∈ H) (hc : rootElt K (-g2c) w ∈ H) :
    LongParam H w := by
  have h1c : rootElt K g2c 1 ∈ H := by
    simpa using rootElt_mul_mem_of_comm comm_rootElt_a_b ha hb
  have hnb : rootElt K (-g2b) w ∈ H := by
    simpa using rootElt_mul_mem_of_comm comm_rootElt_nc_a hc ha
  have hna : rootElt K (-g2a) w ∈ H := by
    simpa using rootElt_mul_mem_of_comm comm_rootElt_b_nc hb hc
  have hb' : rootElt K g2b w ∈ H := by
    simpa using rootElt_mul_mem_of_comm comm_rootElt_na_c hna h1c
  have ha' : rootElt K g2a w ∈ H := by
    simpa using rootElt_mul_mem_of_comm comm_rootElt_c_nb h1c hnb
  have hc' : rootElt K g2c w ∈ H := by
    simpa using rootElt_mul_mem_of_comm comm_rootElt_a_b ha' hb
  exact ⟨ha', hna, hb', hnb, hc', hc⟩

private theorem longParam_mul {H : Subgroup ↥(adjointGroup .G2 K)} {t w : K}
    (ht : LongParam H t) (hw : LongParam H w) : LongParam H (t * w) :=
  ⟨rootElt_mul_mem_of_comm comm_rootElt_c_nb ht.2.2.2.2.1 hw.2.2.2.1,
    rootElt_mul_mem_of_comm comm_rootElt_b_nc ht.2.2.1 hw.2.2.2.2.2,
    rootElt_mul_mem_of_comm comm_rootElt_na_c ht.2.1 hw.2.2.2.2.1,
    rootElt_mul_mem_of_comm comm_rootElt_nc_a ht.2.2.2.2.2 hw.1,
    rootElt_mul_mem_of_comm comm_rootElt_a_b ht.1 hw.2.2.1,
    rootElt_mul_mem_of_comm comm_rootElt_nb_na ht.2.2.2.1 hw.2.1⟩

private theorem longParam_pow {H : Subgroup ↥(adjointGroup .G2 K)} {w : K} (h : LongParam H w)
    (n : ℕ) : LongParam H (w ^ (n + 1)) := by
  induction n with
  | zero => rwa [zero_add, pow_one]
  | succ n ih =>
    rw [pow_succ _ (n + 1)]
    exact longParam_mul ih h

private theorem exists_pow_succ_eq_units [Finite K] {w : Kˣ}
    (hw : ∀ u : Kˣ, u ∈ Subgroup.zpowers w) (u : Kˣ) : ∃ n : ℕ, (w : K) ^ (n + 1) = (u : K) := by
  obtain ⟨n, hn⟩ := mem_powers_iff_mem_zpowers.2 (hw u)
  have hpos : 0 < orderOf w := orderOf_pos w
  refine ⟨n + orderOf w - 1, ?_⟩
  have h2 : w ^ (n + orderOf w) = u := by
    rw [pow_add, pow_orderOf_eq_one, mul_one]
    exact hn
  have h3 := congrArg Units.val h2
  rw [Units.val_pow_eq_pow_val] at h3
  rwa [show n + orderOf w - 1 + 1 = n + orderOf w by omega]

private theorem hasRoot_long_of_generator [Finite K] (H : Subgroup ↥(adjointGroup .G2 K))
    {w : Kˣ} (hw : ∀ u : Kˣ, u ∈ Subgroup.zpowers w)
    (ha : rootElt K g2a 1 ∈ H) (hb : rootElt K g2b 1 ∈ H) (hc : rootElt K (-g2c) (w : K) ∈ H) :
    HasRoot K H g2a ∧ HasRoot K H (-g2a) ∧ HasRoot K H g2b ∧ HasRoot K H (-g2b) ∧
      HasRoot K H g2c ∧ HasRoot K H (-g2c) := by
  have hall : ∀ t : K, LongParam H t := by
    intro t
    by_cases ht : t = 0
    · rw [ht]
      exact ⟨by simp [rootElt_zero], by simp [rootElt_zero], by simp [rootElt_zero],
        by simp [rootElt_zero], by simp [rootElt_zero], by simp [rootElt_zero]⟩
    · obtain ⟨n, hn⟩ := exists_pow_succ_eq_units hw (Units.mk0 t ht)
      rw [Units.val_mk0] at hn
      rw [← hn]
      exact longParam_pow (longParam_of_base ha hb hc) n
  exact ⟨fun x => (hall x).1, fun x => (hall x).2.1, fun x => (hall x).2.2.1,
    fun x => (hall x).2.2.2.1, fun x => (hall x).2.2.2.2.1, fun x => (hall x).2.2.2.2.2⟩

variable (K) in
private noncomputable def torusA (t : Kˣ) : ↥(adjointGroup .G2 K) :=
  ⟨torusElt .G2 K g2ia t, torusElt_mem_adjointGroup _ t⟩

private theorem weylElt_g2ia_eq (t : Kˣ) :
    (⟨weylElt .G2 K g2ia t, weylElt_mem_adjointGroup _ t⟩ : ↥(adjointGroup .G2 K)) =
      rootElt K g2a t * rootElt K (-g2a) ((t⁻¹ : Kˣ) : K) * rootElt K g2a t := by
  refine Subtype.ext ?_
  change weylElt .G2 K g2ia t = pinnedX .G2 K g2a t * pinnedX .G2 K (-g2a) ((t⁻¹ : Kˣ) : K) *
    pinnedX .G2 K g2a t
  rw [g2a_eq_single, pinnedX_single, pinnedX_neg_single, weylElt_eq_xUnit_mul,
    CharTwo.neg_eq]

private theorem torusA_eq (t : Kˣ) :
    torusA K t = ⟨weylElt .G2 K g2ia t, weylElt_mem_adjointGroup _ t⟩ *
      ⟨weylElt .G2 K g2ia (-1), weylElt_mem_adjointGroup _ (-1)⟩ :=
  Subtype.ext rfl

private theorem torusA_mem {H : Subgroup ↥(adjointGroup .G2 K)} (ha : HasRoot K H g2a)
    (ha' : HasRoot K H (-g2a)) (t : Kˣ) : torusA K t ∈ H := by
  have hw : ∀ u : Kˣ,
      (⟨weylElt .G2 K g2ia u, weylElt_mem_adjointGroup _ u⟩ : ↥(adjointGroup .G2 K)) ∈ H := by
    intro u
    rw [weylElt_g2ia_eq]
    exact H.mul_mem (H.mul_mem (ha _) (ha' _)) (ha _)
  rw [torusA_eq]
  exact H.mul_mem (hw t) (hw (-1))

private theorem torusA_conj_rootElt {α : Fin Tag.G2.rank → ℤ} (hα : IsRoot .G2 α) (t : Kˣ)
    (c : K) :
    torusA K t * rootElt K α c * (torusA K t)⁻¹ =
      rootElt K α (((t ^ (∑ j, Tag.G2.cartan g2ia j * α j) : Kˣ) : K) * c) :=
  Subtype.ext (root_torus_conjugation g2ia hα t c)

private theorem torusA_conj_u (t : Kˣ) (c : K) :
    torusA K t * rootElt K g2u c * (torusA K t)⁻¹ = rootElt K g2u ((t : K) * c) := by
  rw [torusA_conj_rootElt isRoot_g2u]
  have h : ∑ j, Tag.G2.cartan g2ia j * g2u j = 1 := by decide
  rw [h, zpow_one]

private theorem torusA_conj_v (t : Kˣ) (c : K) :
    torusA K t * rootElt K g2v c * (torusA K t)⁻¹ = rootElt K g2v c := by
  rw [torusA_conj_rootElt isRoot_g2v]
  have h : ∑ j, Tag.G2.cartan g2ia j * g2v j = 0 := by decide
  rw [h, zpow_zero, Units.val_one, one_mul]

private theorem torusA_conj_nr (t : Kˣ) (c : K) :
    torusA K t * rootElt K (-g2r) c * (torusA K t)⁻¹ = rootElt K (-g2r) ((t : K) * c) := by
  rw [torusA_conj_rootElt (IsRoot.neg isRoot_g2r)]
  have h : ∑ j, Tag.G2.cartan g2ia j * (-g2r) j = 1 := by decide
  rw [h, zpow_one]

variable (K) in
private noncomputable def eElt : ↥(adjointGroup .G2 K) :=
  rootElt K g2r 1 * rootElt K g2a 1 * rootElt K g2r 1

private theorem rootElt_g2a_mul_eElt : rootElt K g2a 1 * eElt K =
    rootElt K g2u 1 * rootElt K g2v 1 * rootElt K g2b 1 * rootElt K g2c 1 := by
  have h : ⁅rootElt K g2a 1, rootElt K g2r 1⁆ = rootElt K g2u (1 * 1) *
      rootElt K g2v (1 * 1 ^ 2) * rootElt K g2b (1 * 1 ^ 3) * rootElt K g2c (1 ^ 2 * 1 ^ 3) :=
    Subtype.ext (comm_a_r 1 1)
  simp only [one_pow, mul_one] at h
  rw [← h, commutatorElement_def, rootElt_inv, rootElt_inv, eElt, mul_assoc, mul_assoc,
    mul_assoc]

private theorem rootElt_u_mul_v_mem {H : Subgroup ↥(adjointGroup .G2 K)} (hb : HasRoot K H g2b)
    (hc : HasRoot K H g2c) (ha : rootElt K g2a 1 ∈ H) (he : eElt K ∈ H) :
    rootElt K g2u 1 * rootElt K g2v 1 ∈ H := by
  have h1 : rootElt K g2a 1 * eElt K ∈ H := H.mul_mem ha he
  rw [rootElt_g2a_mul_eElt] at h1
  have h2 := H.mul_mem h1 (H.inv_mem (H.mul_mem (hb 1) (hc 1)))
  rwa [mul_assoc (rootElt K g2u 1 * rootElt K g2v 1) (rootElt K g2b 1) (rootElt K g2c 1),
    mul_inv_cancel_right] at h2

private theorem rootElt_u_one_add_mem {H : Subgroup ↥(adjointGroup .G2 K)}
    (hT : ∀ t : Kˣ, torusA K t ∈ H) (huv : rootElt K g2u 1 * rootElt K g2v 1 ∈ H) {l : K}
    (hl : l ≠ 0) : rootElt K g2u (1 + l) ∈ H := by
  set t : Kˣ := Units.mk0 l hl with ht
  have h1 : torusA K t * (rootElt K g2u 1 * rootElt K g2v 1) * (torusA K t)⁻¹ ∈ H :=
    H.mul_mem (H.mul_mem (hT t) huv) (H.inv_mem (hT t))
  have e1 : torusA K t * (rootElt K g2u 1 * rootElt K g2v 1) * (torusA K t)⁻¹ =
      rootElt K g2u l * rootElt K g2v 1 := by
    have e2 : torusA K t * (rootElt K g2u 1 * rootElt K g2v 1) * (torusA K t)⁻¹ =
        (torusA K t * rootElt K g2u 1 * (torusA K t)⁻¹) *
          (torusA K t * rootElt K g2v 1 * (torusA K t)⁻¹) := by group
    rw [e2, torusA_conj_u, torusA_conj_v, ht, Units.val_mk0, mul_one]
  rw [e1] at h1
  have h2 := H.mul_mem huv (H.inv_mem h1)
  have e3 : rootElt K g2u 1 * rootElt K g2v 1 * (rootElt K g2u l * rootElt K g2v 1)⁻¹ =
      rootElt K g2u (1 + l) := by
    rw [mul_inv_rev, rootElt_inv, rootElt_inv, rootElt_add, mul_assoc, ← mul_assoc
      (rootElt K g2v 1), rootElt_mul_self, one_mul]
  rwa [e3] at h2

private theorem exists_ne_zero_one_of_four_le_card [Finite K] (hK : 4 ≤ Nat.card K) :
    ∃ s : K, s ≠ 0 ∧ s ≠ 1 := by
  classical
  by_contra h
  have h' : ∀ s : K, s = 0 ∨ s = 1 := fun s => by
    by_cases h0 : s = 0
    · exact Or.inl h0
    · by_cases h1 : s = 1
      · exact Or.inr h1
      · exact absurd ⟨s, h0, h1⟩ h
  have hfin := Fintype.ofFinite K
  have h2 : Nat.card K ≤ 2 := by
    rw [Nat.card_eq_fintype_card]
    calc Fintype.card K ≤ Finset.card ({0, 1} : Finset K) :=
          Finset.card_le_card fun x _ => by simpa using h' x
      _ ≤ 2 := Finset.card_le_two
  omega

private theorem hasRoot_u [Finite K] (hK : 4 ≤ Nat.card K) {H : Subgroup ↥(adjointGroup .G2 K)}
    (hT : ∀ t : Kˣ, torusA K t ∈ H) (huv : rootElt K g2u 1 * rootElt K g2v 1 ∈ H) :
    HasRoot K H g2u := by
  have hne : ∀ x : K, x ≠ 1 → rootElt K g2u x ∈ H := by
    intro x hx
    have hl : 1 + x ≠ 0 := fun h => hx (CharTwo.add_eq_zero.1 h).symm
    have := rootElt_u_one_add_mem hT huv hl
    rwa [CharTwo.add_cancel_left] at this
  intro x
  by_cases hx : x = 1
  · subst hx
    obtain ⟨s, hs0, hs1⟩ := exists_ne_zero_one_of_four_le_card (K := K) hK
    have e : rootElt K g2u 1 = rootElt K g2u s * rootElt K g2u (1 + s) := by
      rw [← rootElt_add, add_comm 1 s, CharTwo.add_cancel_left]
    rw [e]
    exact H.mul_mem (hne s hs1) (hne (1 + s) fun h => hs0 (by linear_combination h))
  · exact hne x hx

private theorem rootReflection_g2a_g2u : rootReflection g2a • g2u = g2r := by
  rw [rootReflection_smul isRoot_g2a]
  exact List.ofFn_injective (by decide +kernel)

private theorem hasRoot_g2r {H : Subgroup ↥(adjointGroup .G2 K)} (ha : HasRoot K H g2a)
    (ha' : HasRoot K H (-g2a)) (hu : HasRoot K H g2u) : HasRoot K H g2r := by
  have h := hasRoot_reflect isRoot_g2a isRoot_g2u ha ha' hu
  rwa [rootReflection_g2a_g2u] at h

private theorem rootReflection_g2b_g2v_eq : rootReflection g2b • g2v = -g2r := by
  rw [rootReflection_smul isRoot_g2b]
  exact List.ofFn_injective (by decide +kernel)

private theorem hasRoot_neg_g2r {H : Subgroup ↥(adjointGroup .G2 K)} (hb : HasRoot K H g2b)
    (hb' : HasRoot K H (-g2b)) (hT : ∀ t : Kˣ, torusA K t ∈ H) (hv : rootElt K g2v 1 ∈ H) :
    HasRoot K H (-g2r) := by
  have hw : wElt K g2b ∈ H := H.mul_mem (H.mul_mem (hb 1) (hb' 1)) (hb 1)
  have h1 : rootElt K (-g2r) 1 ∈ H := by
    have h := H.mul_mem (H.mul_mem hw hv) (H.inv_mem hw)
    rwa [wElt_conj_rootElt isRoot_g2b isRoot_g2v, rootReflection_g2b_g2v_eq] at h
  intro x
  by_cases hx : x = 0
  · rw [hx, rootElt_zero]
    exact H.one_mem
  · have h := H.mul_mem (H.mul_mem (hT (Units.mk0 x hx)) h1) (H.inv_mem (hT (Units.mk0 x hx)))
    rwa [torusA_conj_nr, Units.val_mk0, mul_one] at h

private theorem closure_four_eq_top_of_generator [Finite K] (hK : 4 ≤ Nat.card K) {w : Kˣ}
    (hw : ∀ u : Kˣ, u ∈ Subgroup.zpowers w) :
    Subgroup.closure ({rootElt K g2a 1, rootElt K g2b 1, rootElt K (-g2c) (w : K), eElt K} :
      Set ↥(adjointGroup .G2 K)) = ⊤ := by
  set H : Subgroup ↥(adjointGroup .G2 K) := Subgroup.closure ({rootElt K g2a 1,
    rootElt K g2b 1, rootElt K (-g2c) (w : K), eElt K} : Set ↥(adjointGroup .G2 K)) with hH
  have hd1 : rootElt K g2a 1 ∈ H := Subgroup.subset_closure (by simp)
  have hd2 : rootElt K g2b 1 ∈ H := Subgroup.subset_closure (by simp)
  have hd3 : rootElt K (-g2c) (w : K) ∈ H := Subgroup.subset_closure (by simp)
  have he : eElt K ∈ H := Subgroup.subset_closure (by simp)
  obtain ⟨ha, ha', hb, hb', hc, -⟩ := hasRoot_long_of_generator H hw hd1 hd2 hd3
  have hT := torusA_mem ha ha'
  have huv := rootElt_u_mul_v_mem hb hc hd1 he
  have hu := hasRoot_u hK hT huv
  have hv : rootElt K g2v 1 ∈ H := by
    have h := H.mul_mem (H.inv_mem (hu 1)) huv
    rwa [rootElt_inv, ← mul_assoc, rootElt_mul_self, one_mul] at h
  exact eq_top_of_hasRoot ha ha' (hasRoot_g2r ha ha' hu) (hasRoot_neg_g2r hb hb' hT hv)

private theorem isConj_of_G2Conj {x y : ↥(adjointGroup .G2 K)}
    (h : G2Conj (x : ModGL .G2 K) (y : ModGL .G2 K)) : IsConj x y := by
  obtain ⟨g, hg, hgxy⟩ := h
  rw [isConj_iff]
  exact ⟨⟨g, hg⟩, Subtype.ext hgxy⟩

private theorem isConj_rootElt_a_c : IsConj (rootElt K g2a 1) (rootElt K g2c 1) :=
  isConj_of_G2Conj (G2Conj.a_one one_ne_zero)

private theorem isConj_rootElt_b_c : IsConj (rootElt K g2b 1) (rootElt K g2c 1) :=
  isConj_of_G2Conj (G2Conj.b_one one_ne_zero)

private theorem isConj_rootElt_nc_c {w : K} (hw : w ≠ 0) :
    IsConj (rootElt K (-g2c) w) (rootElt K g2c 1) := by
  have h1 : IsConj (rootElt K (-g2c) w) (rootElt K g2c w) :=
    isConj_iff.2 ⟨n0 K, n0_conj_rootElt_neg isPos_g2c w⟩
  exact h1.trans (isConj_of_G2Conj (G2Conj.c_one hw))

private theorem isConj_eElt_a : IsConj (rootElt K g2a 1) (eElt K) :=
  isConj_iff.2 ⟨rootElt K g2r 1, by rw [eElt, rootElt_inv]⟩

private theorem rootReflection_g2r_g2a : rootReflection g2r • g2a = g2b := by
  rw [rootReflection_smul isRoot_g2r]
  exact List.ofFn_injective (by decide +kernel)

private theorem rootReflection_g2r_g2c : rootReflection g2r • g2c = g2c := by
  rw [rootReflection_smul isRoot_g2r]
  exact List.ofFn_injective (by decide +kernel)

private theorem wElt_g2r_conj_a_c :
    wElt K g2r * (rootElt K g2a 1 * rootElt K g2c 1) * (wElt K g2r)⁻¹ =
      rootElt K g2b 1 * rootElt K g2c 1 := by
  have e1 := wElt_conj_rootElt (K := K) isRoot_g2r isRoot_g2a 1
  have e2 := wElt_conj_rootElt (K := K) isRoot_g2r isRoot_g2c 1
  rw [rootReflection_g2r_g2a] at e1
  rw [rootReflection_g2r_g2c] at e2
  calc wElt K g2r * (rootElt K g2a 1 * rootElt K g2c 1) * (wElt K g2r)⁻¹
      = (wElt K g2r * rootElt K g2a 1 * (wElt K g2r)⁻¹) *
          (wElt K g2r * rootElt K g2c 1 * (wElt K g2r)⁻¹) := by group
    _ = rootElt K g2b 1 * rootElt K g2c 1 := by rw [e1, e2]

private theorem isConj_rootElt_b_mul_c :
    IsConj (rootElt K g2b 1) (rootElt K g2b 1 * rootElt K g2c 1) := by
  have h : ⁅rootElt K g2a 1, rootElt K g2b 1⁆ = rootElt K g2c 1 := by
    rw [comm_rootElt_a_b, mul_one]
  have hbc : Commute (rootElt K g2b 1) (rootElt K g2c 1) := Subtype.ext (commute_b_c 1 1).eq
  refine isConj_iff.2 ⟨rootElt K g2a 1, ?_⟩
  calc rootElt K g2a 1 * rootElt K g2b 1 * (rootElt K g2a 1)⁻¹
      = ⁅rootElt K g2a 1, rootElt K g2b 1⁆ * rootElt K g2b 1 := by
        rw [commutatorElement_def]
        group
    _ = rootElt K g2c 1 * rootElt K g2b 1 := by rw [h]
    _ = rootElt K g2b 1 * rootElt K g2c 1 := hbc.eq.symm

private theorem eElt_mul_c_eq : eElt K * rootElt K g2c 1 =
    rootElt K g2r 1 * (rootElt K g2a 1 * rootElt K g2c 1) * (rootElt K g2r 1)⁻¹ := by
  have hrc : Commute (rootElt K g2r 1) (rootElt K g2c 1) := Subtype.ext (commute_r_c 1 1).eq
  rw [rootElt_inv, eElt]
  calc rootElt K g2r 1 * rootElt K g2a 1 * rootElt K g2r 1 * rootElt K g2c 1
      = rootElt K g2r 1 * rootElt K g2a 1 * (rootElt K g2r 1 * rootElt K g2c 1) := by
        rw [mul_assoc (rootElt K g2r 1 * rootElt K g2a 1) (rootElt K g2r 1)]
    _ = rootElt K g2r 1 * rootElt K g2a 1 * (rootElt K g2c 1 * rootElt K g2r 1) := by
        rw [hrc.eq]
    _ = rootElt K g2r 1 * (rootElt K g2a 1 * rootElt K g2c 1) * rootElt K g2r 1 := by
        simp only [mul_assoc]

private theorem isConj_eElt_mul_c : IsConj (eElt K * rootElt K g2c 1) (rootElt K g2c 1) := by
  have h1 : IsConj (rootElt K g2a 1 * rootElt K g2c 1) (eElt K * rootElt K g2c 1) :=
    isConj_iff.2 ⟨rootElt K g2r 1, eElt_mul_c_eq.symm⟩
  have h2 : IsConj (rootElt K g2a 1 * rootElt K g2c 1) (rootElt K g2b 1 * rootElt K g2c 1) :=
    isConj_iff.2 ⟨wElt K g2r, wElt_g2r_conj_a_c⟩
  exact h1.symm.trans (h2.trans (isConj_rootElt_b_mul_c.symm.trans isConj_rootElt_b_c))

private theorem eElt_comm_c : eElt K * rootElt K g2c 1 = rootElt K g2c 1 * eElt K := by
  have hrc : Commute (rootElt K g2r 1) (rootElt K g2c 1) := Subtype.ext (commute_r_c 1 1).eq
  have hac : Commute (rootElt K g2a 1) (rootElt K g2c 1) := Subtype.ext (commute_a_c 1 1).eq
  exact ((hrc.mul_left hac).mul_left hrc).eq

private theorem rootElt_c_mem_closure (w : K) :
    rootElt K g2c 1 ∈ Subgroup.closure ({rootElt K g2a 1, rootElt K g2b 1, rootElt K (-g2c) w} :
      Set ↥(adjointGroup .G2 K)) := by
  have h : ⁅rootElt K g2a 1, rootElt K g2b 1⁆ = rootElt K g2c 1 := by
    rw [comm_rootElt_a_b, mul_one]
  rw [← h]
  exact commutatorElement_mem_subgp _ (Subgroup.subset_closure (by simp))
    (Subgroup.subset_closure (by simp))

end Aux

theorem g2_exists_long_root_generators (K : Type) [Field K] [Finite K] [CharP K 2]
    (hK : 4 ≤ Nat.card K) :
    ∃ d₁ d₂ d₃ e y : ↥(adjointGroup .G2 K),
      IsConj d₁ ⟨pinnedX .G2 K g2c 1, pinnedX_mem_adjointGroup g2c 1⟩ ∧
      IsConj d₂ ⟨pinnedX .G2 K g2c 1, pinnedX_mem_adjointGroup g2c 1⟩ ∧
      IsConj d₃ ⟨pinnedX .G2 K g2c 1, pinnedX_mem_adjointGroup g2c 1⟩ ∧
      IsConj e ⟨pinnedX .G2 K g2c 1, pinnedX_mem_adjointGroup g2c 1⟩ ∧
      IsConj y ⟨pinnedX .G2 K g2c 1, pinnedX_mem_adjointGroup g2c 1⟩ ∧
      IsConj (e * y) ⟨pinnedX .G2 K g2c 1, pinnedX_mem_adjointGroup g2c 1⟩ ∧
      Subgroup.closure ({d₁, d₂, d₃, e} : Set ↥(adjointGroup .G2 K)) = ⊤ ∧
      y ∈ Subgroup.closure ({d₁, d₂, d₃} : Set ↥(adjointGroup .G2 K)) ∧ e * y = y * e := by
  obtain ⟨w, hw⟩ := IsCyclic.exists_generator (α := Kˣ)
  exact ⟨rootElt K g2a 1, rootElt K g2b 1, rootElt K (-g2c) (w : K), eElt K, rootElt K g2c 1,
    isConj_rootElt_a_c, isConj_rootElt_b_c, isConj_rootElt_nc_c w.ne_zero,
    isConj_eElt_a.symm.trans isConj_rootElt_a_c, IsConj.refl _, isConj_eElt_mul_c,
    closure_four_eq_top_of_generator hK hw, rootElt_c_mem_closure _, eElt_comm_c⟩

end CFSG.RankThree.GF2n.Stroth80
