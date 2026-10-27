module

public import CFSG.Quasithin.H13.A7Coordinates
public import CFSG.Quasithin.H13.A7Hyperplane
public import CFSG.Quasithin.H13.FiveMenu
public import CFSG.Quasithin.Vol2.Ch12Sec2Setting

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.A7

open Equiv Equiv.Perm Subgroup CFSG.Open CFSG.Quasithin.SteinbergCB
open CFSG.LocalAnalysis.ComponentInitial.AlternatingFourGroup (eq_one_of_forall_commute_alternating)
open scoped Pointwise commutatorElement

section Vectors

@[expose] def supp7 (w : Fin 7 → ZMod 2) : Finset (Fin 7) :=
  Finset.univ.filter fun i => w i = 1

theorem mem_supp7 {w : Fin 7 → ZMod 2} {i : Fin 7} : i ∈ supp7 w ↔ w i = 1 := by
  simp [supp7]

theorem card_supp7 (w : Fin 7 → ZMod 2) : (supp7 w).card = hammingNorm w := by
  unfold hammingNorm supp7
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rcases zmodTwo_eq_zero_or_one (w i) with h | h <;> simp [h]

theorem eq_of_supp7_eq {w w' : Fin 7 → ZMod 2} (h : supp7 w = supp7 w') : w = w' := by
  funext i
  have hi : w i = 1 ↔ w' i = 1 := by rw [← mem_supp7, ← mem_supp7, h]
  rcases zmodTwo_eq_zero_or_one (w i) with h1 | h1 <;>
    rcases zmodTwo_eq_zero_or_one (w' i) with h2 | h2
  · rw [h1, h2]
  · exact absurd (hi.2 h2) (by rw [h1]; decide)
  · exact absurd (hi.1 h1) (by rw [h2]; decide)
  · rw [h1, h2]

theorem supp7_permAct7 (g : Perm (Fin 7)) (w : Fin 7 → ZMod 2) :
    supp7 (permAct7 g w) = g • supp7 w := by
  ext i
  rw [mem_supp7, permAct7_apply, Finset.mem_smul_finset]
  constructor
  · intro h
    exact ⟨g⁻¹ i, mem_supp7.2 h, by simp [Perm.smul_def]⟩
  · rintro ⟨j, hj, rfl⟩
    have : g⁻¹ (g • j) = j := by simp [Perm.smul_def]
    rw [this]
    exact mem_supp7.1 hj

theorem exists_alt_permAct7_eq {w w' : Fin 7 → ZMod 2} (h : hammingNorm w = hammingNorm w') :
    ∃ g ∈ alternatingGroup (Fin 7), permAct7 g w = w' := by
  classical
  set k := hammingNorm w with hk
  have : MulAction.IsPretransitive (alternatingGroup (Fin 7)) (Set.powersetCard (Fin 7) k) :=
    Set.powersetCard.isPretransitive_alternatingGroup (by simp)
  let s : Set.powersetCard (Fin 7) k := Set.powersetCard.ofCard (card_supp7 w)
  let t : Set.powersetCard (Fin 7) k := Set.powersetCard.ofCard ((card_supp7 w').trans h.symm)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (alternatingGroup (Fin 7)) s t
  refine ⟨g, g.2, eq_of_supp7_eq ?_⟩
  have h1 : (g : Perm (Fin 7)) • supp7 w = supp7 w' :=
    congrArg (fun u : Set.powersetCard (Fin 7) k => (u : Finset (Fin 7))) hg
  rw [supp7_permAct7, h1]

theorem add_permAct7_threeCycle {w : Fin 7 → ZMod 2} {a b e : Fin 7} (hab : a ≠ b) (hbe : b ≠ e)
    (hae : a ≠ e) (ha : w a = 1) (hb : w b = 1) (he : w e = 0) :
    w + permAct7 (swap a b * swap b e) w = Pi.single a 1 + Pi.single e 1 := by
  funext i
  simp only [Pi.add_apply, permAct7_apply, mul_inv_rev, swap_inv, Perm.mul_apply]
  by_cases hia : i = a
  · subst hia
    rw [swap_apply_left, swap_apply_left, he, ha, Pi.single_eq_same, Pi.single_eq_of_ne hae]
  by_cases hib : i = b
  · subst hib
    rw [swap_apply_right, swap_apply_of_ne_of_ne hab hae, ha, hb,
      Pi.single_eq_of_ne (Ne.symm hab), Pi.single_eq_of_ne hbe]
    decide
  by_cases hie : i = e
  · subst hie
    rw [swap_apply_of_ne_of_ne (Ne.symm hae) (Ne.symm hbe), swap_apply_right, he, hb,
      Pi.single_eq_of_ne (Ne.symm hae), Pi.single_eq_same]
  · rw [swap_apply_of_ne_of_ne hia hib, swap_apply_of_ne_of_ne hib hie,
      Pi.single_eq_of_ne hia, Pi.single_eq_of_ne hie]
    rcases zmodTwo_eq_zero_or_one (w i) with h | h
    · rw [h]
    · rw [h]
      decide

theorem swap_mul_swap_mem_alternating {a b e : Fin 7} (hab : a ≠ b) (hbe : b ≠ e) :
    swap a b * swap b e ∈ alternatingGroup (Fin 7) :=
  mul_mem_alternatingGroup_of_isSwap ⟨a, b, hab, rfl⟩ ⟨b, e, hbe, rfl⟩

theorem eq_sum_pairs_seven {x : Fin 7 → ZMod 2} (hx : x ∈ evenWeight 7) :
    x = ∑ i ∈ Finset.univ.erase (0 : Fin 7), x i • (Pi.single i 1 + Pi.single 0 1) := by
  have hsum : ∑ i, x i = 0 := hx
  funext m
  simp only [Finset.sum_apply, Pi.smul_apply, Pi.add_apply, smul_eq_mul, Pi.single_apply]
  by_cases hm : m = 0
  · subst hm
    have h1 : ∑ i ∈ Finset.univ.erase (0 : Fin 7), x i * ((if (0 : Fin 7) = i then (1 : ZMod 2)
        else 0) + (if (0 : Fin 7) = 0 then 1 else 0)) =
        ∑ i ∈ Finset.univ.erase (0 : Fin 7), x i := by
      refine Finset.sum_congr rfl fun i hi => ?_
      have : (0 : Fin 7) ≠ i := fun h => (Finset.mem_erase.mp hi).1 h.symm
      simp [this]
    rw [h1]
    have h2 := Finset.add_sum_erase Finset.univ x (Finset.mem_univ (0 : Fin 7))
    rw [hsum] at h2
    exact CharTwo.add_eq_zero.mp h2
  · have h1 : ∀ i ∈ Finset.univ.erase (0 : Fin 7), x i * ((if m = i then (1 : ZMod 2) else 0) +
        (if m = 0 then 1 else 0)) = if i = m then x m else 0 := by
      intro i _
      by_cases him : i = m
      · subst him
        simp [hm]
      · have : m ≠ i := fun h => him h.symm
        simp [this, hm, him]
    rw [Finset.sum_congr rfl h1, Finset.sum_ite_eq' (Finset.univ.erase (0 : Fin 7)) m
      (fun _ => x m)]
    simp [Finset.mem_erase, hm]

theorem even_hammingNorm_of_mem_evenWeight {x : Fin 7 → ZMod 2} (hx : x ∈ evenWeight 7) :
    Even (hammingNorm x) := by
  classical
  have hx' : ∑ i, x i = 0 := hx
  rw [← card_supp7]
  have hpar : (((supp7 x).card : ℕ) : ZMod 2) = 0 := by
    rw [← hx']
    have h1 : ∀ i, x i = if x i = 1 then (1 : ZMod 2) else 0 := fun i => by
      rcases zmodTwo_eq_zero_or_one (x i) with h | h <;> simp [h]
    conv_rhs => rw [Finset.sum_congr rfl (fun i _ => h1 i)]
    rw [Finset.sum_boole]
    rfl
  exact (ZMod.natCast_eq_zero_iff_even).1 hpar

theorem evenWeight7_irreducible (W : Submodule (ZMod 2) (Fin 7 → ZMod 2))
    (hWE : W ≤ evenWeight 7)
    (hW : ∀ σ ∈ alternatingGroup (Fin 7), ∀ w ∈ W, permAct7 σ w ∈ W) :
    W = ⊥ ∨ W = evenWeight 7 := by
  classical
  by_cases hbot : W = ⊥
  · exact Or.inl hbot
  right
  refine le_antisymm hWE fun x hx => ?_
  obtain ⟨w, hwW, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
  have hwE : ∑ i, w i = 0 := hWE hwW
  set S := supp7 w with hS
  have hSeven : Even S.card := by
    rw [hS, card_supp7]
    exact even_hammingNorm_of_mem_evenWeight (hWE hwW)
  have hS0 : S.card ≠ 0 := by
    intro h0
    apply hw0
    funext i
    rcases zmodTwo_eq_zero_or_one (w i) with h | h
    · exact h
    · exfalso
      have : i ∈ S := mem_supp7.2 h
      rw [Finset.card_eq_zero.1 h0] at this
      simp at this
  have hS7 : S.card ≤ 7 := by
    have := Finset.card_le_univ S
    simpa using this
  have hS2 : 1 < S.card := by
    obtain ⟨m, hm⟩ := hSeven
    omega
  have hS6 : S.card < 7 := by
    obtain ⟨m, hm⟩ := hSeven
    omega
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.1 hS2
  obtain ⟨e, he⟩ : ∃ e, e ∉ S := by
    by_contra hcon
    push Not at hcon
    have : S = Finset.univ := Finset.eq_univ_of_forall hcon
    rw [this, Finset.card_univ, Fintype.card_fin] at hS6
    omega
  have hwa : w a = 1 := mem_supp7.1 ha
  have hwb : w b = 1 := mem_supp7.1 hb
  have hwe : w e = 0 := by
    rcases zmodTwo_eq_zero_or_one (w e) with h | h
    · exact h
    · exact absurd (mem_supp7.2 h) he
  have hbe : b ≠ e := fun h => he (h ▸ hb)
  have hae : a ≠ e := fun h => he (h ▸ ha)
  have hpair0 : Pi.single a 1 + Pi.single e 1 ∈ W := by
    rw [← add_permAct7_threeCycle hab hbe hae hwa hwb hwe]
    exact W.add_mem hwW (hW _ (swap_mul_swap_mem_alternating hab hbe) w hwW)
  have hpair : ∀ i j : Fin 7, i ≠ j → (Pi.single i 1 + Pi.single j 1 : Fin 7 → ZMod 2) ∈ W := by
    intro i j hij
    have hnorm : ∀ {p q : Fin 7}, p ≠ q →
        hammingNorm (Pi.single p 1 + Pi.single q 1 : Fin 7 → ZMod 2) = 2 := by
      intro p q hpq
      exact hammingNorm_pair p q hpq
    obtain ⟨g, hg, hgw⟩ := exists_alt_permAct7_eq ((hnorm hae).trans (hnorm hij).symm)
    rw [← hgw]
    exact hW g hg _ hpair0
  rw [eq_sum_pairs_seven hx]
  refine W.sum_mem fun i hi => W.smul_mem _ (hpair i 0 (Finset.mem_erase.1 hi).1)

theorem evenWeight7_fixed_eq_zero {x : Fin 7 → ZMod 2} (hx : x ∈ evenWeight 7)
    (hfix : ∀ σ ∈ alternatingGroup (Fin 7), permAct7 σ x = x) : x = 0 := by
  have hx' : ∑ i, x i = 0 := hx
  have h1 : permAct7 (swap 0 1 * swap 1 2) x = x := hfix _ threeCycle_mem
  have h2 : permAct7 (swap 2 3 * swap 3 4) x = x :=
    hfix _ (swap_mul_swap_mem_alternating (by decide) (by decide))
  have h3 : permAct7 (swap 4 5 * swap 5 6) x = x :=
    hfix _ (swap_mul_swap_mem_alternating (by decide) (by decide))
  clear hfix hx
  revert h1 h2 h3 hx'
  revert x
  decide +kernel

end Vectors

section Module

variable {G : Type} [Group G] {T L V : Subgroup G} {ψ : V ≃* Multiplicative (evenWeight 7)}

theorem A7NatConfig.eq_bot_or_eq_of_invariant [Finite G] (h : A7NatConfig T L V ψ)
    {J : Subgroup G} (hJV : J ≤ V) (hLJ : L ≤ normalizer (J : Set G)) : J = ⊥ ∨ J = V := by
  classical
  have hinv : ∀ σ ∈ alternatingGroup (Fin 7), ∀ e ∈ imgSub ψ J, permAct7 σ e ∈ imgSub ψ J := by
    intro σ hσ e he
    obtain ⟨x, hxJ, rfl⟩ := he
    obtain ⟨l, hl, hact⟩ := h.Lonto σ hσ
    let y : V := ⟨l * x * l⁻¹, (mem_normalizer_iff.1 (h.L_le hl) x).1 x.2⟩
    refine ⟨y, (mem_normalizer_iff.1 (hLJ hl) x).1 hxJ, ?_⟩
    exact hact x y rfl
  have hle : imgSub ψ J ≤ evenWeight 7 := by
    rintro _ ⟨x, -, rfl⟩
    exact vec_mem ψ x
  have hcardJ : Nat.card (imgSub ψ J) = Nat.card J := by
    rw [nat_card_imgSub, inf_eq_right.2 hJV]
  rcases evenWeight7_irreducible _ hle hinv with h0 | h1
  · left
    rw [h0] at hcardJ
    have : Nat.card J = 1 := by rw [← hcardJ]; simp
    exact (card_eq_one).1 this
  · right
    rw [h1, nat_card_evenWeight_seven] at hcardJ
    exact eq_of_le_of_card_ge hJV (by rw [← hcardJ, nat_card_of_vec ψ])

theorem A7NatConfig.inf_centralizer_eq_bot [Finite G] (h : A7NatConfig T L V ψ) :
    V ⊓ centralizer (L : Set G) = ⊥ := by
  have hLN : L ≤ normalizer ((V ⊓ centralizer (L : Set G) : Subgroup G) : Set G) := by
    intro l hl
    have hl' : l ∈ normalizer ((centralizer (L : Set G) : Subgroup G) : Set G) := by
      rw [mem_normalizer_iff]
      intro x
      constructor
      · intro hx
        rwa [show l * x * l⁻¹ = x by rw [mem_centralizer_iff.1 hx l hl]; group]
      · intro hx
        have : l * x * l⁻¹ = x := by
          have h1 := mem_centralizer_iff.1 hx l hl
          calc l * x * l⁻¹ = l⁻¹ * (l * (l * x * l⁻¹)) := by group
            _ = l⁻¹ * ((l * x * l⁻¹) * l) := by rw [h1]
            _ = x := by group
        rwa [this] at hx
    rw [mem_normalizer_iff] at hl' ⊢
    have hlV := mem_normalizer_iff.1 (h.L_le hl)
    intro x
    exact ⟨fun ⟨h1, h2⟩ => ⟨(hlV x).1 h1, (hl' x).1 h2⟩,
      fun ⟨h1, h2⟩ => ⟨(hlV x).2 h1, (hl' x).2 h2⟩⟩
  rcases h.eq_bot_or_eq_of_invariant inf_le_left hLN with h0 | h1
  · exact h0
  · exfalso
    apply h.not_le_centralizer
    intro l hl
    rw [mem_centralizer_iff]
    intro v hv
    have hv' : v ∈ V ⊓ centralizer (L : Set G) := by rw [h1]; exact hv
    have hvC : v ∈ centralizer (L : Set G) := hv'.2
    exact (mem_centralizer_iff.1 hvC l hl).symm

theorem A7NatConfig.commutator_eq [Finite G] (h : A7NatConfig T L V ψ) : ⁅V, L⁆ = V := by
  classical
  have hle : ⁅V, L⁆ ≤ V := by
    rw [commutator_le]
    intro v hv l hl
    rw [commutatorElement_def, show v * l * v⁻¹ * l⁻¹ = v * (l * v⁻¹ * l⁻¹) by group]
    exact mul_mem hv ((mem_normalizer_iff.1 (h.L_le hl) v⁻¹).1 (inv_mem hv))
  refine le_antisymm hle ?_
  have hpair : ∀ a e : Fin 7, a ≠ e →
      (Pi.single a 1 + Pi.single e 1 : Fin 7 → ZMod 2) ∈ imgSub ψ ⁅V, L⁆ := by
    intro a e hae
    obtain ⟨b, hba, hbe⟩ : ∃ b : Fin 7, b ≠ a ∧ b ≠ e := by
      by_contra hcon
      push Not at hcon
      have h3 : (Finset.univ : Finset (Fin 7)) ⊆ {a, e} := fun x _ => by
        by_cases hxa : x = a
        · simp [hxa]
        · simp [hcon x hxa]
      have := Finset.card_le_card h3
      rw [Finset.card_univ, Fintype.card_fin] at this
      have h4 := Finset.card_le_two (a := a) (b := e)
      omega
    have hσ := swap_mul_swap_mem_alternating (Ne.symm hba) hbe
    obtain ⟨l, hl, hact⟩ := h.Lonto _ hσ
    obtain ⟨x, hx⟩ := exists_vec_eq ψ
      (show (Pi.single a 1 + Pi.single b 1 : Fin 7 → ZMod 2) ∈ evenWeight 7 by
        rw [mem_evenWeight]
        simp only [Pi.add_apply, Finset.sum_add_distrib, Finset.sum_pi_single', Finset.mem_univ,
          ite_true]
        decide)
    let y : V := ⟨l * x * l⁻¹, (mem_normalizer_iff.1 (h.L_le hl) x).1 x.2⟩
    have hy := hact x y rfl
    refine ⟨x * y⁻¹, ?_, ?_⟩
    · have : ((x * y⁻¹ : V) : G) = ⁅(x : G), l⁆ := by
        simp only [y, Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def]
        group
      rw [this]
      exact commutator_mem_commutator x.2 hl
    · rw [vec_mul, vec_inv, hy, hx]
      have hw : (Pi.single a 1 + Pi.single b 1 : Fin 7 → ZMod 2) + permAct7 (swap a b * swap b e)
          (Pi.single a 1 + Pi.single b 1) = Pi.single a 1 + Pi.single e 1 :=
        add_permAct7_threeCycle (Ne.symm hba) hbe hae (by simp [Ne.symm hba]) (by simp [hba])
          (by simp [hae, Ne.symm hbe])
      exact hw
  have hE : evenWeight 7 ≤ imgSub ψ ⁅V, L⁆ := by
    intro x hx
    rw [eq_sum_pairs_seven hx]
    exact Submodule.sum_mem _ fun i hi =>
      Submodule.smul_mem _ _ (hpair i 0 (Finset.mem_erase.1 hi).1)
  have hcard : Nat.card V ≤ Nat.card (⁅V, L⁆ : Subgroup G) := by
    rw [nat_card_of_vec ψ, ← nat_card_evenWeight_seven]
    calc Nat.card (evenWeight 7) ≤ Nat.card (imgSub ψ ⁅V, L⁆) :=
          Nat.card_le_card_of_injective (Submodule.inclusion hE) (Submodule.inclusion_injective hE)
      _ = Nat.card (V ⊓ ⁅V, L⁆ : Subgroup G) := nat_card_imgSub ψ _
      _ = Nat.card (⁅V, L⁆ : Subgroup G) := by rw [inf_eq_right.2 hle]
  exact (eq_of_le_of_card_ge hle hcard).symm.le

end Module

theorem eq_bot_of_isPGroup_of_normal_alternating {N : Subgroup (Perm (Fin 7))}
    (hNA : N ≤ alternatingGroup (Fin 7)) (hN2 : IsPGroup 2 N)
    (hNn : ∀ σ ∈ alternatingGroup (Fin 7), ∀ n ∈ N, σ * n * σ⁻¹ ∈ N) : N = ⊥ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsimple : IsSimpleGroup (alternatingGroup (Fin 7)) :=
    alternatingGroup.isSimpleGroup (by simp)
  have hNn' : (N.subgroupOf (alternatingGroup (Fin 7))).Normal := by
    constructor
    intro n hn g
    rw [mem_subgroupOf] at hn ⊢
    exact hNn g g.2 n hn
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.subgroupOf (alternatingGroup (Fin 7))) with
    h | h
  · rw [eq_bot_iff]
    intro n hn
    have : (⟨n, hNA hn⟩ : alternatingGroup (Fin 7)) ∈ N.subgroupOf (alternatingGroup (Fin 7)) :=
      hn
    rw [h, mem_bot] at this
    exact (mem_bot).2 (congrArg Subtype.val this)
  · exfalso
    have hle : alternatingGroup (Fin 7) ≤ N := by
      intro σ hσ
      have : (⟨σ, hσ⟩ : alternatingGroup (Fin 7)) ∈ N.subgroupOf (alternatingGroup (Fin 7)) :=
        h ▸ mem_top _
      exact this
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 (hN2.to_le hle)
    rw [coord_card_alternating_seven] at hk
    have h3 : 3 ∣ 2 ^ k := hk ▸ (by decide : 3 ∣ 2520)
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
    omega

section Reduced

variable {G : Type} [Group G] {T L V : Subgroup G} {ψ : V ≃* Multiplicative (evenWeight 7)}

theorem isElementaryAbelian_of_vec (ψ : V ≃* Multiplicative (evenWeight 7)) :
    CFSG.IsElementaryAbelian 2 V :=
  { toIsMulCommutative := ⟨⟨fun a b => mul_comm_of_vec ψ a b⟩⟩
    exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x => by
      rw [pow_two]
      exact sq_eq_one_of_vec ψ x }

theorem A7NatConfig.le_reducedAggregate [Finite G] (h : A7NatConfig T L V ψ) :
    V ≤ reducedAggregate (L ⊔ T) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set X := L ⊔ T with hX
  have hXV : X ≤ normalizer (V : Set G) := sup_le h.L_le h.T_le
  have hVX : V ≤ X := h.le_T.trans le_sup_right
  set VX := V.subgroupOf X with hVXdef
  have hVXn : VX.Normal := (normal_subgroupOf_iff_le_normalizer hVX).2 hXV
  have hVXel : CFSG.IsElementaryAbelian 2 VX := by
    have := isElementaryAbelian_of_vec ψ
    exact IsElementaryAbelian.subgroupOf hVX
  have hXact : ∀ x ∈ X, ∃ σ, IsCoordAct ψ x σ := fun x hx => h.Nact x (hXV hx)
  set ρ := coordRep ψ hXV hXact with hρ
  have hker : ∀ x : X, ρ x = 1 ↔ x ∈ centralizer (VX : Set X) := by
    intro x
    rw [coordRep_eq_one_iff, mem_centralizer_iff, mem_centralizer_iff]
    constructor
    · intro hx v hv
      have hv' : (v : G) ∈ V := hv
      exact Subtype.ext (hx v hv')
    · intro hx v hv
      exact congrArg Subtype.val (hx ⟨v, hVX hv⟩ (show (⟨v, hVX hv⟩ : X) ∈ VX from hv))
  have hAimg : ∀ σ ∈ alternatingGroup (Fin 7), ∃ x : X, ρ x = σ := by
    intro σ hσ
    obtain ⟨l, hl, hact⟩ := h.Lonto σ hσ
    have hlX : l ∈ X := le_sup_left (b := T) hl
    exact ⟨⟨l, hlX⟩, IsCoordAct.unique ψ (hXV hlX) (coordRep_spec ψ hXV hXact ⟨l, hlX⟩) hact⟩
  have hmem : VX ∈ primeReducedFamily X 2 := by
    refine ⟨hVXn, hVXel, ?_⟩
    set C := centralizer (VX : Set X) with hC
    set π := QuotientGroup.mk' C with hπ
    set Kt := (CFSG.pCore 2 (X ⧸ C)).comap π with hKt
    have hKtn : Kt.Normal := (CFSG.pCore_normal (p := 2) (G := X ⧸ C)).comap π
    have hKt2 : ∀ k ∈ Kt, ∃ a : ℕ, ρ k ^ 2 ^ a = 1 := by
      intro k hk
      obtain ⟨a, ha⟩ := (CFSG.pCore_isPGroup (p := 2) (G := X ⧸ C)) ⟨π k, hk⟩
      refine ⟨a, ?_⟩
      have h1 : π (k ^ 2 ^ a) = 1 := by
        rw [map_pow]
        exact congrArg Subtype.val ha
      rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
      rw [← map_pow]
      exact (hker _).2 h1
    set N : Subgroup (Perm (Fin 7)) := Kt.map ρ ⊓ alternatingGroup (Fin 7) with hNdef
    have hN : N = ⊥ := by
      refine eq_bot_of_isPGroup_of_normal_alternating inf_le_right ?_ ?_
      · rintro ⟨n, ⟨k, hk, rfl⟩, -⟩
        obtain ⟨a, ha⟩ := hKt2 k hk
        exact ⟨a, Subtype.ext ha⟩
      · intro σ hσ n hn
        obtain ⟨⟨k, hk, rfl⟩, hnA⟩ := mem_inf.1 hn
        obtain ⟨x, rfl⟩ := hAimg σ hσ
        refine mem_inf.2 ⟨⟨x * k * x⁻¹, hKtn.conj_mem k hk x, by rw [map_mul, map_mul, map_inv]⟩,
          ?_⟩
        exact (alternatingGroup.normal (α := Fin 7)).conj_mem _ hnA _
    have hcomm : ∀ k ∈ Kt, ∀ c ∈ alternatingGroup (Fin 7), ρ k * c = c * ρ k := by
      intro k hk c hc
      obtain ⟨x, hx⟩ := hAimg c hc
      have hm : ρ (k * x * k⁻¹ * x⁻¹) ∈ N := by
        refine mem_inf.2 ⟨⟨k * x * k⁻¹ * x⁻¹, ?_, rfl⟩, ?_⟩
        · rw [show k * x * k⁻¹ * x⁻¹ = k * (x * k⁻¹ * x⁻¹) by group]
          exact mul_mem hk (hKtn.conj_mem k⁻¹ (inv_mem hk) x)
        · rw [map_mul, map_mul, map_mul, map_inv, map_inv, hx]
          exact mul_mem ((alternatingGroup.normal (α := Fin 7)).conj_mem c hc _) (inv_mem hc)
      rw [hN, mem_bot, map_mul, map_mul, map_mul, map_inv, map_inv, hx] at hm
      calc ρ k * c = ρ k * c * (ρ k)⁻¹ * c⁻¹ * (c * ρ k) := by group
        _ = c * ρ k := by rw [hm, one_mul]
    have hKtC : Kt ≤ C := by
      intro k hk
      rw [← hker]
      exact eq_one_of_forall_commute_alternating (by simp) (hcomm k hk)
    rw [eq_bot_iff]
    intro y hy
    obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective C y
    have hk : k ∈ Kt := hy
    rw [mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hKtC hk
  have hle := le_sSup hmem
  calc V = VX.map X.subtype := by rw [hVXdef, subgroupOf_map_subtype, inf_eq_left.2 hVX]
    _ ≤ (primeReducedAggregate X 2).map X.subtype := map_mono hle

end Reduced

section IrrPlus

variable {G : Type} [Group G] {T L V : Subgroup G} {ψ : V ≃* Multiplicative (evenWeight 7)}

theorem A7NatConfig.isIrrPlusIn [Finite G] (h : A7NatConfig T L V ψ) :
    IsIrrPlusIn L (reducedAggregate (L ⊔ T)) T V := by
  have hV1 : V ≠ ⊥ := by
    intro hV
    have h64 := nat_card_of_vec ψ
    rw [hV, card_bot] at h64
    omega
  have hC := h.inf_centralizer_eq_bot
  refine ⟨h.le_reducedAggregate, hV1, h.L_le, h.commutator_eq, ?_, ?_, ?_⟩
  · rw [hC]
    exact bot_lt_iff_ne_bot.2 hV1
  · intro J _ hJV hLJ
    rcases h.eq_bot_or_eq_of_invariant hJV hLJ with h0 | h1
    · left
      rw [h0, hC]
    · exact Or.inr h1
  · intro J _ hJ _ _
    have hcl : conjClosure V T = V :=
      le_antisymm (conjClosure_le fun t ht v hv => (mem_normalizer_iff.1 (h.T_le ht) v).1 hv)
        (le_conjClosure V T)
    rw [hcl] at hJ
    exact hJ

theorem A7NatConfig.hyp1223 [Finite G] (h : A7NatConfig T L V ψ) (hs : IsSimpleGroup G)
    (hnab : ∃ a b : G, a * b ≠ b * a) (hQTKE : QuasithinUnique.quasithinIsQTKECat G)
    (hT : quasithinIsSylowTwo T) (hex : ¬ QT13Excluded G) (hmax : quasithinIsMaximalLocal T L)
    (hf : quasithinIsFaithfulLocal T L) (hq : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L)) :
    Hyp1223 G T L V where
  simple := hs
  nonabelian := hnab
  qtke := hQTKE
  sylow := hT
  notAlt := fun h' => hex (qt13Excluded_of_alt12_2_2 h')
  maximal := hmax
  faithful := hf
  quasisimple := hq
  normalizes := h.T_le.trans h.NM
  irrPlus := h.isIrrPlusIn

end IrrPlus

end CFSG.Quasithin.H13.A7
