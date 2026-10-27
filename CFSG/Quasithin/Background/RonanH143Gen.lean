module

public import CFSG.Quasithin.Background.RonanH143Vocab

public section

open scoped Pointwise

namespace CFSG.Quasithin.RonanH143

open CFSG.Open CFSG.Quasithin

theorem exists_labAct {G α : Type*} [Group G] [MulAction G α] {n : ℕ} (X : Fin n → α)
    (hX : Function.Injective X) (H : Subgroup G) (hH : ∀ g ∈ H, ∀ i, ∃ j, g • X i = X j) :
    ∃ π : ↥H →* Equiv.Perm (Fin n), ∀ (g : ↥H) (i : Fin n), X (π g i) = (g : G) • X i := by
  have hc : ∀ g : ↥H, ∀ i, ∃ j, (g : G) • X i = X j := fun g i => hH (g : G) g.2 i
  choose f hf using hc
  have hmul : ∀ g h : ↥H, ∀ i, f (g * h) i = f g (f h i) := by
    intro g h i
    apply hX
    rw [← hf (g * h) i, ← hf g (f h i), ← hf h i, Subgroup.coe_mul, mul_smul]
  have hone : ∀ i, f 1 i = i := by
    intro i
    apply hX
    rw [← hf 1 i, Subgroup.coe_one, one_smul]
  have hinv : ∀ g : ↥H, ∀ i, f g⁻¹ (f g i) = i := by
    intro g i
    apply hX
    rw [← hf g⁻¹ (f g i), ← hf g i, Subgroup.coe_inv, inv_smul_smul]
  have hinv' : ∀ g : ↥H, ∀ i, f g (f g⁻¹ i) = i := by
    intro g i
    apply hX
    rw [← hf g (f g⁻¹ i), ← hf g⁻¹ i, Subgroup.coe_inv, smul_inv_smul]
  refine ⟨{ toFun := fun g =>
              { toFun := f g
                invFun := f g⁻¹
                left_inv := hinv g
                right_inv := hinv' g }
            map_one' := Equiv.ext hone
            map_mul' := fun g h => Equiv.ext (hmul g h) }, fun g i => (hf g i).symm⟩

theorem labAct_eq_of_smul {G α : Type*} [Group G] [MulAction G α] {n : ℕ} (X : Fin n → α)
    (hX : Function.Injective X) (H : Subgroup G) (π : ↥H →* Equiv.Perm (Fin n))
    (hπ : ∀ (g : ↥H) (i : Fin n), X (π g i) = (g : G) • X i) (g : ↥H)
    (σ : Equiv.Perm (Fin n)) (h : ∀ i, (g : G) • X i = X (σ i)) : π g = σ :=
  Equiv.ext fun i => hX ((hπ g i).trans (h i))

theorem card_eq_card_ker_mul {G : Type*} [Group G] [Finite G] {n : ℕ}
    (π : G →* Equiv.Perm (Fin n)) (hπ : π.range = ⊤) :
    Nat.card G = Nat.card π.ker * n.factorial := by
  have h1 := Subgroup.card_ker_mul_card_range π
  rw [hπ, Subgroup.card_top, Nat.card_perm, Nat.card_fin] at h1
  exact h1.symm

theorem ker_eq_of_card_le {G : Type*} [Group G] [Finite G] {n : ℕ}
    (π : G →* Equiv.Perm (Fin n)) (hπ : π.range = ⊤) (N : Subgroup G) (hN : N ≤ π.ker)
    (hc : Nat.card G ≤ Nat.card N * n.factorial) : π.ker = N := by
  have h2 := card_eq_card_ker_mul π hπ
  have hfac : 0 < n.factorial := Nat.factorial_pos n
  rw [h2] at hc
  have hle : Nat.card π.ker ≤ Nat.card N := Nat.le_of_mul_le_mul_right hc hfac
  exact (Subgroup.eq_of_le_of_card_ge hN hle).symm

theorem card_mul_factorial_le {G : Type*} [Group G] [Finite G] {n : ℕ}
    (π : G →* Equiv.Perm (Fin n)) (C N : Subgroup G) (hC : C.map π = ⊤) (hNC : N ≤ C)
    (hNk : N ≤ π.ker) : Nat.card N * n.factorial ≤ Nat.card C := by
  have hrange : (π.comp C.subtype).range = ⊤ := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
    exact hC
  have h2 := card_eq_card_ker_mul (π.comp C.subtype) hrange
  have hle : N.subgroupOf C ≤ (π.comp C.subtype).ker := by
    intro x hx
    exact MonoidHom.mem_ker.mpr (MonoidHom.mem_ker.mp (hNk (Subgroup.mem_subgroupOf.mp hx)))
  have hcardN : Nat.card (N.subgroupOf C) = Nat.card N :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNC).toEquiv
  have hle2 : Nat.card (N.subgroupOf C) ≤ Nat.card (π.comp C.subtype).ker :=
    Subgroup.card_le_of_le hle
  calc Nat.card N * n.factorial
      = Nat.card (N.subgroupOf C) * n.factorial := by rw [hcardN]
    _ ≤ Nat.card (π.comp C.subtype).ker * n.factorial := Nat.mul_le_mul hle2 le_rfl
    _ = Nat.card C := h2.symm

theorem map_closure_eq_top_of_cycle_swap {G : Type*} [Group G] {n : ℕ}
    (π : G →* Equiv.Perm (Fin n)) (σ : Equiv.Perm (Fin n)) (hσ : σ.IsCycle)
    (hs : σ.support = ⊤) (x : Fin n) (g₁ g₂ : G) (h1 : π g₁ = σ)
    (h2 : π g₂ = Equiv.swap x (σ x)) : (Subgroup.closure ({g₁, g₂} : Set G)).map π = ⊤ := by
  have hs' : σ.support = Finset.univ := hs.trans Finset.top_eq_univ
  have key := Equiv.Perm.closure_cycle_adjacent_swap hσ hs' x
  rw [MonoidHom.map_closure, Set.image_pair, h1, h2, key]

theorem alternatingGroup_le_map_of_index_le_two {G : Type*} [Group G] [Finite G] {n : ℕ}
    (π : G →* Equiv.Perm (Fin n)) (hπ : π.range = ⊤) (H : Subgroup G) (hH : H.index ≤ 2) :
    alternatingGroup (Fin n) ≤ H.map π := by
  have hsurj : Function.Surjective π := MonoidHom.range_eq_top.mp hπ
  have hdvd : (H.map π).index ∣ H.index := H.index_map_dvd hsurj
  have hpos : 0 < H.index := Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite (H := H))
  have hle : (H.map π).index ≤ 2 := (Nat.le_of_dvd hpos hdvd).trans hH
  exact Equiv.Perm.alternatingGroup_le_of_index_le_two hle

theorem ronanH143_not_isPGroup_alt {n : ℕ} (hn : 5 ≤ n) :
    ¬ IsPGroup 2 ↥(alternatingGroup (Fin n)) := by
  intro hA
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
  obtain ⟨k, hk⟩ := hA.exists_card_eq
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin] at hk
  have h2 : 2 ∣ Nat.factorial n := Nat.dvd_factorial (by norm_num) (by omega)
  have h3 : 3 ∣ Nat.factorial n := Nat.dvd_factorial (by norm_num) (by omega)
  have hdiv : 2 * (Nat.factorial n / 2) = Nat.factorial n := Nat.mul_div_cancel' h2
  have h3' : 3 ∣ Nat.factorial n / 2 := by omega
  rw [hk] at h3'
  have h32 : 3 ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3'
  omega

theorem ronanH143_normal_perm_bot {n : ℕ} (hn : 5 ≤ n) {K : Subgroup (Equiv.Perm (Fin n))}
    [K.Normal] (hK2 : IsPGroup 2 ↥K) : K = ⊥ := by
  by_contra hne
  have hnt : Nontrivial ↥K := (Subgroup.nontrivial_iff_ne_bot K).mpr hne
  have hcard : 5 ≤ Nat.card (Fin n) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_fin]
    exact hn
  have hle : alternatingGroup (Fin n) ≤ K := Equiv.Perm.alternatingGroup_le_of_normal hcard hnt
  exact ronanH143_not_isPGroup_alt hn (hK2.to_le hle)

theorem pCore_le_ker_of_range_top {G : Type*} [Group G] [Finite G] {n : ℕ} (hn : 5 ≤ n)
    (π : G →* Equiv.Perm (Fin n)) (hπ : π.range = ⊤) : CFSG.pCore 2 G ≤ π.ker := by
  have hsurj : Function.Surjective π := MonoidHom.range_eq_top.mp hπ
  have hNn : (CFSG.pCore 2 G).Normal := CFSG.pCore_normal
  have hNp : IsPGroup 2 (CFSG.pCore 2 G) := CFSG.pCore_isPGroup
  have hMn : ((CFSG.pCore 2 G).map π).Normal := Subgroup.Normal.map hNn π hsurj
  have hM : IsPGroup 2 ((CFSG.pCore 2 G).map π) := hNp.map π
  have hbot : (CFSG.pCore 2 G).map π = ⊥ := ronanH143_normal_perm_bot hn hM
  intro g hg
  rw [MonoidHom.mem_ker]
  have hmem : π g ∈ (CFSG.pCore 2 G).map π := ⟨g, hg, rfl⟩
  rw [hbot, Subgroup.mem_bot] at hmem
  exact hmem

theorem pCore_le_ker_of_range_alt {G : Type*} [Group G] [Finite G] {n : ℕ} (hn : 5 ≤ n)
    (π : G →* Equiv.Perm (Fin n)) (hπ : π.range = alternatingGroup (Fin n)) :
    CFSG.pCore 2 G ≤ π.ker := by
  have hNn : (CFSG.pCore 2 G).Normal := CFSG.pCore_normal
  have hNp : IsPGroup 2 (CFSG.pCore 2 G) := CFSG.pCore_isPGroup
  have hM : IsPGroup 2 ((CFSG.pCore 2 G).map π) := hNp.map π
  have hMA : (CFSG.pCore 2 G).map π ≤ alternatingGroup (Fin n) := by
    rw [← hπ]
    exact Subgroup.map_le_range _ _
  have hMn : (((CFSG.pCore 2 G).map π).subgroupOf (alternatingGroup (Fin n))).Normal := by
    constructor
    intro m hm a
    rw [Subgroup.mem_subgroupOf] at hm ⊢
    obtain ⟨x, hx, hxm⟩ := hm
    have ha : (a : Equiv.Perm (Fin n)) ∈ π.range := by
      rw [hπ]
      exact a.2
    obtain ⟨l, hl⟩ := ha
    refine ⟨l * x * l⁻¹, hNn.conj_mem x hx l, ?_⟩
    rw [map_mul, map_mul, map_inv, hl, hxm]
    rfl
  have hs : IsSimpleGroup ↥(alternatingGroup (Fin n)) :=
    alternatingGroup.isSimpleGroup (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; exact hn)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
    (((CFSG.pCore 2 G).map π).subgroupOf (alternatingGroup (Fin n))) with h | h
  · intro x hx
    rw [MonoidHom.mem_ker]
    have hm : π x ∈ (CFSG.pCore 2 G).map π := ⟨x, hx, rfl⟩
    have hm' : (⟨π x, hMA hm⟩ : ↥(alternatingGroup (Fin n))) ∈
        ((CFSG.pCore 2 G).map π).subgroupOf (alternatingGroup (Fin n)) :=
      Subgroup.mem_subgroupOf.2 hm
    rw [h, Subgroup.mem_bot] at hm'
    exact congrArg Subtype.val hm'
  · exfalso
    have hle : alternatingGroup (Fin n) ≤ (CFSG.pCore 2 G).map π := by
      intro a ha
      have : (⟨a, ha⟩ : ↥(alternatingGroup (Fin n))) ∈
          ((CFSG.pCore 2 G).map π).subgroupOf (alternatingGroup (Fin n)) := by
        rw [h]
        trivial
      exact Subgroup.mem_subgroupOf.1 this
    exact ronanH143_not_isPGroup_alt hn (hM.to_le hle)

theorem pCoreOf_eq_of_ker {M N : Subgroup P24} {n : ℕ} (hn : 5 ≤ n)
    (π : ↥M →* Equiv.Perm (Fin n))
    (hπ : π.range = ⊤ ∨ π.range = alternatingGroup (Fin n))
    (hker : π.ker = N.subgroupOf M) (hNM : N ≤ M) (hN : IsPGroup 2 ↥N) : pCoreOf 2 M = N := by
  have hle1 : CFSG.pCore 2 ↥M ≤ N.subgroupOf M := by
    rw [← hker]
    rcases hπ with hπ | hπ
    · exact pCore_le_ker_of_range_top hn π hπ
    · exact pCore_le_ker_of_range_alt hn π hπ
  have hnorm : (N.subgroupOf M).Normal := by
    rw [← hker]
    infer_instance
  have hpg : IsPGroup 2 ↥(N.subgroupOf M) := hN.of_equiv (Subgroup.subgroupOfEquivOfLe hNM).symm
  have hmem : N.subgroupOf M ∈ {K : Subgroup ↥M | K.Normal ∧ IsPGroup 2 K} := ⟨hnorm, hpg⟩
  have hle2 : N.subgroupOf M ≤ CFSG.pCore 2 ↥M := le_sSup hmem
  have heq : CFSG.pCore 2 ↥M = N.subgroupOf M := le_antisymm hle1 hle2
  rw [pCoreOf, heq, Subgroup.map_subgroupOf_eq_of_le hNM]

end CFSG.Quasithin.RonanH143
