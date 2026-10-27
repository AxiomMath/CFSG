module

public import CFSG.Quasithin.Vol2.Ch12Sec6T2Basic
public import CFSG.Quasithin.Vol2.Ch12Sec6L23c

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.G6 S126 S126L1a S126P S126E

namespace S126T2

open S126F Equiv

@[expose] def NoPair (B : Subgroup (Perm (Fin 8))) : Prop :=
  ∀ i j : Fin 8, i ≠ j → ∃ σ ∈ B, ¬ ((σ i = i ∧ σ j = j) ∨ (σ i = j ∧ σ j = i))

@[expose] noncomputable def nx (y : D8) : Fin 8 → ZMod 2 := Multiplicative.toAdd (iota y)

theorem nx_zero (y : D8) : nx y 0 = 0 := iota_zero y

theorem nx_inj {y₁ y₂ : D8} (h : nx y₁ = nx y₂) : y₁ = y₂ :=
  iota_inj (Multiplicative.toAdd.injective h)

variable {B : Subgroup (Perm (Fin 8))}

theorem inv_eq_self {σ : Perm (Fin 8)} (h : σ * σ = 1) : σ⁻¹ = σ :=
  inv_eq_of_mul_eq_one_right h

theorem nx_apply {y : D8} (hy : y ∈ fixD B) {σ : Perm (Fin 8)} (hσ : σ ∈ B) (h2 : σ * σ = 1)
    (i : Fin 8) : nx y (σ i) = nx y i + nx y (σ 0) := by
  have h := cond_of_fix (hy σ hσ) i
  rw [inv_eq_self h2] at h
  calc nx y (σ i) = nx y (σ i) + nx y (σ 0) + nx y (σ 0) := by
        rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
    _ = nx y i + nx y (σ 0) := by
        change Multiplicative.toAdd (iota y) (σ i) + Multiplicative.toAdd (iota y) (σ 0) +
          nx y (σ 0) = _
        rw [h]
        rfl

theorem card_fixD_le_eight (hB : NoPair B) : Nat.card (fixD B) ≤ 8 := by
  classical
  set W := fixD B with hW
  let r : Fin 8 → D8 ⧸ W := fun i => ((QuotientGroup.mk (pe 0 i) : D8) : D8 ⧸ W)
  have hr : Function.Injective r := by
    intro i j hij
    by_contra hne
    have h1 := QuotientGroup.eq.1 hij
    have e : ((QuotientGroup.mk (pe 0 i) : D8))⁻¹ * QuotientGroup.mk (pe 0 j) =
        (QuotientGroup.mk (pe i j) : D8) := by
      rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
      congr 1
      rw [show (pe 0 i)⁻¹ = pe i 0 by
        rw [inv_eq_of_mul_eq_one_right (by rw [S126L23c.pe_mul_pe, S126L23c.pe_self] :
          pe 0 i * pe i 0 = 1)], S126L23c.pe_mul_pe]
    rw [e] at h1
    obtain ⟨σ, hσ, hn⟩ := hB i j hne
    apply hn
    have h2 := h1 σ hσ
    rw [S126L20a.dAct_pe] at h2
    exact mk_pe_eq_mk_pe hne h2.symm
  have h8 : 8 ≤ W.index := by
    have := Nat.card_le_card_of_injective r hr
    rwa [Nat.card_fin] at this
  have hmul := Subgroup.card_mul_index W
  rw [S126L20.card_D8_eq] at hmul
  by_contra hlt
  push Not at hlt
  have : 9 * 8 ≤ Nat.card W * W.index := Nat.mul_le_mul hlt h8
  omega

theorem fix_of_fix (hcomm : ∀ σ ∈ B, ∀ τ ∈ B, σ * τ = τ * σ) {ρ τ : Perm (Fin 8)} (hρ : ρ ∈ B)
    (hτ : τ ∈ B) {q : Fin 8} (h : ρ q = q) : ρ (τ q) = τ q := by
  have := congrArg (fun f : Perm (Fin 8) => f q) (hcomm ρ hρ τ hτ)
  simp only [Perm.mul_apply] at this
  rw [this, h]

section Orbits

variable (hinv : ∀ σ ∈ B, σ * σ = 1)
include hinv

theorem isPGroup_of_inv : IsPGroup 2 ↥B := fun g =>
  ⟨1, Subtype.ext (by simpa [pow_two] using hinv g g.2)⟩

theorem exists_move (hB : NoPair B) (q : Fin 8) : ∃ a ∈ B, a q ≠ q := by
  by_contra h
  push Not at h
  have hp := isPGroup_of_inv hinv
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmod := hp.card_modEq_card_fixedPoints (Fin 8)
  rw [Nat.card_fin] at hmod
  have hq : q ∈ MulAction.fixedPoints ↥B (Fin 8) := fun g => h g g.2
  have hpos : 0 < Nat.card ↥(MulAction.fixedPoints ↥B (Fin 8)) :=
    Nat.card_pos_iff.2 ⟨⟨q, hq⟩, inferInstance⟩
  have h2 : 1 < (MulAction.fixedPoints ↥B (Fin 8)).ncard := by
    rw [← Nat.card_coe_set_eq]
    have := hmod.symm
    unfold Nat.ModEq at this
    omega
  obtain ⟨r, hr, hrq⟩ := Set.exists_ne_of_one_lt_ncard h2 q
  obtain ⟨σ, hσ, hn⟩ := hB q r hrq.symm
  exact hn (Or.inl ⟨h σ hσ, hr ⟨σ, hσ⟩⟩)

theorem exists_move2 (hcomm : ∀ σ ∈ B, ∀ τ ∈ B, σ * τ = τ * σ) (hB : NoPair B) {a : Perm (Fin 8)}
    (ha : a ∈ B) {q : Fin 8} (haq : a q ≠ q) : ∃ b ∈ B, b q ≠ q ∧ b q ≠ a q := by
  by_contra h
  push Not at h
  obtain ⟨σ, hσ, hn⟩ := hB q (a q) haq.symm
  have hσa : σ (a q) = a (σ q) := by
    have := congrArg (fun f : Perm (Fin 8) => f q) (hcomm σ hσ a ha)
    simpa only [Perm.mul_apply] using this
  have haa : a (a q) = q := by
    have := congrArg (fun f : Perm (Fin 8) => f q) (hinv a ha)
    simpa only [Perm.mul_apply, Perm.one_apply] using this
  apply hn
  by_cases h1 : σ q = q
  · exact Or.inl ⟨h1, by rw [hσa, h1]⟩
  · exact Or.inr ⟨h σ hσ h1, by rw [hσa, h σ hσ h1, haa]⟩

end Orbits

theorem exists_four (hinv : ∀ σ ∈ B, σ * σ = 1) (hcomm : ∀ σ ∈ B, ∀ τ ∈ B, σ * τ = τ * σ)
    (hB : NoPair B) (q : Fin 8) : ∃ a ∈ B, ∃ b ∈ B, a q ≠ q ∧ b q ≠ q ∧ b q ≠ a q ∧
      (a * b) q ≠ q ∧ (a * b) q ≠ a q ∧ (a * b) q ≠ b q := by
  have happ : ∀ σ ∈ B, ∀ i, σ (σ i) = i := fun σ hσ i => by
    have := congrArg (fun f : Perm (Fin 8) => f i) (hinv σ hσ)
    simpa only [Perm.mul_apply, Perm.one_apply] using this
  obtain ⟨a, haB, ha⟩ := exists_move hinv hB q
  obtain ⟨b, hbB, hb0, hba⟩ := exists_move2 hinv hcomm hB haB ha
  refine ⟨a, haB, b, hbB, ha, hb0, hba, ?_, ?_, ?_⟩
  · intro e
    rw [Perm.mul_apply] at e
    apply hba
    calc b q = a (a (b q)) := (happ a haB _).symm
      _ = a q := by rw [e]
  · exact fun e => hb0 (a.injective (by rw [← Perm.mul_apply, e]))
  · intro e
    rw [hcomm a haB b hbB, Perm.mul_apply] at e
    exact ha (b.injective e)

theorem card_mul_card_fixD_le (hcomm : ∀ σ ∈ B, ∀ τ ∈ B, σ * τ = τ * σ)
    (hinv : ∀ σ ∈ B, σ * σ = 1) (hB : NoPair B) : Nat.card B * Nat.card (fixD B) ≤ 64 := by
  classical
  have hf8 := card_fixD_le_eight hB
  by_cases h8 : Nat.card B ≤ 8
  · calc Nat.card B * Nat.card (fixD B) ≤ 8 * 8 := Nat.mul_le_mul h8 hf8
      _ = 64 := rfl
  push Not at h8
  have hp := isPGroup_of_inv hinv
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have happ : ∀ σ ∈ B, ∀ i, σ (σ i) = i := fun σ hσ i => by
    have := congrArg (fun f : Perm (Fin 8) => f i) (hinv σ hσ)
    simpa only [Perm.mul_apply, Perm.one_apply] using this
  have hcomm' : ∀ σ ∈ B, ∀ τ ∈ B, ∀ i, σ (τ i) = τ (σ i) := fun σ hσ τ hτ i => by
    have := congrArg (fun f : Perm (Fin 8) => f i) (hcomm σ hσ τ hτ)
    simpa only [Perm.mul_apply] using this
  have hinj0 : (∀ i, ∃ τ ∈ B, τ 0 = i) → Nat.card B ≤ 8 := by
    intro htr
    have hi : Function.Injective fun σ : ↥B => (σ : Perm (Fin 8)) 0 := by
      intro σ τ e
      apply Subtype.ext
      have hρ : ∀ i, ((τ : Perm (Fin 8)) * σ) i = i := by
        intro i
        obtain ⟨κ, hκ, rfl⟩ := htr i
        refine fix_of_fix hcomm (B.mul_mem τ.2 σ.2) hκ ?_
        change (τ : Perm (Fin 8)) ((σ : Perm (Fin 8)) 0) = 0
        rw [show (σ : Perm (Fin 8)) 0 = (τ : Perm (Fin 8)) 0 from e, happ _ τ.2]
      have h1 : (τ : Perm (Fin 8)) * σ = 1 := Equiv.ext hρ
      calc (σ : Perm (Fin 8)) = τ * (τ * σ) := by rw [← mul_assoc, hinv _ τ.2, one_mul]
        _ = τ := by rw [h1, mul_one]
    have := Nat.card_le_card_of_injective _ hi
    rwa [Nat.card_fin] at this
  obtain ⟨a, haB, b, hbB, ha, hb0, hba, hab0, haba, habb⟩ := exists_four hinv hcomm hB 0
  set O : Finset (Fin 8) := {0, a 0, b 0, (a * b) 0} with hO
  have hOcard : O.card = 4 := by
    rw [hO, Finset.card_insert_of_notMem (by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨ha.symm, hb0.symm, hab0.symm⟩),
      Finset.card_insert_of_notMem (by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨hba.symm, haba.symm⟩), Finset.card_pair habb.symm]
  have hOrep : ∀ o ∈ O, ∃ τ ∈ B, τ 0 = o := by
    intro o ho
    simp only [hO, Finset.mem_insert, Finset.mem_singleton] at ho
    rcases ho with rfl | rfl | rfl | rfl
    exacts [⟨1, B.one_mem, rfl⟩, ⟨a, haB, rfl⟩, ⟨b, hbB, rfl⟩, ⟨a * b, B.mul_mem haB hbB, rfl⟩]
  have hK1 : ∀ σ ∈ B, σ 0 ∈ O := by
    by_contra hc
    push Not at hc
    obtain ⟨c, hcB, hc0⟩ := hc
    apply absurd h8
    push Not
    apply hinj0
    obtain ⟨n, hn⟩ := hp.card_orbit (0 : Fin 8)
    have hsub : ((insert (c 0) O : Finset (Fin 8)) : Set (Fin 8)) ⊆ MulAction.orbit ↥B 0 := by
      intro i hi
      rw [Finset.coe_insert, Set.mem_insert_iff] at hi
      rcases hi with rfl | hi
      · exact ⟨⟨c, hcB⟩, rfl⟩
      · obtain ⟨τ, hτ, rfl⟩ := hOrep i hi
        exact ⟨⟨τ, hτ⟩, rfl⟩
    have h5 : 5 ≤ (MulAction.orbit ↥B (0 : Fin 8)).ncard := by
      have := Set.ncard_le_ncard hsub (Set.toFinite _)
      rwa [Set.ncard_coe_finset, Finset.card_insert_of_notMem hc0, hOcard] at this
    have hle : (MulAction.orbit ↥B (0 : Fin 8)).ncard ≤ 8 := by
      have := Set.ncard_le_ncard (Set.subset_univ (MulAction.orbit ↥B (0 : Fin 8)))
      rwa [Set.ncard_univ, Nat.card_fin] at this
    rw [← Nat.card_coe_set_eq, hn] at h5 hle
    have hn3 : n = 3 := by
      have h1 : n < 4 := by
        by_contra h
        push Not at h
        have : 2 ^ 4 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h
        omega
      interval_cases n <;> simp_all
    have huniv : MulAction.orbit ↥B (0 : Fin 8) = Set.univ := by
      refine Set.eq_of_subset_of_ncard_le (Set.subset_univ _) ?_ (Set.toFinite _)
      rw [Set.ncard_univ, Nat.card_fin, ← Nat.card_coe_set_eq, hn, hn3]
      norm_num
    intro i
    have hi : i ∈ MulAction.orbit ↥B (0 : Fin 8) := huniv ▸ Set.mem_univ i
    obtain ⟨τ, hτ⟩ := hi
    exact ⟨τ, τ.2, hτ⟩
  have hK2 : ∀ σ ∈ B, ∀ o ∈ O, σ o ∈ O := by
    intro σ hσ o ho
    obtain ⟨τ, hτ, rfl⟩ := hOrep o ho
    rw [← Perm.mul_apply]
    exact hK1 _ (B.mul_mem hσ hτ)
  have hK5 : ∀ σ ∈ B, ∀ r, r ∉ O → σ r ∉ O := by
    intro σ hσ r hr h
    exact hr (happ σ hσ r ▸ hK2 σ hσ _ h)
  obtain ⟨c₂, hc₂B, c₃, hc₃B, hc₂1, hc₃1, hc₂₃, hc₂0, hc₃0⟩ : ∃ c₂ ∈ B, ∃ c₃ ∈ B, c₂ ≠ 1 ∧
      c₃ ≠ 1 ∧ c₂ ≠ c₃ ∧ c₂ 0 = 0 ∧ c₃ 0 = 0 := by
    set s : Finset (Perm (Fin 8)) := (B : Set (Perm (Fin 8))).toFinset with hs
    have hscard : s.card = Nat.card B := by
      rw [hs, Set.toFinset_card, ← Nat.card_eq_fintype_card]
      rfl
    have hmaps : ∀ σ ∈ s, σ 0 ∈ O := fun σ hσ => hK1 σ (by simpa [hs] using hσ)
    obtain ⟨o, -, ho⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to hmaps
      (by rw [hOcard, hscard]; omega : O.card * 2 < s.card)
    obtain ⟨σ₁, hσ₁, σ₂, hσ₂, σ₃, hσ₃, h12, h13, h23⟩ := Finset.two_lt_card.1 ho
    simp only [Finset.mem_filter, hs, Set.mem_toFinset, SetLike.mem_coe] at hσ₁ hσ₂ hσ₃
    have e₂ : (σ₁ * σ₂) 0 = 0 := by rw [Perm.mul_apply, hσ₂.2, ← hσ₁.2, happ σ₁ hσ₁.1]
    have e₃ : (σ₁ * σ₃) 0 = 0 := by rw [Perm.mul_apply, hσ₃.2, ← hσ₁.2, happ σ₁ hσ₁.1]
    refine ⟨σ₁ * σ₂, B.mul_mem hσ₁.1 hσ₂.1, σ₁ * σ₃, B.mul_mem hσ₁.1 hσ₃.1, ?_, ?_, ?_, e₂, e₃⟩
    · intro e
      apply h12
      calc σ₁ = σ₁ * (σ₁ * σ₂) := by rw [e, mul_one]
        _ = σ₂ := by rw [← mul_assoc, hinv σ₁ hσ₁.1, one_mul]
    · intro e
      apply h13
      calc σ₁ = σ₁ * (σ₁ * σ₃) := by rw [e, mul_one]
        _ = σ₃ := by rw [← mul_assoc, hinv σ₁ hσ₁.1, one_mul]
    · intro e
      exact h23 (mul_left_cancel e)
  obtain ⟨p, hp⟩ : ∃ p : Fin 8, p ∉ O := by
    by_contra h
    push Not at h
    have : (Finset.univ : Finset (Fin 8)).card ≤ O.card :=
      Finset.card_le_card fun i _ => h i
    rw [Finset.card_univ, Fintype.card_fin, hOcard] at this
    omega
  obtain ⟨a', ha'B, b', hb'B, ha', hb'0, hb'a, hab'0, hab'a, hab'b⟩ := exists_four hinv hcomm hB p
  set O' : Finset (Fin 8) := {p, a' p, b' p, (a' * b') p} with hO'
  have hO'card : O'.card = 4 := by
    rw [hO', Finset.card_insert_of_notMem (by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨ha'.symm, hb'0.symm, hab'0.symm⟩),
      Finset.card_insert_of_notMem (by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨hb'a.symm, hab'a.symm⟩), Finset.card_pair hab'b.symm]
  have hO'rep : ∀ r ∈ O', ∃ τ ∈ B, τ p = r := by
    intro r hr
    simp only [hO', Finset.mem_insert, Finset.mem_singleton] at hr
    rcases hr with rfl | rfl | rfl | rfl
    exacts [⟨1, B.one_mem, rfl⟩, ⟨a', ha'B, rfl⟩, ⟨b', hb'B, rfl⟩,
      ⟨a' * b', B.mul_mem ha'B hb'B, rfl⟩]
  have hO'O : ∀ r ∈ O', r ∉ O := by
    intro r hr
    obtain ⟨τ, hτ, rfl⟩ := hO'rep r hr
    exact hK5 τ hτ p hp
  have hcompl : ∀ r, r ∉ O → r ∈ O' := by
    intro r hr
    by_contra hr'
    have hdisj : Disjoint O O' := Finset.disjoint_left.2 fun x hx hx' => hO'O x hx' hx
    have h1 : (insert r (O ∪ O')).card ≤ 8 := by
      have := Finset.card_le_card (Finset.subset_univ (insert r (O ∪ O')))
      rwa [Finset.card_univ, Fintype.card_fin] at this
    rw [Finset.card_insert_of_notMem (by simp [hr, hr']), Finset.card_union_of_disjoint hdisj,
      hOcard, hO'card] at h1
    omega
  have hfix1 : ∀ ρ ∈ B, ρ 0 = 0 → ρ p = p → ρ = 1 := by
    intro ρ hρ h0 hp'
    refine Equiv.ext fun i => ?_
    by_cases hi : i ∈ O
    · obtain ⟨τ, hτ, rfl⟩ := hOrep i hi
      exact fix_of_fix hcomm hρ hτ h0
    · obtain ⟨τ, hτ, rfl⟩ := hO'rep i (hcompl i hi)
      exact fix_of_fix hcomm hρ hτ hp'
  have hc₂₃1 : c₂ * c₃ ≠ 1 := fun e => hc₂₃ (by
    calc c₂ = c₂ * (c₃ * c₃) := by rw [hinv c₃ hc₃B, mul_one]
      _ = c₃ := by rw [← mul_assoc, e, one_mul])
  have hc₂₃0 : (c₂ * c₃) 0 = 0 := by rw [Perm.mul_apply, hc₃0, hc₂0]
  have hmov : ∀ c ∈ B, c ≠ 1 → c 0 = 0 → c p ≠ p := fun c hc h1 h0 e => h1 (hfix1 c hc h0 e)
  have hm₂ := hmov c₂ hc₂B hc₂1 hc₂0
  have hm₃ := hmov c₃ hc₃B hc₃1 hc₃0
  have hm₂₃ := hmov _ (B.mul_mem hc₂B hc₃B) hc₂₃1 hc₂₃0
  have hd₂₃ : c₂ p ≠ c₃ p := by
    intro e
    apply hm₂₃
    rw [Perm.mul_apply, ← e, happ c₂ hc₂B]
  have hd₂ : (c₂ * c₃) p ≠ c₂ p := fun e => hm₃ (c₂.injective (by rw [← Perm.mul_apply, e]))
  have hd₃ : (c₂ * c₃) p ≠ c₃ p := by
    intro e
    rw [Perm.mul_apply, hcomm' c₂ hc₂B c₃ hc₃B] at e
    exact hm₂ (c₃.injective e)
  have hcov : ∀ r, r ∉ O → ∃ c ∈ B, c 0 = 0 ∧ c p = r := by
    intro r hr
    set C : Finset (Fin 8) := {p, c₂ p, c₃ p, (c₂ * c₃) p} with hC
    have hCcard : C.card = 4 := by
      rw [hC, Finset.card_insert_of_notMem (by
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
          exact ⟨hm₂.symm, hm₃.symm, hm₂₃.symm⟩),
        Finset.card_insert_of_notMem (by
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
          exact ⟨hd₂₃, hd₂.symm⟩), Finset.card_pair hd₃.symm]
    have hCO' : C ⊆ O' := by
      intro x hx
      refine hcompl x ?_
      simp only [hC, Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact hp
      · exact hK5 c₂ hc₂B p hp
      · exact hK5 c₃ hc₃B p hp
      · exact hK5 _ (B.mul_mem hc₂B hc₃B) p hp
    have hCeq : C = O' := Finset.eq_of_subset_of_card_le hCO' (by rw [hCcard, hO'card])
    have hrC : r ∈ C := hCeq ▸ hcompl r hr
    simp only [hC, Finset.mem_insert, Finset.mem_singleton] at hrC
    rcases hrC with rfl | rfl | rfl | rfl
    exacts [⟨1, B.one_mem, rfl, rfl⟩, ⟨c₂, hc₂B, hc₂0, rfl⟩, ⟨c₃, hc₃B, hc₃0, rfl⟩,
      ⟨c₂ * c₃, B.mul_mem hc₂B hc₃B, hc₂₃0, rfl⟩]
  have hval : ∀ y ∈ fixD B, ∀ i, nx y i = if i ∈ O then 0 else nx y p := by
    intro y hy i
    have hconst : ∀ r, r ∉ O → nx y r = nx y p := by
      intro r hr
      obtain ⟨c, hc, hc0, rfl⟩ := hcov r hr
      rw [nx_apply hy hc (hinv c hc), hc0, nx_zero, add_zero]
    have hzero : ∀ τ ∈ B, nx y (τ 0) = 0 := by
      intro τ hτ
      have h1 := nx_apply hy hτ (hinv τ hτ) p
      rw [hconst _ (hK5 τ hτ p hp)] at h1
      exact left_eq_add.1 h1
    split_ifs with hi
    · obtain ⟨τ, hτ, rfl⟩ := hOrep i hi
      exact hzero τ hτ
    · exact hconst i hi
  have hfix2 : Nat.card (fixD B) ≤ 2 := by
    have hi : Function.Injective fun y : ↥(fixD B) => nx (y : D8) p := by
      intro y₁ y₂ e
      apply Subtype.ext
      apply nx_inj
      funext i
      rw [hval _ y₁.2, hval _ y₂.2]
      simp only at e
      rw [e]
    have := Nat.card_le_card_of_injective _ hi
    rwa [Nat.card_zmod] at this
  have hB16 : Nat.card B ≤ 16 := by
    have hi : Function.Injective fun σ : ↥B =>
        (⟨((σ : Perm (Fin 8)) 0, (σ : Perm (Fin 8)) p), Finset.mem_product.2
          ⟨hK1 _ σ.2, hcompl _ (hK5 _ σ.2 p hp)⟩⟩ : ↥(O ×ˢ O')) := by
      intro σ τ e
      have e' := congrArg Subtype.val e
      simp only [Prod.mk.injEq] at e'
      apply Subtype.ext
      have h1 := hfix1 _ (B.mul_mem τ.2 σ.2)
        (by rw [Perm.mul_apply, e'.1, happ _ τ.2]) (by rw [Perm.mul_apply, e'.2, happ _ τ.2])
      calc (σ : Perm (Fin 8)) = τ * (τ * σ) := by rw [← mul_assoc, hinv _ τ.2, one_mul]
        _ = τ := by rw [h1, mul_one]
    have := Nat.card_le_card_of_injective _ hi
    rwa [Nat.card_eq_finsetCard, Finset.card_product, hOcard, hO'card] at this
  calc Nat.card B * Nat.card (fixD B) ≤ 16 * 2 := Nat.mul_le_mul hB16 hfix2
    _ ≤ 64 := by norm_num

end S126T2

end CFSG.Quasithin.H13
