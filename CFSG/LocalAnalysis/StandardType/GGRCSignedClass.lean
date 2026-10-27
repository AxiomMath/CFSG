module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveRMModuleDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveZSInputs

public section

namespace CFSG.StandardType

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section L1

private lemma l05nK42_finrank_range_ge_two_of_pair
    {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    [Module.Finite (ZMod p) V] {T : V →ₗ[ZMod p] V} {u w : V}
    (hu : u ∈ LinearMap.range T) (hw : w ∈ LinearMap.range T)
    (hli : LinearIndependent (ZMod p) ![u, w]) :
    2 ≤ Module.finrank (ZMod p) (LinearMap.range T) := by
  have hspan_le : Submodule.span (ZMod p) (Set.range ![u, w]) ≤ LinearMap.range T := by
    rw [Submodule.span_le]
    rintro x ⟨k, rfl⟩
    fin_cases k
    · simpa using hu
    · simpa using hw
  have h2 : Module.finrank (ZMod p) (Submodule.span (ZMod p) (Set.range ![u, w])) = 2 := by
    rw [finrank_span_eq_card hli]
    simp
  have := Submodule.finrank_mono hspan_le
  omega

private lemma l05nK42_indep_pair_of_coord
    {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V) {u w : V} {a d : Fin n}
    (hua : b.equivFun u a = 1) (hwa : b.equivFun w a = 0)
    (hud : b.equivFun u d = 0) (hwd : b.equivFun w d = 1) :
    LinearIndependent (ZMod p) ![u, w] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  constructor
  · have h := congrArg (fun z => b.equivFun z a) hst
    simp only [map_add, map_smul, Pi.add_apply, Pi.smul_apply, map_zero, Pi.zero_apply] at h
    simp only [smul_eq_mul, hua, hwa, mul_one, mul_zero, add_zero] at h
    exact h
  · have h := congrArg (fun z => b.equivFun z d) hst
    simp only [map_add, map_smul, Pi.add_apply, Pi.smul_apply, map_zero, Pi.zero_apply] at h
    simp only [smul_eq_mul, hud, hwd, mul_zero, mul_one, zero_add] at h
    exact h

private theorem l05nK42_refl_shape
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V) (r : V ≃ₗ[ZMod p] V)
    (hr : GGLinRefl r) (σ : Equiv.Perm (Fin n)) (c : Fin n → ZMod p)
    (hc : ∀ i, c i = 1 ∨ c i = -1) (hrb : ∀ i, r (b i) = c i • b (σ i)) :
    (∃ i, σ = 1 ∧ c i = -1 ∧ ∀ j, j ≠ i → c j = 1) ∨
      ∃ i j, i ≠ j ∧ σ = Equiv.swap i j ∧ c i * c j = 1 ∧ ∀ k, k ≠ i → k ≠ j → c k = 1 := by
  classical
  haveI : Module.Finite (ZMod p) V := Module.Finite.of_basis b
  have hp : p.Prime := Fact.out
  have htwo : (2 : ZMod p) ≠ 0 := by
    intro h
    have hdvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h
    have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
    exact hp2 (le_antisymm hle hp.two_le)
  have hneg2 : (-(2 : ZMod p)) ≠ 0 := neg_ne_zero.mpr htwo
  have hr2 : ∀ v, r (r v) = v := fun v => by
    have h := congrArg (fun e : V ≃ₗ[ZMod p] V => e v) hr.1
    rw [LinearEquiv.mul_apply] at h
    simpa using h
  let T : V →ₗ[ZMod p] V := (r : V →ₗ[ZMod p] V) - LinearMap.id
  have hTfin : Module.finrank (ZMod p) (LinearMap.range T) = 1 := hr.2
  have hTb : ∀ i, T (b i) = c i • b (σ i) - b i := by
    intro i
    simp only [T, LinearMap.sub_apply, LinearMap.id_apply]
    rw [show (r : V →ₗ[ZMod p] V) (b i) = r (b i) from rfl, hrb i]
  have hσ2 : ∀ i, σ (σ i) = i := by
    intro i
    by_contra hne
    have h := hr2 (b i)
    rw [hrb i, map_smul, hrb (σ i), smul_smul] at h
    have h' := congrArg (fun v => b.equivFun v i) h
    simp only [map_smul, Pi.smul_apply, Module.Basis.equivFun_self, ↓reduceIte, smul_eq_mul] at h'
    rw [if_neg hne, mul_zero] at h'
    exact zero_ne_one h'
  have hcσ : ∀ i, c (σ i) = c i := by
    intro i
    have h := hr2 (b i)
    rw [hrb i, map_smul, hrb (σ i), smul_smul, hσ2 i] at h
    have h' := congrArg (fun v => b.equivFun v i) h
    simp only [map_smul, Pi.smul_apply, Module.Basis.equivFun_self, ↓reduceIte, smul_eq_mul,
      mul_one] at h'
    rcases hc i with h1 | h1
    · rw [h1, one_mul] at h'; rw [h1, h']
    · rw [h1] at h'
      have hcinv : c (σ i) = -1 := by
        have h2 : (-1 : ZMod p) * c (σ i) = (-1) * (-1) := by rw [h']; ring
        exact mul_left_cancel₀ (neg_ne_zero.mpr one_ne_zero) h2
      rw [h1, hcinv]
  have hvi_mem : ∀ i, b i - c i • b (σ i) ∈ LinearMap.range T := by
    intro i
    refine ⟨-(b i), ?_⟩
    rw [map_neg, hTb i, neg_sub]
  have hvi_ne : ∀ i, σ i ≠ i → b i - c i • b (σ i) ≠ 0 := by
    intro i hi h0
    have h' := congrArg (fun v => b.equivFun v i) h0
    simp only [map_sub, map_smul, Pi.sub_apply, Pi.smul_apply, Module.Basis.equivFun_self,
      ↓reduceIte, smul_eq_mul, map_zero, Pi.zero_apply] at h'
    rw [if_neg hi, mul_zero, sub_zero] at h'
    exact one_ne_zero h'
  have hbk_mem : ∀ k, σ k = k → c k = -1 → b k ∈ LinearMap.range T := by
    intro k hk hck
    refine ⟨(-(2 : ZMod p))⁻¹ • b k, ?_⟩
    have hTk : T (b k) = (-(2 : ZMod p)) • b k := by
      rw [hTb k, hk, hck]; module
    rw [map_smul, hTk, smul_smul, inv_mul_cancel₀ hneg2, one_smul]
  have htwo_moves : ∀ {u w : V}, u ∈ LinearMap.range T → w ∈ LinearMap.range T →
      LinearIndependent (ZMod p) ![u, w] → False := by
    intro u w hu hw hli
    have := l05nK42_finrank_range_ge_two_of_pair hu hw hli
    omega
  have hcoord_vi : ∀ i a, b.equivFun (b i - c i • b (σ i)) a =
      (if i = a then 1 else 0) - c i * (if σ i = a then 1 else 0) := by
    intro i a
    simp only [map_sub, map_smul, Pi.sub_apply, Pi.smul_apply, Module.Basis.equivFun_self,
      smul_eq_mul]
  have hcoord_vk : ∀ k a, b.equivFun (b k - c k • b (σ k)) a =
      (if k = a then 1 else 0) - c k * (if σ k = a then 1 else 0) := by
    intro k a
    simp only [map_sub, map_smul, Pi.sub_apply, Pi.smul_apply, Module.Basis.equivFun_self,
      smul_eq_mul]
  have hno_two_cycles : ∀ i k, σ i ≠ i → σ k ≠ k → k ≠ i → k ≠ σ i → False := by
    intro i k hi hk hki hksi
    have hki' : i ≠ k := fun h => hki h.symm
    have hsi_k : σ i ≠ k := fun h => hksi h.symm
    have hi_sk : i ≠ σ k := by
      intro h
      have hsk : σ k = i := h.symm
      have h1 : σ (σ k) = σ i := congrArg σ hsk
      rw [hσ2 k] at h1
      exact hsi_k h1.symm
    refine htwo_moves (hvi_mem i) (hvi_mem k)
      (l05nK42_indep_pair_of_coord (b := b) (u := b i - c i • b (σ i))
        (w := b k - c k • b (σ k)) (a := i) (d := k) ?_ ?_ ?_ ?_)
    · rw [hcoord_vi i i]; simp [hi]
    · rw [hcoord_vk k i]; simp [hki, Ne.symm hi_sk]
    · rw [hcoord_vi i k]; simp [hki', hsi_k]
    · rw [hcoord_vk k k]; simp [hk]
  have hno_mixed : ∀ i k, σ i ≠ i → σ k = k → c k = -1 → False := by
    intro i k hi hk hck
    have hki : k ≠ i := by
      intro h
      exact hi (by rw [← h, hk])
    have hsi_k : σ i ≠ k := by
      intro h
      have hki_eq : k = i := by rw [← hk, ← h, hσ2 i]
      exact hi (by rw [h, hki_eq])
    refine htwo_moves (hvi_mem i) (hbk_mem k hk hck)
      (l05nK42_indep_pair_of_coord (b := b) (u := b i - c i • b (σ i))
        (w := b k) (a := i) (d := k) ?_ ?_ ?_ ?_)
    · rw [hcoord_vi i i]; simp [hi]
    · simp [Module.Basis.equivFun_self, hki]
    · rw [hcoord_vi i k]; simp [Ne.symm hki, hsi_k]
    · simp [Module.Basis.equivFun_self]
  have hno_neg_fixed : ∀ k l, σ k = k → c k = -1 → σ l = l → c l = -1 → k = l := by
    intro k l hk hck hl hcl
    by_contra hkl
    refine htwo_moves (hbk_mem k hk hck) (hbk_mem l hl hcl)
      (l05nK42_indep_pair_of_coord (b := b) (u := b k) (w := b l) (a := k) (d := l) ?_ ?_ ?_ ?_)
    · simp [Module.Basis.equivFun_self]
    · simp [Module.Basis.equivFun_self, Ne.symm hkl]
    · simp [Module.Basis.equivFun_self, hkl]
    · simp [Module.Basis.equivFun_self]
  by_cases hmoved : ∃ i, σ i ≠ i
  · obtain ⟨i, hi⟩ := hmoved
    right
    refine ⟨i, σ i, Ne.symm hi, ?_, ?_, ?_⟩
    · ext k
      by_cases hk : k = i
      · rw [hk, Equiv.swap_apply_left]
      · by_cases hk' : k = σ i
        · rw [hk', hσ2 i, Equiv.swap_apply_right]
        · have hkfix : σ k = k := by
            by_contra hne
            exact hno_two_cycles i k hi hne hk hk'
          rw [hkfix, Equiv.swap_apply_of_ne_of_ne hk hk']
    · rcases hc i with h1 | h1 <;> rw [hcσ i, h1] <;> ring
    · intro k hki hksi
      rcases hc k with h1 | h1
      · exact h1
      · have hkfix : σ k = k := by
          by_contra hne
          exact hno_two_cycles i k hi hne hki hksi
        exact (hno_mixed i k hi hkfix h1).elim
  · push Not at hmoved
    left
    have hex : ∃ i, c i = -1 := by
      by_contra h
      push Not at h
      have hc1 : ∀ i, c i = 1 := fun i => (hc i).resolve_right (h i)
      have hT0 : T = 0 := by
        apply b.ext
        intro i
        rw [hTb i, hmoved i, hc1 i, one_smul, sub_self, LinearMap.zero_apply]
      rw [hT0, LinearMap.range_zero, finrank_bot] at hTfin
      omega
    obtain ⟨i, hi⟩ := hex
    refine ⟨i, ?_, hi, ?_⟩
    · ext k; rw [hmoved k, Equiv.Perm.one_apply]
    · intro j hj
      rcases hc j with h1 | h1
      · exact h1
      · exact (hj (hno_neg_fixed j i (hmoved j) h1 (hmoved i) hi)).elim

end L1

section Cat

private lemma l05nK42_diagMap_apply
    {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V) (d : Fin n → (ZMod p)ˣ) (k : Fin n) :
    ZS.diagMap p b d (b k) = (d k : ZMod p) • b k := by
  apply b.equivFun.injective
  rw [map_smul]
  rw [ZS.diagMap, LinearEquiv.trans_apply, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
  have hk : b.equivFun (b k) = Pi.single k 1 := by
    funext j
    rw [Module.Basis.equivFun_self, Pi.single_apply]
    by_cases h : k = j
    · rw [if_pos h, if_pos h.symm]
    · rw [if_neg h, if_neg (fun hh => h hh.symm)]
  rw [hk]
  funext j
  by_cases h : j = k
  · subst h; rfl
  · simp [Pi.single_apply, h]

private lemma l05nK42_ext_basis
    {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V) {e₁ e₂ : V ≃ₗ[ZMod p] V}
    (h : ∀ k, e₁ (b k) = e₂ (b k)) : e₁ = e₂ := by
  apply LinearEquiv.ext
  intro v
  have h' : (e₁ : V →ₗ[ZMod p] V) = (e₂ : V →ₗ[ZMod p] V) := by
    apply Module.Basis.ext
    exact h
  exact congrArg (fun f : V →ₗ[ZMod p] V => f v) h'

private noncomputable def l05nK42_S
    {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V) (i : Fin n) : V ≃ₗ[ZMod p] V :=
  ZS.diagMap p b (fun j => if j = i then -1 else 1)

private noncomputable def l05nK42_Tp
    {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V) (i j : Fin n) : V ≃ₗ[ZMod p] V :=
  ZS.permMap p b (Equiv.swap i j)

private noncomputable def l05nK42_Tm
    {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V) (i j : Fin n) : V ≃ₗ[ZMod p] V :=
  ZS.permMap p b (Equiv.swap i j) *
    ZS.diagMap p b (fun k => if k = i ∨ k = j then -1 else 1)

private lemma l05nK42_S_apply
    {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V) (i k : Fin n) :
    l05nK42_S b i (b k) = (if k = i then -1 else 1 : ZMod p) • b k := by
  rw [l05nK42_S, l05nK42_diagMap_apply]
  congr 1
  by_cases h : k = i <;> simp [h]

private lemma l05nK42_permMap_apply
    {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V) (σ : Equiv.Perm (Fin n)) (k : Fin n) :
    ZS.permMap p b σ (b k) = b (σ k) :=
  Module.Basis.equiv_apply (b := b) (b' := b) (e := σ) (i := k)

private lemma l05nK42_Tp_apply
    {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V) (i j k : Fin n) :
    l05nK42_Tp b i j (b k) = b (Equiv.swap i j k) := by
  rw [l05nK42_Tp, l05nK42_permMap_apply]

private lemma l05nK42_Tm_apply
    {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V) (i j k : Fin n) :
    l05nK42_Tm b i j (b k) =
      (if k = i ∨ k = j then -1 else 1 : ZMod p) • b (Equiv.swap i j k) := by
  rw [l05nK42_Tm, LinearEquiv.mul_apply, l05nK42_diagMap_apply, map_smul,
    l05nK42_permMap_apply]
  congr 1
  by_cases h : k = i ∨ k = j <;> simp [h]

private lemma l05nK42_S_mul_self
    {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V) (i : Fin n) :
    l05nK42_S b i * l05nK42_S b i = 1 := by
  apply l05nK42_ext_basis (b := b)
  intro k
  rw [LinearEquiv.mul_apply, l05nK42_S_apply, map_smul, l05nK42_S_apply, smul_smul]
  by_cases h : k = i <;> simp [h]

private lemma l05nK42_Tp_mul_self
    {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V) (i j : Fin n) :
    l05nK42_Tp b i j * l05nK42_Tp b i j = 1 := by
  apply l05nK42_ext_basis (b := b)
  intro k
  rw [LinearEquiv.mul_apply, l05nK42_Tp_apply, l05nK42_Tp_apply, Equiv.swap_apply_self]
  simp

private lemma l05nK42_Tm_mul_self
    {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V) (i j : Fin n) :
    l05nK42_Tm b i j * l05nK42_Tm b i j = 1 := by
  apply l05nK42_ext_basis (b := b)
  intro k
  have hd : (if Equiv.swap i j k = i ∨ Equiv.swap i j k = j then -1 else 1 : ZMod p) =
      (if k = i ∨ k = j then -1 else 1 : ZMod p) := by
    by_cases h : k = i
    · subst h; simp
    · by_cases h' : k = j
      · subst h'; simp
      · rw [Equiv.swap_apply_of_ne_of_ne h h']
  rw [LinearEquiv.mul_apply, l05nK42_Tm_apply, map_smul, l05nK42_Tm_apply,
    Equiv.swap_apply_self, smul_smul, hd]
  by_cases h : k = i ∨ k = j <;> simp [h]

private lemma l05nK42_reflection_eq
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V) (r : V ≃ₗ[ZMod p] V) (hr : GGLinRefl r)
    (σ : Equiv.Perm (Fin n)) (c : Fin n → ZMod p) (hc : ∀ i, c i = 1 ∨ c i = -1)
    (hrb : ∀ i, r (b i) = c i • b (σ i)) :
    (∃ i, r = l05nK42_S b i) ∨
      ∃ i j, i ≠ j ∧ (r = l05nK42_Tp b i j ∨ r = l05nK42_Tm b i j) := by
  rcases l05nK42_refl_shape hp2 b r hr σ c hc hrb with
    ⟨i, hσ, hci, hcj⟩ | ⟨i, j, hij, hσ, hcij, hck⟩
  · left
    refine ⟨i, ?_⟩
    apply l05nK42_ext_basis (b := b)
    intro k
    rw [hrb k, hσ, Equiv.Perm.one_apply, l05nK42_S_apply]
    by_cases hk : k = i
    · rw [hk, hci]; simp
    · rw [hcj k hk]; simp [hk]
  · right
    refine ⟨i, j, hij, ?_⟩
    rcases hc i with hci | hci
    · left
      have hcj : c j = 1 := by simpa [hci] using hcij
      have hc1 : ∀ k, c k = 1 := by
        intro k
        by_cases hk : k = i
        · rw [hk]; exact hci
        · by_cases hk' : k = j
          · rw [hk']; exact hcj
          · exact hck k hk hk'
      apply l05nK42_ext_basis (b := b)
      intro k
      rw [hrb k, hσ, l05nK42_Tp_apply, hc1 k, one_smul]
    · right
      have hcj : c j = -1 := by
        have h3 : (-1 : ZMod p) * c j = 1 := by simpa [hci] using hcij
        have h2 : (-1 : ZMod p) * c j = (-1) * (-1) := by rw [h3]; ring
        exact mul_left_cancel₀ (neg_ne_zero.mpr one_ne_zero) h2
      have hcval : ∀ k, c k = (if k = i ∨ k = j then -1 else 1 : ZMod p) := by
        intro k
        by_cases hk : k = i
        · rw [hk, hci]; simp
        · by_cases hk' : k = j
          · rw [hk', hcj]; simp
          · rw [hck k hk hk']; simp [hk, hk']
      apply l05nK42_ext_basis (b := b)
      intro k
      rw [hrb k, hσ, l05nK42_Tm_apply, hcval k]

private lemma l05nK42_conj_S
    {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V) (i j : Fin n)
    (t : V ≃ₗ[ZMod p] V)
    (ht : t = l05nK42_Tp b i j ∨ t = l05nK42_Tm b i j) :
    t * l05nK42_S b j * t⁻¹ = l05nK42_S b i := by
  rcases ht with rfl | rfl
  · rw [inv_eq_of_mul_eq_one_right (l05nK42_Tp_mul_self b i j)]
    apply l05nK42_ext_basis (b := b)
    intro k
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, l05nK42_Tp_apply, l05nK42_S_apply,
      map_smul, l05nK42_Tp_apply, Equiv.swap_apply_self, l05nK42_S_apply]
    have hcoef : (if Equiv.swap i j k = j then -1 else 1 : ZMod p) =
        (if k = i then -1 else 1 : ZMod p) := by
      by_cases hk : k = i
      · rw [hk, Equiv.swap_apply_left]; simp
      · by_cases hk' : k = j
        · rw [hk', Equiv.swap_apply_right]; simp [eq_comm]
        · rw [Equiv.swap_apply_of_ne_of_ne hk hk', if_neg hk', if_neg hk]
    rw [hcoef]
  · rw [inv_eq_of_mul_eq_one_right (l05nK42_Tm_mul_self b i j)]
    apply l05nK42_ext_basis (b := b)
    intro k
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, l05nK42_Tm_apply]
    rw [map_smul, l05nK42_S_apply]
    rw [map_smul]
    rw [map_smul]
    rw [l05nK42_Tm_apply, Equiv.swap_apply_self]
    rw [l05nK42_S_apply]
    have hd : (if Equiv.swap i j k = i ∨ Equiv.swap i j k = j then -1 else 1 : ZMod p) =
        (if k = i ∨ k = j then -1 else 1 : ZMod p) := by
      by_cases hk : k = i
      · rw [hk]; simp
      · by_cases hk' : k = j
        · rw [hk']; simp
        · rw [Equiv.swap_apply_of_ne_of_ne hk hk']
    have hsw : (if Equiv.swap i j k = j then -1 else 1 : ZMod p) =
        (if k = i then -1 else 1 : ZMod p) := by
      by_cases hk : k = i
      · rw [hk, Equiv.swap_apply_left]; simp
      · by_cases hk' : k = j
        · rw [hk', Equiv.swap_apply_right]; simp [eq_comm]
        · rw [Equiv.swap_apply_of_ne_of_ne hk hk', if_neg hk', if_neg hk]
    rw [hd, hsw]
    simp only [smul_smul]
    by_cases hki : k = i
    · simp [hki]
    · by_cases hkj : k = j
      · by_cases hji : j = i <;> simp [hki, hkj, hji]
      · simp [hki, hkj]

end Cat

section Graph

private lemma l05nK42_Tp_comm
    {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V) (i j : Fin n) :
    l05nK42_Tp b j i = l05nK42_Tp b i j := by
  simp only [l05nK42_Tp, Equiv.swap_comm]

private lemma l05nK42_Tm_comm
    {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V) (i j : Fin n) :
    l05nK42_Tm b j i = l05nK42_Tm b i j := by
  apply l05nK42_ext_basis (b := b)
  intro k
  rw [l05nK42_Tm_apply, l05nK42_Tm_apply, Equiv.swap_comm]
  congr 1
  by_cases h : k = i <;> by_cases h' : k = j <;> simp [h, h']

private lemma l05nK42_graph_connected
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V)
    (A : Subgroup (V ≃ₗ[ZMod p] V)) (hirr : ZS.AbsIrred p A)
    (hgen : A = Subgroup.closure {r | r ∈ A ∧ GGLinRefl r})
    (hmon : ∀ a ∈ A, ∃ (σ : Equiv.Perm (Fin n)) (c : Fin n → ZMod p),
      (∀ i, c i = 1 ∨ c i = -1) ∧ ∀ i, a (b i) = c i • b (σ i))
    (S : Set (Fin n))
    (hclosed : ∀ i j, i ∈ S →
      (l05nK42_Tp b i j ∈ A ∨ l05nK42_Tm b i j ∈ A) → j ∈ S)
    (hne : S.Nonempty) :
    S = Set.univ := by
  classical
  let W : Submodule (ZMod p) V := Submodule.span (ZMod p) (b '' S)
  have hsq_of_mul : ∀ (e : V ≃ₗ[ZMod p] V), e * e = 1 → ∀ v, e (e v) = v := by
    intro e he v
    have h := congrArg (fun f : V ≃ₗ[ZMod p] V => f v) he
    rw [LinearEquiv.mul_apply] at h
    simpa using h
  have hPres : ∀ r ∈ A, GGLinRefl r → W.map (r : V →ₗ[ZMod p] V) = W := by
    intro r hrA hrRefl
    obtain ⟨σ, c, hc, hrb⟩ := hmon r hrA
    rcases l05nK42_reflection_eq hp2 b r hrRefl σ c hc hrb with
      ⟨i, rfl⟩ | ⟨i, j, hij, hT⟩
    · have hsub : W.map ((l05nK42_S b i : V ≃ₗ[ZMod p] V) : V →ₗ[ZMod p] V) ≤ W := by
        rw [Submodule.map_le_iff_le_comap, Submodule.span_le]
        rintro x ⟨k, hkS, rfl⟩
        change (l05nK42_S b i) (b k) ∈ W
        rw [l05nK42_S_apply]
        exact W.smul_mem _ (Submodule.subset_span ⟨k, hkS, rfl⟩)
      refine le_antisymm hsub ?_
      intro w hw
      refine Submodule.mem_map.mpr
        ⟨l05nK42_S b i w, hsub (Submodule.mem_map_of_mem hw),
          hsq_of_mul (l05nK42_S b i) (l05nK42_S_mul_self b i) w⟩
    · rcases hT with rfl | rfl
      · have hswap : ∀ k, k ∈ S → Equiv.swap i j k ∈ S := by
          intro k hkS
          by_cases hk : k = i
          · rw [hk] at hkS
            rw [hk, Equiv.swap_apply_left]
            exact hclosed i j hkS (Or.inl hrA)
          · by_cases hk' : k = j
            · rw [hk'] at hkS
              rw [hk', Equiv.swap_apply_right]
              exact hclosed j i hkS (Or.inl (by rwa [l05nK42_Tp_comm]))
            · rw [Equiv.swap_apply_of_ne_of_ne hk hk']; exact hkS
        have hsub : W.map ((l05nK42_Tp b i j : V ≃ₗ[ZMod p] V) : V →ₗ[ZMod p] V) ≤ W := by
          rw [Submodule.map_le_iff_le_comap, Submodule.span_le]
          rintro x ⟨k, hkS, rfl⟩
          change (l05nK42_Tp b i j) (b k) ∈ W
          rw [l05nK42_Tp_apply]
          exact Submodule.subset_span ⟨Equiv.swap i j k, hswap k hkS, rfl⟩
        refine le_antisymm hsub ?_
        intro w hw
        refine Submodule.mem_map.mpr
          ⟨l05nK42_Tp b i j w, hsub (Submodule.mem_map_of_mem hw),
            hsq_of_mul (l05nK42_Tp b i j) (l05nK42_Tp_mul_self b i j) w⟩
      · have hswap : ∀ k, k ∈ S → Equiv.swap i j k ∈ S := by
          intro k hkS
          by_cases hk : k = i
          · rw [hk] at hkS
            rw [hk, Equiv.swap_apply_left]
            exact hclosed i j hkS (Or.inr hrA)
          · by_cases hk' : k = j
            · rw [hk'] at hkS
              rw [hk', Equiv.swap_apply_right]
              exact hclosed j i hkS (Or.inr (by rwa [l05nK42_Tm_comm]))
            · rw [Equiv.swap_apply_of_ne_of_ne hk hk']; exact hkS
        have hsub : W.map ((l05nK42_Tm b i j : V ≃ₗ[ZMod p] V) : V →ₗ[ZMod p] V) ≤ W := by
          rw [Submodule.map_le_iff_le_comap, Submodule.span_le]
          rintro x ⟨k, hkS, rfl⟩
          change (l05nK42_Tm b i j) (b k) ∈ W
          rw [l05nK42_Tm_apply]
          exact W.smul_mem _ (Submodule.subset_span ⟨Equiv.swap i j k, hswap k hkS, rfl⟩)
        refine le_antisymm hsub ?_
        intro w hw
        refine Submodule.mem_map.mpr
          ⟨l05nK42_Tm b i j w, hsub (Submodule.mem_map_of_mem hw),
            hsq_of_mul (l05nK42_Tm b i j) (l05nK42_Tm_mul_self b i j) w⟩
  have hA : ∀ a ∈ A, W.map (a : V →ₗ[ZMod p] V) = W := by
    let H : Subgroup (V ≃ₗ[ZMod p] V) :=
      { carrier := {a | W.map (a : V →ₗ[ZMod p] V) = W}
        one_mem' := by
          show W.map ((1 : V ≃ₗ[ZMod p] V) : V →ₗ[ZMod p] V) = W
          rw [LinearEquiv.coe_toLinearMap_one, Submodule.map_id]
        mul_mem' := by
          intro x y hx hy
          show W.map ((x * y : V ≃ₗ[ZMod p] V) : V →ₗ[ZMod p] V) = W
          rw [LinearEquiv.coe_toLinearMap_mul, Module.End.mul_eq_comp, Submodule.map_comp, hy, hx]
        inv_mem' := by
          intro x hx
          show W.map ((x⁻¹ : V ≃ₗ[ZMod p] V) : V →ₗ[ZMod p] V) = W
          have hcomp : (W.map (x : V →ₗ[ZMod p] V)).map
                ((x⁻¹ : V ≃ₗ[ZMod p] V) : V →ₗ[ZMod p] V) =
              W.map (((x⁻¹ : V ≃ₗ[ZMod p] V) * x : V ≃ₗ[ZMod p] V) : V →ₗ[ZMod p] V) := by
            rw [LinearEquiv.coe_toLinearMap_mul, Module.End.mul_eq_comp, Submodule.map_comp]
          rw [hx, inv_mul_cancel, LinearEquiv.coe_toLinearMap_one, Submodule.map_id] at hcomp
          exact hcomp }
    have hle : Subgroup.closure {r | r ∈ A ∧ GGLinRefl r} ≤ H := by
      rw [Subgroup.closure_le]
      rintro r ⟨hrA, hrRefl⟩
      exact hPres r hrA hrRefl
    intro a ha
    exact hle (by rwa [← hgen])
  have hW : W = ⊥ ∨ W = ⊤ :=
    hirr.1 W fun a ha w hw => by
      have := hA a ha
      exact this ▸ Submodule.mem_map_of_mem hw
  have hWtop : W = ⊤ := by
    rcases hW with hbot | htop
    · exfalso
      obtain ⟨i, hiS⟩ := hne
      have : b i ∈ W := Submodule.subset_span ⟨i, hiS, rfl⟩
      rw [hbot] at this
      exact b.ne_zero i (by simpa using this)
    · exact htop
  ext j
  constructor
  · intro _; exact Set.mem_univ j
  · intro _
    by_contra hj
    have hmem : b j ∈ W := by rw [hWtop]; exact Submodule.mem_top
    have hspan : b j ∈ Submodule.span (ZMod p) (b '' S) := hmem
    have hzero : b.equivFun (b j) j = 0 := by
      let K : Submodule (ZMod p) V :=
        { carrier := {x | b.equivFun x j = 0}
          zero_mem' := by show b.equivFun 0 j = 0; rw [map_zero, Pi.zero_apply]
          add_mem' := by
            intro x y hx hy
            show b.equivFun (x + y) j = 0
            rw [map_add, Pi.add_apply, hx, hy, add_zero]
          smul_mem' := by
            intro a x hx
            show b.equivFun (a • x) j = 0
            rw [map_smul, Pi.smul_apply, hx, smul_zero] }
      have hK : b '' S ⊆ K := by
        rintro x ⟨k, hkS, rfl⟩
        show b.equivFun (b k) j = 0
        rw [Module.Basis.equivFun_self]
        by_cases hk : k = j
        · exact absurd (hk ▸ hkS) hj
        · simp [hk]
      exact (Submodule.span_le.mpr hK) hspan
    rw [Module.Basis.equivFun_self] at hzero
    simp [hj] at hzero

end Graph

section Dichotomy

private lemma l05nK42_sign_changes_all
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V)
    (A : Subgroup (V ≃ₗ[ZMod p] V)) (hirr : ZS.AbsIrred p A)
    (hgen : A = Subgroup.closure {r | r ∈ A ∧ GGLinRefl r})
    (hmon : ∀ a ∈ A, ∃ (σ : Equiv.Perm (Fin n)) (c : Fin n → ZMod p),
      (∀ i, c i = 1 ∨ c i = -1) ∧ ∀ i, a (b i) = c i • b (σ i))
    {i : Fin n} (hi : l05nK42_S b i ∈ A) :
    ∀ j, l05nK42_S b j ∈ A := by
  classical
  let Sset : Set (Fin n) := {j | l05nK42_S b j ∈ A}
  have hSne : Sset.Nonempty := ⟨i, hi⟩
  have hclosed : ∀ p q, p ∈ Sset →
      (l05nK42_Tp b p q ∈ A ∨ l05nK42_Tm b p q ∈ A) → q ∈ Sset := by
    intro p q hp hT
    rcases hT with hT | hT
    · have hconj := l05nK42_conj_S b q p (l05nK42_Tp b p q) (Or.inl (l05nK42_Tp_comm b q p))
      change l05nK42_S b q ∈ A
      rw [← hconj]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hT hp) (Subgroup.inv_mem _ hT)
    · have hconj := l05nK42_conj_S b q p (l05nK42_Tm b p q) (Or.inr (l05nK42_Tm_comm b q p))
      change l05nK42_S b q ∈ A
      rw [← hconj]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hT hp) (Subgroup.inv_mem _ hT)
  have hSuniv := l05nK42_graph_connected hp2 b A hirr hgen hmon Sset hclosed hSne
  intro j
  have : j ∈ Sset := by rw [hSuniv]; exact Set.mem_univ j
  exact this

end Dichotomy

section SignedClass

private def l05nK42_tw {p : ℕ} {n : ℕ} (i j k : Fin n) : ZMod p :=
  if k = i ∨ k = j then -1 else 1

private lemma l05nK42_Tm_apply_tw
    {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V) (i j k : Fin n) :
    l05nK42_Tm b i j (b k) = l05nK42_tw (p := p) i j k • b (Equiv.swap i j k) := by
  rw [l05nK42_Tm_apply]; rfl

private lemma l05nK42_tw_self {p : ℕ} {n : ℕ} (i j k : Fin n) :
    l05nK42_tw (p := p) i j k * l05nK42_tw (p := p) i j k = 1 := by
  rw [l05nK42_tw]
  by_cases h : k = i ∨ k = j <;> simp [h]

private lemma l05nK42_tw_eq_neg_or_one {p : ℕ} {n : ℕ} (i j k : Fin n) :
    l05nK42_tw (p := p) i j k = -1 ∨ l05nK42_tw (p := p) i j k = 1 := by
  rw [l05nK42_tw]
  by_cases h : k = i ∨ k = j <;> simp [h]

private lemma l05nK42_swap_conj {n : ℕ} {i j k m : Fin n}
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    Equiv.swap i j (Equiv.swap j k (Equiv.swap i j m)) = Equiv.swap i k m := by
  by_cases hmi : m = i
  · rw [hmi, Equiv.swap_apply_left, Equiv.swap_apply_left,
      show Equiv.swap i j k = k from Equiv.swap_apply_of_ne_of_ne (Ne.symm hik) (Ne.symm hjk),
      Equiv.swap_apply_left]
  · by_cases hmj : m = j
    · rw [hmj, Equiv.swap_apply_right,
        show Equiv.swap j k i = i from Equiv.swap_apply_of_ne_of_ne hij hik,
        Equiv.swap_apply_left,
        show Equiv.swap i k j = j from Equiv.swap_apply_of_ne_of_ne (Ne.symm hij) hjk]
    · by_cases hmk : m = k
      · rw [hmk, show Equiv.swap i j k = k from
            Equiv.swap_apply_of_ne_of_ne (Ne.symm hik) (Ne.symm hjk),
          Equiv.swap_apply_right, Equiv.swap_apply_right, Equiv.swap_apply_right]
      · rw [show Equiv.swap i j m = m from Equiv.swap_apply_of_ne_of_ne hmi hmj,
          show Equiv.swap j k m = m from Equiv.swap_apply_of_ne_of_ne hmj hmk,
          show Equiv.swap i j m = m from Equiv.swap_apply_of_ne_of_ne hmi hmj,
          show Equiv.swap i k m = m from Equiv.swap_apply_of_ne_of_ne hmi hmk]

private lemma l05nK42_tw_swap₁ {p : ℕ} {n : ℕ} {i j k m : Fin n}
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    l05nK42_tw (p := p) j k (Equiv.swap i j m) = l05nK42_tw (p := p) i k m := by
  by_cases hmi : m = i
  · rw [hmi, Equiv.swap_apply_left]
    simp [l05nK42_tw]
  · by_cases hmj : m = j
    · rw [hmj, Equiv.swap_apply_right]
      simp [l05nK42_tw, hij, Ne.symm hij, hik, Ne.symm hik, hjk, Ne.symm hjk]
    · by_cases hmk : m = k
      · rw [hmk, show Equiv.swap i j k = k from
            Equiv.swap_apply_of_ne_of_ne (Ne.symm hik) (Ne.symm hjk)]
        simp [l05nK42_tw]
      · rw [show Equiv.swap i j m = m from Equiv.swap_apply_of_ne_of_ne hmi hmj]
        simp [l05nK42_tw, hmi, Ne.symm hmi, hmj, Ne.symm hmj, hmk, Ne.symm hmk]

private lemma l05nK42_tw_mul_swap {p : ℕ} {n : ℕ} {i j k m : Fin n}
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    l05nK42_tw (p := p) i j m * l05nK42_tw (p := p) i j (Equiv.swap j k (Equiv.swap i j m))
      = l05nK42_tw (p := p) i k m := by
  by_cases hmi : m = i
  · rw [hmi, Equiv.swap_apply_left, Equiv.swap_apply_left]
    simp [l05nK42_tw, hij, Ne.symm hij, hik, Ne.symm hik, hjk, Ne.symm hjk]
  · by_cases hmj : m = j
    · rw [hmj, Equiv.swap_apply_right,
        show Equiv.swap j k i = i from Equiv.swap_apply_of_ne_of_ne hij hik]
      simp [l05nK42_tw, hij, Ne.symm hij, hjk, Ne.symm hjk]
    · by_cases hmk : m = k
      · rw [hmk, show Equiv.swap i j k = k from
              Equiv.swap_apply_of_ne_of_ne (Ne.symm hik) (Ne.symm hjk),
            Equiv.swap_apply_right]
        simp [l05nK42_tw, hik, Ne.symm hik, hjk, Ne.symm hjk]
      · rw [show Equiv.swap i j m = m from Equiv.swap_apply_of_ne_of_ne hmi hmj,
            show Equiv.swap j k m = m from Equiv.swap_apply_of_ne_of_ne hmj hmk]
        simp [l05nK42_tw, hmi, hmj, hmk]

private lemma l05nK42_tw_product_sign
    {p : ℕ} {n : ℕ} {i j : Fin n} (hij : i ≠ j) (k : Fin n) :
    l05nK42_tw (p := p) i j k =
      (if k = i then -1 else 1 : ZMod p) * (if k = j then -1 else 1) := by
  rw [l05nK42_tw]
  by_cases hki : k = i
  · rw [if_pos (Or.inl hki), if_pos hki, if_neg (fun h => hij (hki ▸ h))]
    ring
  · by_cases hkj : k = j
    · rw [if_pos (Or.inr hkj), if_neg hki, if_pos hkj]; ring
    · rw [if_neg (fun h => h.elim hki hkj), if_neg hki, if_neg hkj]; ring

private lemma l05nK42_conj_Tp_Tp
    {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V) {i j k : Fin n}
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    l05nK42_Tp b i j * l05nK42_Tp b j k * l05nK42_Tp b i j = l05nK42_Tp b i k := by
  apply l05nK42_ext_basis (b := b)
  intro m
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply]
  simp only [l05nK42_Tp_apply]
  rw [l05nK42_swap_conj hij hjk hik]

private lemma l05nK42_conj_Tp_Tm
    {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V) {i j k : Fin n}
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    l05nK42_Tp b i j * l05nK42_Tm b j k * l05nK42_Tp b i j = l05nK42_Tm b i k := by
  apply l05nK42_ext_basis (b := b)
  intro m
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply]
  simp only [l05nK42_Tp_apply, l05nK42_Tm_apply_tw, map_smul, smul_smul]
  rw [l05nK42_swap_conj hij hjk hik]
  rw [l05nK42_tw_swap₁ hij hjk hik]

private lemma l05nK42_conj_Tm_Tp
    {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V) {i j k : Fin n}
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    l05nK42_Tm b i j * l05nK42_Tp b j k * l05nK42_Tm b i j = l05nK42_Tm b i k := by
  apply l05nK42_ext_basis (b := b)
  intro m
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply]
  simp only [l05nK42_Tp_apply, l05nK42_Tm_apply_tw, map_smul, smul_smul]
  rw [l05nK42_swap_conj hij hjk hik]
  rw [l05nK42_tw_mul_swap hij hjk hik]

private lemma l05nK42_conj_Tm_Tm
    {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V) {i j k : Fin n}
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    l05nK42_Tm b i j * l05nK42_Tm b j k * l05nK42_Tm b i j = l05nK42_Tp b i k := by
  apply l05nK42_ext_basis (b := b)
  intro m
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply]
  simp only [l05nK42_Tp_apply, l05nK42_Tm_apply_tw, map_smul, smul_smul]
  rw [l05nK42_swap_conj hij hjk hik, l05nK42_tw_swap₁ hij hjk hik]
  rw [show l05nK42_tw (p := p) i j m * l05nK42_tw (p := p) i k m *
        l05nK42_tw (p := p) i j (Equiv.swap j k (Equiv.swap i j m)) =
      (l05nK42_tw (p := p) i j m *
        l05nK42_tw (p := p) i j (Equiv.swap j k (Equiv.swap i j m))) *
          l05nK42_tw (p := p) i k m by ring]
  rw [l05nK42_tw_mul_swap hij hjk hik]
  rw [l05nK42_tw_self, one_smul]

private def l05nK42_Gamma
    {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V) (A : Subgroup (V ≃ₗ[ZMod p] V))
    (i j : Fin n) : Prop :=
  l05nK42_Tp b i j ∈ A ∨ l05nK42_Tm b i j ∈ A

private lemma l05nK42_Gamma_self
    {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V) (A : Subgroup (V ≃ₗ[ZMod p] V))
    (i : Fin n) : l05nK42_Gamma b A i i := by
  left
  have h : l05nK42_Tp b i i = 1 := by
    apply l05nK42_ext_basis (b := b)
    intro k
    rw [l05nK42_Tp_apply]
    simp
  rw [h]
  exact A.one_mem

private lemma l05nK42_Gamma_comm
    {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V) (A : Subgroup (V ≃ₗ[ZMod p] V))
    {i j : Fin n} (h : l05nK42_Gamma b A i j) : l05nK42_Gamma b A j i := by
  rcases h with h | h
  · exact Or.inl (by rwa [l05nK42_Tp_comm])
  · exact Or.inr (by rwa [l05nK42_Tm_comm])

private lemma l05nK42_Gamma_step_distinct
    {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V) (A : Subgroup (V ≃ₗ[ZMod p] V))
    {i j k : Fin n} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (h1 : l05nK42_Gamma b A i j) (h2 : l05nK42_Gamma b A j k) :
    l05nK42_Gamma b A i k := by
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · exact Or.inl (by
      rw [← l05nK42_conj_Tp_Tp b hij hjk hik]
      exact A.mul_mem (A.mul_mem h1 h2) h1)
  · exact Or.inr (by
      rw [← l05nK42_conj_Tp_Tm b hij hjk hik]
      exact A.mul_mem (A.mul_mem h1 h2) h1)
  · exact Or.inr (by
      rw [← l05nK42_conj_Tm_Tp b hij hjk hik]
      exact A.mul_mem (A.mul_mem h1 h2) h1)
  · exact Or.inl (by
      rw [← l05nK42_conj_Tm_Tm b hij hjk hik]
      exact A.mul_mem (A.mul_mem h1 h2) h1)

private lemma l05nK42_Gamma_trans
    {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V) (A : Subgroup (V ≃ₗ[ZMod p] V))
    {i j k : Fin n} (h1 : l05nK42_Gamma b A i j) (h2 : l05nK42_Gamma b A j k)
    (hik : i ≠ k) : l05nK42_Gamma b A i k := by
  rcases eq_or_ne j i with rfl | hji
  · exact h2
  · rcases eq_or_ne j k with rfl | hjk
    · exact h1
    · exact l05nK42_Gamma_step_distinct b A (Ne.symm hji) hjk hik h1 h2

private lemma l05nK42_Gamma_all
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V)
    (A : Subgroup (V ≃ₗ[ZMod p] V)) (hirr : ZS.AbsIrred p A)
    (hgen : A = Subgroup.closure {r | r ∈ A ∧ GGLinRefl r})
    (hmon : ∀ a ∈ A, ∃ (σ : Equiv.Perm (Fin n)) (c : Fin n → ZMod p),
      (∀ i, c i = 1 ∨ c i = -1) ∧ ∀ i, a (b i) = c i • b (σ i))
    (i : Fin n) : ∀ j, l05nK42_Gamma b A i j := by
  intro j
  let S : Set (Fin n) := {k | k = i ∨ l05nK42_Gamma b A i k}
  have hSne : S.Nonempty := ⟨i, Or.inl rfl⟩
  have hclosed : ∀ p q, p ∈ S →
      (l05nK42_Tp b p q ∈ A ∨ l05nK42_Tm b p q ∈ A) → q ∈ S := by
    intro p q hp hpq
    rcases hp with rfl | hip
    · exact Or.inr hpq
    · by_cases hqi : q = i
      · exact Or.inl hqi
      · exact Or.inr (l05nK42_Gamma_trans b A hip hpq (Ne.symm hqi))
  have hSuniv := l05nK42_graph_connected hp2 b A hirr hgen hmon S hclosed hSne
  have hj : j ∈ S := by rw [hSuniv]; exact Set.mem_univ j
  rcases hj with rfl | h
  · exact l05nK42_Gamma_self b A j
  · exact h

private lemma l05nK42_one_ne_neg_one {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    (1 : ZMod p) ≠ -1 := by
  intro h
  have h2 : (2 : ZMod p) = 0 := by
    have := congrArg (fun x : ZMod p => x + 1) h
    simpa [one_add_one_eq_two] using this
  have hp : p.Prime := Fact.out
  have hdvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h2
  have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
  exact hp2 (le_antisymm hle hp.two_le)

private lemma l05nK42_sign_mul {p : ℕ} (x y : ZMod p)
    (hx : x = 1 ∨ x = -1) (hy : y = 1 ∨ y = -1) : x * y = 1 ∨ x * y = -1 := by
  rcases hx with hx | hx <;> rcases hy with hy | hy <;> rw [hx, hy] <;> norm_num

private lemma l05nK42_monomial_mul
    {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} {b : Module.Basis (Fin n) (ZMod p) V} {a a' : V ≃ₗ[ZMod p] V}
    {σ σ' : Equiv.Perm (Fin n)} {c c' : Fin n → ZMod p}
    (ha : ∀ i, a (b i) = c i • b (σ i))
    (ha' : ∀ i, a' (b i) = c' i • b (σ' i)) (i : Fin n) :
    (a * a') (b i) = (c' i * c (σ' i)) • b (σ (σ' i)) := by
  rw [LinearEquiv.mul_apply, ha', map_smul, ha, smul_smul]

private lemma l05nK42_monomial_pair_unique
    {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} {b : Module.Basis (Fin n) (ZMod p) V} {a : V ≃ₗ[ZMod p] V}
    {σ₁ σ₂ : Equiv.Perm (Fin n)} {c₁ c₂ : Fin n → ZMod p}
    (h1 : ∀ i, a (b i) = c₁ i • b (σ₁ i))
    (h2 : ∀ i, a (b i) = c₂ i • b (σ₂ i))
    (hc1 : ∀ i, c₁ i = 1 ∨ c₁ i = -1) :
    σ₁ = σ₂ ∧ c₁ = c₂ := by
  have hσ : σ₁ = σ₂ := by
    ext i
    by_contra hne
    have heq : c₁ i • b (σ₁ i) = c₂ i • b (σ₂ i) := by rw [← h1 i, h2 i]
    have h := congrArg (fun v => b.equivFun v (σ₁ i)) heq
    simp only [map_smul, Pi.smul_apply, smul_eq_mul, Module.Basis.equivFun_self] at h
    rw [if_neg (show ¬ (σ₂ i = σ₁ i) from fun hh => hne (congrArg Fin.val hh.symm))] at h
    simp at h
    rcases hc1 i with hc | hc
    · rw [hc] at h; exact one_ne_zero h
    · rw [hc] at h; exact neg_ne_zero.mpr one_ne_zero h
  refine ⟨hσ, ?_⟩
  funext i
  have h := h1 i
  rw [h2 i, hσ] at h
  have h' := congrArg (fun v => b.equivFun v (σ₂ i)) h
  simp only [map_smul, Pi.smul_apply, smul_eq_mul, Module.Basis.equivFun_self] at h'
  simp at h'
  exact h'.symm

private def l05nK42_PDsub
    {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V) : Subgroup (V ≃ₗ[ZMod p] V) where
  carrier := {a | ∃ (σ : Equiv.Perm (Fin n)) (c : Fin n → ZMod p),
      (∀ i, c i = 1 ∨ c i = -1) ∧ (∏ i, c i = 1) ∧ ∀ i, a (b i) = c i • b (σ i)}
  one_mem' := by
    refine ⟨1, fun _ => 1, ?_, ?_, ?_⟩
    · intro i; left; rfl
    · simp
    · intro i; simp
  mul_mem' := by
    rintro a a' ⟨σ, c, hc, hprod, ha⟩ ⟨σ', c', hc', hprod', ha'⟩
    refine ⟨σ * σ', fun i => c' i * c (σ' i), ?_, ?_, ?_⟩
    · intro i; exact l05nK42_sign_mul _ _ (hc' i) (hc (σ' i))
    · rw [Finset.prod_mul_distrib]
      have hre : ∏ i, c (σ' i) = ∏ i, c i :=
        Fintype.prod_equiv σ' (fun i => c (σ' i)) c (fun i => rfl)
      rw [hre, hprod, hprod', mul_one]
    · intro i; exact l05nK42_monomial_mul ha ha' i
  inv_mem' := by
    rintro a ⟨σ, c, hc, hprod, ha⟩
    refine ⟨σ⁻¹, fun i => c (σ⁻¹ i), ?_, ?_, ?_⟩
    · intro i; exact hc _
    · have hre : ∏ i, c (σ⁻¹ i) = ∏ i, c i :=
        Fintype.prod_equiv σ⁻¹ (fun i => c (σ⁻¹ i)) c (fun i => rfl)
      rw [hre, hprod]
    · intro i
      apply a.injective
      change a (a.symm (b i)) = a (c (σ⁻¹ i) • b (σ⁻¹ i))
      rw [LinearEquiv.apply_symm_apply, map_smul, ha (σ⁻¹ i)]
      rw [show σ (σ⁻¹ i) = i from Equiv.apply_symm_apply σ i, smul_smul]
      rcases hc (σ⁻¹ i) with h | h <;> rw [h] <;> simp

private lemma l05nK42_permMap_one
    {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V) :
    ZS.permMap p b 1 = (1 : V ≃ₗ[ZMod p] V) := by
  apply l05nK42_ext_basis (b := b)
  intro k
  rw [l05nK42_permMap_apply]
  simp

private lemma l05nK42_permMap_mul
    {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V) (σ τ : Equiv.Perm (Fin n)) :
    ZS.permMap p b (σ * τ) = ZS.permMap p b σ * ZS.permMap p b τ := by
  apply l05nK42_ext_basis (b := b)
  intro k
  rw [LinearEquiv.mul_apply, l05nK42_permMap_apply, l05nK42_permMap_apply, l05nK42_permMap_apply,
    Equiv.Perm.mul_apply]

private def l05nK42_du {p : ℕ} {n : ℕ} (s : Finset (Fin n)) : Fin n → (ZMod p)ˣ :=
  fun i => if i ∈ s then -1 else 1

private lemma l05nK42_diagMap_one
    {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V) :
    ZS.diagMap p b (1 : Fin n → (ZMod p)ˣ) = 1 := by
  apply l05nK42_ext_basis (b := b)
  intro k
  rw [l05nK42_diagMap_apply]
  simp

private lemma l05nK42_diagMap_mul
    {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V) (d₁ d₂ : Fin n → (ZMod p)ˣ) :
    ZS.diagMap p b d₁ * ZS.diagMap p b d₂ = ZS.diagMap p b (fun i => d₁ i * d₂ i) := by
  apply l05nK42_ext_basis (b := b)
  intro k
  rw [LinearEquiv.mul_apply, l05nK42_diagMap_apply, l05nK42_diagMap_apply, map_smul,
    l05nK42_diagMap_apply, smul_smul]
  congr 1
  rw [← Units.val_mul]
  exact mul_comm _ _

private lemma l05nK42_D_apply
    {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V) (s : Finset (Fin n)) (x : Fin n) :
    ZS.diagMap p b (l05nK42_du (p := p) s) (b x) = (if x ∈ s then -1 else 1 : ZMod p) • b x := by
  rw [l05nK42_diagMap_apply]
  congr 1
  by_cases hx : x ∈ s <;> simp [l05nK42_du, hx]

private lemma l05nK42_D_mem
    {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V) (A : Subgroup (V ≃ₗ[ZMod p] V))
    (hS : ∀ i, l05nK42_S b i ∈ A) (s : Finset (Fin n)) :
    ZS.diagMap p b (l05nK42_du (p := p) s) ∈ A := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      have h1 : l05nK42_du (p := p) (∅ : Finset (Fin n)) = 1 := by
        funext i; simp [l05nK42_du]
      rw [h1, l05nK42_diagMap_one]
      exact A.one_mem
  | insert a s ha ih =>
      have hstep : l05nK42_du (p := p) (insert a s) =
          (fun i => if i = a then (-1 : (ZMod p)ˣ) else 1) * l05nK42_du (p := p) s := by
        funext i
        by_cases hia : i = a
        · rw [hia]; simp [l05nK42_du, ha]
        · by_cases his : i ∈ s
          · simp [l05nK42_du, Finset.mem_insert, hia, his]
          · simp [l05nK42_du, Finset.mem_insert, hia, his]
      rw [hstep]
      change ZS.diagMap p b (fun i => (if i = a then (-1 : (ZMod p)ˣ) else 1) *
        l05nK42_du (p := p) s i) ∈ A
      rw [← l05nK42_diagMap_mul]
      exact A.mul_mem (hS a) ih

private lemma l05nK42_Tp_mul_SS
    {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V) {i j : Fin n} (hij : i ≠ j) :
    l05nK42_Tp b i j * l05nK42_S b i * l05nK42_S b j = l05nK42_Tm b i j := by
  apply l05nK42_ext_basis (b := b)
  intro k
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply]
  simp only [l05nK42_Tp_apply, l05nK42_S_apply, l05nK42_Tm_apply_tw, map_smul, smul_smul]
  rw [show (if k = j then -1 else 1 : ZMod p) * (if k = i then -1 else 1)
        = l05nK42_tw (p := p) i j k by
      rw [mul_comm, ← l05nK42_tw_product_sign hij k]]

private lemma l05nK42_Tp_eq_Tm_mul_SS
    {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V) {i j : Fin n} (hij : i ≠ j) :
    l05nK42_Tp b i j = l05nK42_Tm b i j * l05nK42_S b j * l05nK42_S b i := by
  rw [← l05nK42_Tp_mul_SS b hij]
  simp only [mul_assoc, l05nK42_S_mul_self, mul_one, one_mul]

private lemma l05nK42_both_of_Gamma_of_S
    {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V) (A : Subgroup (V ≃ₗ[ZMod p] V))
    {i j : Fin n} (hij : i ≠ j)
    (hSi : l05nK42_S b i ∈ A) (hSj : l05nK42_S b j ∈ A)
    (h : l05nK42_Gamma b A i j) :
    l05nK42_Tp b i j ∈ A ∧ l05nK42_Tm b i j ∈ A := by
  have hTp : l05nK42_Tp b i j ∈ A := by
    rcases h with h | h
    · exact h
    · rw [l05nK42_Tp_eq_Tm_mul_SS b hij]
      exact A.mul_mem (A.mul_mem h hSj) hSi
  have hTm : l05nK42_Tm b i j ∈ A := by
    rcases h with h | h
    · rw [← l05nK42_Tp_mul_SS b hij]
      exact A.mul_mem (A.mul_mem h hSi) hSj
    · exact h
  exact ⟨hTp, hTm⟩

private lemma l05nK42_permMap_mem
    {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V) (A : Subgroup (V ≃ₗ[ZMod p] V))
    (hTp : ∀ i j, l05nK42_Tp b i j ∈ A) (σ : Equiv.Perm (Fin n)) :
    ZS.permMap p b σ ∈ A := by
  classical
  refine Equiv.Perm.swap_induction_on σ ?_ ?_
  · rw [l05nK42_permMap_one]; exact A.one_mem
  · intro f x y hxy hf
    rw [l05nK42_permMap_mul]
    exact A.mul_mem (hTp x y) hf

private lemma l05nK42_monomial_mem_of_S_permMap
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V) (A : Subgroup (V ≃ₗ[ZMod p] V))
    (hS : ∀ i, l05nK42_S b i ∈ A) (hP : ∀ σ, ZS.permMap p b σ ∈ A)
    {a : V ≃ₗ[ZMod p] V} {σ : Equiv.Perm (Fin n)} {c : Fin n → ZMod p}
    (hc : ∀ i, c i = 1 ∨ c i = -1) (ha : ∀ i, a (b i) = c i • b (σ i)) :
    a ∈ A := by
  classical
  let s : Finset (Fin n) := Finset.univ.filter (fun k => c (σ.symm k) = -1)
  have hDmem : ZS.diagMap p b (l05nK42_du (p := p) s) ∈ A := l05nK42_D_mem b A hS s
  have hmem : ∀ i, (σ i ∈ s) ↔ c i = -1 := by
    intro i
    simp only [s, Finset.mem_filter, Finset.mem_univ, true_and, Equiv.symm_apply_apply]
  have hDeq : a = ZS.diagMap p b (l05nK42_du (p := p) s) * ZS.permMap p b σ := by
    apply l05nK42_ext_basis (b := b)
    intro i
    rw [ha i, LinearEquiv.mul_apply, l05nK42_permMap_apply, l05nK42_D_apply]
    rcases hc i with hci | hci
    · have hni : σ i ∉ s := by
        rw [hmem i, hci]; exact fun h => l05nK42_one_ne_neg_one hp2 h
      rw [hci, if_neg hni, one_smul]
    · rw [hci, if_pos ((hmem i).mpr hci)]
  rw [hDeq]
  exact A.mul_mem hDmem (hP σ)

private lemma l05nK42_tw_swap₂ {p : ℕ} {n : ℕ} {i j k m : Fin n}
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    l05nK42_tw (p := p) i j (Equiv.swap j k m) = l05nK42_tw (p := p) i k m := by
  by_cases hmj : m = j
  · rw [hmj, Equiv.swap_apply_left]
    simp [l05nK42_tw, hij, Ne.symm hij, hik, Ne.symm hik, hjk, Ne.symm hjk]
  · by_cases hmk : m = k
    · rw [hmk, Equiv.swap_apply_right]
      simp [l05nK42_tw, hjk, Ne.symm hjk, hik, Ne.symm hik]
    · by_cases hmi : m = i
      · rw [hmi, show Equiv.swap j k i = i from Equiv.swap_apply_of_ne_of_ne hij hik]
        simp [l05nK42_tw]
      · rw [show Equiv.swap j k m = m from Equiv.swap_apply_of_ne_of_ne hmj hmk]
        simp [l05nK42_tw, hmi, hmj, hmk]

private lemma l05nK42_tw_invariant {p : ℕ} {n : ℕ} (i j m : Fin n) :
    l05nK42_tw (p := p) i j (Equiv.swap i j m) = l05nK42_tw (p := p) i j m := by
  by_cases hmi : m = i
  · rw [hmi, Equiv.swap_apply_left]; simp [l05nK42_tw]
  · by_cases hmj : m = j
    · rw [hmj, Equiv.swap_apply_right]; simp [l05nK42_tw]
    · rw [Equiv.swap_apply_of_ne_of_ne hmi hmj]

private lemma l05nK42_tw_mul_tw {p : ℕ} {n : ℕ} {i j k m : Fin n}
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    l05nK42_tw (p := p) i j m * l05nK42_tw (p := p) j k m = l05nK42_tw (p := p) i k m := by
  by_cases hmi : m = i
  · rw [hmi]
    simp [l05nK42_tw, hij, Ne.symm hij, hik, Ne.symm hik]
  · by_cases hmj : m = j
    · rw [hmj]
      simp [l05nK42_tw, hij, Ne.symm hij, hjk, Ne.symm hjk]
    · by_cases hmk : m = k
      · rw [hmk]
        simp [l05nK42_tw, hik, Ne.symm hik, hjk, Ne.symm hjk]
      · simp [l05nK42_tw, hmi, hmj, hmk]

private lemma l05nK42_tw_conj_tm_coeff {p : ℕ} {n : ℕ} {i j k m : Fin n}
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    l05nK42_tw (p := p) j k m * l05nK42_tw (p := p) i j (Equiv.swap j k m) *
      l05nK42_tw (p := p) j k (Equiv.swap j k m) = l05nK42_tw (p := p) i k m := by
  rw [l05nK42_tw_invariant j k m,
    show l05nK42_tw (p := p) j k m * l05nK42_tw (p := p) i j (Equiv.swap j k m) *
          l05nK42_tw (p := p) j k m =
        (l05nK42_tw (p := p) j k m * l05nK42_tw (p := p) j k m) *
          l05nK42_tw (p := p) i j (Equiv.swap j k m) by ring]
  rw [l05nK42_tw_self, one_mul]
  exact l05nK42_tw_swap₂ hij hjk hik

private noncomputable def l05nK42_D2
    {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V) (i j : Fin n) : V ≃ₗ[ZMod p] V :=
  l05nK42_Tp b i j * l05nK42_Tm b i j

private lemma l05nK42_D2_apply
    {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V) (i j k : Fin n) :
    l05nK42_D2 b i j (b k) = l05nK42_tw (p := p) i j k • b k := by
  rw [l05nK42_D2, LinearEquiv.mul_apply, l05nK42_Tm_apply_tw, map_smul, l05nK42_Tp_apply,
    Equiv.swap_apply_self]

private lemma l05nK42_D2_comm
    {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V) (i j : Fin n) :
    l05nK42_D2 b i j = l05nK42_D2 b j i := by
  apply l05nK42_ext_basis (b := b)
  intro k
  rw [l05nK42_D2_apply, l05nK42_D2_apply]
  congr 1
  simp [l05nK42_tw, or_comm]

private lemma l05nK42_D2_mul
    {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V) {i j k : Fin n}
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    l05nK42_D2 b i j * l05nK42_D2 b j k = l05nK42_D2 b i k := by
  apply l05nK42_ext_basis (b := b)
  intro m
  rw [LinearEquiv.mul_apply, l05nK42_D2_apply, l05nK42_D2_apply, map_smul, l05nK42_D2_apply,
    smul_smul]
  congr 1
  rw [mul_comm]
  exact l05nK42_tw_mul_tw hij hjk hik

private lemma l05nK42_conj_D2
    {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V) {i j k : Fin n}
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (t : V ≃ₗ[ZMod p] V)
    (ht : t = l05nK42_Tp b j k ∨ t = l05nK42_Tm b j k) :
    t * l05nK42_D2 b i j * t⁻¹ = l05nK42_D2 b i k := by
  rcases ht with rfl | rfl
  · rw [inv_eq_of_mul_eq_one_right (l05nK42_Tp_mul_self b j k)]
    apply l05nK42_ext_basis (b := b)
    intro m
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, l05nK42_Tp_apply, l05nK42_D2_apply,
      map_smul, l05nK42_Tp_apply, Equiv.swap_apply_self, l05nK42_D2_apply]
    congr 1
    exact l05nK42_tw_swap₂ hij hjk hik
  · rw [inv_eq_of_mul_eq_one_right (l05nK42_Tm_mul_self b j k)]
    apply l05nK42_ext_basis (b := b)
    intro m
    simp only [LinearEquiv.mul_apply, l05nK42_Tm_apply_tw, l05nK42_D2_apply, map_smul, smul_smul,
      Equiv.swap_apply_self]
    congr 1
    rw [← mul_assoc]
    exact l05nK42_tw_conj_tm_coeff hij hjk hik

private lemma l05nK42_Tp_self
    {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V) (i : Fin n) :
    l05nK42_Tp b i i = 1 := by
  apply l05nK42_ext_basis (b := b)
  intro k
  rw [l05nK42_Tp_apply]
  simp

private lemma l05nK42_Tp_all_of_S
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V)
    (A : Subgroup (V ≃ₗ[ZMod p] V)) (hirr : ZS.AbsIrred p A)
    (hgen : A = Subgroup.closure {r | r ∈ A ∧ GGLinRefl r})
    (hmon : ∀ a ∈ A, ∃ (σ : Equiv.Perm (Fin n)) (c : Fin n → ZMod p),
      (∀ i, c i = 1 ∨ c i = -1) ∧ ∀ i, a (b i) = c i • b (σ i))
    (hS : ∀ i, l05nK42_S b i ∈ A) (i j : Fin n) :
    l05nK42_Tp b i j ∈ A := by
  by_cases hij : i = j
  · rw [hij, l05nK42_Tp_self]; exact A.one_mem
  · exact (l05nK42_both_of_Gamma_of_S b A hij (hS i) (hS j)
      (l05nK42_Gamma_all hp2 b A hirr hgen hmon i j)).1

private lemma l05nK42_Tp_mem_PDsub
    {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V) (i j : Fin n) :
    l05nK42_Tp b i j ∈ l05nK42_PDsub b := by
  refine ⟨Equiv.swap i j, fun _ => 1, ?_, ?_, ?_⟩
  · intro k; left; rfl
  · simp
  · intro k; rw [l05nK42_Tp_apply]; simp

private lemma l05nK42_prod_tw
    {p : ℕ} [Fact p.Prime] {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    ∏ k, l05nK42_tw (p := p) i j k = 1 := by
  trans ∏ k, (if k = i then -1 else 1 : ZMod p) * (if k = j then -1 else 1)
  · exact Finset.prod_congr rfl (fun k _ => l05nK42_tw_product_sign hij k)
  · have h1 : ∏ k, (if k = i then -1 else 1 : ZMod p) = -1 := by
      rw [Finset.prod_eq_single i]
      · simp
      · intro b _ hb; simp [hb]
      · intro h; exact absurd (Finset.mem_univ i) h
    have h2 : ∏ k, (if k = j then -1 else 1 : ZMod p) = -1 := by
      rw [Finset.prod_eq_single j]
      · simp
      · intro b _ hb; simp [hb]
      · intro h; exact absurd (Finset.mem_univ j) h
    rw [Finset.prod_mul_distrib, h1, h2]
    norm_num

private lemma l05nK42_Tm_mem_PDsub
    {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V) {i j : Fin n} (hij : i ≠ j) :
    l05nK42_Tm b i j ∈ l05nK42_PDsub b := by
  refine ⟨Equiv.swap i j, l05nK42_tw (p := p) i j, ?_, ?_, ?_⟩
  · intro k; exact (l05nK42_tw_eq_neg_or_one i j k).symm
  · exact l05nK42_prod_tw hij
  · intro k; rw [l05nK42_Tm_apply_tw]

private lemma l05nK42_mem_PDsub
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V)
    (A : Subgroup (V ≃ₗ[ZMod p] V)) (hirr : ZS.AbsIrred p A)
    (hgen : A = Subgroup.closure {r | r ∈ A ∧ GGLinRefl r})
    (hmon : ∀ a ∈ A, ∃ (σ : Equiv.Perm (Fin n)) (c : Fin n → ZMod p),
      (∀ i, c i = 1 ∨ c i = -1) ∧ ∀ i, a (b i) = c i • b (σ i))
    (hnoS : ∀ i, l05nK42_S b i ∉ A) :
    A ≤ l05nK42_PDsub b := by
  rw [hgen, Subgroup.closure_le]
  rintro r ⟨hrA, hrRefl⟩
  obtain ⟨σ, c, hc, hrb⟩ := hmon r hrA
  rcases l05nK42_reflection_eq hp2 b r hrRefl σ c hc hrb with ⟨i, rfl⟩ | ⟨i, j, hij, hT⟩
  · exact absurd hrA (hnoS i)
  · rcases hT with rfl | rfl
    · exact l05nK42_Tp_mem_PDsub b i j
    · exact l05nK42_Tm_mem_PDsub b hij

private lemma l05nK42_prod_sign_one
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V)
    (A : Subgroup (V ≃ₗ[ZMod p] V)) (hirr : ZS.AbsIrred p A)
    (hgen : A = Subgroup.closure {r | r ∈ A ∧ GGLinRefl r})
    (hmon : ∀ a ∈ A, ∃ (σ : Equiv.Perm (Fin n)) (c : Fin n → ZMod p),
      (∀ i, c i = 1 ∨ c i = -1) ∧ ∀ i, a (b i) = c i • b (σ i))
    (hnoS : ∀ i, l05nK42_S b i ∉ A)
    {a : V ≃ₗ[ZMod p] V} (ha : a ∈ A)
    {σ : Equiv.Perm (Fin n)} {c : Fin n → ZMod p}
    (hc : ∀ i, c i = 1 ∨ c i = -1) (haa : ∀ i, a (b i) = c i • b (σ i)) :
    ∏ i, c i = 1 := by
  obtain ⟨σ', c', hc', hprod', ha'⟩ := l05nK42_mem_PDsub hp2 b A hirr hgen hmon hnoS ha
  obtain ⟨-, hcc⟩ := l05nK42_monomial_pair_unique haa ha' hc
  rw [hcc, hprod']

private lemma l05nK42_Tp_eq_D2_mul_Tm
    {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V) (i j : Fin n) :
    l05nK42_Tp b i j = l05nK42_D2 b i j * l05nK42_Tm b i j := by
  rw [l05nK42_D2]
  simp only [mul_assoc, l05nK42_Tm_mul_self, mul_one]

private lemma l05nK42_D2_all_of_pair
    {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V) (A : Subgroup (V ≃ₗ[ZMod p] V))
    (hall : ∀ i j, l05nK42_Gamma b A i j)
    {i₀ j₀ : Fin n} (hij₀ : i₀ ≠ j₀) (hD : l05nK42_D2 b i₀ j₀ ∈ A) :
    ∀ k l, k ≠ l → l05nK42_D2 b k l ∈ A := by
  have hDik : ∀ k, k ≠ i₀ → l05nK42_D2 b i₀ k ∈ A := by
    intro k hik₀
    by_cases hkj : k = j₀
    · rw [hkj]; exact hD
    · have hjk : j₀ ≠ k := Ne.symm hkj
      have hik : i₀ ≠ k := Ne.symm hik₀
      rcases hall j₀ k with ht | ht
      · have hconj := l05nK42_conj_D2 b hij₀ hjk hik (l05nK42_Tp b j₀ k) (Or.inl rfl)
        rw [← hconj]
        exact A.mul_mem (A.mul_mem ht hD) (A.inv_mem ht)
      · have hconj := l05nK42_conj_D2 b hij₀ hjk hik (l05nK42_Tm b j₀ k) (Or.inr rfl)
        rw [← hconj]
        exact A.mul_mem (A.mul_mem ht hD) (A.inv_mem ht)
  intro k l hkl
  by_cases hki : k = i₀
  · rw [hki]
    exact hDik l (fun hl => hkl (hki.trans hl.symm))
  · by_cases hli : l = i₀
    · rw [hli, l05nK42_D2_comm]
      exact hDik k hki
    · have h1 : l05nK42_D2 b k i₀ ∈ A := by
        rw [l05nK42_D2_comm]; exact hDik k hki
      have h2 : l05nK42_D2 b i₀ l ∈ A := hDik l hli
      have hmul := l05nK42_D2_mul b hki (Ne.symm hli) hkl
      rw [← hmul]
      exact A.mul_mem h1 h2

private lemma l05nK42_Tp_all_of_D2
    {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V) (A : Subgroup (V ≃ₗ[ZMod p] V))
    (hall : ∀ i j, l05nK42_Gamma b A i j)
    (hDall : ∀ k l, k ≠ l → l05nK42_D2 b k l ∈ A) (i j : Fin n) :
    l05nK42_Tp b i j ∈ A := by
  by_cases hij : i = j
  · rw [hij, l05nK42_Tp_self]; exact A.one_mem
  · rcases hall i j with h | h
    · exact h
    · rw [l05nK42_Tp_eq_D2_mul_Tm]
      exact A.mul_mem (hDall i j hij) h

private lemma l05nK42_pair_case_II
    {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V) (A : Subgroup (V ≃ₗ[ZMod p] V))
    (hall : ∀ i j, l05nK42_Gamma b A i j)
    (hpair : ∃ i j, i ≠ j ∧ l05nK42_Tp b i j ∈ A ∧ l05nK42_Tm b i j ∈ A) :
    (∀ k l, k ≠ l → l05nK42_D2 b k l ∈ A) ∧ (∀ i j, l05nK42_Tp b i j ∈ A) := by
  obtain ⟨i₀, j₀, hij₀, hTp, hTm⟩ := hpair
  have hD0 : l05nK42_D2 b i₀ j₀ ∈ A := by
    rw [l05nK42_D2]; exact A.mul_mem hTp hTm
  have hDall := l05nK42_D2_all_of_pair b A hall hij₀ hD0
  exact ⟨hDall, l05nK42_Tp_all_of_D2 b A hall hDall⟩

private lemma l05nK42_E_pair
    {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V) (a b' : Fin n) (hab : a ≠ b')
    (t' : Finset (Fin n)) (ha : a ∉ t') (hb : b' ∉ t') :
    ZS.diagMap p b (l05nK42_du (p := p) (insert a (insert b' t'))) =
      l05nK42_D2 b a b' * ZS.diagMap p b (l05nK42_du (p := p) t') := by
  apply l05nK42_ext_basis (b := b)
  intro k
  rw [LinearEquiv.mul_apply]
  simp only [l05nK42_D_apply, map_smul, l05nK42_D2_apply, smul_smul]
  congr 1
  by_cases hka : k = a
  · rw [hka]; simp [l05nK42_tw, Finset.mem_insert, ha]
  · by_cases hkb : k = b'
    · rw [hkb]; simp [l05nK42_tw, Finset.mem_insert, hb, hab, Ne.symm hab]
    · by_cases hkt : k ∈ t'
      · simp [l05nK42_tw, Finset.mem_insert, hkt, hka, hkb]
      · simp [l05nK42_tw, Finset.mem_insert, hkt, hka, hkb]

private lemma l05nK42_diag_mem_of_prod
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V) (A : Subgroup (V ≃ₗ[ZMod p] V))
    (hD : ∀ k l, k ≠ l → l05nK42_D2 b k l ∈ A)
    (s : Finset (Fin n)) (hsprod : ∏ k ∈ s, (-1 : ZMod p) = 1) :
    ZS.diagMap p b (l05nK42_du (p := p) s) ∈ A := by
  classical
  have H : ∀ m, (∀ k, k < m → ∀ t : Finset (Fin n), t.card = k →
        (∏ x ∈ t, (-1 : ZMod p)) = 1 →
        ZS.diagMap p b (l05nK42_du (p := p) t) ∈ A) →
      ∀ t : Finset (Fin n), t.card = m → (∏ x ∈ t, (-1 : ZMod p)) = 1 →
        ZS.diagMap p b (l05nK42_du (p := p) t) ∈ A := by
    intro m ih t htm htprod
    by_cases h0 : t.card = 0
    · have ht0 : t = ∅ := Finset.card_eq_zero.mp h0
      have h1 : l05nK42_du (p := p) (∅ : Finset (Fin n)) = 1 := by
        funext i; simp [l05nK42_du]
      rw [ht0, h1, l05nK42_diagMap_one]; exact A.one_mem
    · have hpos : 0 < t.card := Nat.pos_of_ne_zero h0
      obtain ⟨a, ha⟩ := Finset.card_pos.mp hpos
      by_cases hs1 : (t.erase a).Nonempty
      · obtain ⟨b', hb'⟩ := hs1
        let t' : Finset (Fin n) := (t.erase a).erase b'
        have hb_erase : b' ∈ t.erase a := hb'
        have ha' : a ∉ t' := by simp [t']
        have hb'' : b' ∉ t' := by simp [t']
        have hab : a ≠ b' := by
          have : b' ≠ a := (Finset.mem_erase.mp hb_erase).1
          exact Ne.symm this
        have ht_eq : t = insert a (insert b' t') := by
          rw [← Finset.insert_erase ha, ← Finset.insert_erase hb_erase]
        have hcard' : t'.card < t.card := by
          have h1 : t'.card + 1 = (t.erase a).card := Finset.card_erase_add_one hb_erase
          have h2 : (t.erase a).card + 1 = t.card := Finset.card_erase_add_one ha
          omega
        have hprod' : ∏ k ∈ t', (-1 : ZMod p) = 1 := by
          have ha_ins : a ∉ insert b' t' := by simp [Finset.mem_insert, hab, ha']
          have h := htprod
          rw [ht_eq, Finset.prod_insert ha_ins, Finset.prod_insert hb''] at h
          ring_nf at h
          exact h
        have ih' := ih t'.card (by omega) t' rfl hprod'
        rw [ht_eq, l05nK42_E_pair b a b' hab t' ha' hb'']
        exact A.mul_mem (hD a b' hab) ih'
      · have hteq : t = {a} := by
          rw [← Finset.insert_erase ha,
            Finset.card_eq_zero.mp
              (Nat.eq_zero_of_not_pos (fun h => hs1 (Finset.card_pos.mp h)))]
          simp
        rw [hteq, Finset.prod_singleton] at htprod
        exact absurd htprod.symm (l05nK42_one_ne_neg_one hp2)
  have key : ∀ t : Finset (Fin n), t.card = s.card →
      (∏ x ∈ t, (-1 : ZMod p)) = 1 → ZS.diagMap p b (l05nK42_du (p := p) t) ∈ A :=
    Nat.strong_induction_on s.card H
  exact key s rfl hsprod

private lemma l05nK42_monomial_mem_of_D2_Tp
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V) (A : Subgroup (V ≃ₗ[ZMod p] V))
    (hD : ∀ k l, k ≠ l → l05nK42_D2 b k l ∈ A) (hP : ∀ σ, ZS.permMap p b σ ∈ A)
    {a : V ≃ₗ[ZMod p] V} {σ : Equiv.Perm (Fin n)} {c : Fin n → ZMod p}
    (hc : ∀ i, c i = 1 ∨ c i = -1) (hcp : ∏ i, c i = 1)
    (ha : ∀ i, a (b i) = c i • b (σ i)) :
    a ∈ A := by
  classical
  let s : Finset (Fin n) := Finset.univ.filter (fun k => c (σ.symm k) = -1)
  have hmem' : ∀ k, (k ∈ s) ↔ c (σ.symm k) = -1 := by
    intro k; simp only [s, Finset.mem_filter, Finset.mem_univ, true_and]
  have hmem : ∀ i, (σ i ∈ s) ↔ c i = -1 := by
    intro i; rw [hmem' (σ i), Equiv.symm_apply_apply]
  have hsprod : ∏ k ∈ s, (-1 : ZMod p) = 1 := by
    have h1 : ∏ k ∈ s, (-1 : ZMod p) = ∏ k, (l05nK42_du (p := p) s k : ZMod p) := by
      rw [← Finset.prod_subset (Finset.subset_univ s)
        (fun k _ hk => by simp [l05nK42_du, hk])]
      apply Finset.prod_congr rfl
      intro k hk
      simp [l05nK42_du, hk]
    have h2 : ∏ k, (l05nK42_du (p := p) s k : ZMod p) = ∏ k, c (σ.symm k) := by
      apply Finset.prod_congr rfl
      intro k _
      by_cases hk : k ∈ s
      · have hck : c (σ.symm k) = -1 := (hmem' k).mp hk
        rw [hck]; simp [l05nK42_du, hk]
      · have hck : c (σ.symm k) ≠ -1 := fun h => hk ((hmem' k).mpr h)
        rcases hc (σ.symm k) with h | h
        · simp [l05nK42_du, hk, h]
        · exact absurd h hck
    calc ∏ k ∈ s, (-1 : ZMod p) = ∏ k, (l05nK42_du (p := p) s k : ZMod p) := h1
      _ = ∏ k, c (σ.symm k) := h2
      _ = ∏ k, c k := Fintype.prod_equiv σ.symm (fun k => c (σ.symm k)) c (fun k => rfl)
      _ = 1 := hcp
  have hDmem : ZS.diagMap p b (l05nK42_du (p := p) s) ∈ A :=
    l05nK42_diag_mem_of_prod hp2 b A hD s hsprod
  have hDeq : a = ZS.diagMap p b (l05nK42_du (p := p) s) * ZS.permMap p b σ := by
    apply l05nK42_ext_basis (b := b)
    intro i
    rw [ha i, LinearEquiv.mul_apply, l05nK42_permMap_apply, l05nK42_D_apply]
    rcases hc i with hci | hci
    · have hni : σ i ∉ s := by
        rw [hmem i, hci]; exact fun h => l05nK42_one_ne_neg_one hp2 h
      rw [hci, if_neg hni, one_smul]
    · rw [hci, if_pos ((hmem i).mpr hci)]
  rw [hDeq]
  exact A.mul_mem hDmem (hP σ)

private noncomputable def l05nK42_eps
    {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V) (A : Subgroup (V ≃ₗ[ZMod p] V))
    (i j : Fin n) : ZMod p := by
  classical
  exact if l05nK42_Tp b i j ∈ A then 1 else -1

private lemma l05nK42_eps_self
    {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V) (A : Subgroup (V ≃ₗ[ZMod p] V))
    (i : Fin n) : l05nK42_eps b A i i = 1 := by
  rw [l05nK42_eps, if_pos]
  rw [l05nK42_Tp_self]; exact A.one_mem

private lemma l05nK42_eps_mul_self
    {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V) (A : Subgroup (V ≃ₗ[ZMod p] V))
    (i j : Fin n) : l05nK42_eps b A i j * l05nK42_eps b A i j = 1 := by
  classical
  classical
  rw [l05nK42_eps]
  by_cases h : l05nK42_Tp b i j ∈ A <;> simp [h]

private lemma l05nK42_eps_eq_neg_or_one
    {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V) (A : Subgroup (V ≃ₗ[ZMod p] V))
    (i j : Fin n) : l05nK42_eps b A i j = 1 ∨ l05nK42_eps b A i j = -1 := by
  classical
  rw [l05nK42_eps]
  by_cases h : l05nK42_Tp b i j ∈ A <;> simp [h]

private lemma l05nK42_eps_symm
    {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V) (A : Subgroup (V ≃ₗ[ZMod p] V))
    (i j : Fin n) : l05nK42_eps b A i j = l05nK42_eps b A j i := by
  classical
  rw [l05nK42_eps, l05nK42_eps, l05nK42_Tp_comm]

private lemma l05nK42_eps_mul
    {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V) (A : Subgroup (V ≃ₗ[ZMod p] V))
    (hall : ∀ i j, l05nK42_Gamma b A i j)
    (hno : ∀ i j, i ≠ j → ¬ (l05nK42_Tp b i j ∈ A ∧ l05nK42_Tm b i j ∈ A))
    {i j k : Fin n} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    l05nK42_eps b A i k = l05nK42_eps b A i j * l05nK42_eps b A j k := by
  rw [l05nK42_eps, l05nK42_eps, l05nK42_eps]
  by_cases h1 : l05nK42_Tp b i j ∈ A
  · by_cases h2 : l05nK42_Tp b j k ∈ A
    · have h3 : l05nK42_Tp b i k ∈ A := by
        rw [← l05nK42_conj_Tp_Tp b hij hjk hik]
        exact A.mul_mem (A.mul_mem h1 h2) h1
      rw [if_pos h3, if_pos h1, if_pos h2]; ring
    · have h2' : l05nK42_Tm b j k ∈ A := by
        rcases hall j k with h | h
        · exact absurd h h2
        · exact h
      have hpik : l05nK42_Tm b i k ∈ A := by
        rw [← l05nK42_conj_Tp_Tm b hij hjk hik]
        exact A.mul_mem (A.mul_mem h1 h2') h1
      have h3 : l05nK42_Tp b i k ∉ A := fun h => hno i k hik ⟨h, hpik⟩
      rw [if_neg h3, if_pos h1, if_neg h2]; ring
  · have h1' : l05nK42_Tm b i j ∈ A := by
      rcases hall i j with h | h
      · exact absurd h h1
      · exact h
    by_cases h2 : l05nK42_Tp b j k ∈ A
    · have hpik : l05nK42_Tm b i k ∈ A := by
        rw [← l05nK42_conj_Tm_Tp b hij hjk hik]
        exact A.mul_mem (A.mul_mem h1' h2) h1'
      have h3 : l05nK42_Tp b i k ∉ A := fun h => hno i k hik ⟨h, hpik⟩
      rw [if_neg h3, if_neg h1, if_pos h2]; ring
    · have h2' : l05nK42_Tm b j k ∈ A := by
        rcases hall j k with h | h
        · exact absurd h h2
        · exact h
      have h3 : l05nK42_Tp b i k ∈ A := by
        rw [← l05nK42_conj_Tm_Tm b hij hjk hik]
        exact A.mul_mem (A.mul_mem h1' h2') h1'
      rw [if_pos h3, if_neg h1, if_neg h2]; ring

private lemma l05nK42_eps_eq_d
    {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V) (A : Subgroup (V ≃ₗ[ZMod p] V))
    (z : Fin n) (hall : ∀ i j, l05nK42_Gamma b A i j)
    (hno : ∀ i j, i ≠ j → ¬ (l05nK42_Tp b i j ∈ A ∧ l05nK42_Tm b i j ∈ A))
    (i j : Fin n) :
    l05nK42_eps b A i j = l05nK42_eps b A z i * l05nK42_eps b A z j := by
  classical
  by_cases hiz : i = z
  · rw [hiz, l05nK42_eps_self, one_mul]
  · by_cases hjz : j = z
    · rw [hjz, l05nK42_eps_self, mul_one, l05nK42_eps_symm]
    · by_cases hij : i = j
      · rw [hij, l05nK42_eps_self]
        exact (l05nK42_eps_mul_self b A z j).symm
      · have hm : l05nK42_eps b A i z = l05nK42_eps b A i j * l05nK42_eps b A j z :=
          l05nK42_eps_mul b A hall hno hij hjz hiz
        have hmain : l05nK42_eps b A i j = l05nK42_eps b A i z * l05nK42_eps b A j z := by
          rw [hm, mul_assoc, l05nK42_eps_mul_self, mul_one]
        rw [hmain, l05nK42_eps_symm b A i z, l05nK42_eps_symm b A j z]

private lemma l05nK42_d_swap_eq
    {p : ℕ} {n : ℕ} {i j : Fin n} (hij : i ≠ j) {d : Fin n → ZMod p} (hd : d i = d j)
    (l : Fin n) : d (Equiv.swap i j l) = d l := by
  by_cases hli : l = i
  · rw [hli, Equiv.swap_apply_left, hd]
  · by_cases hlj : l = j
    · rw [hlj, Equiv.swap_apply_right, hd]
    · rw [Equiv.swap_apply_of_ne_of_ne hli hlj]

private lemma l05nK42_d_swap_tw
    {p : ℕ} {n : ℕ} {i j : Fin n} (hij : i ≠ j) {d : Fin n → ZMod p}
    (hd : d i = - d j) (l : Fin n) :
    d (Equiv.swap i j l) * l05nK42_tw (p := p) i j l = d l := by
  by_cases hli : l = i
  · rw [hli, Equiv.swap_apply_left,
      show l05nK42_tw (p := p) i j i = -1 by simp [l05nK42_tw]]
    rw [hd]; ring
  · by_cases hlj : l = j
    · rw [hlj, Equiv.swap_apply_right,
        show l05nK42_tw (p := p) i j j = -1 by simp [l05nK42_tw]]
      rw [hd]; ring
    · rw [Equiv.swap_apply_of_ne_of_ne hli hlj,
        show l05nK42_tw (p := p) i j l = 1 by simp [l05nK42_tw, hli, hlj]]
      rw [mul_one]

private lemma l05nK42_Tp_fixes_sum
    {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V) (d : Fin n → ZMod p) {i j : Fin n}
    (hij : i ≠ j) (hd : ∀ l, d (Equiv.swap i j l) = d l) :
    l05nK42_Tp b i j (∑ k, d k • b k) = ∑ k, d k • b k := by
  rw [map_sum]
  simp only [map_smul, l05nK42_Tp_apply]
  rw [Fintype.sum_equiv (Equiv.swap i j) (fun k => d k • b (Equiv.swap i j k))
    (fun l => d (Equiv.swap i j l) • b l) (fun x => by rw [Equiv.swap_apply_self])]
  apply Finset.sum_congr rfl
  intro l _
  rw [hd l]

private lemma l05nK42_Tm_fixes_sum
    {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V) (d : Fin n → ZMod p) {i j : Fin n}
    (hij : i ≠ j) (hd : ∀ l, d (Equiv.swap i j l) * l05nK42_tw (p := p) i j l = d l) :
    l05nK42_Tm b i j (∑ k, d k • b k) = ∑ k, d k • b k := by
  rw [map_sum]
  simp only [map_smul, l05nK42_Tm_apply_tw, smul_smul]
  rw [Fintype.sum_equiv (Equiv.swap i j)
    (fun k => (d k * l05nK42_tw (p := p) i j k) • b (Equiv.swap i j k))
    (fun l => (d (Equiv.swap i j l) * l05nK42_tw (p := p) i j (Equiv.swap i j l)) • b l)
    (fun x => by rw [Equiv.swap_apply_self])]
  apply Finset.sum_congr rfl
  intro l _
  rw [l05nK42_tw_invariant i j l, hd l]

private lemma l05nK42_no_pair_contra
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (hn : 4 ≤ n) (b : Module.Basis (Fin n) (ZMod p) V)
    (A : Subgroup (V ≃ₗ[ZMod p] V)) (hirr : ZS.AbsIrred p A)
    (hgen : A = Subgroup.closure {r | r ∈ A ∧ GGLinRefl r})
    (hmon : ∀ a ∈ A, ∃ (σ : Equiv.Perm (Fin n)) (c : Fin n → ZMod p),
      (∀ i, c i = 1 ∨ c i = -1) ∧ ∀ i, a (b i) = c i • b (σ i))
    (hnoS : ∀ i, l05nK42_S b i ∉ A)
    (hall : ∀ i j, l05nK42_Gamma b A i j)
    (hno : ∀ i j, i ≠ j → ¬ (l05nK42_Tp b i j ∈ A ∧ l05nK42_Tm b i j ∈ A)) :
    False := by
  classical
  let z : Fin n := ⟨0, by omega⟩
  let d : Fin n → ZMod p := fun i => l05nK42_eps b A z i
  have hd_eq : ∀ i j, l05nK42_eps b A i j = d i * d j := fun i j =>
    l05nK42_eps_eq_d b A z hall hno i j
  have hd_sign : ∀ i, d i = 1 ∨ d i = -1 := fun i => l05nK42_eps_eq_neg_or_one b A z i
  have hd_mul_self : ∀ i, d i * d i = 1 := fun i => l05nK42_eps_mul_self b A z i
  have hdz : d z = 1 := by
    change l05nK42_eps b A z z = 1
    exact l05nK42_eps_self b A z
  have hd_swap_eq : ∀ {i j : Fin n}, i ≠ j → l05nK42_Tp b i j ∈ A →
      ∀ l, d (Equiv.swap i j l) = d l := by
    intro i j hij hTp l
    have he : l05nK42_eps b A i j = 1 := by rw [l05nK42_eps, if_pos hTp]
    have hdi : d i = d j := by
      have h1 : d i * d j = 1 := by rw [← hd_eq i j, he]
      calc d i = d i * 1 := (mul_one _).symm
        _ = d i * (d j * d j) := by rw [hd_mul_self j]
        _ = (d i * d j) * d j := by ring
        _ = 1 * d j := by rw [h1]
        _ = d j := one_mul _
    exact l05nK42_d_swap_eq hij hdi l
  have hd_swap_tw : ∀ {i j : Fin n}, i ≠ j → l05nK42_Tm b i j ∈ A →
      ∀ l, d (Equiv.swap i j l) * l05nK42_tw (p := p) i j l = d l := by
    intro i j hij hTm l
    have he : l05nK42_eps b A i j = -1 := by
      rw [l05nK42_eps, if_neg (fun h => hno i j hij ⟨h, hTm⟩)]
    have h1 : d i * d j = -1 := by rw [← hd_eq i j, he]
    have hdi : d i = - d j := by
      calc d i = d i * 1 := (mul_one _).symm
        _ = d i * (d j * d j) := by rw [hd_mul_self j]
        _ = (d i * d j) * d j := by ring
        _ = -1 * d j := by rw [h1]
        _ = - d j := by ring
    exact l05nK42_d_swap_tw hij hdi l
  let v : V := ∑ k, d k • b k
  have hv_coord : b.equivFun v z = 1 := by
    change b.equivFun (∑ k, d k • b k) z = 1
    rw [map_sum, Finset.sum_apply]
    simp only [map_smul, Pi.smul_apply, Module.Basis.equivFun_self, smul_eq_mul,
      Pi.single_apply]
    rw [Finset.sum_eq_single z]
    · simp [hdz]
    · intro k _ hk; simp [hk]
    · intro h; exact absurd (Finset.mem_univ z) h
  have hv_ne_zero : v ≠ 0 := by
    intro h
    have := congrArg (fun w => b.equivFun w z) h
    rw [hv_coord, map_zero, Pi.zero_apply] at this
    exact one_ne_zero this
  let H : Subgroup (V ≃ₗ[ZMod p] V) :=
    { carrier := {a | a v = v}
      one_mem' := by show (1 : V ≃ₗ[ZMod p] V) v = v; simp
      mul_mem' := by
        intro x y hx hy
        show (x * y) v = v
        rw [LinearEquiv.mul_apply, hy, hx]
      inv_mem' := by
        intro x hx
        show x⁻¹ v = v
        apply x.injective
        change x (x.symm v) = x v
        rw [LinearEquiv.apply_symm_apply, hx] }
  have hfix : ∀ a ∈ A, a v = v := by
    have hAle : A ≤ H := by
      rw [hgen, Subgroup.closure_le]
      rintro r ⟨hrA, hrRefl⟩
      obtain ⟨σ, c, hc, hrb⟩ := hmon r hrA
      rcases l05nK42_reflection_eq hp2 b r hrRefl σ c hc hrb with ⟨i, rfl⟩ | ⟨i, j, hij, hT⟩
      · exact absurd hrA (hnoS i)
      · rcases hT with rfl | rfl
        · exact l05nK42_Tp_fixes_sum b d hij (fun l => hd_swap_eq hij hrA l)
        · exact l05nK42_Tm_fixes_sum b d hij (fun l => hd_swap_tw hij hrA l)
    intro a ha
    exact hAle ha
  let W : Submodule (ZMod p) V := Submodule.span (ZMod p) ({v} : Set V)
  have hWinv : ∀ a ∈ A, ∀ w ∈ W, a w ∈ W := by
    intro a ha w hw
    have hav : a v ∈ W := by
      rw [hfix a ha]; exact Submodule.subset_span (Set.mem_singleton v)
    have hmap : W.map (a : V →ₗ[ZMod p] V) ≤ W := by
      rw [Submodule.map_le_iff_le_comap, Submodule.span_le]
      rintro x hx
      rw [Set.mem_singleton_iff] at hx
      subst hx
      exact hav
    exact hmap (Submodule.mem_map_of_mem hw)
  rcases hirr.1 W hWinv with hbot | htop
  · exfalso
    have hmem : v ∈ W := Submodule.subset_span (Set.mem_singleton v)
    rw [hbot] at hmem
    exact hv_ne_zero ((Submodule.mem_bot (ZMod p)).mp hmem)
  · exfalso
    let z' : Fin n := ⟨1, by omega⟩
    have hzz' : z ≠ z' := by
      intro h
      have := congrArg Fin.val h
      simp [z, z'] at this
    have hz_mem : b z ∈ W := by rw [htop]; exact Submodule.mem_top
    have hz'_mem : b z' ∈ W := by rw [htop]; exact Submodule.mem_top
    obtain ⟨c1, hc1⟩ := Submodule.mem_span_singleton.mp hz_mem
    obtain ⟨c2, hc2⟩ := Submodule.mem_span_singleton.mp hz'_mem
    have hc2_ne : c2 ≠ 0 := by
      intro h; rw [h, zero_smul] at hc2; exact b.ne_zero z' hc2.symm
    have heq : c2 • b z = c1 • b z' := by
      rw [← hc1, ← hc2, smul_smul, smul_smul, mul_comm]
    have hcoord := congrArg (fun w => b.equivFun w z) heq
    simp only [map_smul, Pi.smul_apply, smul_eq_mul, Module.Basis.equivFun_self] at hcoord
    simp [hzz', Ne.symm hzz'] at hcoord
    exact hc2_ne hcoord

end SignedClass

theorem ggRC_signed_class {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {V : Type}
    [AddCommGroup V] [Module (ZMod p) V] {n : ℕ} (hn : 4 ≤ n)
    (b : Module.Basis (Fin n) (ZMod p) V)
    (A : Subgroup (V ≃ₗ[ZMod p] V)) (hirr : ZS.AbsIrred p A)
    (hgen : A = Subgroup.closure {r | r ∈ A ∧ GGLinRefl r})
    (hmon : ∀ a ∈ A, ∃ (σ : Equiv.Perm (Fin n)) (c : Fin n → ZMod p),
      (∀ i, c i = 1 ∨ c i = -1) ∧ ∀ i, a (b i) = c i • b (σ i)) :
    (∀ a : V ≃ₗ[ZMod p] V, a ∈ A ↔ ∃ (σ : Equiv.Perm (Fin n)) (c : Fin n → ZMod p),
      (∀ i, c i = 1 ∨ c i = -1) ∧ ∀ i, a (b i) = c i • b (σ i)) ∨
    (∀ a : V ≃ₗ[ZMod p] V, a ∈ A ↔ ∃ (σ : Equiv.Perm (Fin n)) (c : Fin n → ZMod p),
      (∀ i, c i = 1 ∨ c i = -1) ∧ ∏ i, c i = 1 ∧ ∀ i, a (b i) = c i • b (σ i)) := by
  classical
  have hall : ∀ i j, l05nK42_Gamma b A i j :=
    fun i j => l05nK42_Gamma_all hp2 b A hirr hgen hmon i j
  by_cases hsome : ∃ i, l05nK42_S b i ∈ A
  · left
    obtain ⟨i₀, hi₀⟩ := hsome
    have hS : ∀ i, l05nK42_S b i ∈ A :=
      l05nK42_sign_changes_all hp2 b A hirr hgen hmon hi₀
    have hTp : ∀ i j, l05nK42_Tp b i j ∈ A :=
      l05nK42_Tp_all_of_S hp2 b A hirr hgen hmon hS
    have hP : ∀ σ, ZS.permMap p b σ ∈ A := l05nK42_permMap_mem b A hTp
    intro a
    constructor
    · intro ha
      exact hmon a ha
    · rintro ⟨σ, c, hc, ha⟩
      exact l05nK42_monomial_mem_of_S_permMap hp2 b A hS hP hc ha
  · right
    have hnoS : ∀ i, l05nK42_S b i ∉ A := by
      intro i hi
      exact hsome ⟨i, hi⟩
    by_cases hpair : ∃ i j, i ≠ j ∧ l05nK42_Tp b i j ∈ A ∧ l05nK42_Tm b i j ∈ A
    · obtain ⟨hDall, hTpall⟩ := l05nK42_pair_case_II b A hall hpair
      have hP : ∀ σ, ZS.permMap p b σ ∈ A := l05nK42_permMap_mem b A hTpall
      intro a
      constructor
      · intro ha
        obtain ⟨σ, c, hc, haa⟩ := hmon a ha
        exact ⟨σ, c, hc, l05nK42_prod_sign_one hp2 b A hirr hgen hmon hnoS ha hc haa, haa⟩
      · rintro ⟨σ, c, hc, hcp, haa⟩
        exact l05nK42_monomial_mem_of_D2_Tp hp2 b A hDall hP hc hcp haa
    · exfalso
      have hno : ∀ i j, i ≠ j →
          ¬ (l05nK42_Tp b i j ∈ A ∧ l05nK42_Tm b i j ∈ A) := by
        intro i j hij hp
        exact hpair ⟨i, j, hij, hp.1, hp.2⟩
      exact l05nK42_no_pair_contra hp2 hn b A hirr hgen hmon hnoS hall hno

end CFSG.StandardType
