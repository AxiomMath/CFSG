module


import CFSG.Quasithin.Recognition.St84.Gen.Sec6LeafGen
public import CFSG.Quasithin.Recognition.St84.SetupArc

public section

namespace CFSG.Quasithin.St84

open SimpleGraph CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.Fan86 CFSG.Quasithin.F6.GoldAmL3T

open scoped Pointwise commutatorElement

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace Setup

variable (X : Setup Γ G)

theorem Gi_eq_L_sup_K (i : ℤ) : X.Gi i = X.L i ⊔ X.K := by
  have hf : X.Gi i ⊓ X.Gi (i + 1) ⊔ X.L i = X.Gi i := frattini_oTwoPrime X.hyp (X.adj i)
  rw [← hf, ← X.K_sup_edgeSylow i, sup_assoc, sup_eq_right.mpr (X.edgeSylow_le_L i),
    sup_comm]

private theorem exists_mul_K_of_mem (i : ℤ) {g : G} (hg : g ∈ X.Gi i) :
    ∃ j ∈ X.L i, ∃ k ∈ X.K, g = j * k := by
  have hKN : X.K ≤ Subgroup.normalizer (X.L i : Set G) :=
    (X.K_le_Gi i).trans (le_normalizer_oTwoPrime (X.Gi i))
  have hset : ((X.L i ⊔ X.K : Subgroup G) : Set G) = (X.L i : Set G) * (X.K : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left (X.L i) X.K hKN
  have hg' : g ∈ (X.L i : Set G) * (X.K : Set G) := by
    rw [← hset, ← X.Gi_eq_L_sup_K i]
    exact hg
  obtain ⟨j, hjL, k, hkK, hjk⟩ := hg'
  exact ⟨j, hjL, k, hkK, hjk.symm⟩

private theorem exists_mul_K_of_mem_H (i : ℤ) {H : Subgroup G} (hH : H ≤ X.Gi i)
    (hK : X.K ≤ H) {g : G} (hg : g ∈ H) :
    ∃ j ∈ H ⊓ X.L i, ∃ k ∈ X.K, g = j * k := by
  obtain ⟨j, hjL, k, hkK, hgjk⟩ := X.exists_mul_K_of_mem i (hH hg)
  have hkH : k ∈ H := hK hkK
  have hjH : j ∈ H := by
    have hj_eq : j = g * k⁻¹ := by rw [hgjk]; group
    rw [hj_eq]
    exact H.mul_mem hg (H.inv_mem hkH)
  exact ⟨j, ⟨hjH, hjL⟩, k, hkK, hgjk⟩

private theorem exists_mem_J_smul (i : ℤ) {H : Subgroup G} (hH : H ≤ X.Gi i)
    (hK : X.K ≤ H)
    (htr : ∀ a b : V, Γ.Adj (X.vert i) a → Γ.Adj (X.vert i) b → ∃ g ∈ H, g • a = b)
    {a : V} (ha : Γ.Adj (X.vert i) a) :
    ∃ j ∈ H ⊓ X.L i, j • X.vert (i + 1) = a := by
  obtain ⟨g, hgH, hg⟩ := htr (X.vert (i + 1)) a (X.adj i) ha
  obtain ⟨j, hjJ, k, hkK, hgjk⟩ := X.exists_mul_K_of_mem_H i hH hK hgH
  refine ⟨j, hjJ, ?_⟩
  have h1 : j • X.vert (i + 1) = g • X.vert (i + 1) := by
    rw [hgjk, mul_smul, X.K_fix k hkK (i + 1)]
  exact h1.trans hg

private noncomputable def coverSubgroup (i : ℤ) {H : Subgroup G} (hH : H ≤ X.Gi i) :
    Subgroup G where
  carrier := {l : G | l ∈ X.L i ∧ ∃ l' ∈ oTwoPrime H,
    ∀ w : V, Γ.Adj (X.vert i) w → l' • w = l • w}
  one_mem' := ⟨(X.L i).one_mem, 1, (oTwoPrime H).one_mem, by intro w _; simp⟩
  mul_mem' := by
    intro l1 l2 hl1 hl2
    obtain ⟨hl1L, l1', hl1', h1⟩ := hl1
    obtain ⟨hl2L, l2', hl2', h2⟩ := hl2
    refine ⟨(X.L i).mul_mem hl1L hl2L, l1' * l2', (oTwoPrime H).mul_mem hl1' hl2', ?_⟩
    intro w hw
    have hw2 : Γ.Adj (X.vert i) (l2 • w) := by
      have hfix : l2 • X.vert i = X.vert i :=
        MulAction.mem_stabilizer_iff.mp (X.L_le_Gi i hl2L)
      rw [← hfix]
      exact (X.hyp.adj_smul l2 (X.vert i) w).2 hw
    calc (l1' * l2') • w = l1' • (l2' • w) := mul_smul l1' l2' w
      _ = l1' • (l2 • w) := by rw [h2 w hw]
      _ = l1 • (l2 • w) := h1 (l2 • w) hw2
      _ = (l1 * l2) • w := (mul_smul l1 l2 w).symm
  inv_mem' := by
    intro l hl
    obtain ⟨hlL, l', hl', h⟩ := hl
    refine ⟨(X.L i).inv_mem hlL, l'⁻¹, (oTwoPrime H).inv_mem hl', ?_⟩
    intro w hw
    have hl'G : l' ∈ X.Gi i := hH (oTwoPrime_le H hl')
    have hw' : Γ.Adj (X.vert i) (l'⁻¹ • w) := by
      have hfixinv : l'⁻¹ • X.vert i = X.vert i := by
        calc l'⁻¹ • X.vert i = l'⁻¹ • (l' • X.vert i) := by
              rw [MulAction.mem_stabilizer_iff.mp hl'G]
          _ = X.vert i := by simp
      rw [← hfixinv]
      exact (X.hyp.adj_smul l'⁻¹ (X.vert i) w).2 hw
    have h1 : l' • (l'⁻¹ • w) = l • (l'⁻¹ • w) := h (l'⁻¹ • w) hw'
    have hw_eq : w = l • (l'⁻¹ • w) := by
      rw [← h1]
      simp
    have : l⁻¹ • w = l'⁻¹ • w := by
      calc l⁻¹ • w = l⁻¹ • (l • (l'⁻¹ • w)) := by rw [← hw_eq]
        _ = l'⁻¹ • w := by simp
    exact this.symm

private theorem Q_le_coverSubgroup (i : ℤ) {H : Subgroup G} (hH : H ≤ X.Gi i) :
    X.Q i ≤ X.coverSubgroup i hH := by
  intro l hl
  have hlL : l ∈ X.L i :=
    le_oTwoPrime_of_isPGroup (pCoreOf_isPGroup' (X.Gi i)) (X.Q_le_Gi i) hl
  refine ⟨hlL, 1, (oTwoPrime H).one_mem, ?_⟩
  intro w hw
  rw [one_smul]
  exact (X.Q_fixes_neighbors_vert i w hw l hl).symm

private theorem twoElem_mem_coverSubgroup (i : ℤ) {H : Subgroup G} (hH : H ≤ X.Gi i)
    {x : G} (hxH : x ∈ H) (hxL : x ∈ X.L i) (hx2 : ∃ n : ℕ, x ^ 2 ^ n = 1) :
    x ∈ X.coverSubgroup i hH :=
  ⟨hxL, x, Subgroup.subset_closure ⟨hxH, hx2⟩, by intro w _; rfl⟩

private theorem normalizer_coverSubgroup (i : ℤ) {H : Subgroup G} (hH : H ≤ X.Gi i) :
    H ⊓ X.L i ≤ Subgroup.normalizer (X.coverSubgroup i hH : Set G) := by
  have hforward : ∀ j ∈ H ⊓ X.L i, ∀ m ∈ X.coverSubgroup i hH,
      j * m * j⁻¹ ∈ X.coverSubgroup i hH := by
    intro j hj m hm
    obtain ⟨hjH, hjL⟩ := Subgroup.mem_inf.mp hj
    obtain ⟨hmL, m', hm', hm_eq⟩ := hm
    have hjG : j ∈ X.Gi i := hH hjH
    have hjn : X.Gi i ≤ Subgroup.normalizer (X.L i : Set G) :=
      le_normalizer_oTwoPrime (X.Gi i)
    have hLmem : j * m * j⁻¹ ∈ X.L i :=
      (Subgroup.mem_normalizer_iff.mp (hjn hjG) m).mp hmL
    have hHmem : j * m' * j⁻¹ ∈ oTwoPrime H :=
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_oTwoPrime H hjH) m').mp hm'
    refine ⟨hLmem, j * m' * j⁻¹, hHmem, ?_⟩
    intro w hw
    have hwj : Γ.Adj (X.vert i) (j⁻¹ • w) := by
      have hfixinv : j⁻¹ • X.vert i = X.vert i := by
        calc j⁻¹ • X.vert i = j⁻¹ • (j • X.vert i) := by
              rw [MulAction.mem_stabilizer_iff.mp hjG]
          _ = X.vert i := by simp
      rw [← hfixinv]
      exact (X.hyp.adj_smul j⁻¹ (X.vert i) w).2 hw
    calc (j * m' * j⁻¹) • w = j • (m' • (j⁻¹ • w)) := by simp only [mul_smul]
      _ = j • (m • (j⁻¹ • w)) := by rw [hm_eq (j⁻¹ • w) hwj]
      _ = (j * m * j⁻¹) • w := by simp only [mul_smul]
  intro j hj
  rw [Subgroup.mem_set_normalizer_iff]
  intro m
  constructor
  · exact hforward j hj m
  · intro hm
    have hjinv : j⁻¹ ∈ H ⊓ X.L i := (H ⊓ X.L i).inv_mem hj
    have hthis := hforward j⁻¹ hjinv (j * m * j⁻¹) hm
    have h_eq : j⁻¹ * (j * m * j⁻¹) * (j⁻¹)⁻¹ = m := by group
    rwa [h_eq] at hthis

private theorem exists_fixed_neighbor_of_twoElem (i : ℤ) (hn : 2 ≤ X.n i) {x : G}
    (hxG : x ∈ X.Gi i) (hx2 : ∃ n : ℕ, x ^ 2 ^ n = 1) :
    ∃ a : V, Γ.Adj (X.vert i) a ∧ x • a = a := by
  classical
  obtain ⟨n, hxpow⟩ := hx2
  let P : Subgroup G := Subgroup.zpowers x
  have hPG : P ≤ MulAction.stabilizer G (X.vert i) := by
    rw [Subgroup.zpowers_le]
    exact hxG
  let D : SubMulAction P V := neighborActionOf X.hyp P hPG
  haveI : Finite D := (X.hyp.finite_neighborSet (X.vert i)).to_subtype
  have hP2 : IsPGroup 2 P := isPGroup_zpowers_of_pow_two hxpow
  have hcard : Nat.card D = 2 ^ X.n i + 1 := by
    have h1 : Nat.card D = (Γ.neighborSet (X.vert i)).ncard := by
      change Nat.card ↥(D : Set V) = (Γ.neighborSet (X.vert i)).ncard
      rw [Nat.card_coe_set_eq]
      rfl
    rw [h1]
    exact (X.hyp.valency (X.vert i)).2
  have hodd : ¬ 2 ∣ Nat.card D := by
    rw [hcard]
    intro hd
    have hn0 : X.n i ≠ 0 := by
      have hpos : 0 < X.n i := lt_of_lt_of_le (by norm_num : (0 : ℕ) < 2) hn
      exact Nat.pos_iff_ne_zero.mp hpos
    have heven : Even (2 ^ X.n i) := Even.pow_of_ne_zero even_two hn0
    exact (Nat.not_even_iff_odd.mpr heven.add_one) (even_iff_two_dvd.mpr hd)
  obtain ⟨a, ha⟩ := hP2.nonempty_fixed_point_of_prime_not_dvd_card D hodd
  refine ⟨a.1, ?_, ?_⟩
  · have haD : Γ.Adj (X.vert i) (a : V) := by
      have h : (a : V) ∈ (D : Set V) := a.2
      change (a : V) ∈ Γ.neighborSet (X.vert i) at h
      exact h
    exact haD
  · have hfix := (MulAction.mem_fixedPoints.mp ha) (⟨x, Subgroup.mem_zpowers x⟩ : P)
    have hval := congrArg Subtype.val hfix
    rw [SubMulAction.val_smul, MulAction.subgroup_smul_def] at hval
    exact hval

private theorem mem_edgeSylow_of_twoElem (i : ℤ) {y : G} (hyG : y ∈ X.Gi i)
    (hyG1 : y ∈ X.Gi (i + 1)) (hy2 : ∃ n : ℕ, y ^ 2 ^ n = 1) :
    y ∈ X.edgeSylow i := by
  classical
  obtain ⟨n, hn⟩ := hy2
  haveI : Finite ↥(X.Gi i ⊓ X.Gi (i + 1)) :=
    finite_of_le_stabilizer X.hyp (H := X.Gi i ⊓ X.Gi (i + 1)) inf_le_left
  let P : Subgroup G := Subgroup.zpowers y
  have hPedge : P ≤ X.Gi i ⊓ X.Gi (i + 1) := by
    rw [Subgroup.zpowers_le]
    exact ⟨hyG, hyG1⟩
  have hP2 : IsPGroup 2 P := isPGroup_zpowers_of_pow_two hn
  have hSnorm : ((X.edgeSylow i).subgroupOf (X.Gi i ⊓ X.Gi (i + 1))).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi i ⊓ X.Gi (i + 1)))
  exact le_of_normal_isSylowTwoOf (X.isSylowTwoOf_edgeSylow i) hSnorm hPedge hP2
    (Subgroup.mem_zpowers y)

private theorem edgeSylow_le_coverSubgroup_of_not_le (i : ℤ) {H : Subgroup G}
    (hH : H ≤ X.Gi i) (hK : X.K ≤ H)
    (hnot : ¬ H ⊓ X.L i ⊓ X.edgeSylow i ≤ X.Q i) :
    X.edgeSylow i ≤ X.coverSubgroup i hH := by
  let A : Subgroup G := H ⊓ X.L i ⊓ X.edgeSylow i
  have hA : A ≤ X.edgeSylow i := inf_le_right
  have hKiJ : X.K ⊓ X.L i ≤ H ⊓ X.L i :=
    le_inf (inf_le_left.trans hK) inf_le_right
  have hKedge : X.K ≤ X.Gi i ⊓ X.Gi (i + 1) := by
    rw [← X.K_sup_edgeSylow i]
    exact le_sup_left
  have hKN : X.K ≤ Subgroup.normalizer (X.edgeSylow i : Set G) :=
    hKedge.trans
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi i ⊓ X.Gi (i + 1)))
  have hKnorm : X.K ⊓ X.L i ≤ Subgroup.normalizer (A : Set G) :=
    (le_inf (hKiJ.trans Subgroup.le_normalizer) (inf_le_left.trans hKN)).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hsup : A ⊔ X.Q i = X.edgeSylow i := X.sup_Q_eq_edgeSylow_of_left_gen i hKnorm hA hnot
  have hAle : A ≤ X.coverSubgroup i hH := by
    intro x hx
    obtain ⟨hxJ, hxS⟩ := Subgroup.mem_inf.mp hx
    obtain ⟨hxH, hxL⟩ := Subgroup.mem_inf.mp hxJ
    obtain ⟨n, hn⟩ := (X.isPGroup_edgeSylow i).exists_pow_pow_eq_one ⟨x, hxS⟩
    exact X.twoElem_mem_coverSubgroup i hH hxH hxL
      ⟨n, by simpa using congrArg Subtype.val hn⟩
  rw [← hsup]
  exact sup_le hAle (X.Q_le_coverSubgroup i hH)

private theorem L_le_coverSubgroup_of_not_le (i : ℤ) (hn : 2 ≤ X.n i) {H : Subgroup G}
    (hH : H ≤ X.Gi i) (hK : X.K ≤ H)
    (htr : ∀ a b : V, Γ.Adj (X.vert i) a → Γ.Adj (X.vert i) b → ∃ g ∈ H, g • a = b)
    (hnot : ¬ H ⊓ X.L i ⊓ X.edgeSylow i ≤ X.Q i) :
    X.L i ≤ X.coverSubgroup i hH := by
  have hSle : X.edgeSylow i ≤ X.coverSubgroup i hH :=
    X.edgeSylow_le_coverSubgroup_of_not_le i hH hK hnot
  have hJnorm := X.normalizer_coverSubgroup i hH
  have htwo : ∀ x ∈ X.Gi i, (∃ n : ℕ, x ^ 2 ^ n = 1) → x ∈ X.coverSubgroup i hH := by
    intro x hxG hx2
    obtain ⟨a, ha, hxa⟩ := X.exists_fixed_neighbor_of_twoElem i hn hxG hx2
    obtain ⟨j, hjJ, hja⟩ := X.exists_mem_J_smul i hH hK htr ha
    let y : G := j⁻¹ * x * j
    have hyG : y ∈ X.Gi i := by
      dsimp only [y]
      exact (X.Gi i).mul_mem ((X.Gi i).mul_mem ((X.Gi i).inv_mem (X.L_le_Gi i hjJ.2))
        hxG) (X.L_le_Gi i hjJ.2)
    have hyG1 : y ∈ X.Gi (i + 1) := by
      rw [Setup.Gi, MulAction.mem_stabilizer_iff]
      dsimp only [y]
      calc (j⁻¹ * x * j) • X.vert (i + 1)
          = j⁻¹ • (x • (j • X.vert (i + 1))) := by simp only [mul_smul]
        _ = j⁻¹ • (x • a) := by rw [hja]
        _ = j⁻¹ • a := by rw [hxa]
        _ = X.vert (i + 1) := by rw [← hja]; simp
    have hy2 : ∃ n : ℕ, y ^ 2 ^ n = 1 := by
      obtain ⟨n, hn⟩ := hx2
      refine ⟨n, ?_⟩
      dsimp only [y]
      have hconj : j⁻¹ * x * j = j⁻¹ * x * (j⁻¹)⁻¹ := by group
      rw [hconj, conj_pow, hn]
      group
    have hyS : y ∈ X.edgeSylow i := X.mem_edgeSylow_of_twoElem i hyG hyG1 hy2
    have hyM : y ∈ X.coverSubgroup i hH := hSle hyS
    have hx_eq : x = j * y * j⁻¹ := by dsimp only [y]; group
    rw [hx_eq]
    exact (Subgroup.mem_set_normalizer_iff.mp (hJnorm hjJ) y).mp hyM
  rw [Setup.L, oTwoPrime, Subgroup.closure_le]
  rintro x ⟨hxG, n, hx2⟩
  exact htwo x hxG ⟨n, hx2⟩

private theorem inf_J_Gi_succ_le_Gi_pred (i : ℤ) {H : Subgroup G} (hK : X.K ≤ H)
    (hJQ : H ⊓ X.L i ⊓ X.edgeSylow i ≤ X.Q i) :
    H ⊓ X.L i ⊓ X.Gi (i + 1) ≤ X.Gi (i - 1) := by
  intro x hx
  obtain ⟨hxJ, hxG1⟩ := Subgroup.mem_inf.mp hx
  obtain ⟨hxH, hxL⟩ := Subgroup.mem_inf.mp hxJ
  have hxG : x ∈ X.Gi i := X.L_le_Gi i hxL
  have hxKS : x ∈ X.K ⊔ X.edgeSylow i := by
    rw [X.K_sup_edgeSylow i]
    exact ⟨hxG, hxG1⟩
  have hKN : X.K ≤ Subgroup.normalizer (X.edgeSylow i : Set G) := by
    have hKedge : X.K ≤ X.Gi i ⊓ X.Gi (i + 1) := by
      rw [← X.K_sup_edgeSylow i]
      exact le_sup_left
    exact hKedge.trans
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi i ⊓ X.Gi (i + 1)))
  have hset : ((X.K ⊔ X.edgeSylow i : Subgroup G) : Set G) =
      (X.K : Set G) * (X.edgeSylow i : Set G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right X.K (X.edgeSylow i) hKN
  have hxprod : x ∈ (X.K : Set G) * (X.edgeSylow i : Set G) := by
    rw [← hset]
    exact hxKS
  obtain ⟨k, hkK, s, hsS, hks⟩ := hxprod
  have hkH : k ∈ H := hK hkK
  have hsL : s ∈ X.L i := X.edgeSylow_le_L i hsS
  have hkL : k ∈ X.L i := by
    have hk_eq : k = x * s⁻¹ := by rw [← hks]; group
    rw [hk_eq]
    exact (X.L i).mul_mem hxL ((X.L i).inv_mem hsL)
  have hsH : s ∈ H := by
    have hs_eq : s = k⁻¹ * x := by rw [← hks]; group
    rw [hs_eq]
    exact H.mul_mem (H.inv_mem hkH) hxH
  have hsJQ : s ∈ X.Q i :=
    hJQ ⟨⟨hsH, hsL⟩, hsS⟩
  have hsfix : s • X.vert (i - 1) = X.vert (i - 1) := by
    have hadj : Γ.Adj (X.vert i) (X.vert (i - 1)) := by
      have h := (X.adj (i - 1)).symm
      rwa [show i - 1 + 1 = i by omega] at h
    exact X.Q_fixes_neighbors_vert i (X.vert (i - 1)) hadj s hsJQ
  rw [Setup.Gi, MulAction.mem_stabilizer_iff]
  rw [← hks, mul_smul, hsfix, X.K_fix k hkK (i - 1)]

private theorem smul_pred_of_smul_succ (i : ℤ) (hn : 2 ≤ X.n i) {H : Subgroup G}
    (hK : X.K ≤ H) (hJQ : H ⊓ X.L i ⊓ X.edgeSylow i ≤ X.Q i)
    {h : G} (hhJ : h ∈ H ⊓ X.L i) (hh : h • X.vert (i + 1) = X.vert (i - 1)) :
    h • X.vert (i - 1) = X.vert (i + 1) := by
  have hhH : h ∈ H := (Subgroup.mem_inf.mp hhJ).1
  have hhL : h ∈ X.L i := (Subgroup.mem_inf.mp hhJ).2
  have hhG : h ∈ X.Gi i := X.L_le_Gi i hhL
  have hadj_pred : Γ.Adj (X.vert i) (X.vert (i - 1)) := by
    have h := (X.adj (i - 1)).symm
    rwa [show i - 1 + 1 = i by omega] at h
  have hfix : ∀ x ∈ H ⊓ X.L i ⊓ X.Gi (i + 1), x • (h • X.vert (i - 1)) =
      h • X.vert (i - 1) := by
    intro x hx
    obtain ⟨hxJ, hxG1⟩ := Subgroup.mem_inf.mp hx
    obtain ⟨hxH, hxL⟩ := Subgroup.mem_inf.mp hxJ
    have hxfixTminus : x • X.vert (i - 1) = X.vert (i - 1) :=
      MulAction.mem_stabilizer_iff.mp (X.inf_J_Gi_succ_le_Gi_pred i hK hJQ ⟨hxJ, hxG1⟩)
    have hconjJ : h⁻¹ * x * h ∈ H ⊓ X.L i := by
      refine ⟨H.mul_mem (H.mul_mem (H.inv_mem hhH) hxH) hhH, ?_⟩
      exact (Subgroup.mem_normalizer_iff''.mp
        ((le_normalizer_oTwoPrime (X.Gi i)) hhG) x).mp hxL
    have hconjG1 : h⁻¹ * x * h ∈ X.Gi (i + 1) := by
      rw [Setup.Gi, MulAction.mem_stabilizer_iff]
      calc (h⁻¹ * x * h) • X.vert (i + 1)
          = h⁻¹ • (x • (h • X.vert (i + 1))) := by simp only [mul_smul]
        _ = h⁻¹ • (x • X.vert (i - 1)) := by rw [hh]
        _ = h⁻¹ • X.vert (i - 1) := by rw [hxfixTminus]
        _ = X.vert (i + 1) := by rw [← hh]; simp
    have hconjfix : (h⁻¹ * x * h) • X.vert (i - 1) = X.vert (i - 1) :=
      MulAction.mem_stabilizer_iff.mp
        (X.inf_J_Gi_succ_le_Gi_pred i hK hJQ ⟨hconjJ, hconjG1⟩)
    have h1 : h • ((h⁻¹ * x * h) • X.vert (i - 1)) = h • X.vert (i - 1) :=
      congrArg (fun z => h • z) hconjfix
    have h2 : h • ((h⁻¹ * x * h) • X.vert (i - 1)) = x • (h • X.vert (i - 1)) := by
      rw [← mul_smul, show h * (h⁻¹ * x * h) = x * h by group, mul_smul]
    rwa [h2] at h1
  obtain ⟨k, hkKi, hk1⟩ : ∃ k ∈ X.Ki i, k ≠ 1 := by
    obtain ⟨a, ha⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp (X.torus_ne_bot i hn)
    exact ⟨a.1, a.2, fun h => ha (Subtype.ext h)⟩
  have hkK : k ∈ X.K := hkKi.1
  have hkL : k ∈ X.L i := hkKi.2
  have hkH : k ∈ H := hK hkK
  have hkG1 : k ∈ X.Gi (i + 1) := X.K_le_Gi (i + 1) hkK
  have hkfix : k • (h • X.vert (i - 1)) = h • X.vert (i - 1) :=
    hfix k ⟨⟨hkH, hkL⟩, hkG1⟩
  have hadj_h : Γ.Adj (X.vert i) (h • X.vert (i - 1)) := by
    have hfixi : h • X.vert i = X.vert i := MulAction.mem_stabilizer_iff.mp hhG
    rw [← hfixi]
    exact (X.hyp.adj_smul h (X.vert i) (X.vert (i - 1))).2 hadj_pred
  rcases (X.torus_fixed i hn hkKi hk1 (h • X.vert (i - 1)) hadj_h).mp hkfix with
    hTminus | hTplus
  · exfalso
    have hne : X.vert (i - 1) ≠ X.vert (i + 1) := by
      intro heq
      have := X.vert_injective heq
      omega
    apply hne
    have heq : h • X.vert (i - 1) = h • X.vert (i + 1) := by rw [hTminus, hh]
    exact MulAction.injective h heq
  · exact hTplus

private theorem case_two_contradiction (i : ℤ) (hn : 2 ≤ X.n i) {H : Subgroup G}
    (hH : H ≤ X.Gi i) (hK : X.K ≤ H)
    (htr : ∀ a b : V, Γ.Adj (X.vert i) a → Γ.Adj (X.vert i) b → ∃ g ∈ H, g • a = b)
    (hJQ : H ⊓ X.L i ⊓ X.edgeSylow i ≤ X.Q i) : False := by
  classical
  let Δ := ↥(Γ.neighborSet (X.vert i))
  have hfin : Finite Δ := (X.hyp.finite_neighborSet (X.vert i)).to_subtype
  letI : Fintype Δ := Fintype.ofFinite Δ
  have hex (a : Δ) : ∃ j ∈ H ⊓ X.L i, j • X.vert (i + 1) = (a : V) :=
    X.exists_mem_J_smul i hH hK htr (by
      have := a.2
      rwa [SimpleGraph.mem_neighborSet] at this)
  let j : Δ → G := fun a => Classical.choose (hex a)
  have hjJ : ∀ a : Δ, j a ∈ H ⊓ X.L i := fun a => (Classical.choose_spec (hex a)).1
  have hjT : ∀ a : Δ, j a • X.vert (i + 1) = (a : V) :=
    fun a => (Classical.choose_spec (hex a)).2
  have hadj_pred : Γ.Adj (X.vert i) (X.vert (i - 1)) := by
    have h := (X.adj (i - 1)).symm
    rwa [show i - 1 + 1 = i by omega] at h
  have hne : X.vert (i - 1) ≠ X.vert (i + 1) := by
    intro heq
    have := X.vert_injective heq
    omega
  let σfun : Δ → Δ := fun a =>
    ⟨j a • X.vert (i - 1), by
      rw [SimpleGraph.mem_neighborSet]
      have hjG : j a ∈ X.Gi i := X.L_le_Gi i (Subgroup.mem_inf.mp (hjJ a)).2
      have hfix : j a • X.vert i = X.vert i := MulAction.mem_stabilizer_iff.mp hjG
      rw [← hfix]
      exact (X.hyp.adj_smul (j a) (X.vert i) (X.vert (i - 1))).2 hadj_pred⟩
  have hσne : ∀ a : Δ, σfun a ≠ a := by
    intro a h
    apply hne
    have h1 : j a • X.vert (i - 1) = (a : V) := congrArg Subtype.val h
    have h2 : j a • X.vert (i - 1) = j a • X.vert (i + 1) := by rw [h1, hjT a]
    exact MulAction.injective (j a) h2
  have hσinvol : Function.Involutive σfun := by
    intro a
    apply Subtype.ext
    have hhJ : (j a)⁻¹ * j (σfun a) ∈ H ⊓ X.L i :=
      (H ⊓ X.L i).mul_mem ((H ⊓ X.L i).inv_mem (hjJ a)) (hjJ (σfun a))
    have hh : ((j a)⁻¹ * j (σfun a)) • X.vert (i + 1) = X.vert (i - 1) := by
      calc ((j a)⁻¹ * j (σfun a)) • X.vert (i + 1)
          = (j a)⁻¹ • (j (σfun a) • X.vert (i + 1)) := by simp only [mul_smul]
        _ = (j a)⁻¹ • (σfun a : V) := by rw [hjT (σfun a)]
        _ = (j a)⁻¹ • (j a • X.vert (i - 1)) := rfl
        _ = X.vert (i - 1) := by simp
    have hhpred : ((j a)⁻¹ * j (σfun a)) • X.vert (i - 1) = X.vert (i + 1) :=
      X.smul_pred_of_smul_succ i hn hK hJQ hhJ hh
    calc (σfun (σfun a) : V) = j (σfun a) • X.vert (i - 1) := rfl
      _ = j a • (((j a)⁻¹ * j (σfun a)) • X.vert (i - 1)) := by
          rw [← mul_smul]
          rw [show j a * ((j a)⁻¹ * j (σfun a)) = j (σfun a) by group]
      _ = j a • X.vert (i + 1) := by rw [hhpred]
      _ = (a : V) := hjT a
  let σ : Equiv.Perm Δ := hσinvol.toPerm σfun
  have hσ2 : σ ^ 2 = 1 := by
    ext a
    change (σfun (σfun a) : V) = (a : V)
    exact congrArg Subtype.val (hσinvol a)
  have hsupp : σ.support = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro a
    rw [Equiv.Perm.mem_support]
    exact hσne a
  have hdvd : 2 ∣ Nat.card Δ := by
    have h := Equiv.Perm.two_dvd_card_support hσ2
    rwa [hsupp, Finset.card_univ, ← Nat.card_eq_fintype_card] at h
  have hodd : ¬ 2 ∣ Nat.card Δ := by
    have hcard : Nat.card Δ = 2 ^ X.n i + 1 := by
      simpa [Δ] using (X.hyp.valency (X.vert i)).2
    rw [hcard]
    intro hd
    obtain ⟨c, hc⟩ := hd
    have h2 : 2 ∣ 2 ^ X.n i := dvd_pow_self 2 (by omega : X.n i ≠ 0)
    obtain ⟨d, hd'⟩ := h2
    omega
  exact hodd hdvd

theorem covers_of_two_le (i : ℤ) (hn : 2 ≤ X.n i) {H : Subgroup G} (hH : H ≤ X.Gi i)
    (hK : X.K ≤ H)
    (htr : ∀ a b : V, Γ.Adj (X.vert i) a → Γ.Adj (X.vert i) b → ∃ g ∈ H, g • a = b) :
    ∀ l ∈ X.L i, ∃ l' ∈ oTwoPrime H, ∀ w : V, Γ.Adj (X.vert i) w → l' • w = l • w := by
  by_cases hJQ : H ⊓ X.L i ⊓ X.edgeSylow i ≤ X.Q i
  · exact absurd hJQ (X.case_two_contradiction i hn hH hK htr)
  · intro l hl
    have hlM := X.L_le_coverSubgroup_of_not_le i hn hH hK htr hJQ hl
    exact hlM.2

end Setup

end CFSG.Quasithin.St84
