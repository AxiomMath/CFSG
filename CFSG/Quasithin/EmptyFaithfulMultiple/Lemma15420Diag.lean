module

public import CFSG.Quasithin.EmptyFaithfulMultiple.Lemma15420Config
public import CFSG.Quasithin.EmptyFaithfulMultiple.Lemma15420Offender

public section

namespace CFSG.Quasithin.EmptyFaithfulMultiple

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

namespace L15420

variable {G : Type*} [Group G]

theorem thompsonJ_le_baum (T : Subgroup G) : thompsonJ T ≤ baum T := fun x hx =>
  ⟨thompsonJ_le T hx, Subgroup.mem_centralizer_iff.mpr fun _ he =>
    (Subgroup.mem_centralizer_iff.mp (eOf_le_centerOf T he).2 x hx).symm⟩

theorem mem_of_pow_mem_of_pow_mem {H : Subgroup G} {x : G} {a b : ℕ} (hab : Nat.Coprime a b)
    (ha : x ^ a ∈ H) (hb : x ^ b ∈ H) : x ∈ H := by
  have h := Nat.gcd_eq_gcd_ab a b
  rw [hab.gcd_eq_one, Nat.cast_one] at h
  have e : x = (x ^ a) ^ (Nat.gcdA a b) * (x ^ b) ^ (Nat.gcdB a b) := by
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_add, ← h, zpow_one]
  rw [e]
  exact H.mul_mem (H.zpow_mem ha _) (H.zpow_mem hb _)

variable [Finite G]

theorem exists_odd_pow_not_mem {N : Subgroup G} {x : G} (hxN : x ∉ N) (h3 : x ^ 3 ∈ N) :
    ∃ k : ℕ, Odd (orderOf (x ^ k)) ∧ x ^ k ∉ N := by
  have hn : orderOf x ≠ 0 := (orderOf_pos x).ne'
  obtain ⟨k, m, hm, hkm⟩ := Nat.exists_eq_two_pow_mul_odd hn
  refine ⟨2 ^ k, ?_, fun h => hxN ?_⟩
  · rw [orderOf_pow' x (pow_ne_zero k two_ne_zero), hkm,
      Nat.gcd_eq_right (Dvd.intro m rfl), Nat.mul_div_cancel_left m (by positivity)]
    exact hm
  · exact mem_of_pow_mem_of_pow_mem (Nat.Coprime.pow_left k (by norm_num)) h h3

omit [Finite G] in
theorem le_sup_zpowers_of_relIndex_three {X₁ : Subgroup G} (hi : (pCoreOf 2 X₁).relIndex X₁ = 3)
    {x : G} (hx : x ∈ X₁) (hxQ : x ∉ pCoreOf 2 X₁) :
    X₁ ≤ pCoreOf 2 X₁ ⊔ Subgroup.zpowers x := by
  set Q := pCoreOf 2 X₁
  have hQB : Q ≤ Q ⊔ Subgroup.zpowers x := le_sup_left
  have hBA : Q ⊔ Subgroup.zpowers x ≤ X₁ :=
    sup_le (CFSG.LieType.BorelTits.pCoreOf_le 2 X₁) (Subgroup.zpowers_le.mpr hx)
  have hm := Subgroup.relIndex_mul_relIndex Q (Q ⊔ Subgroup.zpowers x) X₁ hQB hBA
  rw [hi] at hm
  have hdvd : Q.relIndex (Q ⊔ Subgroup.zpowers x) ∣ 3 := Dvd.intro _ hm
  rcases Nat.Prime.eq_one_or_self_of_dvd Nat.prime_three _ hdvd with h1 | h3
  · exfalso
    have : Q ⊔ Subgroup.zpowers x ≤ Q := Subgroup.relIndex_eq_one.mp h1
    exact hxQ (this (Subgroup.mem_sup_right (Subgroup.mem_zpowers x)))
  · rw [h3] at hm
    have h1 : (Q ⊔ Subgroup.zpowers x).relIndex X₁ = 1 := by omega
    exact Subgroup.relIndex_eq_one.mp h1

end L15420

variable {G : Type} [Group G] [Finite G] {T : Subgroup G}

namespace Setting15419

variable (s : Setting15419 G T)

theorem VZ_le_centerOf (hyp : MultipleCentralizerHypothesis G T) :
    VZ T s.M₁ ≤ centerOf (pCoreOf 2 s.M₁) := by
  obtain ⟨S, hS⟩ := exists_sylow_of_quasithinIsSylowTwo hyp.sylow
  have hSM : (S : Subgroup G) ≤ s.M₁ := hS ▸ s.inM₁.2
  have hF : s.M₁ ⊓ Subgroup.centralizer (pCoreOf 2 s.M₁ : Set G) ≤ pCoreOf 2 s.M₁ :=
    hyp.qtke.2.1 s.M₁ s.inM₁.1.1 ⟨S, hSM⟩
  exact (conjClosure_le_centerOf_pCoreOf s.M₁ S hSM hF (Z := quasithinOmegaOneCenter T)
    (by rw [hS])).1

theorem VZ_le_T (hyp : MultipleCentralizerHypothesis G T) : VZ T s.M₁ ≤ T := by
  have hsyl : IsSylowTwoOf T s.M₁ := isSylowTwoOf_of_quasithinIsSylowTwo hyp.sylow s.inM₁.2
  exact ((s.VZ_le_centerOf hyp).trans inf_le_left).trans
    (L15420.pCoreOf_le_of_isSylowTwoOf hsyl)

theorem isElemAbelian_VZ (hyp : MultipleCentralizerHypothesis G T) :
    IsElemAbelian 2 (VZ T s.M₁) :=
  isElemAbelian_VZ_of_inM hyp s.inM₁

theorem pCoreOf_X_le (h12 : Stmt15412 G T) : pCoreOf 2 s.X ≤ pCoreOf 2 s.M₁ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hM : s.M₁ ≤ Subgroup.normalizer (s.X : Set G) := Config15420.M₁_le_normalizer_X h12 s
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
    ((CFSG.LieType.BorelTits.pCoreOf_le 2 s.X).trans s.le_X)
    (hM.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 s.X))
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 s.X)

theorem pCoreOf_X_le_centralizer (hyp : MultipleCentralizerHypothesis G T)
    (h12 : Stmt15412 G T) :
    pCoreOf 2 s.X ≤ Subgroup.centralizer (VZ T s.M₁ : Set G) := by
  intro n hn
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  exact ((s.VZ_le_centerOf hyp hv).2 n (s.pCoreOf_X_le h12 hn)).symm

theorem pCoreOf_le_pCoreOf_X {W : Subgroup G} (hWX : W ≤ s.X)
    (hN : s.X ≤ Subgroup.normalizer (W : Set G)) : pCoreOf 2 W ≤ pCoreOf 2 s.X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
    ((CFSG.LieType.BorelTits.pCoreOf_le 2 W).trans hWX)
    (hN.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 W))
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 W)

omit [Finite G] in
theorem X₁_le_X : s.X₁ ≤ s.X := by
  obtain ⟨hX, -⟩ := s.dataX
  rw [hX]; exact le_sup_left

omit [Finite G] in
theorem X₂_le_X : s.X₂ ≤ s.X := by
  obtain ⟨hX, -⟩ := s.dataX
  rw [hX]; exact le_sup_right

omit [Finite G] in
theorem X_le_normalizer_X₁ : s.X ≤ Subgroup.normalizer (s.X₁ : Set G) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h, -⟩ := s.dataX
  exact h

omit [Finite G] in
theorem X_le_normalizer_X₂ : s.X ≤ Subgroup.normalizer (s.X₂ : Set G) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h⟩ := s.dataX
  exact h

theorem card_commutator_X (hyp : MultipleCentralizerHypothesis G T) :
    Nat.card (⁅VZ T s.M₁, s.X⁆ : Subgroup G) = 16 := by
  obtain ⟨-, -, -, -, -, hVX, hinf, hc₁, hc₂, -⟩ := s.dataX
  have hV := s.isElemAbelian_VZ hyp
  have := hV.1
  have hle₁ : ⁅VZ T s.M₁, s.X₁⁆ ≤ VZ T s.M₁ :=
    commutator_le_of_le_normalizer ((s.X₁_le_X.trans s.le_X).trans
      (le_normalizer_conjClosure _ _))
  have hle₂ : ⁅VZ T s.M₁, s.X₂⁆ ≤ VZ T s.M₁ :=
    commutator_le_of_le_normalizer ((s.X₂_le_X.trans s.le_X).trans
      (le_normalizer_conjClosure _ _))
  obtain ⟨h, -⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute ⁅VZ T s.M₁, s.X₁⁆
    ⁅VZ T s.M₁, s.X₂⁆ (fun x hx y hy => setLike_mul_comm (s := VZ T s.M₁) (hle₁ hx) (hle₂ hy))
  rw [hinf, Subgroup.card_bot, mul_one, hc₁, hc₂, ← hVX] at h
  exact h

theorem relIndex_X_and_pow (hyp : MultipleCentralizerHypothesis G T) (h12 : Stmt15412 G T) :
    (pCoreOf 2 s.X).relIndex s.X = 9 ∧ ∀ x ∈ s.X, x ^ 3 ∈ pCoreOf 2 s.X := by
  obtain ⟨-, -, -, ⟨k, hk, hi, hpow, hc⟩, -⟩ := (h12 s.M₁ s.inM₁).2 s.X s.famX s.le_X
  rw [s.card_commutator_X hyp] at hc
  rcases hk with rfl | rfl
  · norm_num at hc
  · exact ⟨by rw [hi]; norm_num, hpow⟩

omit [Finite G] in
theorem X_eq_oTwoUpper : s.X = oTwoUpper s.X := by
  obtain ⟨hX, hO₁, hO₂, -⟩ := s.dataX
  refine le_antisymm ?_ (oTwoUpper_le _)
  have h1 : s.X₁ ≤ oTwoUpper s.X :=
    calc s.X₁ = oTwoUpper s.X₁ := hO₁
      _ ≤ oTwoUpper s.X := oTwoUpper_mono s.X₁_le_X
  have h2 : s.X₂ ≤ oTwoUpper s.X :=
    calc s.X₂ = oTwoUpper s.X₂ := hO₂
      _ ≤ oTwoUpper s.X := oTwoUpper_mono s.X₂_le_X
  calc s.X = s.X₁ ⊔ s.X₂ := hX
    _ ≤ oTwoUpper s.X := sup_le h1 h2

theorem exists_diag (hyp : MultipleCentralizerHypothesis G T) :
    ∃ a ∈ thompsonJ T, a * a = 1 ∧
      a ∈ Subgroup.centralizer ((⁅VZ T s.M₁, s.X₂⁆ : Subgroup G) : Set G) ∧
      a ∉ Subgroup.centralizer ((⁅VZ T s.M₁, s.X₁⁆ : Subgroup G) : Set G) := by
  obtain ⟨-, hO₁, -, -, -, -, hinf, hc₁, hc₂, hJ₁, -, hS₁, hS₂, -⟩ := s.dataX
  set V := VZ T s.M₁ with hVdef
  set V₁ := (⁅V, s.X₁⁆ : Subgroup G)
  set V₂ := (⁅V, s.X₂⁆ : Subgroup G)
  have hV := s.isElemAbelian_VZ hyp
  have hVN : s.M₁ ≤ Subgroup.normalizer (V : Set G) := le_normalizer_conjClosure _ _
  have hX₁V : s.X₁ ≤ Subgroup.normalizer (V : Set G) := (s.X₁_le_X.trans s.le_X).trans hVN
  have hX₂V : s.X₂ ≤ Subgroup.normalizer (V : Set G) := (s.X₂_le_X.trans s.le_X).trans hVN
  have hV₁V : V₁ ≤ V := commutator_le_of_le_normalizer hX₁V
  have hV₂V : V₂ ≤ V := commutator_le_of_le_normalizer hX₂V
  have hJT : thompsonJ T ≤ T := L15420.thompsonJ_le T
  have hJN : ∀ i : Subgroup G, baum T ≤ Subgroup.normalizer (i : Set G) →
      thompsonJ T ≤ Subgroup.normalizer ((⁅V, i⁆ : Subgroup G) : Set G) := fun i hi x hx =>
    A4.mem_normalizer_commutator (hVN (s.inM₁.2 (hJT hx))) (hi (L15420.thompsonJ_le_baum T hx))
  have hJC : ¬ thompsonJ T ≤ Subgroup.centralizer (V₁ : Set G) := by
    intro hJ
    have hcomm : ⁅s.X₁, thompsonJ T⁆ ≤ Subgroup.centralizer (V₁ : Set G) := by
      rw [Subgroup.commutator_le]
      intro x hx j hj
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      have hxN : x ∈ Subgroup.normalizer (V₁ : Set G) :=
        A4.mem_normalizer_commutator (hX₁V hx) (Subgroup.le_normalizer hx)
      have hjv : ∀ w ∈ V₁, j * w = w * j := fun w hw =>
        (Subgroup.mem_centralizer_iff.mp (hJ hj) w hw).symm
      have h1 : x⁻¹ * v * x ∈ V₁ := by
        have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hxN) v).mp hv
        simpa using this
      have h2 : j⁻¹ * v = v * j⁻¹ := by
        have := hjv v hv
        calc j⁻¹ * v = j⁻¹ * (v * j) * j⁻¹ := by group
          _ = j⁻¹ * (j * v) * j⁻¹ := by rw [this]
          _ = v * j⁻¹ := by group
      have h3 := hjv _ h1
      rw [commutatorElement_def]
      calc v * (x * j * x⁻¹ * j⁻¹) = x * (x⁻¹ * v * x) * j * x⁻¹ * j⁻¹ := by group
        _ = x * (j * (x⁻¹ * v * x)) * x⁻¹ * j⁻¹ := by rw [h3]; group
        _ = x * j * x⁻¹ * (v * j⁻¹) := by group
        _ = x * j * x⁻¹ * (j⁻¹ * v) := by rw [h2]
        _ = x * j * x⁻¹ * j⁻¹ * v := by group
    rw [hJ₁] at hcomm
    have hbot := commutator_inf_centralizer_eq_bot_of_card_eq_four hV hX₁V hO₁ hc₁
    have : V₁ ⊓ Subgroup.centralizer (s.X₁ : Set G) = V₁ := by
      refine inf_eq_left.mpr fun v hv => ?_
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      exact (Subgroup.mem_centralizer_iff.mp (hcomm hx) v hv).symm
    rw [this] at hbot
    rw [hbot, Subgroup.card_bot] at hc₁
    omega
  obtain ⟨A, hA, hAC⟩ : ∃ A : Subgroup G, IsMaxElemAbelian T A ∧
      ¬ A ≤ Subgroup.centralizer (V₁ : Set G) := by
    by_contra h
    push Not at h
    exact hJC (iSup₂_le fun A hA => h A hA)
  have hAJ : A ≤ thompsonJ T := le_iSup₂_of_le A hA le_rfl
  obtain ⟨a, haA, haC₂, haC₁⟩ := L15420.exists_mem_centralizer_not_mem hA hV (s.VZ_le_T hyp)
    hV₁V hV₂V hc₁ hc₂ hinf (hAJ.trans (hJN s.X₁ hS₁)) (hAJ.trans (hJN s.X₂ hS₂)) hAC
  have ha2 : a * a = 1 := by rw [← sq]; exact hA.2.1.2 a haA
  exact ⟨a, hAJ haA, ha2, haC₂, haC₁⟩

end Setting15419

namespace Config15420

variable {s : Setting15419 G T} {I₀ : Subgroup G}

theorem exists_swap' (hyp : MultipleCentralizerHypothesis G T) (h12 : Stmt15412 G T)
    (c : Config15420 s I₀) :
    ∃ u ∈ T ⊓ I₀, s.X₁.map (MulAut.conj u).toMonoidHom = s.X₂ ∧
      s.X₂.map (MulAut.conj u).toMonoidHom = s.X₁ := by
  obtain ⟨u, hu, hne⟩ := c.exists_swap
  refine ⟨u, hu, ?_⟩
  rcases s.permutesX hyp h12 (s.inM₁.2 hu.1) with ⟨h1, h2⟩ | h
  · exfalso
    rcases s.choice₁ with e | e <;> rw [e] at hne
    · exact hne h1
    · exact hne h2
  · exact h

end Config15420

end CFSG.Quasithin.EmptyFaithfulMultiple
