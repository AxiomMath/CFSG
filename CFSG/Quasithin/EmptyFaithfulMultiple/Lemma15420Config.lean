module

public import CFSG.Quasithin.EmptyFaithfulMultiple.Lemma15420Reduce
public import CFSG.Quasithin.Background.OrderingMax

public section

namespace CFSG.Quasithin.EmptyFaithfulMultiple

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

namespace L15420

variable {G : Type*} [Group G]

theorem thompsonJ_le (T : Subgroup G) : thompsonJ T ≤ T :=
  iSup₂_le fun _ hA => hA.1

theorem eOf_le_centerOf (T : Subgroup G) : eOf T ≤ centerOf (thompsonJ T) :=
  (Subgroup.closure_le _).mpr fun _ hx => hx.1

theorem eOf_le_baum (T : Subgroup G) : eOf T ≤ baum T := fun _ he =>
  ⟨thompsonJ_le T (eOf_le_centerOf T he).1, Subgroup.mem_centralizer_iff.mpr fun _ hf =>
    (Subgroup.mem_centralizer_iff.mp (eOf_le_centerOf T he).2 _ (eOf_le_centerOf T hf).1)⟩

theorem omegaOneCenter_le_eOf [Finite G] (T : Subgroup G) :
    quasithinOmegaOneCenter T ≤ eOf T := by
  rw [eOf, ← (omegaOne_centralizer_thompsonJ T).1]
  refine Subgroup.closure_mono ?_
  rintro z ⟨⟨hzT, hzC⟩, hz2⟩
  exact ⟨⟨hzT, Subgroup.centralizer_le (thompsonJ_le T) hzC⟩, hz2⟩

theorem omegaOneCenter_le_center (T : Subgroup G) :
    quasithinOmegaOneCenter T ≤ T ⊓ Subgroup.centralizer (T : Set G) :=
  (Subgroup.closure_le _).mpr fun _ hx => hx.1

end L15420

variable {G : Type} [Group G] [Finite G] {T : Subgroup G}

structure Config15420 (s : Setting15419 G T) (I₀ : Subgroup G) : Prop where
  inH : InH s.I I₀
  sylow : IsSylowTwoOf (T ⊓ I₀) I₀
  lt : s.T₀ < T ⊓ I₀
  sylow_of_le : ∀ J : Subgroup G, InH s.I J → T ⊓ I₀ ≤ J → IsSylowTwoOf (T ⊓ I₀) J
  not_le : ¬ T ⊓ I₀ ≤ Subgroup.normalizer (s.L₁ : Set G)

theorem exists_config15420 (hyp : MultipleCentralizerHypothesis G T) (h12 : Stmt15412 G T)
    (h16 : Stmt15416 G T) (s : Setting15419 G T) {I₀ : Subgroup G} (hI₀ : InH s.I I₀)
    (hns : ¬ IsSylowTwoOf s.T₀ I₀) :
    ∃ (s' : Setting15419 G T) (J : Subgroup G), Config15420 s' J := by
  obtain ⟨s', J, hs', hJ, hsyl, hlt, hle⟩ := exists_config hyp h12 h16 s hI₀ hns
  by_cases h₁ : T ⊓ J ≤ Subgroup.normalizer (s'.L₁ : Set G)
  · have h₂ : ¬ T ⊓ J ≤ Subgroup.normalizer (s'.L₂ : Set G) := by
      intro h₂
      have := s'.le_T₀_of_le_normalizer hyp h12 inf_le_left h₁ h₂
      rw [hs'] at this
      exact absurd this (not_le_of_gt hlt)
    refine ⟨s'.swap, J, ⟨?_, hsyl, ?_, ?_, ?_⟩⟩
    · rw [Setting15419.swap_I]
      exact hJ
    · rw [Setting15419.swap_T₀, hs']
      exact hlt
    · intro J' hJ' hle'
      rw [Setting15419.swap_I] at hJ'
      exact hle J' hJ' hle'
    · exact h₂
  · exact ⟨s', J, ⟨hJ, hsyl, hs' ▸ hlt, hle, h₁⟩⟩

namespace Config15420

variable {s : Setting15419 G T} {I₀ : Subgroup G}

theorem le_normalizer (hyp : MultipleCentralizerHypothesis G T) (h12 : Stmt15412 G T)
    (c : Config15420 s I₀) : T ≤ Subgroup.normalizer ((T ⊓ I₀ : Subgroup G) : Set G) := by
  have hcomm : ⁅T, T⁆ ≤ T ⊓ I₀ := (s.commutator_le_T₀ hyp h12).trans c.lt.le
  have key : ∀ t ∈ T, ∀ x ∈ T ⊓ I₀, t * x * t⁻¹ ∈ T ⊓ I₀ := by
    intro t ht x hx
    have h1 : t * x * t⁻¹ * x⁻¹ ∈ T ⊓ I₀ := by
      have := Subgroup.commutator_mem_commutator ht hx.1
      rw [commutatorElement_def] at this
      exact hcomm this
    have e : t * x * t⁻¹ = (t * x * t⁻¹ * x⁻¹) * x := by group
    rw [e]
    exact Subgroup.mul_mem _ h1 hx
  intro t ht
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨key t ht x, fun hx => ?_⟩
  have := key t⁻¹ (T.inv_mem ht) _ hx
  simpa [mul_assoc] using this

omit [Finite G] in
theorem exists_swap (c : Config15420 s I₀) :
    ∃ u ∈ T ⊓ I₀, s.L₁.map (MulAut.conj u).toMonoidHom ≠ s.L₁ := by
  by_contra h
  push Not at h
  exact c.not_le fun u hu => mem_normalizer_iff_map_conj.mpr (h u hu)

theorem le_X (hyp : MultipleCentralizerHypothesis G T) (h12 : Stmt15412 G T)
    (c : Config15420 s I₀) : s.X ≤ I₀ := by
  obtain ⟨u, hu, hne⟩ := c.exists_swap
  have huM : u ∈ s.M₁ := s.inM₁.2 hu.1
  have hL₁ : s.L₁ ≤ I₀ := ((le_sup_left.trans le_sup_left).trans c.inH.1)
  have hL₁u : s.L₁.map (MulAut.conj u).toMonoidHom ≤ I₀ := by
    rw [← map_conj_eq_self_of_mem hu.2]
    exact Subgroup.map_mono hL₁
  obtain ⟨hX, -⟩ := s.dataX
  rw [hX]
  rcases s.choice₁ with h | h <;> rcases s.permutesX hyp h12 huM with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact absurd (h ▸ h1 : s.L₁.map (MulAut.conj u).toMonoidHom = s.L₁) hne
  · rw [h] at hL₁ hL₁u
    rw [h1] at hL₁u
    exact sup_le hL₁ hL₁u
  · exact absurd (h ▸ h2 : s.L₁.map (MulAut.conj u).toMonoidHom = s.L₁) hne
  · rw [h] at hL₁ hL₁u
    rw [h2] at hL₁u
    exact sup_le hL₁u hL₁

theorem omegaOneCenter_le (c : Config15420 s I₀) : quasithinOmegaOneCenter T ≤ T ⊓ I₀ :=
  (((L15420.omegaOneCenter_le_eOf T).trans (L15420.eOf_le_baum T)).trans s.baum_le_T₀).trans
    c.lt.le

end Config15420

omit [Finite G] in
theorem inf_centralizer_omegaOneCenter_le (h8 : Stmt1548 G T) (I₀ : Subgroup G) :
    I₀ ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) ≤ T ⊓ I₀ := fun _ hx =>
  ⟨h8 ▸ hx.2, hx.1⟩

theorem exists_zX (hnot : ¬ IsLThreeTwoOrASix G)
    (h12 : Stmt15412 G T) (h14 : Stmt15414 G T) (s : Setting15419 G T) :
    ∃ z ∈ quasithinOmegaOneCenter T, z ≠ 1 ∧ z ∈ Subgroup.centralizer (s.X : Set G) ∧
      Subgroup.centralizer ({z} : Set G) ≤ s.M₁ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hidx, hZ4⟩ := h14 hnot
  have h2 := hidx s.X s.famX
  have hne : quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (s.X : Set G) ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.relIndex_bot_left, hZ4] at h2
    omega
  obtain ⟨z, ⟨hzZ, hzX⟩, hz1'⟩ :=
    (Subgroup.bot_or_exists_ne_one (quasithinOmegaOneCenter T ⊓
      Subgroup.centralizer (s.X : Set G))).resolve_left hne
  refine ⟨z, hzZ, hz1', hzX, ?_⟩
  obtain ⟨-, -, hU₁, -⟩ := (h12 s.M₁ s.inM₁).2 s.X s.famX s.le_X
  have hz2 : (z : G) ^ 2 = 1 := sq_eq_one_of_mem_omegaOneCenter T hzZ
  have hzo : orderOf (z : G) = 2 := orderOf_eq_prime hz2 hz1'
  have hP2 : IsPGroup 2 (Subgroup.zpowers (z : G)) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, hzo, pow_one]
  have hPne : Subgroup.zpowers (z : G) ≠ ⊥ := by
    rw [Ne, Subgroup.zpowers_eq_bot]
    exact hz1'
  have h2loc : IsTwoLocal (Subgroup.normalizer ((Subgroup.zpowers (z : G) : Subgroup G) : Set G)) :=
    ⟨_, hPne, hP2, rfl⟩
  obtain ⟨M, hM, hNM⟩ := exists_maxTwoLocal_ge h2loc
  have hCN : Subgroup.centralizer ({(z : G)} : Set G) ≤
      Subgroup.normalizer ((Subgroup.zpowers (z : G) : Subgroup G) : Set G) := by
    rw [Subgroup.zpowers_eq_closure, ← Subgroup.centralizer_closure]
    exact Subgroup.centralizer_le_normalizer _
  have hXC : s.X ≤ Subgroup.centralizer ({(z : G)} : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.mp hzX x hx
  have hTC : T ≤ Subgroup.centralizer ({(z : G)} : Set G) := by
    intro t ht
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.mp (L15420.omegaOneCenter_le_center T hzZ).2 t ht
  have hXTM : s.X ⊔ T ≤ M := (sup_le hXC hTC).trans (hCN.trans hNM)
  have e : M = s.M₁ := hU₁.2 M ⟨hM, hXTM⟩
  rw [← e]
  exact hCN.trans hNM

namespace L15420

variable {G : Type*} [Group G]

theorem mem_normalizer_sup {A B : Subgroup G} {g : G}
    (hA : g ∈ Subgroup.normalizer (A : Set G)) (hB : g ∈ Subgroup.normalizer (B : Set G)) :
    g ∈ Subgroup.normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hA hB ⊢
  rw [Subgroup.map_sup, hA, hB]

theorem mem_normalizer_inf {A B : Subgroup G} {g : G}
    (hA : g ∈ Subgroup.normalizer (A : Set G)) (hB : g ∈ Subgroup.normalizer (B : Set G)) :
    g ∈ Subgroup.normalizer ((A ⊓ B : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at hA hB ⊢
  intro x
  simp only [Subgroup.mem_inf]
  rw [hA x, hB x]

theorem normalizer_le_normalizer_of_char {C R : Subgroup G} (hCR : C ≤ R)
    (hchar : (C.subgroupOf R).Characteristic) :
    Subgroup.normalizer (R : Set G) ≤ Subgroup.normalizer (C : Set G) := by
  have := CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic (C.subgroupOf R)
  rwa [Subgroup.map_subgroupOf_eq_of_le hCR] at this

theorem pCoreOf_le_of_isSylowTwoOf [Finite G] {M S : Subgroup G} (hS : IsSylowTwoOf S M) :
    pCoreOf 2 M ≤ S :=
  hS.le_of_normalizes (CFSG.LieType.BorelTits.pCoreOf_le 2 M)
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M)
    (by have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
        exact CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M)

theorem isSylowTwoOf_of_le_of_le [Finite G] {S K H : Subgroup G} (hS : IsSylowTwoOf S H)
    (hSK : S ≤ K) (hKH : K ≤ H) : IsSylowTwoOf S K := by
  refine isSylowTwoOf_of_card_eq hSK hS.isPGroup (le_antisymm ?_ ?_)
  · exact card_le_twoPart hSK hS.isPGroup
  · rw [hS.card_eq]
    exact twoPart_mono hKH

end L15420

namespace Config15420

variable {s : Setting15419 G T} {I₀ : Subgroup G}

omit [Finite G] in
theorem M₁_le_normalizer_X (h12 : Stmt15412 G T) (s : Setting15419 G T) :
    s.M₁ ≤ Subgroup.normalizer (s.X : Set G) :=
  ((h12 s.M₁ s.inM₁).2 s.X s.famX s.le_X).1

theorem le_normalizer_R (hyp : MultipleCentralizerHypothesis G T) (h12 : Stmt15412 G T)
    (c : Config15420 s I₀) :
    T ≤ Subgroup.normalizer ((pCoreOf 2 (s.X ⊔ T ⊓ I₀) : Subgroup G) : Set G) := by
  have hTX : T ≤ Subgroup.normalizer (s.X : Set G) := s.inM₁.2.trans (M₁_le_normalizer_X h12 s)
  have hTT := c.le_normalizer hyp h12
  have h : T ≤ Subgroup.normalizer ((s.X ⊔ T ⊓ I₀ : Subgroup G) : Set G) := fun t ht =>
    L15420.mem_normalizer_sup (hTX ht) (hTT ht)
  exact h.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _)

omit [Finite G] in
theorem X_le_normalizer_R :
    s.X ≤ Subgroup.normalizer ((pCoreOf 2 (s.X ⊔ T ⊓ I₀) : Subgroup G) : Set G) :=
  le_sup_left.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _)

theorem normalizer_le_M₁ (hyp : MultipleCentralizerHypothesis G T) (h12 : Stmt15412 G T)
    (c : Config15420 s I₀) {C : Subgroup G} (hCR : C ≤ pCoreOf 2 (s.X ⊔ T ⊓ I₀)) (hC : C ≠ ⊥)
    (hchar : (C.subgroupOf (pCoreOf 2 (s.X ⊔ T ⊓ I₀))).Characteristic) :
    Subgroup.normalizer (C : Set G) ≤ s.M₁ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, hU₁, -⟩ := (h12 s.M₁ s.inM₁).2 s.X s.famX s.le_X
  have hNR := L15420.normalizer_le_normalizer_of_char hCR hchar
  have hXT : s.X ⊔ T ≤ Subgroup.normalizer (C : Set G) :=
    (sup_le X_le_normalizer_R (c.le_normalizer_R hyp h12)).trans hNR
  have h2 : IsTwoLocal (Subgroup.normalizer (C : Set G)) :=
    ⟨C, hC, (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _).to_le hCR, rfl⟩
  obtain ⟨M, hM, hNM⟩ := exists_maxTwoLocal_ge h2
  have e : M = s.M₁ := hU₁.2 M ⟨hM, hXT.trans hNM⟩
  rw [← e]
  exact hNM

theorem omegaOneCenter_le_R (hyp : MultipleCentralizerHypothesis G T) (c : Config15420 s I₀) :
    quasithinOmegaOneCenter T ≤ pCoreOf 2 (s.X ⊔ T ⊓ I₀) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hS⟩ := exists_sylow_of_quasithinIsSylowTwo hyp.sylow
  have hXT2 : pCoreOf 2 (s.X ⊔ T) ≠ ⊥ := by
    rcases s.famX.1 with h | h
    · exact h.2.2.1
    · exact h.2.2.1.2
  have hSle : (S : Subgroup G) ≤ s.X ⊔ T := by rw [hS]; exact le_sup_right
  have hchar : CharTwo (s.X ⊔ T) := charTwo_of_inH hyp.qtke.2.1 S ⟨hSle, hXT2⟩
  have hO2T : pCoreOf 2 (s.X ⊔ T) ≤ T := by
    have := pCoreOf_two_le_sylow _ S hSle
    rwa [hS] at this
  have hZO : quasithinOmegaOneCenter T ≤ pCoreOf 2 (s.X ⊔ T) := by
    intro z hz
    have hz' := L15420.omegaOneCenter_le_center T hz
    refine hchar ⟨Subgroup.mem_sup_right hz'.1, ?_⟩
    exact Subgroup.centralizer_le hO2T hz'.2
  have hTIT : s.X ⊔ T ⊓ I₀ ≤ s.X ⊔ T := sup_le_sup_left inf_le_left _
  have hZ2 : quasithinOmegaOneCenter T ≤ s.X ⊔ T ⊓ I₀ :=
    c.omegaOneCenter_le.trans (le_sup_right : T ⊓ I₀ ≤ s.X ⊔ T ⊓ I₀)
  refine (le_inf hZO hZ2).trans ?_
  refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right ?_
    ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _).to_le inf_le_left)
  intro g hg
  exact L15420.mem_normalizer_inf
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _ (hTIT hg)) (Subgroup.le_normalizer hg)

theorem commutator_X_R_le (hyp : MultipleCentralizerHypothesis G T) (h12 : Stmt15412 G T)
    (c : Config15420 s I₀) : ⁅s.X, pCoreOf 2 (s.X ⊔ T ⊓ I₀)⁆ ≤ pCoreOf 2 s.X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set R := pCoreOf 2 (s.X ⊔ T ⊓ I₀) with hRdef
  have hXI : s.X ⊔ T ⊓ I₀ ≤ I₀ := sup_le (c.le_X hyp h12) inf_le_right
  have hRT : R ≤ T :=
    (L15420.pCoreOf_le_of_isSylowTwoOf
      (L15420.isSylowTwoOf_of_le_of_le c.sylow le_sup_right hXI)).trans inf_le_left
  have hRX : R ≤ Subgroup.normalizer (s.X : Set G) :=
    hRT.trans (s.inM₁.2.trans (M₁_le_normalizer_X h12 s))
  have h1 : ⁅s.X, R⁆ ≤ s.X := commutator_le_of_le_normalizer hRX
  have h2 : ⁅s.X, R⁆ ≤ R := by
    rw [Subgroup.commutator_comm]
    exact commutator_le_of_le_normalizer X_le_normalizer_R
  refine (le_inf h1 h2).trans ?_
  refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left ?_
    ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _).to_le inf_le_right)
  intro x hx
  exact L15420.mem_normalizer_inf (Subgroup.le_normalizer hx) (X_le_normalizer_R hx)

end Config15420

end CFSG.Quasithin.EmptyFaithfulMultiple
