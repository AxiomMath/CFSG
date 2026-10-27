module

public import CFSG.Quasithin.H13.A6S1355
public import CFSG.Quasithin.Background.F8G2
public import CFSG.Quasithin.H13.A6S4Reduced

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin

@[expose] def Input1356Two : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (S : Setting4 G T L V),
    ¬ LieModel G .PSp 3 2 1 → ∀ g : G, conjSub g S.V2 ≤ V →
      ∃ l ∈ L, conjSub g S.V2 = conjSub l S.V2

theorem inW4_of_inW2 : ∀ y : P6, InW2 y → InW4 y := by
  decide +kernel

@[expose] def StabW2 (σ : Perm (Fin 6)) : Prop := ∀ y : P6, InW2 y → InW2 (act4f σ y)

instance (σ : Perm (Fin 6)) : Decidable (StabW2 σ) := by unfold StabW2; infer_instance

@[expose] def TrivModW2 (σ : Perm (Fin 6)) : Prop :=
  ∀ x : P6, InW4 x → InW2 (x * (act4f σ x)⁻¹)

instance (σ : Perm (Fin 6)) : Decidable (TrivModW2 σ) := by unfold TrivModW2; infer_instance

@[expose] def K4syn : List (Perm (Fin 6)) :=
  [1, swap 0 1 * swap 2 3, swap 0 1 * swap 4 5, swap 2 3 * swap 4 5]

theorem mem_K4syn : ∀ σ : Perm (Fin 6), StabW2 σ → TrivModW2 σ → Perm.sign σ = 1 →
    σ ∈ K4syn := by
  decide +kernel

@[expose] def OntoW2 (σ : Perm (Fin 6)) : Prop :=
  ∀ y : P6, InW2 y → ∃ x : P6, InW4 x ∧ y = x * (act4f σ x)⁻¹

instance (σ : Perm (Fin 6)) : Decidable (OntoW2 σ) := by unfold OntoW2; infer_instance

theorem K4syn_onto : ∀ σ ∈ K4syn, σ ≠ 1 → OntoW2 σ := by
  decide +kernel

@[expose] def FPF (σ : Perm (Fin 6)) : Prop :=
  ∀ y : P6, InW4 y → ∃ x : P6, InW4 x ∧ y = x * (act4f σ x)⁻¹

instance (σ : Perm (Fin 6)) : Decidable (FPF σ) := by unfold FPF; infer_instance

@[expose] def MovesW2 (σ : Perm (Fin 6)) : Prop := ∃ y : P6, InW2 y ∧ act4f σ y ≠ y

instance (σ : Perm (Fin 6)) : Decidable (MovesW2 σ) := by unfold MovesW2; infer_instance

@[expose] def SpanMod (σ : Perm (Fin 6)) : Prop :=
  ∀ y z : P6, InW4 y → ¬ InW2 y → InW4 z → InW2 z ∨ InW2 (z * y) ∨ InW2 (z * act4f σ y) ∨
    InW2 (z * y * act4f σ y)

instance (σ : Perm (Fin 6)) : Decidable (SpanMod σ) := by unfold SpanMod; infer_instance

theorem fpf_of : ∀ σ : Perm (Fin 6), StabW2 σ → σ ^ 45 = 1 → MovesW2 σ → FPF σ ∧ SpanMod σ := by
  decide +kernel

theorem pow_45_of_odd {σ : Perm (Fin 6)} {m : ℕ} (hm : Odd m) (h : σ ^ m = 1) : σ ^ 45 = 1 := by
  rw [← orderOf_dvd_iff_pow_eq_one]
  have h1 : orderOf σ ∣ m := orderOf_dvd_of_pow_eq_one h
  have h2 : orderOf σ ∣ 2 ^ 4 * 45 := by
    have := orderOf_dvd_card (x := σ)
    rwa [Fintype.card_perm, Fintype.card_fin] at this
  have hcop : (orderOf σ).Coprime (2 ^ 4) :=
    Nat.Coprime.pow_right 4 (Nat.coprime_two_right.2 (Odd.of_dvd_nat hm h1))
  exact hcop.dvd_of_dvd_mul_left h2

theorem orderOf_c3 : orderOf (swap (0 : Fin 3) 1 * swap 1 2) = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact orderOf_eq_prime (by decide) (by decide)

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

theorem V2_lt_V : S.V2 < V := by
  refine lt_of_le_of_ne S.V2_le_V fun h => ?_
  have := S.card_V2
  rw [h, S.card_V] at this
  omega

theorem stabW2_of_mem {x : ↥(Subgroup.normalizer (V : Set G))}
    (hx : (x : G) ∈ Subgroup.normalizer (S.V2 : Set G)) : StabW2 (S.frame.ρ x) := by
  intro y hy
  obtain ⟨v, hv⟩ := S.frame.ψ.surjective ⟨y, inW4_of_inW2 y hy⟩
  have hv2 : (v : G) ∈ S.V2 := by
    refine S.mem_pre.2 ⟨v.2, ?_⟩
    have e : S.frame.ψ ⟨(v : G), v.2⟩ = ⟨y, inW4_of_inW2 y hy⟩ := hv
    rw [e]
    exact hy
  obtain ⟨_, hW⟩ := S.mem_pre.1 ((Subgroup.mem_normalizer_iff.mp hx v).mp hv2)
  have e : S.frame.ψ ⟨(x : G) * v * (x : G)⁻¹, (Subgroup.mem_normalizer_iff.mp x.2 v).mp v.2⟩ =
      act4 (S.frame.ρ x) ⟨y, inW4_of_inW2 y hy⟩ := by
    rw [S.psi_conj x v, hv]
  have hW' : S.frame.ψ ⟨(x : G) * v * (x : G)⁻¹,
      (Subgroup.mem_normalizer_iff.mp x.2 v).mp v.2⟩ ∈ W2sub := hW
  rw [e] at hW'
  exact hW'

theorem movesW2_of_not_mem {x : ↥(Subgroup.normalizer (V : Set G))}
    (hx : (x : G) ∉ Subgroup.centralizer (S.V2 : Set G)) : MovesW2 (S.frame.ρ x) := by
  rw [Subgroup.mem_centralizer_iff] at hx
  push Not at hx
  obtain ⟨w, hw, hne⟩ := hx
  obtain ⟨hwV, hwW2⟩ := S.mem_pre.1 hw
  refine ⟨S.frame.ψ ⟨w, hwV⟩, hwW2, fun h => hne ?_⟩
  have h' : act4 (S.frame.ρ x) (S.frame.ψ ⟨w, hwV⟩) = S.frame.ψ ⟨w, hwV⟩ := Subtype.ext h
  have := (S.conj_eq_iff x ⟨w, hwV⟩).2 h'
  calc w * x = x * w * (x : G)⁻¹ * x := by rw [this]
    _ = x * w := by group

theorem mem_V2_of {v : ↥V} (h : InW2 (S.frame.ψ v : P6)) : (v : G) ∈ S.V2 :=
  S.mem_pre.2 ⟨v.2, h⟩

theorem le_of_fpf {X : Subgroup G} {x : ↥(Subgroup.normalizer (V : Set G))} (hxX : (x : G) ∈ X)
    (hVX : V ≤ Subgroup.normalizer (X : Set G)) (hfpf : FPF (S.frame.ρ x)) : V ≤ X := by
  intro v hv
  obtain ⟨y, hyW4, hy⟩ := hfpf _ (S.frame.ψ ⟨v, hv⟩).2
  obtain ⟨u, hu⟩ := S.frame.ψ.surjective ⟨y, hyW4⟩
  have hxu : (x : G) * u * (x : G)⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp x.2 u).mp u.2
  have heq : v = u * x * (u : G)⁻¹ * (x : G)⁻¹ := by
    have e : (u : G) * x * (u : G)⁻¹ * (x : G)⁻¹ = u * ((x : G) * u * (x : G)⁻¹)⁻¹ := by group
    have h1 : S.frame.ψ ⟨v, hv⟩ = S.frame.ψ (u * (⟨(x : G) * u * (x : G)⁻¹, hxu⟩ : ↥V)⁻¹) := by
      rw [map_mul, map_inv, S.psi_conj x u, hu]
      exact Subtype.ext hy
    have := congrArg Subtype.val (S.frame.ψ.injective h1)
    rw [e]
    simpa using this
  rw [heq]
  have h2 : (u : G) * x * (u : G)⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.mp (hVX u.2) x).mp hxX
  exact X.mul_mem h2 (X.inv_mem hxX)

@[expose] noncomputable def X2 : Subgroup G := by
  classical
  exact if IsHatA6 L then oTwoRes ⁅L₁Of L S.V2, T ⊓ L⁆ else L₁Of L S.V2

theorem X2_hat (h : IsHatA6 L) : S.X2 = oTwoRes ⁅L₁Of L S.V2, T ⊓ L⁆ := by
  simp [X2, h]

theorem X2_not_hat (h : ¬ IsHatA6 L) : S.X2 = L₁Of L S.V2 := by
  simp [X2, h]

theorem X2_le_L2 : S.X2 ≤ S.L2 := by
  by_cases h : IsHatA6 L
  · rw [S.X2_hat h]
    refine (oTwoRes_le _).trans ?_
    rw [Subgroup.commutator_le]
    intro a ha b hb
    rw [commutatorElement_def]
    have hbN : b ∈ Subgroup.normalizer (S.L2 : Set G) :=
      le_normalizer_oTwoRes (L ⊓ Subgroup.normalizer (S.V2 : Set G))
        ⟨hb.2, S.T_le_normalizer_V2 hb.1⟩
    have h1 : b * a⁻¹ * b⁻¹ ∈ S.L2 :=
      (Subgroup.mem_normalizer_iff.mp hbN _).mp (Subgroup.inv_mem _ ha)
    have e : a * b * a⁻¹ * b⁻¹ = a * (b * a⁻¹ * b⁻¹) := by group
    rw [e]
    exact Subgroup.mul_mem _ ha h1
  · rw [S.X2_not_hat h]
    exact le_rfl

theorem L2_le_L : S.L2 ≤ L := (oTwoRes_le _).trans inf_le_left

theorem L2_le_NV2 : S.L2 ≤ Subgroup.normalizer (S.V2 : Set G) := (oTwoRes_le _).trans inf_le_right

theorem pCoreOf_G1_le_T : pCoreOf 2 (g1 T V) ≤ T := pCoreOf_le_of_sylow S.h13.sylow S.T_le_NV1

theorem I2_le_NV2 : conjClosure (pCoreOf 2 (g1 T V)) (Subgroup.normalizer (S.V2 : Set G)) ≤
    Subgroup.normalizer (S.V2 : Set G) :=
  conjClosure_le fun _ hh _ hq => Subgroup.mul_mem _ (Subgroup.mul_mem _ hh
    (S.T_le_normalizer_V2 (S.pCoreOf_G1_le_T hq))) (Subgroup.inv_mem _ hh)

theorem exists_X2_elem (h13315 : Stmt13_3_15) :
    ∃ x ∈ S.X2, (∃ m : ℕ, Odd m ∧ x ^ m = 1) ∧ x ∉ Subgroup.centralizer (S.V2 : Set G) ∧
      x ∈ Subgroup.normalizer (S.V2 : Set G) := by
  obtain ⟨-, -, h3, ⟨e⟩, h5, -⟩ := h13315 G T L V S.V2 S.X2 _ S.h13 S.irr S.zv S.isV2
    S.not_iso_a5 S.X2_hat S.X2_not_hat rfl
  set I₂ := conjClosure (pCoreOf 2 (g1 T V)) (Subgroup.normalizer (S.V2 : Set G))
  obtain ⟨y, hy⟩ := QuotientGroup.mk_surjective (e.symm (swap (0 : Fin 3) 1 * swap 1 2))
  obtain ⟨a, m, hm, hnm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos y).ne'
  have hym : (y ^ (2 ^ a)) ^ m = 1 := by rw [← pow_mul, ← hnm, pow_orderOf_eq_one]
  have hne : ((y ^ (2 ^ a) : ↥I₂) : ↥I₂ ⧸ CFSG.pCore 2 ↥I₂) ≠ 1 := by
    intro h
    have h1 : e ((y : ↥I₂ ⧸ CFSG.pCore 2 ↥I₂) ^ (2 ^ a)) = 1 := by
      rw [← QuotientGroup.mk_pow, h, map_one]
    rw [map_pow, hy, MulEquiv.apply_symm_apply] at h1
    have h2 := orderOf_dvd_of_pow_eq_one h1
    rw [orderOf_c3] at h2
    have h3 := Nat.prime_three.dvd_of_dvd_pow h2
    omega
  refine ⟨((y ^ (2 ^ a) : ↥I₂) : G), ?_, ⟨m, hm, by simpa using congrArg Subtype.val hym⟩,
    fun hC => hne ?_, S.I2_le_NV2 (y ^ (2 ^ a)).2⟩
  · rw [← h5]
    exact Subgroup.subset_closure ⟨(y ^ (2 ^ a)).2, m, hm, by simpa using congrArg Subtype.val hym⟩
  · rw [QuotientGroup.eq_one_iff]
    have : ((y ^ (2 ^ a) : ↥I₂) : G) ∈ pCoreOf 2 I₂ := by
      rw [← h3]
      exact ⟨(y ^ (2 ^ a)).2, hC⟩
    exact (mem_pCore_iff _).2 this

theorem NV2_le_NX2 (h13315 : Stmt13_3_15) :
    Subgroup.normalizer (S.V2 : Set G) ≤ Subgroup.normalizer (S.X2 : Set G) := by
  obtain ⟨h1, -, -, -, h5, -⟩ := h13315 G T L V S.V2 S.X2 _ S.h13 S.irr S.zv S.isV2
    S.not_iso_a5 S.X2_hat S.X2_not_hat rfl
  rw [← h5]
  exact A5.le_normalizer_oTwoRes_of_le_normalizer h1

theorem V_le_X2 (h13315 : Stmt13_3_15) : V ≤ S.X2 := by
  obtain ⟨x, hxX, ⟨m, hm, hxm⟩, hxC, hxN⟩ := S.exists_X2_elem h13315
  have hxL : x ∈ L := S.L2_le_L (S.X2_le_L2 hxX)
  have hx' : (⟨x, S.frame.L_le hxL⟩ : ↥(Subgroup.normalizer (V : Set G))) ^ m = 1 :=
    Subtype.ext (by simpa using hxm)
  have h45 : (S.frame.ρ ⟨x, S.frame.L_le hxL⟩) ^ 45 = 1 := by
    refine pow_45_of_odd hm ?_
    rw [← map_pow, hx', map_one]
  obtain ⟨hfpf, -⟩ := fpf_of _ (S.stabW2_of_mem hxN) h45 (S.movesW2_of_not_mem hxC)
  exact S.le_of_fpf (x := ⟨x, S.frame.L_le hxL⟩) hxX
    ((S.V_le_T.trans S.T_le_normalizer_V2).trans (S.NV2_le_NX2 h13315)) hfpf

theorem almostSpecialHyp_V2 (h13315 : Stmt13_3_15) :
    AlmostSpecialHyp V S.V2 L T (Subgroup.normalizer (S.V2 : Set G)) where
  elemAbelian := S.elemAbelian_V
  ne_bot := fun h => by
    have := S.card_V2
    rw [h, Subgroup.card_bot] at this
    omega
  le_V := S.V2_le_V
  oTwo_eq := by
    rw [← oTwoRes_eq_oTwoUpper]
    exact (A5.oTwoRes_eq_of_faithful S.h13.faithful).symm
  V_le_T := S.V_le_T
  T_le_normV₁ := S.T_le_normalizer_V2
  T_le_normV := S.frame.T_le
  T_le_normL := S.T_le_NL
  sylow_LT := A5.isSylowTwoOf_of_le S.h13.sylow le_sup_right
  H_le := le_rfl
  lOne_sup_le := by
    rw [lOne_eq_L₁Of]
    exact sup_le S.L2_le_NV2 S.T_le_normalizer_V2
  sylow_H := A5.isSylowTwoOf_of_le S.h13.sylow S.T_le_normalizer_V2
  charTwo := by
    have hV2 : S.V2 ≤ pCoreOf 2 (Subgroup.normalizer (S.V2 : Set G)) :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 Subgroup.le_normalizer le_rfl
        (S.isPGroup_V.to_le S.V2_le_V)
    have hne : pCoreOf 2 (Subgroup.normalizer (S.V2 : Set G)) ≠ ⊥ := by
      intro h
      rw [h, le_bot_iff] at hV2
      have := S.card_V2
      rw [hV2, Subgroup.card_bot] at this
      omega
    have key : ∀ H : Subgroup G, InH T H → CharTwo H := by
      intro H hH
      obtain ⟨P, hP⟩ := exists_sylow_of_quasithinIsSylowTwo S.h13.sylow
      subst hP
      exact CFSG.Quasithin.charTwo_of_inH S.h13.qtke.2.1 P hH
    exact key _ ⟨S.T_le_normalizer_V2, hne⟩
  irred := by
    rw [lOne_eq_L₁Of]
    refine ⟨S.V2_lt_V, sup_le (S.L2_le_L.trans S.frame.L_le) S.frame.T_le,
      sup_le S.L2_le_NV2 S.T_le_normalizer_V2, fun W h1 h2 hN => ?_⟩
    by_cases hW : W ≤ S.V2
    · exact Or.inl (le_antisymm hW h1)
    right
    refine le_antisymm h2 fun v hv => ?_
    obtain ⟨w, hwW, hwV2⟩ := IsConcreteLE.not_le_iff_exists.1 hW
    have hwV : w ∈ V := h2 hwW
    obtain ⟨x, hxX, ⟨m, hm, hxm⟩, hxC, hxN⟩ := S.exists_X2_elem h13315
    have hxL2 : x ∈ S.L2 := S.X2_le_L2 hxX
    have hxL : x ∈ L := S.L2_le_L hxL2
    set x' : ↥(Subgroup.normalizer (V : Set G)) := ⟨x, S.frame.L_le hxL⟩
    have hx' : x' ^ m = 1 := Subtype.ext (by simpa using hxm)
    have h45 : (S.frame.ρ x') ^ 45 = 1 := by
      refine pow_45_of_odd hm ?_
      rw [← map_pow, hx', map_one]
    obtain ⟨-, hspan⟩ := fpf_of _ (S.stabW2_of_mem hxN) h45 (S.movesW2_of_not_mem hxC)
    have hxW : x ∈ Subgroup.normalizer (W : Set G) := hN (le_sup_left (a := L₁Of L S.V2) hxL2)
    have hxw : x * w * x⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.mp hxW w).mp hwW
    have hxwV : x * w * x⁻¹ ∈ V := h2 hxw
    have hy : ¬ InW2 (S.frame.ψ ⟨w, hwV⟩ : P6) := fun h => hwV2 (S.mem_V2_of h)
    have hσy : act4f (S.frame.ρ x') (S.frame.ψ ⟨w, hwV⟩ : P6) =
        (S.frame.ψ ⟨x * w * x⁻¹, hxwV⟩ : P6) :=
      (congrArg Subtype.val (S.psi_conj x' ⟨w, hwV⟩)).symm
    rcases hspan _ _ (S.frame.ψ ⟨w, hwV⟩).2 hy (S.frame.ψ ⟨v, hv⟩).2 with h | h | h | h
    · exact h1 (S.mem_V2_of h)
    · have hm : InW2 (S.frame.ψ (⟨v, hv⟩ * ⟨w, hwV⟩) : P6) := by
        rw [map_mul]
        exact h
      have := h1 (S.mem_V2_of hm)
      have e : v = (v * w) * w⁻¹ := by group
      rw [e]
      exact W.mul_mem this (W.inv_mem hwW)
    · have hm : InW2 (S.frame.ψ (⟨v, hv⟩ * ⟨x * w * x⁻¹, hxwV⟩) : P6) := by
        rw [map_mul]
        rw [hσy] at h
        exact h
      have := h1 (S.mem_V2_of hm)
      have e : v = (v * (x * w * x⁻¹)) * (x * w * x⁻¹)⁻¹ := by group
      rw [e]
      exact W.mul_mem this (W.inv_mem hxw)
    · have hm : InW2 (S.frame.ψ (⟨v, hv⟩ * ⟨w, hwV⟩ * ⟨x * w * x⁻¹, hxwV⟩) : P6) := by
        rw [map_mul, map_mul]
        rw [hσy] at h
        exact h
      have := h1 (S.mem_V2_of hm)
      have e : v = (v * w * (x * w * x⁻¹)) * (x * w * x⁻¹)⁻¹ * w⁻¹ := by group
      rw [e]
      exact W.mul_mem (W.mul_mem this (W.inv_mem hxw)) (W.inv_mem hwW)

theorem V_le_pCoreOf_G2 (h13315 : Stmt13_3_15) :
    V ≤ pCoreOf 2 (Subgroup.normalizer (S.V2 : Set G)) := by
  have hA := S.almostSpecialHyp_V2 h13315
  have hU := hA.G22_one.2
  have hcc := hA.conjClosure_le_N
  intro v hv
  have hvU : v ∈ conjClosure V (Subgroup.normalizer (S.V2 : Set G)) := le_conjClosure _ _ hv
  have hQ : tmk S.V2 ⟨v, hcc hvU⟩ ∈
      tildeOf S.V2 (pCoreOf 2 (Subgroup.normalizer (S.V2 : Set G))) :=
    omegaOneCenterOf_le _ ((secImg_le_iff.1 hU) ⟨v, hcc hvU⟩ hvU)
  exact (secMk_mem_secImg_iff hA.V₁_le_pCoreOf).1 hQ

theorem comm_mem_V2 (h13315 : Stmt13_3_15) {u u' : G}
    (hu : u ∈ conjClosure V (Subgroup.normalizer (S.V2 : Set G)))
    (hu' : u' ∈ conjClosure V (Subgroup.normalizer (S.V2 : Set G))) :
    u * u' * u⁻¹ * u'⁻¹ ∈ S.V2 := by
  have hA := S.almostSpecialHyp_V2 h13315
  have hU := hA.G22_one.2
  have hcc := hA.conjClosure_le_N
  have hmemY : ∀ u (hu : u ∈ conjClosure V (Subgroup.normalizer (S.V2 : Set G))),
      tmk S.V2 ⟨u, hcc hu⟩ ∈
        omegaOneCenterOf (tildeOf S.V2 (pCoreOf 2 (Subgroup.normalizer (S.V2 : Set G)))) :=
    fun u hu => (secImg_le_iff.1 hU) ⟨u, hcc hu⟩ hu
  have hyQ := omegaOneCenterOf_le _ (hmemY u' hu')
  have hxy := (mem_centralizer_of_mem_omegaOneCenterOf (hmemY u hu) hyQ).symm
  exact commutator_mem_of_secMk_commute hxy

theorem conjClosure_le_NV (h13315 : Stmt13_3_15) :
    conjClosure V (Subgroup.normalizer (S.V2 : Set G)) ≤ Subgroup.normalizer (V : Set G) := by
  intro u hu
  have hVU := le_conjClosure V (Subgroup.normalizer (S.V2 : Set G))
  rw [Subgroup.mem_normalizer_iff]
  intro v
  constructor
  · intro hv
    have hc := S.V2_le_V (S.comm_mem_V2 h13315 hu (hVU hv))
    have e : u * v * u⁻¹ = (u * v * u⁻¹ * v⁻¹) * v := by group
    rw [e]
    exact V.mul_mem hc hv
  · intro hv
    have hc := S.V2_le_V (S.comm_mem_V2 h13315 (Subgroup.inv_mem _ hu) (hVU hv))
    have e : v = (u⁻¹ * (u * v * u⁻¹) * u⁻¹⁻¹ * (u * v * u⁻¹)⁻¹) * (u * v * u⁻¹) := by group
    rw [e]
    exact V.mul_mem hc hv

theorem conjClosure_le_X2 (h13315 : Stmt13_3_15) :
    conjClosure V (Subgroup.normalizer (S.V2 : Set G)) ≤ S.X2 :=
  conjClosure_le fun _ hh _ hv =>
    (Subgroup.mem_normalizer_iff.mp (S.NV2_le_NX2 h13315 hh) _).mp (S.V_le_X2 h13315 hv)

theorem lemma13_5_6_three (hNS : ¬ LieModel G .PSp 3 2 1) (h1356two : Input1356Two)
    (h13315 : Stmt13_3_15) (g : G) (hg : S.V2 ≤ V ⊓ conjSub g⁻¹ V) :
    ⁅V, conjSub g⁻¹ V⁆ = ⊥ ∨ (⁅V, conjSub g⁻¹ V⁆ = S.V2 ∧
      conjSub g⁻¹ V ≤ Subgroup.normalizer (V : Set G) ∧
        autOn (conjSub g⁻¹ V) V ≤ autOn S.L2 V) := by
  have hW : conjSub g S.V2 ≤ V := by
    have := (le_conjSub_iff g⁻¹).1 (hg.trans inf_le_right)
    rwa [inv_inv] at this
  obtain ⟨l, hlL, hl⟩ := h1356two G T L V S hNS g hW
  have hk : l⁻¹ * g ∈ Subgroup.normalizer (S.V2 : Set G) := by
    have e : conjSub (l⁻¹ * g) S.V2 = S.V2 := by
      rw [conjSub_mul, hl, conjSub_conjSub_inv]
    refine F7.mem_normalizer_of_conj_le e.le ?_
    rw [← e, conjSub_conjSub_inv, e]
  have hVk : conjSub g⁻¹ V = conjSub (l⁻¹ * g)⁻¹ V := by
    rw [mul_inv_rev, inv_inv, conjSub_mul, A5.conjSub_self_of_mem (S.frame.L_le hlL)]
  rw [hVk]
  set k := l⁻¹ * g
  set U := conjClosure V (Subgroup.normalizer (S.V2 : Set G))
  have hUN := S.conjClosure_le_NV h13315
  have hUX := S.conjClosure_le_X2 h13315
  have hVU := le_conjClosure V (Subgroup.normalizer (S.V2 : Set G))
  have hcc : U ≤ Subgroup.normalizer (S.V2 : Set G) := (S.almostSpecialHyp_V2 h13315).conjClosure_le_N
  have hVkU : conjSub k⁻¹ V ≤ U := by
    intro a ha
    rw [mem_conjSub, inv_inv] at ha
    have := mem_conjClosure (Z := V) (Subgroup.inv_mem _ hk) ha
    have e : k⁻¹ * (k * a * k⁻¹) * k⁻¹⁻¹ = a := by group
    rwa [e] at this
  have hρ : ∀ (a : G) (ha : a ∈ conjSub k⁻¹ V), S.frame.ρ ⟨a, hUN (hVkU ha)⟩ ∈ K4syn := by
    intro a ha
    have haU := hVkU ha
    refine mem_K4syn _ (S.stabW2_of_mem (hcc haU)) (fun x hx => ?_)
      ((S.frame.image_L _).1 ⟨_, S.L2_le_L (S.X2_le_L2 (hUX haU)), rfl⟩)
    obtain ⟨v, hv⟩ := S.frame.ψ.surjective ⟨x, hx⟩
    have hvU : (v : G) ∈ U := hVU v.2
    have hc := S.comm_mem_V2 h13315 hvU haU
    have hav : a * v * a⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp (hUN haU) v).mp v.2
    have hcV : (v : G) * a * (v : G)⁻¹ * a⁻¹ ∈ V := S.V2_le_V hc
    have e : S.frame.ψ ⟨(v : G) * a * (v : G)⁻¹ * a⁻¹, hcV⟩ =
        S.frame.ψ (v * (⟨a * v * a⁻¹, hav⟩ : ↥V)⁻¹) := by
      congr 1
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    have hW2 : InW2 (S.frame.ψ ⟨(v : G) * a * (v : G)⁻¹ * a⁻¹, hcV⟩ : P6) :=
      (S.mem_pre.1 hc).2
    rw [e, map_mul, map_inv, S.psi_conj ⟨a, hUN haU⟩ v, hv] at hW2
    exact hW2
  by_cases hall : ∀ (a : G) (ha : a ∈ conjSub k⁻¹ V), S.frame.ρ ⟨a, hUN (hVkU ha)⟩ = 1
  · left
    rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro a ha
    exact (S.rho_eq_one_iff _).1 (hall a ha)
  push Not at hall
  obtain ⟨a, ha, ha1⟩ := hall
  refine Or.inr ⟨le_antisymm ?_ ?_, fun _ hx => hUN (hVkU hx), ?_⟩
  · rw [Subgroup.commutator_le]
    intro v hv b hb
    exact S.comm_mem_V2 h13315 (hVU hv) (hVkU hb)
  · intro w hw
    obtain ⟨hwV, hwW2⟩ := S.mem_pre.1 hw
    obtain ⟨y, hyW4, hy⟩ := K4syn_onto _ (hρ a ha) ha1 _ hwW2
    obtain ⟨u, hu⟩ := S.frame.ψ.surjective ⟨y, hyW4⟩
    have hau : a * u * a⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp (hUN (hVkU ha)) u).mp u.2
    have heq : w = u * a * (u : G)⁻¹ * a⁻¹ := by
      have e : (u : G) * a * (u : G)⁻¹ * a⁻¹ = u * (a * u * a⁻¹)⁻¹ := by group
      have h1 : S.frame.ψ ⟨w, hwV⟩ = S.frame.ψ (u * (⟨a * u * a⁻¹, hau⟩ : ↥V)⁻¹) := by
        rw [map_mul, map_inv, S.psi_conj ⟨a, hUN (hVkU ha)⟩ u, hu]
        exact Subtype.ext hy
      have := congrArg Subtype.val (S.frame.ψ.injective h1)
      rw [e]
      simpa using this
    rw [heq]
    exact Subgroup.commutator_mem_commutator u.2 ha
  · rintro _ ⟨x, hx, rfl⟩
    exact ⟨x, S.X2_le_L2 (hUX (hVkU hx)), rfl⟩

end Setting4

end CFSG.Quasithin.H13.A6
