module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem14Stab
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem14Mod

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin.E3
  CFSG.LieType.BorelTits
open scoped IsMulCommutative commutatorElement

variable {G : Type} [Group G] [Finite G] {T M L V : Subgroup G} {n : ℕ}

theorem oTwoUpper_oTwoUpper_ch6 {G : Type*} [Group G] (X : Subgroup G) :
    oTwoUpper (oTwoUpper X) = oTwoUpper X :=
  le_antisymm (oTwoUpper_le _) ((Subgroup.closure_le _).mpr fun _ hx =>
    mem_oTwoUpper_of_odd (Subgroup.subset_closure hx) hx.2)

theorem le_normalizer_commutator_self {G : Type*} [Group G] (H : Subgroup G) :
    H ≤ Subgroup.normalizer (((⁅H, H⁆ : Subgroup G)) : Set G) := by
  refine le_normalizer_of_conj_mem fun c hc x hx => ?_
  have key : ⁅H, H⁆ ≤ (⁅H, H⁆).comap (MulAut.conj c).toMonoidHom := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, map_commutatorElement]
    exact Subgroup.commutator_mem_commutator
      (by simpa using H.mul_mem (H.mul_mem hc ha) (H.inv_mem hc))
      (by simpa using H.mul_mem (H.mul_mem hc hb) (H.inv_mem hc))
  simpa using key hx

theorem commutator_self_eq_of_simple {X : Type*} [Group X] {S : Subgroup X}
    (hs : IsSimpleGroup ↥S) {B B' : X} (hB : B ∈ S) (hB' : B' ∈ S) (hBB' : B * B' ≠ B' * B) :
    ⁅S, S⁆ = S := by
  refine le_antisymm (A3.commutator_self_le S) ?_
  have hnorm : ((⁅S, S⁆ : Subgroup X).subgroupOf S).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (A3.commutator_self_le S)).mpr
      (le_normalizer_commutator_self S)
  rcases hs.eq_bot_or_eq_top_of_normal ((⁅S, S⁆ : Subgroup X).subgroupOf S) with h0 | h0
  · exfalso
    have hmem : (⟨⁅B, B'⁆, A3.commutator_self_le S (Subgroup.commutator_mem_commutator hB hB')⟩ :
        ↥S) ∈ (⁅S, S⁆ : Subgroup X).subgroupOf S :=
      Subgroup.mem_subgroupOf.mpr (Subgroup.commutator_mem_commutator hB hB')
    rw [h0, Subgroup.mem_bot] at hmem
    have h1 : ⁅B, B'⁆ = 1 := congrArg Subtype.val hmem
    exact hBB' (commutatorElement_eq_one_iff_mul_comm.mp h1)
  · intro x hx
    have : (⟨x, hx⟩ : ↥S) ∈ (⁅S, S⁆ : Subgroup X).subgroupOf S := by
      rw [h0]
      exact Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.mp this

theorem eq_bot_or_eq_of_subnormal_simple {X : Type*} [Group X] {S A : Subgroup X}
    (hs : IsSimpleGroup ↥S) (hA : IsSubnormal A S) : A = ⊥ ∨ A = S :=
  hA.eq_bot_or_eq_of_isSimpleGroup hs

theorem eq_bot_of_isPGroup_of_perfect {G : Type*} [Group G] [Finite G] {K : Subgroup G}
    (hK : IsPGroup 2 K) (hp : ⁅K, K⁆ = K) : K = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsNilpotent ↥K := hK.isNilpotent
  have hsolv : Group.IsSolvable ↥K := inferInstance
  rw [← perfectCore_eq_self_of_perfect hp]
  exact (isSolvable_iff_perfectCore_eq_bot K).mp hsolv

theorem exists_pow_mul_eq {G : Type*} [Group G] {H M : Subgroup G}
    (hHM : M ≤ Subgroup.normalizer (H : Set G)) {y z : G} (hy : y ∈ H) (hz : z ∈ M) (j : ℕ) :
    ∃ y' ∈ H, (y * z) ^ j = y' * z ^ j := by
  induction j with
  | zero => exact ⟨1, H.one_mem, by simp⟩
  | succ j ih =>
    obtain ⟨y', hy', hj⟩ := ih
    refine ⟨y' * (z ^ j * y * (z ^ j)⁻¹), H.mul_mem hy'
      ((Subgroup.mem_normalizer_iff.mp (hHM (M.pow_mem hz j)) y).mp hy), ?_⟩
    rw [pow_succ, hj, pow_succ]
    group

theorem oTwoUpper_le_of_map_eq {G : Type*} [Group G] [Finite G] {L : Subgroup G} {Y : Type*}
    [Group Y] (f : ↥L →* Y) (hker : ∀ x : ↥L, f x = 1 → ∃ k : ℕ, (x : G) ^ 2 ^ k = 1)
    {H X : Subgroup G} (hHX : IsSubnormal H X) (hXL : X ≤ L)
    (hf : (X.subgroupOf L).map f ≤ (H.subgroupOf L).map f) : oTwoUpper X ≤ H := by
  revert hf
  induction hHX with
  | refl => exact fun _ => oTwoUpper_le _
  | @step H' M _ hle hN hMX ih =>
    intro hf
    have hsub : (M.subgroupOf L).map f ≥ (H'.subgroupOf L).map f :=
      Subgroup.map_mono fun x hx => Subgroup.mem_subgroupOf.mpr
        (hle (Subgroup.mem_subgroupOf.mp hx))
    have h1 : oTwoUpper _ ≤ M := ih hXL (hf.trans hsub)
    have hHMn : M ≤ Subgroup.normalizer (H' : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hle).mp hN
    have hML : M ≤ L := (A3.subnormal_le hMX).trans hXL
    have h2 : oTwoUpper M ≤ H' := by
      refine oTwoUpper_le_of_pow_mem fun x hx => ?_
      have hxL : x ∈ L := hML hx
      have hmem : f ⟨x, hxL⟩ ∈ (H'.subgroupOf L).map f :=
        hf (Subgroup.mem_map_of_mem f (Subgroup.mem_subgroupOf.mpr (A3.subnormal_le hMX hx)))
      obtain ⟨y, hy, hfy⟩ := Subgroup.mem_map.mp hmem
      have hyH : (y : G) ∈ H' := Subgroup.mem_subgroupOf.mp hy
      obtain ⟨k, hk⟩ := hker (y⁻¹ * ⟨x, hxL⟩) (by rw [map_mul, map_inv, hfy, inv_mul_cancel])
      have hzM : (y : G)⁻¹ * x ∈ M := M.mul_mem (M.inv_mem (hle hyH)) hx
      obtain ⟨y', hy', hpow⟩ := exists_pow_mul_eq hHMn hyH hzM (2 ^ k)
      refine ⟨k, ?_⟩
      have e : x = (y : G) * ((y : G)⁻¹ * x) := by group
      have hk' : ((y : G)⁻¹ * x) ^ 2 ^ k = 1 := by simpa using hk
      rw [e, hpow, hk', mul_one]
      exact hy'
    calc oTwoUpper _ = oTwoUpper (oTwoUpper _) := (oTwoUpper_oTwoUpper_ch6 _).symm
      _ ≤ oTwoUpper M := oTwoUpper_mono h1
      _ ≤ H' := h2

namespace Hyp611Nat

theorem exists_fieldAut_data (h : Hyp611Nat G T M L V n) {t : G} (htT : t ∈ T)
    (ht : IsInvolutoryFieldAut L t) :
    ∃ (σ : h.data.K ≃+* h.data.K) (u₁ u₂ : Fin 2 → h.data.K),
      (∀ (c : h.data.K) (w : Fin 2 → h.data.K),
        h.data.conj ⟨t, h.toHyp611.T_le_normalizer htT⟩ (c • w) =
          σ c • h.data.conj ⟨t, h.toHyp611.T_le_normalizer htT⟩ w) ∧
      h.data.conj ⟨t, h.toHyp611.T_le_normalizer htT⟩ u₁ = u₁ ∧
      h.data.conj ⟨t, h.toHyp611.T_le_normalizer htT⟩ u₂ = u₂ ∧ det2 u₁ u₂ ≠ 0 ∧
      Nat.card ↥(stabFixField σ) * Nat.card ↥(stabFixField σ) = 2 ^ n := by
  set tt : Subgroup.normalizer (V : Set G) := ⟨t, h.toHyp611.T_le_normalizer htT⟩ with htt
  obtain ⟨σ, hσ⟩ := h.data.exists_semilinear tt (h.T_le_normalizer_L htT)
  obtain ⟨u₁, u₂, hu₁, hu₂, hdet⟩ := h.exists_basis_fix htT ht
  obtain ⟨θ, hθ⟩ := h.exists_ne_of_fieldAut htT ht hσ
  have hfix : Nat.card {w : Fin 2 → h.data.K // h.data.conj tt w = w} = 2 ^ n := by
    rw [← Nat.card_congr (h.data.fixedEquiv tt)]
    exact h.card_fix_of_fieldAut htT ht
  have h1 := card_fixed_le_fix_mul_self (h.data.conj tt) σ hσ
  have h2 := card_fixed_mul_self_le σ hθ
  rw [hfix] at h1
  rw [h.data.card] at h2
  have hc : Nat.card ↥(stabFixField σ) = Nat.card {c : h.data.K // σ c = c} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun _ => mem_stabFixField)
  refine ⟨σ, u₁, u₂, hσ, hu₁, hu₂, hdet, ?_⟩
  rw [hc]
  exact le_antisymm h2 h1

theorem four_le_card_fixField (h : Hyp611Nat G T M L V n) {σ : h.data.K ≃+* h.data.K}
    (hc : Nat.card ↥(stabFixField σ) * Nat.card ↥(stabFixField σ) = 2 ^ n) (hn4 : 4 ≤ n) :
    4 ≤ Nat.card ↥(stabFixField σ) := by
  by_contra hlt
  push Not at hlt
  have h16 : 16 ≤ 2 ^ n :=
    calc 16 = 2 ^ 4 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn4
  have : Nat.card ↥(stabFixField σ) * Nat.card ↥(stabFixField σ) ≤ 3 * 3 :=
    Nat.mul_le_mul (by omega) (by omega)
  omega

theorem map_lOne_fix_eq (h : Hyp611Nat G T M L V n) {t : G} (htT : t ∈ T)
    (ht : IsInvolutoryFieldAut L t) (hn4 : 4 ≤ n) :
    ((lOne L (V ⊓ Subgroup.centralizer ({t} : Set G))).subgroupOf L).map h.data.rho =
      stabSub (h.data.conj ⟨t, h.toHyp611.T_le_normalizer htT⟩) := by
  classical
  have : CharP h.data.K 2 := charP_two_of_two_dvd h.two_dvd_card_K
  set U := V ⊓ Subgroup.centralizer ({t} : Set G) with hU
  set tt : Subgroup.normalizer (V : Set G) := ⟨t, h.toHyp611.T_le_normalizer htT⟩ with htt
  obtain ⟨σ, u₁, u₂, hσ, hu₁, hu₂, hdet, hc⟩ := h.exists_fieldAut_data htT ht
  have h4 := four_le_card_fixField h hc hn4
  apply le_antisymm
  · rintro _ ⟨ℓ, hℓ, rfl⟩
    have hℓU : (ℓ : G) ∈ Subgroup.normalizer (U : Set G) :=
      ((oTwoUpper_le _).trans inf_le_right) (Subgroup.mem_subgroupOf.mp hℓ)
    have hfix : ∀ {w}, h.data.conj tt w = w →
        h.data.conj tt (((h.data.rho ℓ : Matrix.SpecialLinearGroup (Fin 2) h.data.K) :
          Matrix (Fin 2) (Fin 2) h.data.K).mulVec w) =
        ((h.data.rho ℓ : Matrix.SpecialLinearGroup (Fin 2) h.data.K) :
          Matrix (Fin 2) (Fin 2) h.data.K).mulVec w := by
      intro w hw
      rw [← h.data.conj_eq_rho, ← h.mem_addSub_fix_iff htT]
      exact h.conj_mem_addSub _ hℓU ((h.mem_addSub_fix_iff htT w).mpr hw)
    exact mem_stabSub_of_basis hσ hu₁ hu₂ hdet (hfix hu₁) (hfix hu₂)
  · refine (stabSub_le_oTwoUpper hσ hu₁ hu₂ hdet h4).trans ((Subgroup.closure_le _).mpr ?_)
    rintro B ⟨hB, hBo⟩
    obtain ⟨ℓ, hℓ, hρℓ⟩ := h.exists_mem_lOne_of_comm htT B (mem_stabSub.mp hB) hBo
      (pow_orderOf_eq_one B)
    exact ⟨ℓ, Subgroup.mem_subgroupOf.mpr hℓ, hρℓ⟩

theorem isSimpleGroup_stabSub_fix (h : Hyp611Nat G T M L V n) {t : G} (htT : t ∈ T)
    (ht : IsInvolutoryFieldAut L t) (hn4 : 4 ≤ n) :
    IsSimpleGroup ↥(stabSub (h.data.conj ⟨t, h.toHyp611.T_le_normalizer htT⟩)) := by
  have : CharP h.data.K 2 := charP_two_of_two_dvd h.two_dvd_card_K
  obtain ⟨σ, u₁, u₂, hσ, hu₁, hu₂, hdet, hc⟩ := h.exists_fieldAut_data htT ht
  exact isSimpleGroup_stabSub hσ hu₁ hu₂ hdet (four_le_card_fixField h hc hn4)

theorem exists_not_comm_stabSub_fix (h : Hyp611Nat G T M L V n) {t : G} (htT : t ∈ T)
    (ht : IsInvolutoryFieldAut L t) :
    ∃ B ∈ stabSub (h.data.conj ⟨t, h.toHyp611.T_le_normalizer htT⟩),
      ∃ B' ∈ stabSub (h.data.conj ⟨t, h.toHyp611.T_le_normalizer htT⟩), B * B' ≠ B' * B := by
  have : CharP h.data.K 2 := charP_two_of_two_dvd h.two_dvd_card_K
  obtain ⟨σ, u₁, u₂, hσ, hu₁, hu₂, hdet, -⟩ := h.exists_fieldAut_data htT ht
  have hmem : ∀ M, slFormHom σ u₁ u₂ hdet M ∈
      stabSub (h.data.conj ⟨t, h.toHyp611.T_le_normalizer htT⟩) := fun M => by
    rw [← range_slFormHom hσ hu₁ hu₂ hdet]
    exact ⟨M, rfl⟩
  refine ⟨_, hmem (SL2Model.e12 1), _, hmem (SL2Model.e21 1), fun heq => ?_⟩
  rw [← map_mul, ← map_mul] at heq
  have h1 := congrArg (fun X : Matrix.SpecialLinearGroup (Fin 2) ↥(stabFixField σ) =>
    (X : Matrix (Fin 2) (Fin 2) ↥(stabFixField σ)) 1 1) (slFormHom_injective hdet heq)
  simp only [Matrix.SpecialLinearGroup.coe_mul] at h1
  simp [SL2Model.e12, SL2Model.e21, Matrix.mul_apply, Fin.sum_univ_two,
    CharTwo.add_self_eq_zero] at h1

theorem mem_pCoreOf_of_rho_eq_one (h : Hyp611Nat G T M L V n) {ℓ : ↥L}
    (hℓ : h.data.rho ℓ = 1) : (ℓ : G) ∈ pCoreOf 2 L :=
  h.toHyp5_0_1.inf_centralizer_le h.data.le_normalizer h.module.2.2
    ⟨ℓ.2, (h.data.mem_ker_rho_iff ℓ).mp hℓ⟩

theorem exists_pow_eq_one_of_rho_eq_one (h : Hyp611Nat G T M L V n) {ℓ : ↥L}
    (hℓ : h.data.rho ℓ = 1) : ∃ k : ℕ, (ℓ : G) ^ 2 ^ k = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := (pCoreOf_isPGroup 2 L) ⟨ℓ, h.mem_pCoreOf_of_rho_eq_one hℓ⟩
  exact ⟨k, by simpa using congrArg Subtype.val hk⟩

theorem mem_centralizer_V_of_U (h : Hyp611Nat G T M L V n) {t : G} (htT : t ∈ T)
    (ht : IsInvolutoryFieldAut L t) {ℓ : G} (hℓL : ℓ ∈ L)
    (hℓU : ℓ ∈ Subgroup.centralizer ((V ⊓ Subgroup.centralizer ({t} : Set G) : Subgroup G) :
      Set G)) : ℓ ∈ Subgroup.centralizer (V : Set G) := by
  obtain ⟨u₁, u₂, hu₁, hu₂, hdet⟩ := h.exists_basis_fix htT ht
  have hℓN : ℓ ∈ Subgroup.normalizer (V : Set G) := h.data.le_normalizer hℓL
  have h1 := h.conj_eq_of_fix htT hℓN hℓU hu₁
  have h2 := h.conj_eq_of_fix htT hℓN hℓU hu₂
  obtain ⟨B, hB⟩ := h.data.exists_matrix_of_mem ⟨ℓ, hℓN⟩ hℓL
  apply h.data.mem_centralizer_of_conj_eq ⟨ℓ, hℓN⟩
  intro w
  rw [hB] at h1 h2 ⊢
  rw [eq_one_of_basis hdet h1 h2, Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]

theorem lOne_fix_perfect (h : Hyp611Nat G T M L V n) {t : G} (htT : t ∈ T)
    (ht : IsInvolutoryFieldAut L t) (hn4 : 4 ≤ n) :
    ⁅lOne L (V ⊓ Subgroup.centralizer ({t} : Set G)),
      lOne L (V ⊓ Subgroup.centralizer ({t} : Set G))⁆ =
      lOne L (V ⊓ Subgroup.centralizer ({t} : Set G)) := by
  set LU := lOne L (V ⊓ Subgroup.centralizer ({t} : Set G)) with hLU
  have hLUL : LU ≤ L := (oTwoUpper_le _).trans inf_le_left
  have hS := h.map_lOne_fix_eq htT ht hn4
  have hsimp := h.isSimpleGroup_stabSub_fix htT ht hn4
  obtain ⟨B, hB, B', hB', hBB'⟩ := h.exists_not_comm_stabSub_fix htT ht
  have hSS := commutator_self_eq_of_simple hsimp hB hB' hBB'
  refine le_antisymm (A3.commutator_self_le LU) ?_
  refine (lOne_eq_oTwoUpper L _).le.trans (oTwoUpper_le_of_map_eq h.data.rho
    (fun x hx => h.exists_pow_eq_one_of_rho_eq_one hx) ?_ hLUL ?_)
  · exact A3.subnormal_of_normal (A3.commutator_self_le LU)
      ((Subgroup.normal_subgroupOf_iff_le_normalizer (A3.commutator_self_le LU)).mpr
        (le_normalizer_commutator_self LU))
  · rw [hS, ← hSS]
    rw [Subgroup.commutator_le]
    intro s₁ hs₁ s₂ hs₂
    rw [← hS] at hs₁ hs₂
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hs₁
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hs₂
    refine Subgroup.mem_map.mpr ⟨⁅a, b⁆, ?_, map_commutatorElement _ _ _⟩
    rw [Subgroup.mem_subgroupOf]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_subgroupOf.mp ha)
      (Subgroup.mem_subgroupOf.mp hb)

theorem le_normalizer_lOne_fix (h : Hyp611Nat G T M L V n) {t : G} :
    T ⊓ Subgroup.normalizer ((V ⊓ Subgroup.centralizer ({t} : Set G) : Subgroup G) : Set G) ≤
      Subgroup.normalizer ((lOne L (V ⊓ Subgroup.centralizer ({t} : Set G)) : Subgroup G) :
        Set G) := by
  intro x hx
  refine normalizer_le_normalizer_oTwoUpper _ ?_
  exact Subgroup.inf_normalizer_le_normalizer_inf
    ⟨h.T_le_normalizer_L hx.1, Subgroup.le_normalizer hx.2⟩

theorem lOne_fix_ne_bot (h : Hyp611Nat G T M L V n) {t : G} (htT : t ∈ T)
    (ht : IsInvolutoryFieldAut L t) (hn4 : 4 ≤ n) :
    lOne L (V ⊓ Subgroup.centralizer ({t} : Set G)) ≠ ⊥ := by
  intro h0
  obtain ⟨B, hB, B', hB', hBB'⟩ := h.exists_not_comm_stabSub_fix htT ht
  rw [← h.map_lOne_fix_eq htT ht hn4, h0] at hB
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hB
  have hx1 : x = 1 := by
    have := Subgroup.mem_subgroupOf.mp hx
    rw [Subgroup.mem_bot] at this
    exact Subtype.ext this
  apply hBB'
  rw [hx1, map_one, one_mul, mul_one]

theorem lOne_fix_mem_cComp (h : Hyp611Nat G T M L V n) {t : G} (htT : t ∈ T)
    (ht : IsInvolutoryFieldAut L t) (hn4 : 4 ≤ n) :
    lOne L (V ⊓ Subgroup.centralizer ({t} : Set G)) ∈
      cComp (lOne L (V ⊓ Subgroup.centralizer ({t} : Set G)) ⊔
        (T ⊓ Subgroup.normalizer ((V ⊓ Subgroup.centralizer ({t} : Set G) : Subgroup G) :
          Set G))) := by
  set LU := lOne L (V ⊓ Subgroup.centralizer ({t} : Set G)) with hLU
  set TU := T ⊓ Subgroup.normalizer ((V ⊓ Subgroup.centralizer ({t} : Set G) : Subgroup G) :
    Set G) with hTU
  have hLUL : LU ≤ L := (oTwoUpper_le _).trans inf_le_left
  have hS := h.map_lOne_fix_eq htT ht hn4
  have hsimp := h.isSimpleGroup_stabSub_fix htT ht hn4
  have hnormLU : LU ⊔ TU ≤ Subgroup.normalizer (LU : Set G) :=
    sup_le Subgroup.le_normalizer h.le_normalizer_lOne_fix
  refine ⟨h.lOne_fix_ne_bot htT ht hn4, h.lOne_fix_perfect htT ht hn4,
    A3.subnormal_of_normal le_sup_left
      ((Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr hnormLU),
    fun K hKlt hK1 hKp hKsub => ?_⟩
  have hKLU : IsSubnormal K LU := A3.subnormal_of_le_of_le hKsub hKlt.le le_sup_left
  have hρK : IsSubnormal ((K.subgroupOf L).map h.data.rho) ((LU.subgroupOf L).map h.data.rho) := by
    have h1 := A3.subnormal_comap L.subtype hKLU
    rw [Subgroup.comap_subtype, Subgroup.comap_subtype] at h1
    exact A3.subnormal_map _ h1
  rw [hS] at hρK
  rcases eq_bot_or_eq_of_subnormal_simple hsimp hρK with h0 | h0
  ·
    apply hK1
    refine eq_bot_of_isPGroup_of_perfect ?_ hKp
    rintro ⟨k, hk⟩
    have hkL : k ∈ L := hLUL (hKlt.le hk)
    have hρk : h.data.rho ⟨k, hkL⟩ = 1 := by
      have : h.data.rho ⟨k, hkL⟩ ∈ (K.subgroupOf L).map h.data.rho :=
        Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hk)
      rw [h0, Subgroup.mem_bot] at this
      exact this
    obtain ⟨j, hj⟩ := h.exists_pow_eq_one_of_rho_eq_one hρk
    exact ⟨j, Subtype.ext (by simpa using hj)⟩
  ·
    apply hKlt.not_ge
    refine (lOne_eq_oTwoUpper L _).le.trans (oTwoUpper_le_of_map_eq h.data.rho
      (fun x hx => h.exists_pow_eq_one_of_rho_eq_one hx) hKLU hLUL ?_)
    rw [hS, h0]

theorem pCoreOf_lOne_fix_le (h : Hyp611Nat G T M L V n) {t : G} (htT : t ∈ T)
    (ht : IsInvolutoryFieldAut L t) (hn4 : 4 ≤ n) :
    pCoreOf 2 (lOne L (V ⊓ Subgroup.centralizer ({t} : Set G))) ≤
      Subgroup.centralizer (V : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set LU := lOne L (V ⊓ Subgroup.centralizer ({t} : Set G)) with hLU
  have hLUL : LU ≤ L := (oTwoUpper_le _).trans inf_le_left
  have hS := h.map_lOne_fix_eq htT ht hn4
  have hsimp := h.isSimpleGroup_stabSub_fix htT ht hn4
  obtain ⟨B, hB, B', hB', hBB'⟩ := h.exists_not_comm_stabSub_fix htT ht
  have hSS := commutator_self_eq_of_simple hsimp hB hB' hBB'
  set P := pCoreOf 2 LU with hP
  have hPLU : P ≤ LU := pCoreOf_le 2 LU
  have hρP : IsSubnormal ((P.subgroupOf L).map h.data.rho) ((LU.subgroupOf L).map h.data.rho) := by
    have h1 := A3.subnormal_comap L.subtype (A3.subnormal_of_normal hPLU
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hPLU).mpr (le_normalizer_pCoreOf 2 LU)))
    rw [Subgroup.comap_subtype, Subgroup.comap_subtype] at h1
    exact A3.subnormal_map _ h1
  rw [hS] at hρP
  rcases eq_bot_or_eq_of_subnormal_simple hsimp hρP with h0 | h0
  · intro x hx
    have hxL : x ∈ L := hLUL (hPLU hx)
    have hρx : h.data.rho ⟨x, hxL⟩ = 1 := by
      have : h.data.rho ⟨x, hxL⟩ ∈ (P.subgroupOf L).map h.data.rho :=
        Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hx)
      rw [h0, Subgroup.mem_bot] at this
      exact this
    exact (h.data.mem_ker_rho_iff ⟨x, hxL⟩).mp hρx
  ·
    exfalso
    have hP2 : IsPGroup 2 ↥(stabSub (h.data.conj ⟨t, h.toHyp611.T_le_normalizer htT⟩)) := by
      rw [← h0]
      exact ((pCoreOf_isPGroup 2 LU).of_equiv (Subgroup.subgroupOfEquivOfLe
        (hPLU.trans hLUL)).symm).map h.data.rho
    have hbot := eq_bot_of_isPGroup_of_perfect hP2 hSS
    have hB1 : B = 1 := by
      have := hB
      rw [hbot, Subgroup.mem_bot] at this
      exact this
    apply hBB'
    rw [hB1, one_mul, mul_one]

theorem false_of_lOne_fix_comm_mod (h : Hyp611Nat G T M L V n) {t : G} (htT : t ∈ T)
    (ht : IsInvolutoryFieldAut L t) (hn4 : 4 ≤ n)
    (hc : ∀ a ∈ lOne L (V ⊓ Subgroup.centralizer ({t} : Set G)),
      ∀ b ∈ lOne L (V ⊓ Subgroup.centralizer ({t} : Set G)),
        a * b * a⁻¹ * b⁻¹ ∈ Subgroup.centralizer
          ((V ⊓ Subgroup.centralizer ({t} : Set G) : Subgroup G) : Set G)) : False := by
  set LU := lOne L (V ⊓ Subgroup.centralizer ({t} : Set G)) with hLU
  have hLUL : LU ≤ L := (oTwoUpper_le _).trans inf_le_left
  have hS := h.map_lOne_fix_eq htT ht hn4
  obtain ⟨B, hB, B', hB', hBB'⟩ := h.exists_not_comm_stabSub_fix htT ht
  rw [← hS] at hB hB'
  obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hB
  obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hB'
  have haLU := Subgroup.mem_subgroupOf.mp ha
  have hbLU := Subgroup.mem_subgroupOf.mp hb
  have hcV := h.mem_centralizer_V_of_U htT ht
    (L.mul_mem (L.mul_mem (L.mul_mem a.2 b.2) (L.inv_mem a.2)) (L.inv_mem b.2))
    (hc a haLU b hbLU)
  have hρ : h.data.rho (a * b * a⁻¹ * b⁻¹) = 1 :=
    (h.data.mem_ker_rho_iff (a * b * a⁻¹ * b⁻¹)).mpr (by simpa using hcV)
  apply hBB'
  rw [map_mul, map_mul, map_mul, map_inv, map_inv] at hρ
  calc h.data.rho a * h.data.rho b =
      (h.data.rho a * h.data.rho b * (h.data.rho a)⁻¹ * (h.data.rho b)⁻¹) *
        (h.data.rho b * h.data.rho a) := by group
    _ = h.data.rho b * h.data.rho a := by rw [hρ, one_mul]

end Hyp611Nat

end CFSG.Quasithin.H13
