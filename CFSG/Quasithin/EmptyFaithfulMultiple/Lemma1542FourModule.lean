module

public import CFSG.Quasithin.Background.B6Offenders
public import CFSG.Quasithin.Background.A4Defs

public section

namespace CFSG.Quasithin.EmptyFaithfulMultiple

open CFSG.Open CFSG.Quasithin CFSG.LieType.BorelTits
open scoped commutatorElement

section Kq

variable {V : Type*} [CommGroup V] [Finite V]

theorem kq_le_kq_of_le {X Y : Subgroup (MulAut V)} (h : X ≤ Y) (k : ℕ) : kq Y k ≤ kq X k := by
  unfold kq
  refine Finset.min_mono ?_
  intro s hs
  rw [Set.Finite.mem_toFinset] at hs ⊢
  obtain ⟨A, hA, hAk, rfl⟩ := hs
  exact ⟨A, ⟨hA.1.trans h, hA.2.1, hA.2.2⟩, hAk, rfl⟩

end Kq

section FFJ

variable {V : Type*} [CommGroup V]

theorem ffJ_ffJ (X : Subgroup (MulAut V)) : ffJ (ffJ X) = ffJ X :=
  le_antisymm (iSup₂_le fun _ hA => B6.le_ffJ ⟨hA.1.trans (B6.ffJ_le X), hA.2⟩)
    (iSup₂_le fun _ hA => B6.le_ffJ ⟨B6.le_ffJ hA, hA.2⟩)

theorem ffJ_ne_bot [Finite V] {X : Subgroup (MulAut V)} (h : IsFFModule X) : ffJ X ≠ ⊥ := by
  obtain ⟨A, hA⟩ := B6.exists_isFFStarOffender h
  exact fun hbot => hA.2.1 (le_bot_iff.mp (hbot ▸ B6.le_ffJ hA))

end FFJ

section PCore

variable {Γ : Type*} [Group Γ]

theorem pCore_eq_bot_of_le_normalizer [Finite Γ] {Y J : Subgroup Γ} (hJY : J ≤ Y)
    (hn : Y ≤ Subgroup.normalizer (J : Set Γ)) (hY : pCore 2 Y = ⊥) : pCore 2 J = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : pCoreOf 2 J ≤ pCoreOf 2 Y :=
    le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 J).trans hJY)
      (hn.trans (normalizer_le_normalizer_pCoreOf 2 J)) (pCoreOf_isPGroup 2 J)
  have h2 : pCoreOf 2 Y = ⊥ := by
    unfold pCoreOf
    rw [hY, Subgroup.map_bot]
  have h3 : pCoreOf 2 J = ⊥ := le_bot_iff.mp (h2 ▸ h1)
  exact (Subgroup.map_eq_bot_iff_of_injective _ J.subtype_injective).mp h3

theorem pCore_map_eq_bot {Γ' : Type*} [Group Γ'] {Y : Subgroup Γ} (f : Γ →* Γ')
    (hf : Function.Injective f) (hY : pCore 2 Y = ⊥) : pCore 2 (Y.map f) = ⊥ := by
  rw [← map_pCore_mulEquiv 2 (Y.equivMapOfInjective f hf), hY, Subgroup.map_bot]

end PCore

section Internal

variable {G : Type*} [Group G]

private theorem coe_conjAct_apply (V : Subgroup G) (g : Subgroup.normalizer (V : Set G)) (v : V) :
    ((conjAct V g v : V) : G) = g * v * (g : G)⁻¹ :=
  CFSG.Quasithin.AutOn.coe_conjAct_apply V g v

theorem conjAct_eq_one_iff {V : Subgroup G} (g : Subgroup.normalizer (V : Set G)) :
    conjAct V g = 1 ↔ (g : G) ∈ Subgroup.centralizer (V : Set G) :=
  A4.normalizerMonoidHom_eq_one_iff

theorem range_conjAct_comp_inclusion {H V : Subgroup G}
    (hH : H ≤ Subgroup.normalizer (V : Set G)) :
    ((conjAct V).comp (Subgroup.inclusion hH)).range = autOn H V := by
  unfold autOn
  rw [MonoidHom.range_comp, Subgroup.inclusion_range]

theorem le_normalizer_map_comap {H : Subgroup G} {Γ : Type*} [Group Γ] (f : H →* Γ)
    {K : Subgroup Γ} (hK : f.range ≤ Subgroup.normalizer (K : Set Γ)) :
    H ≤ Subgroup.normalizer (((K.comap f).map H.subtype : Subgroup G) : Set G) := by
  have key : ∀ m : H, ∀ x ∈ (K.comap f).map H.subtype, (m : G) * x * (m : G)⁻¹ ∈
      (K.comap f).map H.subtype := by
    rintro m _ ⟨n, hn, rfl⟩
    refine ⟨m * n * m⁻¹, ?_, rfl⟩
    show f (m * n * m⁻¹) ∈ K
    rw [map_mul, map_mul, map_inv]
    exact (Subgroup.mem_normalizer_iff.mp (hK ⟨m, rfl⟩) (f n)).mp hn
  intro m hm
  exact B6.mem_normalizer_of_forall_mem (key ⟨m, hm⟩) (by simpa using key ⟨m, hm⟩⁻¹)

theorem pCore_autOn_eq_bot [Finite G] {H V : Subgroup G} (hV : IsTwoReducedIn H V) :
    pCore 2 (autOn H V) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set κ := (conjAct V).comp (Subgroup.inclusion hV.2.1)
  have hrange : κ.range = autOn H V := range_conjAct_comp_inclusion hV.2.1
  set P := pCoreOf 2 (autOn H V)
  have hPX : P ≤ autOn H V := pCoreOf_le 2 _
  have hPn : κ.range ≤ Subgroup.normalizer (P : Set (MulAut V)) :=
    hrange ▸ le_normalizer_pCoreOf 2 _
  have hP2 : IsPGroup 2 P := pCoreOf_isPGroup 2 _
  set Q : Subgroup G := (P.comap κ).map H.subtype
  have hQC : Q ≤ Subgroup.centralizer (V : Set G) := by
    refine hV.2.2.2 Q (Subgroup.map_subtype_le _) (le_normalizer_map_comap κ hPn) ?_
    rintro _ ⟨n, hn, rfl⟩
    obtain ⟨k, hk⟩ := hP2 ⟨κ n, hn⟩
    refine ⟨k, ?_⟩
    have h1 : κ (n ^ 2 ^ k) = 1 := by
      rw [map_pow]
      exact congrArg Subtype.val hk
    exact (conjAct_eq_one_iff _).mp h1
  have hPbot : P = ⊥ := by
    refine eq_bot_iff.mpr fun x hx => ?_
    obtain ⟨n, rfl⟩ : x ∈ κ.range := hrange ▸ hPX hx
    exact Subgroup.mem_bot.mpr ((conjAct_eq_one_iff _).mpr (hQC ⟨n, hx, rfl⟩))
  exact (Subgroup.map_eq_bot_iff_of_injective _ (autOn H V).subtype_injective).mp hPbot

theorem coe_mem_commutator_of_mem_commSub {A V U : Subgroup G} (hV : IsElemAbelian 2 V)
    {W : Subgroup V} (hWU : ∀ w ∈ W, (w : G) ∈ U) {c : V}
    (hc : c ∈ @commSub V (commGroupOfElemAbelian hV) W (autOn A V)) :
    (c : G) ∈ ⁅U, A⁆ := by
  induction hc using Subgroup.closure_induction with
  | mem c hc =>
    obtain ⟨x, hx, w, hw, rfl⟩ := hc
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    rw [Subgroup.mem_subgroupOf] at hy
    have h1 : ((conjAct V y w * w⁻¹ : V) : G) = ⁅(y : G), (w : G)⁆ := by
      show ((conjAct V y w : V) : G) * (w : G)⁻¹ = _
      rw [coe_conjAct_apply, commutatorElement_def]
    rw [h1, Subgroup.commutator_comm]
    exact Subgroup.commutator_mem_commutator hy (hWU w hw)
  | one => exact Subgroup.one_mem _
  | mul a b _ _ ha hb => exact Subgroup.mul_mem _ ha hb
  | inv a _ ha => exact Subgroup.inv_mem _ ha

theorem commSeries_autOn_three_eq_bot {A V : Subgroup G} (hV : IsElemAbelian 2 V)
    (h : ⁅⁅⁅V, A⁆, A⁆, A⁆ = ⊥) :
    @commSeries V (commGroupOfElemAbelian hV) (autOn A V) 3 = ⊥ := by
  let _ := commGroupOfElemAbelian hV
  have h0 : ∀ w ∈ commSeries (autOn A V) 0, (w : G) ∈ V := fun w _ => w.2
  have h1 : ∀ w ∈ commSeries (autOn A V) 1, (w : G) ∈ ⁅V, A⁆ :=
    fun _ hw => coe_mem_commutator_of_mem_commSub hV h0 hw
  have h2 : ∀ w ∈ commSeries (autOn A V) 2, (w : G) ∈ ⁅⁅V, A⁆, A⁆ :=
    fun _ hw => coe_mem_commutator_of_mem_commSub hV h1 hw
  have h3 : ∀ w ∈ commSeries (autOn A V) 3, (w : G) ∈ ⁅⁅⁅V, A⁆, A⁆, A⁆ :=
    fun _ hw => coe_mem_commutator_of_mem_commSub hV h2 hw
  refine eq_bot_iff.mpr fun w hw => ?_
  have hw3 := h3 w hw
  rw [h, Subgroup.mem_bot] at hw3
  exact Subgroup.mem_bot.mpr (Subtype.ext hw3)

theorem qhatOf_autOn_le_two [Finite G] {A H V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hAH : A ≤ H) (hAN : A ≤ Subgroup.normalizer (V : Set G)) (hA : IsElemAbelian 2 A)
    (hcub : ⁅⁅⁅V, A⁆, A⁆, A⁆ = ⊥) (hnc : ¬ A ≤ Subgroup.centralizer (V : Set G))
    (hidx : (V ⊓ Subgroup.centralizer (A : Set G)).relIndex V ≤
      ((A ⊓ Subgroup.centralizer (V : Set G)).relIndex A) ^ 2) :
    @qhatOf V (commGroupOfElemAbelian hV) _ (autOn H V) ≤ 2 := by
  let _ := commGroupOfElemAbelian hV
  have hne : autOn A V ≠ ⊥ := autOn_ne_bot_of_not_le_centralizer hAN hnc
  have hel : IsElemAbelian2 (autOn A V) := isElemAbelian2_autOn hV hA hAN
  have hcard : Nat.card (autOn A V) = (A ⊓ Subgroup.centralizer (V : Set G)).relIndex A :=
    card_autOn_eq_relIndex hAN
  have hfix : Nat.card (fixV (autOn A V)) =
      Nat.card (V ⊓ Subgroup.centralizer (A : Set G) : Subgroup G) := card_fixV_autOn_eq hV hAN
  have hindex : (fixV (autOn A V)).index = (V ⊓ Subgroup.centralizer (A : Set G)).relIndex V := by
    have e1 := Subgroup.card_mul_index (fixV (autOn A V))
    have e2 := Subgroup.relIndex_mul_card (V ⊓ Subgroup.centralizer (A : Set G)) V
    rw [inf_eq_left.mpr inf_le_left] at e2
    rw [hfix] at e1
    have hpos : 0 < Nat.card (V ⊓ Subgroup.centralizer (A : Set G) : Subgroup G) := Nat.card_pos
    have e3 : Nat.card (V ⊓ Subgroup.centralizer (A : Set G) : Subgroup G) *
        (fixV (autOn A V)).index = Nat.card (V ⊓ Subgroup.centralizer (A : Set G) : Subgroup G) *
          (V ⊓ Subgroup.centralizer (A : Set G)).relIndex V := by
      rw [e1, mul_comm, e2]
    exact Nat.eq_of_mul_eq_mul_left hpos e3
  have hb : Nat.card (autOn A V) = 2 ^ rk (autOn A V) :=
    card_eq_two_pow_of_isPGroup hel.isPGroup
  have hrk : 0 < rk (autOn A V) := hel.rk_pos hne
  have h2a : 2 ^ rkIdx (fixV (autOn A V)) ≤ 2 ^ (2 * rk (autOn A V)) := by
    calc 2 ^ rkIdx (fixV (autOn A V)) ≤ (fixV (autOn A V)).index :=
          Nat.le_of_dvd (Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite))
            pow_padicValNat_dvd
      _ = (V ⊓ Subgroup.centralizer (A : Set G)).relIndex V := hindex
      _ ≤ ((A ⊓ Subgroup.centralizer (V : Set G)).relIndex A) ^ 2 := hidx
      _ = 2 ^ (2 * rk (autOn A V)) := by rw [← hcard, hb, ← pow_mul, mul_comm]
  have hle : rkIdx (fixV (autOn A V)) ≤ 2 * rk (autOn A V) :=
    (Nat.pow_le_pow_iff_right (by norm_num)).mp h2a
  rw [show (2 : WithTop ℚ) = ((2 : ℚ) : WithTop ℚ) from rfl]
  refine kq_le_iff.mpr ⟨autOn A V, ⟨autOn_le_autOn V hAH, hne, hel⟩,
    commSeries_autOn_three_eq_bot hV hcub, ?_⟩
  unfold rAV
  have hrkq : (0 : ℚ) < rk (autOn A V) := by exact_mod_cast hrk
  rw [div_le_iff₀ hrkq]
  exact_mod_cast hle

end Internal

end CFSG.Quasithin.EmptyFaithfulMultiple
