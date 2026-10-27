module

public import CFSG.Quasithin.H13.NQBlockControlledThompson
public import CFSG.Quasithin.H13.NQBlockTensorGL3
public import CFSG.Quasithin.Background.F1Models
public import CFSG.Quasithin.SteinbergBKNearMaximalElementaryRank
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.H13.NQBlock

open Subgroup CFSG.Open
open CFSG.ProperTwoGeneratedCore.BinaryThreeSpace CFSG.QuasithinUnique.Setup.Family
open scoped commutatorElement Matrix

@[expose] def SimpleSourceTensorAction : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L M : Subgroup G), QTNQ T L M →
    ∀ R : Subgroup G, (R : Set G) = nqOriginalCentralizer T L →
    ∀ H : Subgroup G, quasithinIsMaxTwoLocal H → nqOriginalK T L ⊔ T ≤ H → H ≠ M →
    ∀ Y : Subgroup G, Y ≤ H → (Y.subgroupOf H).Normal → ¬ Y ≤ M →
      ⁅nqOriginalK T L, Y⁆ ≤ pCoreOf 2 Y →
      (Nonempty (Y ⧸ CFSG.pCore 2 Y ≃* alternatingGroup (Fin 5)) ∨
        Nonempty (Y ⧸ CFSG.pCore 2 Y ≃* GL (Fin 3) (ZMod 2))) →
    ∀ j : ℕ, j ≤ 1 → 3 ≤ CFSG.pRank 2 R → normalizer (nqHigherThompson R j : Set G) ≤ M →
    ∀ A ∈ CFSG.higherElemThompsonFamily R j,
      ⁅⁅nqSourceModule Y R, nqOriginalK T L⁆, ⁅Y, A.map R.subtype⁆⁆ ≠ ⊥ →
      j = 1 ∧ (Y ⊔ R) ⊓ centralizer (nqSourceModule Y R : Set G) ≤ R ∧
      ∃ ρ : ↥(Y ⊔ R) →* GL (Fin 3) (ZMod 2),
        (∀ s, ρ s = 1 ↔ (s : G) ∈ centralizer (nqSourceModule Y R : Set G)) ∧
        (Y.subgroupOf (Y ⊔ R)).map ρ = ⊤ ∧ (R.subgroupOf (Y ⊔ R)).map ρ = sylowT ∧
        ((A.map R.subtype).subgroupOf (Y ⊔ R)).map ρ = axisT ∧
        ∃ θ : ↥⁅nqSourceModule Y R, Y⁆ ≃* Multiplicative (Matrix (Fin 3) (Fin 3) (ZMod 2)),
          ∀ (s : ↥(Y ⊔ R)) (u : ↥⁅nqSourceModule Y R, Y⁆)
            (h : (s : G) * u * (s : G)⁻¹ ∈ ⁅nqSourceModule Y R, Y⁆),
            Multiplicative.toAdd (θ ⟨_, h⟩) =
              (ρ s : Matrix (Fin 3) (Fin 3) (ZMod 2)) * Multiplicative.toAdd (θ u)

theorem le_axisT_of_count {B : Subgroup GL32} (hle : B ≤ sylowT) (hB : B ≠ ⊥)
    (hsq : ∀ a ∈ B, a ^ 2 = 1) (hcomm : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a) {r : ℕ}
    (hr : r * Nat.card (fixVec3 B) ^ 3 = 512) (hrB : r ≤ 2 * Nat.card B) : B ≤ axisT := by
  rcases GL3_elementary_abelian_fixed_codimensions hB hcomm hsq with
    ⟨h2, h4, -, -⟩ | ⟨h4, ⟨h2', -⟩ | ⟨h4', -⟩, -⟩
  · rw [h4] at hr
    omega
  · rw [h2'] at hr
    omega
  · exact le_axisT hle hsq hcomm h4 h4'

variable {G : Type} [Group G] [Finite G]

theorem relIndex_ne_zero_of_finite (H K : Subgroup G) : H.relIndex K ≠ 0 := by
  intro h0
  have h := Subgroup.relIndex_mul_card H K
  rw [h0, zero_mul] at h
  exact (Nat.card_pos (α := ↥K)).ne h

theorem simpleSourceTensorEquality_of
    (hTA : SimpleSourceTensorAction) : SimpleSourceTensorEquality := by
  intro G _ _ T L M h R hR H hH hKTH hHM Y hYH hYn hYM hKY hsimp j hj hm hJM A hA
  classical
  by_contra hne
  have hTA' := hTA G T L M h R hR H hH hKTH hHM Y hYH hYn hYM hKY hsimp j hj hm hJM A hA hne
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := nqOriginalK T L with hKdef
  set W := nqSourceModule Y R with hWdef
  set S := Y ⊔ R with hSdef
  set U := ⁅W, Y⁆ with hUdef
  set A' := A.map R.subtype with hA'def
  obtain ⟨rfl, hFR, ρ, hρker, hρY, hρR, hρA, θ, hθ⟩ := hTA'
  obtain ⟨hTK, -, -, htrans⟩ :=
    normal_original_K_overgroup_factors_have_core_containment_and_commutator_transport h hR
  obtain ⟨-, hOHR, htr⟩ := htrans H Y hKTH hYH hYn
  obtain ⟨-, -, -, -, -, hSyl⟩ := htr hKY
  obtain ⟨-, hRKT, -⟩ := original_radical_supplements_share_simple_residual_and_internal_module h hR
  have hTH : T ≤ H := le_sup_right.trans hKTH
  have hRT : R ≤ T := fun r hr => by
    rw [← SetLike.mem_coe, hR] at hr
    exact hr.1
  have hRH : R ≤ H := hRT.trans hTH
  have hSH : S ≤ H := sup_le hYH hRH
  have hHY : H ≤ normalizer (Y : Set G) := (normal_subgroupOf_iff_le_normalizer hYH).mp hYn
  have hKTR : K ⊔ T ≤ normalizer (R : Set G) := by
    rw [hRKT]
    exact CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _
  have hSyl' : QuasithinUnique.IsSylowTwoOf R S := CFSG.ABGLocalTools.isSylowOf_iff.mp hSyl
  have hT' : QuasithinUnique.IsSylowTwoOf T ⊤ := by
    refine ⟨le_top, h.sylow.1, ?_⟩
    change ¬ 2 ∣ T.relIndex ⊤
    rw [Subgroup.relIndex_top_right]
    exact h.sylow.2
  have hHc : QuasithinUnique.CharTwo H :=
    QuasithinUnique.charTwo_of_isTwoLocal_of_isSylowTwoOf_le h.qtke.2.1 hT' hH.1 hTH
  have hOHS : pCoreOf 2 H ≤ pCoreOf 2 S :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (hOHR.trans le_sup_right)
      (hSH.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H)
  have hchar : QuasithinUnique.CharTwo S := fun x hx =>
    hOHS (hHc ⟨hSH hx.1, centralizer_le hOHS hx.2⟩)
  have hWZ := nqSourceModule_le_omegaOneCenterOf_pCoreOf hSyl' hchar
  have hOR : pCoreOf 2 S ≤ R := QuasithinUnique.EscapingLocal.pCoreOf_le_of_isSylowTwoOf hSyl'
  have hWR : W ≤ R := hWZ.trans (((omegaOneCenterOf_le 2 _).trans inf_le_left).trans hOR)
  have hW2 : ∀ w ∈ W, w ^ 2 = 1 := fun w hw => pow_eq_one_of_mem_omegaOneCenterOf (hWZ hw)
  have hSW : S ≤ normalizer (W : Set G) := le_normalizer_nqSourceModule Y R
  have hTW : T ≤ normalizer (W : Set G) := fun t ht =>
    mem_normalizer_nqSourceModule (hHY (hTH ht)) (hKTR (le_sup_right (a := K) ht))
  have hUW : U ≤ W := by
    rw [hUdef, Subgroup.commutator_le]
    intro w hw y hy
    rw [commutatorElement_def, mul_assoc, mul_assoc]
    refine W.mul_mem hw ?_
    rw [← mul_assoc]
    exact (mem_normalizer_iff.mp (hSW (le_sup_left (a := Y) hy)) _).mp (W.inv_mem hw)
  have hUT : U ≤ T := (hUW.trans hWR).trans hRT
  have hTU : T ≤ normalizer (U : Set G) := fun t ht =>
    mem_normalizer_commutator (hTW ht) (hHY (hTH ht))
  have hSU : S ≤ normalizer (U : Set G) := fun s hs =>
    mem_normalizer_commutator (hSW hs) (sup_le le_normalizer (hRH.trans hHY) hs)
  set F := S ⊓ centralizer (W : Set G) with hFdef
  have hθconj : ∀ (s : ↥S) (u : ↥U),
      Multiplicative.toAdd (θ ⟨_, (mem_normalizer_iff.mp (hSU s.2) u).mp u.2⟩) =
        (ρ s : Matrix (Fin 3) (Fin 3) (ZMod 2)) * Multiplicative.toAdd (θ u) :=
    fun s u => hθ s u _
  have hρmem : ∀ (s : ↥S) (a : G) (ha : a ∈ A'),
      ρ s = ρ ⟨a, le_sup_right (a := Y) (map_subtype_le A ha)⟩ → (s : G) ∈ F ⊔ A' := by
    intro s a ha hsa
    have h1 : ρ (⟨a, le_sup_right (a := Y) (map_subtype_le A ha)⟩⁻¹ * s) = 1 := by
      rw [map_mul, map_inv, hsa, inv_mul_cancel]
    have h2 := (hρker _).mp h1
    have e : (s : G) = a * (a⁻¹ * s) := by group
    rw [e]
    exact mul_mem (mem_sup_right ha) (mem_sup_left ⟨S.mul_mem (S.inv_mem
      (le_sup_right (a := Y) (map_subtype_le A ha))) s.2, h2⟩)
  have hWel : CFSG.IsElementaryAbelian 2 ↥W := isElementaryAbelian_of_le_omegaOneCenterOf hWZ
  have : (W.subgroupOf R).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hWR).mpr (le_sup_right.trans hSW)
  have : CFSG.IsElementaryAbelian 2 ↥(W.subgroupOf R) := CFSG.IsElementaryAbelian.subgroupOf hWR
  have hcardM : Nat.card (Multiplicative (Matrix (Fin 3) (Fin 3) (ZMod 2))) = 512 := by
    change Nat.card (Fin 3 → Fin 3 → ZMod 2) = 512
    rw [Nat.card_fun, Nat.card_fun, Nat.card_zmod, Nat.card_fin]
    norm_num
  have hcardU : Nat.card ↥U = 512 := (Nat.card_congr θ.toEquiv).trans hcardM
  have hcW' : centralizer ((W.subgroupOf R : Subgroup ↥R) : Set ↥R) =
      (centralizer (W : Set G)).subgroupOf R := by
    ext r
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
    constructor
    · intro hc w hw
      exact congrArg Subtype.val (hc ⟨w, hWR hw⟩ (Subgroup.mem_subgroupOf.mpr hw))
    · intro hc w hw
      exact Subtype.ext (hc w (Subgroup.mem_subgroupOf.mp (SetLike.mem_coe.mp hw)))
  have hker : ρ.ker = (centralizer (W : Set G)).subgroupOf S := by
    ext s
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, hρker]
  have hBA : ∀ B ∈ CFSG.higherElemThompsonFamily ↥R 1,
      ((B.map R.subtype).subgroupOf S).map ρ ≤ axisT := by
    intro B hB
    set B' := B.map R.subtype with hB'def
    have hB'R : B' ≤ R := map_subtype_le B
    have hB'S : B' ≤ S := hB'R.trans le_sup_right
    obtain ⟨hBel, -⟩ := (CFSG.mem_higherElemThompsonFamily_iff 1 B).mp hB
    have hB'el : CFSG.IsElementaryAbelian 2 ↥B' := CFSG.IsElementaryAbelian.map R.subtype
    have hBhT : (B'.subgroupOf S).map ρ ≤ sylowT := by
      rw [← hρR]
      exact Subgroup.map_mono fun x hx => hB'R hx
    have hsq : ∀ a ∈ (B'.subgroupOf S).map ρ, a ^ 2 = 1 := by
      rintro _ ⟨b, hb, rfl⟩
      rw [← map_pow]
      have hb2 : b ^ 2 = 1 := Subtype.ext (by
        rw [Subgroup.coe_pow, Subgroup.coe_one]
        exact CFSG.elemPow_eq_one_of_isElementaryAbelian (A := B') (b : G) hb)
      rw [hb2, map_one]
    have hcomm : ∀ a ∈ (B'.subgroupOf S).map ρ, ∀ c ∈ (B'.subgroupOf S).map ρ,
        a * c = c * a := by
      rintro _ ⟨b, hb, rfl⟩ _ ⟨b', hb', rfl⟩
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (congrArg (fun x : ↥B' => (x : G)) (hB'el.is_comm.comm ⟨_, hb⟩ ⟨_, hb'⟩))
    by_cases hBh : (B'.subgroupOf S).map ρ = ⊥
    · rw [hBh]
      exact bot_le
    obtain ⟨d, e, hd, he, hde, -, -⟩ :=
      Quasithin.SteinbergBK.near_maximal_elementary_whole_module_rank_inequality
        (W.subgroupOf R) hB
    have hcB : centralizer (B : Set ↥R) = (centralizer (B' : Set G)).subgroupOf R := by
      ext r
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
      constructor
      · rintro hc _ ⟨b, hb, rfl⟩
        exact congrArg Subtype.val (hc b hb)
      · intro hc b hb
        exact Subtype.ext (hc b ⟨b, hb, rfl⟩)
    have hBB' : B'.subgroupOf R = B := by
      ext b
      rw [Subgroup.mem_subgroupOf]
      constructor
      · rintro ⟨b', hb', hbb'⟩
        rwa [show b = b' from Subtype.ext hbb'.symm]
      · intro hb
        exact ⟨b, hb, rfl⟩
    have hcardB : Nat.card ↥((B'.subgroupOf S).map ρ) = 2 ^ e := by
      rw [← Subgroup.relIndex_ker, hker, Subgroup.relIndex_subgroupOf hB'S, ← he,
        Subgroup.inf_relIndex_left, hcW', ← hBB', Subgroup.relIndex_subgroupOf hB'R]
    have hrelW : (centralizer (B' : Set G)).relIndex W = 2 ^ d := by
      rw [← hd, Subgroup.inf_relIndex_left, hcB, Subgroup.relIndex_subgroupOf hWR]
    have hcardC : Nat.card ↥(centralizer (B' : Set G) ⊓ U) =
        Nat.card (fixVec3 ((B'.subgroupOf S).map ρ)) ^ 3 := by
      rw [← card_fixedMat]
      refine Nat.card_congr
        { toFun := fun x => ⟨Multiplicative.toAdd (θ ⟨x, (mem_inf.mp x.2).2⟩), ?_⟩
          invFun := fun Pm => ⟨(θ.symm (Multiplicative.ofAdd Pm.1) : G), ?_⟩
          left_inv := fun x => by
            apply Subtype.ext
            simp
          right_inv := fun Pm => by
            apply Subtype.ext
            simp }
      · rintro _ ⟨⟨b, hbS⟩, hb, rfl⟩
        have hbx : b * (x : G) * b⁻¹ = x := by
          rw [(mem_centralizer_iff.mp (mem_inf.mp x.2).1) b hb, mul_inv_cancel_right]
        have hmem : b * (x : G) * b⁻¹ ∈ U := by
          rw [hbx]
          exact (mem_inf.mp x.2).2
        have h1 := hθ ⟨b, hbS⟩ ⟨x, (mem_inf.mp x.2).2⟩ hmem
        have h0 : (⟨b * (x : G) * b⁻¹, hmem⟩ : ↥U) = ⟨x, (mem_inf.mp x.2).2⟩ := Subtype.ext hbx
        rw [h0] at h1
        exact h1.symm
      · refine mem_inf.mpr ⟨mem_centralizer_iff.mpr fun b hb => ?_,
          (θ.symm (Multiplicative.ofAdd Pm.1)).2⟩
        set u := θ.symm (Multiplicative.ofAdd Pm.1) with hu
        have hmem : b * (u : G) * b⁻¹ ∈ U :=
          (mem_normalizer_iff.mp (hSU (hB'S hb)) u).mp u.2
        have h1 := hθ ⟨b, hB'S hb⟩ u hmem
        have h2 : Multiplicative.toAdd (θ u) = Pm.1 := by
          rw [hu, MulEquiv.apply_symm_apply, toAdd_ofAdd]
        rw [h2, Pm.2 _ ⟨⟨b, hB'S hb⟩, hb, rfl⟩, ← h2] at h1
        have h3 : (⟨b * (u : G) * b⁻¹, hmem⟩ : ↥U) = u :=
          θ.injective (Multiplicative.toAdd.injective h1)
        have h4 := congrArg Subtype.val h3
        change b * (u : G) * b⁻¹ = u at h4
        exact (mul_inv_eq_iff_eq_mul.mp h4)
    have hr := Subgroup.relIndex_mul_card (centralizer (B' : Set G)) U
    rw [hcardU, hcardC] at hr
    have hrW : (centralizer (B' : Set G)).relIndex U ≤ 2 * Nat.card ↥((B'.subgroupOf S).map ρ) := by
      calc (centralizer (B' : Set G)).relIndex U ≤ (centralizer (B' : Set G)).relIndex W :=
            Subgroup.relIndex_le_of_le_right hUW (relIndex_ne_zero_of_finite _ _)
        _ = 2 ^ d := hrelW
        _ ≤ 2 ^ (1 + e) := Nat.pow_le_pow_right (by norm_num) hde
        _ = 2 * Nat.card ↥((B'.subgroupOf S).map ρ) := by rw [hcardB, pow_add, pow_one]
    exact le_axisT_of_count hBhT hBh hsq hcomm hr hrW
  have hJP : nqHigherThompson R 1 ≤ F ⊔ A' := by
    rw [nqHigherThompson, Subgroup.map_le_iff_le_comap]
    apply sSup_le
    intro B hB
    rw [← Subgroup.map_le_iff_le_comap]
    intro b hb
    have hbS : b ∈ S := le_sup_right (a := Y) (map_subtype_le B hb)
    have h1 : ρ ⟨b, hbS⟩ ∈ axisT := hBA B hB ⟨⟨b, hbS⟩, hb, rfl⟩
    rw [← hρA] at h1
    obtain ⟨⟨a, haS⟩, ha, hab⟩ := h1
    exact hρmem ⟨b, hbS⟩ a ha hab.symm
  have hPR : F ⊔ A' ≤ R := sup_le hFR (map_subtype_le A)
  have hNP : normalizer ((F ⊔ A' : Subgroup G) : Set G) ≤ M :=
    (normalizer_le_normalizer_nqHigherThompson hJP hPR).trans hJM
  have hFn : ∀ g ∈ S, ∀ f ∈ F, g * f * g⁻¹ ∈ F := fun g hg f hf =>
    ⟨S.mul_mem (S.mul_mem hg hf.1) (S.inv_mem hg),
      conj_mem_centralizer_of_normalizer (hSW hg) hf.2⟩
  have hfwd : ∀ (y : G) (hy : y ∈ Y),
      ρ ⟨y, le_sup_left (a := Y) hy⟩ ∈ normalizer (axisT : Set GL32) →
        ∀ p ∈ F ⊔ A', y * p * y⁻¹ ∈ F ⊔ A' := by
    intro y hy hN p hp
    have hyS : y ∈ S := le_sup_left (a := Y) hy
    have hle : F ⊔ A' ≤ (F ⊔ A').comap (MulAut.conj y).toMonoidHom := by
      refine sup_le (fun f hf => mem_sup_left (hFn y hyS f hf)) (fun a ha => ?_)
      change y * a * y⁻¹ ∈ F ⊔ A'
      have haS : a ∈ S := le_sup_right (a := Y) (map_subtype_le A ha)
      have hyaS : y * a * y⁻¹ ∈ S := S.mul_mem (S.mul_mem hyS haS) (S.inv_mem hyS)
      have h1 : ρ ⟨a, haS⟩ ∈ axisT := by
        rw [← hρA]
        exact ⟨⟨a, haS⟩, ha, rfl⟩
      have h2 : ρ ⟨y * a * y⁻¹, hyaS⟩ ∈ axisT := by
        have e : (⟨y * a * y⁻¹, hyaS⟩ : ↥S) = ⟨y, hyS⟩ * ⟨a, haS⟩ * (⟨y, hyS⟩)⁻¹ := rfl
        rw [e, map_mul, map_mul, map_inv]
        exact (mem_normalizer_iff.mp hN _).mp h1
      rw [← hρA] at h2
      obtain ⟨⟨a', ha'S⟩, ha', hab⟩ := h2
      exact hρmem ⟨y * a * y⁻¹, hyaS⟩ a' ha' hab.symm
    exact hle hp
  have hYN : ∀ (y : G) (hy : y ∈ Y),
      ρ ⟨y, le_sup_left (a := Y) hy⟩ ∈ normalizer (axisT : Set GL32) → y ∈ M := by
    intro y hy hyN
    refine hNP (mem_normalizer_of_conj_mem (hfwd y hy hyN) fun p hp => ?_)
    have hyN' : ρ ⟨y⁻¹, le_sup_left (a := Y) (Y.inv_mem hy)⟩ ∈ normalizer (axisT : Set GL32) := by
      have e : (⟨y⁻¹, le_sup_left (a := Y) (Y.inv_mem hy)⟩ : ↥S) =
          (⟨y, le_sup_left (a := Y) hy⟩)⁻¹ := rfl
      rw [e, map_inv]
      exact inv_mem hyN
    have := hfwd y⁻¹ (Y.inv_mem hy) hyN' p hp
    rwa [inv_inv] at this
  set ZU := U ⊓ centralizer (T : Set G) with hZUdef
  have hU0 : U ≠ ⊥ := by
    intro h0
    have h1 := hcardU
    rw [h0, Subgroup.card_bot] at h1
    omega
  have hZUne : ZU ≠ ⊥ := by
    have hT2 : IsPGroup 2 ↥T := h.sylow.1
    have : Group.IsNilpotent ↥T := hT2.isNilpotent
    have hUn : (U.subgroupOf T).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hUT).mpr hTU
    have hUne' : U.subgroupOf T ≠ ⊥ := by
      intro h0
      apply hU0
      rw [eq_bot_iff]
      intro v hv
      have : (⟨v, hUT hv⟩ : ↥T) ∈ U.subgroupOf T := hv
      rw [h0, mem_bot] at this
      exact (mem_bot).mpr (congrArg Subtype.val this)
    have hc := Group.IsNilpotent.inf_center_ne_bot_of_normal hUne'
    intro h0
    apply hc
    rw [eq_bot_iff]
    intro t ht
    obtain ⟨htU, htc⟩ := mem_inf.mp ht
    have h1 : (t : G) ∈ ZU := mem_inf.mpr ⟨htU, mem_centralizer_iff.mpr fun s hs =>
      congrArg Subtype.val ((mem_center_iff.mp htc) ⟨s, hs⟩)⟩
    rw [h0, mem_bot] at h1
    exact (mem_bot).mpr (Subtype.ext h1)
  have hZUZ : ZU ≤ quasithinOmegaOneCenter T := fun z hz =>
    subset_closure ⟨mem_inf.mpr ⟨hUT hz.1, hz.2⟩, hW2 z (hUW hz.1)⟩
  have hCZU : centralizer (ZU : Set G) ≤ M := by
    have hZU2 : IsPGroup 2 ZU := h.sylow.1.to_le (inf_le_left.trans hUT)
    have hloc : IsTwoLocal (normalizer (ZU : Set G)) := ⟨ZU, hZUne, hZU2, rfl⟩
    obtain ⟨M', hM'⟩ := Set.Finite.exists_maximal
      (s := {X : Subgroup G | IsTwoLocal X ∧ normalizer (ZU : Set G) ≤ X}) (Set.toFinite _)
      ⟨_, hloc, le_rfl⟩
    have hM'max : quasithinIsMaxTwoLocal M' :=
      ⟨hM'.1.1, fun X hX hMX => le_antisymm (hM'.2 ⟨hX, hM'.1.2.trans hMX⟩ hMX) hMX⟩
    have hCN : centralizer (ZU : Set G) ≤ normalizer (ZU : Set G) :=
      Subgroup.centralizer_le_normalizer _
    have hCM' : centralizer (quasithinOmegaOneCenter T : Set G) ≤ M' :=
      ((centralizer_le hZUZ).trans hCN).trans hM'.1.2
    rw [← h.centralizer_unique M' hM'max hCM']
    exact hCN.trans hM'.1.2
  have hYl : ∀ (y : G) (hy : y ∈ Y), (ρ ⟨y, le_sup_left (a := Y) hy⟩ : Mat3) *ᵥ
      (Pi.single 0 1 : Fin 3 → ZMod 2) = Pi.single 0 1 → y ∈ M := by
    intro y hy hye
    apply hCZU
    rw [mem_centralizer_iff]
    intro z hz
    have hzU : z ∈ U := hz.1
    have hfix : ∀ g ∈ sylowT, (g : Mat3) * Multiplicative.toAdd (θ ⟨z, hzU⟩) =
        Multiplicative.toAdd (θ ⟨z, hzU⟩) := by
      intro g hg
      rw [← hρR] at hg
      obtain ⟨⟨r, hrS⟩, hr, rfl⟩ := hg
      have hrT : r ∈ T := hRT hr
      have hrz : r * z * r⁻¹ = z := by
        rw [(mem_centralizer_iff.mp hz.2) r hrT, mul_inv_cancel_right]
      have hmem : r * z * r⁻¹ ∈ U := by
        rw [hrz]
        exact hzU
      have h1 := hθ ⟨r, hrS⟩ ⟨z, hzU⟩ hmem
      have h0 : (⟨r * z * r⁻¹, hmem⟩ : ↥U) = ⟨z, hzU⟩ := Subtype.ext hrz
      rw [h0] at h1
      exact h1.symm
    have h2 := mul_eq_of_fixed_sylowT hfix hye
    have hmem : y * z * y⁻¹ ∈ U :=
      (mem_normalizer_iff.mp (hSU (le_sup_left (a := Y) hy)) z).mp hzU
    have h3 := hθ ⟨y, le_sup_left (a := Y) hy⟩ ⟨z, hzU⟩ hmem
    rw [h2] at h3
    have h4 := congrArg Subtype.val (θ.injective (Multiplicative.toAdd.injective h3))
    change y * z * y⁻¹ = z at h4
    exact (mul_inv_eq_iff_eq_mul.mp h4).symm
  have hQ : Subgroup.closure ({g : GL32 |
      (g : Mat3) *ᵥ (Pi.single 0 1 : Fin 3 → ZMod 2) = Pi.single 0 1} ∪
        (normalizer (axisT : Set GL32) : Set GL32)) ≤ ((Y ⊓ M).subgroupOf S).map ρ := by
    rw [Subgroup.closure_le]
    intro g hg
    have hgY : g ∈ (Y.subgroupOf S).map ρ := by
      rw [hρY]
      exact mem_top g
    obtain ⟨⟨y, hyS⟩, hy, rfl⟩ := hgY
    have hyY : y ∈ Y := hy
    refine ⟨⟨y, hyS⟩, mem_inf.mpr ⟨hyY, ?_⟩, rfl⟩
    rcases hg with hg | hg
    · exact hYl y hyY hg
    · exact hYN y hyY hg
  rw [closure_stab_union_normalizer_axisT_eq_top] at hQ
  apply hYM
  intro y hy
  have hyS : y ∈ S := le_sup_left (a := Y) hy
  obtain ⟨⟨y', hy'S⟩, hy'YM, hyy'⟩ := hQ (mem_top (ρ ⟨y, hyS⟩))
  have hy'M : y' ∈ M := (mem_inf.mp hy'YM).2
  have h1 : ρ (⟨y', hy'S⟩⁻¹ * ⟨y, hyS⟩) = 1 := by
    rw [map_mul, map_inv, hyy', inv_mul_cancel]
  have h2 : y'⁻¹ * y ∈ F := ⟨S.mul_mem (S.inv_mem hy'S) hyS, (hρker _).mp h1⟩
  have e : y = y' * (y'⁻¹ * y) := by group
  rw [e]
  exact M.mul_mem hy'M (h.t_le (hRT (hFR h2)))

end CFSG.Quasithin.H13.NQBlock
