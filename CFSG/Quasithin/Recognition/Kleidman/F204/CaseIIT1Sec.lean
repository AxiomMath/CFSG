module

public import CFSG.Quasithin.Recognition.Kleidman.F204.CaseIIT2Sec
public import CFSG.Quasithin.Recognition.Kleidman.F204.CaseIIT2Alg
public import CFSG.Quasithin.Recognition.Kleidman.F204.LocalFive

public section

namespace CFSG.Quasithin.Kleidman.F204

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.F7
  CFSG.Quasithin.FA5 CFSG.Quasithin.F53 CFSG.Quasithin.CosetGeom
open scoped commutatorElement

namespace Sec

open Subgroup

section Abstract

variable {A : Type*} [CommGroup A] [Finite A] {Γ : Type*} [Group Γ] {ρ : Γ →* MulAut A}

omit [Finite A] in
theorem ginv_subgroupOf {Y X : Subgroup A} (hY : GInv ρ Y) (hX : GInv ρ X) :
    GInv (subAct Y hY) (X.subgroupOf Y) := by
  intro g y hy
  show ((subAct Y hY g y : Y) : A) ∈ X
  rw [subAct_coe]; exact hX g y hy

theorem layer_five (h2 : ∀ a : A, a * a = 1) {Qs : Subgroup Γ} {Y X : Subgroup A} (_hXY : X ≤ Y)
    (hY : GInv ρ Y) (hX : GInv ρ X) (hQ : ∀ q ∈ Qs, ∀ y ∈ Y, ρ q y * y⁻¹ ∈ X) {t c : Γ}
    (ht2 : t * t ∈ Qs) (hc5 : c ^ 5 = 1) (hinv : ∃ q ∈ Qs, t * c * t⁻¹ = c⁻¹ * q)
    (hidx : idx (ρ t) Y X ≤ 2) : ∀ y ∈ Y, ρ c y * y⁻¹ ∈ X := by
  let X' : Subgroup ↥Y := X.subgroupOf Y
  have hX' : GInv (subAct Y hY) X' := ginv_subgroupOf hY hX
  let ρh : Γ →* MulAut (↥Y ⧸ X') := quotAct X' hX'
  have hV2 : ∀ v : ↥Y ⧸ X', v * v = 1 := by
    intro v
    induction v using QuotientGroup.induction_on with
    | H a => rw [← QuotientGroup.mk_mul]; exact (congrArg _ (Subtype.ext (h2 a))).trans (QuotientGroup.mk_one _)
  have hmem : ∀ (g : Γ) (y : Y), ρh g (y : ↥Y ⧸ X') = (y : ↥Y ⧸ X') ↔ ρ g y * y⁻¹ ∈ X := by
    intro g y
    rw [quotAct_mk, QuotientGroup.eq]
    show ((((subAct Y hY g y)⁻¹ * y : ↥Y)) : A) ∈ X ↔ _
    have e : (ρ g y)⁻¹ * (y : A) = (ρ g y * (y : A)⁻¹)⁻¹ := by simp [mul_comm]
    rw [Subgroup.coe_mul, Subgroup.coe_inv, subAct_coe, e, inv_mem_iff]
    exact Iff.rfl
  have hker : ∀ q ∈ Qs, ρh q = 1 := by
    intro q hq
    ext v
    induction v using QuotientGroup.induction_on with
    | H y => exact (hmem q y).mpr (hQ q hq y y.2)
  have hζ2 : ρh t ^ 2 = 1 := by
    rw [sq, ← map_mul]; exact hker _ ht2
  have hξ5 : ρh c ^ 5 = 1 := by
    rw [← map_pow, hc5, map_one]
  have hinv' : ρh t * ρh c * (ρh t)⁻¹ = (ρh c)⁻¹ := by
    obtain ⟨q, hq, hqe⟩ := hinv
    rw [← map_inv, ← map_mul, ← map_mul, hqe, map_mul, hker q hq, mul_one, map_inv]
  have hfix : (FA5.fixSub (ρh t)).index ≤ 2 := by
    let H : Subgroup ↥Y := (I (ρ t) Y X).subgroupOf Y
    have hsub : H.map (QuotientGroup.mk' X') ≤ FA5.fixSub (ρh t) := by
      rintro _ ⟨y, hy, rfl⟩
      rw [FA5.mem_fixSub]
      exact (hmem t y).mpr (Subgroup.mem_subgroupOf.mp hy).2
    calc (FA5.fixSub (ρh t)).index ≤ (H.map (QuotientGroup.mk' X')).index :=
          Subgroup.index_antitone hsub
      _ ≤ H.index := Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
          (Subgroup.index_map_dvd H (QuotientGroup.mk'_surjective X'))
      _ = idx (ρ t) Y X := rfl
      _ ≤ 2 := hidx
  have h1 : ρh c = 1 := FA5.eq_one_of_inverted_transvection hV2 hξ5 hζ2 hinv' hfix
  intro y hy
  exact (hmem c ⟨y, hy⟩).mp (by rw [h1]; rfl)

theorem five_trivial_of_layers (h2 : ∀ a : A, a * a = 1) (Qs : Subgroup Γ) [Qs.Normal]
    (hnil : ∀ Y : Subgroup A, GInv ρ Y → qcomm ρ Qs Y = Y → Y = ⊥) {t c : Γ}
    (ht2 : t * t ∈ Qs) (hc5 : c ^ 5 = 1) (hinv : ∃ q ∈ Qs, t * c * t⁻¹ = c⁻¹ * q)
    (Y0 : Subgroup A) (hY0 : ∀ y ∈ Y0, ρ t y = y) (hY0i : Y0.index ≤ 2) :
    ∀ n : ℕ, ∀ W : Subgroup A, Nat.card W ≤ n → GInv ρ W → ∀ y ∈ W, ρ c y = y := by
  have hodd : Odd (orderOf c) := by
    have hd : orderOf c ∣ 5 := orderOf_dvd_of_pow_eq_one hc5
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 5)).mp hd with h | h <;> rw [h] <;> decide
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro W hn hW y hy
    set W' := qcomm ρ Qs W with hW'
    have hW'le : W' ≤ W := qcomm_le hW
    have hW'g : GInv ρ W' := qcomm_ginv hW
    by_cases heq : W' = W
    · have := hnil W hW heq
      rw [this] at hy
      rw [Subgroup.mem_bot.mp hy, map_one]
    · have hlt : W' < W := lt_of_le_of_ne hW'le heq
      have hcard : Nat.card W' < n := lt_of_lt_of_le (Subgroup.card_lt_of_lt hlt) hn
      have hfixW' : ∀ w ∈ W', ρ c w = w := ih _ hcard W' le_rfl hW'g
      have hidx : idx (ρ t) W W' ≤ 2 := by
        have hsub : W ⊓ Y0 ≤ I (ρ t) W W' := by
          intro a ha
          refine ⟨ha.1, ?_⟩
          show kap (ρ t) a ∈ W'
          rw [kap_apply, hY0 a ha.2, mul_inv_cancel]; exact W'.one_mem
        unfold idx
        calc (I (ρ t) W W').relIndex W ≤ (W ⊓ Y0).relIndex W :=
              Subgroup.relIndex_le_of_le_left hsub (relIndex_ne_zero' _ _)
          _ = Y0.relIndex W := by rw [inf_comm, Subgroup.inf_relIndex_right]
          _ ≤ Y0.index := Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
              (Subgroup.relIndex_dvd_index_of_normal Y0 W)
          _ ≤ 2 := hY0i
      have hlayer := layer_five h2 hW'le hW hW'g (fun q hq y hy => mul_inv_mem_qcomm hq hy)
        ht2 hc5 hinv hidx
      exact coprime_sub h2 hodd hfixW' (fun y hy => hlayer y hy) y hy

end Abstract

end Sec

variable {G : Type} [Group G] [Finite G] {L1 L2 S D X : Subgroup G}

theorem inv_rel_stab (F : Frame L1 L2 S D X) {δ : Geo (P1 L1 L2 S) (P2 L1 L2 S)}
    (hδ : vtype δ = false) {x t : G} (hx : x ∈ stab δ) (hx5 : x ^ 5 = 1) (ht : t ∈ stab δ)
    (htQ : t ∉ Qv δ) (ht2 : t * t ∈ Qv δ) : ∃ q ∈ Qv δ, t * x * t⁻¹ = x⁻¹ * q := by
  obtain ⟨h, hh1, hh2, hhx⟩ := exists_conj_stab_false_X F hδ hx hx5
  have ha'P : h * t * h⁻¹ ∈ P1 L1 L2 S := by rw [← hh1]; exact mem_conjSub_of_mem' ht
  have ha'Q : h * t * h⁻¹ ∉ Q1 L1 L2 S := by
    intro hm
    rw [← hh2, mem_conjSub] at hm
    apply htQ
    have e : h⁻¹ * (h * t * h⁻¹) * h = t := by group
    rwa [e] at hm
  have ha'2 : (h * t * h⁻¹) * (h * t * h⁻¹) ∈ Q1 L1 L2 S := by
    rw [← hh2]
    have e : (h * t * h⁻¹) * (h * t * h⁻¹) = h * (t * t) * h⁻¹ := by group
    rw [e]; exact mem_conjSub_of_mem' ht2
  obtain ⟨q, hq, hinv⟩ := inv_of_involution_P1 F ha'P ha'2 ha'Q hhx
  refine ⟨h⁻¹ * q * h, ?_, ?_⟩
  · rw [← hh2, mem_conjSub] at hq
    exact hq
  · have e : t * x * t⁻¹ = h⁻¹ * ((h * t * h⁻¹) * (h * x * h⁻¹) * (h * t * h⁻¹)⁻¹) * h := by group
    rw [e, hinv]
    group

open Sec in
theorem five_centralizes_mod (F : Frame L1 L2 S D X) {δ : Geo (P1 L1 L2 S) (P2 L1 L2 S)}
    (hδ : vtype δ = false) {U V Y : Subgroup G} (hU : IsElemAbelian 2 U)
    (hUn : stab δ ≤ Subgroup.normalizer (U : Set G)) (hVU : V ≤ U)
    (hVn : stab δ ≤ Subgroup.normalizer (V : Set G)) {t : G} (ht : t ∈ stab δ) (htQ : t ∉ Qv δ)
    (ht2 : t ^ 2 ∈ Qv δ) (_hYU : Y ≤ U) (hY : Y.relIndex U ≤ 2)
    (hYt : ∀ y ∈ Y, t * y * t⁻¹ * y⁻¹ ∈ V) :
    ∀ x ∈ stab δ, x ^ 5 = 1 → ∀ u ∈ U, x * u * x⁻¹ * u⁻¹ ∈ V := by
  intro x hx hx5 u hu
  let cg : CommGroup ↥U := { (inferInstance : Group ↥U) with
    mul_comm := fun a b => Subtype.ext (isElemAbelian_comm hU a.2 b.2) }
  let ρ : ↥(stab δ) →* MulAut ↥U := U.normalizerMonoidHom.comp (Subgroup.inclusion hUn)
  have hρ : ∀ (g : ↥(stab δ)) (a : ↥U), (((ρ g a : ↥U)) : G) = (g : G) * a * (g : G)⁻¹ :=
    fun g a => Subgroup.normalizerMonoidHom_apply_apply_coe U (Subgroup.inclusion hUn g) a
  have h2 : ∀ a : ↥U, a * a = 1 := fun a => Subtype.ext (by
    have := hU.2 a a.2
    simpa [sq] using this)
  let Vq : Subgroup ↥U := V.subgroupOf U
  have hVq : GInv ρ Vq := by
    intro g y hy
    rw [Subgroup.mem_subgroupOf] at hy ⊢
    rw [hρ]
    exact (Subgroup.mem_normalizer_iff.mp (hVn g.2) y).mp hy
  let ρ' : ↥(stab δ) →* MulAut (↥U ⧸ Vq) := quotAct Vq hVq
  have hρ'mk : ∀ (g : ↥(stab δ)) (a : ↥U), ρ' g (a : ↥U ⧸ Vq) = ((ρ g a : ↥U) : ↥U ⧸ Vq) :=
    fun g a => quotAct_mk hVq g a
  let Qs : Subgroup ↥(stab δ) := (Qv δ).subgroupOf (stab δ)
  have hQsn : Qs.Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have := (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 (stab δ) g.2) (n : G)).mp hn
    have h' : (g : G) * (n : G) * (g : G)⁻¹ ∈ Qv δ := this
    simpa using h'⟩
  have hker' : ∀ g : ↥(stab δ), g ∈ Qs ↔ (g : G) ∈ Qv δ := fun g => Subgroup.mem_subgroupOf
  have hcomm_le : ∀ Z : Subgroup ↥U, (qcomm ρ Qs Z).map U.subtype ≤ ⁅Z.map U.subtype, Qv δ⁆ := by
    intro Z
    rw [Subgroup.map_le_iff_le_comap]
    refine (Subgroup.closure_le _).mpr ?_
    rintro _ ⟨q, hq, y, hy, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap]
    have hqQ : (q : G) ∈ Qv δ := (hker' q).mp hq
    have e : ((ρ q y * y⁻¹ : ↥U) : G) = ⁅(q : G), (y : G)⁆ := by
      rw [Subgroup.coe_mul, hρ, Subgroup.coe_inv, commutatorElement_def]
    show ((ρ q y * y⁻¹ : ↥U) : G) ∈ _
    rw [e, Subgroup.commutator_comm]
    exact Subgroup.commutator_mem_commutator hqQ (Subgroup.mem_map_of_mem _ hy)
  have hUQ2 : IsPGroup 2 (U ⊔ Qv δ : Subgroup G) :=
    IsPGroup.to_sup_of_normal_left' (F7.isPGroup_of_isElemAbelian hU)
      (pCoreOf_isPGroup 2 (stab δ)) (le_trans (pCoreOf_le 2 _) hUn)
  have hnil : ∀ Y : Subgroup (↥U ⧸ Vq), GInv ρ' Y → qcomm ρ' Qs Y = Y → Y = ⊥ := by
    intro Y hYg hY
    let Yt : Subgroup ↥U := Y.comap (QuotientGroup.mk' Vq)
    have hYt : GInv ρ Yt := by
      intro g y hy
      show QuotientGroup.mk' Vq (ρ g y) ∈ Y
      have := hYg g (QuotientGroup.mk' Vq y) hy
      rwa [show ρ' g (QuotientGroup.mk' Vq y) = QuotientGroup.mk' Vq (ρ g y) from hρ'mk g y] at this
    have hYle : Yt ≤ Vq ⊔ qcomm ρ Qs Yt := by
      intro a ha
      have hmk : QuotientGroup.mk' Vq a ∈ qcomm ρ' Qs Y := by rw [hY]; exact ha
      have hsub : qcomm ρ' Qs Y ≤ (qcomm ρ Qs Yt).map (QuotientGroup.mk' Vq) := by
        refine (Subgroup.closure_le _).mpr ?_
        rintro _ ⟨q, hq, yb, hyb, rfl⟩
        obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective Vq yb
        refine ⟨ρ q y * y⁻¹, mul_inv_mem_qcomm hq hyb, ?_⟩
        show QuotientGroup.mk' Vq (ρ q y * y⁻¹) = _
        rw [map_mul, map_inv]
        show _ = ρ' q (QuotientGroup.mk' Vq y) * (QuotientGroup.mk' Vq y)⁻¹
        rw [show ρ' q (QuotientGroup.mk' Vq y) = QuotientGroup.mk' Vq (ρ q y) from hρ'mk q y]
      have h1 : a ∈ ((qcomm ρ Qs Yt).map (QuotientGroup.mk' Vq)).comap (QuotientGroup.mk' Vq) :=
        Subgroup.mem_comap.mpr (hsub hmk)
      rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk', sup_comm] at h1
      exact h1
    have hUV : U ≤ Subgroup.normalizer (V : Set G) := by
      intro u hu
      rw [Subgroup.mem_normalizer_iff]
      intro h
      constructor
      · intro hh
        have hc := isElemAbelian_comm hU hu (hVU hh)
        have e : u * h * u⁻¹ = h := by rw [hc]; group
        rw [e]; exact hh
      · intro hh
        have hc := isElemAbelian_comm hU hu (hVU hh)
        have hc2 : u * (u * h * u⁻¹) = u * h := by
          rw [hc]; group
        have e : u * h * u⁻¹ = h := mul_left_cancel hc2
        rw [e] at hh; exact hh
    have hHQ : U ⊔ Qv δ ≤ Subgroup.normalizer (V : Set G) :=
      sup_le hUV (le_trans (pCoreOf_le 2 _) hVn)
    have hYg : Yt.map U.subtype ≤ V ⊔ ⁅Yt.map U.subtype, U ⊔ Qv δ⁆ := by
      rintro g ⟨a, ha, rfl⟩
      have h1 := hYle ha
      have h2' : (a : G) ∈ (Vq ⊔ qcomm ρ Qs Yt).map U.subtype := ⟨a, h1, rfl⟩
      rw [Subgroup.map_sup] at h2'
      have e : Vq.map U.subtype = V := Subgroup.map_subgroupOf_eq_of_le hVU
      rw [e] at h2'
      refine (sup_le_sup_left (le_trans (hcomm_le Yt)
        (Subgroup.commutator_mono le_rfl le_sup_right)) V) h2'
    have hYV : Yt.map U.subtype ≤ V :=
      le_of_le_sup_commutator hUQ2 ((Subgroup.map_subtype_le Yt).trans le_sup_left) hHQ hYg
    rw [eq_bot_iff]
    intro yb hyb
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective Vq yb
    have haG : (a : G) ∈ V := hYV ⟨a, hyb, rfl⟩
    exact Subgroup.mem_bot.mpr ((QuotientGroup.eq_one_iff a).mpr (Subgroup.mem_subgroupOf.mpr haG))
  have h2' : ∀ a : ↥U ⧸ Vq, a * a = 1 := by
    intro v
    induction v using QuotientGroup.induction_on with
    | H a => rw [← QuotientGroup.mk_mul, h2 a]; exact QuotientGroup.mk_one _
  let t' : ↥(stab δ) := ⟨t, ht⟩
  let c : ↥(stab δ) := ⟨x, hx⟩
  let Y0 : Subgroup (↥U ⧸ Vq) := (Y.subgroupOf U).map (QuotientGroup.mk' Vq)
  have hY0 : ∀ y ∈ Y0, ρ' t' y = y := by
    rintro _ ⟨y0, hy0, rfl⟩
    show ρ' t' (y0 : ↥U ⧸ Vq) = (y0 : ↥U ⧸ Vq)
    rw [hρ'mk, QuotientGroup.eq]
    have e : (ρ t' y0)⁻¹ * y0 = (ρ t' y0 * y0⁻¹)⁻¹ := by simp [mul_comm]
    rw [e]
    refine Subgroup.inv_mem _ ?_
    show (((ρ t' y0 * y0⁻¹ : ↥U)) : G) ∈ V
    rw [Subgroup.coe_mul, hρ, Subgroup.coe_inv]
    exact hYt _ (Subgroup.mem_subgroupOf.mp hy0)
  have hY0i : Y0.index ≤ 2 :=
    (Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
      (Subgroup.index_map_dvd _ (QuotientGroup.mk'_surjective Vq))).trans hY
  have ht2' : t' * t' ∈ Qs := by
    rw [hker']
    show t * t ∈ Qv δ
    rw [← pow_two]; exact ht2
  have hc5 : c ^ 5 = 1 := Subtype.ext (by simpa using hx5)
  have hinv : ∃ q ∈ Qs, t' * c * t'⁻¹ = c⁻¹ * q := by
    obtain ⟨q, hq, hqe⟩ := inv_rel_stab F hδ hx hx5 ht htQ (by rw [← pow_two]; exact ht2)
    refine ⟨⟨q, pCoreOf_le 2 _ hq⟩, (hker' _).mpr hq, Subtype.ext ?_⟩
    simpa using hqe
  have hTop : GInv ρ' (⊤ : Subgroup (↥U ⧸ Vq)) := fun _ _ _ => Subgroup.mem_top _
  have hfix := five_trivial_of_layers h2' Qs hnil ht2' hc5 hinv Y0 hY0 hY0i (Nat.card (⊤ : Subgroup (↥U ⧸ Vq)))
    ⊤ le_rfl hTop (⟨u, hu⟩ : ↥U) (Subgroup.mem_top _)
  rw [hρ'mk, QuotientGroup.eq] at hfix
  have e : (ρ c (⟨u, hu⟩ : ↥U))⁻¹ * (⟨u, hu⟩ : ↥U) = (ρ c (⟨u, hu⟩ : ↥U) * (⟨u, hu⟩ : ↥U)⁻¹)⁻¹ := by
    simp [mul_comm]
  rw [e, inv_mem_iff] at hfix
  have h3 := Subgroup.mem_subgroupOf.mp hfix
  rw [Subgroup.coe_mul, hρ, Subgroup.coe_inv] at h3
  exact h3

end CFSG.Quasithin.Kleidman.F204
