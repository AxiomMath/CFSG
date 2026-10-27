module

public import CFSG.Quasithin.H13.NQCoreEscapingBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.ReducedCore

public section

namespace CFSG.Quasithin.H13.NQCore

open Subgroup CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup
open scoped commutatorElement

section Abstract

variable {H : Type*} [Group H] [Finite H]

omit [Finite H] in
theorem commutator_eq_self_of_isSimpleGroup {S : Subgroup H} [IsSimpleGroup S]
    (hS : ¬ IsMulCommutative S) : ⁅S, S⁆ = S := by
  have hc : (commutator S).Normal := inferInstance
  rcases hc.eq_bot_or_eq_top with hb | ht
  · exfalso
    apply hS
    refine ⟨⟨fun a b => ?_⟩⟩
    have hmem : ⁅a, b⁆ ∈ commutator S := by
      rw [_root_.commutator_def]
      exact Subgroup.commutator_mem_commutator (mem_top a) (mem_top b)
    rw [hb, mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
    exact hmem
  · have h1 : (commutator S).map S.subtype = S := by
      rw [ht, ← MonoidHom.range_eq_map, range_subtype]
    rw [_root_.commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
      range_subtype] at h1
    exact h1

omit [Finite H] in
theorem commutator_biSup_eq {ι : Type*} {p : ι → Prop} (S : ι → Subgroup H)
    (hS : ∀ i, p i → ⁅S i, S i⁆ = S i) :
    ⁅⨆ (i) (_ : p i), S i, ⨆ (i) (_ : p i), S i⁆ = ⨆ (i) (_ : p i), S i := by
  refine le_antisymm (Subgroup.commutator_le.mpr fun x hx y hy => ?_) ?_
  · rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hx hy) (inv_mem hx)) (inv_mem hy)
  refine iSup₂_le fun i hi => ?_
  calc S i = ⁅S i, S i⁆ := (hS i hi).symm
    _ ≤ _ := Subgroup.commutator_mono (le_iSup₂_of_le i hi le_rfl) (le_iSup₂_of_le i hi le_rfl)

theorem perfectResidual_minimal_structure {T X : Subgroup H}
    (hT : IsSylowTwoOf T (⊤ : Subgroup H)) (hTn : ¬ T.Normal) (hTX : T ≤ X) (hXH : X < ⊤)
    (hmax : ∀ Y : Subgroup H, T ≤ Y → Y < ⊤ → Y ≤ X) (hns : ¬ Group.IsSolvable H) :
    CFSG.perfectResidual H ⊔ kerIn X ⊤ = oddResidualPreimage H ∧
      CFSG.perfectResidual H ⊔ T = ⊤ ∧ CFSG.perfectResidual H ≠ ⊥ ∧
      Group.IsPerfect (CFSG.perfectResidual H) ∧ (CFSG.perfectResidual H).Characteristic := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨⟨-, hJK⟩, -, hKT, ⟨hKn, -⟩, -, hsimple⟩ :=
    qt_A7_unique_Sylow_overgroup_core_and_simple_section hT hTn hTX hXH hmax
  obtain ⟨L, -, -, -, hKeq, -, -, hconjs, -⟩ := hsimple hns
  obtain ⟨-, hYc, hYp, -, hiff, hbot⟩ := CFSG.perfect_residual_characterization (G := H)
  have := hKn
  have hKbar : ⁅(oddResidualPreimage H).map (QuotientGroup.mk' (kerIn X ⊤)),
      (oddResidualPreimage H).map (QuotientGroup.mk' (kerIn X ⊤))⁆ =
        (oddResidualPreimage H).map (QuotientGroup.mk' (kerIn X ⊤)) := by
    rw [hKeq]
    refine commutator_biSup_eq _ fun t ht => ?_
    obtain ⟨hs, hna⟩ := hconjs t ht
    exact commutator_eq_self_of_isSimpleGroup hna
  have hpg : IsPGroup 2 (H ⧸ oddResidualPreimage H) := by
    intro g
    obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective g
    have hh : h ∈ oddResidualPreimage H ⊔ T := hKT ▸ mem_top h
    obtain ⟨k, hk, t, ht, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hh
    obtain ⟨n, hn⟩ := hT.2.1 ⟨t, ht⟩
    refine ⟨n, ?_⟩
    have hk1 : (k : H ⧸ oddResidualPreimage H) = 1 := (QuotientGroup.eq_one_iff k).mpr hk
    have ht1 : t ^ 2 ^ n = 1 := congrArg Subtype.val hn
    rw [QuotientGroup.mk_mul, hk1, one_mul, ← QuotientGroup.mk_pow, ht1, QuotientGroup.mk_one]
  have hYK : CFSG.perfectResidual H ≤ oddResidualPreimage H := by
    have := hpg.isNilpotent
    exact (hiff (oddResidualPreimage H)).mp inferInstance
  have hYbar : (CFSG.perfectResidual H).map (QuotientGroup.mk' (kerIn X ⊤)) =
      CFSG.perfectResidual (H ⧸ kerIn X ⊤) :=
    CFSG.RankThreeCoreUniqueness.Helpers.finite_perfectResidual_map_eq _
      (QuotientGroup.mk'_surjective _)
  have hKle : (oddResidualPreimage H).map (QuotientGroup.mk' (kerIn X ⊤)) ≤
      (CFSG.perfectResidual H).map (QuotientGroup.mk' (kerIn X ⊤)) := by
    rw [hYbar]
    exact (CFSG.perfect_residual_transport (MonoidHom.id (H ⧸ kerIn X ⊤))).2.2 _
      (Subgroup.isPerfect_iff.mpr hKbar)
  have hKYJ : oddResidualPreimage H ≤ CFSG.perfectResidual H ⊔ kerIn X ⊤ := by
    have h1 := Subgroup.comap_mono (f := QuotientGroup.mk' (kerIn X ⊤)) hKle
    rw [Subgroup.comap_map_eq, Subgroup.comap_map_eq, QuotientGroup.ker_mk'] at h1
    exact le_sup_left.trans h1
  have hYJ : CFSG.perfectResidual H ⊔ kerIn X ⊤ = oddResidualPreimage H :=
    le_antisymm (sup_le hYK hJK.le) hKYJ
  have hYT : CFSG.perfectResidual H ⊔ T = ⊤ := by
    by_contra hne
    have h1 := hmax _ le_sup_right (lt_top_iff_ne_top.mpr hne)
    have h2 : oddResidualPreimage H ≤ X := hYJ ▸ sup_le (le_sup_left.trans h1) kerIn_le
    have h3 : (⊤ : Subgroup H) ≤ X := hKT ▸ sup_le h2 hTX
    exact hXH.ne (top_le_iff.mp h3)
  exact ⟨hYJ, hYT, fun hb => hns (hbot.mp hb), hYp, hYc⟩

end Abstract

section Ambient

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem subgroupOf_lt_top_iff {K H : Subgroup G} (hKH : K ≤ H) :
    K.subgroupOf H < ⊤ ↔ K < H := by
  constructor
  · intro hlt
    refine lt_of_le_of_ne hKH fun heq => hlt.ne ?_
    rw [heq, subgroupOf_self]
  · intro hlt
    refine lt_top_iff_ne_top.mpr fun heq => hlt.ne ?_
    exact le_antisymm hKH (subgroupOf_eq_top.mp heq)

theorem minimal_escaping_abstract {T L M : Subgroup G}
    (h : QTNQ T L M)
    (hTI : ∀ g : G, qtnqU L M ⊓ CFSG.conjugate (qtnqU L M) g = ⊥ ∨
      CFSG.conjugate (qtnqU L M) g = qtnqU L M)
    (hW : normalizer ((sSup {X : Subgroup G | (∃ g : G, CFSG.conjugate (qtnqU L M) g = X) ∧
      X ≤ T} : Subgroup G) : Set G) ≤ M)
    {H₀ H : Subgroup G} (hH₀ : quasithinIsMaxTwoLocal H₀) (hTH₀ : T ≤ H₀)
    (hTH : T ≤ H) (hHH₀ : H ≤ H₀) (hHM : ¬ H ≤ M)
    (hmin : ∀ K : Subgroup G, T ≤ K → K ≤ H₀ → ¬ K ≤ M → Nat.card H ≤ Nat.card K) :
    IsSylowTwoOf (T.subgroupOf H) ⊤ ∧ ¬ (T.subgroupOf H).Normal ∧
      T.subgroupOf H ≤ (H ⊓ M).subgroupOf H ∧ (H ⊓ M).subgroupOf H < ⊤ ∧
      (∀ Y' : Subgroup ↥H, T.subgroupOf H ≤ Y' → Y' < ⊤ → Y' ≤ (H ⊓ M).subgroupOf H) ∧
      ¬ Group.IsSolvable ↥H := by
  classical
  obtain ⟨hns, -, -, hTn, hTX, hXlt, hmaxG⟩ :=
    minimal_escaping_basic h hTI hW hH₀ hTH₀ hTH hHH₀ hHM hmin
  refine ⟨?_, hTn, fun x hx => hTX hx, (subgroupOf_lt_top_iff inf_le_left).mpr hXlt, ?_, hns⟩
  · refine ⟨le_top, h.sylow.1.of_equiv (subgroupOfEquivOfLe hTH).symm, ?_⟩
    change ¬ 2 ∣ (T.subgroupOf H).relIndex ⊤
    rw [Subgroup.relIndex_top_right]
    exact fun hd => h.sylow.2 (hd.trans (Subgroup.relIndex_dvd_index_of_le hTH))
  · intro Y' hTY' hY'
    have hKH : Y'.map H.subtype ≤ H := map_subtype_le _
    have hTK : T ≤ Y'.map H.subtype := fun t ht => ⟨⟨t, hTH ht⟩, hTY' ht, rfl⟩
    have hKlt : Y'.map H.subtype < H := by
      have h1 : (Y'.map H.subtype).subgroupOf H = Y' :=
        Subgroup.comap_map_eq_self_of_injective H.subtype_injective Y'
      rw [← subgroupOf_lt_top_iff hKH, h1]
      exact hY'
    have hle := hmaxG _ hTK hKlt
    intro y hy
    exact hle ⟨y, hy, rfl⟩

theorem minimal_escaping_structure {T L M : Subgroup G}
    (h : QTNQ T L M)
    (hTI : ∀ g : G, qtnqU L M ⊓ CFSG.conjugate (qtnqU L M) g = ⊥ ∨
      CFSG.conjugate (qtnqU L M) g = qtnqU L M)
    (hW : normalizer ((sSup {X : Subgroup G | (∃ g : G, CFSG.conjugate (qtnqU L M) g = X) ∧
      X ≤ T} : Subgroup G) : Set G) ≤ M)
    {H₀ H : Subgroup G} (hH₀ : quasithinIsMaxTwoLocal H₀) (hTH₀ : T ≤ H₀)
    (hTH : T ≤ H) (hHH₀ : H ≤ H₀) (hHM : ¬ H ≤ M)
    (hmin : ∀ K : Subgroup G, T ≤ K → K ≤ H₀ → ¬ K ≤ M → Nat.card H ≤ Nat.card K) :
    ((CFSG.perfectResidual ↥H).map H.subtype ≠ ⊥ ∧
      ⁅(CFSG.perfectResidual ↥H).map H.subtype, (CFSG.perfectResidual ↥H).map H.subtype⁆ =
        (CFSG.perfectResidual ↥H).map H.subtype ∧
      (((CFSG.perfectResidual ↥H).map H.subtype).subgroupOf H).Characteristic) ∧
    ((CFSG.perfectResidual ↥H).map H.subtype ⊔ T = H ∧
      ¬ (CFSG.perfectResidual ↥H).map H.subtype ≤ M ∧
      ∀ x ∈ H, ∃ k : ℕ, x ^ 2 ^ k ∈ (CFSG.perfectResidual ↥H).map H.subtype) ∧
    pCoreOf 2 ((CFSG.perfectResidual ↥H).map H.subtype) =
      (CFSG.perfectResidual ↥H).map H.subtype ⊓ pCoreOf 2 H ∧
    (pCoreOf 2 H ≤ (kerIn ((H ⊓ M).subgroupOf H) ⊤).map H.subtype ∧
      Group.IsNilpotent ((kerIn ((H ⊓ M).subgroupOf H) ⊤).map
        (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥H))) ∧
      Odd (Nat.card ((kerIn ((H ⊓ M).subgroupOf H) ⊤).map
        (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥H))))) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hT'syl, hTn, hT'X', hX'lt, hmax', hns⟩ :=
    minimal_escaping_abstract h hTI hW hH₀ hTH₀ hTH hHH₀ hHM hmin
  obtain ⟨-, hYT, hY1, hYp, hYc⟩ :=
    perfectResidual_minimal_structure hT'syl hTn hT'X' hX'lt hmax' hns
  obtain ⟨⟨hRJ, -⟩, ⟨hJnil, hJodd, -⟩, -⟩ :=
    qt_A7_unique_Sylow_overgroup_core_and_simple_section hT'syl hTn hT'X' hX'lt hmax'
  have hYsub : ((CFSG.perfectResidual ↥H).map H.subtype).subgroupOf H =
      CFSG.perfectResidual ↥H :=
    Subgroup.comap_map_eq_self_of_injective H.subtype_injective _
  have hYH : (CFSG.perfectResidual ↥H).map H.subtype ≤ H := map_subtype_le _
  have := hYc
  have hYn : (CFSG.perfectResidual ↥H).Normal := inferInstance
  have hHnY : H ≤ normalizer (((CFSG.perfectResidual ↥H).map H.subtype : Subgroup G) : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hYH).mp (by rw [hYsub]; exact hYn)
  have hYTG : (CFSG.perfectResidual ↥H).map H.subtype ⊔ T = H := by
    have h1 := congrArg (Subgroup.map H.subtype) hYT
    rwa [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hTH, ← MonoidHom.range_eq_map,
      range_subtype] at h1
  have h2grp : ∀ x ∈ H, ∃ k : ℕ, x ^ 2 ^ k ∈ (CFSG.perfectResidual ↥H).map H.subtype := by
    intro x hx
    have hx' : (⟨x, hx⟩ : ↥H) ∈ CFSG.perfectResidual ↥H ⊔ T.subgroupOf H := hYT ▸ mem_top _
    obtain ⟨y, hy, t, ht, hyt⟩ := Subgroup.mem_sup_of_normal_left.mp hx'
    obtain ⟨k, hk⟩ := (h.sylow.1.of_equiv (subgroupOfEquivOfLe hTH).symm) ⟨t, ht⟩
    refine ⟨k, ⟨⟨x, hx⟩ ^ 2 ^ k, ?_, rfl⟩⟩
    show (⟨x, hx⟩ : ↥H) ^ 2 ^ k ∈ CFSG.perfectResidual ↥H
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, ← hyt, QuotientGroup.mk_mul,
      (QuotientGroup.eq_one_iff y).mpr hy, one_mul, ← QuotientGroup.mk_pow]
    have ht1 : t ^ 2 ^ k = 1 := congrArg Subtype.val hk
    rw [ht1, QuotientGroup.mk_one]
  have hqY : pCoreOf 2 ((CFSG.perfectResidual ↥H).map H.subtype) =
      (CFSG.perfectResidual ↥H).map H.subtype ⊓ pCoreOf 2 H := by
    apply le_antisymm
    · refine le_inf (LieType.BorelTits.pCoreOf_le 2 _) ?_
      refine LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
        ((LieType.BorelTits.pCoreOf_le 2 _).trans hYH)
        (hHnY.trans (LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _))
        (LieType.BorelTits.pCoreOf_isPGroup 2 _)
    · refine LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left ?_
        ((LieType.BorelTits.pCoreOf_isPGroup 2 H).to_le inf_le_right)
      have key : ∀ y ∈ (CFSG.perfectResidual ↥H).map H.subtype,
          ∀ z ∈ (CFSG.perfectResidual ↥H).map H.subtype ⊓ pCoreOf 2 H,
            y * z * y⁻¹ ∈ (CFSG.perfectResidual ↥H).map H.subtype ⊓ pCoreOf 2 H := by
        intro y hy z hz
        obtain ⟨hzY, hzR⟩ := mem_inf.mp hz
        exact mem_inf.mpr ⟨mul_mem (mul_mem hy hzY) (inv_mem hy),
          (mem_normalizer_iff.mp (LieType.BorelTits.le_normalizer_pCoreOf 2 H (hYH hy)) z).mp hzR⟩
      intro y hy
      refine mem_normalizer_iff.mpr fun z => ⟨key y hy z, fun hz => ?_⟩
      have := key y⁻¹ (inv_mem hy) _ hz
      simpa [mul_assoc] using this
  refine ⟨⟨fun hb => hY1 ((map_eq_bot_iff_of_injective _ H.subtype_injective).mp hb), ?_,
    by rw [hYsub]; exact hYc⟩, ⟨hYTG, fun hYM => hHM (hYTG ▸ sup_le hYM h.t_le), h2grp⟩, hqY, ?_,
    hJnil,
    hJodd⟩
  · rw [← Subgroup.map_commutator, Subgroup.isPerfect_iff.mp hYp]
  · exact map_mono hRJ

end Ambient

end CFSG.Quasithin.H13.NQCore
