module

public import CFSG.Quasithin.EmptyFaithful.S151S9P2B
public import CFSG.GroupTheory.BaerSuzuki.Helpers

public section

namespace CFSG.Quasithin

namespace HSRuLoc

namespace Lift

open CFSG.Open CFSG.QuasithinUnique CFSG.Blueprint
open scoped Pointwise

variable {G : Type} [Group G]

theorem mem_liftK_iff {L : Subgroup G} {H : Type} [Group H] (π : ↥L →* H) (Kb : Subgroup H) {x : G} :
    x ∈ liftK L π Kb ↔ ∃ y : ↥L, y ∈ ⁅Kb.comap π, Kb.comap π⁆ ∧ (y : G) = x :=
  Subgroup.mem_map

theorem mem_liftK_iff' {L : Subgroup G} {H : Type} [Group H] (π : ↥L →* H) (Kb : Subgroup H) {x : G}
    (hx : x ∈ L) : x ∈ liftK L π Kb ↔ (⟨x, hx⟩ : ↥L) ∈ ⁅Kb.comap π, Kb.comap π⁆ := by
  rw [mem_liftK_iff]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro h
    exact ⟨⟨x, hx⟩, h, rfl⟩

theorem mem_liftR_iff {L : Subgroup G} {H : Type} [Group H] (π : ↥L →* H) (Kb Rb : Subgroup H)
    {x : G} :
    x ∈ liftR L π Kb Rb ↔ ∃ y : ↥L, y ∈ ⁅Kb.comap π, Kb.comap π⁆ ∧ π y ∈ Rb ∧ (y : G) = x := by
  constructor
  · rintro ⟨hK, hR⟩
    obtain ⟨y, hy, rfl⟩ := hK
    obtain ⟨y', hy', hyy'⟩ := hR
    have : y' = y := Subtype.ext hyy'
    subst this
    exact ⟨y', hy, hy', rfl⟩
  · rintro ⟨y, hy, hyR, rfl⟩
    exact ⟨⟨y, hy, rfl⟩, ⟨y, hyR, rfl⟩⟩

theorem mem_liftR_iff' {L : Subgroup G} {H : Type} [Group H] (π : ↥L →* H) (Kb Rb : Subgroup H)
    {x : G} (hx : x ∈ L) :
    x ∈ liftR L π Kb Rb ↔
      (⟨x, hx⟩ : ↥L) ∈ ⁅Kb.comap π, Kb.comap π⁆ ∧ π ⟨x, hx⟩ ∈ Rb := by
  rw [mem_liftR_iff]
  constructor
  · rintro ⟨y, hy, hyR, rfl⟩
    exact ⟨hy, hyR⟩
  · rintro ⟨hy, hyR⟩
    exact ⟨⟨x, hx⟩, hy, hyR, rfl⟩

theorem liftR_le_liftK (L : Subgroup G) {H : Type} [Group H] (π : ↥L →* H) (Kb Rb : Subgroup H) :
    liftR L π Kb Rb ≤ liftK L π Kb := inf_le_left

theorem le_normalizer_liftK [Finite G] {L S : Subgroup G} {H : Type} [Group H] [Finite H]
    {π : ↥L →* H} {P Kb Rb : Subgroup H} {e : ℕ} (c : LiftCtx L S π P Kb Rb e) :
    S ≤ Subgroup.normalizer (liftK L π Kb : Set G) := by
  intro s hs
  have hsL : s ∈ Subgroup.normalizer (L : Set G) := c.hSN hs
  let φ : ↥L ≃* ↥L := L.normalizerMonoidHom ⟨s, hsL⟩
  have hφ : ∀ x : ↥L, ((φ x : ↥L) : G) = s * x * s⁻¹ := fun x =>
    Subgroup.normalizerMonoidHom_apply_apply_coe L ⟨s, hsL⟩ x
  have hker : π.ker.map φ.toMonoidHom = π.ker := by
    rw [c.hker]
    exact Subgroup.characteristic_iff_map_eq.mp (CFSG.BaerSuzuki.Helpers.pCore_characteristic 2) φ
  have hP : ((S ⊓ L).subgroupOf L).map π = P := c.hP.symm
  have hT : (S ⊓ L).subgroupOf L ≤ ((S ⊓ L).subgroupOf L).map φ.toMonoidHom := by
    intro t ht
    have hts : (t : G) ∈ S ⊓ L := ht
    have hs' : s⁻¹ ∈ Subgroup.normalizer (L : Set G) := inv_mem hsL
    have hL : s⁻¹ * (t : G) * s ∈ L := by
      have := (Subgroup.mem_normalizer_iff.mp hs' t).mp t.2
      simpa using this
    have hS : s⁻¹ * (t : G) * s ∈ S := S.mul_mem (S.mul_mem (S.inv_mem hs) hts.1) hs
    refine ⟨⟨s⁻¹ * t * s, hL⟩, ⟨hS, hL⟩, ?_⟩
    apply Subtype.ext
    show ((φ ⟨s⁻¹ * t * s, hL⟩ : ↥L) : G) = t
    rw [hφ]
    simp [mul_assoc]
  have hmain := map_comap_eq_of_uniq π c.hπ _ hP c.hm.le c.hm.uniq φ hker hT
  have hD : (⁅Kb.comap π, Kb.comap π⁆).map φ.toMonoidHom = ⁅Kb.comap π, Kb.comap π⁆ := by
    rw [Subgroup.map_commutator, hmain]
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    obtain ⟨y, hy, rfl⟩ := (mem_liftK_iff π Kb).mp hx
    refine (mem_liftK_iff π Kb).mpr ⟨φ y, ?_, hφ y⟩
    rw [← hD]
    exact Subgroup.mem_map_of_mem _ hy
  · intro hx
    obtain ⟨y', hy', hy'x⟩ := (mem_liftK_iff π Kb).mp hx
    have hy'' : y' ∈ (⁅Kb.comap π, Kb.comap π⁆).map φ.toMonoidHom := by rw [hD]; exact hy'
    obtain ⟨y, hy, rfl⟩ := hy''
    refine (mem_liftK_iff π Kb).mpr ⟨y, hy, ?_⟩
    have h1 : s * (y : G) * s⁻¹ = s * x * s⁻¹ := by rw [← hφ]; exact hy'x
    exact mul_left_cancel (mul_right_cancel h1)

theorem exists_alpha [Finite G] {L S : Subgroup G} {H : Type} [Group H] [Finite H] {π : ↥L →* H}
    {P Kb Rb : Subgroup H} {e : ℕ} (c : LiftCtx L S π P Kb Rb e) :
    ∃ α : ↥(liftK L π Kb) →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 (ZMod 2)),
      Function.Surjective α ∧ ∀ k : ↥(liftK L π Kb), α k = 1 ↔ (k : G) ∈ liftR L π Kb Rb := by
  obtain ⟨a, ha, hak⟩ := c.hm.quot
  have hmapD : (⁅Kb.comap π, Kb.comap π⁆).map π = Kb := map_commutator_comap π c.hπ c.hm.perf
  have hmem : ∀ k : ↥(liftK L π Kb), π (Subgroup.inclusion (liftK_le c) k) ∈ Kb := by
    intro k
    have hD : (Subgroup.inclusion (liftK_le c) k) ∈ ⁅Kb.comap π, Kb.comap π⁆ :=
      (mem_liftK_iff' π Kb (liftK_le c k.2)).mp k.2
    have := Subgroup.mem_map_of_mem π hD
    rwa [hmapD] at this
  let f : ↥(liftK L π Kb) →* ↥Kb :=
    (π.comp (Subgroup.inclusion (liftK_le c))).codRestrict Kb hmem
  have hf : Function.Surjective f := by
    rintro ⟨b, hb⟩
    have hb' : b ∈ (⁅Kb.comap π, Kb.comap π⁆).map π := by rw [hmapD]; exact hb
    obtain ⟨y, hy, rfl⟩ := hb'
    have hyK : (y : G) ∈ liftK L π Kb := (mem_liftK_iff' π Kb y.2).mpr hy
    exact ⟨⟨y, hyK⟩, rfl⟩
  refine ⟨a.comp f, ha.comp hf, fun k => ?_⟩
  have hk : (k : G) ∈ L := liftK_le c k.2
  rw [MonoidHom.comp_apply, ← MonoidHom.mem_ker, hak, Subgroup.mem_subgroupOf,
    mem_liftR_iff' π Kb Rb hk]
  constructor
  · intro h
    exact ⟨(mem_liftK_iff' π Kb hk).mp k.2, h⟩
  · intro h
    exact h.2

theorem liftR_isPGroup [Finite G] {L S : Subgroup G} {H : Type} [Group H] [Finite H] {π : ↥L →* H}
    {P Kb Rb : Subgroup H} {e : ℕ} (c : LiftCtx L S π P Kb Rb e) :
    IsPGroup 2 ↥(liftR L π Kb Rb) := by
  rw [← pCoreOf_liftK c]
  exact CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _

theorem liftK_mem_cComp [Finite G] {L S : Subgroup G} {H : Type} [Group H] [Finite H] {π : ↥L →* H}
    {P Kb Rb : Subgroup H} {e : ℕ} (c : LiftCtx L S π P Kb Rb e) :
    liftK L π Kb ∈ cComp (liftK L π Kb ⊔ S) := by
  have := isSimpleGroup_statedSL3
  set K := liftK L π Kb with hK
  set R := liftR L π Kb Rb with hR
  obtain ⟨α, hα, hαk⟩ := exists_alpha c
  have hnorm := le_normalizer_liftK c
  have hKnorm : K ⊔ S ≤ Subgroup.normalizer (K : Set G) :=
    sup_le Subgroup.le_normalizer hnorm
  have hKN : (K.subgroupOf (K ⊔ S)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr hKnorm
  have hRK : R ≤ K := liftR_le_liftK L π Kb Rb
  have hR2 : IsPGroup 2 ↥R := liftR_isPGroup c
  have hRsolv : Group.IsSolvable ↥R := by
    have : Group.IsNilpotent ↥R := hR2.isNilpotent
    infer_instance
  refine ⟨?_, liftK_perf c, A3.subnormal_of_normal le_sup_left hKN, ?_⟩
  · intro hbot
    have h1 : Subsingleton ↥K := by rw [hbot]; infer_instance
    have h2 : Subsingleton ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 (ZMod 2)) := hα.subsingleton
    exact not_subsingleton _ h2
  · intro K' hlt hne hperf hsub
    have hsubK : IsSubnormal K' K := A3.subnormal_of_le_of_le hsub hlt.le le_sup_left
    obtain ⟨M, hMK, hMn, hK'M⟩ := A3.subnormal_exists_normal_of_lt hsubK hlt
    have hnormα : ((M.subgroupOf K).map α).Normal := Subgroup.Normal.map hMn α hα
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((M.subgroupOf K).map α) with h | h
    · have hMR : M ≤ R := by
        intro m hm
        have hmem : (⟨m, hMK.le hm⟩ : ↥K) ∈ M.subgroupOf K := hm
        have : (⟨m, hMK.le hm⟩ : ↥K) ∈ α.ker := (Subgroup.map_eq_bot_iff _).mp h hmem
        exact (hαk _).mp (MonoidHom.mem_ker.mp this)
      have hK'R : K' ≤ R := hK'M.trans hMR
      have h3 : K' ≤ perfectCore R := le_perfectCore_of_perfect hK'R hperf
      rw [(isSolvable_iff_perfectCore_eq_bot R).mp hRsolv] at h3
      exact hne (le_bot_iff.mp h3)
    · have hKle : K ≤ M ⊔ R := by
        intro k hk
        have hk' : α ⟨k, hk⟩ ∈ (M.subgroupOf K).map α := by rw [h]; exact Subgroup.mem_top _
        obtain ⟨m', hm', hm'k⟩ := hk'
        have hmM : (m' : G) ∈ M := hm'
        have hrR : (m'⁻¹ * ⟨k, hk⟩ : ↥K) ∈ α.ker := by
          rw [MonoidHom.mem_ker, map_mul, map_inv, hm'k, inv_mul_cancel]
        have hrR' : (((m'⁻¹ * ⟨k, hk⟩ : ↥K)) : G) ∈ R := (hαk _).mp (MonoidHom.mem_ker.mp hrR)
        have hkeq : k = (m' : G) * (((m'⁻¹ * ⟨k, hk⟩ : ↥K)) : G) := by simp
        rw [hkeq]
        exact Subgroup.mul_mem_sup hmM hrR'
      have hY : K = M ⊔ R := le_antisymm hKle (sup_le hMK.le hRK)
      have h4 := perfectCore_le_of_sup_solvable hMK.le hMn hY hRsolv
      rw [perfectCore_eq_self_of_perfect (liftK_perf c)] at h4
      exact absurd (lt_of_lt_of_le hMK h4) (lt_irrefl _)

theorem charTwo_liftK [Finite G] {L S : Subgroup G} {H : Type} [Group H] [Finite H] {π : ↥L →* H}
    {P Kb Rb : Subgroup H} {e : ℕ} (c : LiftCtx L S π P Kb Rb e) :
    CharTwo (liftK L π Kb) := by
  have hmapD : (⁅Kb.comap π, Kb.comap π⁆).map π = Kb := map_commutator_comap π c.hπ c.hm.perf
  intro x hx
  obtain ⟨hxK, hxC⟩ := hx
  rw [pCoreOf_liftK c] at hxC ⊢
  have hxL : x ∈ L := liftK_le c hxK
  have hxD : (⟨x, hxL⟩ : ↥L) ∈ ⁅Kb.comap π, Kb.comap π⁆ := (mem_liftK_iff' π Kb hxL).mp hxK
  have hxKb : π ⟨x, hxL⟩ ∈ Kb := by
    have := Subgroup.mem_map_of_mem π hxD
    rwa [hmapD] at this
  refine (mem_liftR_iff' π Kb Rb hxL).mpr ⟨hxD, c.hm.R_cent (π ⟨x, hxL⟩) hxKb fun r hr => ?_⟩
  have hrK : r ∈ (⁅Kb.comap π, Kb.comap π⁆).map π := by rw [hmapD]; exact c.hm.R_le hr
  obtain ⟨y, hy, rfl⟩ := hrK
  have hyR : (y : G) ∈ liftR L π Kb Rb := (mem_liftR_iff' π Kb Rb y.2).mpr ⟨hy, hr⟩
  have hcomm : (y : G) * x = x * y := Subgroup.mem_centralizer_iff.mp hxC (y : G) hyR
  have h1 : (⟨x, hxL⟩ : ↥L) * y = y * ⟨x, hxL⟩ := Subtype.ext hcomm.symm
  rw [← map_mul, ← map_mul, h1]

theorem pCore_eq_subgroupOf_pCoreOf (K : Subgroup G) :
    CFSG.pCore 2 ↥K = (pCoreOf 2 K).subgroupOf K := by
  have h1 : CFSG.Open.pCore 2 ↥K = CFSG.pCore 2 ↥K := rfl
  exact (Subgroup.comap_map_eq_self_of_injective K.subtype_injective _).symm

theorem isModO2Surj_liftK [Finite G] {L S : Subgroup G} {H : Type} [Group H] [Finite H]
    {π : ↥L →* H} {P Kb Rb : Subgroup H} {e : ℕ} (c : LiftCtx L S π P Kb Rb e) :
    ∃ α : ↥(liftK L π Kb) →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 (ZMod 2)),
      IsModO2Surj (liftK L π Kb) α := by
  obtain ⟨α, hα, hαk⟩ := exists_alpha c
  refine ⟨α, hα, ?_⟩
  rw [pCore_eq_subgroupOf_pCoreOf, pCoreOf_liftK c]
  ext k
  rw [MonoidHom.mem_ker, hαk, Subgroup.mem_subgroupOf]

theorem not_liftK_le_centralizer [Finite G] {L S : Subgroup G} {H : Type} [Group H] [Finite H]
    {π : ↥L →* H} {P Kb Rb : Subgroup H} {e : ℕ} (c : LiftCtx L S π P Kb Rb e) :
    ¬ liftK L π Kb ≤ Subgroup.centralizer (centerOf (S ⊓ L) : Set G) := by
  intro hle
  have hmapD : (⁅Kb.comap π, Kb.comap π⁆).map π = Kb := map_commutator_comap π c.hπ c.hm.perf
  obtain ⟨l, hl, hlw⟩ : ∃ l ∈ L, l ∉ Subgroup.centralizer (centerOf (S ⊓ L) : Set G) := by
    by_contra hcon
    push Not at hcon
    exact c.hnc fun l hl => hcon l hl
  rw [Subgroup.mem_centralizer_iff] at hlw
  push Not at hlw
  obtain ⟨w, hw, hwl⟩ := hlw
  have hw2 : w ∈ S ⊓ L ∧ w ∈ Subgroup.centralizer ((S ⊓ L : Subgroup G) : Set G) := hw
  obtain ⟨hwST, hwC⟩ := hw2
  have hwL : w ∈ L := hwST.2
  set w' : ↥L := ⟨w, hwL⟩ with hw'
  have hw'T : w' ∈ (S ⊓ L).subgroupOf L := hwST
  have hπw : π w' ≠ 1 := by
    intro h1
    have h2 : w' ∈ Subgroup.center ↥L := ker_le_center c (MonoidHom.mem_ker.mpr h1)
    apply hwl
    have := Subgroup.mem_center_iff.mp h2 ⟨l, hl⟩
    exact (congrArg Subtype.val this).symm
  have hcent : π w' ∈ centerOf P := by
    refine ⟨?_, ?_⟩
    · rw [c.hP]
      exact Subgroup.mem_map_of_mem π hw'T
    · show π w' ∈ Subgroup.centralizer (P : Set H)
      rw [Subgroup.mem_centralizer_iff]
      intro p hp
      rw [c.hP] at hp
      obtain ⟨t, ht, rfl⟩ := hp
      have htST : (t : G) ∈ S ⊓ L := ht
      have : (t : G) * w = w * t := Subgroup.mem_centralizer_iff.mp hwC (t : G) htST
      have h3 : t * w' = w' * t := Subtype.ext this
      rw [← map_mul, ← map_mul, h3]
  obtain ⟨k, hk, hkw⟩ := c.hm.notC (π w') hcent hπw
  have hk' : k ∈ (⁅Kb.comap π, Kb.comap π⁆).map π := by rw [hmapD]; exact hk
  obtain ⟨y, hy, rfl⟩ := hk'
  have hyK : (y : G) ∈ liftK L π Kb := (mem_liftK_iff' π Kb y.2).mpr hy
  have hcomm : w * (y : G) = (y : G) * w := Subgroup.mem_centralizer_iff.mp (hle hyK) w hw
  have h1 : y * w' = w' * y := Subtype.ext hcomm.symm
  apply hkw
  rw [← map_mul, ← map_mul, h1]

end Lift

end HSRuLoc

end CFSG.Quasithin
