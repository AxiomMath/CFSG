module

public import CFSG.Quasithin.EmptyFaithful.R3c10Bnd
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsL2 IsU3)

variable {G : Type} [Group G] [Finite G]

private theorem w183tp_card_shape {L : Subgroup G} (hshape : IsL2 ↥L 2 ∨ IsU3 ↥L 2) :
    Nat.card ↥L = 60 ∨ Nat.card ↥L = 62400 := by
  rcases hshape with h | h
  · left
    have hst : StatedClassicalModel ↥L .PSL 2 2 2 :=
      CFSG.Blueprint.LieModel.statedClassicalModel h (by decide)
    obtain ⟨-, -, -, hd⟩ := CFSG.Quasithin.R3c6.psl2Data hst
    norm_num at hd
    exact hd
  · right
    have hst : StatedClassicalModel ↥L .PSU 3 2 2 :=
      CFSG.Blueprint.LieModel.statedClassicalModel h (by decide)
    obtain ⟨-, -, -, -, hd⟩ := CFSG.Quasithin.R3c6.psu3Data hst
    norm_num at hd
    exact hd

section Certified


theorem w183tp_borel_rigid {L Q : Subgroup G} (hsimple : IsSimpleGroup ↥L)
    (hnab : ∃ a ∈ L, ∃ b ∈ L, a * b ≠ b * a) (hshape : IsL2 ↥L 2 ∨ IsU3 ↥L 2)
    (hQ : IsSylowIn 2 Q L) {v : G} (hv : v ∈ Subgroup.normalizer (L : Set G)) (hv2 : v * v = 1)
    (hc : ∀ b ∈ L ⊓ Subgroup.normalizer (Q : Set G), v * b = b * v) :
    v ∈ Subgroup.centralizer (L : Set G) := by
  haveI := hsimple
  have hnab' : ∃ a b : ↥L, a * b ≠ b * a := by
    obtain ⟨a, ha, b, hb, hab⟩ := hnab
    exact ⟨⟨a, ha⟩, ⟨b, hb⟩, fun h => hab (congrArg Subtype.val h)⟩
  obtain ⟨hq, hcenterL⟩ := CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnab'
  have hcenterG : centerOf L = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    have hz : (⟨x, hx.1⟩ : ↥L) ∈ Subgroup.center ↥L :=
      CFSG.Quasithin.SBc2.mem_centerOf_iff_center.mp hx
    have hz1 : (⟨x, hx.1⟩ : ↥L) = 1 := by
      rw [← Subgroup.mem_bot, ← hcenterL]
      exact hz
    simpa using congrArg Subtype.val hz1
  have hnotp : ¬ IsPGroup 2 ↥L := by
    intro hp
    haveI : Nontrivial ↥L := by
      obtain ⟨a, ha, b, hb, hab⟩ := hnab
      exact ⟨⟨a * b, L.mul_mem ha hb⟩, ⟨b * a, L.mul_mem hb ha⟩,
        fun h => hab (congrArg Subtype.val h)⟩
    have hc' := hp.center_nontrivial
    rw [hcenterL] at hc'
    exact (Subgroup.nontrivial_iff_ne_bot ⊥).mp hc' rfl
  have hpCore : pCoreOf 2 L = ⊥ := by
    have hle : pCoreOf 2 L ≤ L := CFSG.LieType.BorelTits.pCoreOf_le 2 L
    have hnormal : ((pCoreOf 2 L).subgroupOf L).Normal :=
      Subgroup.normal_subgroupOf_of_le_normalizer
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L)
    rcases hsimple.eq_bot_or_eq_top_of_normal ((pCoreOf 2 L).subgroupOf L) with h | h
    · rw [← Subgroup.map_subgroupOf_eq_of_le hle, h, Subgroup.map_bot]
    · exfalso
      apply hnotp
      have hLP : L ≤ pCoreOf 2 L := fun x hx => by
        have h1 : (⟨x, hx⟩ : ↥L) ∈ (pCoreOf 2 L).subgroupOf L := h ▸ Subgroup.mem_top _
        exact h1
      exact (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L).to_le hLP
  have hZ : centerOf L = pCoreOf 2 L := by rw [hcenterG, hpCore]
  have hQ' : CFSG.QuasithinUnique.IsSylowTwoOf Q L := hQ
  have hY : CFSG.Quasithin.R3c8.BorelPkg (↥L ⧸ Subgroup.center ↥L) := by
    have hmul : (↥L ⧸ Subgroup.center ↥L) ≃* ↥L :=
      (QuotientGroup.quotientMulEquivOfEq hcenterL).trans QuotientGroup.quotientBot
    rcases hshape with h | h
    · apply CFSG.Quasithin.R3c10.borelPkg_psl2 (f := 2) (by norm_num)
      exact CFSG.Blueprint.LieModel.statedClassicalModel
        (CFSG.Blueprint.LieModel.of_mulEquiv hmul.symm h) (by decide)
    · apply CFSG.Quasithin.R3c8.borelPkg_psu3
      exact CFSG.Blueprint.LieModel.statedClassicalModel
        (CFSG.Blueprint.LieModel.of_mulEquiv hmul.symm h) (by decide)
  exact (CFSG.Quasithin.R3c8.borelLift_of_pkg hq hZ hQ' hY).2 v hv hv2 hc

end Certified

theorem w183tp_sylow_not_normal {L Q : Subgroup G} (hsimple : IsSimpleGroup ↥L)
    (hnab : ∃ a ∈ L, ∃ b ∈ L, a * b ≠ b * a) (hshape : IsL2 ↥L 2 ∨ IsU3 ↥L 2)
    (hQ : IsSylowIn 2 Q L) :
    Q ≠ ⊥ ∧ ¬ ∀ l ∈ L, ∀ q ∈ Q, l * q * l⁻¹ ∈ Q := by
  haveI := hsimple
  have hcard := w183tp_card_shape hshape
  have htwo : 2 ∣ Nat.card ↥L := by
    rcases hcard with h | h <;> rw [h] <;> norm_num
  have hnab' : ∃ a b : ↥L, a * b ≠ b * a := by
    obtain ⟨a, ha, b, hb, hab⟩ := hnab
    exact ⟨⟨a, ha⟩, ⟨b, hb⟩, fun h => hab (congrArg Subtype.val h)⟩
  have hcenterL : Subgroup.center ↥L = ⊥ :=
    (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnab').2
  have hnotp : ¬ IsPGroup 2 ↥L := by
    intro hp
    haveI : Nontrivial ↥L := by
      obtain ⟨a, ha, b, hb, hab⟩ := hnab
      exact ⟨⟨a * b, L.mul_mem ha hb⟩, ⟨b * a, L.mul_mem hb ha⟩,
        fun h => hab (congrArg Subtype.val h)⟩
    have hc' := hp.center_nontrivial
    rw [hcenterL] at hc'
    exact (Subgroup.nontrivial_iff_ne_bot ⊥).mp hc' rfl
  have hQne : Q ≠ ⊥ := by
    intro hbot
    have hnd : ¬ 2 ∣ (Q.subgroupOf L).index := hQ.not_dvd_relIndex
    have hindex : (Q.subgroupOf L).index = Nat.card ↥L := by
      rw [hbot, Subgroup.bot_subgroupOf]
      exact Subgroup.index_bot
    rw [hindex] at hnd
    exact hnd htwo
  refine ⟨hQne, ?_⟩
  intro hnorm
  have hleN : L ≤ Subgroup.normalizer (Q : Set G) := by
    intro l hl
    rw [Subgroup.mem_normalizer_iff]
    intro q
    exact ⟨fun hq => hnorm l hl q hq, fun hq => by
      have h := hnorm l⁻¹ (L.inv_mem hl) (l * q * l⁻¹) hq
      rwa [show l⁻¹ * (l * q * l⁻¹) * (l⁻¹)⁻¹ = q by group] at h⟩
  have hnormal : (Q.subgroupOf L).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQ.le).mpr hleN
  rcases hsimple.eq_bot_or_eq_top_of_normal (Q.subgroupOf L) with hbot | htop
  · have hQbot : Q = ⊥ := by
      rw [eq_bot_iff]
      intro q hq
      rw [Subgroup.mem_bot]
      have h1 : (⟨q, hQ.le hq⟩ : ↥L) ∈ Q.subgroupOf L := hq
      rw [hbot] at h1
      exact congrArg Subtype.val (Subgroup.mem_bot.mp h1)
    exact hQne hQbot
  · have hLQ : L ≤ Q := Subgroup.subgroupOf_eq_top.mp htop
    exact hnotp (hQ.isPGroup.to_le hLQ)

theorem w183tp_le_normalizer_inf {Y T L : Subgroup G} (hTY : T ≤ Y)
    (hLn : ∀ y ∈ Y, ∀ l ∈ L, y * l * y⁻¹ ∈ L) :
    T ≤ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G) := by
  intro t ht
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    exact ⟨T.mul_mem (T.mul_mem ht hx.1) (T.inv_mem ht), hLn t (hTY ht) x hx.2⟩
  · intro hx
    have hxT : x ∈ T := by
      have h := T.mul_mem (T.mul_mem (T.inv_mem ht) hx.1) ht
      rwa [show t⁻¹ * (t * x * t⁻¹) * t = x by group] at h
    have hxL : x ∈ L := by
      have h := hLn t⁻¹ (Y.inv_mem (hTY ht)) (t * x * t⁻¹) hx.2
      rwa [show t⁻¹ * (t * x * t⁻¹) * (t⁻¹)⁻¹ = x by group] at h
    exact ⟨hxT, hxL⟩

theorem w183tp_normalizer_ne {Y L Q : Subgroup G} (hLY : L ≤ Y)
    (hQL : ¬ ∀ l ∈ L, ∀ q ∈ Q, l * q * l⁻¹ ∈ Q) :
    Y ⊓ Subgroup.normalizer (Q : Set G) ≠ Y := by
  intro h
  apply hQL
  intro l hl q hq
  have hlY : l ∈ Y := hLY hl
  have hlN : l ∈ Y ⊓ Subgroup.normalizer (Q : Set G) := by
    rw [h]
    exact hlY
  exact (Subgroup.mem_normalizer_iff.mp hlN.2 q).mp hq

section Certified


theorem w183tp_false_one {Y T L : Subgroup G} {d : G} (hT : IsSylowIn 2 T Y) (hLY : L ≤ Y)
    (hLn : ∀ y ∈ Y, ∀ l ∈ L, y * l * y⁻¹ ∈ L) (hsimple : IsSimpleGroup ↥L)
    (hnab : ∃ a ∈ L, ∃ b ∈ L, a * b ≠ b * a)
    (hcent : ∀ y ∈ Y, (∀ l ∈ L, y * l = l * y) → y = 1) (hshape : IsL2 ↥L 2 ∨ IsU3 ↥L 2)
    (hdY : d ∈ Y) (hd1 : d ≠ 1) (hd2 : d * d = 1)
    (hX : ∀ X : Subgroup G, X ≤ Y → T ≤ X → X ≠ Y → ∀ x ∈ X, x * d = d * x) : False := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnormal : (L.subgroupOf Y).Normal := by
    refine ⟨fun n hn g => ?_⟩
    have h := hLn g g.2 n (Subgroup.mem_subgroupOf.mp hn)
    exact Subgroup.mem_subgroupOf.mpr (by simpa using h)
  have hQ : IsSylowIn 2 (T ⊓ L) L := hT.inf_normal hLY hnormal
  obtain ⟨-, hQn⟩ := w183tp_sylow_not_normal hsimple hnab hshape hQ
  have hXY : Y ⊓ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G) ≤ Y := inf_le_left
  have hTX : T ≤ Y ⊓ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G) :=
    le_inf hT.le (w183tp_le_normalizer_inf hT.le hLn)
  have hXne := w183tp_normalizer_ne (Y := Y) hLY hQn
  have hdN : d ∈ Subgroup.normalizer (L : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro l
    constructor
    · intro hl
      exact hLn d hdY l hl
    · intro hl
      have h := hLn d⁻¹ (Y.inv_mem hdY) (d * l * d⁻¹) hl
      rwa [show d⁻¹ * (d * l * d⁻¹) * (d⁻¹)⁻¹ = l by group] at h
  have hc : ∀ b ∈ L ⊓ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G), d * b = b * d := by
    intro b hb
    exact (hX _ hXY hTX hXne b ⟨hLY hb.1, hb.2⟩).symm
  have hcL := w183tp_borel_rigid hsimple hnab hshape hQ hdN hd2 hc
  exact hd1 (hcent d hdY fun l hl => (Subgroup.mem_centralizer_iff.mp hcL l hl).symm)

end Certified

end CFSG.LocalAnalysis.WeakClosure81

end
