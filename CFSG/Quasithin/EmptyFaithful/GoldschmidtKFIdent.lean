module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtKFResidue
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtHSRuLocSimple
public import CFSG.Assembly.RankThreeEvenDefs

public section

namespace CFSG.Quasithin.SBd19F

open CFSG CFSG.LocalCores CFSG.Open CFSG.Quasithin

theorem mem_cComp_of_normal_quasisimple {G : Type*} [Group G] {X L : Subgroup G} (hle : L ≤ X)
    (hN : (L.subgroupOf X).Normal) (hq : CFSG.IsQuasisimple ↥L) : L ∈ cComp X := by
  have hperf : Group.IsPerfect ↥L := hq.1
  have hnt : Nontrivial ↥L := isQuasisimple_nontrivial hq
  refine ⟨?_, ?_, A3.subnormal_of_normal hle hN, ?_⟩
  · intro hbot
    have : Subsingleton ↥L := by rw [hbot]; exact inferInstance
    exact not_subsingleton _ this
  · exact Subgroup.commutator_eq_self
  · intro K hKL hKbot hKperf hKsub
    obtain ⟨P, hPL, hPn, hKP⟩ := A3.subnormal_exists_normal_of_lt
      (A3.subnormal_of_le_of_le hKsub hKL.le hle) hKL
    have hPne : P.subgroupOf L ≠ ⊤ := fun h =>
      hPL.ne (le_antisymm hPL.le (Subgroup.subgroupOf_eq_top.mp h))
    have hPc : P.subgroupOf L ≤ Subgroup.center ↥L :=
      (quasisimple_normal_subgroups hq hPn).resolve_left hPne
    have hKc : K ≤ (Subgroup.center ↥L).map L.subtype := fun x hx =>
      ⟨⟨x, hKL.le hx⟩, hPc (Subgroup.mem_subgroupOf.mpr (hKP hx)), rfl⟩
    apply hKbot
    rw [eq_bot_iff]
    intro x hx
    have hcomm : ∀ a ∈ K, ∀ b ∈ K, a * b = b * a := by
      intro a ha b hb
      obtain ⟨a', ha', rfl⟩ := hKc ha
      obtain ⟨b', hb', rfl⟩ := hKc hb
      exact congrArg Subtype.val ((Subgroup.mem_center_iff.mp ha') b').symm
    have : x ∈ ⁅K, K⁆ := by rw [hKperf]; exact hx
    rw [Subgroup.mem_bot]
    refine (Subgroup.commutator_le (H₁ := K) (H₂ := K) (H₃ := ⊥)).mpr (fun a ha b hb => ?_) this
    rw [Subgroup.mem_bot, commutatorElement_def, hcomm a ha b hb]
    group

theorem ident_of_normal {H : Type} [Group H] [Finite H] {L₂ Lx : Subgroup H} [L₂.Normal]
    (hB : Input15338Ident) (hq₂ : CFSG.IsQuasisimple ↥L₂)
    (hlist₂ : A23List (↥L₂ ⧸ Subgroup.center ↥L₂)) (hrk₂ : CFSG.Open.pRank 3 L₂ = 2)
    (hLx : Lx ≤ L₂) (hqx : CFSG.IsQuasisimple ↥Lx)
    (hcard : Nat.card (↥Lx ⧸ Subgroup.center ↥Lx) = 168) (hZ1 : Subgroup.center ↥Lx = ⊥)
    {v : H} (hv2 : v * v = 1)
    (hvLx : ∀ l ∈ Lx, v * l = l * v)
    (hnorm : ∀ g : H, g * v = v * g → g ∈ Subgroup.normalizer (Lx : Set H)) :
    IsPSL 3 2 2 (↥L₂ ⧸ Subgroup.center ↥L₂) ∨ IsSporadic .J2 (↥L₂ ⧸ Subgroup.center ↥L₂) ∨
      IsPSL 3 7 1 (↥L₂ ⧸ Subgroup.center ↥L₂) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let ψ : H →* MulAut ↥L₂ := MulAut.conjNormal
  have hψ : ∀ (g : H) (n : ↥L₂), ((ψ g n : ↥L₂) : H) = g * n * g⁻¹ := fun g n =>
    MulAut.conjNormal_apply g n
  have hrk : CFSG.Open.pRank 3 (⊤ : Subgroup ↥L₂) = 2 := by
    rw [pRank_top_subtype]; exact hrk₂
  refine hB ↥L₂ hq₂ hlist₂ hrk (ψ v) (by rw [← map_mul, hv2, map_one]) ?_
  let Lf : Subgroup ↥L₂ := Lx.subgroupOf L₂
  have hLf_le : Lf ≤ SBd18.fixedSub (ψ v) := by
    intro x hx
    rw [SBd18.mem_fixedSub]
    apply Subtype.ext
    rw [hψ]
    have h1 := hvLx x hx
    calc v * (x : H) * v⁻¹ = (x : H) * v * v⁻¹ := by rw [h1]
      _ = x := by group
  have hLf_norm : (Lf.subgroupOf (SBd18.fixedSub (ψ v))).Normal := by
    refine ⟨fun n hn g => ?_⟩
    have hnL : ((n : ↥(SBd18.fixedSub (ψ v))) : ↥L₂) ∈ Lf := hn
    have hgfix : ψ v (g : ↥L₂) = g := (SBd18.mem_fixedSub).mp g.2
    have hgv : (g : H) * v = v * (g : H) := by
      have := congrArg Subtype.val hgfix
      rw [hψ] at this
      calc (g : H) * v = (v * (g : H) * v⁻¹) * v := by rw [this]
        _ = v * (g : H) := by group
    have hgN := hnorm _ hgv
    have hnLx : (((n : ↥(SBd18.fixedSub (ψ v))) : ↥L₂) : H) ∈ Lx := hnL
    change ((((g * n * g⁻¹ : ↥(SBd18.fixedSub (ψ v))) : ↥L₂)) : H) ∈ Lx
    exact (Subgroup.mem_normalizer_iff.mp hgN _).mp hnLx
  have hqf : CFSG.IsQuasisimple ↥Lf :=
    isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hLx).symm hqx
  refine ⟨Lf, mem_cComp_of_normal_quasisimple hLf_le hLf_norm hqf, hqf, ?_, ?_⟩
  · have h1 := Subgroup.map_center_eq (Subgroup.subgroupOfEquivOfLe hLx).symm
    rw [hZ1, Subgroup.map_bot] at h1
    exact h1.symm
  have : IsSimpleGroup (↥Lx ⧸ Subgroup.center ↥Lx) := hqx.2.1
  have h168 := HSRuLoc.Mod.isPSL_three_two_of_simple_card_168
    (H := ↥Lx ⧸ Subgroup.center ↥Lx) hcard
  let e : (↥Lx ⧸ Subgroup.center ↥Lx) ≃* (↥Lf ⧸ Subgroup.center ↥Lf) :=
    QuotientGroup.congr _ _ (Subgroup.subgroupOfEquivOfLe hLx).symm
      (Subgroup.map_center_eq (Subgroup.subgroupOfEquivOfLe hLx).symm)
  exact IsPSL.of_mulEquiv e h168

end CFSG.Quasithin.SBd19F
