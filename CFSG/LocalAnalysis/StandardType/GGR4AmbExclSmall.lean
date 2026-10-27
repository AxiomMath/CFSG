module

public import CFSG.LocalAnalysis.StandardType.GGR4JMeetKGDefs
public import CFSG.LocalAnalysis.StandardType.GGR4ActionHom
public import CFSG.LocalAnalysis.StandardType.Marking
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyDichotomy

public section

namespace CFSG.StandardType

open CFSG.Assembly

theorem ggR4AmbExcl_small (hM10 : GGSmallThreeRank) :
    GGR4AmbExcl fun lab => lab.tag = .G2 ∨ lab.tag = .triD4 ∨ lab.tag = .twB2 ∨
      lab.tag = .twF4 ∨ lab.tag = .B2der ∨ lab.tag = .G2der ∨ lab.tag = .twF4der := by
  intro G _ _ B Bs x L D J hCfg _ hCard _ Γ _ _ C V _ _ ι φ h α hD hF4 hGen hmark
  obtain ⟨hperf, lab, hlab, hraw⟩ := hmark
  have hT : lab.tag = .G2 ∨ lab.tag = .triD4 ∨ lab.tag = .twB2 ∨ lab.tag = .twF4 ∨
      lab.tag = .B2der ∨ lab.tag = .G2der ∨ lab.tag = .twF4der :=
    GGDichotomy.rawDatum_elim_const (largeEvenRawDatum_mono (fun R _ I F hq => by
      obtain ⟨-, -, -, hT, -⟩ := hq
      exact hT) hraw)
  obtain ⟨R, _, I, F, ⟨_, _, θ, _, hBsN, hBs3⟩, hA⟩ :=
    largeEvenRawDatum_exists (hM10 lab hlab hT _ hraw)
  obtain ⟨ρ, hρI, -, hρk⟩ := ggR4_actionHom hCfg hperf θ hBsN hBs3
  let ψ : ↥Bs →* MulAut R := ρ.comp (Subgroup.inclusion hBsN)
  have hBsEa : IsElemAbelian 3 Bs := hCfg.tableB_facts.2.1
  have hxBs : x ∈ Bs := hCfg.tableB_facts.2.2.1
  have hψI : ∀ a ∈ ψ.range, a ∈ I := by
    intro a ha
    obtain ⟨b, rfl⟩ := MonoidHom.mem_range.mp ha
    exact hρI (b : G) b.2
  have hψEa : IsElemAbelian 3 ψ.range := by
    refine ⟨?_, ?_⟩
    · refine ⟨⟨fun a b => ?_⟩⟩
      obtain ⟨x, hx⟩ := MonoidHom.mem_range.mp a.2
      obtain ⟨y, hy⟩ := MonoidHom.mem_range.mp b.2
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hx, ← hy, ← map_mul, ← map_mul]
      exact congrArg ψ (Subtype.ext (CFSG.Open.IsElemAbelian.comm hBsEa x.2 y.2))
    · intro a ha
      obtain ⟨b, rfl⟩ := MonoidHom.mem_range.mp ha
      have hb3 : b ^ 3 = 1 := by
        apply Subtype.ext
        simpa using hBsEa.2 (b : G) b.2
      rw [← map_pow, hb3, map_one]
  have hker : ψ.ker = (Subgroup.zpowers x).subgroupOf Bs := by
    ext b
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    change ρ (Subgroup.inclusion hBsN b) = 1 ↔ (b : G) ∈ Subgroup.zpowers x
    exact hρk (b : G) b.2
  have hzple : Subgroup.zpowers x ≤ Bs := Subgroup.zpowers_le.mpr hxBs
  have hkerz : Nat.card ↥((Subgroup.zpowers x).subgroupOf Bs) = 3 := by
    rw [← Subgroup.card_subtype Bs ((Subgroup.zpowers x).subgroupOf Bs),
      Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hzple, Nat.card_zpowers,
      hCfg.orderOf_x]
  have hcardrange : Nat.card ψ.range = 3 ^ 4 := by
    have h := Subgroup.card_ker_mul_card_range ψ
    rw [hker, hkerz, hCard] at h
    norm_num at h ⊢
    omega
  have hle := hA ψ.range hψI hψEa
  rw [hcardrange] at hle
  norm_num at hle

end CFSG.StandardType

end
