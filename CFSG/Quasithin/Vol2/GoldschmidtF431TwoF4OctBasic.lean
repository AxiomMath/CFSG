module

public import CFSG.Quasithin.Vol2.GoldschmidtF431TwoF4OctConj
public import CFSG.Quasithin.Vol2.GoldschmidtF431TwoF4OctSpec
public import CFSG.LocalAnalysis.EvenBN.TwoF4.ModelLeviWeyl

public section

namespace CFSG.Quasithin.H13.F431.TwoF4

open CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag CFSG.LieType.Chevalley CFSG.Blueprint
  CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.EvenBN.TwoF4

set_option linter.unusedSectionVars false


variable {K : Type} [Field K] [Finite K] [CharP K F4.prime] {a : ℕ}

theorem mem_octH_iff {x : Gm K a} : x ∈ octH K a ↔ (x : ModGL F4.tag K) ∈ F4.reeFixedTorus K a :=
  Iff.rfl

theorem octComm : OctComm K a := by
  intro x hx y hy
  exact Subtype.ext (reeFixedTorus_mul_comm hx hy)

theorem octUH : OctUH K a := by
  unfold OctUH
  rw [eq_bot_iff]
  intro x hx
  have h := reeFixed_mul_unique (t := F4) (K := K) (a := a) (h₁ := (x : ModGL F4.tag K)) (h₂ := 1)
    (u₁ := 1) (u₂ := (x : ModGL F4.tag K)) hx.2 (one_mem _) (one_mem _) hx.1
    (by rw [mul_one, one_mul])
  exact Subtype.ext h.1

theorem octConj₁ (hK : Nat.card K = 2 ^ (2 * a + 1)) : OctConj₁ K a := by
  intro h hh
  have hT : (h : ModGL F4.tag K) ∈ torusH K a := by
    rw [torusH_eq_reeFixedTorus hK]
    exact hh
  have := (Subgroup.mem_normalizer_iff.1 (weylR_mem_normalizer_torusH (K := K) (a := a) hK)
    (h : ModGL F4.tag K)).1 hT
  rw [mem_octH_iff, ← torusH_eq_reeFixedTorus hK]
  exact this

theorem octConj₂ (hK : Nat.card K = 2 ^ (2 * a + 1)) : OctConj₂ K a := by
  intro h hh
  have hT : (h : ModGL F4.tag K) ∈ torusH K a := by
    rw [torusH_eq_reeFixedTorus hK]
    exact hh
  have := (Subgroup.mem_normalizer_iff.1 (weylS_mem_normalizer_torusH (K := K) (a := a) hK)
    (h : ModGL F4.tag K)).1 hT
  rw [mem_octH_iff, ← torusH_eq_reeFixedTorus hK]
  exact this

theorem octSq₁ : OctSq₁ K a := by
  have : octR1 K a * octR1 K a = 1 := Subtype.ext (weylR_mul_self (K := K))
  unfold OctSq₁
  rw [this]
  exact one_mem _

theorem octSq₂ : OctSq₂ K a := by
  have : octR2 K a * octR2 K a = 1 := Subtype.ext (weylS_mul_self (K := K))
  unfold OctSq₂
  rw [this]
  exact one_mem _

theorem octPow : OctPow K a := by
  have h1 : (weylS K * weylR K) ^ 8 = 1 := by
    have := pow_orderOf_eq_one (weylS K * weylR K)
    rwa [orderOf_weylS_mul_weylR] at this
  have e : weylR K * weylS K = (weylS K * weylR K)⁻¹ := by
    rw [mul_inv_rev, ← eq_inv_of_mul_eq_one_left (weylR_mul_self (K := K)),
      ← eq_inv_of_mul_eq_one_left (weylS_mul_self (K := K))]
  have : (octR1 K a * octR2 K a) ^ 8 = 1 := by
    apply Subtype.ext
    change (weylR K * weylS K) ^ 8 = 1
    rw [e, inv_pow, h1, inv_one]
  unfold OctPow
  rw [this]
  exact one_mem _

theorem octInv (hK : Nat.card K = 2 ^ (2 * a + 1)) : OctInv K a := by
  intro i hi h hh x hx
  obtain ⟨h0, hle⟩ := hi
  have hk : i ∈ octKeys := mem_octKeys_iff.2 (by omega)
  have hT : (h : ModGL F4.tag K) ∈ torusH K a := by
    rw [torusH_eq_reeFixedTorus hK]
    exact hh
  exact (Subgroup.mem_normalizer_iff.1 (torusH_le_normalizer_rootSpan_inf hK (S := octBlock i)
    (fun α hα => isRoot_of_mem_octBlock hk hα) hT) (x : ModGL F4.tag K)).1 hx

section Cert117


theorem octNilp : OctNilp K a := by
  have h := isNilpotent_reeFixedPosUnipotent (t := F4) (K := K) (a := a)
  exact Group.nilpotent_of_mulEquiv
    (Subgroup.subgroupOfEquivOfLe
      (reeFixedPosUnipotent_le_reeGamma (t := F4) (K := K) (a := a))).symm

theorem octNeBot : OctNeBot K a := by
  intro i hi
  obtain ⟨h0, hle⟩ := hi
  have hk : i ∈ octKeys := mem_octKeys_iff.2 (by omega)
  obtain ⟨w, hw, j, hQ⟩ := octBlock_mem_largeReeBlocks hk
  have h1 := largeReeBlockGroup_ne_bot K a hw j
  rw [← hQ] at h1
  intro hbot
  apply h1
  rw [eq_bot_iff]
  intro g hg
  have hgΓ : g ∈ F4.reeGamma K a := (Subgroup.mem_inf.1 hg).2
  have hmem : (⟨g, hgΓ⟩ : Gm K a) ∈ octRoot K a i := hg
  rw [hbot, Subgroup.mem_bot] at hmem
  exact Subgroup.mem_bot.2 (congrArg Subtype.val hmem)

end Cert117

end CFSG.Quasithin.H13.F431.TwoF4
