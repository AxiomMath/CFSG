module

public import CFSG.Sporadic.MI301.Frame
import CFSG.Sporadic.Bridge.Co1Surj
import CFSG.LocalAnalysis.GLTheoremA.CatB.CfgILayer
import CFSG.LocalAnalysis.GLTheoremA.CatB.H301LayerQuot
public import CFSG.Sporadic.Co1

public section

namespace CFSG.Sporadic.MI301

open CFSG.Monster.GMS CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA
  CFSG.LocalAnalysis.GLTheoremA.S8 CFSG.Blueprint


section Generic


variable {G H : Type} [Group G] [Finite G] [Group H] {p : ℕ}

private theorem center_eq_bot_of_mulEquiv_simple {M : Type} [Group M] (e : M ≃* H)
    (hs : IsSimpleGroup H) (hn : ∃ a b : H, a * b ≠ b * a) : Subgroup.center M = ⊥ := by
  haveI : IsSimpleGroup M := e.isSimpleGroup
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center M) with h | h
  · exact h
  · obtain ⟨a, b, hab⟩ := hn
    have hb : e.symm b ∈ Subgroup.center M := h ▸ Subgroup.mem_top _
    exact absurd (by simpa using congrArg e (Subgroup.mem_center_iff.1 hb (e.symm a))) hab

private theorem glaPComponent_glaPLayer_of_surjective {C : Subgroup G} (hp : p.Prime)
    (φ : ↥C →* H) (hφ : Function.Surjective φ) (hN : ¬ p ∣ Nat.card φ.ker)
    (hs : IsSimpleGroup H) (hn : ∃ a b : H, a * b ≠ b * a) (hpH : p ∣ Nat.card H) :
    GLAPComponent p C (GLAPLayer p C) ∧ Nonempty (PSimple p (GLAPLayer p C) ≃* H) := by
  let eT : ↥(⊤ : Subgroup (↥C ⧸ φ.ker)) ≃* H :=
    Subgroup.topEquiv.trans (QuotientGroup.quotientKerEquivOfSurjective φ hφ)
  have hnab : ∃ a b : ↥(⊤ : Subgroup (↥C ⧸ φ.ker)), a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hn
    exact ⟨eT.symm a, eT.symm b, fun h' => hab (by simpa using congrArg eT h')⟩
  have hpS : p ∣ Nat.card ↥(⊤ : Subgroup (↥C ⧸ φ.ker)) := by
    rw [Nat.card_congr eT.toEquiv]
    exact hpH
  obtain ⟨e₁⟩ := H301.nonempty_pQuot_glaPLayer_of_quotient hp φ.ker hN ⊤ eT.isSimpleGroup hnab
    hpS (fun _ _ _ => Subgroup.mem_top _) le_top
  obtain ⟨e₂⟩ := H301.nonempty_pQuot_glaPLayer_subtype hp C
  let e : PQuot p (GLAPLayer p C) ≃* H := e₂.trans (e₁.trans eT)
  let eS : PSimple p (GLAPLayer p C) ≃* H :=
    (QuotientGroup.quotientMulEquivOfEq (center_eq_bot_of_mulEquiv_simple e hs hn)).trans
      (QuotientGroup.quotientBot.trans e)
  exact ⟨S8.CfgI.glaPLayer_isComponent_of_isSimple hp eS.isSimpleGroup, ⟨eS⟩⟩

end Generic

private theorem exists_mul_ne_mul_co1 : ∃ a b : NativeSporadic.Co1, a * b ≠ b * a := by
  by_contra hc
  haveI : IsMulCommutative NativeSporadic.Co1 :=
    ⟨⟨fun a b => not_not.1 fun hab => hc ⟨a, b, hab⟩⟩⟩
  have h := Group.is_simple_iff_prime_card.mp CFSG.Sporadic.Co1.isSimpleGroup_Co1
  rw [CFSG.Sporadic.Co1.card_Co1] at h
  norm_num at h

theorem leech_hNL {G : Type} [Group G] [Finite G] {z : G} (h : GMSLeechCentralizer z) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpC : p ∣ Nat.card CFSG.Blueprint.NativeSporadic.Co1) :
    ∃ J₀ : Subgroup G, GLAPComponent p (Subgroup.normalizer (leechQ z : Set G)) J₀ ∧
      catalogIs (PSimple p J₀) (sporIs .Co1) := by
  rw [normalizer_leechQ h]
  obtain ⟨-, -, hcard, ⟨φ, hφ, hker⟩, -⟩ := h
  have hN : ¬ p ∣ Nat.card φ.ker := by
    rw [hker, hcard]
    exact fun hd => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hd))
  obtain ⟨hJ, ⟨eS⟩⟩ := glaPComponent_glaPLayer_of_surjective hp φ hφ hN
    CFSG.Sporadic.Co1.isSimpleGroup_Co1 exists_mul_ne_mul_co1 hpC
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.Co1.nonempty_mulEquiv
  exact ⟨_, hJ, .sporadic .Co1, rfl, ⟨eS.trans b⟩⟩

end CFSG.Sporadic.MI301
