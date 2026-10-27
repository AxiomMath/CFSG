module

public import CFSG.Quasithin.EmptyFaithful.S146zDHSide
public import CFSG.Quasithin.EmptyFaithful.S146zDEng

public section

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7 CFSG.Quasithin.CosetGeom
open scoped commutatorElement

namespace CFSG.Quasithin.ThreeD

section PartI

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G}

local notation "Zz" => quasithinOmegaOneCenter T

theorem partI (S : Setting146 G T M) (c23 : Conc14623 T M)
    {K Kp U₁ U₂ : Subgroup G} {s : G} (cK : ThreeC.CCtx T M K U₁ U₂ s)
    (hKp : Kp ∈ cComp (mcOf T)) (hcomps : ∀ L ∈ cComp (mcOf T), L = K ∨ L = Kp)
    (hkz : perfectCore (mcOf T) = K ⊔ Kp)
    (hc22K : ⁅⁅uOfL22 T M, K⁆, Kp⁆ = ⊥) (hc22Kp : ⁅⁅uOfL22 T M, Kp⁆, K⁆ = ⊥)
    {g : G} {A₁ : Subgroup G} (hA₁ : A₁ = conjSub g Zz) (hA₁c : Nat.card A₁ = 2)
    (hA₁Z : A₁ ⊓ Zz = ⊥) (hA₁UK : A₁ ≤ U₁ ⊔ U₂) :
    Kp ≤ conjSub g (mcOf T) ∧
      ∀ P : Subgroup G, P ≤ mcOf T → ⁅P, P⁆ = P → P ≤ conjSub g (mcOf T) → P ≤ Kp := by
  classical
  have hG : IsHTM T M (mcOf T) := S.isHTM_mcOf
  have hKpH : Kp ≤ mcOf T := le_of_mem_cComp hKp
  have hHN : conjSub g (mcOf T) = Subgroup.normalizer (A₁ : Set G) := by
    rw [hA₁, conjSub_normalizer, S.normalizer_Z]
  have hHZ : mcOf T ≤ Subgroup.normalizer (Zz : Set G) := fun h hh => by
    rw [S.normalizer_Z]; exact hh
  have hZc : mcOf T ≤ Subgroup.centralizer (Zz : Set G) := by
    rw [← normalizer_eq_centralizer_of_card_eq_two S.card_Z]; exact hHZ
  have hKpcent : Kp ≤ Subgroup.centralizer ((U₁ ⊔ U₂ : Subgroup G) : Set G) := by
    rw [← cK.hsup]
    refine Subgroup.le_centralizer_iff.mpr (sup_le ?_ ?_)
    · exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hc22K
    · exact fun z hz => Subgroup.mem_centralizer_iff.mpr fun k hk =>
        (Subgroup.mem_centralizer_iff.mp (hZc (hKpH hk)) z hz).symm
  have hKpN : Kp ≤ conjSub g (mcOf T) := by
    rw [hHN]
    intro k hk
    refine Subgroup.centralizer_le_normalizer _ ?_
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact Subgroup.mem_centralizer_iff.mp (hKpcent hk) a (hA₁UK ha)
  refine ⟨hKpN, fun P hPH hP hPN => ?_⟩
  obtain ⟨a₀, ha₀, huniq⟩ := (Nat.card_eq_two_iff' (1 : ↥A₁)).mp hA₁c
  have ha₀1 : (a₀ : G) ≠ 1 := fun h => ha₀ (Subtype.ext h)
  have ha₀Z : (a₀ : G) ∉ Zz := by
    intro hZ
    have : (a₀ : G) ∈ A₁ ⊓ Zz := ⟨a₀.2, hZ⟩
    rw [hA₁Z, Subgroup.mem_bot] at this
    exact ha₀1 this
  have hfix : ∀ p ∈ P, p * (a₀ : G) * p⁻¹ = a₀ := by
    intro p hp
    have hpA : p ∈ Subgroup.normalizer (A₁ : Set G) := hHN ▸ hPN hp
    have h1 : p * (a₀ : G) * p⁻¹ ∈ A₁ := (Subgroup.mem_normalizer_iff.mp hpA _).mp a₀.2
    by_contra hne
    have h2 : (⟨p * (a₀ : G) * p⁻¹, h1⟩ : ↥A₁) ≠ 1 := fun h => by
      have := congrArg Subtype.val h
      have e : p * (a₀ : G) * p⁻¹ = 1 := this
      apply ha₀1
      have e' : (a₀ : G) = p⁻¹ * (p * (a₀ : G) * p⁻¹) * p := by group
      rw [e', e]; group
    have h3 := huniq _ h2
    exact hne (congrArg Subtype.val h3)
  exact perfect_le_Kp S c23 cK hKp hcomps hkz hc22K hc22Kp (a := a₀) (hA₁UK a₀.2) ha₀Z hPH hP hfix

end PartI

end CFSG.Quasithin.ThreeD
