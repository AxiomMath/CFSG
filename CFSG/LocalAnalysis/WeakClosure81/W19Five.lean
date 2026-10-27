module

public import CFSG.LocalAnalysis.WeakClosure81.W19Struct
public import CFSG.LocalAnalysis.WeakClosure81.W19Basic

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

namespace MinCex193

variable {D : Data G} {V₀ V : Subgroup G} {p : ℕ} {X : Subgroup G}

theorem exists_mem_normalizer_Z (c : MinCex193 D V₀ V p X) :
    ∃ g : G, g ∈ normalizer (Z193 D V : Set G) ∧ g ∉ D.M := by
  have h : ¬ normalizer (Z193 D V : Set G) ≤ D.M := fun h => c.fail (Or.inr h)
  obtain ⟨g, hg, hgM⟩ := SetLike.not_le_iff_exists.1 h
  exact ⟨g, hg, hgM⟩

theorem not_dvd_card_inf_centralizer_cClos (c : MinCex193 D V₀ V p X) :
    ¬ p ∣ Nat.card ↥((X ⊔ D.T) ⊓ centralizer (E3.cClos V 1 D.T : Set G)) := by
  haveI : Fact p.Prime := ⟨c.hyp.prime⟩
  obtain ⟨g, hgZ, hgM⟩ := c.exists_mem_normalizer_Z
  obtain ⟨v, hv⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 c.inf_Z193_ne_bot
  have hvV₀ : (v : G) ∈ V₀ := (Subgroup.mem_inf.1 v.2).1
  have hvZ : (v : G) ∈ Z193 D V := (Subgroup.mem_inf.1 v.2).2
  have hv1 : (v : G) ≠ 1 := fun h => hv (Subtype.ext h)
  set w : G := g⁻¹ * v * g with hw
  have hw1 : w ≠ 1 := by
    intro h
    apply hv1
    have : g * (g⁻¹ * (v : G) * g) * g⁻¹ = 1 := by rw [← hw, h]; group
    simpa [mul_assoc] using this
  have hwV₀ : w ∈ conjSubgroup V₀ g := by
    rw [mem_conjSubgroup_iff]
    have e : g * w * g⁻¹ = (v : G) := by rw [hw]; group
    rw [e]
    exact hvV₀
  have hwZ : w ∈ Z193 D V := by
    have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hgZ) (v : G)).1 hvZ
    simpa [hw] using this
  have hwC : w ∈ E3.cClos V 1 D.T := c.Z193_le_cClos hwZ
  have hV₀W : V₀ ≤ E3.wClos V 1 D.T := c.V₀_le_V.trans c.V_le_wClos
  have hV₀cent : V₀ ≤ centralizer ({w} : Set G) := by
    intro u hu
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact ((Subgroup.mem_centralizer_iff.1 hwC.2) u (hV₀W hu)).symm
  have hcent : centralizer ({w} : Set G) ≤ conjSubgroup D.M g :=
    centralizer_le_conj_M c.setting c.ne_bot g hwV₀ hw1
  have hV₀M : V₀ ≤ conjSubgroup D.M g := hV₀cent.trans hcent
  intro hdvd
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card'
    (G := ↥((X ⊔ D.T) ⊓ centralizer (E3.cClos V 1 D.T : Set G))) p hdvd
  have hxmem : (x : G) ∈ (X ⊔ D.T) ⊓ centralizer (E3.cClos V 1 D.T : Set G) := x.2
  have hxH : (x : G) ∈ X ⊔ D.T := (Subgroup.mem_inf.1 hxmem).1
  have hxC : (x : G) ∈ centralizer (E3.cClos V 1 D.T : Set G) := (Subgroup.mem_inf.1 hxmem).2
  have hxw : (x : G) ∈ conjSubgroup D.M g := by
    apply hcent
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact (Subgroup.mem_centralizer_iff.1 hxC) w hwC
  have hox : orderOf (x : G) = p := by rw [Subgroup.orderOf_coe]; exact hx
  have hP : IsPGroup p (Subgroup.zpowers (x : G)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hox, pow_one])
  have hzH : Subgroup.zpowers (x : G) ≤ X ⊔ D.T := (Subgroup.zpowers_le).2 hxH
  have hbot := c.hyp.inf_conj_M_eq_bot (c.setting.normalizer₀ c.ne_bot).ge hzH hP hgM hV₀M
  have hx1 : (x : G) = 1 := by
    have : (x : G) ∈ Subgroup.zpowers (x : G) ⊓ conjSubgroup D.M g :=
      Subgroup.mem_inf.2 ⟨Subgroup.mem_zpowers _, hxw⟩
    rw [hbot, Subgroup.mem_bot] at this
    exact this
  rw [hx1, orderOf_one] at hox
  exact c.hyp.prime.one_lt.ne hox

end MinCex193

end CFSG.LocalAnalysis.WeakClosure81
