module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section1

namespace CFSG
end CFSG
open CFSG

/-!
# An odd-core inversion helper

This lower-layer helper proves a valid odd-core specialization of the
fixed-point-free inversion argument.  It predates the source correction for
Lemma 2.3(ii): the paper's actual subgroup there is
`O_{π(F(Ĥ))ᶜ}(F(M))`, not `oddCoreOf M`.  The corrected owner uses the
generic endpoint in `Section2/InvolutionInvertsOfDisjointHhat`.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

private theorem oddCore_normal_in_local
    {G : Type u} [Group G] (M : Subgroup G) :
    IsNormalIn (oddCoreOf M) M := by
  refine ⟨?_, ?_⟩
  · intro k hk
    rcases Subgroup.mem_map.mp hk with ⟨p, _hp, rfl⟩
    exact (p : ↥M).2
  · intro h hh k hk
    rcases Subgroup.mem_map.mp hk with ⟨p, _hp, rfl⟩
    have hpM : (p : ↥M) ∈ pPrimeCore 2 M := _hp
    have hnorm : (⟨h, hh⟩ : ↥M) * (p : ↥M) * (⟨h, hh⟩ : ↥M)⁻¹ ∈
        pPrimeCore 2 M :=
      (pPrimeCore_normal (p := 2) (G := M)).conj_mem
        (p : ↥M) hpM (⟨h, hh⟩ : ↥M)
    exact Subgroup.mem_map.mpr
      ⟨(⟨h, hh⟩ : ↥M) * (p : ↥M) * (⟨h, hh⟩ : ↥M)⁻¹, hnorm, by simp⟩

/-- If the odd core of `M` is disjoint from `Hhat`, then an involution `t`
lying in `M` inverts that odd core whenever `Hhat` contains `C_G(t)`.

This is a general utility, not the source-corrected statement of Lemma 2.3(ii). -/
public theorem oddCore_inversion_of_disjoint
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (M : Subgroup G)
    (hcore : oddCoreOf M ⊓ c.Hhat = ⊥) :
    c.t ∈ M → ∀ x : G, x ∈ (oddCoreOf M : Set G) →
      c.t * x * c.t⁻¹ = x⁻¹ := by
  classical
  intro htM x hx
  let D : Subgroup G := oddCoreOf M
  have hx' : x ∈ D := by simpa [D] using hx
  have hcop : Nat.Coprime 2 (Nat.card ↥D) := by
    dsimp [D, oddCoreOf]
    rw [Subgroup.card_subtype]
    exact pPrimeCore_coprime_card (p := 2) (G := M)
  have hD_normal : IsNormalIn D M := by
    simpa [D] using oddCore_normal_in_local (G := G) M
  have htD : ∀ y : G, y ∈ D → c.t * y * c.t⁻¹ ∈ D :=
    fun y hy => hD_normal.2 c.t htM y hy
  have hcD : ∀ y : G, y ∈ D → c.t * y * c.t⁻¹ = y → y = 1 := by
    intro y hy hfix
    have hcent : y ∈ Subgroup.centralizer ({c.t} : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      have hzt : z = c.t := by simpa using hz
      rw [hzt]
      calc
        c.t * y = (c.t * y * c.t⁻¹) * c.t := by group
        _ = y * c.t := by rw [hfix]
    have hH : y ∈ c.H := by
      rw [c.H_eq_centralizer]
      exact hcent
    have hmem : y ∈ D ⊓ c.Hhat := ⟨hy, c.H_le_Hhat hH⟩
    have hbot : y ∈ (⊥ : Subgroup G) := by
      rw [← hcore]
      simpa [D] using hmem
    exact Subgroup.mem_bot.mp hbot
  rcases fact_1_5_ii_decomposition (X := D) (s := c.t)
      c.t_involution hcop htD x hx' with
    ⟨c₀, hc₀C, i, hiI, hxi⟩
  have hc₀fix : c.t * c₀ * c.t⁻¹ = c₀ := by
    have hct : c.t * c₀ = c₀ * c.t :=
      (Subgroup.mem_centralizer_iff (g := c₀)
        (s := ({c.t} : Set G))).1 hc₀C.2 c.t (by simp)
    calc
      c.t * c₀ * c.t⁻¹ = (c₀ * c.t) * c.t⁻¹ := by rw [hct]
      _ = c₀ := by group
  have hc₀₁ : c₀ = 1 := hcD c₀ hc₀C.1 hc₀fix
  have hx_i : x = i := by
    calc
      x = c₀ * i := hxi
      _ = i := by rw [hc₀₁]; simp
  calc
    c.t * x * c.t⁻¹ = c.t * (c₀ * i) * c.t⁻¹ := by rw [hxi]
    _ = c.t * i * c.t⁻¹ := by rw [hc₀₁]; simp
    _ = i⁻¹ := hiI.2
    _ = x⁻¹ := by rw [hx_i]

end CFSG.GorensteinWalter
