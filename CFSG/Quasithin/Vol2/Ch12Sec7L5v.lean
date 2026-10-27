module

public import CFSG.Quasithin.Vol2.Ch12Sec7L5d
public import CFSG.Quasithin.Vol2.Ch12Sec7ModH

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin

namespace S127

variable {G : Type} [Group G]

@[expose] def K714 (V : Subgroup G) (z : G) : Subgroup G :=
  conjClosure V (Subgroup.centralizer ({z} : Set G))

@[expose] def U714 (T L V : Subgroup G) (z : G) : Subgroup G :=
  conjClosure (V1 T L V) (K714 V z)

end S127

open S127

@[expose] def Ident12714R1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (t : G), Setting1273 G T L V t →
    ∀ z ∈ V1 T L V, z ≠ 1 → T ≤ Subgroup.centralizer ({z} : Set G) →
    ¬ V ≤ pCoreOf 2 (Subgroup.centralizer ({z} : Set G)) →
    autOn (U714 T L V z) V = autOn (R1 T L V) V →
      orderOf z = 2 ∧ Nonempty (↥(Subgroup.centralizer ({z} : Set G)) ≃* ↥(Subgroup.centralizer
        ({transvection15} : Set (Matrix.SpecialLinearGroup (Fin 5) (ZMod 2))))) ∧
      ∃ g : G, g⁻¹ * z * g ∈ pCoreOf 2 (Subgroup.centralizer ({z} : Set G)) ∧ g⁻¹ * z * g ≠ z

@[expose] def Ident12714R2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (t : G), Setting1273 G T L V t →
    ∀ z ∈ V1 T L V, z ≠ 1 → T ≤ Subgroup.centralizer ({z} : Set G) →
    ¬ V ≤ pCoreOf 2 (Subgroup.centralizer ({z} : Set G)) →
    autOn (U714 T L V z) V ≠ autOn (R1 T L V) V → False

open CFSG.LieType.BorelTits in
theorem ident12714_of (h74 : Lemma12_7_4) (hR1 : Ident12714R1) (hR2 : Ident12714R2) :
    Ident12714 := by
  intro G _ _ T L V h t ht h18 z hz h45 hGt hVz
  have hS : Setting1273 G T L V t := ⟨h, ht, h18, hGt⟩
  obtain ⟨⟨z₀, hz₀V1, hz₀1, hTz₀, t₀, -, -, -, h18₀, horb⟩, -⟩ := h74 G T L V h
  have hz1 : z ≠ 1 := S127.ne_one_of_relIndex h45 (by decide)
  obtain ⟨l, hlL, hlz⟩ : ∃ l ∈ L, l * z * l⁻¹ = z₀ := by
    rcases horb z hz hz1 with h1 | ⟨l, hl, hlt⟩
    · exact h1
    · exfalso
      have e := S127.L5.relIndex_centralizer_conj (Subgroup.le_normalizer hl) z
      rw [hlt, h18₀, h45] at e
      norm_num at e
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := S127.Mod.L_le_normalizer h
  have hC : Subgroup.centralizer ({z₀} : Set G) =
      (Subgroup.centralizer ({z} : Set G)).map (MulAut.conj l).toMonoidHom := by
    rw [← hlz]
    exact S127.L5.centralizer_conj l z
  have hO : pCoreOf 2 (Subgroup.centralizer ({z₀} : Set G)) =
      (pCoreOf 2 (Subgroup.centralizer ({z} : Set G))).map (MulAut.conj l).toMonoidHom := by
    rw [hC]
    exact pCoreOf_map_mulEquiv 2 (MulAut.conj l) _
  have hVz₀ : ¬ V ≤ pCoreOf 2 (Subgroup.centralizer ({z₀} : Set G)) := by
    intro hle
    apply hVz
    have hVl : V.map (MulAut.conj l).toMonoidHom = V := S127.L5.map_conj_eq (hLV hlL)
    rw [hO, ← hVl] at hle
    exact (Subgroup.map_le_map_iff_of_injective (MulAut.conj l).injective).mp hle
  by_cases hU : autOn (U714 T L V z₀) V = autOn (R1 T L V) V
  · obtain ⟨ho, ⟨e⟩, g, hg1, hg2⟩ := hR1 G T L V t hS z₀ hz₀V1 hz₀1 hTz₀ hVz₀ hU
    refine ⟨?_, ⟨?_⟩, l⁻¹ * g * l, ?_, ?_⟩
    · have hord : orderOf (l * z * l⁻¹) = orderOf z := by
        simpa [MulAut.conj_apply] using
          orderOf_injective (MulAut.conj l).toMonoidHom (MulAut.conj l).injective z
      rw [← ho, ← hlz, hord]
    · exact (((Subgroup.centralizer ({z} : Set G)).equivMapOfInjective
        (MulAut.conj l).toMonoidHom (MulAut.conj l).injective).trans
        (MulEquiv.subgroupCongr hC.symm)).trans e
    · have hmem : g⁻¹ * z₀ * g ∈
          (pCoreOf 2 (Subgroup.centralizer ({z} : Set G))).map (MulAut.conj l).toMonoidHom :=
        hO ▸ hg1
      obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hmem
      have e2 : (l⁻¹ * g * l)⁻¹ * z * (l⁻¹ * g * l) = y := by
        have hyx' : l * y * l⁻¹ = g⁻¹ * z₀ * g := hyx
        rw [← hlz] at hyx'
        calc (l⁻¹ * g * l)⁻¹ * z * (l⁻¹ * g * l)
            = l⁻¹ * (g⁻¹ * (l * z * l⁻¹) * g) * l := by group
          _ = l⁻¹ * (l * y * l⁻¹) * l := by rw [hyx']
          _ = y := by group
      rw [e2]
      exact hy
    · intro heq
      apply hg2
      calc g⁻¹ * z₀ * g = l * ((l⁻¹ * g * l)⁻¹ * z * (l⁻¹ * g * l)) * l⁻¹ := by
            rw [← hlz]
            group
        _ = l * z * l⁻¹ := by rw [heq]
        _ = z₀ := hlz
  · exact (hR2 G T L V t hS z₀ hz₀V1 hz₀1 hTz₀ hVz₀ hU).elim

end CFSG.Quasithin.H13
