module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.CriticalDistanceGeometry.L3YC.Setting
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.CriticalDistanceGeometry.L3YC.LemmaA
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.L3YC.L3YCF56

public section

open CFSG.QuasithinUnique (quasithinIsQTKECat)

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.S1417 CFSG.Quasithin.SBd7
  CFSG.Quasithin.S153D
open scoped commutatorElement Pointwise

namespace Stellmacher.CD.L3YC

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem card_inf_centralizer_eq_two {V' W V S : Subgroup G} {a b : G} (ha : a ∈ V') (ha1 : a ≠ 1)
    (ha2 : a * a = 1) (haS : ∀ s ∈ S, s * a = a * s) (hVW : V' ⊓ W = ⊥) (hb : b ∈ W) (hb1 : b ≠ 1)
    (hV' : V' ≤ V)
    (hZ : ∀ v ∈ V, (∀ s ∈ S, s * v = v * s) → v = 1 ∨ v = a ∨ v = b ∨ v = a * b ∨ v = b * a) :
    Nat.card ↥(V' ⊓ Subgroup.centralizer (S : Set G)) = 2 := by
  have hbV' : b ∈ V' → False := fun h => hb1 (by
    have : b ∈ V' ⊓ W := ⟨h, hb⟩
    rwa [hVW, Subgroup.mem_bot] at this)
  have hK : V' ⊓ Subgroup.centralizer (S : Set G) = Subgroup.zpowers a := by
    apply le_antisymm
    · rintro v ⟨hv, hvS⟩
      have hvS' : ∀ s ∈ S, s * v = v * s := fun s hs =>
        Subgroup.mem_centralizer_iff.mp hvS s hs
      rcases hZ v (hV' hv) hvS' with h | h | h | h | h
      · rw [h]; exact Subgroup.one_mem _
      · rw [h]; exact Subgroup.mem_zpowers a
      · exact (hbV' (h ▸ hv)).elim
      · exfalso
        apply hbV'
        have : b = a⁻¹ * v := by rw [h]; group
        rw [this]
        exact V'.mul_mem (V'.inv_mem ha) hv
      · exfalso
        apply hbV'
        have : b = v * a⁻¹ := by rw [h]; group
        rw [this]
        exact V'.mul_mem hv (V'.inv_mem ha)
    · rw [Subgroup.zpowers_le]
      exact ⟨ha, Subgroup.mem_centralizer_iff.mpr fun s hs => haS s hs⟩
  rw [hK, Nat.card_zpowers, orderOf_eq_prime (by rwa [pow_two]) ha1]

theorem bad_case_rows (h11 : StageLemma14111) (h113 : StageLemma14113) (hQ : quasithinIsQTKECat G)
    (hs : IsSimpleGroup G) (hnab : ∃ a b : G, a * b ≠ b * a) (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (h39 : A39ForSQTK) (h312 : A312ForSQTK) {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}
    (c : Ctx15316 T Mc M V₁ V₂ Yp I L t) (hq : IsLnTwoQuot L 3) (c12 : Concl15312Two Yp L)
    (hV : ⁅VZ T M, YL153 Yp L⁆ ≠ ⊥) (hYY : Yp = Y153 Mc M)
    (hSL : Sgp153 T V₁ ≤ Subgroup.normalizer (L : Set G))
    {t' : G} (ht'T : t' ∈ T) (ht'S : t' ∉ Sgp153 T V₁)
    (hswap : B6.conjSub t' (YL153 Yp L) = YC153 Yp L)
    (h4 : MS93.IsC134Case4Corr (L ⊔ Sgp153 T V₁) (Sgp153 T V₁) L) :
    ∃ c₀ : G, c₀ ≠ 1 ∧ c₀ * c₀ = 1 ∧ c₀ ∈ c134CQ (L ⊔ Sgp153 T V₁) L ∧
      L ≤ Subgroup.centralizer ({c₀} : Set G) ∧
      IsSylowTwoOf (Sgp153 T V₁) (Subgroup.centralizer ({c₀} : Set G)) ∧
      (¬ Subgroup.centralizer ({c₀} : Set G) ≤ Subgroup.normalizer (L : Set G) →
        ∃ L₁ ∈ cComp (Subgroup.centralizer ({c₀} : Set G)), L ≤ L₁ ∧
          (A312Case (modO2Image (Subgroup.centralizer ({c₀} : Set G)) L)
              (modO2Image (Subgroup.centralizer ({c₀} : Set G)) L₁) ∨
            A312Nonquasi (modO2Image (Subgroup.centralizer ({c₀} : Set G)) L)
              (modO2Image (Subgroup.centralizer ({c₀} : Set G)) L₁))) := by
  classical
  obtain ⟨Vc, Vn, c₀, u₀, hlabel, hc₀Q, -, hc₀V, hu₀V, hc₀1, hu₀1, hc₀2, hu₀2, hS, hsw, hsw', hZ⟩ :=
    Stellmacher.PU.L3YC.pu_f5_f6 h113 h37 h38 c hq c12 hV hYY hSL ht'T ht'S hswap h4
  have hh : Hyp15310 G T Mc M V₁ V₂ Yp t := c.ctx.hyp
  have hyp : Hyp153 G T Mc M := hh.hyp
  have hD := hh.decomp
  have hTS : T ≤ Subgroup.normalizer (Sgp153 T V₁ : Set G) :=
    Hyp153.T_le_normalizer_Sgp153 hyp hD
  have hLc : L ≤ Subgroup.centralizer ({c₀} : Set G) := by
    intro l hl
    rw [Subgroup.mem_centralizer_iff]
    intro h hh'
    rw [Set.mem_singleton_iff] at hh'
    rw [hh']
    exact (Subgroup.mem_centralizer_iff.mp hc₀Q.2 l hl).symm
  have hcen : ∀ x : G, (∀ s ∈ Sgp153 T V₁, s * x = x * s) →
      x ∈ Subgroup.centralizer ((Sgp153 T V₁ : Subgroup G) : Set G) := fun x hx =>
    Subgroup.mem_centralizer_iff.mpr fun s hs => hx s hs
  have hSyl : IsSylowTwoOf (Sgp153 T V₁) (Subgroup.centralizer ({c₀} : Set G)) := by
    rcases hlabel with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · subst h1 h2
      have hcard := card_inf_centralizer_eq_two (W := Vn) hc₀V hc₀1 hc₀2 (fun s hs => (hS s hs).1)
        hD.inf hu₀V hu₀1 hD.le₁ (fun v hv hvS => by
          rcases hZ v hv hvS with h | h | h | h
          · exact Or.inl h
          · exact Or.inr (Or.inl h)
          · exact Or.inr (Or.inr (Or.inl h))
          · exact Or.inr (Or.inr (Or.inr (Or.inl h))))
      exact isSylowTwoOf_centralizer_singleton h11 hyp hD hc₀V hc₀1
        (hcen c₀ fun s hs => (hS s hs).1) hcard
    · subst h1 h2
      have hinf : Vn ⊓ Vc = ⊥ := hD.inf
      have hcard := card_inf_centralizer_eq_two (W := Vc) hu₀V hu₀1 hu₀2 (fun s hs => (hS s hs).2)
        hinf hc₀V hc₀1 hD.le₁ (fun v hv hvS => by
          rcases hZ v hv hvS with h | h | h | h
          · exact Or.inl h
          · exact Or.inr (Or.inr (Or.inl h))
          · exact Or.inr (Or.inl h)
          · exact Or.inr (Or.inr (Or.inr (Or.inr h))))
      have hSylu := isSylowTwoOf_centralizer_singleton h11 hyp hD hu₀V hu₀1
        (hcen u₀ fun s hs => (hS s hs).2) hcard
      have := isSylowTwoOf_centralizer_conj hSylu (hTS ht'T)
      rwa [hsw'] at this
  refine ⟨c₀, hc₀1, hc₀2, hc₀Q, hLc, hSyl, fun hnn => ?_⟩
  exact exists_component_row_ne hQ hs hnab h37 h38 h39 h312 (pCoreOf_centralizer_ne_bot hc₀1 hc₀2)
    hSyl hLc (lFamily_of_ctx c hSL) hSL hnn

end Stellmacher.CD.L3YC

end CFSG.Quasithin
