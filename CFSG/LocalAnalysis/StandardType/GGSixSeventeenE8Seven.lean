module

public import CFSG.LocalAnalysis.StandardType.GGSixStepThreeCFSeventeenCases
public import CFSG.LocalAnalysis.StandardType.GGPsiDiagInnerAdj
public import CFSG.LocalAnalysis.StandardType.GGTableBStdSub

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

@[expose] def GGSixSeventeenE8SevenCentInput : Prop :=
  ∀ b : ↥(adjointGroup .E8 (GaloisField 2 1)), orderOf b = 7 →
    ∃ L : Subgroup ↥(adjointGroup .E8 (GaloisField 2 1)),
      IsComponentOf L (Subgroup.centralizer {b}) ∧
        ∀ A : Subgroup ↥(adjointGroup .E8 (GaloisField 2 1)), A ≤ Subgroup.centralizer {b} →
          A ≤ Subgroup.centralizer (L : Set ↥(adjointGroup .E8 (GaloisField 2 1))) →
            IsElemAbelian 7 A → Nat.card A ≤ 7 ^ 2

section Reduction

theorem exists_component_of_mem_bstar_E8Seven (hcent : GGSixSeventeenE8SevenCentInput)
    {G : Type} [Group G] (ψ : ↥(adjointGroup .E8 (GaloisField 2 1)) →* G)
    {G₀ : Subgroup G} (hrange : ψ.range = G₀)
    (hker : ψ.ker ≤ Subgroup.center ↥(adjointGroup .E8 (GaloisField 2 1)))
    (hC : Subgroup.centralizer (G₀ : Set G) = ⊥) {Bs : Subgroup G} (hBs : IsElemAbelian 7 Bs)
    (hdiag : ∀ c ∈ Bs,
      GGPsiInnerDiag (CFSG.LieType.Steinberg.Adjoint.e8Datum (GaloisField 2 1)) ψ c)
    {b : G} (hb : b ∈ Bs) (hb1 : b ≠ 1) :
    ∃ L₂ : Subgroup G, IsComponentOf L₂ (G₀ ⊓ Subgroup.centralizer {b}) ∧
      Nat.card (Bs ⊓ Subgroup.centralizer (L₂ : Set G) : Subgroup G) ≤ 7 ^ 2 := by
  classical
  subst hrange
  have hψ : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have hz := hker ha
    rw [center_adjointGroup_eq_bot] at hz
    exact Subgroup.mem_bot.mp hz
  have hBsG : Bs ≤ ψ.range := by
    intro c hc
    obtain ⟨g, hg, hcg⟩ := PsiDiag.Adj.exists_mem_centralizer_E8 ψ hker (hdiag c hc)
    rw [hC, Subgroup.mem_bot] at hcg
    rw [eq_inv_of_mul_eq_one_left hcg]
    exact ψ.range.inv_mem hg
  obtain ⟨b', rfl⟩ := hBsG hb
  have hb'7 : b' ^ 7 = 1 := hψ (by rw [map_pow, map_one]; exact hBs.2 _ hb)
  have hb'1 : b' ≠ 1 := fun h => hb1 (by rw [h, map_one])
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨L', hL', hA⟩ := hcent b' (orderOf_eq_prime hb'7 hb'1)
  have hmapC : (Subgroup.centralizer ({b'} : Set ↥(adjointGroup .E8 (GaloisField 2 1)))).map ψ =
      ψ.range ⊓ Subgroup.centralizer {ψ b'} := by
    ext g
    simp only [Subgroup.mem_map, Subgroup.mem_inf, MonoidHom.mem_range,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨y, rfl⟩, by rw [← map_mul, ← map_mul, hy]⟩
    · rintro ⟨⟨y, rfl⟩, hy⟩
      exact ⟨y, hψ (by rw [map_mul, map_mul]; exact hy), rfl⟩
  refine ⟨L'.map ψ, hmapC ▸ isComponentOf_map_of_injective ψ hψ hL', ?_⟩
  have hHr : Bs ⊓ Subgroup.centralizer ((L'.map ψ : Subgroup G) : Set G) ≤ ψ.range :=
    inf_le_left.trans hBsG
  have hmem : ∀ {a}, a ∈ (Bs ⊓ Subgroup.centralizer ((L'.map ψ : Subgroup G) : Set G)).comap ψ →
      ψ a ∈ Bs ∧ ψ a ∈ Subgroup.centralizer ((L'.map ψ : Subgroup G) : Set G) := fun ha =>
    Subgroup.mem_inf.mp (Subgroup.mem_comap.mp ha)
  rw [← Subgroup.map_comap_eq_self hHr, Subgroup.card_map_of_injective hψ]
  refine hA _ (fun a ha => ?_) (fun a ha => ?_) ⟨⟨⟨fun a c => Subtype.ext (hψ ?_)⟩⟩, ?_⟩
  · rw [Subgroup.mem_centralizer_singleton_iff]
    apply hψ
    rw [map_mul, map_mul]
    exact TableB.IsElemAbelian.comm hBs (hmem ha).1 hb
  · rw [Subgroup.mem_centralizer_iff]
    intro l hl
    apply hψ
    rw [map_mul, map_mul]
    exact Subgroup.mem_centralizer_iff.mp (hmem ha).2 (ψ l) (Subgroup.mem_map_of_mem ψ hl)
  · rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
    exact TableB.IsElemAbelian.comm hBs (hmem a.2).1 (hmem c.2).1
  · intro a ha
    exact hψ (by rw [map_pow, map_one]; exact hBs.2 _ (hmem ha).1)

theorem ggSixSeventeenE8SevenInput_of_cent (hcent : GGSixSeventeenE8SevenCentInput) :
    GGSixSeventeenE8SevenInput := by
  intro G _ _ p B Bs x L D J t n f ψ ht hf hp hctx s1 b L₁ hpair
  subst ht hf hp
  exact exists_component_of_mem_bstar_E8Seven hcent ψ hctx.range_eq hctx.2.2.2.2.1.2 s1.1
    hctx.bstar.2.1 hctx.2.2.2.2.2.2.1.2 hpair.1 hpair.2.1

end Reduction

end CFSG.StandardType
