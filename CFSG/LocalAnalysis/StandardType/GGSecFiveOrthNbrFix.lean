module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveOrthSetup

public section

namespace CFSG.StandardType.OrthF3

open CFSG CFSG.Assembly CFSG.Open CFSG.Blueprint CFSG.LieType.Universal TauCeti

theorem ggOrthNbr_not_le
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {Q : QuadraticForm (ZMod 3) V} {ι : Additive ↥Bs ≃+ V} (S : GGOrthSetup B Bs x L D J 𝒦 Q ι) (hFix : GGSecFiveFixInput)
    {y : G} {K : Subgroup G} (hnb : GGNbr 3 B x D J y K) : ¬ ggAutomizer L Bs ≤ ggAutomizer K Bs := by
  intro hle
  have hS : LargeEvenSStar 3 B x L := S.cfg.1.1.1.2.2.2.2.2.2.1
  have hDB : D ≤ B := S.cfg.1.1.2.2.1.1
  have hBBs : B ≤ Bs := S.cfg.1.1.2.1.1
  have hyD : y ∈ D :=
    hnb.2.1 ▸ Subgroup.subset_closure (Set.mem_insert_of_mem x rfl)
  have hyB : y ∈ B := hDB hyD
  have hyBs : y ∈ Bs := hBBs hyB
  have hKz : K ≤ Subgroup.centralizer ({y} : Set G) := hnb.1.2.2.2.1
  have hfix_y : ∀ φ ∈ ggAutomizer K Bs, φ ⟨y, hyBs⟩ = ⟨y, hyBs⟩ := by
    intro φ hφ
    have hyfix : y ∈ ggFixG Bs φ := mem_ggFixG_of_mem_ggAutomizer hyBs hKz hφ
    rw [ggFixG, Subgroup.mem_map] at hyfix
    obtain ⟨b, hb, hbval⟩ := hyfix
    have hbeq : b = ⟨y, hyBs⟩ := Subtype.ext hbval
    rw [← hbeq]
    exact mem_ggFix.mp hb
  have hyzx : (y : G) ∈ Subgroup.zpowers x :=
    hFix G 3 B Bs x L D J 𝒦 S.cfg S.split ⟨y, hyBs⟩ fun φ hφ => hfix_y φ (hle hφ)
  have hxB : x ∈ B := hS.2.1
  have hxne : x ≠ 1 := hS.2.2.1
  have hx3 : x ^ 3 = 1 := hS.1.1.2 x hxB
  have hyne : y ≠ 1 := hnb.1.2.2.1
  have hy3 : y ^ 3 = 1 := hnb.1.1.1.2 y hyB
  have hox : orderOf x = 3 := orderOf_eq_prime hx3 hxne
  have hoy : orderOf y = 3 := orderOf_eq_prime hy3 hyne
  have hzy : Subgroup.zpowers y = Subgroup.zpowers x := by
    apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hyzx)
    rw [Nat.card_zpowers, Nat.card_zpowers, hoy, hox]
  have hcent : Subgroup.centralizer ({y} : Set G) =
      Subgroup.centralizer (Subgroup.zpowers x) := by
    rw [← Subgroup.centralizer_closure ({y} : Set G), ← Subgroup.zpowers_eq_closure y, hzy]
  have hKx : K ≤ Subgroup.centralizer (Subgroup.zpowers x) := hcent ▸ hKz
  have hcomm : (⁅K, Subgroup.zpowers x⁆ : Subgroup G) = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hKx
  exact hnb.2.2.2 (by rw [hcomm]; exact bot_le)

end CFSG.StandardType.OrthF3

end
