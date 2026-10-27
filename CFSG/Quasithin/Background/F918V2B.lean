module

public import CFSG.Quasithin.Background.F918V2BA
public import CFSG.Quasithin.Background.F918V2BB
public import CFSG.Quasithin.Background.B1MoreIrr

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin.Z391
open scoped Pointwise

theorem d391_types (hD35 : D35)
    {W : Type} [CommGroup W] [Finite W] {M T L : Subgroup (MulAut W)} {V : Subgroup W}
    (hD : D3Std M L T L V) (hlt : V < orbSup T V)
    (hC : ∀ g ∈ L, (∀ v ∈ V, g v = v) → ∀ x ∈ L, g * x = x * g)
    {Q : Type} [CommGroup Q] [MulDistribMulAction ↥M Q] (π : W →* Q)
    (hπs : Function.Surjective π)
    (hπM : ∀ (g : ↥M) (w : W), g • π w = π ((g : MulAut W) w)) (hker : π.ker = fixV L)
    (t : ↥M)
    (hni : ¬ XMod.Iso ↥(L.subgroupOf M) (V.map π) (t • V.map π)) :
    ∀ g : ↥M, XMod.Iso ↥(L.subgroupOf M) (g • V.map π) (V.map π) ∨
      XMod.Iso ↥(L.subgroupOf M) (g • V.map π) (t • V.map π) := by
  intro g
  have hLM : L ≤ M := le_of_mem_cComp hD.hyp.comp
  have hMn : ∀ m ∈ M, ∀ l ∈ L, m * l * m⁻¹ ∈ L := fun m hm l hl =>
    ((Subgroup.mem_normalizer_iff.1 (hD.hyp.Mp_normal hm)) l).1 hl
  have hΛ : ∀ g : ↥M, ∀ l ∈ L.subgroupOf M, g * l * g⁻¹ ∈ L.subgroupOf M :=
    fun g l hl => hMn (g : MulAut W) g.2 (l : MulAut W) hl
  obtain ⟨hLV, hcomm, hlt', -⟩ := mem_irrPlus_top_iff.mp hD.hyp.irr
  set P : Subgroup Q := V.map π with hPdef
  have hP : ∀ l ∈ L.subgroupOf M, ∀ x ∈ P, l • x ∈ P := by
    intro l hl x hx
    obtain ⟨v, hv, rfl⟩ := hx
    rw [hπM]
    exact ⟨_, hLV (l : MulAut W) hl v hv, rfl⟩
  have hfin : Finite Q := Finite.of_surjective π hπs
  have h5 : D35Five L V := (hD35 W M L T L V hD hlt hC).2.2.2
  let q : ↥V →* ↥P := π.subgroupMap V
  have hq : Function.Surjective q := MonoidHom.subgroupMap_surjective π V
  have hqk : ∀ v : ↥V, q v = 1 ↔ (v : W) ∈ V ⊓ fixV L := by
    intro v
    have : q v = 1 ↔ π v = 1 := by
      rw [← Subtype.coe_inj]
      rfl
    rw [this, ← MonoidHom.mem_ker, hker]
    exact ⟨fun h => ⟨v.2, h⟩, fun h => h.2⟩
  have heq : ∀ (g : ↥(L.subgroupOf M)) (v : ↥V)
      (hv : (((Subgroup.subgroupOfEquivOfLe hLM) g : ↥L) : MulAut W) (v : W) ∈ V),
      q ⟨(((Subgroup.subgroupOfEquivOfLe hLM) g : ↥L) : MulAut W) (v : W), hv⟩ =
        v2bActHom (L.subgroupOf M) P hP g (q v) := by
    intro g v hv
    exact Subtype.ext (hπM (g : ↥M) (v : W)).symm
  have hnt : ∃ g : ↥(L.subgroupOf M), v2bActHom (L.subgroupOf M) P hP g ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have h1 : commSub V L ≤ fixV L := by
      rw [commSub, Subgroup.closure_le]
      rintro _ ⟨x, hx, w, hw, rfl⟩
      have h2 := congrArg (fun φ : MulAut ↥P => ((φ ⟨π w, w, hw, rfl⟩ : ↥P) : Q))
        (hcon ⟨⟨x, hLM hx⟩, hx⟩)
      simp only [v2b_coe_actHom, MulAut.one_apply] at h2
      have h3 : π (x w) = π w := (hπM ⟨x, hLM hx⟩ w).symm.trans h2
      show x w * w⁻¹ ∈ fixV L
      rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, h3, mul_inv_cancel]
    apply hlt'.not_ge
    intro v hv
    exact ⟨hv, h1 (hcomm.symm ▸ hv)⟩
  obtain ⟨hinj, htc⟩ := injective_and_twoClass_of_d35Five (Subgroup.subgroupOfEquivOfLe hLM) q hq
    hqk (v2bActHom (L.subgroupOf M) P hP) heq hD.hyp.quasi hnt h5
  rcases exists_iso_of_twoClass hΛ hP hinj htc 1 t g with ⟨h1, -⟩ | ⟨-, h2⟩ | ⟨-, h3⟩
  · exact absurd (by rwa [one_smul] at h1) hni
  · left
    rwa [one_smul] at h2
  · right
    exact h3

end CFSG.Quasithin
