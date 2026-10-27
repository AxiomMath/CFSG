module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8HatCentral
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8HatLayer
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8HatLayerCent
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8HatOp
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8HatGL2
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8HatSeven
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8HatInvol
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8HatNatProps

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

theorem c8h_natural_rep
    (hSz : Inputs1719.K_CatalogueThreePrimeSz) {Γ : Type} [Group Γ]
    [Finite Γ] {B : Subgroup Γ} {d : Γ} (h : C8HatSetup Γ B d) :
    ∃ (ρ : Γ →* ↥(StatedSL 2 (ZMod 7))) (Oh Zh : Subgroup Γ), C8HatNat Γ d ρ Oh Zh := by
  have hF := c8h_fstar_not_central h.ne_top h.prod h.d_order h.d_cent
  obtain ⟨hsz, hcount⟩ :=
    c8h_layer_components h.kgroup hSz h.no2 (h.rank 5 Nat.prime_five (by omega))
  have hE := c8h_cent_layer h.d_order h.l3 hsz hcount
  obtain ⟨p, hp, hp3, hnot⟩ := c8h_exists_op h.no2 hF hE
  obtain ⟨ψ, Oh, Zh, φ, hψker, hψcent, hmod⟩ :=
    c8h_gl2_of_op hp hp3 (h.rank p hp hp3) h.d_order h.l3 hnot
  have hp7 : p = 7 := c8h_p_eq_seven hp hp3 h.l3 ψ hψker
  subst hp7
  obtain ⟨ρ, hρs, hρψ⟩ := c8h_sl2_of_gl2 h.l3 ψ hψker
  have hρk : ρ.ker = ψ.ker := by
    ext γ
    simp only [MonoidHom.mem_ker]
    rw [← hρψ γ]
    exact ⟨fun h => by rw [h]; rfl, fun h => Subtype.ext h⟩
  obtain ⟨h1, h2, h3, h4, h7, h5, h6⟩ := c8h_nat_props hmod ρ hρs hρψ
  exact ⟨ρ, Oh, Zh,
    { surj := hρs
      ker_le := by rw [hρk]; exact hψker
      cent := fun n hn => hψcent n (by rwa [← hρk])
      normal := hmod.normal
      z_normal := hmod.z_normal
      z_le := hmod.z_le
      le_core := hmod.le_core
      o_le_ker := h1
      index := h2
      comm := h3
      pow := h4
      ngen := hmod.ngen
      d_act := hmod.d_act
      act_one := h7
      inv := h5
      irred := h6 }⟩

theorem c8h_invol
    (hSz : Inputs1719.K_CatalogueThreePrimeSz) {Γ : Type} [Group Γ] [Finite Γ]
    {B : Subgroup Γ} {d : Γ} (h : C8HatSetup Γ B d) :
    ∀ t : Γ, t ^ 2 = 1 → t ∈ CFSG.pPrimeCore 3 Γ := by
  obtain ⟨ρ, Oh, Zh, hρ⟩ := c8h_natural_rep hSz h
  exact c8h_invol_of_sl2 h.l3 ρ hρ.surj hρ.ker_le

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
