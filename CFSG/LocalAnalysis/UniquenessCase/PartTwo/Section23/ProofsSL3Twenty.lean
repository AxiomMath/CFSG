module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsComponents
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsRootModule
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsSL3
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.TIFusion
public import CFSG.LocalAnalysis.UniquenessCase.UC22P20i
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22v

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

private theorem uc22s23_20_1_mem_normalizer_conj_Z {D : Data G} {Ch : Choice2011 G}
    (c : Ctx2311 D Ch) {g x : G} (hgL : g ∈ c.L)
    (hxcent : x ∈ Subgroup.centralizer (c.E : Set G)) :
    x ∈ Subgroup.normalizer ((D.Z.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) := by
  have hLN : c.L ≤ c.N := by
    have hNle : c.L ⊔ D.T ≤ c.N := by
      have hmem : c.N ∈ calMOf (c.L ⊔ D.T) := by rw [c.hN]; simp
      exact hmem.2
    exact (le_sup_left : c.L ≤ c.L ⊔ D.T).trans hNle
  have hVE : c.V ≤ c.E := uc22p22v_le_conjClosure D.M c.V
  have hZgV : ∀ z ∈ D.Z, g * z * g⁻¹ ∈ c.V := by
    intro z hz
    exact (Subgroup.mem_normalizer_iff.mp
      (uc22p22v_le_normalizer_conjClosure c.N D.Z (hLN hgL)) z).mp
      (uc22p22v_le_conjClosure c.N D.Z hz)
  let Zg : Subgroup G := D.Z.map (MulAut.conj g).toMonoidHom
  change x ∈ Subgroup.normalizer (Zg : Set G)
  have hconj_of_cent {y : G} (hy : y ∈ Subgroup.centralizer (c.E : Set G)) :
      ∀ u ∈ Zg, y * u * y⁻¹ ∈ Zg := by
    intro u hu
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hu
    have huE : g * z * g⁻¹ ∈ c.E := hVE (by simpa [MulAut.conj_apply] using hZgV z hz)
    have hcomm : (g * z * g⁻¹) * y = y * (g * z * g⁻¹) :=
      (Subgroup.mem_centralizer_iff.mp hy) _ huE
    refine Subgroup.mem_map.mpr ⟨z, hz, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact (calc
      y * (g * z * g⁻¹) * y⁻¹ = (g * z * g⁻¹) * y * y⁻¹ := by rw [← hcomm]
      _ = g * z * g⁻¹ := by group).symm
  have hconj := hconj_of_cent hxcent
  have hconjInv := hconj_of_cent ((Subgroup.centralizer (c.E : Set G)).inv_mem hxcent)
  rw [Subgroup.mem_normalizer_iff]
  intro u
  refine ⟨hconj u, ?_⟩
  intro hu
  have hthis := hconjInv (x * u * x⁻¹) hu
  have heq : x⁻¹ * (x * u * x⁻¹) * x⁻¹⁻¹ = u := by group
  rwa [heq] at hthis

private theorem uc22s23_20_1_mem_conj_M {D : Data G} {Ch : Choice2011 G}
    (c : Ctx2311 D Ch) (h4 : S23_4 D Ch) (h1930 : H1930 D) {g x : G}
    (hxNZ : x ∈ Subgroup.normalizer
      ((D.Z.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G)) :
    x ∈ D.M.map (MulAut.conj g).toMonoidHom := by
  let y : G := g⁻¹ * x * g
  have key : ∀ w : G, w ∈ Subgroup.normalizer
      ((D.Z.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) →
      ∀ z ∈ D.Z, (g⁻¹ * w * g) * z * (g⁻¹ * w * g)⁻¹ ∈ D.Z := by
    intro w hw z hz
    let Zg : Subgroup G := D.Z.map (MulAut.conj g).toMonoidHom
    have hzZg : g * z * g⁻¹ ∈ Zg := by
      refine Subgroup.mem_map.mpr ⟨z, hz, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    have hconj : w * (g * z * g⁻¹) * w⁻¹ ∈ Zg :=
      (Subgroup.mem_normalizer_iff.mp hw (g * z * g⁻¹)).mp hzZg
    obtain ⟨z', hz', hz'eq⟩ := Subgroup.mem_map.mp hconj
    have hz'eq' : g * z' * g⁻¹ = w * (g * z * g⁻¹) * w⁻¹ := by
      simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using hz'eq
    have hcalc : (g⁻¹ * w * g) * z * (g⁻¹ * w * g)⁻¹ = z' := by
      calc
        (g⁻¹ * w * g) * z * (g⁻¹ * w * g)⁻¹ =
            g⁻¹ * (w * (g * z * g⁻¹) * w⁻¹) * g := by group
        _ = g⁻¹ * (g * z' * g⁻¹) * g := by rw [← hz'eq']
        _ = z' := by group
    rw [hcalc]
    exact hz'
  have hyZ := key x hxNZ
  have hyZInv := key x⁻¹ ((Subgroup.normalizer _).inv_mem hxNZ)
  have hyNorm : y ∈ Subgroup.normalizer (D.Z : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro z
    refine ⟨hyZ z, ?_⟩
    intro hz
    have hthis := hyZInv (y * z * y⁻¹) hz
    have heq : (g⁻¹ * x⁻¹ * g) * (y * z * y⁻¹) * (g⁻¹ * x⁻¹ * g)⁻¹ = z := by
      simp only [y]; group
    rwa [heq] at hthis
  have hNZ : Subgroup.normalizer (D.Z : Set G) = D.M := by
    rw [← (h4 h1930 c.toCtx23L).1]
    exact Data.normalizer_U_eq D
  have hyM : y ∈ D.M := by
    rw [hNZ] at hyNorm
    exact hyNorm
  refine Subgroup.mem_map.mpr ⟨y, hyM, ?_⟩
  simp only [y, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  group

theorem s23_20_1_of (D : Data G) (Ch : Choice2011 G) (h4 : S23_4 D Ch) (h6 : S23_6 D Ch)
    (hsp : ∀ p ∈ D.sig1, CFSG.RankThree.PartOne.IsStronglyPEmbedded p D.M)
    (h19 : S23_19 D Ch) : S23_20_1 D Ch := by
  intro h1930 c
  rw [Set.eq_empty_iff_forall_notMem]
  intro p hp
  rw [Set.mem_inter_iff] at hp
  obtain ⟨hpsig, hppi⟩ := hp
  obtain ⟨hp, hp2⟩ := D.sig_prime p hpsig
  haveI : Fact p.Prime := ⟨hp⟩
  rw [piSet] at hppi
  obtain ⟨-, hpdvd⟩ := hppi
  obtain ⟨x, hxord⟩ := exists_prime_orderOf_dvd_card' (G := ↥c.CMETilde) p hpdvd
  have hxmem : (x : G) ∈ c.CMETilde := x.2
  have hxordG : orderOf (x : G) = p := (Subgroup.orderOf_coe x).trans hxord
  have hxodd : Odd (orderOf (x : G)) := hxordG ▸ hp.odd_of_ne_two hp2
  have hxop : (x : G) ∈ CFSG.Quasithin.opResidual 2 c.CMETilde :=
    CFSG.Quasithin.mem_opResidual_of_coprime hxmem (Nat.coprime_two_right.mpr hxodd)
  rw [h19 h1930 c] at hxop
  have hxCME : (x : G) ∈ c.CME := CFSG.Quasithin.opResidual_le 2 c.CME hxop
  rw [Ctx2311.CME, Subgroup.mem_inf] at hxCME
  obtain ⟨hxM, hxcent⟩ := hxCME
  have hLnotM : ¬ c.L ≤ D.M := uc22p20i_not_le_M D c.hL.1
  obtain ⟨g, hgL, hgM⟩ : ∃ g ∈ c.L, g ∉ D.M := by
    by_contra h
    push Not at h
    exact hLnotM h
  have hxNZ : (x : G) ∈ Subgroup.normalizer
      ((D.Z.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) :=
    uc22s23_20_1_mem_normalizer_conj_Z c hgL hxcent
  have hxMmap : (x : G) ∈ D.M.map (MulAut.conj g).toMonoidHom :=
    uc22s23_20_1_mem_conj_M c h4 h1930 hxNZ
  have hpdvd : p ∣ Nat.card ↥(D.M ⊓ D.M.map (MulAut.conj g).toMonoidHom) := by
    have h := Subgroup.card_dvd_of_le (H := Subgroup.zpowers (x : G))
      (K := D.M ⊓ D.M.map (MulAut.conj g).toMonoidHom)
      (Subgroup.zpowers_le.mpr ⟨hxM, hxMmap⟩)
    rwa [Nat.card_zpowers, hxordG] at h
  have hp1 : p ∈ D.sig1 := by
    have hsig := h6 h1930 c.toCtx23L
    rwa [hsig] at hpsig
  exact (hsp p hp1).2.2 g hgM hpdvd

end CFSG.LocalAnalysis.UniquenessCase.UC22
