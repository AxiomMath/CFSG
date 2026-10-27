module

public import CFSG.Quasithin.Background.A3StructureDefs
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitAutL34Make
public import CFSG.Quasithin.Background.D2Basic

public section

namespace CFSG.Quasithin.H13.Ch9.KGFF

open CFSG.Quasithin CFSG.ComponentClassification.PerfectAutomorphisms
open scoped IsMulCommutative

section L34

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem commutator_eq_self_of_perfect {L : Subgroup G} (hL : Group.IsPerfect ↥L) :
    ⁅L, L⁆ = L := by
  have hm : (⊤ : Subgroup ↥L).map L.subtype = L := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hc : commutator ↥L = ⊤ := Group.isPerfect_def.mp hL
  calc ⁅L, L⁆ = ⁅(⊤ : Subgroup ↥L).map L.subtype, (⊤ : Subgroup ↥L).map L.subtype⁆ := by rw [hm]
    _ = Subgroup.map L.subtype ⁅(⊤ : Subgroup ↥L), (⊤ : Subgroup ↥L)⁆ :=
      (Subgroup.map_commutator _ _ _).symm
    _ = L := by rw [← commutator_def, hc, hm]

theorem le_center_of_coprime {Q : Type*} [Group Q] [Finite Q] (hq : CFSG.IsQuasisimple Q)
    (hev : 2 ∣ Nat.card Q) {N : Subgroup Q} (hN : N.Normal) (hc : Nat.Coprime 2 (Nat.card N)) :
    N ≤ Subgroup.center Q := by
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hq hN with h | h
  · exfalso
    rw [h, Subgroup.card_top] at hc
    exact absurd (Nat.dvd_gcd dvd_rfl hev) (by rw [hc]; norm_num)
  · exact h

theorem rk_le_four_add_of_l34
    {L E : Subgroup G} (hq : CFSG.IsQuasisimple ↥L) (hev : 2 ∣ Nat.card ↥L)
    (hL : IsPSL 3 2 2 (↥L ⧸ Subgroup.center ↥L))
    (hEN : E ≤ Subgroup.normalizer (L : Set G)) (hE : CFSG.Open.IsElemAbelian 2 E) :
    rk ↥E ≤ 4 + rk ↥(E ⊓ Subgroup.centralizer (L : Set G)) := by
  have : Group.IsPerfect ↥L := hq.1
  have hK : ⁅L, L⁆ = L := commutator_eq_self_of_perfect hq.1
  have hO : CFSG.Open.fusionOddCore ↥L ≤ Subgroup.center ↥L :=
    sSup_le fun N hN => le_center_of_coprime hq hev hN.1 (Nat.coprime_two_left.mpr hN.2)
  have hZ : CFSG.Open.fusionZStar ↥L = Subgroup.center ↥L :=
    (CFSG.LocalCores.quasisimple_central_quotient hq _ hO).2.1
  have hL' : CFSG.ComponentClassification.GrSLit.IsL34Type
      (↥L ⧸ CFSG.Open.fusionZStar ↥L) := by
    obtain ⟨hadm, K, hKf, hKfin, hKc, ⟨e⟩⟩ := hL
    exact Or.inl ⟨by decide, hadm, K, hKf, hKfin, hKc,
      ⟨(QuotientGroup.quotientMulEquivOfEq hZ).trans e⟩⟩
  obtain ⟨ρ⟩ := CFSG.ComponentClassification.HSFLit.AutL34.exists_real hK hL'
  have hEe : CFSG.ComponentClassification.GrSLit.IsElemTwo E := by
    have := hE.1
    refine ⟨fun x hx y hy => congrArg Subtype.val (mul_comm (⟨x, hx⟩ : ↥E) ⟨y, hy⟩),
      fun x hx => ?_⟩
    rw [← sq]
    exact hE.2 x hx
  have h1 := ρ.rank hEN hEe
  have hP : CFSG.pPrimeCore 2 ↥L ≤ Subgroup.center ↥L :=
    sSup_le fun N hN => le_center_of_coprime hq hev hN.1 hN.2
  have hle : E ⊓ CFSG.ComponentClassification.UnbalancedLayer.coreActionKernel L ≤
      E ⊓ Subgroup.centralizer (L : Set G) := by
    rintro g ⟨hgE, hgN, hg⟩
    refine ⟨hgE, Subgroup.mem_centralizer_iff.mpr fun j hj => ?_⟩
    have hgN' : g⁻¹ ∈ Subgroup.normalizer (L : Set G) := Subgroup.inv_mem _ hgN
    set φ : ↥L →* ↥L := (L.normalizerMonoidHom ⟨g⁻¹, hgN'⟩).toMonoidHom with hφ
    have hφj : ∀ l : ↥L, ((φ l : ↥L) : G) = g⁻¹ * l * g := by
      intro l
      change g⁻¹ * (l : G) * g⁻¹⁻¹ = g⁻¹ * l * g
      rw [inv_inv]
    have hcen : ∀ l : ↥L, l⁻¹ * φ l ∈ Subgroup.center ↥L := by
      intro l
      obtain ⟨c, hc, hcl⟩ := hg l l.2
      have hcl' : c = l⁻¹ * φ l := by
        apply Subtype.ext
        have hcl2 : (c : G) = (l : G)⁻¹ * g⁻¹ * l * g := hcl
        rw [hcl2, Subgroup.coe_mul, Subgroup.coe_inv, hφj]
        group
      rw [← hcl']
      exact hP hc
    have hid := hom_eq_id_of_central_displacement φ hcen
    have h2 := congrArg (fun f : ↥L →* ↥L => ((f ⟨j, hj⟩ : ↥L) : G)) hid
    simp only [MonoidHom.id_apply] at h2
    rw [hφj] at h2
    calc j * g = g * (g⁻¹ * j * g) := by group
      _ = g * j := by rw [h2]
  have h2 := h1.trans (Nat.mul_le_mul_left 16 (Subgroup.card_le_of_le hle))
  have hEp : IsPGroup 2 ↥E :=
    isPGroup_two_of_sq_eq_one fun x => Subtype.ext (by simpa using hE.2 x x.2)
  have hCp : IsPGroup 2 ↥(E ⊓ Subgroup.centralizer (L : Set G)) :=
    isPGroup_two_of_sq_eq_one fun x => Subtype.ext (by simpa using hE.2 x x.2.1)
  rw [card_eq_two_pow_of_isPGroup hEp, card_eq_two_pow_of_isPGroup hCp,
    show (16 : ℕ) = 2 ^ 4 by norm_num, ← pow_add] at h2
  exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h2

end L34

end CFSG.Quasithin.H13.Ch9.KGFF
