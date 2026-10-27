module

public import CFSG.LocalAnalysis.StandardType.GGNbrLSideTransport
import CFSG.LocalAnalysis.StandardType.Marking

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggNbrLSide_large_of_L {G : Type} [Group G] (L : Subgroup G) {E U : Subgroup ↥L}
    (hE : CFSG.Open.IsElemAbelian 3 E) (hEc : Nat.card E = 3 ^ 5) (hU2 : IsPGroup 2 U)
    (hU : U ≠ ⊥) (hEU : E ≤ Subgroup.normalizer (U : Set ↥L)) : GGLarge3RankIn2Local L := by
  have hinj : Function.Injective L.subtype := Subtype.val_injective
  haveI : IsMulCommutative ↥E := hE.1
  refine ⟨E.map L.subtype, U.map L.subtype, Subgroup.map_subtype_le E, Subgroup.map_subtype_le U,
    ⟨Subgroup.map_isMulCommutative E L.subtype, ?_⟩, ?_, hU2.of_equiv
      (U.equivMapOfInjective L.subtype hinj), ?_, ?_⟩
  · rintro _ ⟨a, ha, rfl⟩
    have h := congrArg L.subtype (hE.2 a ha)
    simpa [map_pow] using h
  · rw [Nat.card_congr (E.equivMapOfInjective L.subtype hinj).toEquiv.symm]
    exact hEc
  · intro h
    exact hU ((Subgroup.map_eq_bot_iff_of_injective U hinj).1 h)
  · rintro _ ⟨x, hx, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro g
    have hx' := Subgroup.mem_normalizer_iff.1 (hEU hx)
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨x * u * x⁻¹, (hx' u).1 hu, by simp⟩
    · intro hg
      obtain ⟨v, hv, hvg⟩ := hg
      have hgL : g ∈ L := by
        have : g = (L.subtype x)⁻¹ * (L.subtype v) * L.subtype x := by
          rw [hvg]; group
        rw [this]
        exact L.mul_mem (L.mul_mem (L.inv_mem x.2) v.2) x.2
      refine ⟨⟨g, hgL⟩, ?_, rfl⟩
      have hv' : x * ⟨g, hgL⟩ * x⁻¹ = v := by
        apply Subtype.ext
        simpa using hvg.symm
      exact (hx' ⟨g, hgL⟩).2 (by rw [hv']; exact hv)

theorem ggNbrLSide_of_rs_35 (hRS : GGNbrLSideRS) (h35 : GGNbrLSide35) : GGNbrLSide := by
  intro G _ _ B Bs x L D J hcfg y K hnbr hnl Q hQ4 hQ3 hF b hbB hbJ
  have hS : LargeEvenSStar 3 B x L := hcfg.1.2.2.2.2.2.2.1
  have hBab : CFSG.Open.IsElemAbelian 3 B := hS.1.1
  have hLx : L ≤ Subgroup.centralizer ({x} : Set G) := hS.2.2.2.1.1
  have hLq : CFSG.Assembly.IsQuasisimple L := hS.2.2.2.1.2.2
  have hJc : CFSG.Assembly.IsComponentOf J (L ⊓ Subgroup.centralizer (D : Set G)) :=
    hcfg.2.2.1.2.2.2.2.2.1
  have hyB : y ∈ B := hnbr.1.2.1
  have hDxy : D = Subgroup.closure {x, y} := hnbr.2.1
  have hyD : y ∈ D := by
    rw [hDxy]
    exact Subgroup.subset_closure (by simp)
  have hDcard : Nat.card D = 3 ^ 2 := hcfg.2.2.1.2.2.1
  have hxD : x ∈ D := hcfg.2.2.1.2.2.2.1
  have hyx : y ∉ Subgroup.zpowers x := by
    intro hy
    have hD_le : D ≤ Subgroup.zpowers x := by
      rw [hDxy, Subgroup.closure_le]
      rintro z (rfl | rfl)
      · exact Subgroup.mem_zpowers _
      · exact hy
    have hD_eq : D = Subgroup.zpowers x := le_antisymm hD_le (Subgroup.zpowers_le.mpr hxD)
    have hxB : x ∈ B := hS.2.1
    have hord : orderOf x = 3 := orderOf_eq_prime (hBab.2 x hxB) hS.2.2.1
    have hcard : Nat.card D = 3 := by rw [hD_eq, Nat.card_zpowers, hord]
    omega
  have hcent : L ⊓ Subgroup.centralizer (D : Set G) = L ⊓ Subgroup.centralizer ({y} : Set G) := by
    ext l
    rw [Subgroup.mem_inf, Subgroup.mem_inf, Subgroup.mem_centralizer_iff,
      Subgroup.mem_centralizer_iff]
    refine ⟨fun h => ⟨h.1, fun z hz => ?_⟩, fun h => ⟨h.1, fun d hd => ?_⟩⟩
    · rw [Set.mem_singleton_iff.mp hz]
      exact h.2 y hyD
    · have hx' : x * l = l * x := Subgroup.mem_centralizer_iff.1 (hLx h.1) x rfl
      have hy' : y * l = l * y := h.2 y rfl
      have hcl : D ≤ Subgroup.centralizer ({l} : Set G) := by
        rw [hDxy, Subgroup.closure_le]
        rintro z (rfl | rfl)
        · exact Subgroup.mem_centralizer_iff.2 fun w hw => by
            rw [Set.mem_singleton_iff.mp hw]
            exact hx'.symm
        · exact Subgroup.mem_centralizer_iff.2 fun w hw => by
            rw [Set.mem_singleton_iff.mp hw]
            exact hy'.symm
      exact (Subgroup.mem_centralizer_iff.1 (hcl hd) l rfl).symm
  rw [hcent] at hJc
  obtain ⟨hcomm, lab, hlab, hraw⟩ := ggNbrLSide_marking_of_config hcfg
  have hraw' := (largeEvenRawDatum_legacy _ _).2 hraw
  obtain ⟨R₀, _, I₀, F₀, -, -, θ₀, hs, -⟩ := largeEvenRawDatum_exists hraw'
  obtain ⟨R, _, I, F, ⟨-, -, θ, -, hBN, hI⟩, hDich⟩ :=
    largeEvenRawDatum_exists (hRS lab hlab hs _ hraw')
  have hyL : y ∈ Subgroup.normalizer (L : Set G) := hBN hyB
  have hbL : b ∈ Subgroup.normalizer (L : Set G) := hBN hbB
  have hφI : ggLAut L θ ⟨y, hyL⟩ ∈ I := ggLAut_mem_of_induces L θ hBN hI hyB
  have hψI : ggLAut L θ ⟨b, hbL⟩ ∈ I := ggLAut_mem_of_induces L θ hBN hI hbB
  have hφ1 : ggLAut L θ ⟨y, hyL⟩ ≠ 1 := by
    intro h1
    have hyC := mem_centralizer_of_ggLAut_eq_one L θ hcomm h1
    have : y ∈ B ⊓ Subgroup.centralizer (L : Set G) := ⟨hyB, hyC⟩
    rw [inf_centralizer_eq_zpowers_of_sstar Nat.prime_three hS] at this
    exact hyx this
  have hφ3 : ggLAut L θ ⟨y, hyL⟩ ^ 3 = 1 := by
    rw [← map_pow]
    have : (⟨y, hyL⟩ : Subgroup.normalizer (L : Set G)) ^ 3 = 1 :=
      Subtype.ext (hBab.2 y hyB)
    rw [this, map_one]
  have hψ3 : ggLAut L θ ⟨b, hbL⟩ ^ 3 = 1 := by
    rw [← map_pow]
    have : (⟨b, hbL⟩ : Subgroup.normalizer (L : Set G)) ^ 3 = 1 :=
      Subtype.ext (hBab.2 b hbB)
    rw [this, map_one]
  have hφψ : ggLAut L θ ⟨y, hyL⟩ * ggLAut L θ ⟨b, hbL⟩ =
      ggLAut L θ ⟨b, hbL⟩ * ggLAut L θ ⟨y, hyL⟩ := by
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (TableB.IsElemAbelian.comm hBab hyB hbB)
  obtain ⟨J', ψJ, e, hJ'c, hψJ, hψJ', he⟩ := ggNbrLSide_comp_transport hLq θ hyL hJc
  have hJL : J ≤ L := hJc.1.trans inf_le_left
  have hind := ggNbrLSide_induces_transport θ hJL hbL hbJ ψJ hψJ hψJ' e he
  obtain ⟨F₁, _, _, hF₁, ⟨eF⟩⟩ := hF
  rcases hDich _ hφI _ hψI hφ1 hφ3 hψ3 hφψ J' hJ'c Q hQ4 hQ3
      ⟨F₁, inferInstance, inferInstance, hF₁, ⟨e.symm.trans eF⟩⟩ _ hind with hinn | hlarge
  · exact ggInnDiagPSL3_of_congr e hinn
  · exfalso
    obtain ⟨E, U, hE, hEc, hU2, hU, hEU⟩ := h35 lab hlarge ↥L
      ⟨hcomm, lab, hlab, (largeEvenRawDatum_legacy _ _).1
        (largeEvenRawDatum_mono (fun R _ I F hq => by
          obtain ⟨hsim, hna, θ', hsp, -, -⟩ := hq
          exact ⟨hsim, hna, θ', rfl, hsp⟩) hraw')⟩
    exact hnl (ggNbrLSide_large_of_L L hE hEc hU2 hU hEU)

end CFSG.StandardType

end
