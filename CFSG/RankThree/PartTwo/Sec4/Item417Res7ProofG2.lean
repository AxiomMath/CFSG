module

public import CFSG.RankThree.PartTwo.Sec4.Item417Res6ProofExc
public import CFSG.RankThree.PartTwo.Sec4.Item417Res6ProofTools
public import CFSG.RankThree.PartTwo.Sec4.Item417Res7ProofG2Torus
public import CFSG.LocalAnalysis.EvenBN.G2.Torus
public import CFSG.RankThree.PartOne.K133H.TorusImage
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67A2Hom
import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67A2Torus
import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67A2Sylow
import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67A2Diag
import CFSG.LieType.Chevalley.AdjointCenter
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpWedge
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A3NativeBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Native
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.Reduced
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6Containment
public import CFSG.Quasithin.Background.A3Structure312
public import CFSG.Quasithin.Background.SmithB42G2FNat
public import CFSG.Quasithin.Background.SmithB42G2FOff
public import CFSG.Quasithin.H13.J4Order
public import CFSG.Quasithin.H13.J4OrderBase
public import CFSG.Quasithin.Vol2.Ch11G2Q8LineGen
public import CFSG.Quasithin.Vol2.Ch11SecBFacts22
public import CFSG.Quasithin.Vol2.Ch11SecBFacts22G
public import CFSG.Quasithin.Vol2.Ch11StatementsF
public import CFSG.Quasithin.Vol2.Ch11StatementsG
public import CFSG.Quasithin.Vol2.Ch11StatementsH
public import CFSG.Quasithin.Vol2.Ch11StatementsInputs
public import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.S10.Defs
public import CFSG.RankThree.PartTwo.Sec4.StatementsSporadic
public import CFSG.Sporadic.Schreier.J4SProfileNode
public import Certificates.Certificate8026Base

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.Chevalley CFSG.RankThree.PartOne CFSG.ComponentClassification.UnbalancedCatalog
open Res417Three Res417Five Res417Six

namespace Res417Seven

theorem primitive_cube_root_of_orderOf_three {K : Type} [Field K] {ζ : Kˣ} (hζ : orderOf ζ = 3) :
    (ζ : K) ^ 2 + ζ + 1 = 0 ∧ (ζ : K) ≠ 1 := by
  have hζ3 : (ζ : K) ^ 3 = 1 := by
    have h := pow_orderOf_eq_one ζ
    rw [hζ] at h
    simpa using congrArg Units.val h
  have hζ1 : (ζ : K) ≠ 1 := fun h => by
    have h1 : ζ = 1 := Units.ext (by simpa using h)
    rw [h1, orderOf_one] at hζ
    exact absurd hζ (by norm_num)
  refine ⟨?_, hζ1⟩
  have h : ((ζ : K) - 1) * ((ζ : K) ^ 2 + ζ + 1) = 0 := by linear_combination hζ3
  rcases mul_eq_zero.1 h with h | h
  · exact absurd (sub_eq_zero.1 h) hζ1
  · exact h

section Certs


open CFSG.GH74.GLS.Stage2.Bender.Thm1 in
theorem exists_conj_mem_torusTorsion_three {K : Type} [Field K] [Finite K]
    (h31 : 3 ∣ Nat.card K - 1) (E : Subgroup (adjointGroup .G2 K))
    (hE3 : ∀ x ∈ E, x ^ 3 = 1) (hEc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) :
    ∃ g : adjointGroup .G2 K, ∀ x ∈ E,
      ((g * x * g⁻¹ : adjointGroup .G2 K) : ModGL .G2 K) ∈ torusTorsion K 3 := by
  obtain ⟨φ, hφinj, hφ⟩ := exists_a2Hom_injective (K := K)
  have hEp : IsPGroup 3 E := fun x => ⟨1, Subtype.ext (by simpa using hE3 x x.2)⟩
  obtain ⟨y, hy⟩ := exists_conj_le_range_of_three_dvd_sub_one h31 φ hφinj E hEp
  set E' : Subgroup (Matrix.SpecialLinearGroup (Fin 3) K) :=
    (E.map (MulAut.conj y).toMonoidHom).comap φ with hE'
  have hmemE' : ∀ X, X ∈ E' ↔ φ X ∈ E.map (MulAut.conj y).toMonoidHom := fun X => Iff.rfl
  have hconjE : ∀ z ∈ E.map (MulAut.conj y).toMonoidHom, z ^ 3 = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    show (y * x * y⁻¹) ^ 3 = 1
    rw [conj_pow, hE3 x hx, mul_one, mul_inv_cancel]
  have hconjc : ∀ z ∈ E.map (MulAut.conj y).toMonoidHom,
      ∀ z' ∈ E.map (MulAut.conj y).toMonoidHom, z * z' = z' * z := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨x', hx', rfl⟩
    show y * x * y⁻¹ * (y * x' * y⁻¹) = y * x' * y⁻¹ * (y * x * y⁻¹)
    calc y * x * y⁻¹ * (y * x' * y⁻¹) = y * (x * x') * y⁻¹ := by group
      _ = y * (x' * x) * y⁻¹ := by rw [hEc x hx x' hx']
      _ = y * x' * y⁻¹ * (y * x * y⁻¹) := by group
  have hE'3 : ∀ X ∈ E', X ^ 3 = 1 := fun X hX => hφinj (by
    rw [map_pow, map_one]
    exact hconjE _ ((hmemE' X).mp hX))
  have hE'c : ∀ X ∈ E', ∀ Y ∈ E', X * Y = Y * X := fun X hX Y hY => hφinj (by
    rw [map_mul, map_mul]
    exact hconjc _ ((hmemE' X).mp hX) _ ((hmemE' Y).mp hY))
  obtain ⟨ζ, hζ⟩ := exists_units_orderOf_eq_of_dvd_card_sub_one Nat.prime_three h31
  obtain ⟨hω, hω1⟩ := primitive_cube_root_of_orderOf_three hζ
  obtain ⟨Y, hY⟩ := exists_diagonalizing_of_commuting_cube_one (ζ : K) hω hω1 E' hE'3 hE'c
  refine ⟨φ Y * y, fun x hx => ?_⟩
  obtain ⟨X, hX⟩ : y * x * y⁻¹ ∈ φ.range := hy ⟨x, hx, rfl⟩
  have hXE' : X ∈ E' := by
    rw [hmemE', hX]
    exact ⟨x, hx, rfl⟩
  have hd := phi_diag_mem_torusGroup φ hφ (Y * X * Y⁻¹) (hY X hXE')
  have heq : φ Y * y * x * (φ Y * y)⁻¹ = φ (Y * X * Y⁻¹) := by
    rw [map_mul, map_mul, map_inv, hX]
    group
  rw [mem_torusTorsion_iff]
  refine ⟨by rw [heq]; exact hd, ?_⟩
  rw [← Subgroup.coe_pow, conj_pow, hE3 x hx, mul_one, mul_inv_cancel, Subgroup.coe_one]

end Certs

section Aut


variable {K : Type} [Field K]

theorem nonempty_weylGroup_G2_mulEquiv_dihedral [CharP K 2] :
    Nonempty (WeylGroup .G2 ≃* DihedralGroup 6) := by
  set ρ := CFSG.LocalAnalysis.EvenBN.G2.Model.canonicalRepHom K with hρ
  have hρinj : Function.Injective ρ := fun w w' h =>
    (eq_and_eq_of_mul_canonicalRep_eq (one_mem (torusGroup .G2 K)) (one_mem _)
      (by rw [one_mul, one_mul]; exact h)).2
  have hrange : ρ.range = Subgroup.closure
      ({CFSG.LocalAnalysis.EvenBN.G2.Model.wa K, CFSG.LocalAnalysis.EvenBN.G2.Model.wb K} :
        Set (ModGL .G2 K)) := by
    apply le_antisymm
    · rintro _ ⟨w, rfl⟩
      have h := canonicalRep_mem_closure (coxeterSystem .G2) K w
      refine (Subgroup.closure_le _).2 ?_ h
      rintro _ ⟨i, rfl⟩
      fin_cases i
      exacts [Subgroup.subset_closure (Or.inr rfl), Subgroup.subset_closure (Or.inl rfl)]
    · rw [Subgroup.closure_le]
      rintro _ (rfl | rfl)
      · exact ⟨simple .G2 g2ir, canonicalRep_simple (coxeterSystem .G2) K g2ir⟩
      · exact ⟨simple .G2 g2ia, canonicalRep_simple (coxeterSystem .G2) K g2ia⟩
  obtain ⟨⟨e⟩, -⟩ := CFSG.LocalAnalysis.EvenBN.G2.Model.yamada_3_8 (K := K)
  exact ⟨((MonoidHom.ofInjective hρinj).trans (MulEquiv.subgroupCongr hrange)).trans e⟩

theorem nonempty_torusImage_torusTorsion_three_mulEquiv [Finite K] [CharP K 2]
    (h31 : 3 ∣ Nat.card K - 1) :
    Nonempty (torusImage ((torusTorsion K 3).subgroupOf (adjointGroup .G2 K)) ⊤ ≃*
      DihedralGroup 6) := by
  classical
  set C := adjointGroup .G2 K with hC
  set T := (torusTorsion K 3).subgroupOf C with hT
  have hmemT : ∀ x : C, x ∈ T ↔ (x : ModGL .G2 K) ∈ torusTorsion K 3 := fun x =>
    Subgroup.mem_subgroupOf
  have hTcomm := (triangular_borel_structure.{0, 0} .G2 K).1
  set ι₀ : WeylGroup .G2 →* C :=
    (CFSG.LocalAnalysis.EvenBN.G2.Model.canonicalRepHom K).codRestrict C
      (fun w => canonicalRep_mem_adjointGroup _ K w) with hι₀def
  have hι₀ : ∀ w, ((ι₀ w : C) : ModGL .G2 K) = canonicalRep (coxeterSystem .G2) K w :=
    fun w => rfl
  have hN : ∀ w, ι₀ w ∈ Subgroup.normalizer (T : Set C) := by
    intro w
    rw [Subgroup.mem_normalizer_iff]
    intro x
    rw [hmemT, hmemT]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hι₀]
    exact Subgroup.mem_normalizer_iff.mp (mem_normalizer_torusTorsion_of_mem_normalizer
      (canonicalRep_mem_normalizer (R := K) w)) x
  set ι : WeylGroup .G2 →* Subgroup.normalizer (T : Set C) := ι₀.codRestrict _ hN with hιdef
  set Ψ : WeylGroup .G2 →* MulAut T := T.normalizerMonoidHom.comp ι with hΨdef
  have hΨapp : ∀ w (t : T), (((Ψ w t : T) : C) : ModGL .G2 K) =
      canonicalRep (coxeterSystem .G2) K w * t * (canonicalRep (coxeterSystem .G2) K w)⁻¹ :=
    fun w t => rfl
  have hΨinj : Function.Injective Ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro w hw
    rw [MonoidHom.mem_ker] at hw
    have hcen : canonicalRep (coxeterSystem .G2) K w ∈ adjointGroup .G2 K ⊓
        Subgroup.centralizer (torusTorsion K 3 : Set (ModGL .G2 K)) := by
      refine ⟨canonicalRep_mem_adjointGroup _ K w, Subgroup.mem_centralizer_iff.mpr fun x hx => ?_⟩
      have hxC : x ∈ C := torusGroup_le_adjointGroup_G2 (torusTorsion_le_torusGroup 3 hx)
      have h1 := congrArg (fun σ : MulAut T =>
        (((σ ⟨⟨x, hxC⟩, (hmemT _).mpr hx⟩ : T) : C) : ModGL .G2 K)) hw
      simp only [MulAut.one_apply] at h1
      rw [hΨapp] at h1
      calc x * canonicalRep (coxeterSystem .G2) K w =
          (canonicalRep (coxeterSystem .G2) K w * x * (canonicalRep (coxeterSystem .G2) K w)⁻¹) *
            canonicalRep (coxeterSystem .G2) K w := by rw [h1]
        _ = canonicalRep (coxeterSystem .G2) K w * x := by group
    rw [g2_adjointGroup_inf_centralizer_torusTorsion_three h31] at hcen
    have h2 := eq_and_eq_of_mul_canonicalRep_eq hcen (one_mem (torusGroup .G2 K)) (w := 1)
      (w' := w) (by rw [canonicalRep_one, mul_one, one_mul])
    rw [Subgroup.mem_bot, ← h2.2]
  have hrange : Ψ.range = torusImage T ⊤ := by
    ext σ
    rw [K133H.mem_torusImage_iff]
    constructor
    · rintro ⟨w, rfl⟩
      exact ⟨ι₀ w, hN w, Subgroup.mem_top _, rfl⟩
    · rintro ⟨n, hn, -, rfl⟩
      have hn' : (n : ModGL .G2 K) ∈ adjointGroup .G2 K ⊓
          Subgroup.normalizer (torusTorsion K 3 : Set (ModGL .G2 K)) := by
        refine ⟨n.2, Subgroup.mem_normalizer_iff.mpr fun x => ⟨fun hx => ?_, fun hx => ?_⟩⟩
        · have hxC : x ∈ C := torusGroup_le_adjointGroup_G2 (torusTorsion_le_torusGroup 3 hx)
          have h1 := (Subgroup.mem_normalizer_iff.mp hn ⟨x, hxC⟩).mp ((hmemT _).mpr hx)
          rw [hmemT] at h1
          simpa using h1
        · have hyC : (n : ModGL .G2 K) * x * (n : ModGL .G2 K)⁻¹ ∈ C :=
            torusGroup_le_adjointGroup_G2 (torusTorsion_le_torusGroup 3 hx)
          have hxC : x ∈ C := by
            have : x = (n : ModGL .G2 K)⁻¹ * ((n : ModGL .G2 K) * x * (n : ModGL .G2 K)⁻¹) *
                (n : ModGL .G2 K) := by group
            rw [this]
            exact mul_mem (mul_mem (inv_mem n.2) hyC) n.2
          have h1 : n * ⟨x, hxC⟩ * n⁻¹ ∈ T := by
            rw [hmemT]
            simpa using hx
          exact (hmemT _).mp ((Subgroup.mem_normalizer_iff.mp hn ⟨x, hxC⟩).mpr h1)
      obtain ⟨h, hh, w, hhw⟩ := g2_exists_eq_mul_canonicalRep_of_mem_normalizer_three h31 hn'
      refine ⟨w, MulEquiv.ext fun t => Subtype.ext (Subtype.ext ?_)⟩
      rw [hΨapp]
      change _ = (n : ModGL .G2 K) * ((t : C) : ModGL .G2 K) * (n : ModGL .G2 K)⁻¹
      have htT : ((t : C) : ModGL .G2 K) ∈ torusGroup .G2 K :=
        torusTorsion_le_torusGroup 3 ((hmemT _).mp t.2)
      have hsT : canonicalRep (coxeterSystem .G2) K w * ((t : C) : ModGL .G2 K) *
          (canonicalRep (coxeterSystem .G2) K w)⁻¹ ∈ torusGroup .G2 K :=
        (Subgroup.mem_normalizer_iff.mp (canonicalRep_mem_normalizer (R := K) w) _).mp htT
      rw [hhw]
      calc canonicalRep (coxeterSystem .G2) K w * ((t : C) : ModGL .G2 K) *
            (canonicalRep (coxeterSystem .G2) K w)⁻¹ =
          h * (canonicalRep (coxeterSystem .G2) K w * ((t : C) : ModGL .G2 K) *
            (canonicalRep (coxeterSystem .G2) K w)⁻¹) * h⁻¹ := by
            rw [hTcomm h hh _ hsT, mul_inv_cancel_right]
        _ = _ := by group
  obtain ⟨e⟩ := nonempty_weylGroup_G2_mulEquiv_dihedral (K := K)
  exact ⟨((MulEquiv.subgroupCongr hrange).symm.trans (MonoidHom.ofInjective hΨinj).symm).trans e⟩

end Aut

section Main


theorem k417DatumG2Even_holds : K417DatumG2Even := by
  intro X _ f hev hX D hD
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hX
  have hf : f ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hK
    exact (Finite.one_lt_card (α := K)).ne' hK
  have : CharP K 2 := by
    have := Fintype.ofFinite K
    exact charP_of_card_eq_prime_pow (p := 2) (f := f) (by rw [Fintype.card_eq_nat_card, hK])
  have h31 : 3 ∣ Nat.card K - 1 := by
    rw [hK]
    have h := (two_pow_mod_three f).1 hev
    generalize 2 ^ f = m at h ⊢
    omega
  set φ : X ≃* adjointGroup .G2 K := e.trans
    ((QuotientGroup.quotientMulEquivOfEq center_adjointGroup_eq_bot).trans
      QuotientGroup.quotientBot) with hφ
  obtain ⟨hDe, hmax, -⟩ := hD
  set T := (torusTorsion K 3).subgroupOf (adjointGroup .G2 K) with hTdef
  have hTmem : ∀ x : adjointGroup .G2 K, x ∈ T ↔ (x : ModGL .G2 K) ∈ torusTorsion K 3 :=
    fun x => Subgroup.mem_subgroupOf
  have hTcomm : ∀ s ∈ T, ∀ t ∈ T, s * t = t * s := fun s hs t ht => Subtype.ext
    ((triangular_borel_structure.{0, 0} .G2 K).1 _
      (torusTorsion_le_torusGroup 3 ((hTmem s).mp hs)) _
      (torusTorsion_le_torusGroup 3 ((hTmem t).mp ht)))
  have hTexp : ∀ t ∈ T, t ^ 3 = 1 := fun t ht => Subtype.ext (by
    rw [Subgroup.coe_pow]
    exact (mem_torusTorsion_iff.mp ((hTmem t).mp ht)).2)
  have hD3 : ∀ x ∈ D.map φ.toMonoidHom, x ^ 3 = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    show φ x ^ 3 = 1
    rw [← map_pow, hDe.2 x hx, map_one]
  have hDc : ∀ x ∈ D.map φ.toMonoidHom, ∀ y ∈ D.map φ.toMonoidHom, x * y = y * x := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    show φ x * φ y = φ y * φ x
    have hxy : x * y = y * x := congrArg Subtype.val (hDe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
    rw [← map_mul, ← map_mul, hxy]
  obtain ⟨g, hg⟩ := exists_conj_mem_torusTorsion_three h31 (D.map φ.toMonoidHom) hD3 hDc
  have hmap := map_eq_of_conj_le φ hmax hTcomm hTexp fun x hx =>
    (hTmem _).mpr (hg _ ⟨x, hx, rfl⟩)
  refine ⟨?_, ?_⟩
  · rw [card_eq_of_map_eq _ hmap, hTdef,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (torusTorsion_le_torusGroup 3 |>.trans
        torusGroup_le_adjointGroup_G2)).toEquiv, natCard_torusTorsion h31]
    norm_num
  · obtain ⟨ψ⟩ := nonempty_autIn_mulEquiv_of_map_eq _ hmap
    obtain ⟨ψ'⟩ := nonempty_torusImage_torusTorsion_three_mulEquiv h31
    exact ⟨ψ.trans ψ'⟩

end Main

end Res417Seven

end CFSG.RankThree.PartTwo.Sec4
