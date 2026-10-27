module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.RankThree.PartOne.KE.CTMain

public noncomputable section

namespace CFSG.RankThree.PartOne.KE

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

section Weyl

variable {τ : Tag} {L : Type} [Field L]

theorem torusGroup_comm {g h : ModGL τ L} (hg : g ∈ torusGroup τ L) (hh : h ∈ torusGroup τ L) :
    g * h = h * g := by
  obtain ⟨a, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hg
  obtain ⟨b, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hh
  have h1 : rootDiagUnit τ a * rootDiagUnit τ b = rootDiagUnit τ (a * b) :=
    ((rootDiagUnitHom τ L).map_mul a b).symm
  have h2 : rootDiagUnit τ b * rootDiagUnit τ a = rootDiagUnit τ (b * a) :=
    ((rootDiagUnitHom τ L).map_mul b a).symm
  rw [h1, h2, mul_comm a b]

theorem canonicalRep_mul_inv_mem_torusGroup {n : ModGL τ L} (hn : n ∈ monomialSubgroup τ L)
    (w : WeylGroup τ) (hw : weylQuotientHom τ L ⟨n, hn⟩ = w) :
    canonicalRep (coxeterSystem τ) L w * n⁻¹ ∈ torusGroup τ L := by
  obtain ⟨ρ, -, hρ, -, -, hρker⟩ := (Weyl_normalizer_quotient τ L).2.1
  have hρπ : ∀ g : monomialSubgroup τ L, ρ g = weylQuotientHom τ L g := fun g =>
    (hρ g).unique (mapsRootLines_weylQuotientHom g)
  have hcanN : canonicalRep (coxeterSystem τ) L w ∈ monomialSubgroup τ L :=
    canonicalRep_mem_monomialSubgroup L w
  have hcan : weylQuotientHom τ L ⟨canonicalRep (coxeterSystem τ) L w, hcanN⟩ = w :=
    weylQuotientHom_eq (mapsRootLines_canonicalRep w)
  have hker : (⟨canonicalRep (coxeterSystem τ) L w, hcanN⟩ * ⟨n, hn⟩⁻¹ : monomialSubgroup τ L) ∈
      ρ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hρπ, hρπ, hcan, hw, mul_inv_cancel]
  rw [hρker, Subgroup.mem_subgroupOf] at hker
  exact hker

theorem twistedTorusOf_eq_of_weylImage [IsAlgClosed L] {n : ModGL τ L}
    (hn : n ∈ monomialSubgroup τ L) (w : WeylGroup τ) (hw : weylQuotientHom τ L ⟨n, hn⟩ = w)
    (Φ : ModGL τ L →* ModGL τ L)
    (hΦ : ∀ b : Fin τ.rank → Lˣ, ∃ b' : Fin τ.rank → Lˣ,
      Φ (rootDiagUnit τ b) = rootDiagUnit τ b') :
    twistedTorusOf n Φ = twistedTorusOf (canonicalRep (coxeterSystem τ) L w) Φ := by
  have hh := canonicalRep_mul_inv_mem_torusGroup hn w hw
  have hh' : n * (canonicalRep (coxeterSystem τ) L w)⁻¹ ∈ torusGroup τ L := by
    have := inv_mem hh
    simpa using this
  have key : ∀ x ∈ torusGroup τ L,
      n * Φ x * n⁻¹ =
        canonicalRep (coxeterSystem τ) L w * Φ x * (canonicalRep (coxeterSystem τ) L w)⁻¹ := by
    intro x hx
    obtain ⟨a, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hx
    obtain ⟨b', hb'⟩ := hΦ a
    rw [hb']
    set c := canonicalRep (coxeterSystem τ) L w with hc
    set y := rootDiagUnit τ b' with hy
    have hcy : c * y * c⁻¹ ∈ torusGroup τ L := by
      rw [hc, hy, canonicalRep_conj_rootDiagUnit]
      exact rootDiagUnit_mem_torusGroup _
    have hcomm := torusGroup_comm hh' hcy
    calc n * y * n⁻¹ = (n * c⁻¹) * (c * y * c⁻¹) * (n * c⁻¹)⁻¹ := by group
      _ = c * y * c⁻¹ := by rw [hcomm, mul_inv_cancel_right]
  ext x
  constructor
  · intro hx
    obtain ⟨hx1, hx2⟩ := mem_twistedTorusOf.1 hx
    exact mem_twistedTorusOf.2 ⟨hx1, by rw [← key x hx1]; exact hx2⟩
  · intro hx
    obtain ⟨hx1, hx2⟩ := mem_twistedTorusOf.1 hx
    exact mem_twistedTorusOf.2 ⟨hx1, by rw [key x hx1]; exact hx2⟩

theorem twistedTorus_eq_of_weylImage [IsAlgClosed L] {n : ModGL τ L}
    (hn : n ∈ monomialSubgroup τ L)
    (w : WeylGroup τ) (hw : weylQuotientHom τ L ⟨n, hn⟩ = w) (Fr : L →+* L) :
    twistedTorus n Fr = twistedTorus (canonicalRep (coxeterSystem τ) L w) Fr :=
  twistedTorusOf_eq_of_weylImage hn w hw _ fun b =>
    ⟨fun i => Units.map Fr.toMonoidHom (b i), Units.ext (entrywise_rootDiag Fr b)⟩

end Weyl

theorem twistedTorus_eq_map_twistedFixedTuples_of_weylImage {τ : Tag} {L : Type} [Field L]
    [IsAlgClosed L] {n : ModGL τ L} (hn : n ∈ monomialSubgroup τ L) (w : WeylGroup τ)
    (hw : weylQuotientHom τ L ⟨n, hn⟩ = w) (Fr : L →+* L) :
    twistedTorus n Fr = (twistedFixedTuples w Fr).map (rootDiagUnitHom τ L) := by
  rw [twistedTorus_eq_of_weylImage hn w hw Fr]
  exact twistedTorus_eq_map_twistedFixedTuples w Fr

end CFSG.RankThree.PartOne.KE
