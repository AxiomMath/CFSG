module

public import CFSG.LocalAnalysis.StandardType.GGPGLToralityMain
public import CFSG.LocalAnalysis.StandardType.GGTableBTypeADvd

public section

namespace CFSG.StandardType

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.Assembly

namespace TypeA

variable {d p : ℕ} {K : Type} [Field K]

theorem isProjElem_comap [Finite K] (hd : 0 < d) {X : Subgroup (MulAut (projectiveSL d K))}
    (hX : IsElemAbelian p X) : PGLTor.IsProjElem p (X.comap (conjAut d K)) := by
  let N : Subgroup (GL (Fin d) K) := ⊤
  let ρ : N →* MulAut (projectiveSL d K) := (conjAut d K).domRestrict N
  have hNscal : ∀ u : Kˣ, GeneralLinearGroup.scalar (Fin d) u ∈ N := fun _ =>
    Subgroup.mem_top _
  have hρscal : ∀ u : Kˣ, ρ ⟨GeneralLinearGroup.scalar (Fin d) u, hNscal u⟩ = 1 := by
    intro u
    simpa [ρ, N, MonoidHom.domRestrict_apply] using conjAut_scalar (n := d) (K := K) u
  have hker : ∀ x : N, ρ x = 1 → ∃ u : Kˣ,
      (x : GL (Fin d) K) = GeneralLinearGroup.scalar (Fin d) u := by
    intro x hx
    have hx' : conjAut d K (x : GL (Fin d) K) = 1 := by
      simpa [ρ, N, MonoidHom.domRestrict_apply] using hx
    obtain ⟨c, hc⟩ := exists_scalar_of_conjAut_eq_one hx'
    exact exists_unit_of_scalar hd hc
  have hG := PGLTor.isProjElem_comap_map_subtype (N := N) (ρ := ρ) hNscal hρscal hker hX
  have hmap : (X.comap ρ).map N.subtype = X.comap (conjAut d K) := by
    ext g
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa [ρ, N, MonoidHom.domRestrict_apply] using hx
    · intro hg
      exact ⟨⟨g, Subgroup.mem_top g⟩, by
        simpa [ρ, N, MonoidHom.domRestrict_apply] using hg, rfl⟩
  rwa [hmap] at hG

theorem card_comap_eq [Finite K] (hd : 0 < d) {X : Subgroup (MulAut (projectiveSL d K))}
    (hXI : (X : Set (MulAut (projectiveSL d K))) ⊆ Set.range (conjAut d K)) :
    Nat.card (X.comap (conjAut d K)) = Nat.card X * (Nat.card K - 1) := by
  have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  set G := X.comap (conjAut d K) with hG
  set f := (conjAut d K).comp G.subtype with hf
  have hrange : f.range = X := by
    ext x
    constructor
    · rintro ⟨A, rfl⟩
      exact A.2
    · intro hx
      obtain ⟨A, rfl⟩ := hXI hx
      exact ⟨⟨A, hx⟩, rfl⟩
  have hscal : ∀ u : Kˣ, GeneralLinearGroup.scalar (Fin d) u ∈ G := fun u => by
    change conjAut d K _ ∈ X
    rw [conjAut_scalar]
    exact X.one_mem
  have hker : Nat.card f.ker = Nat.card K - 1 := by
    rw [← Nat.card_units K]
    symm
    refine Nat.card_eq_of_bijective
      (fun u => ⟨⟨GeneralLinearGroup.scalar (Fin d) u, hscal u⟩, by
        rw [MonoidHom.mem_ker, hf, MonoidHom.comp_apply, Subgroup.coe_subtype, conjAut_scalar]⟩)
      ⟨fun u v huv => ?_, fun x => ?_⟩
    · have h1 := congrArg (fun y : f.ker => ((y : G) : GL (Fin d) K)) huv
      exact PGLTor.scalar_injective h1
    · have h1 : conjAut d K (x : G) = 1 := x.2
      obtain ⟨c, hc⟩ := exists_scalar_of_conjAut_eq_one h1
      obtain ⟨u, hu⟩ := exists_unit_of_scalar hd hc
      exact ⟨u, Subtype.ext (Subtype.ext hu.symm)⟩
  rw [← Subgroup.card_ker_mul_card_range f, hrange, hker, mul_comm]

theorem isToral_comap_of_pow_lt_card [Finite K] (hp : p.Prime) (hp2 : p ≠ 2)
    (hpK : p ∣ Nat.card K - 1) (X : Subgroup (MulAut (projectiveSL d K)))
    (hX : IsElemAbelian p X)
    (hXI : (X : Set (MulAut (projectiveSL d K))) ⊆ Set.range (conjAut d K))
    (hcard : p ^ (d / p + 1) < Nat.card X) :
    PGLTor.IsToral (X.comap (conjAut d K)) := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · exact ⟨1, fun _ _ i => i.elim0⟩
  rcases PGLTor.toral_or_card_le hp hp2 hpK (isProjElem_comap hd hX) with htor | hbound
  · exact htor
  · exfalso
    rw [card_comap_eq hd hXI, Fintype.card_fin] at hbound
    have hK1 : 0 < Nat.card K - 1 := by
      have := Finite.one_lt_card (α := K)
      omega
    exact (not_le.mpr hcard) (Nat.le_of_mul_le_mul_right hbound hK1)

theorem ggPGLTorality_holds [Finite K] (hp : p.Prime) (hp2 : p ≠ 2) (hpK : p ∣ Nat.card K - 1) :
    GGPGLTorality p d K := by
  intro X hX hXI hcard1 hcard3
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · exact ⟨1, fun _ _ i => i.elim0⟩
  rcases PGLTor.toral_or_card_le hp hp2 hpK (isProjElem_comap hd hX) with ⟨A₀, hA₀⟩ | hbound
  · exact ⟨A₀, fun A hA i j hij => hA₀ A hA i j hij⟩
  · exfalso
    rw [card_comap_eq hd hXI, Fintype.card_fin] at hbound
    have hK1 : 0 < Nat.card K - 1 := by
      have := Finite.one_lt_card (α := K)
      omega
    have hX' : Nat.card X ≤ p ^ (d / p + 1) := Nat.le_of_mul_le_mul_right hbound hK1
    have h1 := (Nat.pow_le_pow_iff_right hp.one_lt).mp (hcard1.trans hX')
    have h2 := (Nat.pow_le_pow_iff_right hp.one_lt).mp (hcard3.trans hX')
    have hp3 : 3 ≤ p := by
      have := hp.two_le
      omega
    have hdiv : d / p ≤ d / 3 := Nat.div_le_div_left hp3 (by norm_num)
    omega

end TypeA

theorem ggPGLToralityInput_holds : GGPGLToralityInput := fun _ _ _ _ _ hp hp2 hpK _ =>
  TypeA.ggPGLTorality_holds hp hp2 hpK

theorem ggBstarInputOn_typeA_split_holds : GGBstarInputOn GGTypeASplitLabel :=
  ggBstarInputOn_typeA_split ggPGLToralityInput_holds

theorem ggStdSubPreInputOn_typeA_split_holds : GGStdSubPreInputOn GGTypeASplitLabel :=
  ggStdSubPreInputOn_typeA_split ggPGLToralityInput_holds

end CFSG.StandardType
