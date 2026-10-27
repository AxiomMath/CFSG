module

public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesE6NonsplitThree
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesE6QPlusThreeFrame
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesE6QPlusThreeNormalForm
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesTwE6Tools
public import CFSG.LocalAnalysis.StandardType.GGSixBstarNoOffenderExcWeylTypes
public import CFSG.GroupTheory.QuasiDihedralFusion.Basic
public import CFSG.GroupTheory.GL52.Basic
import all CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesE6NonsplitThree

public section

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Open

namespace CFSG.StandardType.ExcFrames

private theorem isElemAbelian_top_f4 :
    IsElemAbelian 3 (⊤ : Subgroup (Multiplicative (Fin Tag.F4.rank → ZMod 3))) := by
  refine ⟨inferInstance, fun x _ => ?_⟩
  apply Multiplicative.toAdd.injective
  rw [toAdd_pow, toAdd_one]
  funext i
  rw [Pi.smul_apply, Pi.zero_apply, nsmul_eq_mul, ZMod.natCast_self, zero_mul]

private theorem card_range_of_injective {G : Type*} [Group G]
    {ι : Multiplicative (Fin Tag.F4.rank → ZMod 3) →* G}
    (hinj : Function.Injective ι) : Nat.card ι.range = 3 ^ 4 := by
  rw [← Subgroup.map_top ι, Subgroup.card_map_of_injective (f := ι) hinj,
    Subgroup.card_top, Nat.card_eq_fintype_card]
  change Fintype.card (Fin 4 → ZMod 3) = 3 ^ 4
  rw [Fintype.card_fun, Fintype.card_fin, ZMod.card]

private theorem sc_map_conj {G : Type*} [Group G] {A : Subgroup G}
    (hSC : ∀ y ∈ Subgroup.centralizer (A : Set G), y ^ 3 = 1 → y ∈ A) (c : G) :
    ∀ y ∈ Subgroup.centralizer
        ((A.map (MulAut.conj c).toMonoidHom : Subgroup G) : Set G), y ^ 3 = 1 →
      y ∈ A.map (MulAut.conj c).toMonoidHom := by
  intro y hy hy3
  rw [CFSG.GroupTheory.GL52.centralizer_map_conj c A] at hy
  obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hy
  refine Subgroup.mem_map.mpr ⟨z, hSC z hz ?_, rfl⟩
  have h1 : MulAut.conj c (z ^ 3) = MulAut.conj c 1 := by
    rw [map_pow, map_one]
    exact hy3
  exact (MulAut.conj c).injective h1

private theorem sc_transport {G : Type*} [Group G] {A : Subgroup G} (hA : IsElemAbelian 3 A)
    (hA4 : 3 ^ 4 ≤ Nat.card A)
    (hSC : ∀ y ∈ Subgroup.centralizer (A : Set G), y ^ 3 = 1 → y ∈ A) (c : G) :
    IsElemAbelian 3 (A.map (MulAut.conj c).toMonoidHom) ∧
      3 ^ 4 ≤ Nat.card (A.map (MulAut.conj c).toMonoidHom) ∧
      (∀ y ∈ Subgroup.centralizer
        ((A.map (MulAut.conj c).toMonoidHom : Subgroup G) : Set G), y ^ 3 = 1 →
          y ∈ A.map (MulAut.conj c).toMonoidHom) :=
  ⟨CFSG.Open.IsElemAbelian.map hA _, by
      rw [Subgroup.card_map_of_injective (K := A) (f := (MulAut.conj c).toMonoidHom)
        (MulAut.conj c).injective]
      exact hA4,
    sc_map_conj hSC c⟩

section Holds

theorem e6ThreeRefFrame_holds :
    E6ThreeRefFrame := by
  unfold E6ThreeRefFrame
  intro K _ _ _ h3
  obtain ⟨D⟩ := E6QPlusThree.nonempty_e6QPlusThreeFrame h3
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcard : 1 < Nat.card K := Finite.one_lt_card
  have h3' : ¬ 3 ∣ Nat.card K - 1 := by
    intro h
    have hsub : 3 ∣ (Nat.card K + 1) - (Nat.card K - 1) := Nat.dvd_sub h3 h
    have h2 : (Nat.card K + 1) - (Nat.card K - 1) = 2 := by omega
    rw [h2] at hsub
    exact (by norm_num : ¬ (3 : ℕ) ∣ 2) hsub
  refine ⟨D.frame.range, D.frame, ?_, ?_, ?_, D.frame_injective, rfl, ?_⟩
  · rw [← Subgroup.map_top D.frame]
    exact CFSG.Open.IsElemAbelian.map isElemAbelian_top_f4 D.frame
  · exact (card_range_of_injective D.frame_injective).ge
  · intro c hc hc3
    exact D.mem_frame_range_of_commute c
      (fun s => ((Subgroup.mem_centralizer_iff.mp hc) _ ⟨s, rfl⟩).symm) hc3
  · intro β hβ hβA
    obtain ⟨x, σ, -, hβeq⟩ := E6QPlusThree.exists_inner_normalForm_E6 h3'
      (p := 3) (by norm_num) β hβ
    have hβι : ∀ s, β (D.frame s) = x * D.frame s * x⁻¹ := fun s => by
      apply Subtype.ext
      rw [hβeq (D.frame s), D.entrywise_frame]
      rfl
    have hxN : x ∈ D.N :=
      D.mem_N_of_conj x (fun s => by rw [← hβι s]; exact hβA _ ⟨s, rfl⟩)
    refine ⟨D.weyl ⟨x, hxN⟩, fun s => ?_⟩
    rw [hβι (Multiplicative.ofAdd s)]
    exact D.conj_frame ⟨x, hxN⟩ s

theorem e6ThreeSCReference_holds
    {K : Type} [Field K] [Finite K] [CharP K 2]
    (h3 : 3 ∣ Nat.card K + 1) (D : E6QPlusThree.E6QPlusThreeFrame K)
    {A : Subgroup (adjointGroup .E6 K)}
    (hA : IsElemAbelian 3 A) (hA4 : 3 ^ 4 ≤ Nat.card A)
    (hASC : ∀ c ∈ Subgroup.centralizer (A : Set (adjointGroup .E6 K)), c ^ 3 = 1 → c ∈ A) :
    ∃ c : adjointGroup .E6 K, A = D.frame.range.map (MulAut.conj c).toMonoidHom := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Finite (adjointGroup .E6 K) := generated_group_finite .E6 K
  obtain ⟨P, hP⟩ := D.exists_sylow_le
  obtain ⟨c, -, hc⟩ := CFSG.QuasiDihedralFusion.exists_conj_le_sylow (p := 3)
    (H := adjointGroup .E6 K) ⊤ P le_top A le_top (CFSG.Open.IsElemAbelian.isPGroup hA)
  obtain ⟨hA₁, hA₁4, hA₁SC⟩ := sc_transport hA hA4 hASC c
  have hA₁N : A.map (MulAut.conj c).toMonoidHom ≤ D.N := hc.trans hP
  let φ : A.map (MulAut.conj c).toMonoidHom →* WeylGroup .F4 :=
    D.weyl.comp (Subgroup.inclusion hA₁N)
  have hbot : φ.range = ⊥ := by
    by_contra hne
    have hlt := card_lt_of_weylHom (τ := Tag.F4) (p := 3)
      (NoOffExc.ggWeylNoOffender_F4 Nat.prime_three (by norm_num))
      D.frame D.frame_injective (A := A.map (MulAut.conj c).toMonoidHom) hA₁ φ
      (fun a s => D.conj_frame (Subgroup.inclusion hA₁N a) s)
      (fun a ha => D.mem_frame_range_of_weyl_eq_one (Subgroup.inclusion hA₁N a) ha
        (hA₁.2 (a : adjointGroup .E6 K) a.2)) hne
    change Nat.card (A.map (MulAut.conj c).toMonoidHom) < 3 ^ 4 at hlt
    omega
  have hAle : A.map (MulAut.conj c).toMonoidHom ≤ D.frame.range := by
    intro a ha
    have hmem : φ ⟨a, ha⟩ ∈ φ.range := ⟨⟨a, ha⟩, rfl⟩
    rw [hbot] at hmem
    have hφa : φ ⟨a, ha⟩ = 1 := by simpa using hmem
    exact D.mem_frame_range_of_weyl_eq_one ⟨a, hA₁N ha⟩ hφa (hA₁.2 a ha)
  have hcomm : ∀ x ∈ D.frame.range, ∀ y ∈ D.frame.range, x * y = y * x := by
    rintro x ⟨s, rfl⟩ y ⟨t, rfl⟩
    calc D.frame s * D.frame t = D.frame (s * t) := (map_mul _ _ _).symm
      _ = D.frame (t * s) := congrArg D.frame (mul_comm s t)
      _ = D.frame t * D.frame s := map_mul _ _ _
  have hpow : ∀ x ∈ D.frame.range, x ^ 3 = 1 := by
    rintro x ⟨s, rfl⟩
    rw [← map_pow]
    have hs : s ^ 3 = 1 := by
      apply Multiplicative.toAdd.injective
      rw [toAdd_pow, toAdd_one]
      funext i
      rw [Pi.smul_apply, Pi.zero_apply, nsmul_eq_mul, ZMod.natCast_self, zero_mul]
    rw [hs, map_one]
  have hrange_le : D.frame.range ≤ A.map (MulAut.conj c).toMonoidHom := by
    intro x hx
    exact hA₁SC x (Subgroup.mem_centralizer_iff.mpr fun a ha =>
      (hcomm x hx a (hAle ha)).symm) (hpow x hx)
  have heq : A.map (MulAut.conj c).toMonoidHom = D.frame.range := le_antisymm hAle hrange_le
  refine ⟨c⁻¹, ?_⟩
  calc A = (A.map (MulAut.conj c).toMonoidHom).map (MulAut.conj c⁻¹).toMonoidHom := by
        rw [Subgroup.map_map]
        have hcomp : (MulAut.conj c⁻¹).toMonoidHom.comp (MulAut.conj c).toMonoidHom =
            MonoidHom.id (adjointGroup .E6 K) := by
          refine MonoidHom.ext fun x => ?_
          show MulAut.conj c⁻¹ (MulAut.conj c x) = x
          rw [MulAut.conj_apply, MulAut.conj_apply]
          group
        rw [hcomp, Subgroup.map_id]
    _ = D.frame.range.map (MulAut.conj c⁻¹).toMonoidHom := by rw [heq]

theorem e6ThreeSCUnique_holds :
    E6ThreeSCUnique := by
  unfold E6ThreeSCUnique
  intro K _ _ _ h3 A A' hA hA4 hASC hA' hA'4 hA'SC
  obtain ⟨D⟩ := E6QPlusThree.nonempty_e6QPlusThreeFrame h3
  obtain ⟨c, hc⟩ := e6ThreeSCReference_holds h3 D hA hA4 hASC
  obtain ⟨c', hc'⟩ := e6ThreeSCReference_holds h3 D hA' hA'4 hA'SC
  refine ⟨c' * c⁻¹, ?_⟩
  have hcomp : (MulAut.conj (c' * c⁻¹)).toMonoidHom.comp (MulAut.conj c).toMonoidHom =
      (MulAut.conj c').toMonoidHom := by
    ext x
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    group
  rw [hc', hc, Subgroup.map_map, hcomp]

end Holds

end CFSG.StandardType.ExcFrames
