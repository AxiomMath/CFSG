module

public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelEFrame
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelA2BlockE
public import CFSG.LocalAnalysis.StandardType.GGSixBstarE6ThreeIndex
public import CFSG.LocalAnalysis.StandardType.GGSixBstarE6ThreeConjCore
public import CFSG.LocalAnalysis.StandardType.GGTwE6ThreeRankFiveSylow

public section

namespace CFSG.StandardType.E6ThreeModel

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley TableBExc.E6Three
  CFSG.RankThree.CentralCover CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

variable {K : Type} [Field K] [Finite K]

private theorem exists_conj_xHat_data [Finite K] [CharP K 2] (h3 : 3 ∣ Nat.card K - 1)
    {ζ : Kˣ} (hζo : orderOf ζ = 3) (hζ : ζ ^ 3 = 1)
    {X : Subgroup (MulAut (adjointGroup .E6 K))} (hX : IsElemAbelian 3 X)
    (hXI : X ≤ (hatAut .E6 K).range) :
    ∃ (γ : MulAut (adjointGroup .E6 K)) (_ : γ ∈ (hatAut .E6 K).range)
      (E : Subgroup (ModGL .E6 K)),
      E ≤ hatGroup .E6 K ∧ IsElemAbelian 3 E ∧
      E ≤ xHat .E6 K modelHomE6.range ∧ Nat.card E = Nat.card X ∧
      (∀ φ, φ ∈ X.map (MulAut.conj γ).toMonoidHom ↔
        ∃ e ∈ E, ∃ he : e ∈ hatGroup .E6 K, hatAut .E6 K ⟨e, he⟩ = φ) := by
  have := Fact.mk Nat.prime_three
  have : Finite (hatGroup .E6 K) := finite_hatGroup
  set κ := hatAut .E6 K with hκ
  set Y : Subgroup (hatGroup .E6 K) := X.comap κ with hY
  set f : Y →* X := (κ.comp Y.subtype).codRestrict X (fun y => y.2) with hf
  have hfs : Function.Surjective f := by
    rintro ⟨φ, hφ⟩
    obtain ⟨x, rfl⟩ := hXI hφ
    exact ⟨⟨x, hφ⟩, rfl⟩
  obtain ⟨Q₀⟩ := (inferInstance : Nonempty (Sylow 3 Y))
  have hXp : IsPGroup 3 (⊤ : Subgroup X) := fun g => by
    obtain ⟨k, hk⟩ := TableB.isPGroup_of_isElemAbelian hX ⟨g.1, g.1.2⟩
    exact ⟨k, Subtype.ext hk⟩
  have hQ : (Q₀ : Subgroup Y).map f = ⊤ :=
    ((Q₀.mapSurjective hfs).is_maximal' hXp le_top).symm
  set P : Subgroup (hatGroup .E6 K) := (Q₀ : Subgroup Y).map Y.subtype with hP
  have hP3 : IsPGroup 3 P := Q₀.isPGroup'.map _
  have hPX : P.map κ = X := by
    have hcomp : κ.comp Y.subtype = X.subtype.comp f := MonoidHom.ext fun _ => rfl
    rw [hP, Subgroup.map_map, hcomp, ← Subgroup.map_map, hQ, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  obtain ⟨c, hc⟩ := TableBF4.exists_conj_le_of_not_dvd_index Nat.prime_three
    (not_three_dvd_index_xHat h3) hP3
  set P' := P.map (MulAut.conj c).toMonoidHom with hP'
  set E : Subgroup (ModGL .E6 K) := P'.map (hatGroup .E6 K).subtype with hEdef
  have hEX : E ≤ xHat .E6 K modelHomE6.range := by
    rintro _ ⟨p, hp, rfl⟩
    exact Subgroup.mem_subgroupOf.mp (hc hp)
  have hEH : E ≤ hatGroup .E6 K := by
    rintro _ ⟨p, hp, rfl⟩
    exact p.2
  have hker : ∀ p ∈ P', κ p = 1 → p = 1 := fun p hp h1 =>
    eq_one_of_hatAut_eq_one (xHat_le_monoHat _ (hEX ⟨p, hp, rfl⟩)) h1
  have hP'X : P'.map κ = X.map (MulAut.conj (κ c)).toMonoidHom := by
    have hcomp : κ.comp (MulAut.conj c).toMonoidHom = (MulAut.conj (κ c)).toMonoidHom.comp κ :=
      MonoidHom.ext fun p => by
        simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul,
          map_inv]
    rw [hP', Subgroup.map_map, hcomp, ← Subgroup.map_map, hPX]
  have hcardP' : Nat.card P' = Nat.card X := by
    rw [← card_map_eq_of_ker κ hker, hP'X,
      Subgroup.card_map_of_injective (MulAut.conj (κ c)).injective]
  have hcardE : Nat.card E = Nat.card X := by
    rw [hEdef, Subgroup.card_map_of_injective (hatGroup .E6 K).subtype_injective, hcardP']
  have hXc : IsElemAbelian 3 (X.map (MulAut.conj (κ c)).toMonoidHom) :=
    TableB.isElemAbelian_map hX _
  have hP'ab : ∀ p ∈ P', ∀ p' ∈ P', p * p' = p' * p := by
    intro p hp p' hp'
    have h1 : κ (p * p' * (p' * p)⁻¹) = 1 := by
      rw [map_mul, map_mul, map_inv, map_mul,
        TableB.IsElemAbelian.comm hXc (hP'X ▸ ⟨p, hp, rfl⟩ : κ p ∈ _)
          (hP'X ▸ ⟨p', hp', rfl⟩ : κ p' ∈ _), mul_inv_cancel]
    have h2 := hker _ (mul_mem (mul_mem hp hp') (inv_mem (mul_mem hp' hp))) h1
    exact mul_inv_eq_one.mp h2
  have hP'3 : ∀ p ∈ P', p ^ 3 = 1 := by
    intro p hp
    refine hker _ (pow_mem hp 3) ?_
    rw [map_pow]
    exact hXc.2 _ (hP'X ▸ ⟨p, hp, rfl⟩ : κ p ∈ _)
  have hP'el : IsElemAbelian 3 P' :=
    ⟨⟨⟨fun a b => Subtype.ext (hP'ab a a.2 b b.2)⟩⟩, hP'3⟩
  have hE : IsElemAbelian 3 E := TableB.isElemAbelian_map hP'el _
  have hP'X' : ∀ φ, φ ∈ X.map (MulAut.conj (κ c)).toMonoidHom ↔
      ∃ e ∈ E, ∃ he : e ∈ hatGroup .E6 K, κ ⟨e, he⟩ = φ := by
    intro φ
    rw [← hP'X]
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact ⟨(p : ModGL .E6 K), by rw [hEdef]; exact Subgroup.mem_map.mpr ⟨p, hp, rfl⟩, p.2, rfl⟩
    · rintro ⟨e, he, hhe, rfl⟩
      rw [hEdef] at he
      obtain ⟨p, hp, hpe⟩ := Subgroup.mem_map.mp he
      refine ⟨p, hp, ?_⟩
      exact congrArg κ (Subtype.ext hpe)
  exact ⟨κ c, ⟨c, by rw [hκ]⟩, E, hEH, hE, hEX, hcardE, hP'X'⟩

theorem eFrame_shape [CharP K 2] {ζ : Kˣ} (hζo : orderOf ζ = 3) (hζ : ζ ^ 3 = 1) :
    (eFrame K ζ hζ).Shape := by
  intro X hXH hXel hX5
  have h3 : 3 ∣ Nat.card K - 1 := by
    have h : orderOf ζ ∣ Nat.card Kˣ := orderOf_dvd_natCard ζ
    rw [Nat.card_units] at h
    rwa [hζo] at h
  obtain ⟨γ₀, hγ₀, E, hEH, hEel, hEX, hcardE, hP'X⟩ :=
    exists_conj_xHat_data h3 hζo hζ hXel hXH
  have hE5 : 3 ^ 5 ≤ Nat.card E := by rw [hcardE]; exact hX5
  rcases NoOffTwE6Three.torus_or_cyclic hζo hζ hEel hEX hE5 with hdiag | ⟨i, hEXi⟩
  ·
    refine ⟨γ₀, hγ₀, fun x hx => ?_⟩
    have hmem : γ₀ * x * γ₀⁻¹ ∈ X.map (MulAut.conj γ₀).toMonoidHom := ⟨x, hx, rfl⟩
    obtain ⟨e, he, hhe, heq⟩ := (hP'X _).mp hmem
    obtain ⟨v, hv⟩ := hdiag e he
    refine ⟨Multiplicative.ofAdd v, ?_⟩
    rw [← heq]
    rw [show (⟨e, hhe⟩ : hatGroup .E6 K) =
        ⟨rootDiagUnit .E6 (zetaVec ζ hζ v), rootDiagUnit_mem_hatGroup _⟩ from
      Subtype.ext hv]
    exact NoOffE6Three.hatAut_rootDiagUnit_eq_rootDiagAutHom (zetaVec ζ hζ v)
  ·
    obtain ⟨z, hz, hzE⟩ := a2BlockSplit_holds h3 hζ hζo i hEel hEH hEXi
    let zH : hatGroup .E6 K := ⟨z, hz⟩
    refine ⟨hatAut .E6 K zH * γ₀, ?_, fun x hx => ?_⟩
    · exact mul_mem (MonoidHom.mem_range.mpr ⟨zH, rfl⟩) hγ₀
    · have hmem : γ₀ * x * γ₀⁻¹ ∈ X.map (MulAut.conj γ₀).toMonoidHom := ⟨x, hx, rfl⟩
      obtain ⟨e, he, hhe, heq⟩ := (hP'X _).mp hmem
      obtain ⟨v, hv⟩ := hzE e he
      refine ⟨Multiplicative.ofAdd v, ?_⟩
      have h1 : (hatAut .E6 K zH * γ₀) * x * (hatAut .E6 K zH * γ₀)⁻¹ =
          hatAut .E6 K (zH * ⟨e, hhe⟩ * zH⁻¹) := by
        rw [map_mul, map_mul, map_inv, heq]
        group
      rw [h1]
      rw [show zH * ⟨e, hhe⟩ * zH⁻¹ =
          ⟨rootDiagUnit .E6 (zetaVec ζ hζ v), rootDiagUnit_mem_hatGroup _⟩ from
        Subtype.ext (by simpa using hv)]
      exact NoOffE6Three.hatAut_rootDiagUnit_eq_rootDiagAutHom (zetaVec ζ hζ v)

end CFSG.StandardType.E6ThreeModel
