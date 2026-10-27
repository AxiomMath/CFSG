module

public import CFSG.LocalAnalysis.WeakClosure81.EightThirteenPGapCover
public import CFSG.LocalAnalysis.WeakClosure81.EightThirteenPGapA2Model
public import CFSG.LocalAnalysis.WeakClosure81.EightThirteenPGapPull
import CFSG.Open.StatedCenterThree

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup

private lemma wcgapc2_injOn_of_isPGroup {G₀ G : Type} [Group G₀] [Finite G₀] [Group G]
    (α : G₀ →* G) (hodd : Odd (Nat.card ↥α.ker)) {P : Subgroup G₀}
    (hP : IsPGroup 2 P) : ∀ x ∈ P, ∀ y ∈ P, α x = α y → x = y := by
  obtain ⟨n, hn⟩ := hP.exists_card_dvd_pow
  have hcop : Nat.Coprime (Nat.card ↥α.ker) (Nat.card ↥P) :=
    Nat.Coprime.of_dvd (dvd_refl _) hn (hodd.coprime_two_right.pow_right n)
  have hinf : α.ker ⊓ P = ⊥ := Subgroup.inf_eq_bot_of_coprime hcop
  intro x hx y hy hxy
  have hmem : x⁻¹ * y ∈ α.ker ⊓ P :=
    Subgroup.mem_inf.mpr
      ⟨by rw [MonoidHom.mem_ker, map_mul, map_inv, hxy, inv_mul_cancel],
        P.mul_mem (P.inv_mem hx) hy⟩
  rw [hinf] at hmem
  exact inv_mul_eq_one.mp (by simpa using hmem)

private lemma wcgapc2_card_map_of_injOn {G₀ G : Type} [Group G₀] [Group G] (α : G₀ →* G)
    (P H : Subgroup G₀) (hHP : H ≤ P)
    (hinj : ∀ x ∈ P, ∀ y ∈ P, α x = α y → x = y) :
    Nat.card ↥(H.map α) = Nat.card ↥H := by
  have hinj' : Function.Injective (α.comp P.subtype) :=
    fun x y hxy => Subtype.ext (hinj x x.2 y y.2 hxy)
  calc Nat.card ↥(H.map α)
      = Nat.card ↥(((H.subgroupOf P).map P.subtype).map α) := by
        rw [Subgroup.map_subgroupOf_eq_of_le hHP]
    _ = Nat.card ↥((H.subgroupOf P).map (α.comp P.subtype)) := by
        rw [Subgroup.map_map]
    _ = Nat.card ↥(H.subgroupOf P) :=
        Nat.card_congr
          (Subgroup.equivMapOfInjective (H.subgroupOf P) (α.comp P.subtype) hinj').symm.toEquiv
    _ = Nat.card ↥H := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHP).toEquiv

private lemma wcgapc2_map_inf_centralizer_of_injOn {G₀ G : Type} [Group G₀] [Group G]
    (α : G₀ →* G) (P : Subgroup G₀)
    (hinj : ∀ x ∈ P, ∀ y ∈ P, α x = α y → x = y) :
    (P ⊓ Subgroup.centralizer (P : Set G₀)).map α =
      P.map α ⊓ Subgroup.centralizer ((P.map α : Subgroup G) : Set G) := by
  apply le_antisymm
  · intro s hs
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hs
    obtain ⟨hzP, hzc⟩ := Subgroup.mem_inf.mp hz
    refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_map.mpr ⟨z, hzP, rfl⟩, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro s' hs'
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp hs'
    rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.mp hzc t ht]
  · intro s hs
    obtain ⟨hsS, hsc⟩ := Subgroup.mem_inf.mp hs
    obtain ⟨z, hzP, rfl⟩ := Subgroup.mem_map.mp hsS
    refine Subgroup.mem_map.mpr ⟨z, Subgroup.mem_inf.mpr ⟨hzP, ?_⟩, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    have hcomm := Subgroup.mem_centralizer_iff.mp hsc (α t)
      (Subgroup.mem_map.mpr ⟨t, ht, rfl⟩)
    have hker : α (z * t * z⁻¹ * t⁻¹) = 1 := by
      simp only [map_mul, map_inv]
      rw [← hcomm]
      group
    have hmem : z * t * z⁻¹ * t⁻¹ ∈ P :=
      P.mul_mem (P.mul_mem (P.mul_mem hzP ht) (P.inv_mem hzP)) (P.inv_mem ht)
    have h1 : z * t * z⁻¹ * t⁻¹ = 1 :=
      hinj _ hmem 1 P.one_mem (by simpa using hker)
    have ht1 : z * t * z⁻¹ = t := by
      have := congrArg (· * t) h1
      simpa [mul_assoc] using this
    have hzt : z * t = t * z := by
      have := congrArg (· * z) ht1
      simpa [mul_assoc] using this
    exact hzt.symm

theorem a2KleinData_of_cover {G₀ G : Type} [Group G₀] [Finite G₀] [Group G] (α : G₀ →* G)
    (hα : Function.Surjective α) (hodd : Odd (Nat.card ↥α.ker))
    (h : ∀ S₀ : Sylow 2 G₀, A2KleinData (S₀ : Subgroup G₀)) (S : Sylow 2 G) :
    A2KleinData (S : Subgroup G) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S₀, hS₀eq⟩ := Sylow.mapSurjective_surjective (p := 2) hα S
  let P : Subgroup G₀ := (S₀ : Subgroup G₀)
  have hSeq : (S : Subgroup G) = P.map α := by
    have h := hS₀eq ▸ Sylow.coe_mapSurjective hα S₀
    simpa [P] using h
  obtain ⟨hPcard, hZPcard, h₀, hh₀N, hfix₀⟩ := h S₀
  have hinj : ∀ x ∈ P, ∀ y ∈ P, α x = α y → x = y :=
    wcgapc2_injOn_of_isPGroup (P := P) α hodd S₀.isPGroup'
  have hcardS : Nat.card ↥(S : Subgroup G) = 64 := by
    rw [hSeq, wcgapc2_card_map_of_injOn α P P le_rfl hinj]
    exact hPcard
  have hZeq : (P ⊓ Subgroup.centralizer (P : Set G₀)).map α =
      (S : Subgroup G) ⊓ Subgroup.centralizer ((S : Subgroup G) : Set G) := by
    rw [hSeq]
    exact wcgapc2_map_inf_centralizer_of_injOn α P hinj
  have hZcard : Nat.card ↥((S : Subgroup G) ⊓
      Subgroup.centralizer ((S : Subgroup G) : Set G)) = 4 := by
    rw [← hZeq, wcgapc2_card_map_of_injOn α P
      (P ⊓ Subgroup.centralizer (P : Set G₀)) inf_le_left hinj]
    exact hZPcard
  refine ⟨hcardS, hZcard, α h₀, ?_, ?_⟩
  · rw [hSeq]
    exact Subgroup.le_normalizer_map (H := P) α (Subgroup.mem_map.mpr ⟨h₀, hh₀N, rfl⟩)
  · intro z hz hz1
    rw [← hZeq] at hz
    obtain ⟨z₀, hz₀, rfl⟩ := Subgroup.mem_map.mp hz
    have hz₀P : z₀ ∈ P := (Subgroup.mem_inf.mp hz₀).1
    have hfix := hfix₀ z₀ hz₀ (fun h0 => hz1 (by rw [h0, map_one]))
    intro heq
    apply hfix
    have hmem : h₀ * z₀ * h₀⁻¹ ∈ P :=
      (Subgroup.mem_normalizer_iff.mp hh₀N z₀).mp hz₀P
    refine hinj (h₀ * z₀ * h₀⁻¹) hmem z₀ hz₀P ?_
    simpa only [map_mul, map_inv] using heq

theorem a2KleinData_of_hasSL3Cover {G : Type} [Group G] [Finite G] (h : HasSL3Cover G)
    (S : Sylow 2 G) : A2KleinData (S : Subgroup G) := by
  obtain ⟨F, hF, hFin, hFcard, α, hα, hker⟩ := h
  letI : Field F := hF
  letI : Finite F := hFin
  have hcenter : Nat.card (Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) F)) = 3 := by
    rw [Nat.card_congr (Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity' (0 : Fin 3)).toEquiv,
      Fintype.card_fin]
    exact CFSG.Open.StatedCenterThree.card_rootsOfUnity_three (by norm_num [hFcard])
  have hdvd : Nat.card ↥α.ker ∣ 3 := by
    have h3 := Subgroup.card_dvd_of_le hker
    convert h3 using 1
    exact hcenter.symm
  have hodd : Odd (Nat.card ↥α.ker) := by
    rcases Nat.prime_three.eq_one_or_self_of_dvd (Nat.card ↥α.ker) hdvd with h1 | h3
    · rw [h1]; exact odd_one
    · rw [h3]; exact ⟨1, by norm_num⟩
  exact a2KleinData_of_cover α hα hodd
    (fun S₀ => @a2KleinData_slThree F hF hFin hFcard S₀) S

theorem borelGL32CenterOn_shapeSL3 :
    BorelGL32CenterOn ShapeSL3 :=
  borelGL32CenterOn_of_kills ShapeSL3 fun Y _ _ L hL S hSy =>
    borelKills_center_of_a2 hSy.toSylow.isPGroup'
      (a2KleinData_of_hasSL3Cover (hasSL3Cover_of_shapeSL3 hL) hSy.toSylow)

theorem borelGL32CenterOn_shapeL3 : BorelGL32CenterOn ShapeL3 :=
  borelGL32CenterOn_of_kills ShapeL3 fun Y _ _ L hL S hSy =>
    borelKills_center_of_a2 hSy.toSylow.isPGroup'
      (a2KleinData_of_hasSL3Cover (hasSL3Cover_of_shapeL3 hL) hSy.toSylow)

end CFSG.LocalAnalysis.WeakClosure81

end
