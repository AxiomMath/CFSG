module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoUnitaryAux
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoPairing
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoTransfer
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoInner
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoInnerQ
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoAutL
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoModel
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoCover
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoCoverTwo
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoSixAux
public import CFSG.LocalAnalysis.StandardType.GGUSixTwoLocalSetting

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Open

variable {G : Type} [Group G] [Finite G]

private theorem exists_not_mem_and_map_eq_torU {K : Type} [Field K] [Finite K]
    (hG : IsCharTwoType G) (hK4 : Nat.card K = 4)
    {ω : K} (hω : ω ^ 2 + ω + 1 = 0) {Bs L M : Subgroup G} {x : G}
    (θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))
    (hperf : commutator ↥L = ⊤) (hBs : IsElemAbelian 3 Bs) (hNT : GGNoTransvection 3 Bs)
    (hcard : Nat.card Bs = 3 ^ 5) (hxB : x ∈ Bs) (hx1 : x ≠ 1)
    (hLx : L ≤ Subgroup.centralizer {x})
    (hN : (L.subgroupOf (Subgroup.centralizer {x})).Normal)
    (hcyc : ∀ S : Subgroup G, IsPGroup 3 S →
      S ≤ Subgroup.centralizer (L : Set G) → IsCyclic S)
    (hstar : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs)
    (hBsN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hI : ∀ b ∈ Bs, ∃ ψ ∈ LargeEvenMatConjImage
        (LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))
        (LargeEvenGUSet (Fin 6) K (2 ^ 1)),
      LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) ψ)
    (hW : GGWeylOfType 3 CoxeterMatrix.E₆ (ggAutomizer L Bs ⊔ ggAutomizer M Bs)) :
    x ∉ L ∧
      ∃ φ : L ≃* LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)),
        ((Bs ⊓ L).subgroupOf L).map φ.toMonoidHom = USixTwo.torU K := by
  have horderx : orderOf x = 3 := orderOf_eq_prime (hBs.2 x hxB) hx1
  have hBL : Bs ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers x :=
    inf_centralizer_eq_zpowers_of_elemAbelian Nat.prime_three hBs hxB hx1 hLx
      (fun S hSL hSp => hcyc S hSp hSL)
  have hZ2 : IsPGroup 2 (Subgroup.center L) :=
    E6QTwo.isPGroup_two_center hK4 θ hperf hBs hNT hcard hxB hx1 hLx hBL hstar hBsN hI hW
  obtain ⟨-, θ', hmap⟩ :=
    E6QTwo.card_inf_eq_and_exists_map_eq_torU_of_isPGroup hK4 θ hperf hZ2 hBs hcard hxB
      hx1 hBL hstar hBsN hI
  have hxL : x ∉ L := StandardType.not_mem_of_isPGroup_two_center hZ2 horderx hLx
  have hconj : ∃ n ∈ Subgroup.normalizer (Bs : Set G), ∃ h : n * x * n⁻¹ ∈ L,
      θ' (QuotientGroup.mk (⟨n * x * n⁻¹, h⟩ : L)) = USixTwo.threeA hω :=
    exists_mem_normalizer_conj_eq_threeA hK4 hω θ' hZ2 hmap hBs hNT hcard hxB hxL hLx hW
      card_coxeterE6_group
  have hZ : Subgroup.center L = ⊥ :=
    E6QTwo.center_eq_bot_of_isPGroup_two hG hK4 hω θ' hperf hZ2 horderx hLx hN hcyc
      hBs hxB hcard hmap hconj
  obtain ⟨-, φ, hmapφ⟩ :=
    E6QTwo.card_inf_eq_and_exists_map_eq_torU hK4 θ hZ hBs hcard hxB hx1 hLx
      hBL hstar hBsN hI
  exact ⟨hxL, φ, hmapφ⟩

private theorem exists_e6_model
    [Fact (Nat.Prime 3)] {Bs L M : Subgroup G} (hNT : GGNoTransvection 3 Bs)
    (hW : GGWeylOfType 3 CoxeterMatrix.E₆ (ggAutomizer L Bs ⊔ ggAutomizer M Bs))
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [Finite V]
    (ι : Additive ↥Bs ≃+ V) (hVcard : Nat.card V = 3 ^ 5) :
    ∃ (h : Fin 6 → V) (α : Fin 6 → Module.Dual (ZMod 3) V) (hα : ∀ i, α i (h i) = 2)
      (β : LinearMap.BilinForm (ZMod 3) V),
      (∀ i j, α i (h j) = (CartanMatrix.E 6 i j : ZMod 3)) ∧
      (∀ i v, β (h i) v = α i v) ∧
      Nat.card (E6QTwo.e6Weyl hα) = 51840 ∧
      (ggAutomizer L Bs ⊔ ggAutomizer M Bs).map (ggLin (p := 3) ι) = E6QTwo.e6Weyl hα ∧
      (∀ ψ ∈ ggAutomizer L Bs ⊔ ggAutomizer M Bs,
        ggLin (p := 3) ι ψ ∈ E6QTwo.e6Weyl hα) := by
  have hA : ∀ ψ ∈ ggAutomizer L Bs ⊔ ggAutomizer M Bs, ψ ∈ ggInduced ⊤ Bs := by
    intro ψ hψ
    exact mem_ggInduced_top_of_mem_ggAutomizer
      (sup_le (ggAutomizer_mono Bs le_top) (ggAutomizer_mono Bs le_top) hψ)
  obtain ⟨e, h, α, hα, he, hP⟩ := E6QTwo.exists_cartan_pairing_E6 hNT hW hA ι
  obtain ⟨β, hβ⟩ := E6QTwo.exists_bilinForm hP hVcard
  have hmapA : (ggAutomizer L Bs ⊔ ggAutomizer M Bs).map (ggLin (p := 3) ι) =
      E6QTwo.e6Weyl hα :=
    E6QTwo.map_ggLin_eq_e6Weyl ι e hα he
  have hWcard : Nat.card (E6QTwo.e6Weyl hα) = 51840 := by
    rw [E6QTwo.card_e6Weyl_eq ι e hα he]
    rw [show Nat.card ↥(ggAutomizer L Bs ⊔ ggAutomizer M Bs) =
        Nat.card (CoxeterMatrix.E₆).Group from
      (Nat.card_congr e.toEquiv).symm, card_coxeterE6_group]
  have hmem_e6 : ∀ ψ ∈ ggAutomizer L Bs ⊔ ggAutomizer M Bs,
      ggLin (p := 3) ι ψ ∈ E6QTwo.e6Weyl hα := by
    intro ψ hψ
    rw [← hmapA]
    exact Subgroup.mem_map_of_mem _ hψ
  exact ⟨h, α, hα, β, hP, hβ, hWcard, hmapA, hmem_e6⟩

private theorem exists_vx_and_stabilizer {K : Type} [Field K] [Finite K]
    [Fact (Nat.Prime 3)] (hK4 : Nat.card K = 4) {Bs L M : Subgroup G} {x : G}
    (φ : L ≃* LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))
    (hmapφ : ((Bs ⊓ L).subgroupOf L).map φ.toMonoidHom = USixTwo.torU K)
    (hBs : IsElemAbelian 3 Bs) (hcard : Nat.card Bs = 3 ^ 5) (hxB : x ∈ Bs)
    (hx1 : x ≠ 1) (hxL : x ∉ L) (hLx : L ≤ Subgroup.centralizer {x})
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [Finite V]
    (ι : Additive ↥Bs ≃+ V) (hVcard : Nat.card V = 3 ^ 5)
    {h : Fin 6 → V} {α : Fin 6 → Module.Dual (ZMod 3) V} {β : LinearMap.BilinForm (ZMod 3) V}
    (hP : ∀ i j, α i (h j) = (CartanMatrix.E 6 i j : ZMod 3))
    (hβ : ∀ i v, β (h i) v = α i v) (hα : ∀ i, α i (h i) = 2)
    (hWcard : Nat.card (E6QTwo.e6Weyl hα) = 51840)
    (hmem_e6 : ∀ ψ ∈ ggAutomizer L Bs ⊔ ggAutomizer M Bs,
      ggLin (p := 3) ι ψ ∈ E6QTwo.e6Weyl hα) :
    ∃ vx : V, vx = ι (Additive.ofMul (⟨x, hxB⟩ : ↥Bs)) ∧ vx ≠ 0 ∧
      (∀ ψ ∈ ggAutomizer L Bs, ggLin (p := 3) ι ψ vx = vx) ∧ β vx vx = 2 ∧
      (ggAutomizer L Bs).map (ggLin (p := 3) ι) =
        (MulAction.stabilizer (E6QTwo.e6Weyl hα) vx).map (E6QTwo.e6Weyl hα).subtype := by
  let vx : V := ι (Additive.ofMul (⟨x, hxB⟩ : ↥Bs))
  have hvxdef : vx = ι (Additive.ofMul (⟨x, hxB⟩ : ↥Bs)) := rfl
  have hvx : vx ≠ 0 := by
    intro h0
    rw [hvxdef] at h0
    have h1 : Additive.ofMul (⟨x, hxB⟩ : ↥Bs) = 0 := ι.injective (by rw [h0, map_zero])
    have h2 : (⟨x, hxB⟩ : ↥Bs) = 1 := by
      simpa using congrArg Additive.toMul h1
    exact hx1 (by simpa using congrArg Subtype.val h2)
  have hfixAL : ∀ ψ ∈ ggAutomizer L Bs, ψ ⟨x, hxB⟩ = ⟨x, hxB⟩ := by
    intro ψ hψ
    exact ggAutomizer_apply_eq_of_le_centralizer hLx hψ
  have hfixv : ∀ ψ ∈ ggAutomizer L Bs, ggLin (p := 3) ι ψ vx = vx := by
    intro ψ hψ
    rw [hvxdef, ggLin_apply_ofMul, hfixAL ψ hψ]
  have hmapALle : (ggAutomizer L Bs).map (ggLin (p := 3) ι) ≤
      (MulAction.stabilizer (E6QTwo.e6Weyl hα) vx).map (E6QTwo.e6Weyl hα).subtype := by
    rintro _ ⟨ψ, hψ, rfl⟩
    have hstab : (⟨ggLin (p := 3) ι ψ,
        hmem_e6 ψ ((le_sup_left : ggAutomizer L Bs ≤
          ggAutomizer L Bs ⊔ ggAutomizer M Bs) hψ)⟩ :
        ↥(E6QTwo.e6Weyl hα)) ∈ MulAction.stabilizer (E6QTwo.e6Weyl hα) vx := by
      rw [MulAction.mem_stabilizer_iff, Subgroup.smul_def, LinearEquiv.smul_def]
      exact hfixv ψ hψ
    exact Subgroup.mem_map_of_mem (E6QTwo.e6Weyl hα).subtype hstab
  have hALcard720 : 720 ≤ Nat.card (ggAutomizer L Bs) :=
    E6QTwo.le_card_ggAutomizer hK4 φ hmapφ hBs hcard hxB hxL hLx
  have hStabge : Nat.card (ggAutomizer L Bs) ≤
      Nat.card (MulAction.stabilizer (E6QTwo.e6Weyl hα) vx) := by
    have h' := Subgroup.card_le_of_le hmapALle
    rwa [Subgroup.card_map_of_injective (E6QTwo.e6Weyl hα).subtype_injective,
      Subgroup.card_map_of_injective (ggLin_injective ι)] at h'
  have hcases := E6QTwo.stabilizer_cases hP hVcard hβ hα hWcard hvx
  obtain ⟨hBxx, hstabcard⟩ : β vx vx = 2 ∧
      Nat.card (MulAction.stabilizer (E6QTwo.e6Weyl hα) vx) = 720 := by
    rcases hcases with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨h1, h2⟩
    · omega
    · omega
  have hcardAL : Nat.card (ggAutomizer L Bs) = 720 := by omega
  have himg_eq : (ggAutomizer L Bs).map (ggLin (p := 3) ι) =
      (MulAction.stabilizer (E6QTwo.e6Weyl hα) vx).map (E6QTwo.e6Weyl hα).subtype := by
    refine Subgroup.eq_of_le_of_card_ge hmapALle ?_
    rw [Subgroup.card_map_of_injective (E6QTwo.e6Weyl hα).subtype_injective,
      Subgroup.card_map_of_injective (ggLin_injective ι), hcardAL, hstabcard]
  exact ⟨vx, hvxdef, hvx, hfixv, hBxx, himg_eq⟩

omit [Finite G] in
private theorem mem_ggAutomizer_of_fix [Fact (Nat.Prime 3)] {Bs L M : Subgroup G} {x : G}
    (hxB : x ∈ Bs) {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (ι : Additive ↥Bs ≃+ V) {h : Fin 6 → V} {α : Fin 6 → Module.Dual (ZMod 3) V}
    (hα : ∀ i, α i (h i) = 2) {vx : V}
    (hvxdef : vx = ι (Additive.ofMul (⟨x, hxB⟩ : ↥Bs)))
    (himg_eq : (ggAutomizer L Bs).map (ggLin (p := 3) ι) =
      (MulAction.stabilizer (E6QTwo.e6Weyl hα) vx).map (E6QTwo.e6Weyl hα).subtype)
    (hmem_e6 : ∀ ψ ∈ ggAutomizer L Bs ⊔ ggAutomizer M Bs,
      ggLin (p := 3) ι ψ ∈ E6QTwo.e6Weyl hα) :
    ∀ ψ ∈ ggAutomizer L Bs ⊔ ggAutomizer M Bs,
      ψ ⟨x, hxB⟩ = ⟨x, hxB⟩ → ψ ∈ ggAutomizer L Bs := by
  intro ψ hψA hfix
  have hstab : (⟨ggLin (p := 3) ι ψ, hmem_e6 ψ hψA⟩ : ↥(E6QTwo.e6Weyl hα)) ∈
      MulAction.stabilizer (E6QTwo.e6Weyl hα) vx := by
    rw [MulAction.mem_stabilizer_iff, Subgroup.smul_def, LinearEquiv.smul_def,
      hvxdef, ggLin_apply_ofMul, hfix]
  have hmem2 : ggLin (p := 3) ι ψ ∈
      (MulAction.stabilizer (E6QTwo.e6Weyl hα) vx).map (E6QTwo.e6Weyl hα).subtype :=
    Subgroup.mem_map_of_mem _ hstab
  rw [← himg_eq] at hmem2
  obtain ⟨ψ', hψ', hψ'eq⟩ := Subgroup.mem_map.mp hmem2
  exact (ggLin_injective ι hψ'eq) ▸ hψ'

omit [Finite G] in
private theorem exists_weyl_preimage {Bs L M : Subgroup G} {x : G} (hxB : x ∈ Bs)
    (hfix_mem_AL : ∀ ψ ∈ ggAutomizer L Bs ⊔ ggAutomizer M Bs,
      ψ ⟨x, hxB⟩ = ⟨x, hxB⟩ → ψ ∈ ggAutomizer L Bs) :
    ∃ W : Subgroup G, W ≤ Subgroup.normalizer (Bs : Set G) ∧
      (∀ ψ ∈ ggAutomizer L Bs ⊔ ggAutomizer M Bs,
        ∃ g ∈ W, ∀ b : ↥Bs, ((ψ b : ↥Bs) : G) = g * b * g⁻¹) ∧
      W ⊓ Subgroup.centralizer ({x} : Set G) ≤
        (L ⊓ Subgroup.normalizer (Bs : Set G)) ⊔ Subgroup.centralizer (Bs : Set G) := by
  refine ⟨ggConjPreimage Bs (ggAutomizer L Bs ⊔ ggAutomizer M Bs),
    ggConjPreimage_le_normalizer Bs _, ?_, ?_⟩
  · intro ψ hψ
    have hψtop : ψ ∈ ggInduced ⊤ Bs :=
      mem_ggInduced_top_of_mem_ggAutomizer
        (sup_le (ggAutomizer_mono Bs le_top) (ggAutomizer_mono Bs le_top) hψ)
    obtain ⟨g, -, hgN, hg⟩ := hψtop
    refine ⟨g, ?_, hg⟩
    rw [mem_ggConjPreimage_iff ⟨g, hgN⟩]
    have hEq : Bs.normalizerMonoidHom ⟨g, hgN⟩ = ψ := by
      ext b
      exact (hg b).symm
    rw [hEq]
    exact hψ
  · intro w hw
    obtain ⟨hwW, hwC⟩ := Subgroup.mem_inf.mp hw
    have hwN : w ∈ Subgroup.normalizer (Bs : Set G) :=
      ggConjPreimage_le_normalizer Bs _ hwW
    have hψA : Bs.normalizerMonoidHom ⟨w, hwN⟩ ∈
        ggAutomizer L Bs ⊔ ggAutomizer M Bs :=
      (mem_ggConjPreimage_iff ⟨w, hwN⟩).mp hwW
    have hfix : Bs.normalizerMonoidHom ⟨w, hwN⟩ ⟨x, hxB⟩ = ⟨x, hxB⟩ := by
      apply Subtype.ext
      show w * x * w⁻¹ = x
      rw [Subgroup.mem_centralizer_singleton_iff.mp hwC]
      group
    have hψAL : Bs.normalizerMonoidHom ⟨w, hwN⟩ ∈ ggAutomizer L Bs :=
      hfix_mem_AL _ hψA hfix
    obtain ⟨l, hlL, hlN, hlψ⟩ := mem_ggAutomizer_iff.mp hψAL
    have hCb : l⁻¹ * w ∈ Subgroup.centralizer (Bs : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      have h1 : w * b * w⁻¹ =
          ((Bs.normalizerMonoidHom ⟨w, hwN⟩ ⟨b, hb⟩ : ↥Bs) : G) := rfl
      have hcomm' : (l⁻¹ * w) * b = b * (l⁻¹ * w) := by
        calc (l⁻¹ * w) * b = l⁻¹ * (w * b * w⁻¹) * w := by group
          _ = l⁻¹ * (l * b * l⁻¹) * w := by rw [h1, hlψ ⟨b, hb⟩]
          _ = b * (l⁻¹ * w) := by group
      exact hcomm'.symm
    have h1 : l ∈ (L ⊓ Subgroup.normalizer (Bs : Set G)) ⊔
        Subgroup.centralizer (Bs : Set G) :=
      Subgroup.mem_sup_left (Subgroup.mem_inf.mpr ⟨hlL, hlN⟩)
    have h2 : l⁻¹ * w ∈ (L ⊓ Subgroup.normalizer (Bs : Set G)) ⊔
        Subgroup.centralizer (Bs : Set G) :=
      Subgroup.mem_sup_right hCb
    have h3 : l * (l⁻¹ * w) ∈ (L ⊓ Subgroup.normalizer (Bs : Set G)) ⊔
        Subgroup.centralizer (Bs : Set G) := Subgroup.mul_mem _ h1 h2
    rwa [mul_inv_cancel_left] at h3

private theorem exists_reflecting_element {K : Type} [Field K] [Finite K]
    [Fact (Nat.Prime 3)] (hK4 : Nat.card K = 4) {Bs L M : Subgroup G} {x : G}
    (φ : L ≃* LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))
    (hmapφ : ((Bs ⊓ L).subgroupOf L).map φ.toMonoidHom = USixTwo.torU K)
    (hBs : IsElemAbelian 3 Bs) (hcard : Nat.card Bs = 3 ^ 5) (hxB : x ∈ Bs)
    (hxL : x ∉ L) (hLx : L ≤ Subgroup.centralizer {x})
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [Finite V]
    (ι : Additive ↥Bs ≃+ V) {W : Subgroup G}
    (hex : ∀ ψ ∈ ggAutomizer L Bs ⊔ ggAutomizer M Bs,
      ∃ g ∈ W, ∀ b : ↥Bs, ((ψ b : ↥Bs) : G) = g * b * g⁻¹)
    {h : Fin 6 → V} {α : Fin 6 → Module.Dual (ZMod 3) V} {β : LinearMap.BilinForm (ZMod 3) V}
    (hP : ∀ i j, α i (h j) = (CartanMatrix.E 6 i j : ZMod 3))
    (hβ : ∀ i v, β (h i) v = α i v) (hα : ∀ i, α i (h i) = 2)
    (hmapA : (ggAutomizer L Bs ⊔ ggAutomizer M Bs).map (ggLin (p := 3) ι) =
      E6QTwo.e6Weyl hα)
    (hmem_e6 : ∀ ψ ∈ ggAutomizer L Bs ⊔ ggAutomizer M Bs,
      ggLin (p := 3) ι ψ ∈ E6QTwo.e6Weyl hα)
    (hVcard : Nat.card V = 3 ^ 5) {vx : V}
    (hvxdef : vx = ι (Additive.ofMul (⟨x, hxB⟩ : ↥Bs))) (hBxx : β vx vx = 2)
    (hfixv : ∀ ψ ∈ ggAutomizer L Bs, ggLin (p := 3) ι ψ vx = vx) :
    ∃ g ∈ W, (∀ z ∈ Bs ⊓ L, g * z * g⁻¹ = z) ∧ g * x * g⁻¹ = x⁻¹ := by
  obtain ⟨r, hre6, hr⟩ := E6QTwo.exists_mem_e6Weyl_reflection hP hVcard hβ hα hBxx
  obtain ⟨ψg, hψgA, hψgr⟩ := Subgroup.mem_map.mp (by rw [hmapA]; exact hre6)
  obtain ⟨g, hgW, hgψ⟩ := hex ψg hψgA
  have hrneg : r vx = -vx := by rw [hr, hBxx, hvxdef]; module
  have hgx : g * x * g⁻¹ = x⁻¹ := by
    have h1 : ι (Additive.ofMul (ψg ⟨x, hxB⟩)) = -vx := by
      rw [← ggLin_apply_ofMul (p := 3) ι ψg ⟨x, hxB⟩, hψgr, ← hvxdef]
      exact hrneg
    have h2 : ψg ⟨x, hxB⟩ = (⟨x, hxB⟩ : ↥Bs)⁻¹ := by
      have h3 : Additive.ofMul (ψg ⟨x, hxB⟩) = -Additive.ofMul (⟨x, hxB⟩ : ↥Bs) := by
        apply ι.injective
        rw [h1, map_neg, ← hvxdef]
      calc ψg ⟨x, hxB⟩ = Additive.toMul (Additive.ofMul (ψg ⟨x, hxB⟩)) :=
            (toMul_ofMul _).symm
        _ = Additive.toMul (-Additive.ofMul (⟨x, hxB⟩ : ↥Bs)) := by rw [h3]
        _ = (⟨x, hxB⟩ : ↥Bs)⁻¹ := by rw [← ofMul_inv, toMul_ofMul]
    rw [← hgψ ⟨x, hxB⟩]
    exact congrArg Subtype.val h2
  have hgz : ∀ z ∈ Bs ⊓ L, g * z * g⁻¹ = z := by
    intro z hz
    obtain ⟨hzBs, hzL⟩ := Subgroup.mem_inf.mp hz
    let f : ↥Bs →* Multiplicative (ZMod 3) :=
      { toFun := fun b => Multiplicative.ofAdd (β vx (ι (Additive.ofMul b)))
        map_one' := by simp [ofMul_one, map_zero]
        map_mul' := fun a b => by simp [ofMul_mul, map_add] }
    have hf : ∀ ψ' ∈ ggAutomizer L Bs, ∀ b, f (ψ' b) = f b := by
      intro ψ' hψ' b
      have hiso := E6QTwo.bilinForm_apply_e6Weyl hP hVcard hβ hα
        (hmem_e6 ψ' ((le_sup_left : ggAutomizer L Bs ≤
          ggAutomizer L Bs ⊔ ggAutomizer M Bs) hψ')) vx (ι (Additive.ofMul b))
      rw [hfixv ψ' hψ', ggLin_apply_ofMul] at hiso
      exact congrArg Multiplicative.ofAdd hiso
    have hfz : f ⟨z, hzBs⟩ = 1 :=
      E6QTwo.apply_eq_one_of_forall_ggAutomizer hK4 φ hmapφ hBs hcard hxB hxL hLx f hf hzL
    have hzero : β vx (ι (Additive.ofMul (⟨z, hzBs⟩ : ↥Bs))) = 0 := by
      simpa [f] using hfz
    have hrz : r (ι (Additive.ofMul (⟨z, hzBs⟩ : ↥Bs))) =
        ι (Additive.ofMul (⟨z, hzBs⟩ : ↥Bs)) := by
      rw [hr, hzero, zero_smul, sub_zero]
    have hψz : ψg ⟨z, hzBs⟩ = ⟨z, hzBs⟩ := by
      have h1 : ι (Additive.ofMul (ψg ⟨z, hzBs⟩)) =
          ι (Additive.ofMul (⟨z, hzBs⟩ : ↥Bs)) := by
        rw [← ggLin_apply_ofMul (p := 3) ι ψg ⟨z, hzBs⟩, hψgr, hrz]
      exact Additive.ofMul.injective (ι.injective h1)
    rw [← hgψ ⟨z, hzBs⟩, hψz]
  exact ⟨g, hgW, hgz, hgx⟩

private theorem exists_threeA_conj {K : Type} [Field K] [Finite K] [Fact (Nat.Prime 3)]
    (hK4 : Nat.card K = 4) {ω : K} (hω : ω ^ 2 + ω + 1 = 0) {Bs L M : Subgroup G} {x : G}
    (φ : L ≃* LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))
    (hmapφ : ((Bs ⊓ L).subgroupOf L).map φ.toMonoidHom = USixTwo.torU K)
    (hBs : IsElemAbelian 3 Bs) (hcard : Nat.card Bs = 3 ^ 5) (hxB : x ∈ Bs)
    (hxL : x ∉ L) (hLx : L ≤ Subgroup.centralizer {x})
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [Finite V]
    (ι : Additive ↥Bs ≃+ V) {W : Subgroup G}
    (hex : ∀ ψ ∈ ggAutomizer L Bs ⊔ ggAutomizer M Bs,
      ∃ g ∈ W, ∀ b : ↥Bs, ((ψ b : ↥Bs) : G) = g * b * g⁻¹)
    {h : Fin 6 → V} {α : Fin 6 → Module.Dual (ZMod 3) V} {β : LinearMap.BilinForm (ZMod 3) V}
    (hP : ∀ i j, α i (h j) = (CartanMatrix.E 6 i j : ZMod 3))
    (hβ : ∀ i v, β (h i) v = α i v) (hα : ∀ i, α i (h i) = 2)
    (hmapA : (ggAutomizer L Bs ⊔ ggAutomizer M Bs).map (ggLin (p := 3) ι) =
      E6QTwo.e6Weyl hα)
    (hmem_e6 : ∀ ψ ∈ ggAutomizer L Bs ⊔ ggAutomizer M Bs,
      ggLin (p := 3) ι ψ ∈ E6QTwo.e6Weyl hα)
    (hVcard : Nat.card V = 3 ^ 5) {vx : V}
    (hvxdef : vx = ι (Additive.ofMul (⟨x, hxB⟩ : ↥Bs))) (hvx : vx ≠ 0)
    (hBxx : β vx vx = 2) :
    ∃ (n : G) (hnL : n * x * n⁻¹ ∈ L), n ∈ W ∧
      φ ⟨n * x * n⁻¹, hnL⟩ = USixTwo.threeA hω := by
  obtain ⟨a, haL, hφa, ha1, ψa, hψaAL, -, hψaa, hψamod⟩ :=
    E6QTwo.exists_reflection_threeA hK4 hω φ hmapφ hBs hcard hxB hxL hLx
  let va : V := ι (Additive.ofMul a)
  have hvadef : va = ι (Additive.ofMul a) := rfl
  have hva : va ≠ 0 := by
    intro h0
    rw [hvadef] at h0
    have h1 : Additive.ofMul a = 0 := ι.injective (by rw [h0, map_zero])
    have h2 : a = 1 := by simpa using congrArg Additive.toMul h1
    exact ha1 h2
  have hψae6 : ggLin (p := 3) ι ψa ∈ E6QTwo.e6Weyl hα :=
    hmem_e6 ψa ((le_sup_left : ggAutomizer L Bs ≤
      ggAutomizer L Bs ⊔ ggAutomizer M Bs) hψaAL)
  have hgv : ggLin (p := 3) ι ψa va = -va := by
    rw [hvadef, ggLin_apply_ofMul, hψaa, ofMul_inv, map_neg]
  have hgu : ∀ u, ∃ c : ZMod 3, ggLin (p := 3) ι ψa u - u = c • va := by
    intro u
    have h := exists_smul_ggLin_sub_eq_of_forall_mem_zpowers (p := 3) ι
      (fun x y => hBs.1.is_comm.comm x y) hψamod u
    rwa [hvadef]
  have hBaa : β va va = 2 :=
    E6QTwo.bilinForm_self_eq_two_of_neg hP hVcard hβ hα hψae6 hva hgv hgu
  obtain ⟨s, hse6, hsvx⟩ := E6QTwo.exists_mem_e6Weyl_apply_eq hP hVcard hβ hα hvx hva
    (by rw [hBxx, hBaa])
  obtain ⟨ψs, hψsA, hψsr⟩ := Subgroup.mem_map.mp (by rw [hmapA]; exact hse6)
  obtain ⟨n, hnW, hnψ⟩ := hex ψs hψsA
  have hnx : n * x * n⁻¹ = a := by
    have h1 : ι (Additive.ofMul (ψs ⟨x, hxB⟩)) = va := by
      rw [← ggLin_apply_ofMul (p := 3) ι ψs ⟨x, hxB⟩, hψsr, ← hvxdef]
      exact hsvx
    have h2 : ψs ⟨x, hxB⟩ = a := by
      apply Additive.ofMul.injective
      exact ι.injective (by rw [h1, hvadef])
    rw [← hnψ ⟨x, hxB⟩]
    exact congrArg Subtype.val h2
  refine ⟨n, hnx ▸ haL, hnW, ?_⟩
  rw [show (⟨n * x * n⁻¹, hnx ▸ haL⟩ : L) = ⟨a, haL⟩ from Subtype.ext hnx, hφa]

theorem E6QTwo.exists_localSetting_and_package
    (hG : IsCharTwoType G)
    {K : Type} [Field K] [Finite K] (hK4 : Nat.card K = 4) {Bs L M : Subgroup G} {x : G}
    (θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))
    (hperf : commutator ↥L = ⊤) (hBs : IsElemAbelian 3 Bs) (hNT : GGNoTransvection 3 Bs)
    (hcard : Nat.card Bs = 3 ^ 5) (hxB : x ∈ Bs) (hx1 : x ≠ 1)
    (hLx : L ≤ Subgroup.centralizer {x})
    (hN : (L.subgroupOf (Subgroup.centralizer {x})).Normal)
    (hcyc : ∀ S : Subgroup G, IsPGroup 3 S → S ≤ Subgroup.centralizer (L : Set G) → IsCyclic S)
    (hstar : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs)
    (hBsN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hI : ∀ b ∈ Bs, ∃ ψ ∈ LargeEvenMatConjImage
        (LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ 1))) (LargeEvenGUSet (Fin 6) K (2 ^ 1)),
      LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) ψ)
    (hW : GGWeylOfType 3 CoxeterMatrix.E₆ (ggAutomizer L Bs ⊔ ggAutomizer M Bs)) :
    ∃ (ω : K) (hω : ω ^ 2 + ω + 1 = 0)
      (φ : L ≃* LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1))),
      USixTwo.LocalSetting hω x L φ Bs ∧
      ∃ W : Subgroup G, W ≤ Subgroup.normalizer (Bs : Set G) ∧
        W ⊓ Subgroup.centralizer {x} ≤
          (L ⊓ Subgroup.normalizer (Bs : Set G)) ⊔ Subgroup.centralizer (Bs : Set G) ∧
        (∃ n ∈ W, ∃ hnL : n * x * n⁻¹ ∈ L, φ ⟨n * x * n⁻¹, hnL⟩ = USixTwo.threeA hω) ∧
        ∃ g ∈ W, (∀ z ∈ Bs ⊓ L, g * z * g⁻¹ = z) ∧ g * x * g⁻¹ = x⁻¹ := by
  classical
  obtain ⟨ω, hω⟩ := USixTwo.exists_root_omega (K := K) hK4
  have horderx : orderOf x = 3 := orderOf_eq_prime (hBs.2 x hxB) hx1
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hxL, φ, hmapφ⟩ :=
    exists_not_mem_and_map_eq_torU hG hK4 hω θ hperf hBs hNT hcard hxB hx1 hLx hN hcyc
      hstar hBsN hI hW
  obtain ⟨V, hVadd, hVmod, ⟨ι⟩⟩ := exists_ggLinData (p := 3) hBs
  letI := hVadd
  letI := hVmod
  have hVcard : Nat.card V = 3 ^ 5 := by
    rw [← card_eq_of_ggLin ι]
    exact hcard
  haveI : Finite V := Nat.finite_of_card_ne_zero (by rw [hVcard]; norm_num)
  obtain ⟨h, α, hα, β, hP, hβ, hWcard, hmapA, hmem_e6⟩ :=
    exists_e6_model hNT hW ι hVcard
  obtain ⟨vx, hvxdef, hvx, hfixv, hBxx, himg_eq⟩ :=
    exists_vx_and_stabilizer hK4 φ hmapφ hBs hcard hxB hx1 hxL hLx ι hVcard hP hβ hα
      hWcard hmem_e6
  have hfix_mem_AL := mem_ggAutomizer_of_fix hxB ι hα hvxdef himg_eq hmem_e6
  obtain ⟨W, hWN, hex, hWthird⟩ := exists_weyl_preimage hxB hfix_mem_AL
  obtain ⟨g, hgW, hgz, hgx⟩ :=
    exists_reflecting_element hK4 φ hmapφ hBs hcard hxB hxL hLx ι hex hP hβ hα hmapA
      hmem_e6 hVcard hvxdef hBxx hfixv
  obtain ⟨n, hnL, hnW, hnφa⟩ :=
    exists_threeA_conj hK4 hω φ hmapφ hBs hcard hxB hxL hLx ι hex hP hβ hα hmapA
      hmem_e6 hVcard hvxdef hvx hBxx
  refine ⟨ω, hω, φ, ⟨hK4, horderx, hLx, hN, hcyc, hBs, hxB, hcard, hmapφ,
    ⟨n, hWN hnW, hnL, hnφa⟩⟩, W, hWN, hWthird,
    ⟨n, hnW, hnL, hnφa⟩, ⟨g, hgW, hgz, hgx⟩⟩

end CFSG.StandardType

end
