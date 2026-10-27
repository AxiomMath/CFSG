module

public import CFSG.LocalAnalysis.StandardType.GGUSixTwoTorus
public import CFSG.LocalAnalysis.StandardType.GGOneFiveDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveRest
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoAutLQ
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoPairing
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoTransfer
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoModel
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoCartan

public section

namespace CFSG.StandardType.E6QTwo

open CFSG.Assembly Module

variable {G : Type} [Group G] [Finite G] {K : Type} [Field K] [Finite K]

private theorem exists_smul_ggLin_sub_eq_of_mem_zpowers {p : ℕ} [Fact p.Prime] {E : Type}
    [Group E] {V : Type} [AddCommGroup V] [Module (ZMod p) V] (ι : Additive E ≃+ V)
    (hcomm : ∀ x y : E, x * y = y * x) {ψ : MulAut E} {a : E}
    (hmod : ∀ b : E, b⁻¹ * ψ b ∈ Subgroup.zpowers a) (u : V) :
    ∃ c : ZMod p, ggLin (p := p) ι ψ u - u = c • ι (Additive.ofMul a) := by
  obtain ⟨b, rfl⟩ : ∃ b : Additive E, ι b = u := ι.surjective u
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hmod (Additive.toMul b))
  refine ⟨(k : ZMod p), ?_⟩
  have hψeq : ψ (Additive.toMul b) * (Additive.toMul b)⁻¹ = a ^ k := by
    have h2 : ψ (Additive.toMul b) = Additive.toMul b * a ^ k := by rw [hk]; group
    rw [h2]
    rw [← (show Commute a (Additive.toMul b) from hcomm a (Additive.toMul b)).zpow_left k]
    group
  have hsub : ggLin (p := p) ι ψ (ι b) - ι b =
      ι (Additive.ofMul (a ^ k)) := by
    rw [show b = Additive.ofMul (Additive.toMul b) from (ofMul_toMul b).symm,
      ggLin_apply_ofMul, ← map_sub]
    congr 1
    simp only [sub_eq_add_neg, ← ofMul_inv, ← ofMul_mul, hψeq]
  rw [hsub, ofMul_zpow, map_zsmul, Int.cast_smul_eq_zsmul (ZMod p)]

private theorem exists_e6LinearModel {Bs : Subgroup G}
    (hBs : IsElemAbelian 3 Bs) (hcard : Nat.card Bs = 3 ^ 5)
    (hNT : GGNoTransvection 3 Bs) {A : Subgroup (MulAut ↥Bs)}
    (hW : GGWeylOfType 3 CoxeterMatrix.E₆ A)
    (hA : ∀ φ ∈ A, φ ∈ ggInduced ⊤ Bs) (hWcard : Nat.card CoxeterMatrix.E₆.Group = 51840) :
    ∃ (V : Type) (_ : AddCommGroup V) (_ : Module (ZMod 3) V) (ι : Additive ↥Bs ≃+ V)
      (h : Fin 6 → V) (α : Fin 6 → Dual (ZMod 3) V) (hα : ∀ i, α i (h i) = 2)
      (β : LinearMap.BilinForm (ZMod 3) V),
      Nat.card V = 3 ^ 5 ∧ A.map (ggLin (p := 3) ι) = e6Weyl hα ∧
        Nat.card (e6Weyl hα) = 51840 ∧
        (∀ i j, α i (h j) = (CartanMatrix.E 6 i j : ZMod 3)) ∧
        (∀ i v, β (h i) v = α i v) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨V, hVadd, hVmod, ⟨ι⟩⟩ := CFSG.StandardType.exists_ggLinData (p := 3) hBs
  letI := hVadd
  letI := hVmod
  have hVcard : Nat.card V = 3 ^ 5 := by
    rw [← CFSG.StandardType.card_eq_of_ggLin ι]
    exact hcard
  haveI : Finite V := Nat.finite_of_card_ne_zero (by rw [hVcard]; norm_num)
  obtain ⟨e, h, α, hα, he, hP⟩ := exists_cartan_pairing_E6 hNT hW hA ι
  obtain ⟨β, hβ⟩ := exists_bilinForm hP hVcard
  have hmapA : A.map (ggLin (p := 3) ι) = e6Weyl hα :=
    map_ggLin_eq_e6Weyl ι e hα he
  have hWcard' : Nat.card (e6Weyl hα) = 51840 := by
    rw [card_e6Weyl_eq ι e hα he,
      show Nat.card A = Nat.card (CoxeterMatrix.E₆).Group from (Nat.card_congr e.toEquiv).symm,
      hWcard]
  exact ⟨V, hVadd, hVmod, ι, h, α, hα, β, hVcard, hmapA, hWcard', hP, hβ⟩

theorem exists_mem_sup_apply_eq_threeA (hK : Nat.card K = 4) {ω : K} (hω : ω ^ 2 + ω + 1 = 0)
    {Bs L K' : Subgroup G} {x : G}
    (θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))
    (hZ2 : IsPGroup 2 (Subgroup.center L))
    (hmap : ((Bs ⊓ L).subgroupOf L).map
      (θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center L))) = USixTwo.torU K)
    (hBs : IsElemAbelian 3 Bs) (hNT : GGNoTransvection 3 Bs) (hcard : Nat.card Bs = 3 ^ 5)
    (hx : x ∈ Bs) (hxL : x ∉ L) (hLx : L ≤ Subgroup.centralizer {x})
    (hW : GGWeylOfType 3 CoxeterMatrix.E₆ (ggAutomizer L Bs ⊔ ggAutomizer K' Bs))
    (hWcard : Nat.card CoxeterMatrix.E₆.Group = 51840) :
    ∃ ψ ∈ ggAutomizer L Bs ⊔ ggAutomizer K' Bs, ∃ h : ((ψ ⟨x, hx⟩ : ↥Bs) : G) ∈ L,
      θ (QuotientGroup.mk (⟨(ψ ⟨x, hx⟩ : ↥Bs), h⟩ : L)) = USixTwo.threeA hω := by
  classical
  have hx1 : x ≠ 1 := fun h1 => hxL (h1 ▸ L.one_mem)
  let A₀ : Subgroup (MulAut ↥Bs) := ggAutomizer L Bs ⊔ ggAutomizer K' Bs
  have hWeylA : GGWeylOfType 3 CoxeterMatrix.E₆ A₀ := hW
  have hA : ∀ φ ∈ A₀, φ ∈ ggInduced ⊤ Bs := by
    intro φ hφ
    exact mem_ggInduced_top_of_mem_ggAutomizer
      (sup_le (ggAutomizer_mono Bs le_top) (ggAutomizer_mono Bs le_top) hφ)
  obtain ⟨V, hVadd, hVmod, ι, h, α, hα, β, hVcard, hmapA, hWcard', hP, hB⟩ :=
    exists_e6LinearModel hBs hcard hNT hWeylA hA hWcard
  letI := hVadd
  letI := hVmod
  haveI : Finite V := Nat.finite_of_card_ne_zero (by rw [hVcard]; norm_num)
  haveI : Finite (V ≃ₗ[ZMod 3] V) :=
    Finite.of_injective ((↑) : (V ≃ₗ[ZMod 3] V) → V → V) DFunLike.coe_injective
  have hmem_e6 : ∀ φ ∈ A₀, ggLin (p := 3) ι φ ∈ e6Weyl hα := by
    intro φ hφ
    rw [← hmapA]
    exact Subgroup.mem_map_of_mem _ hφ
  let vx : V := ι (Additive.ofMul (⟨x, hx⟩ : ↥Bs))
  have hvxdef : vx = ι (Additive.ofMul (⟨x, hx⟩ : ↥Bs)) := rfl
  have hvx : vx ≠ 0 := by
    intro h0
    rw [hvxdef] at h0
    have h1 : Additive.ofMul (⟨x, hx⟩ : ↥Bs) = 0 := ι.injective (by rw [h0, map_zero])
    have h2 : (⟨x, hx⟩ : ↥Bs) = 1 := by simpa using congrArg Additive.toMul h1
    exact hx1 (by simpa using congrArg Subtype.val h2)
  have hfixAL : ∀ φ ∈ ggAutomizer L Bs, φ ⟨x, hx⟩ = ⟨x, hx⟩ := by
    intro φ hφ
    exact ggAutomizer_apply_eq_of_le_centralizer hLx hφ
  have hfixv : ∀ φ ∈ ggAutomizer L Bs, ggLin (p := 3) ι φ vx = vx := by
    intro φ hφ
    rw [hvxdef, ggLin_apply_ofMul, hfixAL φ hφ]
  have hmapALle : (ggAutomizer L Bs).map (ggLin (p := 3) ι) ≤
      (MulAction.stabilizer (e6Weyl hα) vx).map (e6Weyl hα).subtype := by
    rintro _ ⟨φ, hφ, rfl⟩
    have hstab : (⟨ggLin (p := 3) ι φ, hmem_e6 φ ((le_sup_left : ggAutomizer L Bs ≤ A₀) hφ)⟩ :
        ↥(e6Weyl hα)) ∈ MulAction.stabilizer (e6Weyl hα) vx := by
      rw [MulAction.mem_stabilizer_iff, Subgroup.smul_def, LinearEquiv.smul_def]
      exact hfixv φ hφ
    exact Subgroup.mem_map_of_mem (e6Weyl hα).subtype hstab
  have hALcard720 : 720 ≤ Nat.card (ggAutomizer L Bs) :=
    le_card_ggAutomizer_of_isPGroup hK θ hZ2 hmap hBs hcard hx hxL hLx
  have hStabge : Nat.card (ggAutomizer L Bs) ≤
      Nat.card (MulAction.stabilizer (e6Weyl hα) vx) := by
    have h' := Subgroup.card_le_of_le hmapALle
    rwa [Subgroup.card_map_of_injective (e6Weyl hα).subtype_injective,
      Subgroup.card_map_of_injective (ggLin_injective ι)] at h'
  have hcases := stabilizer_cases hP hVcard hB hα hWcard' hvx
  have hBxx : β vx vx = 2 := by
    rcases hcases with ⟨h1, -⟩ | ⟨-, h1⟩ | ⟨-, h1⟩
    · exact h1
    · omega
    · omega
  obtain ⟨a, haL, hθa, ha1, ψa, hψaAL, -, hψaa, hψamod⟩ :=
    exists_reflection_threeA_of_isPGroup hK hω θ hZ2 hmap hBs hcard hx hxL hLx
  let va : V := ι (Additive.ofMul a)
  have hvadef : va = ι (Additive.ofMul a) := rfl
  have hva : va ≠ 0 := by
    intro h0
    rw [hvadef] at h0
    have h1 : Additive.ofMul a = 0 := ι.injective (by rw [h0, map_zero])
    have h2 : a = 1 := by simpa using congrArg Additive.toMul h1
    exact ha1 h2
  have hψae6 : ggLin (p := 3) ι ψa ∈ e6Weyl hα :=
    hmem_e6 ψa ((le_sup_left : ggAutomizer L Bs ≤ A₀) hψaAL)
  have hgv : ggLin (p := 3) ι ψa va = -va := by
    rw [hvadef, ggLin_apply_ofMul, hψaa, ofMul_inv, map_neg]
  have hgu : ∀ u, ∃ c : ZMod 3, ggLin (p := 3) ι ψa u - u = c • va := by
    intro u
    have hm := exists_smul_ggLin_sub_eq_of_mem_zpowers (p := 3) ι
      (fun x y => hBs.1.is_comm.comm x y) hψamod u
    rwa [← hvadef] at hm
  have hBaa : β va va = 2 :=
    bilinForm_self_eq_two_of_neg hP hVcard hB hα hψae6 hva hgv hgu
  obtain ⟨s, hse6, hsvx⟩ := exists_mem_e6Weyl_apply_eq hP hVcard hB hα hvx hva
    (by rw [hBxx, hBaa])
  obtain ⟨ψs, hψsA, hψsr⟩ := Subgroup.mem_map.mp (by rw [hmapA]; exact hse6)
  have hψsx : ψs ⟨x, hx⟩ = a := by
    have h1 : ι (Additive.ofMul (ψs ⟨x, hx⟩)) = va := by
      rw [← ggLin_apply_ofMul (p := 3) ι ψs ⟨x, hx⟩, hψsr]
      exact hsvx
    have h2 : Additive.ofMul (ψs ⟨x, hx⟩) = Additive.ofMul a := by
      apply ι.injective
      rw [h1, hvadef]
    exact Additive.ofMul.injective h2
  have hval : ((ψs ⟨x, hx⟩ : ↥Bs) : G) = (a : G) :=
    congrArg (fun b : ↥Bs => (b : G)) hψsx
  refine ⟨ψs, hψsA, hval ▸ haL, ?_⟩
  have hL : (⟨ψs ⟨x, hx⟩, hval ▸ haL⟩ : L) = ⟨a, haL⟩ := by
    apply Subtype.ext
    exact hval
  rw [hL]
  exact hθa

end CFSG.StandardType.E6QTwo

end
