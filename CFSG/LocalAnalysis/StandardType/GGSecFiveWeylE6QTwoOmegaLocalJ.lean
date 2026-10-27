module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoOmegaLocalLin
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoOmegaLocalAutAux7
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoOmegaLocalJAux
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoOmegaLocalJAux2
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoOmegaLocalJAux3
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoOmegaLocalJAux5

public section

namespace CFSG.StandardType.E6QTwo

open CFSG.Assembly CFSG.Open

variable {G : Type} [Group G] [Finite G]
variable {K : Type} [Field K] [Finite K]

theorem finrank_fixedSpace_omPlusLin_of_component (hK : Nat.card K = 2) {Bs L : Subgroup G}
    {x : G} (θ : L ⧸ Subgroup.center L ≃* OrthRest.RPlus K 4) (hperf : commutator ↥L = ⊤)
    (hZ2 : IsPGroup 2 (Subgroup.center L)) (hBs : IsElemAbelian 3 Bs)
    (hcard : Nat.card Bs = 3 ^ 5) (hcardE : Nat.card ↥(Bs ⊓ L) = 3 ^ 4) (hx1 : x ≠ 1)
    (hLx : L ≤ Subgroup.centralizer {x})
    (hBL : Bs ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers x)
    (hstar : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs)
    (hBsN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hI : ∀ b ∈ Bs, ∃ φ ∈ LargeEvenInnSet (OrthRest.RPlus K 4),
      LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ)
    {D J : Subgroup G} (hDB : D ≤ Bs) (hDcard : Nat.card D = 3 ^ 2) (hxD : x ∈ D)
    (hJ : CFSG.Assembly.IsComponentOf J (L ⊓ Subgroup.centralizer (D : Set G)))
    {e : G} (heD : e ∈ D) (heL : e ∈ L) (he1 : e ≠ 1) :
    Module.finrank K
        (CFSG.RankThree.PartOne.KCOrthogonal.fixedSpace (omPlusLin hK θ ⟨e, heL⟩)) = 0 ∨
      Module.finrank K
        (CFSG.RankThree.PartOne.KCOrthogonal.fixedSpace (omPlusLin hK θ ⟨e, heL⟩)) = 6 := by
  haveI : CharP K 2 :=
    CFSG.TauCetiBridge.charP_two_of_card_eq_two_pow (f := 1) (by rw [hK]; rfl)
  have hJ' := isComponentOf_map_projOrth hK hZ2 hBs hcard hcardE hx1 hLx hBL hDB hDcard hxD
    hJ heD heL he1 θ
  have hx3 := orderOf_rPlusEquiv_qMap_of_mem_Bs (x := x) hK hZ2 hBs hDB heD heL he1 θ
  have hx'eq : (OrthTorus.rPlusEquiv K (by norm_num : 1 ≤ 4) (qMap (K := K) θ ⟨e, heL⟩) :
      (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) =
      omPlusLin hK θ ⟨e, heL⟩ := by
    ext v
    rfl
  have hcases := fixedSpace_omPlusLin_cases hK hx3 hJ'
  rcases hcases with ⟨h0, -⟩ | ⟨h6, -⟩
  · left
    rw [← hx'eq]
    exact h0
  · right
    rw [← hx'eq]
    exact h6

theorem mem_ggAutomizer_of_fix_omegaPlus (hK : Nat.card K = 2) {Bs L : Subgroup G} {x : G}
    (θ : L ⧸ Subgroup.center L ≃* OrthRest.RPlus K 4) (hperf : commutator ↥L = ⊤)
    (hZ2 : IsPGroup 2 (Subgroup.center L)) (hBs : IsElemAbelian 3 Bs)
    (hcard : Nat.card Bs = 3 ^ 5) (hcardE : Nat.card ↥(Bs ⊓ L) = 3 ^ 4) (hx1 : x ≠ 1)
    (hLx : L ≤ Subgroup.centralizer {x})
    (hBL : Bs ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers x)
    (hstar : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs)
    (hBsN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hI : ∀ b ∈ Bs, ∃ φ ∈ LargeEvenInnSet (OrthRest.RPlus K 4),
      LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ)
    {D J : Subgroup G} (hDB : D ≤ Bs) (hDcard : Nat.card D = 3 ^ 2) (hxD : x ∈ D)
    (hJ : CFSG.Assembly.IsComponentOf J (L ⊓ Subgroup.centralizer (D : Set G))) :
    ∀ ψ ∈ ggAutomizer L Bs, (∀ d : ↥Bs, (d : G) ∈ D → ψ d = d) → ψ ∈ ggAutomizer J Bs := by
  classical
  haveI : CharP K 2 :=
    CFSG.TauCetiBridge.charP_two_of_card_eq_two_pow (f := 1) (by rw [hK]; rfl)
  intro ψ hψ hfix
  obtain ⟨e, heD, heL, he1, -⟩ :=
    exists_mem_inf_eq_sup_of_omegaPlus hZ2 hBs hcard hcardE hx1 hLx hBL hDB hDcard hxD
  obtain ⟨l, hlL, hlN, hl⟩ := mem_ggAutomizer_iff.mp hψ
  have heC : e ∈ Subgroup.centralizer (Bs : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact congrArg Subtype.val (hBs.1.is_comm.comm ⟨b, hb⟩ ⟨e, hDB heD⟩)
  have hle : l * e = e * l := by
    have h := hl ⟨e, hDB heD⟩
    rw [hfix ⟨e, hDB heD⟩ heD] at h
    exact mul_inv_eq_iff_eq_mul.mp h.symm
  have hc : Commute (⟨l, hlL⟩ : ↥L) ⟨e, heL⟩ := Subtype.ext hle
  have hn := (hc.map (qMap (K := K) θ)).map (OrthTorus.rPlusEquiv K (by norm_num : 1 ≤ 4))
  have hx3 := orderOf_rPlusEquiv_qMap_of_mem_Bs (x := x) hK hZ2 hBs hDB heD heL he1 θ
  have hJ' := isComponentOf_map_projOrth hK hZ2 hBs hcard hcardE hx1 hLx hBL hDB hDcard hxD
    hJ heD heL he1 θ
  have hQ := TableBOrth.nondegenerate_qPlusForm (K := K) 4
  obtain ⟨j, hj⟩ : ∃ j : ℕ, CFSG.RankThree.PartOne.piOrth (TableBOrth.qPlusForm K 4)
      (OrthTorus.rPlusEquiv K (by norm_num : 1 ≤ 4) (qMap (K := K) θ ⟨l, hlL⟩) *
        (OrthTorus.rPlusEquiv K (by norm_num : 1 ≤ 4) (qMap (K := K) θ ⟨e, heL⟩) ^ j)⁻¹) ∈
      (((J.subgroupOf L).map (qMap (K := K) θ)).map
        (OrthTorus.rPlusEquiv K (by norm_num : 1 ≤ 4)).toMonoidHom).map
          (CFSG.RankThree.PartOne.piOrth (TableBOrth.qPlusForm K 4)) := by
    rcases fixedSpace_omPlusLin_cases hK hx3 hJ' with ⟨h0, hL', -⟩ | ⟨h6, hL'⟩
    · obtain ⟨j, hj⟩ := exists_pow_mem_specialBlock_of_fixedSpace_eq_zero hK hx3 hn h0
      refine ⟨j, ?_⟩
      rw [hL']
      exact Subgroup.mem_map_of_mem _ hj
    · obtain ⟨j, hj⟩ := exists_pow_mem_supportedFixedDerived_of_fixedSpace_eq_six hK hx3 hn h6
      refine ⟨j, ?_⟩
      rw [hL']
      exact Subgroup.mem_map_of_mem _ hj
  obtain ⟨w, hw, hwj⟩ := Subgroup.mem_map.mp hj
  obtain ⟨u, hu, hwu⟩ := Subgroup.mem_map.mp hw
  obtain ⟨j₀, hj₀, hj₀u⟩ := Subgroup.mem_map.mp hu
  have hq : qMap (K := K) θ j₀ = qMap (K := K) θ (⟨l, hlL⟩ * (⟨e, heL⟩ ^ j)⁻¹) := by
    apply (OrthTorus.rPlusEquiv K (by norm_num : 1 ≤ 4)).injective
    apply CFSG.RankThree.PartOne.piOrth_injective hQ
    rw [hj₀u]
    simp only [MulEquiv.coe_toMonoidHom] at hwu
    rw [hwu, hwj]
    simp only [map_mul, map_inv, map_pow]
  have hz : j₀⁻¹ * (⟨l, hlL⟩ * (⟨e, heL⟩ ^ j)⁻¹) ∈ Subgroup.center L := by
    rw [← qMap_ker (K := K) θ, MonoidHom.mem_ker, map_mul, map_inv, hq, inv_mul_cancel]
  have hzC : ((j₀⁻¹ * (⟨l, hlL⟩ * (⟨e, heL⟩ ^ j)⁻¹) : ↥L) : G) ∈
      Subgroup.centralizer (Bs : Set G) :=
    center_le_centralizer_Bs_of_innerAction θ hperf hBsN hI (Subgroup.mem_map.mpr ⟨_, hz, rfl⟩)
  have hcC : (e ^ j)⁻¹ * ((j₀⁻¹ * (⟨l, hlL⟩ * (⟨e, heL⟩ ^ j)⁻¹) : ↥L) : G)⁻¹ ∈
      Subgroup.centralizer (Bs : Set G) :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.pow_mem _ heC j)) (Subgroup.inv_mem _ hzC)
  have hj₀eq : (j₀ : G) =
      l * ((e ^ j)⁻¹ * ((j₀⁻¹ * (⟨l, hlL⟩ * (⟨e, heL⟩ ^ j)⁻¹) : ↥L) : G)⁻¹) := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_pow, Subgroup.coe_mk]
    group
  generalize (e ^ j)⁻¹ * ((j₀⁻¹ * (⟨l, hlL⟩ * (⟨e, heL⟩ ^ j)⁻¹) : ↥L) : G)⁻¹ = c at hcC hj₀eq
  refine mem_ggAutomizer_iff.mpr ⟨j₀, Subgroup.mem_subgroupOf.mp hj₀, ?_, fun b => ?_⟩
  · rw [hj₀eq]
    exact Subgroup.mul_mem _ hlN (Subgroup.centralizer_le_normalizer _ hcC)
  · have hcb : (b : G) * c = c * b := Subgroup.mem_centralizer_iff.mp hcC b b.2
    rw [hl b, hj₀eq]
    calc l * (b : G) * l⁻¹ = l * (c * b * c⁻¹) * l⁻¹ := by
          rw [← hcb, mul_inv_cancel_right]
      _ = l * c * b * (l * c)⁻¹ := by group

end CFSG.StandardType.E6QTwo

end
