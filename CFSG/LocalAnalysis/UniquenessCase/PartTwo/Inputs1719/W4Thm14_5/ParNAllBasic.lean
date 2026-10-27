module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23d.Defs
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs2
public import CFSG.LocalAnalysis.UniquenessCase.UC22S20
public import CFSG.Quasithin.Background.D2Basic
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.ParNMinimal
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ParabolicTransfer
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsFiveKNshape
import CFSG.Quasithin.EmptyFaithful.T1515C4Mod

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22 Subgroup

theorem nonempty_bar2_hinf_subgroupOf {G : Type} [Group G] [Finite G] {H P : Subgroup G}
    (hPH : P ≤ H) :
    Nonempty (Bar2 (Hinf P) ≃* Bar2 (Hinf (P.subgroupOf H))) := by
  have hPeq : (P.subgroupOf H).map H.subtype = P := by
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hPH]
  have hinf : Hinf P = (Hinf (P.subgroupOf H)).map H.subtype := by
    rw [Hinf_map H.subtype, hPeq]
  exact nonempty_bar2_equiv_of_mulEquiv ((MulEquiv.subgroupCongr hinf).trans
    ((Hinf (P.subgroupOf H)).equivMapOfInjective H.subtype H.subtype_injective).symm)

theorem nonempty_bar2_hinf_map_mulEquiv {Γ Γ' : Type} [Group Γ] [Group Γ'] [Finite Γ]
    [Finite Γ'] (φ : Γ ≃* Γ') (Q : Subgroup Γ) :
    Nonempty (Bar2 (Hinf (Q.map φ.toMonoidHom)) ≃* Bar2 (Hinf Q)) := by
  have hinf : Hinf (Q.map φ.toMonoidHom) = (Hinf Q).map φ.toMonoidHom := (Hinf_map _ Q).symm
  exact nonempty_bar2_equiv_of_mulEquiv ((MulEquiv.subgroupCongr hinf).trans
    ((Hinf Q).equivMapOfInjective φ.toMonoidHom φ.injective).symm)

theorem nonempty_bar2_hinf_equiv_of_eq {G : Type} [Group G] [Finite G] {H P : Subgroup G}
    (hPH : P = H) (hperf : ⁅H, H⁆ = H) (hO2 : CFSG.pCore 2 ↥H = ⊥) :
    Nonempty (Bar2 (Hinf P) ≃* ↥H) := by
  have hinf : Hinf P = H := by
    rw [hPH]
    exact le_antisymm (uc22p21c_Hinf_le H) (uc22p21c_le_Hinf le_rfl hperf)
  obtain ⟨χ⟩ := nonempty_bar2_equiv_of_mulEquiv (MulEquiv.subgroupCongr hinf)
  exact ⟨χ.trans ((QuotientGroup.quotientMulEquivOfEq hO2).trans QuotientGroup.quotientBot)⟩

variable {W : Type} [CommGroup W] [Finite W]

omit [Finite W] in
theorem exists_model_parabolic {H S P : Subgroup (MulAut W)} {Γ : Type} [Group Γ] [Finite Γ]
    {U Q₀ : Subgroup Γ} (hS : IsSylowIn 2 S H)
    (hmodel : ∀ S' : Sylow 2 ↥H, ∃ φ : Γ ≃* ↥H, U.map φ.toMonoidHom = (S' : Subgroup ↥H) ∧
      KTabD.pointStab H S' = Q₀.map φ.toMonoidHom)
    (hBP : H ⊓ normalizer (S : Set (MulAut W)) ≤ P) (hPH : P ≤ H)
    (hPnot : ¬ P ≤ stabSub (fixV S)) :
    ∃ φ : Γ ≃* ↥H, U.map φ.toMonoidHom = (hS.toSylow : Subgroup ↥H) ∧
      KTabD.pointStab H hS.toSylow = Q₀.map φ.toMonoidHom ∧
      ∃ Q : Subgroup Γ, IsParabolicTwo Γ Q ∧ U ≤ Q ∧ ¬ Q ≤ Q₀ ∧
        P.subgroupOf H = Q.map φ.toMonoidHom := by
  obtain ⟨φ, hφU, hφP⟩ := hmodel hS.toSylow
  obtain ⟨hpar, hSP⟩ := isParabolicTwo_subgroupOf hS hBP
  have hnot := not_subgroupOf_le_pointStab hS hPH hPnot
  refine ⟨φ, hφU, hφP, (P.subgroupOf H).comap φ.toMonoidHom,
    IsParabolicTwo.comap φ.toMonoidHom φ.surjective hpar, ?_, ?_, ?_⟩
  · intro u hu
    exact hSP (hφU ▸ Subgroup.mem_map_of_mem φ.toMonoidHom hu)
  · intro hle
    apply hnot
    rw [hφP]
    intro y hy
    refine ⟨φ.symm y, hle (Subgroup.mem_comap.mpr ?_), by simp⟩
    simpa using hy
  · exact (Subgroup.map_comap_eq_self_of_surjective φ.surjective _).symm

theorem nParam_eq_of_least {H S P : Subgroup (MulAut W)} {n j : ℕ} (hS : IsSylowIn 2 S H)
    (hPH : P ≤ H) (hN : NParam (Hinf P) n) (hj : 2 ≤ j)
    (hpar : IsParabolicTwo ↥H (P.subgroupOf H))
    (hSQ : (hS.toSylow : Subgroup ↥H) ≤ P.subgroupOf H)
    (hnot : ¬ P.subgroupOf H ≤ KTabD.pointStab H hS.toSylow)
    (hleast : ∀ P' : Subgroup ↥H, IsParabolicTwo ↥H P' → (hS.toSylow : Subgroup ↥H) ≤ P' →
      ¬ P' ≤ KTabD.pointStab H hS.toSylow → P.subgroupOf H ≤ P')
    (hline : ∀ Pstar : Subgroup ↥H,
      Minimal (fun Pstar : Subgroup ↥H => IsParabolicTwo ↥H Pstar ∧
        (hS.toSylow : Subgroup ↥H) ≤ Pstar ∧
        (∀ t ∈ (hS.toSylow : Subgroup ↥H).map H.subtype,
          (Pstar.map H.subtype).map (MulAut.conj t).toMonoidHom = Pstar.map H.subtype) ∧
        ¬ Pstar ≤ KTabD.pointStab H hS.toSylow) Pstar →
      Pstar ≠ ⊤ ∧ (IsL2 (Bar2 (Hinf Pstar)) j ∨ (j = 1 ∧ Hinf Pstar = ⊥))) : n = j := by
  obtain ⟨-, hL2 | ⟨hj1, -⟩⟩ := hline _ (minimal_good_of_least hS.toSylow hpar hSQ hnot hleast)
  · obtain ⟨χ⟩ := nonempty_bar2_hinf_subgroupOf hPH
    exact kNshape_holds _ _ n j hN (Or.inl (CFSG.Blueprint.LieModel.of_mulEquiv χ.symm hL2))
  · omega

theorem nParam_eq_of_forall_minimal_eq_top {H S P : Subgroup (MulAut W)} {n j : ℕ}
    (hS : IsSylowIn 2 S H) (hBP : H ⊓ normalizer (S : Set (MulAut W)) ≤ P) (hPH : P ≤ H)
    (hcomm : commSub (fixV S) (Hinf P) ≠ ⊥) (hN : NParam (Hinf P) n)
    (hline : ∀ Pstar : Subgroup ↥H,
      Minimal (fun Pstar : Subgroup ↥H => IsParabolicTwo ↥H Pstar ∧
        (hS.toSylow : Subgroup ↥H) ≤ Pstar ∧
        (∀ t ∈ (hS.toSylow : Subgroup ↥H).map H.subtype,
          (Pstar.map H.subtype).map (MulAut.conj t).toMonoidHom = Pstar.map H.subtype) ∧
        ¬ Pstar ≤ KTabD.pointStab H hS.toSylow) Pstar →
      Pstar = ⊤ ∧ IsL2 (Bar2 (Hinf Pstar)) j) : n = j := by
  have : Finite (Subgroup ↥H) :=
    Finite.of_injective (fun K : Subgroup ↥H => (K : Set ↥H)) SetLike.coe_injective
  have hSP : S ≤ P := fun s hs => hBP ⟨hS.le hs, Subgroup.le_normalizer hs⟩
  have hPnot : ¬ P ≤ stabSub (fixV S) := not_le_stabSub_of_commSub_ne_bot hS hSP hPH hcomm
  obtain ⟨hpar, hSP'⟩ := isParabolicTwo_subgroupOf hS hBP
  have hnot := not_subgroupOf_le_pointStab hS hPH hPnot
  obtain ⟨Pstar, hle, hPstar⟩ := Finite.exists_le_minimal
    (p := fun Pstar : Subgroup ↥H => IsParabolicTwo ↥H Pstar ∧
      (hS.toSylow : Subgroup ↥H) ≤ Pstar ∧
      (∀ t ∈ (hS.toSylow : Subgroup ↥H).map H.subtype,
        (Pstar.map H.subtype).map (MulAut.conj t).toMonoidHom = Pstar.map H.subtype) ∧
      ¬ Pstar ≤ KTabD.pointStab H hS.toSylow)
    ⟨hpar, hSP', map_conj_map_subtype_eq_of_le hSP', hnot⟩
  obtain ⟨htop, hL2⟩ := hline Pstar hPstar
  have hPtop : P.subgroupOf H = Pstar := le_antisymm (htop ▸ le_top) hle
  obtain ⟨χ⟩ := nonempty_bar2_hinf_subgroupOf hPH
  rw [hPtop] at χ
  exact kNshape_holds _ _ n j hN (Or.inl (CFSG.Blueprint.LieModel.of_mulEquiv χ.symm hL2))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5
