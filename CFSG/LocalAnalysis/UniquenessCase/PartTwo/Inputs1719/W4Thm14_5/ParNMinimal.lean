module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23d.Defs
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs2
public import CFSG.LocalAnalysis.UniquenessCase.UC22S20
public import CFSG.Quasithin.Background.D2Basic
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ParabolicTransfer
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KNatParMax.Transport
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsFiveKNshape
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.Bar2Transfer
import CFSG.GroupTheory.CoprimeActionSupport.TwoModuloExtension
import CFSG.Adapters.StatedPSLTwo
import CFSG.Quasithin.EmptyFaithful.T1515C4Mod

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22 Subgroup

theorem nonempty_bar2_equiv_of_mulEquiv {G G' : Type} [Group G] [Group G'] {X : Subgroup G}
    {Y : Subgroup G'} (ψ : ↥X ≃* ↥Y) : Nonempty (Bar2 X ≃* Bar2 Y) :=
  ⟨QuotientGroup.congr (CFSG.pCore 2 ↥X) (CFSG.pCore 2 ↥Y) ψ (CFSG.pCore_map_iso 2 ψ)⟩

variable {W : Type} [CommGroup W]

theorem commSub_fixV_Hinf_eq_bot [Finite W] {S P : Subgroup (MulAut W)}
    (hodd : ¬ 2 ∣ S.relIndex P) (hP : P ≤ stabSub (fixV S)) :
    commSub (fixV S) (Hinf P) = ⊥ := by
  have : Finite (MulAut W) :=
    Finite.of_injective (fun f : MulAut W => (f : W → W)) DFunLike.coe_injective
  set C : Subgroup ↥P := (centSub (fixV S)).subgroupOf P with hC
  have hCn : C.Normal := by
    refine ⟨fun c hc p => ?_⟩
    rw [hC, Subgroup.mem_subgroupOf, mem_centSub] at hc ⊢
    intro u hu
    have hpu : ((p : MulAut W)⁻¹) u ∈ fixV S := ((hP (P.inv_mem p.2)) u).2 hu
    change (p : MulAut W) ((c : MulAut W) (((p : MulAut W)⁻¹) u)) = u
    rw [hc _ hpu, MulAut.apply_inv_self]
  have hSC : S.subgroupOf P ≤ C := by
    intro s hs
    rw [hC, Subgroup.mem_subgroupOf, mem_centSub]
    exact fun u hu => mem_fixV.mp hu _ (Subgroup.mem_subgroupOf.mp hs)
  have hodd' : Odd (Nat.card (↥P ⧸ C)) := by
    rw [← Subgroup.index_eq_card, ← Nat.not_even_iff_odd, even_iff_two_dvd]
    exact fun h2 => hodd (h2.trans (Subgroup.index_dvd_of_le hSC))
  have hsolv : Group.IsSolvable (↥P ⧸ C) := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd'
  have hres : CFSG.perfectResidual ↥P ≤ C :=
    CFSG.GroupTheory.CoprimeActionSupport.TwoModuloExtension.perfectResidual_le_of_isSolvable_quotient
      hsolv
  rw [commSub_eq_bot_iff]
  intro w hw
  rw [mem_fixV]
  intro x hx
  obtain ⟨m, hm, rfl⟩ := uc22p21c_mem_Hinf.1 hx
  have hmC : (m : MulAut W) ∈ centSub (fixV S) := Subgroup.mem_subgroupOf.mp (hres hm)
  exact mem_centSub.mp hmC w hw

theorem not_le_stabSub_of_commSub_ne_bot [Finite W] {H S P : Subgroup (MulAut W)}
    (hS : IsSylowIn 2 S H) (hSP : S ≤ P) (hPH : P ≤ H)
    (hcomm : commSub (fixV S) (Hinf P) ≠ ⊥) : ¬ P ≤ stabSub (fixV S) := by
  intro hP
  refine hcomm (commSub_fixV_Hinf_eq_bot (fun h2 => hS.not_dvd_relIndex ?_) hP)
  rw [← Subgroup.relIndex_mul_relIndex S P H hSP hPH]
  exact h2.mul_right _

theorem mem_stabSub_fixV_of_mem_normalizer {S : Subgroup (MulAut W)} {r : MulAut W}
    (hr : r ∈ normalizer (S : Set (MulAut W))) : r ∈ stabSub (fixV S) := by
  have key : ∀ g ∈ normalizer (S : Set (MulAut W)), ∀ v ∈ fixV S, g v ∈ fixV S := by
    intro g hg v hv
    refine mem_fixV.2 fun s hs => ?_
    have hs' : g⁻¹ * s * g⁻¹⁻¹ ∈ S :=
      (Subgroup.mem_normalizer_iff.mp ((normalizer _).inv_mem hg) s).mp hs
    rw [inv_inv] at hs'
    have h1 := mem_fixV.1 hv _ hs'
    calc s (g v) = g ((g⁻¹ * s * g) v) := by
          rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.apply_inv_self]
      _ = g v := by rw [h1]
  intro v
  refine ⟨fun h => ?_, key r hr v⟩
  have := key r⁻¹ ((normalizer _).inv_mem hr) _ h
  rwa [MulAut.inv_apply_self] at this

theorem mem_normalizer_of_map_conj_le [Finite W] {X : Subgroup (MulAut W)} {r : MulAut W}
    (h : X ≤ X.map (MulAut.conj r).toMonoidHom) : r ∈ normalizer (X : Set (MulAut W)) := by
  have : Finite (MulAut W) :=
    Finite.of_injective (fun f : MulAut W => (f : W → W)) DFunLike.coe_injective
  have heq : X.map (MulAut.conj r).toMonoidHom = X :=
    (Subgroup.eq_of_le_of_card_ge h (by
      rw [Subgroup.card_map_of_injective (MulAut.conj r).injective])).symm
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have : (MulAut.conj r) x ∈ X.map (MulAut.conj r).toMonoidHom := ⟨x, hx, rfl⟩
    rwa [heq, MulAut.conj_apply] at this
  · intro hx
    rw [← heq] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hyx
    have : y = x := by
      have := congrArg (fun z => r⁻¹ * z * r) hyx
      simpa [mul_assoc] using this
    rwa [← this]

theorem eq_of_least_of_minimal [Finite W] {H R S P Q : Subgroup (MulAut W)}
    (hRH : R ≤ normalizer (H : Set (MulAut W))) (hRS : R ≤ normalizer (S : Set (MulAut W)))
    (hBP : H ⊓ normalizer (S : Set (MulAut W)) ≤ P) (hPH : P ≤ H)
    (hPnot : ¬ P ≤ stabSub (fixV S))
    (hmin : ∀ Q' : Subgroup (MulAut W), Q' < P → H ⊓ normalizer (S : Set (MulAut W)) ≤ Q' →
      R ≤ normalizer (Q' : Set (MulAut W)) → Hinf Q' = ⊥)
    (hQB : H ⊓ normalizer (S : Set (MulAut W)) ≤ Q) (hQH : Q ≤ H)
    (hQnot : ¬ Q ≤ stabSub (fixV S))
    (hleast : ∀ P' : Subgroup (MulAut W), H ⊓ normalizer (S : Set (MulAut W)) ≤ P' → P' ≤ H →
      ¬ P' ≤ stabSub (fixV S) → Q ≤ P')
    (hQinf : Hinf Q ≠ ⊥) : P = Q := by
  have hQP : Q ≤ P := hleast P hBP hPH hPnot
  have hRQ : R ≤ normalizer (Q : Set (MulAut W)) := by
    intro r hr
    have hrN := hRS hr
    have hrinv : r⁻¹ ∈ normalizer (S : Set (MulAut W)) := (normalizer _).inv_mem hrN
    have hrH := hRH hr
    have hrHinv : r⁻¹ ∈ normalizer (H : Set (MulAut W)) := (normalizer _).inv_mem hrH
    refine mem_normalizer_of_map_conj_le (hleast _ ?_ ?_ ?_)
    · intro x hx
      refine ⟨r⁻¹ * x * r, hQB ⟨?_, ?_⟩, ?_⟩
      · have := (Subgroup.mem_normalizer_iff.mp hrHinv x).mp hx.1
        simpa using this
      · have h1 := (normalizer (S : Set (MulAut W))).mul_mem
          ((normalizer (S : Set (MulAut W))).mul_mem hrinv hx.2) hrN
        exact h1
      · simp [MulAut.conj_apply, mul_assoc]
    · rintro _ ⟨x, hx, rfl⟩
      have := (Subgroup.mem_normalizer_iff.mp hrH x).mp (hQH hx)
      simpa [MulAut.conj_apply] using this
    · intro hle
      apply hQnot
      intro x hx
      have h1 : r * x * r⁻¹ ∈ stabSub (fixV S) := hle ⟨x, hx, by simp [MulAut.conj_apply]⟩
      have h2 := mem_stabSub_fixV_of_mem_normalizer hrN
      have h3 := mem_stabSub_fixV_of_mem_normalizer hrinv
      have h4 : r⁻¹ * (r * x * r⁻¹) * r = x := by group
      rw [← h4]
      exact (stabSub _).mul_mem ((stabSub _).mul_mem h3 h1) h2
  by_contra hne
  exact hQinf (hmin Q (lt_of_le_of_ne hQP (Ne.symm hne)) hQB hRQ)

section Bridge

variable {H S : Subgroup (MulAut W)} (hS : IsSylowIn 2 S H)
include hS

theorem normalizer_toSylow_eq :
    normalizer (((hS.toSylow : Sylow 2 ↥H) : Subgroup ↥H) : Set ↥H) =
      (normalizer (S : Set (MulAut W))).subgroupOf H := by
  rw [IsSylowIn.coe_toSylow hS]
  exact NatParMax.normalizer_subgroupOf_eq hS.le

theorem isParabolicTwo_subgroupOf {P' : Subgroup (MulAut W)}
    (hBP' : H ⊓ normalizer (S : Set (MulAut W)) ≤ P') :
    IsParabolicTwo ↥H (P'.subgroupOf H) ∧ (hS.toSylow : Subgroup ↥H) ≤ P'.subgroupOf H := by
  refine ⟨⟨hS.toSylow, fun x hx => ?_⟩, ?_⟩
  · have hx' : x ∈ normalizer (((hS.toSylow : Sylow 2 ↥H) : Subgroup ↥H) : Set ↥H) := hx
    rw [normalizer_toSylow_eq hS] at hx'
    exact Subgroup.mem_subgroupOf.mpr (hBP' ⟨x.2, Subgroup.mem_subgroupOf.mp hx'⟩)
  · rw [IsSylowIn.coe_toSylow hS]
    intro x hx
    exact Subgroup.mem_subgroupOf.mpr
      (hBP' ⟨x.2, Subgroup.le_normalizer (Subgroup.mem_subgroupOf.mp hx)⟩)

theorem not_subgroupOf_le_pointStab {P' : Subgroup (MulAut W)} (hP'H : P' ≤ H)
    (hP'not : ¬ P' ≤ stabSub (fixV S)) : ¬ P'.subgroupOf H ≤ KTabD.pointStab H hS.toSylow := by
  intro hle
  apply hP'not
  intro x hx
  have h1 : (⟨x, hP'H hx⟩ : ↥H) ∈ KTabD.pointStab H hS.toSylow :=
    hle (Subgroup.mem_subgroupOf.mpr hx)
  have h2 : x ∈ (KTabD.pointStab H hS.toSylow).map H.subtype := ⟨_, h1, rfl⟩
  rw [NatParMax.map_subtype_pointStab_eq_inf_stabSub hS] at h2
  exact h2.2

end Bridge

theorem map_conj_map_subtype_eq_of_le {H : Subgroup (MulAut W)} {S Q : Subgroup ↥H}
    (hSQ : S ≤ Q) : ∀ t ∈ S.map H.subtype,
      (Q.map H.subtype).map (MulAut.conj t).toMonoidHom = Q.map H.subtype := by
  rintro _ ⟨s, hs, rfl⟩
  have hsQ : (s : MulAut W) ∈ Q.map H.subtype := ⟨s, hSQ hs, rfl⟩
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact (Q.map H.subtype).mul_mem ((Q.map H.subtype).mul_mem hsQ hx)
      ((Q.map H.subtype).inv_mem hsQ)
  · intro x hx
    refine ⟨(s : MulAut W)⁻¹ * x * s, ?_, ?_⟩
    · exact (Q.map H.subtype).mul_mem ((Q.map H.subtype).mul_mem
        ((Q.map H.subtype).inv_mem hsQ) hx) hsQ
    · simp [MulAut.conj_apply, mul_assoc]

theorem minimal_good_of_least {H : Subgroup (MulAut W)} (S : Sylow 2 ↥H) {Qα : Subgroup ↥H}
    (hpar : IsParabolicTwo ↥H Qα) (hSQ : (S : Subgroup ↥H) ≤ Qα)
    (hnot : ¬ Qα ≤ KTabD.pointStab H S)
    (hleast : ∀ P : Subgroup ↥H, IsParabolicTwo ↥H P → (S : Subgroup ↥H) ≤ P →
      ¬ P ≤ KTabD.pointStab H S → Qα ≤ P) :
    Minimal (fun Pstar : Subgroup ↥H => IsParabolicTwo ↥H Pstar ∧ (S : Subgroup ↥H) ≤ Pstar ∧
      (∀ t ∈ (S : Subgroup ↥H).map H.subtype,
        (Pstar.map H.subtype).map (MulAut.conj t).toMonoidHom = Pstar.map H.subtype) ∧
      ¬ Pstar ≤ KTabD.pointStab H S) Qα :=
  ⟨⟨hpar, hSQ, map_conj_map_subtype_eq_of_le hSQ, hnot⟩,
    fun Q hQ _ => hleast Q hQ.1 hQ.2.1 hQ.2.2.2⟩

private theorem nontrivial_of_isL2_or_isL2Square {X : Type} [Group X] {j : ℕ}
    (h : IsL2 X j ∨ IsL2Square X j) : Nontrivial X := by
  rcases h with h | ⟨A, B, hA, hB, ⟨e⟩, hLA, -⟩
  · have := CFSG.Blueprint.LieModel.isSimpleGroup_psl_two h
    infer_instance
  · let : Group A := hA
    let : Group B := hB
    have : IsSimpleGroup A := CFSG.Blueprint.LieModel.isSimpleGroup_psl_two hLA
    obtain ⟨a, ha⟩ := exists_ne (1 : A)
    refine ⟨⟨e.symm (a, 1), 1, fun h => ha ?_⟩⟩
    have h1 := congrArg (fun x => (e x).1) h
    simpa using h1

theorem eq_of_leastParabolic [Finite W] {H R S P : Subgroup (MulAut W)} {n j : ℕ}
    (hS : IsSylowIn 2 S H)
    (hRH : R ≤ normalizer (H : Set (MulAut W))) (hRS : R ≤ normalizer (S : Set (MulAut W)))
    (hBP : H ⊓ normalizer (S : Set (MulAut W)) ≤ P) (hPH : P ≤ H)
    (hcomm : commSub (fixV S) (Hinf P) ≠ ⊥)
    (hmin : ∀ Q : Subgroup (MulAut W), Q < P → H ⊓ normalizer (S : Set (MulAut W)) ≤ Q →
      R ≤ normalizer (Q : Set (MulAut W)) → Hinf Q = ⊥)
    (hN : NParam (Hinf P) n) {Qα : Subgroup ↥H}
    (hpar : IsParabolicTwo ↥H Qα) (hSQ : (hS.toSylow : Subgroup ↥H) ≤ Qα)
    (hnot : ¬ Qα ≤ KTabD.pointStab H hS.toSylow)
    (hleast : ∀ P' : Subgroup ↥H, IsParabolicTwo ↥H P' → (hS.toSylow : Subgroup ↥H) ≤ P' →
      ¬ P' ≤ KTabD.pointStab H hS.toSylow → Qα ≤ P')
    (hQ : IsL2 (Bar2 (Hinf Qα)) j ∨ IsL2Square (Bar2 (Hinf Qα)) j) : n = j := by
  have hSP : S ≤ P := fun s hs => hBP ⟨hS.le hs, Subgroup.le_normalizer hs⟩
  have hPnot : ¬ P ≤ stabSub (fixV S) := not_le_stabSub_of_commSub_ne_bot hS hSP hPH hcomm
  have hQH : Qα.map H.subtype ≤ H := Subgroup.map_subtype_le Qα
  have hQB : H ⊓ normalizer (S : Set (MulAut W)) ≤ Qα.map H.subtype := by
    intro x hx
    have hxN : (⟨x, hx.1⟩ : ↥H) ∈
        normalizer (((hS.toSylow : Sylow 2 ↥H) : Subgroup ↥H) : Set ↥H) := by
      rw [normalizer_toSylow_eq hS]
      exact Subgroup.mem_subgroupOf.mpr hx.2
    exact ⟨⟨x, hx.1⟩, hpar.normalizer_le hS.toSylow hSQ hxN, rfl⟩
  have hQnot : ¬ Qα.map H.subtype ≤ stabSub (fixV S) := by
    intro hle
    apply hnot
    intro x hx
    have hxQ : (x : MulAut W) ∈ H ⊓ stabSub (fixV S) := ⟨x.2, hle ⟨x, hx, rfl⟩⟩
    rw [← NatParMax.map_subtype_pointStab_eq_inf_stabSub hS] at hxQ
    obtain ⟨y, hy, hyx⟩ := hxQ
    rwa [← Subtype.ext hyx]
  have hleast' : ∀ P' : Subgroup (MulAut W), H ⊓ normalizer (S : Set (MulAut W)) ≤ P' →
      P' ≤ H → ¬ P' ≤ stabSub (fixV S) → Qα.map H.subtype ≤ P' := by
    intro P' hBP' hP'H hP'not
    obtain ⟨hpar', hSP'⟩ := isParabolicTwo_subgroupOf hS hBP'
    have h := hleast _ hpar' hSP' (not_subgroupOf_le_pointStab hS hP'H hP'not)
    rintro _ ⟨y, hy, rfl⟩
    exact Subgroup.mem_subgroupOf.mp (h hy)
  have hQinf : Hinf (Qα.map H.subtype) = (Hinf Qα).map H.subtype := (Hinf_map H.subtype Qα).symm
  have hψ : ↥(Hinf (Qα.map H.subtype)) ≃* ↥(Hinf Qα) := by
    rw [hQinf]
    exact ((Hinf Qα).equivMapOfInjective H.subtype H.subtype_injective).symm
  obtain ⟨χ⟩ := nonempty_bar2_equiv_of_mulEquiv hψ
  have hQinf' : Hinf (Qα.map H.subtype) ≠ ⊥ := by
    intro hbot
    have : Subsingleton ↥(Hinf (Qα.map H.subtype)) := by
      rw [hbot]
      infer_instance
    have : Subsingleton (Bar2 (Hinf (Qα.map H.subtype))) :=
      (QuotientGroup.mk'_surjective _).subsingleton
    have : Subsingleton (Bar2 (Hinf Qα)) := χ.surjective.subsingleton
    have := nontrivial_of_isL2_or_isL2Square hQ
    exact not_subsingleton (Bar2 (Hinf Qα)) inferInstance
  have hPQ : P = Qα.map H.subtype := eq_of_least_of_minimal hRH hRS hBP hPH hPnot hmin hQB hQH
    hQnot hleast' hQinf'
  rw [hPQ] at hN
  exact kNshape_holds _ _ n j hN
    (hQ.imp (CFSG.Blueprint.LieModel.of_mulEquiv χ.symm) (IsL2Square.of_mulEquiv χ.symm))

theorem eq_of_least_of_line [Finite W] {H R S P : Subgroup (MulAut W)} {n j : ℕ}
    (hS : IsSylowIn 2 S H)
    (hRH : R ≤ normalizer (H : Set (MulAut W))) (hRS : R ≤ normalizer (S : Set (MulAut W)))
    (hBP : H ⊓ normalizer (S : Set (MulAut W)) ≤ P) (hPH : P ≤ H)
    (hcomm : commSub (fixV S) (Hinf P) ≠ ⊥)
    (hmin : ∀ Q : Subgroup (MulAut W), Q < P → H ⊓ normalizer (S : Set (MulAut W)) ≤ Q →
      R ≤ normalizer (Q : Set (MulAut W)) → Hinf Q = ⊥)
    (hN : NParam (Hinf P) n) (hj : 2 ≤ j)
    (hleast : ∃ Qα : Subgroup ↥H, IsParabolicTwo ↥H Qα ∧ (hS.toSylow : Subgroup ↥H) ≤ Qα ∧
      ¬ Qα ≤ KTabD.pointStab H hS.toSylow ∧
      ∀ P' : Subgroup ↥H, IsParabolicTwo ↥H P' → (hS.toSylow : Subgroup ↥H) ≤ P' →
        ¬ P' ≤ KTabD.pointStab H hS.toSylow → Qα ≤ P')
    (hline : ∀ Pstar : Subgroup ↥H,
      Minimal (fun Pstar : Subgroup ↥H => IsParabolicTwo ↥H Pstar ∧
        (hS.toSylow : Subgroup ↥H) ≤ Pstar ∧
        (∀ t ∈ (hS.toSylow : Subgroup ↥H).map H.subtype,
          (Pstar.map H.subtype).map (MulAut.conj t).toMonoidHom = Pstar.map H.subtype) ∧
        ¬ Pstar ≤ KTabD.pointStab H hS.toSylow) Pstar →
      Pstar ≠ ⊤ ∧ (IsL2 (Bar2 (Hinf Pstar)) j ∨ (j = 1 ∧ Hinf Pstar = ⊥))) : n = j := by
  obtain ⟨Qα, hpar, hSQ, hnot, hle⟩ := hleast
  obtain ⟨-, hL2 | ⟨hj1, -⟩⟩ := hline Qα (minimal_good_of_least hS.toSylow hpar hSQ hnot hle)
  · exact eq_of_leastParabolic hS hRH hRS hBP hPH hcomm hmin hN hpar hSQ hnot hle (Or.inl hL2)
  · omega

theorem eq_of_forall_minimal_eq_top [Finite W] {H R S P : Subgroup (MulAut W)} {n j : ℕ}
    (hS : IsSylowIn 2 S H)
    (hRH : R ≤ normalizer (H : Set (MulAut W))) (hRS : R ≤ normalizer (S : Set (MulAut W)))
    (hBP : H ⊓ normalizer (S : Set (MulAut W)) ≤ P) (hPH : P ≤ H)
    (hcomm : commSub (fixV S) (Hinf P) ≠ ⊥)
    (hmin : ∀ Q : Subgroup (MulAut W), Q < P → H ⊓ normalizer (S : Set (MulAut W)) ≤ Q →
      R ≤ normalizer (Q : Set (MulAut W)) → Hinf Q = ⊥)
    (hN : NParam (Hinf P) n)
    (hline : ∀ Pstar : Subgroup ↥H,
      Minimal (fun Pstar : Subgroup ↥H => IsParabolicTwo ↥H Pstar ∧
        (hS.toSylow : Subgroup ↥H) ≤ Pstar ∧
        (∀ t ∈ (hS.toSylow : Subgroup ↥H).map H.subtype,
          (Pstar.map H.subtype).map (MulAut.conj t).toMonoidHom = Pstar.map H.subtype) ∧
        ¬ Pstar ≤ KTabD.pointStab H hS.toSylow) Pstar →
      Pstar = ⊤ ∧ IsL2 (Bar2 (Hinf Pstar)) j) : n = j := by
  have : Finite (MulAut W) :=
    Finite.of_injective (fun f : MulAut W => (f : W → W)) DFunLike.coe_injective
  have : Finite (Subgroup ↥H) :=
    Finite.of_injective (fun K : Subgroup ↥H => (K : Set ↥H)) SetLike.coe_injective
  have hSP : S ≤ P := fun s hs => hBP ⟨hS.le hs, Subgroup.le_normalizer hs⟩
  have hPnot : ¬ P ≤ stabSub (fixV S) := not_le_stabSub_of_commSub_ne_bot hS hSP hPH hcomm
  have htop : ∀ P' : Subgroup ↥H, IsParabolicTwo ↥H P' → (hS.toSylow : Subgroup ↥H) ≤ P' →
      ¬ P' ≤ KTabD.pointStab H hS.toSylow → P' = ⊤ := by
    intro P' hpar' hSP' hnot'
    obtain ⟨Pstar, hle, hPstar⟩ := Finite.exists_le_minimal
      (p := fun Pstar : Subgroup ↥H => IsParabolicTwo ↥H Pstar ∧
        (hS.toSylow : Subgroup ↥H) ≤ Pstar ∧
        (∀ t ∈ (hS.toSylow : Subgroup ↥H).map H.subtype,
          (Pstar.map H.subtype).map (MulAut.conj t).toMonoidHom = Pstar.map H.subtype) ∧
        ¬ Pstar ≤ KTabD.pointStab H hS.toSylow)
      ⟨hpar', hSP', map_conj_map_subtype_eq_of_le hSP', hnot'⟩
    exact top_le_iff.mp ((hline Pstar hPstar).1 ▸ hle)
  obtain ⟨hpar, hSP'⟩ := isParabolicTwo_subgroupOf hS hBP
  have hnot := not_subgroupOf_le_pointStab hS hPH hPnot
  have hPtop : P.subgroupOf H = ⊤ := htop _ hpar hSP' hnot
  have hgood : Minimal (fun Pstar : Subgroup ↥H => IsParabolicTwo ↥H Pstar ∧
      (hS.toSylow : Subgroup ↥H) ≤ Pstar ∧
      (∀ t ∈ (hS.toSylow : Subgroup ↥H).map H.subtype,
        (Pstar.map H.subtype).map (MulAut.conj t).toMonoidHom = Pstar.map H.subtype) ∧
      ¬ Pstar ≤ KTabD.pointStab H hS.toSylow) ⊤ := by
    refine minimal_good_of_least hS.toSylow (hPtop ▸ hpar) le_top (hPtop ▸ hnot) ?_
    intro P' hpar' hSP'' hnot'
    exact (htop P' hpar' hSP'' hnot').ge
  refine eq_of_leastParabolic hS hRH hRS hBP hPH hcomm hmin hN (hPtop ▸ hpar) le_top
    (hPtop ▸ hnot) (fun P' hpar' hSP'' hnot' => (htop P' hpar' hSP'' hnot').ge) (Or.inl ?_)
  exact (hline ⊤ hgood).2

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5
