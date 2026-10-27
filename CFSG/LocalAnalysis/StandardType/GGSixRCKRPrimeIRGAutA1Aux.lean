module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeIRGDefs
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeIRGA1Sl2
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.StandardType CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.RCKC1
  CFSG.StandardType.ClassicalPosition
open CFSG.Open (StatedLieTag)

theorem irgA1_map_conj_subgroup_mulAut
    {G Q : Type*} [Group G] [Group Q]
    (mk : G →* Q) (θ : MulAut Q) (α : MulAut G)
    (hα : ∀ g : G, θ (mk g) = mk (α g))
    {A B : Subgroup G} {u w : G}
    (h : (A.map (MulAut.conj u).toMonoidHom).map α.toMonoidHom =
      B.map (MulAut.conj w).toMonoidHom) :
    (((A.map (MulAut.conj u).toMonoidHom).map mk).map θ.toMonoidHom) =
      (B.map (MulAut.conj w).toMonoidHom).map mk := by
  have hcomp : θ.toMonoidHom.comp mk = mk.comp α.toMonoidHom := MonoidHom.ext hα
  calc
    (((A.map (MulAut.conj u).toMonoidHom).map mk).map θ.toMonoidHom)
        = (A.map (MulAut.conj u).toMonoidHom).map (θ.toMonoidHom.comp mk) := by
          simp only [Subgroup.map_map, MonoidHom.comp_assoc]
    _ = (A.map (MulAut.conj u).toMonoidHom).map (mk.comp α.toMonoidHom) := by rw [hcomp]
    _ = ((A.map (MulAut.conj u).toMonoidHom).map α.toMonoidHom).map mk := by
          simp only [Subgroup.map_map, MonoidHom.comp_assoc]
    _ = (B.map (MulAut.conj w).toMonoidHom).map mk := by rw [h]

theorem irgA1_card_rootSubgroup (F : Type) [Field F] {i j : Fin 2} (hij : i ≠ j) :
    Nat.card (SpecialLinear.rootSubgroup 1 F hij) = Nat.card F := by
  let f : F → SpecialLinear.rootSubgroup 1 F hij := fun c =>
    ⟨Matrix.SpecialLinearGroup.transvection hij c,
      (SpecialLinear.mem_rootSubgroup hij _).mpr ⟨c, rfl⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · intro a b h
      have h' := congrArg (fun g : SpecialLinear.rootSubgroup 1 F hij =>
        ((g : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) i j) h
      simpa [f, Matrix.SpecialLinearGroup.transvection_coe, Matrix.single_apply, hij] using h'
    · intro g
      obtain ⟨c, hc⟩ := (SpecialLinear.mem_rootSubgroup hij
        (g : Matrix.SpecialLinearGroup (Fin 2) F)).mp g.2
      exact ⟨c, Subtype.ext hc⟩
  exact (Nat.card_congr (Equiv.ofBijective f hf)).symm

theorem irgA1_rootSubgroup_inf_opposite (F : Type) [Field F] :
    SpecialLinear.rootSubgroup 1 F (show (0 : Fin 2) ≠ 1 by decide) ⊓
        SpecialLinear.rootSubgroup 1 F (show (1 : Fin 2) ≠ 0 by decide) = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  obtain ⟨h1, h2⟩ := Subgroup.mem_inf.mp hg
  rw [Subgroup.mem_bot]
  obtain ⟨a, ha⟩ :=
    (SpecialLinear.mem_rootSubgroup (show (0 : Fin 2) ≠ 1 by decide) g).mp h1
  obtain ⟨b, hb⟩ :=
    (SpecialLinear.mem_rootSubgroup (show (1 : Fin 2) ≠ 0 by decide) g).mp h2
  have hab : a = 0 := by
    have h := congrArg (fun x : Matrix.SpecialLinearGroup (Fin 2) F =>
      ((x : Matrix (Fin 2) (Fin 2) F) 0 1)) (ha.trans hb.symm)
    simpa [Matrix.SpecialLinearGroup.transvection_coe, Matrix.single_apply,
      show (0 : Fin 2) ≠ 1 by decide] using h
  rw [← ha, hab]
  exact Matrix.SpecialLinearGroup.transvection_coeff_zero _

theorem irgA1_mem_roots_one {F : Type} [Field F] {β : Fin 1 → ℤ}
    (hβ : β ∈ (SpecialLinear.rootDatum 1 F).roots) :
    β = Pi.single (0 : Fin 1) 1 ∨ β = -Pi.single (0 : Fin 1) 1 := by
  change β ∈ roots (SpecialLinear.isFiniteType_A 1) ∅ at hβ
  rw [SpecialLinear.roots_eq] at hβ
  obtain ⟨i, j, hij, hto⟩ := hβ
  fin_cases i <;> fin_cases j
  · exact absurd rfl hij
  · left
    apply SpecialLinear.toStd_injective 1
    rw [SpecialLinear.toStd_single]
    exact hto
  · right
    apply SpecialLinear.toStd_injective 1
    rw [SpecialLinear.toStd_neg, SpecialLinear.toStd_single, hto, neg_sub]
    funext a
    fin_cases a <;> simp
  · exact absurd rfl hij

theorem irgA1_single_mem_roots (F : Type) [Field F] :
    Pi.single (0 : Fin 1) 1 ∈ (SpecialLinear.rootDatum 1 F).roots := by
  change Pi.single (0 : Fin 1) 1 ∈ roots (SpecialLinear.isFiniteType_A 1) ∅
  rw [SpecialLinear.roots_eq]
  exact ⟨0, 1, by decide, SpecialLinear.toStd_single 1 0⟩

theorem irgA1_neg_single_mem_roots (F : Type) [Field F] :
    -Pi.single (0 : Fin 1) 1 ∈ (SpecialLinear.rootDatum 1 F).roots := by
  change -Pi.single (0 : Fin 1) 1 ∈ roots (SpecialLinear.isFiniteType_A 1) ∅
  rw [SpecialLinear.roots_eq]
  refine ⟨1, 0, by decide, ?_⟩
  rw [SpecialLinear.toStd_neg, SpecialLinear.toStd_single, neg_sub]
  funext a
  fin_cases a <;> simp

theorem irgA1_neg_mem_roots_one (F : Type) [Field F] {β : Fin 1 → ℤ}
    (hβ : β ∈ (SpecialLinear.rootDatum 1 F).roots) :
    -β ∈ (SpecialLinear.rootDatum 1 F).roots := by
  rcases irgA1_mem_roots_one (F := F) hβ with rfl | rfl
  · simpa using irgA1_neg_single_mem_roots (F := F)
  · simpa using irgA1_single_mem_roots (F := F)

theorem irgA1_ggLongRoot_PSL (F : Type) [Field F] {β : Fin 1 → ℤ}
    (hβ : β ∈ (SpecialLinear.rootDatum 1 F).roots) :
    GGLongRoot (SpecialLinear.rootDatum 1 F) β := by
  have hcases := irgA1_mem_roots_one (F := F) hβ
  have hαmem := irgA1_single_mem_roots (F := F)
  have hsum : ∀ δ : Fin 1 → ℤ, δ ∈ (SpecialLinear.rootDatum 1 F).roots →
      ∑ i, δ i ≤ ∑ i, (Pi.single (0 : Fin 1) 1 : Fin 1 → ℤ) i := by
    intro δ hδ
    rcases irgA1_mem_roots_one (F := F) hδ with rfl | rfl
    · rw [Fin.sum_univ_one]
    · rw [Fin.sum_univ_one]
      simp
  rcases hcases with rfl | rfl
  · refine ⟨1, Pi.single (0 : Fin 1) 1, hαmem, hsum, ?_⟩
    rw [map_one, Module.End.one_apply]
    rfl
  · refine ⟨(coxeterMatrix (SpecialLinear.isFiniteType_A 1)).toCoxeterSystem.simple 0,
      Pi.single (0 : Fin 1) 1, hαmem, hsum, ?_⟩
    change -Pi.single (0 : Fin 1) 1 =
      weylAction (SpecialLinear.isFiniteType_A 1)
        ((coxeterMatrix (SpecialLinear.isFiniteType_A 1)).toCoxeterSystem.simple 0)
        (Pi.single (0 : Fin 1) 1)
    rw [weylAction_simple_single]

theorem irgA1_card_rootGroup (F : Type) [Field F] {β : Fin 1 → ℤ}
    (hβ : β ∈ (SpecialLinear.rootDatum 1 F).roots) :
    Nat.card ((SpecialLinear.rootDatum 1 F).rootGroup β) = Nat.card F := by
  change Nat.card (SpecialLinear.rootGroup 1 F β) = Nat.card F
  rw [SpecialLinear.rootGroup_eq_idx 1 F hβ]
  exact irgA1_card_rootSubgroup (F := F) (i := (SpecialLinear.idx 1 β).1)
    (j := (SpecialLinear.idx 1 β).2) (SpecialLinear.idx_spec 1 hβ).1

theorem irgA1_rootGroup_inf_neg (F : Type) [Field F] {β : Fin 1 → ℤ}
    (hβ : β ∈ (SpecialLinear.rootDatum 1 F).roots) :
    (SpecialLinear.rootGroup 1 F β) ⊓ (SpecialLinear.rootGroup 1 F (-β)) = ⊥ := by
  have hneg : SpecialLinear.toStd 1 (-(Pi.single (0 : Fin 1) 1)) =
      Pi.single (1 : Fin 2) 1 - Pi.single (0 : Fin 2) 1 := by
    rw [SpecialLinear.toStd_neg, SpecialLinear.toStd_single, neg_sub]
    funext a
    fin_cases a <;> simp
  rcases irgA1_mem_roots_one (F := F) hβ with rfl | rfl
  · rw [SpecialLinear.rootGroup_eq 1 F (show (0 : Fin 2) ≠ 1 by decide)
        (SpecialLinear.toStd_single 1 0),
      SpecialLinear.rootGroup_eq 1 F (show (1 : Fin 2) ≠ 0 by decide) hneg]
    exact irgA1_rootSubgroup_inf_opposite F
  · have hpos : SpecialLinear.toStd 1 (-(-(Pi.single (0 : Fin 1) 1))) =
        Pi.single (0 : Fin 2) 1 - Pi.single (1 : Fin 2) 1 := by
      rw [neg_neg, SpecialLinear.toStd_single]
      funext a
      fin_cases a <;> simp
    rw [SpecialLinear.rootGroup_eq 1 F (show (1 : Fin 2) ≠ 0 by decide) hneg,
      SpecialLinear.rootGroup_eq 1 F (show (0 : Fin 2) ≠ 1 by decide) hpos, inf_comm]
    exact irgA1_rootSubgroup_inf_opposite F

theorem irgA1_rootPairAut_sl2 {F : Type} [Field F] [Finite F] [CharP F 2]
    (hF : 4 ≤ Nat.card F)
    (θ : MulAut ((Matrix.SpecialLinearGroup (Fin 2) F) ⧸
      Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F)))
    {β' : Fin 1 → ℤ} (hβ' : β' ∈ (SpecialLinear.rootDatum 1 F).roots)
    (u' : Matrix.SpecialLinearGroup (Fin 2) F) :
    ∃ β : Fin 1 → ℤ, β ∈ (SpecialLinear.rootDatum 1 F).roots ∧
      GGLongRoot (SpecialLinear.rootDatum 1 F) β ∧
      ∃ u : Matrix.SpecialLinearGroup (Fin 2) F,
        (ggRootSub (SpecialLinear.rootDatum 1 F)
            (QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F)))
            β' u').map θ.toMonoidHom =
          ggRootSub (SpecialLinear.rootDatum 1 F)
            (QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F)))
            β u ∧
        (ggRootSub (SpecialLinear.rootDatum 1 F)
            (QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F)))
            (-β') u').map θ.toMonoidHom =
          ggRootSub (SpecialLinear.rootDatum 1 F)
            (QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F)))
            (-β) u := by
  let K := Matrix.SpecialLinearGroup (Fin 2) F
  let D := SpecialLinear.rootDatum 1 F
  let mk := QuotientGroup.mk' (Subgroup.center K)
  have hZ : Subgroup.center K = ⊥ := by
    rw [← CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars_eq_center 2 F,
      CFSG.LocalAnalysis.ComponentInitial.LinearCover.scalars_two_eq_bot F]
  obtain ⟨α, hα⟩ := irg_exists_aut_of_center_eq_bot hZ θ
  let P : Subgroup K := (D.rootGroup β').map (MulAut.conj u').toMonoidHom
  let Q : Subgroup K := (D.rootGroup (-β')).map (MulAut.conj u').toMonoidHom
  have hP : Nat.card P = Nat.card F := by
    change Nat.card ((D.rootGroup β').map (MulAut.conj u').toMonoidHom) = Nat.card F
    rw [Subgroup.card_map_of_injective (K := D.rootGroup β')
      (f := (MulAut.conj u').toMonoidHom) (MulAut.conj u').injective]
    exact irgA1_card_rootGroup (F := F) hβ'
  have hQ : Nat.card Q = Nat.card F := by
    change Nat.card ((D.rootGroup (-β')).map (MulAut.conj u').toMonoidHom) = Nat.card F
    rw [Subgroup.card_map_of_injective (K := D.rootGroup (-β'))
      (f := (MulAut.conj u').toMonoidHom) (MulAut.conj u').injective]
    exact irgA1_card_rootGroup (F := F) (irgA1_neg_mem_roots_one (F := F) hβ')
  have hPQ : P ⊓ Q = ⊥ := by
    change ((D.rootGroup β').map (MulAut.conj u').toMonoidHom) ⊓
      ((D.rootGroup (-β')).map (MulAut.conj u').toMonoidHom) = ⊥
    rw [← Subgroup.map_inf_eq (D.rootGroup β') (D.rootGroup (-β'))
      (MulAut.conj u').toMonoidHom (MulAut.conj u').injective]
    have h := irgA1_rootGroup_inf_neg (F := F) hβ'
    change (D.rootGroup β') ⊓ (D.rootGroup (-β')) = ⊥ at h
    rw [h, Subgroup.map_bot]
  have hP' : Nat.card (P.map α.toMonoidHom) = Nat.card F := by
    rw [Subgroup.card_map_of_injective (K := P) α.injective, hP]
  have hQ' : Nat.card (Q.map α.toMonoidHom) = Nat.card F := by
    rw [Subgroup.card_map_of_injective (K := Q) α.injective, hQ]
  have hPQ' : P.map α.toMonoidHom ⊓ Q.map α.toMonoidHom = ⊥ := by
    rw [← Subgroup.map_inf_eq P Q α.toMonoidHom α.injective, hPQ, Subgroup.map_bot]
  obtain ⟨β, w, hβeq, hPw, hQw⟩ :=
    irg_sl2_pair hF (P.map α.toMonoidHom) (Q.map α.toMonoidHom) hP' hQ' hPQ'
  have hβ : β ∈ (SpecialLinear.rootDatum 1 F).roots := by
    rcases hβeq with rfl | rfl
    · exact irgA1_single_mem_roots (F := F)
    · exact irgA1_neg_single_mem_roots (F := F)
  refine ⟨β, hβ, irgA1_ggLongRoot_PSL (F := F) hβ, w, ?_, ?_⟩
  · have h := irgA1_map_conj_subgroup_mulAut mk θ α hα
        (A := D.rootGroup β') (B := D.rootGroup β) (u := u') (w := w) ?_
    · simpa only [ggRootSub] using h
    · simpa only [P] using hPw
  · have h := irgA1_map_conj_subgroup_mulAut mk θ α hα
        (A := D.rootGroup (-β')) (B := D.rootGroup (-β)) (u := u') (w := w) ?_
    · simpa only [ggRootSub] using h
    · simpa only [Q] using hQw

end CFSG.StandardType.RCKRP
