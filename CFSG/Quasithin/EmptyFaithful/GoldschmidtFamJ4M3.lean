module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtFamJ4M3Ker
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtFamJ4Perf
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtFamJ4Def

public section

namespace CFSG.Quasithin.J4Fam

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT CFSG.Sporadic.J4.QT2 CFSG.Quasithin.F134.J4E9
  CFSG.Quasithin.J4Loc CFSG.Quasithin.J4Rad

section M3Case


theorem isPGroup_ker_rho3_alpha3 (hF : J4Facts) :
    IsPGroup 2 ((rho3 hF).ker ⊓ V0.normalizerMonoidHom.ker : Subgroup ↥M3) := by
  intro m
  have hm1 : (m : ↥M3) ∈ (rho3 hF).ker := (Subgroup.mem_inf.mp m.2).1
  have hm2 : (m : ↥M3) ∈ V0.normalizerMonoidHom.ker := (Subgroup.mem_inf.mp m.2).2
  have hmD : ((m : ↥M3) : J) ∈ Subgroup.centralizer (V0 : Set J) :=
    (normalizerMonoidHom_eq_one_iff' V0 m.1).mp hm2
  have hmDm : (m : ↥M3) ∈ Dm := Subgroup.mem_subgroupOf.mpr hmD
  have hdker : (⟨m.1, hmDm⟩ : ↥Dm) ∈ ((rho3 hF).comp Dm.subtype).ker := hm1
  obtain ⟨k, hk⟩ := isPGroup_ker_rho3_Dm hF ⟨⟨m.1, hmDm⟩, hdker⟩
  refine ⟨k, Subtype.ext ?_⟩
  have h := congrArg (fun y : ((rho3 hF).comp Dm.subtype).ker => ((y : ↥Dm) : ↥M3)) hk
  simpa using h

end M3Case

theorem toGL_bijective_zmod_two :
    Function.Bijective (Matrix.SpecialLinearGroup.toGL (n := Fin 3) (R := ZMod 2)) := by
  refine ⟨Matrix.SpecialLinearGroup.toGL_injective, ?_⟩
  intro g
  have hdet : (g : Matrix (Fin 3) (Fin 3) (ZMod 2)).det = 1 := by
    have h := Matrix.isUnits_det_units g
    generalize (g : Matrix (Fin 3) (Fin 3) (ZMod 2)).det = x at h
    fin_cases x
    · exact absurd h not_isUnit_zero
    · rfl
  exact ⟨⟨g, hdet⟩, Matrix.GeneralLinearGroup.ext fun _ _ => rfl⟩

theorem exists_mulEquiv_GL_of_subgroup_eight {Γ : Type} [Group Γ] [Finite Γ] (V : Subgroup Γ)
    (hcomm : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a) (hsq : ∀ a ∈ V, a * a = 1)
    (hcard : Nat.card V = 8) : Nonempty (MulAut ↥V ≃* GL (Fin 3) (ZMod 2)) :=
  exists_mulEquiv_GL_of_eight (fun a b => Subtype.ext (hcomm a a.2 b b.2))
    (fun a => Subtype.ext (hsq a a.2)) hcard

theorem isPSL32_mulAut_of_subgroup_eight {Γ : Type} [Group Γ] [Finite Γ] (V : Subgroup Γ)
    (hcomm : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a) (hsq : ∀ a ∈ V, a * a = 1)
    (hcard : Nat.card V = 8) : IsPSL 3 2 1 (MulAut ↥V) := by
  obtain ⟨e⟩ := exists_mulEquiv_GL_of_subgroup_eight V hcomm hsq hcard
  exact CFSG.QuasithinUnique.Vol2Native.A312L.Seven.isPSL_three_two
    (e.trans (MulEquiv.ofBijective _ toGL_bijective_zmod_two).symm)

theorem isPSL32_mulAut_V0 (hM : MatFacts) :
    IsPSL 3 2 1 (MulAut ↥V0) :=
  isPSL32_mulAut_of_subgroup_eight V0 (V0_comm hM) (V0_sq hM) (card_V0 hM)

theorem isSimpleGroup_mulAut_of_subgroup_eight {Γ : Type} [Group Γ] [Finite Γ] (V : Subgroup Γ)
    (hcomm : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a) (hsq : ∀ a ∈ V, a * a = 1)
    (hcard : Nat.card V = 8) : IsSimpleGroup (MulAut ↥V) :=
  isSimpleGroup_mulAut_eight (fun a b => Subtype.ext (hcomm a a.2 b b.2))
    (fun a => Subtype.ext (hsq a a.2)) hcard

theorem isSolvable_of_map_le {Γ : Type*} [Group Γ] {B : Subgroup Γ} (P : Subgroup ↥B)
    (S : Subgroup Γ) [Group.IsSolvable ↥S] (h : P.map B.subtype ≤ S) : Group.IsSolvable ↥P := by
  let f : ↥P →* ↥S :=
    { toFun := fun x => ⟨(x.1 : Γ), h ⟨x.1, x.2, rfl⟩⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  refine Group.isSolvable_of_isSolvable_injective (f := f) ?_
  intro x y hxy
  have h1 : ((f x : ↥S) : Γ) = ((f y : ↥S) : Γ) := congrArg Subtype.val hxy
  exact Subtype.ext (Subtype.ext h1)

section Case


theorem m3_case : J4Case M3 := by
  intro B hB hBM
  have hF : J4Facts := j4Facts
  have hM := hF.mat
  have hBle : B ≤ M3 := le_sup_left.trans hBM
  have hBc : B ∈ cComp (B ⊔ P0) := hB
  have hperf : Group.IsPerfect ↥B := Subgroup.isPerfect_iff.mpr (perfect_of_mem_cComp hBc)
  have hnsolv : ¬ Group.IsSolvable ↥B := not_isSolvable_of_mem_cComp hBc
  have hnorm : ∀ P : Subgroup ↥B, P.Normal → P = ⊤ ∨ Group.IsSolvable ↥P := by
    intro P hP
    rcases normal_eq_top_or_map_le_solvRad hBc P with h | h
    · exact Or.inl h
    · right
      have hs : Group.IsSolvable ↥(solvRad B) := solvRad_isSolvable B
      exact isSolvable_of_map_le P (solvRad B) h
  let incl : ↥B →* ↥M3 := Subgroup.inclusion hBle
  have hK : IsPGroup 2 (((rho3 hF).comp incl).ker ⊓ (V0.normalizerMonoidHom.comp incl).ker :
      Subgroup ↥B) := by
    intro b
    have hb1 : incl b.1 ∈ (rho3 hF).ker := (Subgroup.mem_inf.mp b.2).1
    have hb2 : incl b.1 ∈ V0.normalizerMonoidHom.ker := (Subgroup.mem_inf.mp b.2).2
    obtain ⟨k, hk⟩ := isPGroup_ker_rho3_alpha3 hF ⟨incl b.1, Subgroup.mem_inf.mpr ⟨hb1, hb2⟩⟩
    refine ⟨k, Subtype.ext ?_⟩
    apply Subgroup.inclusion_injective hBle
    have h1 := congrArg (fun y : ((rho3 hF).ker ⊓ V0.normalizerMonoidHom.ker : Subgroup ↥M3) =>
      (y : ↥M3)) hk
    simpa using h1
  have hsimple : IsSimpleGroup (MulAut ↥V0) :=
    isSimpleGroup_mulAut_of_subgroup_eight V0 (V0_comm hM) (V0_sq hM) (card_V0 hM)
  rcases modO2_of_two_actions hperf hnsolv hnorm (card_mulAut_V0 hM) ((rho3 hF).comp incl)
      (V0.normalizerMonoidHom.comp incl) hK with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
  · exact J4Shape.of_alt5 e
  · exact J4Shape.of_psl32 e (isPSL32_mulAut_V0 hM)

end Case

end CFSG.Quasithin.J4Fam
