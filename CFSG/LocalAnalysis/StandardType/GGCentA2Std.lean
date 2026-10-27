module

public import CFSG.Blueprint.Catalog
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearAction
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphAction
public import CFSG.LocalAnalysis.StandardType.GGCentA2StdAux2

public section

namespace CFSG.StandardType.NTPlane

open CFSG.Open CFSG.Blueprint CFSG.ComponentClassification.CatalogueBHigherLinearAction
  CFSG.ComponentClassification.CatalogueBGraphForm
open scoped MatrixGroups

theorem ntpA2_std
    {f : ℕ} (hf : 1 ≤ f) {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ ((2 : ℕ) ^ f)) (e : Bool)
    {G : Type} [Group G] (ι : SL(3, L) →* G) (hι : ι.ker ≤ Subgroup.center SL(3, L))
    (stp : G →* G)
    (hstp : ∀ X : SL(3, L), stp (ι X) =
      ι (if e then slGraphAut 3 L (Matrix.SpecialLinearGroup.map Fr X)
        else Matrix.SpecialLinearGroup.map Fr X))
    (K : Subgroup G) (hKq : CFSG.Open.IsQuasisimple ↥K) (hKle : K ≤ ι.range)
    (hKfix : ∀ k ∈ K, stp k = k) :
    ∃ Q : Subgroup G, K ≤ Q ∧ Q ≤ ι.range ∧ (∀ k ∈ Q, stp k = k) ∧
      CFSG.Open.IsQuasisimple ↥Q ∧
      ((e = false ∧ LieModel (↥Q ⧸ Subgroup.center ↥Q) .PSL 3 2 f) ∨
        (e = true ∧ LieModel (↥Q ⧸ Subgroup.center ↥Q) .PSU 3 2 f)) := by
  classical
  cases e with
  | false =>
    have hstp' : ∀ X : SL(3, L), stp (ι X) =
        ι (Matrix.SpecialLinearGroup.map Fr X) := by
      intro X
      simpa using hstp X
    let Φ : SL(3, L) →* SL(3, L) := Matrix.SpecialLinearGroup.map Fr
    let P : Subgroup SL(3, L) := Φ.eqLocus (MonoidHom.id _)
    have hKleP : K ≤ P.map ι :=
      ntpA2S_le_fixed Φ ι hι stp hstp' K hKq.1 hKle hKfix
    let Q : Subgroup G := P.map ι
    have hKQ : K ≤ Q := hKleP
    have hQle : Q ≤ ι.range := Subgroup.map_le_range ι P
    have hQfix : ∀ k ∈ Q, stp k = k := by
      rintro k ⟨x, hx, rfl⟩
      rw [hstp' x]
      exact congrArg ι hx
    have hPqs : CFSG.IsQuasisimple ↥P := by
      change CFSG.IsQuasisimple ↥((Matrix.SpecialLinearGroup.map (n := Fin 3) Fr).eqLocus
        (MonoidHom.id _))
      exact ntpA2S_isQuasisimple_split hf Fr hFr
    obtain ⟨hQqs, ⟨eQP⟩⟩ := ntpA2S_quasisimple_map ι hι P hPqs
    let eP : CFSG.Open.StatedSL 3 (ntpA2S_fixedField Fr) ≃* ↥P :=
      ntpA2S_splitFixedStatedEquiv 3 Fr
    let eProj : ↥P ⧸ Subgroup.center ↥P ≃*
        CFSG.Open.StatedProj (CFSG.Open.StatedSL 3 (ntpA2S_fixedField Fr)) :=
      ntpA2S_splitProjEquiv eP
    have hKcard : Nat.card (ntpA2S_fixedField Fr) = 2 ^ f :=
      ntpA2S_card_fixedField hf Fr hFr
    haveI : Finite (ntpA2S_fixedField Fr) :=
      Nat.finite_of_card_ne_zero (by rw [hKcard]; positivity)
    let eQ : ↥Q ⧸ Subgroup.center ↥Q ≃*
        CFSG.Open.StatedProj (CFSG.Open.StatedSL 3 (ntpA2S_fixedField Fr)) :=
      eQP.symm.trans eProj
    have hmodel : CFSG.Open.StatedClassicalModel
        (↥Q ⧸ Subgroup.center ↥Q) .PSL 3 2 f :=
      ntpA2S_statedClassicalModel_psl hf hKcard eQ
    refine ⟨Q, hKQ, hQle, hQfix, (CFSG.Foundations.SteinbergCA.quasisimple_iff ↥Q).2.2.1.mp hQqs,
      Or.inl ⟨rfl, ?_⟩⟩
    exact Or.inl ⟨by decide, hmodel⟩
  | true =>
    have hstp' : ∀ X : SL(3, L), stp (ι X) =
        ι (slGraphAut 3 L (Matrix.SpecialLinearGroup.map Fr X)) := by
      intro X
      simpa using hstp X
    let Φ : SL(3, L) →* SL(3, L) :=
      (slGraphAut 3 L).toMonoidHom.comp (Matrix.SpecialLinearGroup.map Fr)
    let P : Subgroup SL(3, L) := Φ.eqLocus (MonoidHom.id _)
    have hKleP : K ≤ P.map ι :=
      ntpA2S_le_fixed Φ ι hι stp hstp' K hKq.1 hKle hKfix
    let Q : Subgroup G := P.map ι
    have hKQ : K ≤ Q := hKleP
    have hQle : Q ≤ ι.range := Subgroup.map_le_range ι P
    have hQfix : ∀ k ∈ Q, stp k = k := by
      rintro k ⟨x, hx, rfl⟩
      rw [hstp' x]
      exact congrArg ι hx
    by_cases hq : 2 < 2 ^ f
    · have hPqs : CFSG.IsQuasisimple ↥P := by
        change CFSG.IsQuasisimple ↥(((slGraphAut 3 L).toMonoidHom.comp
          (Matrix.SpecialLinearGroup.map (n := Fin 3) Fr)).eqLocus (MonoidHom.id _))
        exact ntpA2S_isQuasisimple_unitary hf hq Fr hFr
      obtain ⟨hQqs, ⟨eQP⟩⟩ := ntpA2S_quasisimple_map ι hι P hPqs
      let eP : CFSG.Open.StatedSU 3 (2 ^ f) (ntpA2S_fixedField (Fr.comp Fr)) ≃* ↥P :=
        ntpA2S_unitaryFixedEquiv 3 f (by norm_num) hf Fr hFr
      haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have hcardU := ntpA2S_card_fixedField_comp hf Fr hFr
      haveI : Finite (ntpA2S_fixedField (Fr.comp Fr)) :=
        Nat.finite_of_card_ne_zero (by rw [hcardU]; positivity)
      have hqne : (3, 2 ^ f) ≠ (3, 2) := by
        intro h
        have := congrArg Prod.snd h
        omega
      have hZ : Subgroup.center (CFSG.Open.StatedSU 3 (2 ^ f)
          (ntpA2S_fixedField (Fr.comp Fr))) =
          (CFSG.Open.StatedScalars (Fin 3) (ntpA2S_fixedField (Fr.comp Fr))).subgroupOf
            (CFSG.Open.StatedSU 3 (2 ^ f) (ntpA2S_fixedField (Fr.comp Fr))) :=
        (CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card (p := 2) (f := f)
          (F := ntpA2S_fixedField (Fr.comp Fr)) hcardU (by norm_num) hqne).2
      let eProj : ↥P ⧸ Subgroup.center ↥P ≃*
          CFSG.Open.StatedProj (CFSG.Open.StatedSU 3 (2 ^ f)
            (ntpA2S_fixedField (Fr.comp Fr))) :=
        ntpA2S_unitaryProjEquiv 3 (2 ^ f) eP hZ
      let eQ : ↥Q ⧸ Subgroup.center ↥Q ≃*
          CFSG.Open.StatedProj (CFSG.Open.StatedSU 3 (2 ^ f)
            (ntpA2S_fixedField (Fr.comp Fr))) :=
        eQP.symm.trans eProj
      have hf2 : 2 ≤ f := by
        by_contra h
        have h1 : f = 1 := by omega
        subst h1
        norm_num at hq
      have hmodel : CFSG.Open.StatedClassicalModel
          (↥Q ⧸ Subgroup.center ↥Q) .PSU 3 2 f :=
        ntpA2S_statedClassicalModel_psu hf2 hcardU eQ
      refine ⟨Q, hKQ, hQle, hQfix, (CFSG.Foundations.SteinbergCA.quasisimple_iff ↥Q).2.2.1.mp hQqs,
        Or.inr ⟨rfl, ?_⟩⟩
      exact Or.inl ⟨by decide, hmodel⟩
    · have hf1 : f = 1 := by
        have hge : 2 ≤ 2 ^ f := by
          calc 2 = 2 ^ 1 := (pow_one 2).symm
            _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
        have hle : 2 ^ f ≤ 2 := by omega
        have hpow : 2 ^ f = 2 ^ 1 := by
          rw [pow_one]
          exact le_antisymm hle hge
        exact Nat.pow_right_injective (by norm_num : 2 ≤ 2) hpow
      subst hf1
      have hcardU := ntpA2S_card_fixedField_comp hf Fr hFr
      have hcard4 : Nat.card (ntpA2S_fixedField (Fr.comp Fr)) = 4 := by
        simpa using hcardU
      haveI : Finite (ntpA2S_fixedField (Fr.comp Fr)) :=
        Nat.finite_of_card_ne_zero (by rw [hcard4]; norm_num)
      have hSolvSU : Group.IsSolvable
          (CFSG.Open.StatedSU 3 (2 ^ 1) (ntpA2S_fixedField (Fr.comp Fr))) :=
        CFSG.Quasithin.isSolvable_statedSU_one hcardU
      haveI : Group.IsSolvable
          (CFSG.Open.StatedSU 3 (2 ^ 1) (ntpA2S_fixedField (Fr.comp Fr))) := hSolvSU
      have eP : CFSG.Open.StatedSU 3 (2 ^ 1) (ntpA2S_fixedField (Fr.comp Fr)) ≃* ↥P :=
        ntpA2S_unitaryFixedEquiv 3 1 (by norm_num) (by norm_num) Fr (by simpa using hFr)
      have hSolvP : Group.IsSolvable ↥P :=
        Group.isSolvable_of_surjective (f := eP.toMonoidHom) eP.surjective
      haveI : Group.IsSolvable ↥P := hSolvP
      let g : ↥P →* ↥Q :=
        { toFun := fun x => ⟨ι (x : SL(3, L)), Subgroup.mem_map_of_mem ι x.2⟩
          map_one' := by ext; simp
          map_mul' := by intro x y; ext; simp }
      have hgsurj : Function.Surjective g := by
        rintro ⟨q, hq⟩
        obtain ⟨p, hp, rfl⟩ := hq
        exact ⟨⟨p, hp⟩, rfl⟩
      haveI : Group.IsSolvable ↥Q := Group.isSolvable_of_surjective hgsurj
      let inc : ↥K →* ↥Q :=
        { toFun := fun k => ⟨(k : G), hKQ k.2⟩
          map_one' := by ext; simp
          map_mul' := by intro x y; ext; simp }
      have hinc : Function.Injective inc := by
        intro a b h
        apply Subtype.ext
        exact congrArg (fun z : ↥Q => (z : G)) h
      have hSolvK : Group.IsSolvable ↥K :=
        Group.isSolvable_of_isSolvable_injective (f := inc) hinc
      have hKqC : CFSG.IsQuasisimple ↥K :=
        (CFSG.Foundations.SteinbergCA.quasisimple_iff ↥K).2.2.1.mpr hKq
      haveI : Nontrivial ↥K := CFSG.LocalCores.isQuasisimple_nontrivial hKqC
      haveI : Group.IsPerfect ↥K := ⟨hKq.1⟩
      exfalso
      exact Group.IsPerfect.not_isSolvable ↥K hSolvK


end CFSG.StandardType.NTPlane
