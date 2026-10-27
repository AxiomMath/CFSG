module

public import CFSG.Quasithin.Recognition.St84.Gen.Sp4qAmalDefs
public import CFSG.Quasithin.Recognition.St84.Gen.L3qAmalDefs
public import CFSG.RankThree.PartOne.KC.EvenSymplecticFourRootAxisNormalizer

import CFSG.Quasithin.Vol2.GoldschmidtF431SpModel
import CFSG.CGT.PushingUpLit.BHS.ParabolicChoice

public section

noncomputable section

namespace CFSG.Quasithin.F112R.St84

open Matrix CFSG.Open CFSG.QuasithinUnique
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain
open CFSG.QuasithinUnique.Setup.X7b CFSG.RankThree.PartOne.KCRootAxis
open CFSG.Quasithin.H13.F431.SpModel CFSG.QuasithinUnique.Borel252
open scoped MatrixGroups

variable {F : Type} [Field F] [Finite F] [CharP F 2]
variable {n : ℕ}

private def radA2CMap (v : Fin 2 → F) (c : F) : Fin 3 → F :=
  ![c + v 0 * v 1, v 0 ^ 2, v 1 ^ 2]

private theorem radA2Rep_exists (x : ↥(radA2 F)) :
    ∃ p : (Fin 2 → F) × F, (x : antiSp F) = aElt p.1 p.2 := by
  obtain ⟨v, c, h⟩ := mem_radA2_iff.mp x.2
  exact ⟨(v, c), h⟩

private def radA2Rep (x : ↥(radA2 F)) : (Fin 2 → F) × F :=
  Classical.choose (radA2Rep_exists (F := F) x)

private theorem radA2Rep_spec (x : ↥(radA2 F)) :
    (x : antiSp F) = aElt (radA2Rep (F := F) x).1 (radA2Rep (F := F) x).2 :=
  Classical.choose_spec (radA2Rep_exists (F := F) x)

private theorem aElt_inj {v v' : Fin 2 → F} {c c' : F} (h : aElt v c = aElt v' c') :
    v = v' ∧ c = c' := by
  have h' : uElt (v 1) (v 0) c 0 = uElt (v' 1) (v' 0) c' 0 := h
  obtain ⟨h1, h0, hc, -⟩ := uElt_inj h'
  refine ⟨?_, hc⟩
  ext i
  fin_cases i
  · simpa using h0
  · simpa using h1

private def radA2CoordFun (x : ↥(radA2 F)) : Fin 3 → F :=
  radA2CMap (radA2Rep (F := F) x).1 (radA2Rep (F := F) x).2

private theorem radA2CoordFun_eq (x : ↥(radA2 F)) (v : Fin 2 → F) (c : F)
    (h : (x : antiSp F) = aElt v c) :
    radA2CoordFun (F := F) x = radA2CMap v c := by
  unfold radA2CoordFun
  obtain ⟨hv, hc⟩ := aElt_inj ((radA2Rep_spec (F := F) x).symm.trans h)
  rw [hv, hc]

private theorem radA2CMap_add (v w : Fin 2 → F) (c e : F) :
    radA2CMap (v + w) (c + e + (v 0 * w 1 + v 1 * w 0)) =
      radA2CMap v c + radA2CMap w e := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  ext i
  fin_cases i <;> simp [radA2CMap]
  · linear_combination (v 0 * w 1 + v 1 * w 0) * h2
  · linear_combination (v 0 * w 0) * h2
  · linear_combination (v 1 * w 1) * h2

private def radA2CoordHom : ↥(radA2 F) →* Multiplicative (Fin 3 → F) where
  toFun x := Multiplicative.ofAdd (radA2CoordFun (F := F) x)
  map_one' := by
    apply Multiplicative.toAdd.injective
    change radA2CoordFun (F := F) 1 = 0
    rw [radA2CoordFun_eq (F := F) 1 0 0 (by simp [aElt_zero_zero])]
    ext i
    fin_cases i <;> simp [radA2CMap]
  map_mul' x y := by
    apply Multiplicative.toAdd.injective
    change radA2CoordFun (F := F) (x * y) =
      radA2CoordFun (F := F) x + radA2CoordFun (F := F) y
    have hxy : ((x * y : ↥(radA2 F)) : antiSp F) =
        aElt ((radA2Rep (F := F) x).1 + (radA2Rep (F := F) y).1)
          ((radA2Rep (F := F) x).2 + (radA2Rep (F := F) y).2 +
            ((radA2Rep (F := F) x).1 0 * (radA2Rep (F := F) y).1 1 +
              (radA2Rep (F := F) x).1 1 * (radA2Rep (F := F) y).1 0)) := by
      show (x : antiSp F) * (y : antiSp F) = _
      rw [radA2Rep_spec (F := F) x, radA2Rep_spec (F := F) y, aElt_mul]
    calc radA2CoordFun (F := F) (x * y)
        = radA2CMap ((radA2Rep (F := F) x).1 + (radA2Rep (F := F) y).1)
            ((radA2Rep (F := F) x).2 + (radA2Rep (F := F) y).2 +
              ((radA2Rep (F := F) x).1 0 * (radA2Rep (F := F) y).1 1 +
                (radA2Rep (F := F) x).1 1 * (radA2Rep (F := F) y).1 0)) :=
          radA2CoordFun_eq (F := F) (x * y) _ _ hxy
      _ = radA2CoordFun (F := F) x + radA2CoordFun (F := F) y := by
          rw [radA2CoordFun_eq (F := F) x _ _ (radA2Rep_spec (F := F) x),
            radA2CoordFun_eq (F := F) y _ _ (radA2Rep_spec (F := F) y)]
          exact radA2CMap_add _ _ _ _

private theorem radA2CoordFun_injective : Function.Injective (radA2CoordFun (F := F)) := by
  intro x y h
  have hx := radA2Rep_spec (F := F) x
  have hy := radA2Rep_spec (F := F) y
  have h1 : radA2CoordFun (F := F) x 1 = radA2CoordFun (F := F) y 1 := congrFun h 1
  have h2 : radA2CoordFun (F := F) x 2 = radA2CoordFun (F := F) y 2 := congrFun h 2
  rw [radA2CoordFun_eq (F := F) x _ _ hx, radA2CoordFun_eq (F := F) y _ _ hy] at h1 h2
  simp [radA2CMap] at h1 h2
  have hv : (radA2Rep (F := F) x).1 = (radA2Rep (F := F) y).1 := by
    ext i
    fin_cases i
    · exact CharTwo.sq_inj.mp h1
    · exact CharTwo.sq_inj.mp h2
  have h0 := congrFun h 0
  rw [radA2CoordFun_eq (F := F) x _ _ hx, radA2CoordFun_eq (F := F) y _ _ hy, hv] at h0
  simp [radA2CMap] at h0
  have hc : (radA2Rep (F := F) x).2 = (radA2Rep (F := F) y).2 := h0
  apply Subtype.ext
  rw [hx, hy, hv, hc]

private theorem radA2CoordFun_surjective : Function.Surjective (radA2CoordFun (F := F)) := by
  intro z
  obtain ⟨v0, hv0⟩ := exists_sq_eq (z 1)
  obtain ⟨v1, hv1⟩ := exists_sq_eq (z 2)
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  refine ⟨⟨aElt ![v0, v1] (z 0 + v0 * v1), aElt_mem_radA2 _ _⟩, ?_⟩
  rw [radA2CoordFun_eq (F := F) ⟨aElt ![v0, v1] (z 0 + v0 * v1),
    aElt_mem_radA2 _ _⟩ ![v0, v1] (z 0 + v0 * v1) rfl]
  ext i
  fin_cases i
  · simp [radA2CMap]
    linear_combination (v0 * v1) * h2
  · simp [radA2CMap, hv0]
  · simp [radA2CMap, hv1]

def radA2Coord (F : Type) [Field F] [Finite F] [CharP F 2] :
    ↥(radA2 F) ≃* Multiplicative (Fin 3 → F) := by
  refine MulEquiv.ofBijective (radA2CoordHom (F := F)) ⟨?_, ?_⟩
  · intro x y h
    exact radA2CoordFun_injective (by simpa [radA2CoordHom] using congrArg Multiplicative.toAdd h)
  · intro z
    obtain ⟨x, hx⟩ := radA2CoordFun_surjective (F := F) (Multiplicative.toAdd z)
    exact ⟨x, by simpa [radA2CoordHom] using congrArg Multiplicative.ofAdd hx⟩

theorem radA2Coord_aElt (v : Fin 2 → F) (c : F) :
    Multiplicative.toAdd (radA2Coord F ⟨aElt v c, aElt_mem_radA2 v c⟩) =
      ![c + v 0 * v 1, v 0 ^ 2, v 1 ^ 2] := by
  change radA2CoordFun (F := F) ⟨aElt v c, aElt_mem_radA2 v c⟩ = radA2CMap v c
  rw [radA2CoordFun_eq (F := F) ⟨aElt v c, aElt_mem_radA2 v c⟩ v c rfl]

theorem actsByMatrix_radA2Coord (w : Fin 2 → F) (e : F) (l : Fˣ) (M : SL(2, F)) :
    ActsByMatrix (radA2Coord F) (aElt w e * (dElt l * sElt M))
      (((l : F) ^ 2) • sp4RadMat M) := by
  intro x y hy
  obtain ⟨v, c, hx⟩ := mem_radA2_iff.mp x.2
  have hx' : x = ⟨aElt v c, aElt_mem_radA2 v c⟩ := Subtype.ext hx
  have hy' : y = ⟨aElt ((l : F) • ((M : Matrix (Fin 2) (Fin 2) F) *ᵥ v))
      ((l : F) ^ 2 * c), aElt_mem_radA2 _ _⟩ := by
    apply Subtype.ext
    rw [hy, hx']
    simpa only [Subtype.coe_mk] using conj_aElt_normalForm w e l M v c
  rw [hx', hy', radA2Coord_aElt, radA2Coord_aElt]
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hdet : M 0 0 * M 1 1 - M 0 1 * M 1 0 = 1 := by
    have := M.2
    rwa [Matrix.det_fin_two] at this
  have hdet2 : M 0 0 * M 1 1 + M 0 1 * M 1 0 = 1 := by
    linear_combination hdet + (M 0 1 * M 1 0) * h2
  ext i
  fin_cases i
  · simp [radA2CMap, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Fin.sum_univ_three,
      Matrix.smul_apply, sp4RadMat]
    linear_combination ((l : F) ^ 2 * v 0 * v 1) * hdet2
  · simp [radA2CMap, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Fin.sum_univ_three,
      Matrix.smul_apply, sp4RadMat]
    linear_combination ((l : F) ^ 2 * M 0 0 * M 0 1 * v 0 * v 1) * h2
  · simp [radA2CMap, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Fin.sum_univ_three,
      Matrix.smul_apply, sp4RadMat]
    linear_combination ((l : F) ^ 2 * M 1 0 * M 1 1 * v 0 * v 1) * h2

private theorem radA2_sup_leviHom_range :
    radA2 F ⊔ (leviHom₂ F).range = lineStab F := by
  apply le_antisymm
  · exact sup_le radA2_le_lineStab leviHom₂_range_le_lineStab
  · intro g hg
    obtain ⟨v, c, l, M, rfl⟩ := exists_normalForm hg
    rw [← sElt_mul_dElt M l, ← leviHom₂_apply M l]
    exact mul_mem (Subgroup.mem_sup_left (aElt_mem_radA2 v c))
      (Subgroup.mem_sup_right (MonoidHom.mem_range.mpr ⟨(M, l), rfl⟩))

theorem linAction_radA2 :
    LinAction (Subgroup.normalizer (radA2 F : Set (antiSp F))) (radA2 F) (sp4Gamma F) := by
  refine ⟨radA2Coord F, ?_, ?_⟩
  · intro p hp
    obtain ⟨w, e, l, M, rfl⟩ := exists_normalForm (mem_normalizer_radA2_iff.mp hp)
    refine ⟨sp4GammaHom F (M, l ^ 2), MonoidHom.mem_range.mpr ⟨(M, l ^ 2), rfl⟩, ?_⟩
    have hcoe : ((sp4GammaHom F (M, l ^ 2) : GL (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) = ((l : F) ^ 2) • sp4RadMat M := by
      simp only [sp4GammaHom, MonoidHom.noncommCoprod_apply, Units.val_mul,
        coe_sp4RadHom, coe_sp4ScalarHom]
      rw [Matrix.mul_smul, Matrix.mul_one]
      rfl
    rw [hcoe]
    exact actsByMatrix_radA2Coord w e l M
  · intro A hA
    obtain ⟨M, c, hAmat⟩ := mem_sp4Gamma_iff.mp hA
    obtain ⟨x, hx⟩ := exists_sq_eq (c : F)
    have hx0 : x ≠ 0 := by
      intro hx0
      apply c.ne_zero
      rw [← hx, hx0]
      exact zero_pow (by norm_num : (2 : ℕ) ≠ 0)
    let l : Fˣ := Units.mk0 x hx0
    have hl : ((l : F) ^ 2) = (c : F) := by
      change x ^ 2 = (c : F)
      exact hx
    refine ⟨dElt l * sElt M, ?_, ?_⟩
    · rw [mem_normalizer_radA2_iff]
      have := firstCol_normalForm (0 : Fin 2 → F) 0 l M
      rwa [aElt_zero_zero, one_mul] at this
    · rw [hAmat, ← hl]
      simpa only [aElt_zero_zero, one_mul] using
        actsByMatrix_radA2Coord (F := F) (0 : Fin 2 → F) 0 l M

theorem isLinSemidirect_radA2 (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n) :
    IsLinSemidirect (Subgroup.normalizer (radA2 F : Set (antiSp F))) (radA2 F) (sp4Gamma F) where
  le := Subgroup.le_normalizer
  normal := le_rfl
  cent := by
    rintro g ⟨-, hgC⟩
    exact (borel_antiSp hn hF).cent₂ g fun r hr =>
      (Subgroup.mem_centralizer_iff.mp hgC r hr).symm
  split := by
    refine ⟨(leviHom₂ F).range, ?_, ?_, ?_⟩
    · rw [normalizer_radA2_eq]
      exact leviHom₂_range_le_lineStab
    · rw [inf_comm]
      exact radA2_inf_leviHom₂_range
    · rw [normalizer_radA2_eq]
      exact radA2_sup_leviHom_range
  act := linAction_radA2 (F := F)

private theorem actsByMatrix_equivMap {G G' : Type*} [Group G] [Group G'] {F : Type*} [Field F]
    {n : ℕ} {Q : Subgroup G} (β : ↥Q ≃* Multiplicative (Fin n → F)) {p : G}
    {A : Matrix (Fin n) (Fin n) F} (h : ActsByMatrix β p A) (e : G ≃* G') :
    ActsByMatrix ((Q.equivMapOfInjective e.toMonoidHom e.injective).symm.trans β) (e p) A := by
  intro x y hy
  set eQ : ↥Q ≃* ↥(Q.map e.toMonoidHom) :=
    Q.equivMapOfInjective e.toMonoidHom e.injective
  obtain ⟨x0, hx0, hxeq⟩ := Subgroup.mem_map.mp x.2
  obtain ⟨y0, hy0, hyeq⟩ := Subgroup.mem_map.mp y.2
  have hxval : x = ⟨e.toMonoidHom x0, Subgroup.mem_map_of_mem e.toMonoidHom hx0⟩ :=
    Subtype.ext hxeq.symm
  have hyval : y = ⟨e.toMonoidHom y0, Subgroup.mem_map_of_mem e.toMonoidHom hy0⟩ :=
    Subtype.ext hyeq.symm
  have hβx : (eQ.symm.trans β) x = β ⟨x0, hx0⟩ := by
    apply congrArg β
    rw [hxval]
    refine (MulEquiv.symm_apply_eq eQ).mpr ?_
    apply Subtype.ext
    rfl
  have hβy : (eQ.symm.trans β) y = β ⟨y0, hy0⟩ := by
    apply congrArg β
    rw [hyval]
    refine (MulEquiv.symm_apply_eq eQ).mpr ?_
    apply Subtype.ext
    rfl
  have hyrel : y0 = p * x0 * p⁻¹ := by
    apply e.injective
    rw [map_mul, map_mul, map_inv]
    rw [show e y0 = (y : G') from hyeq, show e x0 = (x : G') from hxeq]
    exact hy
  rw [hβx, hβy]
  exact h ⟨x0, hx0⟩ ⟨y0, hy0⟩ hyrel

theorem IsLinSemidirect.map_mulEquiv {G G' : Type*} [Group G] [Group G'] {P Q : Subgroup G}
    {K : Type*} [Field K] {m : ℕ} {Γ : Subgroup (GL (Fin m) K)} (h : IsLinSemidirect P Q Γ)
    (e : G ≃* G') :
    IsLinSemidirect (P.map e.toMonoidHom) (Q.map e.toMonoidHom) Γ where
  le := Subgroup.map_mono h.le
  normal := by
    have hle := Subgroup.map_mono (f := e.toMonoidHom) h.normal
    rwa [Subgroup.map_equiv_normalizer_eq] at hle
  cent := by
    rintro g' ⟨hg'P, hg'C⟩
    obtain ⟨g, hgP, rfl⟩ := Subgroup.mem_map.mp hg'P
    have hgC : g ∈ Subgroup.centralizer (Q : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro q hq
      have h := (Subgroup.mem_centralizer_iff.mp hg'C) (e q)
        (Subgroup.mem_map_of_mem e.toMonoidHom hq)
      apply e.injective
      simpa using h
    exact Subgroup.mem_map_of_mem e.toMonoidHom (h.cent ⟨hgP, hgC⟩)
  split := by
    obtain ⟨X, hXP, hXQ, hsup⟩ := h.split
    refine ⟨X.map e.toMonoidHom, Subgroup.map_mono hXP, ?_, ?_⟩
    · rw [← Subgroup.map_inf X Q e.toMonoidHom e.injective, hXQ, Subgroup.map_bot]
    · rw [← Subgroup.map_sup Q X e.toMonoidHom, hsup]
  act := by
    obtain ⟨β, hP, hΓ⟩ := h.act
    refine ⟨(Q.equivMapOfInjective e.toMonoidHom e.injective).symm.trans β, ?_, ?_⟩
    · intro p' hp'
      obtain ⟨p, hp, rfl⟩ := Subgroup.mem_map.mp hp'
      obtain ⟨A, hA, hAct⟩ := hP p hp
      exact ⟨A, hA, actsByMatrix_equivMap β hAct e⟩
    · intro A hA
      obtain ⟨p, hp, hAct⟩ := hΓ A hA
      exact ⟨e p, Subgroup.mem_map_of_mem e.toMonoidHom hp, actsByMatrix_equivMap β hAct e⟩

theorem isLinSemidirect_radA1 (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n) :
    IsLinSemidirect (Subgroup.normalizer (radA1 F : Set (antiSp F))) (radA1 F) (sp4Gamma F) := by
  have h := (isLinSemidirect_radA2 (F := F) hn hF).map_mulEquiv (minorAut F)
  have hN : (Subgroup.normalizer (radA2 F : Set (antiSp F))).map (minorAut F).toMonoidHom =
      Subgroup.normalizer (radA1 F : Set (antiSp F)) := by
    rw [Subgroup.map_equiv_normalizer_eq, ← radA1_eq_map]
  have hQ : (radA2 F).map (minorAut F).toMonoidHom = radA1 F := radA1_eq_map.symm
  rwa [hN, hQ] at h

theorem isSylowTwoOf_antiUnipotent_normalizer_radA1 (hn : 2 ≤ n)
    (hF : Nat.card F = 2 ^ n) :
    IsSylowTwoOf (antiUnipotent F) (Subgroup.normalizer (radA1 F : Set (antiSp F))) := by
  have hB := borel_antiSp (F := F) hn hF
  have hUN : antiUnipotent F ≤ Subgroup.normalizer (radA1 F : Set (antiSp F)) :=
    (Subgroup.le_normalizer (H := antiUnipotent F)).trans hB.lt₁.le
  exact CFSG.CGT.PushingUpLit.BHS.isSylowTwoOf_of_le hB.sylow hUN le_top

theorem isSylowTwoOf_antiUnipotent_normalizer_radA2 (hn : 2 ≤ n)
    (hF : Nat.card F = 2 ^ n) :
    IsSylowTwoOf (antiUnipotent F) (Subgroup.normalizer (radA2 F : Set (antiSp F))) := by
  have hB := borel_antiSp (F := F) hn hF
  have hUN : antiUnipotent F ≤ Subgroup.normalizer (radA2 F : Set (antiSp F)) :=
    (Subgroup.le_normalizer (H := antiUnipotent F)).trans hB.lt₂.le
  exact CFSG.CGT.PushingUpLit.BHS.isSylowTwoOf_of_le hB.sylow hUN le_top

end CFSG.Quasithin.F112R.St84
