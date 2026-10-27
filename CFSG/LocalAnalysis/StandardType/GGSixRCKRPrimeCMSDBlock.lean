module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeCMSDForm
public import CFSG.LocalAnalysis.ComponentInitial.FieldUnitaryHermitian
import all CFSG.LocalAnalysis.StandardType.ClassicalPosition.GeoPSU

public section

namespace CFSG.StandardType.RCKRP

open CFSG.LieType.Universal CFSG.StandardType CFSG.StandardType.ClassicalPosition
  CFSG.StandardType.TableCRes CFSG.LocalAnalysis.ComponentInitial CFSG.Timmesfeld.LieEmbed
open scoped Matrix


section Aux

variable {n g : ℕ}

noncomputable abbrev rckSD_W (ε : Matrix (Fin n) (Fin n) (PSUF g)) :
    Submodule (PSUF g) (Fin n → PSUF g) :=
  LinearMap.range (Matrix.mulVecLin ε)

noncomputable abbrev rckSD_G {s : GL (Fin n) (PSUF g)}
    (ε : Matrix (Fin n) (Fin n) (PSUF g)) : Subgroup (GL (Fin n) (PSUF g)) :=
  Subgroup.centralizer ({s} : Set (GL (Fin n) (PSUF g))) ⊓ glFixing (1 - ε) ⊓ GUsub (PSUσ g) n

variable {s : GL (Fin n) (PSUF g)} {ε : Matrix (Fin n) (Fin n) (PSUF g)}

private lemma rckSD_gPSU_h_eq_uForm (x y : Fin n → PSUF g) :
    gPSU_h (PSUσ g).toRingHom (Unitary.antidiag n) x y = uForm (PSUσ g) x y := by
  rw [gPSU_h_antidiag_apply, uForm_eq]
  rfl

variable {K : Type} [Field K] [Finite K] [Algebra (PSUF g) K]
variable [Module K (rckSD_W ε)] [IsScalarTower (PSUF g) K (rckSD_W ε)]

private noncomputable def rckSD_hForm :
    rckSD_W ε →ₛₗ[(PSUσ g).toRingHom] rckSD_W ε →ₗ[PSUF g] PSUF g :=
  LinearMap.mk₂'ₛₗ ((PSUσ g).toRingHom) (RingHom.id (PSUF g))
    (fun x y => gPSU_h (PSUσ g).toRingHom (Unitary.antidiag n)
      (x : Fin n → PSUF g) (y : Fin n → PSUF g))
    (fun x x' y => by
      simpa using gPSU_h_add_left (PSUσ g).toRingHom (Unitary.antidiag n)
        (x : Fin n → PSUF g) (x' : Fin n → PSUF g) (y : Fin n → PSUF g))
    (fun c x y => by
      simpa using gPSU_h_smul_left (PSUσ g).toRingHom (Unitary.antidiag n) c
        (x : Fin n → PSUF g) (y : Fin n → PSUF g))
    (fun x y y' => by
      simpa using gPSU_h_add_right (PSUσ g).toRingHom (Unitary.antidiag n)
        (x : Fin n → PSUF g) (y : Fin n → PSUF g) (y' : Fin n → PSUF g))
    (fun c x y => by
      simpa using gPSU_h_smul_right (PSUσ g).toRingHom (Unitary.antidiag n) c
        (x : Fin n → PSUF g) (y : Fin n → PSUF g))

variable {π : Algebra.adjoin (PSUF g)
  (Units.val '' ({s} : Set (GL (Fin n) (PSUF g)))) →ₐ[PSUF g] K}
variable {ρ : K ≃+* K}
variable {B : rckSD_W ε →ₛₗ[((ρ : K ≃+* K) : K →+* K)] rckSD_W ε →ₗ[K] K}

variable (hε : IsPrimAdjIdemIn (PSUσ g).toRingHom (Unitary.antidiag n)
  (Algebra.adjoin (PSUF g) (Units.val '' ({s} : Set (GL (Fin n) (PSUF g))))) ε)
variable (hπ : RCKBlockCoord {s} ε K π)
variable (hB : ∀ x y : rckSD_W ε,
  uForm (PSUσ g) (x : Fin n → PSUF g) (y : Fin n → PSUF g) = Algebra.trace (PSUF g) K (B x y))

private lemma rckSD_mem_G_iff {x : GL (Fin n) (PSUF g)} :
    x ∈ rckSD_G (s := s) ε ↔
      x ∈ Subgroup.centralizer ({s} : Set (GL (Fin n) (PSUF g))) ∧
      x ∈ glFixing (1 - ε) ∧ x ∈ GUsub (PSUσ g) n := by
  simp only [rckSD_G, Subgroup.mem_inf, and_assoc]

private lemma rckSD_mul_comm_adjoin {x : GL (Fin n) (PSUF g)}
    (hx : x ∈ Subgroup.centralizer ({s} : Set (GL (Fin n) (PSUF g))))
    {a : Matrix (Fin n) (Fin n) (PSUF g)}
    (ha : a ∈ Algebra.adjoin (PSUF g) (Units.val '' ({s} : Set (GL (Fin n) (PSUF g))))) :
    (x : Matrix (Fin n) (Fin n) (PSUF g)) * a = a * (x : Matrix (Fin n) (Fin n) (PSUF g)) := by
  have hgen : ∀ t ∈ (Units.val '' ({s} : Set (GL (Fin n) (PSUF g)))),
      Commute (x : Matrix (Fin n) (Fin n) (PSUF g)) t := by
    rintro _ ⟨t, ht, rfl⟩
    rw [Set.mem_singleton_iff] at ht
    rw [ht]
    have h := Subgroup.mem_centralizer_iff.mp hx s (Set.mem_singleton s)
    have h' : (s : Matrix (Fin n) (Fin n) (PSUF g)) * (x : Matrix (Fin n) (Fin n) (PSUF g)) =
        (x : Matrix (Fin n) (Fin n) (PSUF g)) * (s : Matrix (Fin n) (Fin n) (PSUF g)) := by
      simpa only [Units.val_mul] using congrArg (fun u : GL (Fin n) (PSUF g) =>
        (u : Matrix (Fin n) (Fin n) (PSUF g))) h
    exact h'.symm
  exact (Algebra.commute_of_mem_adjoin_of_forall_mem_commute ha hgen).eq

private lemma rckSD_mulVec_mem (hε : IsPrimAdjIdemIn (PSUσ g).toRingHom (Unitary.antidiag n)
      (Algebra.adjoin (PSUF g) (Units.val '' ({s} : Set (GL (Fin n) (PSUF g))))) ε)
    {x : GL (Fin n) (PSUF g)}
    (hx : x ∈ rckSD_G (s := s) ε) {w : Fin n → PSUF g} (hw : w ∈ rckSD_W ε) :
    Matrix.mulVec (x : Matrix (Fin n) (Fin n) (PSUF g)) w ∈ rckSD_W ε := by
  have hxcomm : (x : Matrix (Fin n) (Fin n) (PSUF g)) * ε =
      ε * (x : Matrix (Fin n) (Fin n) (PSUF g)) :=
    rckSD_mul_comm_adjoin (rckSD_mem_G_iff.mp hx).1 hε.1
  obtain ⟨v, hv⟩ := hw
  have hv' : Matrix.mulVec ε v = w := hv
  refine ⟨Matrix.mulVec (x : Matrix (Fin n) (Fin n) (PSUF g)) v, ?_⟩
  rw [Matrix.mulVecLin_apply]
  change Matrix.mulVec ε (Matrix.mulVec (x : Matrix (Fin n) (Fin n) (PSUF g)) v) =
    Matrix.mulVec (x : Matrix (Fin n) (Fin n) (PSUF g)) w
  rw [Matrix.mulVec_mulVec, ← hxcomm, ← Matrix.mulVec_mulVec, hv']

private lemma rckSD_eps_mulVec_of_mem (hε : IsPrimAdjIdemIn (PSUσ g).toRingHom
      (Unitary.antidiag n)
      (Algebra.adjoin (PSUF g) (Units.val '' ({s} : Set (GL (Fin n) (PSUF g))))) ε)
    {w : Fin n → PSUF g} (hw : w ∈ rckSD_W ε) : Matrix.mulVec ε w = w := by
  obtain ⟨v, hv⟩ := hw
  have hv' : Matrix.mulVec ε v = w := hv
  rw [← hv', Matrix.mulVec_mulVec, hε.2.1.eq]

private noncomputable def rckSD_rMap
    (hε : IsPrimAdjIdemIn (PSUσ g).toRingHom (Unitary.antidiag n)
      (Algebra.adjoin (PSUF g) (Units.val '' ({s} : Set (GL (Fin n) (PSUF g))))) ε)
    (hπ : RCKBlockCoord {s} ε K π) (x : rckSD_G (s := s) ε) :
    rckSD_W ε →ₗ[K] rckSD_W ε where
  toFun w := ⟨Matrix.mulVec (x.1 : Matrix (Fin n) (Fin n) (PSUF g)) (w : Fin n → PSUF g),
    rckSD_mulVec_mem hε x.2 w.2⟩
  map_add' u v := by
    apply Subtype.ext
    simp only [Submodule.coe_add, Matrix.mulVec_add]
  map_smul' c w := by
    obtain ⟨a, rfl⟩ := hπ.1 c
    apply Subtype.ext
    change Matrix.mulVec (x.1 : Matrix (Fin n) (Fin n) (PSUF g))
        ((π a • w : rckSD_W ε) : Fin n → PSUF g) =
      ((π a • (⟨Matrix.mulVec (x.1 : Matrix (Fin n) (Fin n) (PSUF g))
        (w : Fin n → PSUF g), rckSD_mulVec_mem hε x.2 w.2⟩ : rckSD_W ε) :
          rckSD_W ε) : Fin n → PSUF g)
    rw [hπ.2.1 a w, hπ.2.1 a ⟨Matrix.mulVec (x.1 : Matrix (Fin n) (Fin n) (PSUF g))
      (w : Fin n → PSUF g), rckSD_mulVec_mem hε x.2 w.2⟩]
    change Matrix.mulVec (x.1 : Matrix (Fin n) (Fin n) (PSUF g))
        (Matrix.mulVec (a : Matrix (Fin n) (Fin n) (PSUF g)) (w : Fin n → PSUF g)) =
      Matrix.mulVec (a : Matrix (Fin n) (Fin n) (PSUF g))
        (Matrix.mulVec (x.1 : Matrix (Fin n) (Fin n) (PSUF g)) (w : Fin n → PSUF g))
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
      rckSD_mul_comm_adjoin (rckSD_mem_G_iff.mp x.2).1 a.2]

private noncomputable def rckSD_rEquiv
    (hε : IsPrimAdjIdemIn (PSUσ g).toRingHom (Unitary.antidiag n)
      (Algebra.adjoin (PSUF g) (Units.val '' ({s} : Set (GL (Fin n) (PSUF g))))) ε)
    (hπ : RCKBlockCoord {s} ε K π) (x : rckSD_G (s := s) ε) :
    rckSD_W ε ≃ₗ[K] rckSD_W ε :=
  LinearEquiv.ofLinearMap (rckSD_rMap hε hπ x) (rckSD_rMap hε hπ x⁻¹)
    (by
      apply LinearMap.ext
      intro w
      change (rckSD_rMap hε hπ x) ((rckSD_rMap hε hπ x⁻¹) w) = w
      apply Subtype.ext
      change Matrix.mulVec ((x : rckSD_G (s := s) ε).1 : Matrix (Fin n) (Fin n) (PSUF g))
          (Matrix.mulVec (((x⁻¹ : rckSD_G (s := s) ε).1) : Matrix (Fin n) (Fin n) (PSUF g))
            (w : Fin n → PSUF g)) = (w : Fin n → PSUF g)
      have hxx : ((x : rckSD_G (s := s) ε).1 : Matrix (Fin n) (Fin n) (PSUF g)) *
          (((x⁻¹ : rckSD_G (s := s) ε).1) : Matrix (Fin n) (Fin n) (PSUF g)) = 1 := by
        simpa using
          congrArg (fun u : GL (Fin n) (PSUF g) => (u : Matrix (Fin n) (Fin n) (PSUF g)))
            (mul_inv_cancel ((x : rckSD_G (s := s) ε).1))
      rw [Matrix.mulVec_mulVec, hxx, Matrix.one_mulVec])
    (by
      apply LinearMap.ext
      intro w
      change (rckSD_rMap hε hπ x⁻¹) ((rckSD_rMap hε hπ x) w) = w
      apply Subtype.ext
      change Matrix.mulVec ((x⁻¹ : rckSD_G (s := s) ε).1 : Matrix (Fin n) (Fin n) (PSUF g))
          (Matrix.mulVec (((x : rckSD_G (s := s) ε).1) : Matrix (Fin n) (Fin n) (PSUF g))
            (w : Fin n → PSUF g)) = (w : Fin n → PSUF g)
      have hxx : (((x⁻¹ : rckSD_G (s := s) ε).1) : Matrix (Fin n) (Fin n) (PSUF g)) *
          ((x : rckSD_G (s := s) ε).1 : Matrix (Fin n) (Fin n) (PSUF g)) = 1 := by
        simpa using
          congrArg (fun u : GL (Fin n) (PSUF g) => (u : Matrix (Fin n) (Fin n) (PSUF g)))
            (inv_mul_cancel ((x : rckSD_G (s := s) ε).1))
      rw [Matrix.mulVec_mulVec, hxx, Matrix.one_mulVec])

private lemma rckSD_hForm_trace
    (hB : ∀ x y : rckSD_W ε,
      uForm (PSUσ g) (x : Fin n → PSUF g) (y : Fin n → PSUF g) =
        Algebra.trace (PSUF g) K (B x y))
    (x y : rckSD_W ε) :
    rckSD_hForm (ε := ε) x y = Algebra.trace (PSUF g) K (B x y) := by
  rw [show rckSD_hForm (ε := ε) x y =
      gPSU_h (PSUσ g).toRingHom (Unitary.antidiag n)
        (x : Fin n → PSUF g) (y : Fin n → PSUF g) from rfl,
    rckSD_gPSU_h_eq_uForm]
  exact hB x y

private lemma rckSD_mem_sesq (hε : IsPrimAdjIdemIn (PSUσ g).toRingHom (Unitary.antidiag n)
      (Algebra.adjoin (PSUF g) (Units.val '' ({s} : Set (GL (Fin n) (PSUF g))))) ε)
    (hπ : RCKBlockCoord {s} ε K π)
    (hB : ∀ x y : rckSD_W ε,
      uForm (PSUσ g) (x : Fin n → PSUF g) (y : Fin n → PSUF g) =
        Algebra.trace (PSUF g) K (B x y))
    (x : rckSD_G (s := s) ε) :
    LinearMap.GeneralLinearGroup.ofLinearEquiv (rckSD_rEquiv hε hπ x) ∈
      sesqUnitaryGroup B := by
  rw [mem_sesqUnitaryGroup]
  refine (CFSG.LieType.SemisimpleCentralizers.HeldUCD.unitary_trace_iff
    (L := PSUF g) (K := K) (W := rckSD_W ε) (rckSD_hForm (ε := ε)) B
    (fun x y => rckSD_hForm_trace hB x y)
    (LinearMap.GeneralLinearGroup.ofLinearEquiv (rckSD_rEquiv hε hπ x) :
      rckSD_W ε →ₗ[K] rckSD_W ε)).mp ?_
  intro u v
  have hxGU : ((x : rckSD_G (s := s) ε).1 : GL (Fin n) (PSUF g)) ∈ GUsub (PSUσ g) n :=
    (rckSD_mem_G_iff.mp x.2).2.2
  have hiso := gPSU_isometry_of_mem (PSUσ g).toRingHom (Unitary.antidiag n)
    (S := ({((x : rckSD_G (s := s) ε).1 : GL (Fin n) (PSUF g))} :
      Set (GL (Fin n) (PSUF g))))
    (hSU := by
      intro t ht
      rw [Set.mem_singleton_iff] at ht
      rw [ht]
      exact mem_GUsub_iff.mp hxGU)
    (s := ((x : rckSD_G (s := s) ε).1 : GL (Fin n) (PSUF g))) (Set.mem_singleton _)
    (u : Fin n → PSUF g) (v : Fin n → PSUF g)
  change gPSU_h (PSUσ g).toRingHom (Unitary.antidiag n)
      (Matrix.mulVec ((x : rckSD_G (s := s) ε).1 : Matrix (Fin n) (Fin n) (PSUF g))
        (u : Fin n → PSUF g))
      (Matrix.mulVec ((x : rckSD_G (s := s) ε).1 : Matrix (Fin n) (Fin n) (PSUF g))
        (v : Fin n → PSUF g)) =
    gPSU_h (PSUσ g).toRingHom (Unitary.antidiag n)
      (u : Fin n → PSUF g) (v : Fin n → PSUF g)
  exact hiso

private noncomputable def rckSD_epsV (v : Fin n → PSUF g) : rckSD_W ε :=
  ⟨Matrix.mulVec ε v, ⟨v, by rw [Matrix.mulVecLin_apply]⟩⟩

private noncomputable def rckSD_extMap (γ : rckSD_W ε ≃ₗ[K] rckSD_W ε) :
    (Fin n → PSUF g) →ₗ[PSUF g] (Fin n → PSUF g) where
  toFun v := (γ (rckSD_epsV (ε := ε) v) : Fin n → PSUF g) + (v - Matrix.mulVec ε v)
  map_add' u v := by
    change (γ (rckSD_epsV (ε := ε) (u + v)) : Fin n → PSUF g) +
        (u + v - Matrix.mulVec ε (u + v)) =
      ((γ (rckSD_epsV (ε := ε) u) : Fin n → PSUF g) + (u - Matrix.mulVec ε u)) +
        ((γ (rckSD_epsV (ε := ε) v) : Fin n → PSUF g) + (v - Matrix.mulVec ε v))
    have hV : rckSD_epsV (ε := ε) (u + v) = rckSD_epsV (ε := ε) u + rckSD_epsV (ε := ε) v := by
      apply Subtype.ext
      exact Matrix.mulVec_add ε u v
    rw [hV, map_add, Matrix.mulVec_add]
    simp only [Submodule.coe_add]
    abel
  map_smul' c v := by
    change (γ (rckSD_epsV (ε := ε) (c • v)) : Fin n → PSUF g) +
        (c • v - Matrix.mulVec ε (c • v)) =
      c • ((γ (rckSD_epsV (ε := ε) v) : Fin n → PSUF g) + (v - Matrix.mulVec ε v))
    have hV : rckSD_epsV (ε := ε) (c • v) = c • rckSD_epsV (ε := ε) v := by
      apply Subtype.ext
      exact Matrix.mulVec_smul ε c v
    rw [hV]
    have hγs : (γ (c • rckSD_epsV (ε := ε) v) : rckSD_W ε) =
        c • (γ (rckSD_epsV (ε := ε) v) : rckSD_W ε) :=
      LinearMap.map_smul_of_tower (γ : rckSD_W ε →ₗ[K] rckSD_W ε) c
        (rckSD_epsV (ε := ε) v)
    rw [hγs, Matrix.mulVec_smul]
    simp only [Submodule.coe_smul, smul_add, smul_sub]

private lemma rckSD_extMap_apply (γ : rckSD_W ε ≃ₗ[K] rckSD_W ε) (v : Fin n → PSUF g) :
    rckSD_extMap (ε := ε) γ v =
      (γ (rckSD_epsV (ε := ε) v) : Fin n → PSUF g) + (v - Matrix.mulVec ε v) := rfl

private lemma rckSD_extMap_eps (hε : IsPrimAdjIdemIn (PSUσ g).toRingHom
      (Unitary.antidiag n)
      (Algebra.adjoin (PSUF g) (Units.val '' ({s} : Set (GL (Fin n) (PSUF g))))) ε)
    (γ : rckSD_W ε ≃ₗ[K] rckSD_W ε) (v : Fin n → PSUF g) :
    Matrix.mulVec ε (rckSD_extMap (ε := ε) γ v) =
      (γ (rckSD_epsV (ε := ε) v) : Fin n → PSUF g) := by
  rw [rckSD_extMap_apply, Matrix.mulVec_add, Matrix.mulVec_sub,
    rckSD_eps_mulVec_of_mem hε (γ (rckSD_epsV (ε := ε) v)).2,
    rckSD_eps_mulVec_of_mem hε (show Matrix.mulVec ε v ∈ rckSD_W ε from ⟨v, rfl⟩)]
  abel

private lemma rckSD_extMap_one_sub (hε : IsPrimAdjIdemIn (PSUσ g).toRingHom
      (Unitary.antidiag n)
      (Algebra.adjoin (PSUF g) (Units.val '' ({s} : Set (GL (Fin n) (PSUF g))))) ε)
    (γ : rckSD_W ε ≃ₗ[K] rckSD_W ε) (v : Fin n → PSUF g) :
    Matrix.mulVec (1 - ε) (rckSD_extMap (ε := ε) γ v) = Matrix.mulVec (1 - ε) v := by
  rw [rckSD_extMap_apply, Matrix.mulVec_add]
  have hγ : Matrix.mulVec (1 - ε) (γ (rckSD_epsV (ε := ε) v) : Fin n → PSUF g) = 0 := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec,
      rckSD_eps_mulVec_of_mem hε (γ (rckSD_epsV (ε := ε) v)).2, sub_self]
  rw [hγ, zero_add]
  rw [Matrix.mulVec_sub, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.sub_mulVec,
    Matrix.one_mulVec, Matrix.mulVec_mulVec, hε.2.1.eq]
  abel

private lemma rckSD_extMap_comp (hε : IsPrimAdjIdemIn (PSUσ g).toRingHom
      (Unitary.antidiag n)
      (Algebra.adjoin (PSUF g) (Units.val '' ({s} : Set (GL (Fin n) (PSUF g))))) ε)
    (γ : rckSD_W ε ≃ₗ[K] rckSD_W ε) :
    (rckSD_extMap (ε := ε) γ).comp (rckSD_extMap (ε := ε) γ.symm) = LinearMap.id := by
  apply LinearMap.ext
  intro v
  rw [LinearMap.comp_apply, LinearMap.id_apply, rckSD_extMap_apply]
  have hεT : Matrix.mulVec ε (rckSD_extMap (ε := ε) γ.symm v) =
      (γ.symm (rckSD_epsV (ε := ε) v) : Fin n → PSUF g) :=
    rckSD_extMap_eps hε γ.symm v
  have h1T : Matrix.mulVec (1 - ε) (rckSD_extMap (ε := ε) γ.symm v) =
      Matrix.mulVec (1 - ε) v := rckSD_extMap_one_sub hε γ.symm v
  have harg : rckSD_epsV (ε := ε) (rckSD_extMap (ε := ε) γ.symm v) =
      γ.symm (rckSD_epsV (ε := ε) v) := Subtype.ext hεT
  have hsub : rckSD_extMap (ε := ε) γ.symm v -
      Matrix.mulVec ε (rckSD_extMap (ε := ε) γ.symm v) = Matrix.mulVec (1 - ε) v := by
    rw [← h1T, Matrix.sub_mulVec, Matrix.one_mulVec]
  rw [harg, γ.apply_symm_apply, hsub]
  change Matrix.mulVec ε v + Matrix.mulVec (1 - ε) v = v
  rw [← Matrix.add_mulVec, add_sub_cancel, Matrix.one_mulVec]

private lemma rckSD_extMap_comp_symm (hε : IsPrimAdjIdemIn (PSUσ g).toRingHom
      (Unitary.antidiag n)
      (Algebra.adjoin (PSUF g) (Units.val '' ({s} : Set (GL (Fin n) (PSUF g))))) ε)
    (γ : rckSD_W ε ≃ₗ[K] rckSD_W ε) :
    (rckSD_extMap (ε := ε) γ.symm).comp (rckSD_extMap (ε := ε) γ) = LinearMap.id := by
  simpa [LinearEquiv.symm_symm] using rckSD_extMap_comp hε γ.symm

private lemma rckSD_extMap_smul_s (hε : IsPrimAdjIdemIn (PSUσ g).toRingHom
      (Unitary.antidiag n)
      (Algebra.adjoin (PSUF g) (Units.val '' ({s} : Set (GL (Fin n) (PSUF g))))) ε)
    (hπ : RCKBlockCoord {s} ε K π) (γ : rckSD_W ε ≃ₗ[K] rckSD_W ε)
    (v : Fin n → PSUF g) :
    rckSD_extMap (ε := ε) γ (Matrix.mulVec (s : Matrix (Fin n) (Fin n) (PSUF g)) v) =
      Matrix.mulVec (s : Matrix (Fin n) (Fin n) (PSUF g)) (rckSD_extMap (ε := ε) γ v) := by
  have hsA : (s : Matrix (Fin n) (Fin n) (PSUF g)) ∈
      Algebra.adjoin (PSUF g) (Units.val '' ({s} : Set (GL (Fin n) (PSUF g)))) :=
    Algebra.subset_adjoin ⟨s, by simp, rfl⟩
  have hsC : s ∈ Subgroup.centralizer ({s} : Set (GL (Fin n) (PSUF g))) := by
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    rw [Set.mem_singleton_iff] at ht
    rw [ht]
  have hsε : (s : Matrix (Fin n) (Fin n) (PSUF g)) * ε =
      ε * (s : Matrix (Fin n) (Fin n) (PSUF g)) :=
    rckSD_mul_comm_adjoin hsC hε.1
  have hV : rckSD_epsV (ε := ε) (Matrix.mulVec (s : Matrix (Fin n) (Fin n) (PSUF g)) v) =
      (π ⟨s, hsA⟩) • rckSD_epsV (ε := ε) v := by
    apply Subtype.ext
    rw [show (((π ⟨s, hsA⟩ • rckSD_epsV (ε := ε) v : rckSD_W ε) : Fin n → PSUF g)) =
        Matrix.mulVec (s : Matrix (Fin n) (Fin n) (PSUF g))
          (rckSD_epsV (ε := ε) v : Fin n → PSUF g) from hπ.2.1 ⟨s, hsA⟩ _]
    change Matrix.mulVec ε (Matrix.mulVec (s : Matrix (Fin n) (Fin n) (PSUF g)) v) =
      Matrix.mulVec (s : Matrix (Fin n) (Fin n) (PSUF g)) (Matrix.mulVec ε v)
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hsε]
  have hγs : (γ (rckSD_epsV (ε := ε)
        (Matrix.mulVec (s : Matrix (Fin n) (Fin n) (PSUF g)) v)) : rckSD_W ε) =
      Matrix.mulVec (s : Matrix (Fin n) (Fin n) (PSUF g))
        (γ (rckSD_epsV (ε := ε) v) : Fin n → PSUF g) := by
    rw [hV, map_smul, hπ.2.1]
  have hslin : Matrix.mulVec (s : Matrix (Fin n) (Fin n) (PSUF g))
        (v - Matrix.mulVec ε v) =
      Matrix.mulVec (s : Matrix (Fin n) (Fin n) (PSUF g)) v -
        Matrix.mulVec ε (Matrix.mulVec (s : Matrix (Fin n) (Fin n) (PSUF g)) v) := by
    rw [Matrix.mulVec_sub]
    congr 1
    rw [Matrix.mulVec_mulVec, hsε, ← Matrix.mulVec_mulVec]
  rw [rckSD_extMap_apply]
  conv_rhs => rw [rckSD_extMap_apply]
  rw [Matrix.mulVec_add, hγs, hslin]

private lemma rckSD_extMap_apply_one_sub (hε : IsPrimAdjIdemIn (PSUσ g).toRingHom
      (Unitary.antidiag n)
      (Algebra.adjoin (PSUF g) (Units.val '' ({s} : Set (GL (Fin n) (PSUF g))))) ε)
    (γ : rckSD_W ε ≃ₗ[K] rckSD_W ε) (v : Fin n → PSUF g) :
    rckSD_extMap (ε := ε) γ (Matrix.mulVec (1 - ε) v) = Matrix.mulVec (1 - ε) v := by
  rw [rckSD_extMap_apply]
  have hεv : Matrix.mulVec ε (Matrix.mulVec (1 - ε) v) = 0 := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_sub, Matrix.mul_one, hε.2.1.eq, sub_self,
      Matrix.zero_mulVec]
  have hzero : rckSD_epsV (ε := ε) (Matrix.mulVec (1 - ε) v) = 0 := Subtype.ext hεv
  rw [hzero, map_zero, hεv]
  simp

private noncomputable def rckSD_unit (hε : IsPrimAdjIdemIn (PSUσ g).toRingHom
      (Unitary.antidiag n)
      (Algebra.adjoin (PSUF g) (Units.val '' ({s} : Set (GL (Fin n) (PSUF g))))) ε)
    (γ : rckSD_W ε ≃ₗ[K] rckSD_W ε) : GL (Fin n) (PSUF g) :=
  ⟨LinearMap.toMatrix' (rckSD_extMap (ε := ε) γ),
   LinearMap.toMatrix' (rckSD_extMap (ε := ε) γ.symm),
   by
     apply Matrix.toLin'.injective
     rw [Matrix.toLin'_mul, Matrix.toLin'_toMatrix', Matrix.toLin'_toMatrix',
       Matrix.toLin'_one]
     exact rckSD_extMap_comp hε γ,
   by
     apply Matrix.toLin'.injective
     rw [Matrix.toLin'_mul, Matrix.toLin'_toMatrix', Matrix.toLin'_toMatrix',
       Matrix.toLin'_one]
     exact rckSD_extMap_comp_symm hε γ⟩

private lemma rckSD_unit_apply (hε : IsPrimAdjIdemIn (PSUσ g).toRingHom
      (Unitary.antidiag n)
      (Algebra.adjoin (PSUF g) (Units.val '' ({s} : Set (GL (Fin n) (PSUF g))))) ε)
    (γ : rckSD_W ε ≃ₗ[K] rckSD_W ε) {w : Fin n → PSUF g} (hw : w ∈ rckSD_W ε) :
    Matrix.mulVec (rckSD_unit hε γ : Matrix (Fin n) (Fin n) (PSUF g)) w =
      (γ ⟨w, hw⟩ : Fin n → PSUF g) := by
  have hεw : Matrix.mulVec ε w = w := rckSD_eps_mulVec_of_mem hε hw
  rw [show Matrix.mulVec (rckSD_unit hε γ : Matrix (Fin n) (Fin n) (PSUF g)) w =
      rckSD_extMap (ε := ε) γ w from LinearMap.toMatrix'_mulVec _ _,
    rckSD_extMap_apply, hεw, show rckSD_epsV (ε := ε) w = ⟨w, hw⟩ from Subtype.ext hεw,
    sub_self, add_zero]

private lemma rckSD_unit_fix (hε : IsPrimAdjIdemIn (PSUσ g).toRingHom
      (Unitary.antidiag n)
      (Algebra.adjoin (PSUF g) (Units.val '' ({s} : Set (GL (Fin n) (PSUF g))))) ε)
    (γ : rckSD_W ε ≃ₗ[K] rckSD_W ε) :
    (rckSD_unit hε γ : Matrix (Fin n) (Fin n) (PSUF g)) * (1 - ε) = 1 - ε := by
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro v
  change Matrix.mulVec ((rckSD_unit hε γ : Matrix (Fin n) (Fin n) (PSUF g)) * (1 - ε)) v =
    Matrix.mulVec (1 - ε) v
  rw [← Matrix.mulVec_mulVec]
  rw [show Matrix.mulVec (rckSD_unit hε γ : Matrix (Fin n) (Fin n) (PSUF g))
      (Matrix.mulVec (1 - ε) v) =
      rckSD_extMap (ε := ε) γ (Matrix.mulVec (1 - ε) v) from
    LinearMap.toMatrix'_mulVec _ _]
  exact rckSD_extMap_apply_one_sub hε γ v

private lemma rckSD_unit_mem_centralizer (hε : IsPrimAdjIdemIn (PSUσ g).toRingHom
      (Unitary.antidiag n)
      (Algebra.adjoin (PSUF g) (Units.val '' ({s} : Set (GL (Fin n) (PSUF g))))) ε)
    (hπ : RCKBlockCoord {s} ε K π) (γ : rckSD_W ε ≃ₗ[K] rckSD_W ε) :
    rckSD_unit hε γ ∈ Subgroup.centralizer ({s} : Set (GL (Fin n) (PSUF g))) := by
  rw [Subgroup.mem_centralizer_iff]
  intro t ht
  rw [Set.mem_singleton_iff] at ht
  rw [ht]
  apply Units.ext
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro v
  change Matrix.mulVec ((s : GL (Fin n) (PSUF g)) * rckSD_unit hε γ :
      Matrix (Fin n) (Fin n) (PSUF g)) v =
    Matrix.mulVec (rckSD_unit hε γ * s : Matrix (Fin n) (Fin n) (PSUF g)) v
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  rw [show Matrix.mulVec (rckSD_unit hε γ : Matrix (Fin n) (Fin n) (PSUF g)) v =
      rckSD_extMap (ε := ε) γ v from LinearMap.toMatrix'_mulVec _ _,
    show Matrix.mulVec (rckSD_unit hε γ : Matrix (Fin n) (Fin n) (PSUF g))
        (Matrix.mulVec (s : Matrix (Fin n) (Fin n) (PSUF g)) v) =
      rckSD_extMap (ε := ε) γ (Matrix.mulVec (s : Matrix (Fin n) (Fin n) (PSUF g)) v)
        from LinearMap.toMatrix'_mulVec _ _]
  exact (rckSD_extMap_smul_s hε hπ γ v).symm

private lemma rckSD_gPSU_h_orth (hε : IsPrimAdjIdemIn (PSUσ g).toRingHom
      (Unitary.antidiag n)
      (Algebra.adjoin (PSUF g) (Units.val '' ({s} : Set (GL (Fin n) (PSUF g))))) ε)
    (u : Fin n → PSUF g) (hu : u ∈ rckSD_W ε) (v : Fin n → PSUF g) :
    gPSU_h (PSUσ g).toRingHom (Unitary.antidiag n) u
      (v - Matrix.mulVec ε v) = 0 := by
  have h := gPSU_h_adjoint (PSUσ g).toRingHom (Unitary.antidiag n) ε
    (PSUantidiag_isUnit_det n g) u (v - Matrix.mulVec ε v)
  rw [rckSD_eps_mulVec_of_mem hε hu, hε.2.2.2.1] at h
  have hzero : Matrix.mulVec ε (v - Matrix.mulVec ε v) = 0 := by
    rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, hε.2.1.eq, sub_self]
  rw [h, hzero]
  simp [gPSU_h]

private lemma rckSD_gPSU_h_orth' (hε : IsPrimAdjIdemIn (PSUσ g).toRingHom
      (Unitary.antidiag n)
      (Algebra.adjoin (PSUF g) (Units.val '' ({s} : Set (GL (Fin n) (PSUF g))))) ε)
    (u : Fin n → PSUF g) (hu : u ∈ rckSD_W ε) (v : Fin n → PSUF g) :
    gPSU_h (PSUσ g).toRingHom (Unitary.antidiag n)
      (v - Matrix.mulVec ε v) u = 0 := by
  rw [gPSU_h_herm (PSUσ g).toRingHom (PSUσ_involutive g) u (v - Matrix.mulVec ε v),
    rckSD_gPSU_h_orth hε u hu v, map_zero]

private lemma rckSD_hForm_γ
    (hB : ∀ x y : rckSD_W ε,
      uForm (PSUσ g) (x : Fin n → PSUF g) (y : Fin n → PSUF g) =
        Algebra.trace (PSUF g) K (B x y))
    (γ : rckSD_W ε ≃ₗ[K] rckSD_W ε)
    (hγ : ∀ x y : rckSD_W ε, B (γ x) (γ y) = B x y) (u v : rckSD_W ε) :
    gPSU_h (PSUσ g).toRingHom (Unitary.antidiag n)
        (γ u : Fin n → PSUF g) (γ v : Fin n → PSUF g) =
      gPSU_h (PSUσ g).toRingHom (Unitary.antidiag n)
        (u : Fin n → PSUF g) (v : Fin n → PSUF g) := by
  have hh := (CFSG.LieType.SemisimpleCentralizers.HeldUCD.unitary_trace_iff
    (L := PSUF g) (K := K) (W := rckSD_W ε) (rckSD_hForm (ε := ε)) B
    (fun x y => rckSD_hForm_trace hB x y)
    (γ : rckSD_W ε →ₗ[K] rckSD_W ε)).mpr hγ
  exact hh u v

private lemma rckSD_extMap_form (hε : IsPrimAdjIdemIn (PSUσ g).toRingHom
      (Unitary.antidiag n)
      (Algebra.adjoin (PSUF g) (Units.val '' ({s} : Set (GL (Fin n) (PSUF g))))) ε)
    (hB : ∀ x y : rckSD_W ε,
      uForm (PSUσ g) (x : Fin n → PSUF g) (y : Fin n → PSUF g) =
        Algebra.trace (PSUF g) K (B x y))
    (γ : rckSD_W ε ≃ₗ[K] rckSD_W ε)
    (hγ : ∀ x y : rckSD_W ε, B (γ x) (γ y) = B x y)
    (x y : Fin n → PSUF g) :
    gPSU_h (PSUσ g).toRingHom (Unitary.antidiag n)
      (rckSD_extMap (ε := ε) γ x) (rckSD_extMap (ε := ε) γ y) =
    gPSU_h (PSUσ g).toRingHom (Unitary.antidiag n) x y := by
  have hxsplit : x = Matrix.mulVec ε x + Matrix.mulVec (1 - ε) x := by
    rw [← Matrix.add_mulVec, add_sub_cancel, Matrix.one_mulVec]
  have hysplit : y = Matrix.mulVec ε y + Matrix.mulVec (1 - ε) y := by
    rw [← Matrix.add_mulVec, add_sub_cancel, Matrix.one_mulVec]
  have hxy : gPSU_h (PSUσ g).toRingHom (Unitary.antidiag n) x y =
      gPSU_h (PSUσ g).toRingHom (Unitary.antidiag n)
          (Matrix.mulVec ε x) (Matrix.mulVec ε y) +
        gPSU_h (PSUσ g).toRingHom (Unitary.antidiag n)
          (x - Matrix.mulVec ε x) (y - Matrix.mulVec ε y) := by
    conv_lhs => rw [hxsplit, hysplit]
    rw [gPSU_h_add_left, gPSU_h_add_right, gPSU_h_add_right]
    simp only [Matrix.sub_mulVec, Matrix.one_mulVec]
    rw [rckSD_gPSU_h_orth hε (Matrix.mulVec ε x) ⟨x, rfl⟩ y,
      rckSD_gPSU_h_orth' hε (Matrix.mulVec ε y) ⟨y, rfl⟩ x]
    abel
  rw [rckSD_extMap_apply, rckSD_extMap_apply,
    gPSU_h_add_left, gPSU_h_add_right, gPSU_h_add_right,
    rckSD_hForm_γ hB γ hγ (rckSD_epsV (ε := ε) x) (rckSD_epsV (ε := ε) y),
    rckSD_gPSU_h_orth hε (γ (rckSD_epsV (ε := ε) x) : Fin n → PSUF g) (γ (rckSD_epsV (ε := ε) x)).2 y,
    rckSD_gPSU_h_orth' hε (γ (rckSD_epsV (ε := ε) y) : Fin n → PSUF g) (γ (rckSD_epsV (ε := ε) y)).2 x,
    hxy]
  simp only [add_zero, zero_add]
  rfl

private lemma rckSD_unit_mem_GU (hε : IsPrimAdjIdemIn (PSUσ g).toRingHom
      (Unitary.antidiag n)
      (Algebra.adjoin (PSUF g) (Units.val '' ({s} : Set (GL (Fin n) (PSUF g))))) ε)
    (hB : ∀ x y : rckSD_W ε,
      uForm (PSUσ g) (x : Fin n → PSUF g) (y : Fin n → PSUF g) =
        Algebra.trace (PSUF g) K (B x y))
    (γ : rckSD_W ε ≃ₗ[K] rckSD_W ε)
    (hγ : ∀ x y : rckSD_W ε, B (γ x) (γ y) = B x y) :
    rckSD_unit hε γ ∈ GUsub (PSUσ g) n := by
  rw [mem_GUsub_iff]
  refine gPSU_conjTr_mul_eq_of_forall (PSUσ g).toRingHom (Unitary.antidiag n)
    (rckSD_unit hε γ : Matrix (Fin n) (Fin n) (PSUF g)) ?_
  intro u v
  rw [show Matrix.mulVec (rckSD_unit hε γ : Matrix (Fin n) (Fin n) (PSUF g)) u =
        rckSD_extMap (ε := ε) γ u from LinearMap.toMatrix'_mulVec _ _,
    show Matrix.mulVec (rckSD_unit hε γ : Matrix (Fin n) (Fin n) (PSUF g)) v =
        rckSD_extMap (ε := ε) γ v from LinearMap.toMatrix'_mulVec _ _]
  simpa only [gPSU_h, ← Matrix.dotProduct_mulVec] using
    rckSD_extMap_form hε hB γ hγ u v

private noncomputable def rckSD_hom (hε : IsPrimAdjIdemIn (PSUσ g).toRingHom
      (Unitary.antidiag n)
      (Algebra.adjoin (PSUF g) (Units.val '' ({s} : Set (GL (Fin n) (PSUF g))))) ε)
    (hπ : RCKBlockCoord {s} ε K π)
    (hB : ∀ x y : rckSD_W ε,
      uForm (PSUσ g) (x : Fin n → PSUF g) (y : Fin n → PSUF g) =
        Algebra.trace (PSUF g) K (B x y)) :
    ↥(rckSD_G (s := s) ε) →* ↥(sesqUnitaryGroup B) where
  toFun x := ⟨LinearMap.GeneralLinearGroup.ofLinearEquiv (rckSD_rEquiv hε hπ x),
    rckSD_mem_sesq hε hπ hB x⟩
  map_one' := by
    apply Subtype.ext
    apply Units.ext
    apply LinearMap.ext
    intro w
    apply Subtype.ext
    change Matrix.mulVec (((1 : rckSD_G (s := s) ε).1) : Matrix (Fin n) (Fin n) (PSUF g))
      (w : Fin n → PSUF g) = (w : Fin n → PSUF g)
    simp [rckSD_rMap]
  map_mul' x y := by
    apply Subtype.ext
    apply Units.ext
    apply LinearMap.ext
    intro w
    apply Subtype.ext
    change Matrix.mulVec (((x * y : rckSD_G (s := s) ε).1) : Matrix (Fin n) (Fin n) (PSUF g))
        (w : Fin n → PSUF g) =
      Matrix.mulVec ((x.1 : Matrix (Fin n) (Fin n) (PSUF g)))
        (Matrix.mulVec ((y.1 : Matrix (Fin n) (Fin n) (PSUF g))) (w : Fin n → PSUF g))
    rw [show (((x * y : rckSD_G (s := s) ε).1) : GL (Fin n) (PSUF g)) =
        (x : GL (Fin n) (PSUF g)) * (y : GL (Fin n) (PSUF g)) from rfl,
      Units.val_mul, Matrix.mulVec_mulVec]

private lemma rckSD_hom_injective (hε : IsPrimAdjIdemIn (PSUσ g).toRingHom
      (Unitary.antidiag n)
      (Algebra.adjoin (PSUF g) (Units.val '' ({s} : Set (GL (Fin n) (PSUF g))))) ε)
    (hπ : RCKBlockCoord {s} ε K π)
    (hB : ∀ x y : rckSD_W ε,
      uForm (PSUσ g) (x : Fin n → PSUF g) (y : Fin n → PSUF g) =
        Algebra.trace (PSUF g) K (B x y)) :
    Function.Injective (rckSD_hom hε hπ hB) := by
  intro x y hxy
  apply Subtype.ext
  apply Units.ext
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro v
  have hGL : LinearMap.GeneralLinearGroup.ofLinearEquiv (rckSD_rEquiv hε hπ x) =
      LinearMap.GeneralLinearGroup.ofLinearEquiv (rckSD_rEquiv hε hπ y) :=
    congrArg Subtype.val hxy
  have hfun : (LinearMap.GeneralLinearGroup.ofLinearEquiv (rckSD_rEquiv hε hπ x) :
        rckSD_W ε → rckSD_W ε) =
      (LinearMap.GeneralLinearGroup.ofLinearEquiv (rckSD_rEquiv hε hπ y) :
        rckSD_W ε → rckSD_W ε) :=
    congrArg (fun g : LinearMap.GeneralLinearGroup K (rckSD_W ε) =>
      (g : rckSD_W ε → rckSD_W ε)) hGL
  have hmap : ∀ w : rckSD_W ε,
      (rckSD_rEquiv hε hπ x : rckSD_W ε →ₗ[K] rckSD_W ε) w =
        (rckSD_rEquiv hε hπ y : rckSD_W ε →ₗ[K] rckSD_W ε) w := by
    intro w
    simpa using congrFun hfun w
  have hxfix : (x.1 : Matrix (Fin n) (Fin n) (PSUF g)) * (1 - ε) = 1 - ε :=
    (rckSD_mem_G_iff.mp x.2).2.1
  have hyfix : (y.1 : Matrix (Fin n) (Fin n) (PSUF g)) * (1 - ε) = 1 - ε :=
    (rckSD_mem_G_iff.mp y.2).2.1
  have hv : v = Matrix.mulVec ε v + Matrix.mulVec (1 - ε) v := by
    rw [← Matrix.add_mulVec, add_sub_cancel, Matrix.one_mulVec]
  have hx1 : Matrix.mulVec (x.1 : Matrix (Fin n) (Fin n) (PSUF g))
      (Matrix.mulVec (1 - ε) v) = Matrix.mulVec (1 - ε) v := by
    rw [Matrix.mulVec_mulVec, hxfix]
  have hy1 : Matrix.mulVec (y.1 : Matrix (Fin n) (Fin n) (PSUF g))
      (Matrix.mulVec (1 - ε) v) = Matrix.mulVec (1 - ε) v := by
    rw [Matrix.mulVec_mulVec, hyfix]
  have hmapMat : Matrix.mulVec (x.1 : Matrix (Fin n) (Fin n) (PSUF g))
      (Matrix.mulVec ε v) =
      Matrix.mulVec (y.1 : Matrix (Fin n) (Fin n) (PSUF g)) (Matrix.mulVec ε v) := by
    simpa [rckSD_rEquiv, rckSD_rMap] using
      congrArg Subtype.val (hmap ⟨Matrix.mulVec ε v, ⟨v, rfl⟩⟩)
  calc Matrix.mulVec (x.1 : Matrix (Fin n) (Fin n) (PSUF g)) v
      = Matrix.mulVec (x.1 : Matrix (Fin n) (Fin n) (PSUF g)) (Matrix.mulVec ε v) +
          Matrix.mulVec (1 - ε) v := by
        conv_lhs => rw [hv]
        rw [Matrix.mulVec_add, hx1]
    _ = Matrix.mulVec (y.1 : Matrix (Fin n) (Fin n) (PSUF g)) (Matrix.mulVec ε v) +
          Matrix.mulVec (1 - ε) v := by rw [hmapMat]
    _ = Matrix.mulVec (y.1 : Matrix (Fin n) (Fin n) (PSUF g)) v := by
        conv_rhs => rw [hv]
        rw [Matrix.mulVec_add, hy1]

private lemma rckSD_hom_surjective (hε : IsPrimAdjIdemIn (PSUσ g).toRingHom
      (Unitary.antidiag n)
      (Algebra.adjoin (PSUF g) (Units.val '' ({s} : Set (GL (Fin n) (PSUF g))))) ε)
    (hπ : RCKBlockCoord {s} ε K π)
    (hB : ∀ x y : rckSD_W ε,
      uForm (PSUσ g) (x : Fin n → PSUF g) (y : Fin n → PSUF g) =
        Algebra.trace (PSUF g) K (B x y)) :
    Function.Surjective (rckSD_hom hε hπ hB) := by
  intro γ
  let γe : rckSD_W ε ≃ₗ[K] rckSD_W ε :=
    LinearMap.GeneralLinearGroup.toLinearEquiv γ.1
  have hγ : ∀ x y : rckSD_W ε, B (γe x) (γe y) = B x y := by
    simpa [γe, LinearMap.GeneralLinearGroup.coe_toLinearEquiv] using
      (mem_sesqUnitaryGroup.mp γ.2)
  let U : GL (Fin n) (PSUF g) := rckSD_unit hε γe
  have hUcen : U ∈ Subgroup.centralizer ({s} : Set (GL (Fin n) (PSUF g))) :=
    rckSD_unit_mem_centralizer hε hπ γe
  have hUfix : U ∈ glFixing (1 - ε) := rckSD_unit_fix hε γe
  have hUGU : U ∈ GUsub (PSUσ g) n := rckSD_unit_mem_GU hε hB γe hγ
  refine ⟨⟨U, ?_⟩, ?_⟩
  · rw [rckSD_mem_G_iff]
    exact ⟨hUcen, hUfix, hUGU⟩
  · apply Subtype.ext
    apply Units.ext
    apply LinearMap.ext
    intro w
    apply Subtype.ext
    change Matrix.mulVec (U : Matrix (Fin n) (Fin n) (PSUF g)) (w : Fin n → PSUF g) =
      (γe w : Fin n → PSUF g)
    exact rckSD_unit_apply hε γe w.2

end Aux

theorem rckSD_blockEquiv {n g : ℕ} {s : GL (Fin n) (PSUF g)}
    {ε : Matrix (Fin n) (Fin n) (PSUF g)}
    (hε : IsPrimAdjIdemIn (PSUσ g).toRingHom (Unitary.antidiag n)
      (Algebra.adjoin (PSUF g) (Units.val '' ({s} : Set (GL (Fin n) (PSUF g))))) ε)
    {K : Type} [Field K] [Finite K] [Algebra (PSUF g) K]
    [Module K (LinearMap.range (Matrix.mulVecLin ε))]
    [IsScalarTower (PSUF g) K (LinearMap.range (Matrix.mulVecLin ε))]
    {π : Algebra.adjoin (PSUF g) (Units.val '' ({s} : Set (GL (Fin n) (PSUF g)))) →ₐ[PSUF g] K}
    (hπ : RCKBlockCoord {s} ε K π) {ρ : K ≃+* K}
    {B : LinearMap.range (Matrix.mulVecLin ε) →ₛₗ[(ρ : K →+* K)]
        LinearMap.range (Matrix.mulVecLin ε) →ₗ[K] K}
    (hB : ∀ x y : LinearMap.range (Matrix.mulVecLin ε),
        CFSG.Timmesfeld.LieEmbed.uForm (PSUσ g) (x : Fin n → PSUF g) (y : Fin n → PSUF g) =
          Algebra.trace (PSUF g) K (B x y)) :
    Nonempty (↥(Subgroup.centralizer ({s} : Set (GL (Fin n) (PSUF g))) ⊓ glFixing (1 - ε) ⊓
        GUsub (PSUσ g) n) ≃* ↥(sesqUnitaryGroup B)) := by
  exact ⟨MulEquiv.ofBijective (rckSD_hom hε hπ hB)
    ⟨rckSD_hom_injective hε hπ hB, rckSD_hom_surjective hε hπ hB⟩⟩

end CFSG.StandardType.RCKRP
