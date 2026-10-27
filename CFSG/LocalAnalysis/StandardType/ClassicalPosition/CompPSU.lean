module

public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.Defs
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.BlockDecomp
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.CompCore
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.GeoAdj
public import CFSG.LieType.Universal.Unitary.Extras
public import CFSG.LieType.Universal.Unitary.Comparison
public import CFSG.LieType.BorelTits.UnitaryForm

public section

namespace CFSG.StandardType.ClassicalPosition

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.StandardType

private lemma cpU_idem_mul_one_sub {F : Type} [Field F] {n : ℕ}
    {e : Matrix (Fin n) (Fin n) F} (h : IsIdempotentElem e) : e * (1 - e) = 0 :=
  h.mul_one_sub_self

private lemma cpU_one_sub_mul_idem {F : Type} [Field F] {n : ℕ}
    {e : Matrix (Fin n) (Fin n) F} (h : IsIdempotentElem e) : (1 - e) * e = 0 :=
  h.one_sub_mul_self

private lemma cpU_one_sub_mul_one_sub {F : Type} [Field F] {n : ℕ}
    {e : Matrix (Fin n) (Fin n) F} (h : IsIdempotentElem e) : (1 - e) * (1 - e) = 1 - e :=
  (IsIdempotentElem.one_sub_iff.mpr h).eq

private lemma cpU_inv_comm_of_comm {F : Type} [Field F] {n : ℕ} (u : GL (Fin n) F)
    (e : Matrix (Fin n) (Fin n) F)
    (hcomm : (u : Matrix (Fin n) (Fin n) F) * e = e * (u : Matrix (Fin n) (Fin n) F)) :
    e * (((u⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) =
      (((u⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) * e := by
  have hnm : ((u⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
      (u : Matrix (Fin n) (Fin n) F) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hmn : (u : Matrix (Fin n) (Fin n) F) *
      ((u⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have h1 : e = ((u⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
      (e * (u : Matrix (Fin n) (Fin n) F)) := by
    calc e = 1 * e := (Matrix.one_mul e).symm
      _ = (((u⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
            (u : Matrix (Fin n) (Fin n) F)) * e := by rw [hnm]
      _ = ((u⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
            ((u : Matrix (Fin n) (Fin n) F) * e) := Matrix.mul_assoc _ _ _
      _ = ((u⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
            (e * (u : Matrix (Fin n) (Fin n) F)) := by rw [hcomm]
  calc e * (((u⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F))
      = (((u⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
          (e * (u : Matrix (Fin n) (Fin n) F))) *
          (((u⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) := by
          conv_lhs => rw [h1]
    _ = ((u⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * e *
          ((u : Matrix (Fin n) (Fin n) F) *
            ((u⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) := by
          simp only [Matrix.mul_assoc]
    _ = ((u⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * e := by
          rw [hmn, Matrix.mul_one]

private lemma cpU_blk_mul_aux {F : Type} [Field F] {n : ℕ}
    (a b e : Matrix (Fin n) (Fin n) F) (hid : IsIdempotentElem e)
    (hmn : a * b = 1) (hne : e * b = b * e)
    (hqn : (1 - e) * b = b * (1 - e)) :
    (a * e + (1 - e)) * (b * e + (1 - e)) = 1 := by
  have ht1 : (a * e) * (b * e) = e := by
    calc (a * e) * (b * e) = a * (e * (b * e)) := Matrix.mul_assoc a e (b * e)
      _ = a * ((e * b) * e) := by rw [← Matrix.mul_assoc e b e]
      _ = a * ((b * e) * e) := by rw [hne]
      _ = a * (b * (e * e)) := by rw [Matrix.mul_assoc b e e]
      _ = a * (b * e) := by rw [hid]
      _ = (a * b) * e := by rw [← Matrix.mul_assoc a b e]
      _ = e := by rw [hmn, Matrix.one_mul]
  have ht2 : (a * e) * (1 - e) = 0 := by
    calc (a * e) * (1 - e) = a * (e * (1 - e)) := Matrix.mul_assoc a e (1 - e)
      _ = 0 := by rw [cpU_idem_mul_one_sub hid, Matrix.mul_zero]
  have ht3 : (1 - e) * (b * e) = 0 := by
    calc (1 - e) * (b * e) = ((1 - e) * b) * e := (Matrix.mul_assoc (1 - e) b e).symm
      _ = (b * (1 - e)) * e := by rw [hqn]
      _ = b * ((1 - e) * e) := Matrix.mul_assoc b (1 - e) e
      _ = 0 := by rw [cpU_one_sub_mul_idem hid, Matrix.mul_zero]
  have ht4 : (1 - e) * (1 - e) = 1 - e := cpU_one_sub_mul_one_sub hid
  have hexp : (a * e + (1 - e)) * (b * e + (1 - e)) =
      (a * e) * (b * e) + (a * e) * (1 - e) + (1 - e) * (b * e) + (1 - e) * (1 - e) := by
    noncomm_ring
  rw [hexp, ht1, ht2, ht3, ht4]
  abel

private noncomputable def cpU_blk {F : Type} [Field F] {n : ℕ} (u : GL (Fin n) F)
    (e : Matrix (Fin n) (Fin n) F)
    (hcomm : (u : Matrix (Fin n) (Fin n) F) * e = e * (u : Matrix (Fin n) (Fin n) F))
    (hid : IsIdempotentElem e) : GL (Fin n) F :=
  Units.mk ((u : Matrix (Fin n) (Fin n) F) * e + (1 - e))
    (((u⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * e + (1 - e))
    (by
      have huinvcomm := cpU_inv_comm_of_comm u e hcomm
      have hmn : (u : Matrix (Fin n) (Fin n) F) *
          ((u⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = 1 := by
        rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
      have hqn : (1 - e) * ((u⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
          ((u⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * (1 - e) := by
        rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one, huinvcomm]
      exact cpU_blk_mul_aux (u : Matrix (Fin n) (Fin n) F)
        (((u⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) e hid hmn
        huinvcomm hqn)
    (by
      have hnm : ((u⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
          (u : Matrix (Fin n) (Fin n) F) = 1 := by
        rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
      have hqm : (1 - e) * (u : Matrix (Fin n) (Fin n) F) =
          (u : Matrix (Fin n) (Fin n) F) * (1 - e) := by
        rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one, ← hcomm]
      exact cpU_blk_mul_aux (((u⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F))
        (u : Matrix (Fin n) (Fin n) F) e hid hnm hcomm.symm hqm)

private def cpU_IsUni {F : Type} [Field F] {n : ℕ} (σ : F →+* F)
    (G : Matrix (Fin n) (Fin n) F) (g : GL (Fin n) F) : Prop :=
  Matrix.transpose ((g : Matrix (Fin n) (Fin n) F).map σ) * G * (g : Matrix (Fin n) (Fin n) F) = G

private lemma cpU_map_transpose_mul {F : Type} [Field F] {n : ℕ} (σ : F →+* F)
    (a b : Matrix (Fin n) (Fin n) F) :
    Matrix.transpose ((a * b).map σ) = Matrix.transpose (b.map σ) * Matrix.transpose (a.map σ) := by
  rw [Matrix.map_mul, Matrix.transpose_mul]

private lemma cpU_map_transpose_one {F : Type} [Field F] {n : ℕ} (σ : F →+* F) :
    Matrix.transpose ((1 : Matrix (Fin n) (Fin n) F).map σ) = 1 := by
  rw [Matrix.map_one σ (map_zero σ) (map_one σ), Matrix.transpose_one]

private lemma cpU_isUni_mul {F : Type} [Field F] {σ : F →+* F} {n : ℕ}
    {G : Matrix (Fin n) (Fin n) F} {a b : GL (Fin n) F}
    (ha : cpU_IsUni σ G a) (hb : cpU_IsUni σ G b) : cpU_IsUni σ G (a * b) := by
  change Matrix.transpose (((a * b : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).map σ) * G *
      ((a * b : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = G
  rw [Units.val_mul, cpU_map_transpose_mul]
  calc Matrix.transpose ((b : Matrix (Fin n) (Fin n) F).map σ) *
        Matrix.transpose ((a : Matrix (Fin n) (Fin n) F).map σ) * G *
        ((a : Matrix (Fin n) (Fin n) F) * (b : Matrix (Fin n) (Fin n) F))
      = Matrix.transpose ((b : Matrix (Fin n) (Fin n) F).map σ) *
          (Matrix.transpose ((a : Matrix (Fin n) (Fin n) F).map σ) * G *
            (a : Matrix (Fin n) (Fin n) F)) * (b : Matrix (Fin n) (Fin n) F) := by
          simp only [Matrix.mul_assoc]
    _ = Matrix.transpose ((b : Matrix (Fin n) (Fin n) F).map σ) * G *
          (b : Matrix (Fin n) (Fin n) F) := by rw [ha]
    _ = G := hb

private lemma cpU_isUni_inv {F : Type} [Field F] {σ : F →+* F} {n : ℕ}
    {G : Matrix (Fin n) (Fin n) F} {a : GL (Fin n) F} (ha : cpU_IsUni σ G a) :
    cpU_IsUni σ G a⁻¹ := by
  change Matrix.transpose (((a⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).map σ) * G *
      ((a⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = G
  have hA'A : Matrix.transpose (((a⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).map σ) *
      Matrix.transpose ((a : Matrix (Fin n) (Fin n) F).map σ) = 1 := by
    rw [← cpU_map_transpose_mul]
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one, cpU_map_transpose_one]
  have hBB' : (a : Matrix (Fin n) (Fin n) F) *
      ((a⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  calc Matrix.transpose (((a⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).map σ) * G *
        ((a⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)
      = Matrix.transpose (((a⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).map σ) *
          (Matrix.transpose ((a : Matrix (Fin n) (Fin n) F).map σ) * G *
            (a : Matrix (Fin n) (Fin n) F)) *
          ((a⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := by rw [ha]
    _ = (Matrix.transpose (((a⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).map σ) *
          Matrix.transpose ((a : Matrix (Fin n) (Fin n) F).map σ)) * G *
          ((a : Matrix (Fin n) (Fin n) F) * ((a⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) := by
          simp only [Matrix.mul_assoc]
    _ = G := by rw [hA'A, hBB', Matrix.one_mul, Matrix.mul_one]

private lemma cpU_isUni_commutator {F : Type} [Field F] {σ : F →+* F} {n : ℕ}
    {G : Matrix (Fin n) (Fin n) F} {X Y : GL (Fin n) F}
    (hX : cpU_IsUni σ G X) (hY : cpU_IsUni σ G Y) :
    cpU_IsUni σ G (Y * X * Y⁻¹ * X⁻¹) :=
  cpU_isUni_mul (cpU_isUni_mul (cpU_isUni_mul hY hX) (cpU_isUni_inv hY))
    (cpU_isUni_inv hX)

private lemma cpU_formAdj_one_sub {F : Type} [Field F] {n : ℕ} (σ : F →+* F)
    {G : Matrix (Fin n) (Fin n) F} (hG : IsUnit G.det) {e : Matrix (Fin n) (Fin n) F}
    (he : formAdj σ G e = e) : formAdj σ G (1 - e) = 1 - e := by
  have h : (1 : Matrix (Fin n) (Fin n) F) - e = 1 + (-1 : F) • e := by
    rw [neg_one_smul, sub_eq_add_neg]
  conv_lhs => rw [h]
  rw [Geo.formAdj_add, Geo.formAdj_one σ hG, Geo.formAdj_smul, he]
  simp [sub_eq_add_neg]

private lemma cpU_isUni_of_formAdj_inv {F : Type} [Field F] {n : ℕ} (σ : F →+* F)
    {G : Matrix (Fin n) (Fin n) F} (hG : IsUnit G.det) {g : GL (Fin n) F}
    (hform : formAdj σ G (g : Matrix (Fin n) (Fin n) F) =
      ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) :
    cpU_IsUni σ G g := by
  have hba : ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
      (g : Matrix (Fin n) (Fin n) F) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have h1 : Matrix.transpose ((g : Matrix (Fin n) (Fin n) F).map σ) * G =
      G * ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := by
    have h := congrArg (fun x => G * x) hform
    simp only [formAdj] at h
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv G hG,
      Matrix.one_mul] at h
    exact h
  change Matrix.transpose ((g : Matrix (Fin n) (Fin n) F).map σ) * G *
      (g : Matrix (Fin n) (Fin n) F) = G
  calc Matrix.transpose ((g : Matrix (Fin n) (Fin n) F).map σ) * G *
        (g : Matrix (Fin n) (Fin n) F)
      = (G * ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) *
          (g : Matrix (Fin n) (Fin n) F) := by rw [h1]
    _ = G * (((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
          (g : Matrix (Fin n) (Fin n) F)) := by rw [Matrix.mul_assoc]
    _ = G := by rw [hba, Matrix.mul_one]

theorem exists_isComponentOf_glBlockCentralizer_PSU {F : Type} [Field F] [Finite F] [CharP F 2]
    {f : ℕ} (n : ℕ) (S : Set (GL (Fin n) F))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {J' : Subgroup ↥(Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n)}
    (hJ : IsComponentOf J'
    ((Subgroup.centralizer S).comap
    (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype)) :
    ∃ ε, IsPrimAdjIdemIn (CFSG.LieType.BorelTits.unitaryInvolution F 2 f).toRingHom
      (Unitary.antidiag n) (Algebra.adjoin F (Units.val '' S)) ε ∧
      IsComponentOf J'
        ⁅glBlockCentralizer (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype
        S ε, glBlockCentralizer
        (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε⁆ := by
  let σe : F ≃+* F := CFSG.LieType.BorelTits.unitaryInvolution F 2 f
  let σ : F →+* F := σe.toRingHom
  let G : Matrix (Fin n) (Fin n) F := Unitary.antidiag n
  have hG : IsUnit G.det := by
    rw [isUnit_iff_ne_zero]
    simpa [G] using Unitary.det_antidiag_ne_zero (F := F) n
  obtain ⟨ε, hprim, hcomp⟩ :=
    Block.exists_isPrimStarIdemIn_isComponentOf_glBlockCentralizer
      (Unitary.SU σe n).subtype (Subgroup.subtype_injective _) S hS (formAdj σ G)
      (Geo.formAdj_one σ hG)
      (fun a _ b _ => Geo.formAdj_add σ G a b)
      (by
        intro ε hε hid hst x hx y hy
        have hxcen : ∀ a ∈ Algebra.adjoin F (Units.val '' S),
            a * ((x : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
              ((x : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * a := by
          intro a ha
          refine Algebra.adjoin_induction
            (p := fun a _ => a * ((x : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
              ((x : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * a) ?_ ?_ ?_ ?_ ha
          · rintro _ ⟨s, hs, rfl⟩
            exact congrArg (fun u : GL (Fin n) F => (u : Matrix (Fin n) (Fin n) F))
              (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_comap.mp hx) s hs)
          · intro r
            rw [Algebra.algebraMap_eq_smul_one, Matrix.smul_mul, Matrix.mul_smul,
              Matrix.one_mul, Matrix.mul_one]
          · intro b c hb hc hpb hpc
            rw [Matrix.add_mul, Matrix.mul_add, hpb, hpc]
          · intro b c hb hc hpb hpc
            rw [Matrix.mul_assoc, hpc, ← Matrix.mul_assoc, hpb, Matrix.mul_assoc]
        have hycen : ∀ a ∈ Algebra.adjoin F (Units.val '' S),
            a * ((y : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
              ((y : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * a := by
          intro a ha
          refine Algebra.adjoin_induction
            (p := fun a _ => a * ((y : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
              ((y : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * a) ?_ ?_ ?_ ?_ ha
          · rintro _ ⟨s, hs, rfl⟩
            exact congrArg (fun u : GL (Fin n) F => (u : Matrix (Fin n) (Fin n) F))
              (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_comap.mp hy) s hs)
          · intro r
            rw [Algebra.algebraMap_eq_smul_one, Matrix.smul_mul, Matrix.mul_smul,
              Matrix.one_mul, Matrix.mul_one]
          · intro b c hb hc hpb hpc
            rw [Matrix.add_mul, Matrix.mul_add, hpb, hpc]
          · intro b c hb hc hpb hpc
            rw [Matrix.mul_assoc, hpc, ← Matrix.mul_assoc, hpb, Matrix.mul_assoc]
        have hmx : ((x : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * ε =
            ε * ((x : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := (hxcen ε hε).symm
        have hmy : ((y : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * ε =
            ε * ((y : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := (hycen ε hε).symm
        let X : GL (Fin n) F := cpU_blk (x : GL (Fin n) F) ε hmx hid
        let Y : GL (Fin n) F := cpU_blk (y : GL (Fin n) F) ε hmy hid
        have hXval : ((X : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
            ((x : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * ε + (1 - ε) := rfl
        have hXinv : (((X⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) =
            (((x : GL (Fin n) F)⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * ε +
              (1 - ε) := rfl
        have hYval : ((Y : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
            ((y : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * ε + (1 - ε) := rfl
        have hxSU : (x : GL (Fin n) F) ∈ Unitary.SU σe n := x.2
        have hySU : (y : GL (Fin n) F) ∈ Unitary.SU σe n := y.2
        have hisox : Matrix.transpose (((x : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).map σ) *
            G * ((x : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = G := by
          have h := (Unitary.mem_SU.mp hxSU).2
          simpa [Unitary.conjTr, G, σ] using h
        have hisoy : Matrix.transpose (((y : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).map σ) *
            G * ((y : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = G := by
          have h := (Unitary.mem_SU.mp hySU).2
          simpa [Unitary.conjTr, G, σ] using h
        have hxform : formAdj σ G ((x : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
            (((x : GL (Fin n) F)⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) :=
          Geo.formAdj_eq_inv_of_isometry σ hG (x : GL (Fin n) F) hisox
        have hyform : formAdj σ G ((y : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
            (((y : GL (Fin n) F)⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) :=
          Geo.formAdj_eq_inv_of_isometry σ hG (y : GL (Fin n) F) hisoy
        have h1e : formAdj σ G (1 - ε) = 1 - ε := cpU_formAdj_one_sub σ hG hst
        have hXform : formAdj σ G ((X : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
            (((X⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) := by
          rw [hXval, hXinv, Geo.formAdj_add,
            Geo.formAdj_mul σ hG ((x : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) ε,
            hst, hxform, h1e, cpU_inv_comm_of_comm (x : GL (Fin n) F) ε hmx]
        have hYform : formAdj σ G ((Y : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
            (((Y⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) := by
          rw [hYval, show (((Y⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) =
              (((y : GL (Fin n) F)⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * ε +
                (1 - ε) from rfl, Geo.formAdj_add,
            Geo.formAdj_mul σ hG ((y : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) ε,
            hst, hyform, h1e, cpU_inv_comm_of_comm (y : GL (Fin n) F) ε hmy]
        have hXuni : cpU_IsUni σ G X := cpU_isUni_of_formAdj_inv σ hG hXform
        have hYuni : cpU_IsUni σ G Y := cpU_isUni_of_formAdj_inv σ hG hYform
        let Z : GL (Fin n) F := Y * X * Y⁻¹ * X⁻¹
        have hZuni : cpU_IsUni σ G Z := cpU_isUni_commutator hXuni hYuni
        have hZdet : ((Z : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).det = 1 := by
          have hdetZ : Matrix.GeneralLinearGroup.det (R := F) Z =
              Matrix.GeneralLinearGroup.det (R := F) Y *
                Matrix.GeneralLinearGroup.det (R := F) X *
                (Matrix.GeneralLinearGroup.det (R := F) Y)⁻¹ *
                (Matrix.GeneralLinearGroup.det (R := F) X)⁻¹ := by
            change Matrix.GeneralLinearGroup.det (R := F)
              (Y * X * Y⁻¹ * X⁻¹) = _
            rw [map_mul, map_mul, map_mul, map_inv, map_inv]
          have h2 : Matrix.GeneralLinearGroup.det (R := F) Z = 1 := by
            rw [hdetZ, mul_comm (Matrix.GeneralLinearGroup.det (R := F) Y)]
            group
          simpa using congrArg (fun z : Fˣ => (z : F)) h2
        have hZSU : Z ∈ Unitary.SU σe n := by
          rw [Unitary.mem_SU]
          refine ⟨hZdet, ?_⟩
          simpa [Unitary.conjTr, G, cpU_IsUni, σ] using hZuni
        refine ⟨⟨Z, hZSU⟩, ?_⟩
        have hgrp : Z * (X * Y) = Y * X := by
          change Y * X * Y⁻¹ * X⁻¹ * (X * Y) = Y * X
          group
        have hmat := congrArg (fun g : GL (Fin n) F => (g : Matrix (Fin n) (Fin n) F)) hgrp
        simpa [Units.val_mul, hXval, hYval] using hmat)
      hJ
  exact ⟨ε, (Block.isPrimStarIdemIn_formAdj_iff σ G (Algebra.adjoin F (Units.val '' S)) ε).mp
    hprim, hcomp⟩
end CFSG.StandardType.ClassicalPosition
