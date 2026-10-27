module

public import CFSG.Quasithin.MS93.S46KC2Fin
public import CFSG.Quasithin.MS93.ML3Facts
public import CFSG.Quasithin.Background.G1Basic

public section

open Matrix Matrix.SpecialLinearGroup CFSG.Quasithin.G1
open scoped MatrixGroups

namespace CFSG.Quasithin.MS93.S46.KC2

variable {F : Type} [Field F]

private noncomputable def emb12 : SL(2, F) →* SL3 F :=
  embSL (n := 3) (show (1 : Fin 3) ≠ 2 by decide)

private theorem emb12_transvection {p q : Fin 2} (hpq : p ≠ q) (c : F) :
    emb12 (SpecialLinearGroup.transvection hpq c) =
      rootElt (![(1 : Fin 3), 2] p) (![(1 : Fin 3), 2] q) c := by
  have hne : ![(1 : Fin 3), 2] p ≠ ![(1 : Fin 3), 2] q := by
    fin_cases p <;> fin_cases q <;> simp_all
  apply Subtype.ext
  rw [emb12, embSL_coe]
  change emb 1 2 (Matrix.transvection p q c) = _
  rw [emb_transvection (show (1 : Fin 3) ≠ 2 by decide) p q hpq c, coe_rootElt hne]
  rfl

private theorem emb12_mem {D : Subgroup (SL3 F)} (h12 : ∀ c : F, rootElt 1 2 c ∈ D)
    (h21 : ∀ c : F, rootElt 2 1 c ∈ D) (B : SL(2, F)) : emb12 B ∈ D := by
  refine SL2.transvection_induction (fun B => emb12 B ∈ D) (fun p q hpq c => ?_)
    (fun B C hB hC => by rw [map_mul]; exact D.mul_mem hB hC) B
  rw [emb12_transvection]
  fin_cases p <;> fin_cases q
  · exact absurd rfl hpq
  · exact h12 c
  · exact h21 c
  · exact absurd rfl hpq

theorem mem_of_row_zero {D : Subgroup (SL3 F)} (h10 : ∀ c : F, rootElt 1 0 c ∈ D)
    (h20 : ∀ c : F, rootElt 2 0 c ∈ D) (h12 : ∀ c : F, rootElt 1 2 c ∈ D)
    (h21 : ∀ c : F, rootElt 2 1 c ∈ D) {A : SL3 F}
    (hA : (A : Matrix (Fin 3) (Fin 3) F) 0 = Pi.single 0 1) : A ∈ D := by
  have h00 : (A : Matrix (Fin 3) (Fin 3) F) 0 0 = 1 := by rw [hA]; simp
  have h01 : (A : Matrix (Fin 3) (Fin 3) F) 0 1 = 0 := by rw [hA]; simp
  have h02 : (A : Matrix (Fin 3) (Fin 3) F) 0 2 = 0 := by rw [hA]; simp
  have hdet : (!![(A : Matrix (Fin 3) (Fin 3) F) 1 1, (A : Matrix (Fin 3) (Fin 3) F) 1 2;
      (A : Matrix (Fin 3) (Fin 3) F) 2 1, (A : Matrix (Fin 3) (Fin 3) F) 2 2]).det = 1 := by
    have h := A.2
    rw [Matrix.det_fin_three, h00, h01, h02] at h
    rw [Matrix.det_fin_two_of]
    linear_combination h
  have e : A = rootElt 1 0 ((A : Matrix (Fin 3) (Fin 3) F) 1 0) *
      rootElt 2 0 ((A : Matrix (Fin 3) (Fin 3) F) 2 0) * emb12 ⟨_, hdet⟩ := by
    apply Subtype.ext
    change (A : Matrix (Fin 3) (Fin 3) F) =
      ((rootElt 1 0 ((A : Matrix (Fin 3) (Fin 3) F) 1 0) : SL3 F) : Matrix (Fin 3) (Fin 3) F) *
        ((rootElt 2 0 ((A : Matrix (Fin 3) (Fin 3) F) 2 0) : SL3 F) : Matrix (Fin 3) (Fin 3) F) *
        emb 1 2 !![(A : Matrix (Fin 3) (Fin 3) F) 1 1, (A : Matrix (Fin 3) (Fin 3) F) 1 2;
          (A : Matrix (Fin 3) (Fin 3) F) 2 1, (A : Matrix (Fin 3) (Fin 3) F) 2 2]
    rw [coe_rootElt (show (1 : Fin 3) ≠ 0 by decide), coe_rootElt (show (2 : Fin 3) ≠ 0 by decide)]
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three, emb_apply, blockMap_apply, Matrix.single_apply,
        Matrix.one_apply, Pi.single_apply, h00, h01, h02]
  rw [e]
  exact D.mul_mem (D.mul_mem (h10 _) (h20 _)) (emb12_mem h12 h21 _)

theorem row_mul (A B : SL3 F) (i : Fin 3) :
    ((A * B : SL3 F) : Matrix (Fin 3) (Fin 3) F) i =
      (A : Matrix (Fin 3) (Fin 3) F) i ᵥ* (B : Matrix (Fin 3) (Fin 3) F) := by
  funext j
  simp [Matrix.mul_apply, Matrix.vecMul, dotProduct]

theorem row_one : ((1 : SL3 F) : Matrix (Fin 3) (Fin 3) F) 0 = Pi.single 0 1 := by
  funext j
  rw [coe_one_SL3]
  fin_cases j <;> simp [Matrix.one_apply]

theorem row_mul_inv {A B : SL3 F}
    (h : (A : Matrix (Fin 3) (Fin 3) F) 0 = (B : Matrix (Fin 3) (Fin 3) F) 0) :
    ((A * B⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F) 0 = Pi.single 0 1 := by
  rw [row_mul, h, ← row_mul, mul_inv_cancel, row_one]

theorem row_mul_of_row_eq {E : SL3 F}
    (hE : (E : Matrix (Fin 3) (Fin 3) F) 0 = Pi.single 1 1) (A : SL3 F) :
    ((E * A : SL3 F) : Matrix (Fin 3) (Fin 3) F) 0 = (A : Matrix (Fin 3) (Fin 3) F) 1 := by
  rw [row_mul, hE, single_one_vecMul]
  rfl

theorem row_ne_zero (A : SL3 F) : (A : Matrix (Fin 3) (Fin 3) F) 0 ≠ 0 := by
  intro h
  have h0 : ∀ j, (A : Matrix (Fin 3) (Fin 3) F) 0 j = 0 := fun j => by rw [h]; rfl
  have hd := A.2
  rw [Matrix.det_fin_three, h0 0, h0 1, h0 2] at hd
  simp at hd

section Two

variable [CharP F 2]

@[expose] noncomputable def iota (F : Type) [Field F] [CharP F 2] : ZMod 2 →+* F :=
  ZMod.castHom (dvd_refl 2) F

@[expose] noncomputable def embv (v : Fin 3 → ZMod 2) : Fin 3 → F := iota F ∘ v

theorem embv_injective : Function.Injective (embv (F := F)) := fun _ _ h =>
  funext fun k => (iota F).injective (congrFun h k)

theorem embv_add (u v : Fin 3 → ZMod 2) : embv (F := F) (u + v) = embv u + embv v := by
  funext k
  simp [embv]

theorem embv_zero : embv (F := F) 0 = 0 := by
  funext k
  simp [embv]

@[expose] noncomputable def matF {l m : Fin 3 → ZMod 2} (hl : l ≠ 0) (hm : m ≠ 0) (hlm : l ≠ m) :
    SL3 F :=
  ⟨(iota F).mapMatrix (matN l m), by rw [← RingHom.map_det, det_matN hl hm hlm, map_one]⟩

theorem matF_zero {l m : Fin 3 → ZMod 2} (hl : l ≠ 0) (hm : m ≠ 0) (hlm : l ≠ m) :
    (matF (F := F) hl hm hlm : Matrix (Fin 3) (Fin 3) F) 0 = embv l :=
  rfl

theorem matF_one {l m : Fin 3 → ZMod 2} (hl : l ≠ 0) (hm : m ≠ 0) (hlm : l ≠ m) :
    (matF (F := F) hl hm hlm : Matrix (Fin 3) (Fin 3) F) 1 = embv m :=
  rfl

theorem embv_single (i : Fin 3) : embv (F := F) (Pi.single i 1) = Pi.single i 1 := by
  funext k
  by_cases h : k = i
  · subst h
    simp [embv]
  · simp [embv, h]

theorem exists_embv_eq [Fintype F] (hq : Fintype.card F = 2) (x : Fin 3 → F) :
    ∃ x' : Fin 3 → ZMod 2, embv x' = x := by
  have hb : Function.Bijective (iota F) :=
    (Fintype.bijective_iff_injective_and_card _).mpr ⟨(iota F).injective, by simp [hq]⟩
  choose y hy using hb.2
  exact ⟨fun k => y (x k), funext fun k => hy (x k)⟩

end Two

end CFSG.Quasithin.MS93.S46.KC2
