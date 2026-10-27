module

public import CFSG.Quasithin.H13.A6S13825nc
public import CFSG.Quasithin.Background.IndQuad

public section

namespace CFSG.Quasithin.H13.A6.L4Tw

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open L4Ind

structure Bits where
  a : ZMod 2
  b : ZMod 2
  c : ZMod 2
  d : ZMod 2
  f : ZMod 2
  e : Bool
deriving DecidableEq

@[expose] def enc (o : Bits) : MulAut SL4 := nf (uSL o.a o.b o.c o.d o.f) o.e

@[expose] def tauBits (o : Bits) : Bits :=
  ⟨o.f, o.d, o.c + o.a * o.d + o.b * o.f, o.b, o.a, o.e⟩

@[expose] def bmul (o p : Bits) : Bits :=
  let q := cond o.e (tauBits p) p
  ⟨o.a + q.a, o.b + q.b, o.c + q.c + o.a * q.d + o.b * q.f, o.d + q.d, o.f + q.f, xor o.e p.e⟩

@[expose] def bone : Bits := ⟨0, 0, 0, 0, 0, false⟩

theorem enc_bone : enc bone = 1 := by
  have h : uSL 0 0 0 0 0 = 1 := Subtype.ext (by decide)
  rw [enc, bone, h, nf_false, map_one]

theorem uSL_tauBits (o : Bits) :
    uSL (tauBits o).a (tauBits o).b (tauBits o).c (tauBits o).d (tauBits o).f =
      tauW (uSL o.a o.b o.c o.d o.f) := by
  rw [tauW_uSL]
  rfl

theorem enc_mul (o p : Bits) : enc o * enc p = enc (bmul o p) := by
  obtain ⟨a, b, c, d, f, e⟩ := o
  rw [enc, enc, nf_mul, enc]
  cases e
  · simp only [Bool.cond_false, bmul, uSL_mul]
  · simp only [Bool.cond_true, bmul]
    rw [← uSL_tauBits, uSL_mul]

@[expose] def isUB (X : M4) : Bool :=
  decide (X 1 0 = 0 ∧ X 2 0 = 0 ∧ X 3 0 = 0 ∧ X 2 1 = 0 ∧ X 3 1 = 0 ∧ X 3 2 = 0 ∧
    X 0 0 = 1 ∧ X 1 1 = 1 ∧ X 2 2 = 1 ∧ X 3 3 = 1)

theorem isUB_iff (g : SL4) : isUB (g : M4) = true ↔ g ∈ unitriangular 4 (ZMod 2) := by
  rw [mem_unitriangular, isUB, decide_eq_true_iff]
  constructor
  · rintro ⟨h10, h20, h30, h21, h31, h32, h00, h11, h22, h33⟩
    refine ⟨fun i j hji => ?_, fun i => ?_⟩
    · fin_cases i <;> fin_cases j <;> simp_all
    · fin_cases i <;> assumption
  · rintro ⟨hl, hd⟩
    exact ⟨hl 1 0 (by decide), hl 2 0 (by decide), hl 3 0 (by decide), hl 2 1 (by decide),
      hl 3 1 (by decide), hl 3 2 (by decide), hd 0, hd 1, hd 2, hd 3⟩

@[expose] def conjM (H Hi : M4) (o : Bits) : M4 :=
  H * uM o.a o.b o.c o.d o.f * cond o.e (w0M * Hᵀ * w0M) Hi

theorem coe_tauW_inv (H Hi : M4) (h : H * Hi = 1) :
    ((tauW (L4Ind.mkSL H Hi h)⁻¹ : SL4) : M4) = w0M * Hᵀ * w0M := by
  rw [tauW_matrix, inv_inv, L4Ind.coe_mkSL]

theorem conj_enc (H Hi : M4) (h : H * Hi = 1) (o : Bits) :
    ∃ X : SL4, (X : M4) = conjM H Hi o ∧
      MulAut.conj (L4Ind.mkSL H Hi h) * enc o * (MulAut.conj (L4Ind.mkSL H Hi h))⁻¹ =
        nf X o.e := by
  refine ⟨_, ?_, conj_nf _ _ _⟩
  rw [conjM, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_uSL,
    L4Ind.coe_mkSL]
  cases o.e
  · rw [Bool.cond_false, Bool.cond_false, L4Ind.coe_mkSL_inv]
  · rw [Bool.cond_true, Bool.cond_true, coe_tauW_inv]

structure Wit where
  H : M4
  Hi : M4
  b : Bits
  b' : Bits

abbrev tq1M : M4 := w0M * q1Mᵀ * w0M

@[expose] def witOK (w : Wit) : Bool :=
  decide (w.H * w.Hi = 1) &&
    isUB (q2M * (conjM w.H w.Hi w.b' * cond w.b'.e tq1M q1M)) && !isUB (conjM w.H w.Hi w.b)

@[expose] def eTab : List Wit :=
  [⟨!![0, 1, 0, 0; 1, 1, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0],
    !![1, 1, 0, 0; 1, 0, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0],
    ⟨0, 0, 0, 0, 1, false⟩, ⟨0, 0, 0, 1, 0, false⟩⟩,
  ⟨!![0, 1, 0, 0; 1, 0, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0],
    !![0, 1, 0, 0; 1, 0, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0],
    ⟨0, 0, 0, 0, 1, false⟩, ⟨0, 0, 1, 0, 0, false⟩⟩,
  ⟨!![0, 1, 0, 0; 1, 0, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0],
    !![0, 1, 0, 0; 1, 0, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0],
    ⟨0, 0, 0, 0, 1, false⟩, ⟨0, 0, 1, 1, 0, false⟩⟩,
  ⟨!![0, 0, 0, 1; 1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 1],
    !![0, 1, 0, 0; 0, 0, 1, 0; 1, 0, 0, 1; 1, 0, 0, 0],
    ⟨0, 0, 0, 0, 1, false⟩, ⟨1, 0, 0, 0, 0, false⟩⟩,
  ⟨!![0, 0, 0, 1; 1, 0, 0, 0; 0, 0, 1, 1; 0, 1, 1, 0],
    !![0, 1, 0, 0; 1, 0, 1, 1; 1, 0, 1, 0; 1, 0, 0, 0],
    ⟨0, 0, 0, 0, 1, false⟩, ⟨1, 0, 1, 0, 0, false⟩⟩,
  ⟨!![0, 0, 1, 0; 1, 0, 0, 0; 0, 0, 0, 1; 0, 1, 0, 0],
    !![0, 1, 0, 0; 0, 0, 0, 1; 1, 0, 0, 0; 0, 0, 1, 0],
    ⟨0, 0, 0, 1, 0, false⟩, ⟨0, 0, 1, 0, 0, false⟩⟩,
  ⟨!![0, 0, 1, 0; 1, 0, 0, 0; 0, 0, 0, 1; 0, 1, 0, 0],
    !![0, 1, 0, 0; 0, 0, 0, 1; 1, 0, 0, 0; 0, 0, 1, 0],
    ⟨0, 0, 0, 1, 0, false⟩, ⟨0, 0, 1, 0, 1, false⟩⟩,
  ⟨!![0, 0, 0, 1; 1, 0, 0, 0; 0, 0, 1, 0; 0, 1, 0, 0],
    !![0, 1, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0; 1, 0, 0, 0],
    ⟨0, 0, 0, 1, 0, false⟩, ⟨0, 1, 0, 0, 0, false⟩⟩,
  ⟨!![0, 0, 0, 1; 1, 0, 0, 0; 0, 0, 1, 1; 0, 1, 1, 0],
    !![0, 1, 0, 0; 1, 0, 1, 1; 1, 0, 1, 0; 1, 0, 0, 0],
    ⟨0, 0, 0, 1, 0, false⟩, ⟨0, 1, 1, 0, 0, false⟩⟩,
  ⟨!![0, 1, 0, 0; 1, 0, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0],
    !![0, 1, 0, 0; 1, 0, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0],
    ⟨0, 0, 0, 1, 1, false⟩, ⟨0, 0, 1, 0, 0, false⟩⟩,
  ⟨!![0, 1, 0, 0; 1, 0, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0],
    !![0, 1, 0, 0; 1, 0, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0],
    ⟨0, 0, 0, 1, 1, false⟩, ⟨0, 0, 1, 1, 0, false⟩⟩,
  ⟨!![0, 0, 0, 1; 1, 0, 0, 0; 0, 0, 1, 0; 0, 1, 0, 0],
    !![0, 1, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0; 1, 0, 0, 0],
    ⟨0, 0, 0, 1, 1, false⟩, ⟨1, 1, 0, 0, 0, false⟩⟩,
  ⟨!![0, 0, 0, 1; 1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 1],
    !![0, 1, 0, 0; 0, 0, 1, 0; 1, 0, 0, 1; 1, 0, 0, 0],
    ⟨0, 0, 0, 1, 1, false⟩, ⟨1, 1, 1, 0, 0, false⟩⟩,
  ⟨!![0, 1, 0, 0; 1, 1, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0],
    !![1, 1, 0, 0; 1, 0, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0],
    ⟨0, 0, 0, 0, 0, true⟩, ⟨0, 0, 1, 0, 0, false⟩⟩,
  ⟨!![0, 0, 1, 0; 1, 0, 0, 0; 0, 0, 0, 1; 0, 1, 0, 0],
    !![0, 1, 0, 0; 0, 0, 0, 1; 1, 0, 0, 0; 0, 0, 1, 0],
    ⟨0, 1, 0, 0, 0, false⟩, ⟨0, 0, 1, 0, 0, false⟩⟩,
  ⟨!![0, 0, 1, 0; 1, 0, 0, 0; 0, 0, 0, 1; 0, 1, 0, 0],
    !![0, 1, 0, 0; 0, 0, 0, 1; 1, 0, 0, 0; 0, 0, 1, 0],
    ⟨0, 1, 0, 1, 0, false⟩, ⟨0, 0, 1, 0, 0, false⟩⟩,
  ⟨!![0, 0, 1, 0; 1, 0, 0, 0; 0, 0, 0, 1; 0, 1, 0, 0],
    !![0, 1, 0, 0; 0, 0, 0, 1; 1, 0, 0, 0; 0, 0, 1, 0],
    ⟨0, 1, 0, 1, 0, true⟩, ⟨0, 0, 1, 0, 0, false⟩⟩,
  ⟨!![0, 1, 0, 0; 1, 0, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0],
    !![0, 1, 0, 0; 1, 0, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0],
    ⟨1, 0, 0, 0, 0, false⟩, ⟨0, 0, 1, 0, 0, false⟩⟩,
  ⟨!![0, 1, 0, 0; 1, 0, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0],
    !![0, 1, 0, 0; 1, 0, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0],
    ⟨1, 0, 0, 0, 1, false⟩, ⟨0, 0, 1, 0, 0, false⟩⟩,
  ⟨!![0, 1, 0, 0; 1, 0, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0],
    !![0, 1, 0, 0; 1, 0, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0],
    ⟨1, 0, 0, 0, 1, true⟩, ⟨0, 0, 1, 0, 0, false⟩⟩,
  ⟨!![0, 1, 0, 0; 1, 0, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0],
    !![0, 1, 0, 0; 1, 0, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0],
    ⟨1, 1, 0, 0, 0, false⟩, ⟨0, 0, 1, 0, 0, false⟩⟩,
  ⟨!![0, 1, 0, 0; 1, 0, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0],
    !![0, 1, 0, 0; 1, 0, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0],
    ⟨1, 1, 0, 1, 1, false⟩, ⟨0, 0, 1, 0, 0, false⟩⟩,
  ⟨!![0, 1, 0, 0; 1, 0, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0],
    !![0, 1, 0, 0; 1, 0, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0],
    ⟨1, 1, 0, 1, 1, true⟩, ⟨0, 0, 1, 0, 0, false⟩⟩,
  ⟨!![0, 0, 0, 1; 1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 1],
    !![0, 1, 0, 0; 0, 0, 1, 0; 1, 0, 0, 1; 1, 0, 0, 0],
    ⟨0, 0, 1, 0, 1, false⟩, ⟨1, 0, 0, 0, 0, false⟩⟩,
  ⟨!![0, 0, 0, 1; 1, 0, 0, 0; 0, 0, 1, 1; 0, 1, 1, 0],
    !![0, 1, 0, 0; 1, 0, 1, 1; 1, 0, 1, 0; 1, 0, 0, 0],
    ⟨0, 0, 1, 0, 1, false⟩, ⟨1, 0, 1, 0, 0, false⟩⟩,
  ⟨!![0, 0, 0, 1; 1, 0, 0, 0; 0, 0, 1, 0; 0, 1, 0, 0],
    !![0, 1, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0; 1, 0, 0, 0],
    ⟨0, 0, 1, 1, 0, false⟩, ⟨0, 1, 0, 0, 0, false⟩⟩,
  ⟨!![0, 0, 0, 1; 1, 0, 0, 0; 0, 0, 1, 1; 0, 1, 1, 0],
    !![0, 1, 0, 0; 1, 0, 1, 1; 1, 0, 1, 0; 1, 0, 0, 0],
    ⟨0, 0, 1, 1, 0, false⟩, ⟨0, 1, 1, 0, 0, false⟩⟩,
  ⟨!![0, 0, 0, 1; 1, 0, 0, 0; 0, 0, 1, 0; 0, 1, 0, 0],
    !![0, 1, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0; 1, 0, 0, 0],
    ⟨0, 0, 1, 1, 1, false⟩, ⟨1, 1, 0, 0, 0, false⟩⟩,
  ⟨!![0, 0, 0, 1; 1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 1],
    !![0, 1, 0, 0; 0, 0, 1, 0; 1, 0, 0, 1; 1, 0, 0, 0],
    ⟨0, 0, 1, 1, 1, false⟩, ⟨1, 1, 1, 0, 0, false⟩⟩,
  ⟨!![0, 0, 0, 1; 1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 1],
    !![0, 1, 0, 0; 0, 0, 1, 0; 1, 0, 0, 1; 1, 0, 0, 0],
    ⟨0, 1, 0, 0, 0, false⟩, ⟨1, 0, 0, 0, 0, false⟩⟩,
  ⟨!![0, 0, 1, 0; 1, 0, 0, 0; 0, 0, 0, 1; 0, 1, 0, 0],
    !![0, 1, 0, 0; 0, 0, 0, 1; 1, 0, 0, 0; 0, 0, 1, 0],
    ⟨0, 1, 0, 0, 0, false⟩, ⟨1, 0, 1, 0, 0, false⟩⟩,
  ⟨!![0, 1, 0, 0; 1, 1, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0],
    !![1, 1, 0, 0; 1, 0, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0],
    ⟨0, 0, 0, 0, 0, true⟩, ⟨0, 1, 0, 1, 0, false⟩⟩,
  ⟨!![0, 0, 1, 0; 1, 0, 0, 0; 0, 0, 0, 1; 0, 1, 0, 0],
    !![0, 1, 0, 0; 0, 0, 0, 1; 1, 0, 0, 0; 0, 0, 1, 0],
    ⟨0, 1, 0, 1, 0, false⟩, ⟨0, 0, 1, 0, 0, true⟩⟩,
  ⟨!![0, 1, 0, 0; 1, 1, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0],
    !![1, 1, 0, 0; 1, 0, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0],
    ⟨1, 0, 0, 0, 1, false⟩, ⟨0, 1, 0, 1, 0, false⟩⟩,
  ⟨!![0, 0, 1, 0; 1, 0, 1, 0; 0, 0, 0, 1; 0, 1, 0, 0],
    !![1, 1, 0, 0; 0, 0, 0, 1; 1, 0, 0, 0; 0, 0, 1, 0],
    ⟨0, 1, 0, 1, 0, false⟩, ⟨1, 1, 1, 1, 1, true⟩⟩,
  ⟨!![0, 0, 1, 0; 1, 0, 0, 0; 0, 0, 0, 1; 0, 1, 0, 0],
    !![0, 1, 0, 0; 0, 0, 0, 1; 1, 0, 0, 0; 0, 0, 1, 0],
    ⟨0, 1, 0, 1, 0, false⟩, ⟨1, 0, 1, 0, 1, false⟩⟩,
  ⟨!![0, 0, 1, 0; 1, 0, 0, 0; 0, 0, 0, 1; 0, 1, 0, 0],
    !![0, 1, 0, 0; 0, 0, 0, 1; 1, 0, 0, 0; 0, 0, 1, 0],
    ⟨0, 1, 0, 1, 0, false⟩, ⟨1, 0, 1, 0, 1, true⟩⟩,
  ⟨!![0, 1, 0, 0; 1, 0, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0],
    !![0, 1, 0, 0; 1, 0, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0],
    ⟨1, 0, 0, 0, 0, false⟩, ⟨0, 1, 1, 0, 0, false⟩⟩,
  ⟨!![0, 1, 0, 0; 1, 0, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0],
    !![0, 1, 0, 0; 1, 0, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0],
    ⟨1, 0, 1, 0, 0, false⟩, ⟨0, 1, 1, 0, 0, false⟩⟩,
  ⟨!![0, 0, 1, 0; 1, 0, 1, 0; 0, 0, 0, 1; 0, 1, 0, 0],
    !![1, 1, 0, 0; 0, 0, 0, 1; 1, 0, 0, 0; 0, 0, 1, 0],
    ⟨0, 1, 1, 1, 0, false⟩, ⟨0, 1, 1, 1, 0, true⟩⟩,
  ⟨!![0, 0, 1, 0; 1, 0, 0, 0; 0, 0, 0, 1; 0, 1, 0, 0],
    !![0, 1, 0, 0; 0, 0, 0, 1; 1, 0, 0, 0; 0, 0, 1, 0],
    ⟨0, 1, 1, 1, 0, false⟩, ⟨0, 0, 1, 0, 0, true⟩⟩,
  ⟨!![0, 1, 0, 0; 1, 0, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0],
    !![0, 1, 0, 0; 1, 0, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0],
    ⟨1, 0, 0, 0, 1, false⟩, ⟨0, 1, 1, 1, 0, false⟩⟩,
  ⟨!![0, 1, 0, 0; 1, 0, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0],
    !![0, 1, 0, 0; 1, 0, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0],
    ⟨1, 0, 0, 0, 1, true⟩, ⟨0, 1, 1, 1, 0, false⟩⟩,
  ⟨!![0, 1, 0, 0; 1, 0, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0],
    !![0, 1, 0, 0; 1, 0, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0],
    ⟨1, 0, 1, 0, 1, false⟩, ⟨0, 1, 1, 1, 0, false⟩⟩,
  ⟨!![0, 1, 0, 0; 1, 0, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0],
    !![0, 1, 0, 0; 1, 0, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0],
    ⟨1, 0, 1, 0, 1, true⟩, ⟨0, 1, 1, 1, 0, false⟩⟩,
  ⟨!![0, 0, 1, 0; 1, 0, 1, 0; 0, 0, 0, 1; 0, 1, 0, 0],
    !![1, 1, 0, 0; 0, 0, 0, 1; 1, 0, 0, 0; 0, 0, 1, 0],
    ⟨0, 0, 0, 0, 0, true⟩, ⟨1, 0, 0, 0, 1, false⟩⟩,
  ⟨!![0, 1, 0, 0; 1, 0, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0],
    !![0, 1, 0, 0; 1, 0, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0],
    ⟨1, 0, 0, 0, 1, false⟩, ⟨0, 0, 1, 0, 0, true⟩⟩,
  ⟨!![0, 1, 0, 0; 1, 1, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0],
    !![1, 1, 0, 0; 1, 0, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0],
    ⟨1, 0, 0, 0, 1, false⟩, ⟨1, 1, 1, 1, 1, true⟩⟩,
  ⟨!![0, 1, 0, 0; 1, 0, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0],
    !![0, 1, 0, 0; 1, 0, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0],
    ⟨1, 0, 0, 0, 1, false⟩, ⟨0, 1, 1, 1, 0, true⟩⟩,
  ⟨!![0, 1, 0, 0; 1, 1, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0],
    !![1, 1, 0, 0; 1, 0, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0],
    ⟨1, 0, 1, 0, 1, false⟩, ⟨1, 0, 1, 0, 1, true⟩⟩,
  ⟨!![0, 1, 0, 0; 1, 0, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0],
    !![0, 1, 0, 0; 1, 0, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0],
    ⟨1, 0, 1, 0, 1, false⟩, ⟨0, 0, 1, 0, 0, true⟩⟩,
  ⟨!![0, 0, 1, 0; 1, 0, 0, 0; 0, 0, 0, 1; 0, 1, 0, 0],
    !![0, 1, 0, 0; 0, 0, 0, 1; 1, 0, 0, 0; 0, 0, 1, 0],
    ⟨0, 1, 0, 1, 0, true⟩, ⟨1, 0, 1, 0, 1, false⟩⟩,
  ⟨!![0, 1, 0, 0; 1, 0, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0],
    !![0, 1, 0, 0; 1, 0, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0],
    ⟨1, 0, 1, 0, 1, false⟩, ⟨0, 1, 1, 1, 0, true⟩⟩,
  ⟨!![1, 0, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1; 0, 1, 1, 0],
    !![1, 0, 0, 0; 0, 1, 0, 1; 0, 1, 0, 0; 0, 0, 1, 0],
    ⟨0, 0, 0, 0, 0, true⟩, ⟨1, 1, 0, 1, 1, false⟩⟩,
  ⟨!![0, 1, 0, 0; 1, 0, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0],
    !![0, 1, 0, 0; 1, 0, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0],
    ⟨1, 1, 0, 1, 1, false⟩, ⟨0, 0, 1, 0, 0, true⟩⟩,
  ⟨!![0, 0, 1, 0; 1, 0, 0, 0; 0, 0, 0, 1; 0, 1, 0, 0],
    !![0, 1, 0, 0; 0, 0, 0, 1; 1, 0, 0, 0; 0, 0, 1, 0],
    ⟨1, 1, 0, 1, 1, false⟩, ⟨1, 0, 1, 0, 1, true⟩⟩,
  ⟨!![0, 1, 0, 0; 1, 0, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0],
    !![0, 1, 0, 0; 1, 0, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0],
    ⟨1, 1, 0, 1, 1, false⟩, ⟨0, 1, 1, 1, 0, true⟩⟩,
  ⟨!![0, 1, 0, 0; 1, 1, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0],
    !![1, 1, 0, 0; 1, 0, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0],
    ⟨1, 1, 1, 1, 1, false⟩, ⟨1, 1, 1, 1, 1, true⟩⟩,
  ⟨!![0, 1, 0, 0; 1, 0, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0],
    !![0, 1, 0, 0; 1, 0, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0],
    ⟨1, 1, 1, 1, 1, false⟩, ⟨0, 0, 1, 0, 0, true⟩⟩,
  ⟨!![1, 0, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1; 0, 1, 1, 0],
    !![1, 0, 0, 0; 0, 1, 0, 1; 0, 1, 0, 0; 0, 0, 1, 0],
    ⟨0, 1, 0, 1, 0, true⟩, ⟨1, 1, 1, 1, 1, false⟩⟩,
  ⟨!![0, 1, 0, 0; 1, 0, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0],
    !![0, 1, 0, 0; 1, 0, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0],
    ⟨1, 1, 1, 1, 1, false⟩, ⟨0, 1, 1, 1, 0, true⟩⟩]

theorem eTab_ok : eTab.all witOK = true := by
  decide +kernel

@[expose] def allBits : List Bits :=
  [0, 1].flatMap fun a => [0, 1].flatMap fun b => [0, 1].flatMap fun c => [0, 1].flatMap fun d =>
    [0, 1].flatMap fun f => [false, true].map fun e => (⟨a, b, c, d, f, e⟩ : Bits)

theorem mem_allBits (o : Bits) : o ∈ allBits := by
  obtain ⟨a, b, c, d, f, e⟩ := o
  revert a b c d f e
  decide

@[expose] def pairOK (o o' : Bits) : Bool :=
  !decide (o.e = false ∧ o ≠ bone ∧ o' ≠ bone ∧ o' ≠ o ∧ bmul o o' = bmul o' o ∧
      bmul o o = bone ∧ bmul o' o' = bone) ||
    eTab.any fun w => decide (w.b ∈ [o, o', bmul o o'] ∧ w.b' ∈ [o, o', bmul o o'])

theorem pairOK_all : (allBits.all fun o => allBits.all fun o' => pairOK o o') = true := by
  decide +kernel

theorem exists_wit {o o' : Bits} (he : o.e = false) (ho : o ≠ bone) (ho' : o' ≠ bone)
    (hoo : o' ≠ o) (hc : bmul o o' = bmul o' o) (h2 : bmul o o = bone) (h2' : bmul o' o' = bone) :
    ∃ w ∈ eTab, w.b ∈ [o, o', bmul o o'] ∧ w.b' ∈ [o, o', bmul o o'] := by
  have h := List.all_eq_true.1 pairOK_all o (mem_allBits o)
  have h3 := List.all_eq_true.1 h o' (mem_allBits o')
  simp only [pairOK, Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
    List.any_eq_true, decide_eq_true_eq] at h3
  rcases h3 with h3 | h3
  · exact absurd ⟨he, ho, ho', hoo, hc, h2, h2'⟩ h3
  · exact h3

theorem uSL_inj {a b c d f a' b' c' d' f' : ZMod 2}
    (h : uSL a b c d f = uSL a' b' c' d' f') :
    a = a' ∧ b = b' ∧ c = c' ∧ d = d' ∧ f = f' := by
  have hm : uM a b c d f = uM a' b' c' d' f' := congrArg Subtype.val h
  exact ⟨congrFun (congrFun hm 0) 1, congrFun (congrFun hm 0) 2, congrFun (congrFun hm 0) 3,
    congrFun (congrFun hm 1) 3, congrFun (congrFun hm 2) 3⟩

theorem enc_inj {x y : Bits} (he : x.e = y.e) (h : enc x = enc y) : x = y := by
  have h' : MulAut.conj (uSL x.a x.b x.c x.d x.f) = MulAut.conj (uSL y.a y.b y.c y.d y.f) := by
    have := congrArg (· * (cond x.e tauW 1)⁻¹) h
    simpa only [enc, nf, he, mul_inv_cancel_right] using this
  obtain ⟨ha, hb, hc, hd, hf⟩ := uSL_inj (conj_injective h')
  obtain ⟨a, b, c, d, f, e⟩ := x
  obtain ⟨a', b', c', d', f', e'⟩ := y
  simp only at ha hb hc hd hf he
  subst ha hb hc hd hf he
  rfl

theorem bmul_e (o p : Bits) : (bmul o p).e = xor o.e p.e := rfl

theorem exists_mem_ne_ne {G : Type*} [Group G] {E : Subgroup G} (h4 : 4 ≤ Nat.card E) (x y : G) :
    ∃ z ∈ E, z ≠ x ∧ z ≠ y := by
  by_contra hcon
  push Not at hcon
  have hsub : (E : Set G) ⊆ {x, y} := fun z hz => by
    by_cases hzx : z = x
    · exact Or.inl hzx
    · exact Or.inr (hcon z hz hzx)
  have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
  have h2 : ({x, y} : Set G).ncard ≤ 2 :=
    (Set.ncard_insert_le x {y}).trans (by rw [Set.ncard_singleton])
  have h3 : (E : Set G).ncard = Nat.card E := (Nat.card_coe_set_eq _).symm
  omega

variable {M : Type*} [CommGroup M] {Φ : MulAut SL4 →* MulAut M} {m₀ : M}

theorem exists_fix_of_quad (hsq : ∀ x : M, x * x = 1)
    (hU : ∀ u ∈ unitriangular 4 (ZMod 2), Φ (MulAut.conj u) m₀ = m₀) (hτ : Φ tauW m₀ = m₀)
    (hrel : m₀ * Φ (MulAut.conj q1) m₀ * Φ (MulAut.conj q2) m₀ = 1)
    {E : Subgroup (MulAut SL4)} (hE : ∀ x ∈ E, ∃ o, x = enc o)
    (hab : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hE2 : ∀ x ∈ E, x * x = 1)
    (h4 : 4 ≤ Nat.card E) (hq : IndQuad.QuadOn Φ (E : Set (MulAut SL4))) :
    ∃ A : SL4, A ∉ unitriangular 4 (ZMod 2) ∧ Φ (MulAut.conj A) m₀ = m₀ := by
  have hτ' : ∀ ε : Bool, Φ (cond ε tauW 1) m₀ = m₀ := fun ε => by
    cases ε
    · rw [Bool.cond_false, map_one, MulAut.one_apply]
    · exact hτ
  have hnf : ∀ (X : SL4) (ε : Bool), Φ (nf X ε) m₀ = Φ (MulAut.conj X) m₀ := fun X ε => by
    rw [nf, map_mul, MulAut.mul_apply, hτ']
  obtain ⟨o, hoE, hoe, ho1⟩ : ∃ o : Bits, enc o ∈ E ∧ o.e = false ∧ o ≠ bone := by
    obtain ⟨x₁, hx₁, hx₁1, -⟩ := exists_mem_ne_ne h4 1 1
    obtain ⟨o₁, rfl⟩ := hE x₁ hx₁
    have hne : ∀ p : Bits, enc p ≠ 1 → p ≠ bone := fun p hp h => hp (h ▸ enc_bone)
    cases h₁ : o₁.e
    · exact ⟨o₁, hx₁, h₁, hne _ hx₁1⟩
    obtain ⟨x₂, hx₂, hx₂1, hx₂x₁⟩ := exists_mem_ne_ne h4 1 (enc o₁)
    obtain ⟨o₂, rfl⟩ := hE x₂ hx₂
    cases h₂ : o₂.e
    · exact ⟨o₂, hx₂, h₂, hne _ hx₂1⟩
    refine ⟨bmul o₁ o₂, ?_, by rw [bmul_e, h₁, h₂]; rfl, ?_⟩
    · rw [← enc_mul]
      exact E.mul_mem hx₁ hx₂
    · intro h
      apply hx₂x₁
      have h1 : enc o₁ * enc o₂ = 1 := by rw [enc_mul, h, enc_bone]
      calc enc o₂ = enc o₁ * (enc o₁ * enc o₂) := by
            rw [← mul_assoc, hE2 _ hx₁, one_mul]
        _ = enc o₁ := by rw [h1, mul_one]
  obtain ⟨a', ha'E, ha'1, ha'o⟩ := exists_mem_ne_ne h4 1 (enc o)
  obtain ⟨o', rfl⟩ := hE a' ha'E
  have ho'1 : o' ≠ bone := fun h => ha'1 (h ▸ enc_bone)
  have hoo : o' ≠ o := fun h => ha'o (h ▸ rfl)
  have hcomm : bmul o o' = bmul o' o := by
    refine enc_inj (by rw [bmul_e, bmul_e, Bool.xor_comm]) ?_
    rw [← enc_mul, ← enc_mul]
    exact hab _ hoE _ ha'E
  have hsq' : ∀ p : Bits, enc p ∈ E → bmul p p = bone := fun p hp =>
    enc_inj (by rw [bmul_e, Bool.xor_self]; rfl) (by rw [← enc_mul, enc_bone]; exact hE2 _ hp)
  obtain ⟨w, hw, hb, hb'⟩ := exists_wit hoe ho1 ho'1 hoo hcomm (hsq' o hoE) (hsq' o' ha'E)
  have hmemE : ∀ p ∈ [o, o', bmul o o'], enc p ∈ E := by
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl
    · exact hoE
    · exact ha'E
    · rw [← enc_mul]
      exact E.mul_mem hoE ha'E
  have hok := List.all_eq_true.1 eTab_ok w hw
  simp only [witOK, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hok
  obtain ⟨⟨hHH, hT1⟩, hT2⟩ := hok
  obtain ⟨Y, hYm, hY⟩ := conj_enc w.H w.Hi hHH w.b'
  obtain ⟨X, hXm, hX⟩ := conj_enc w.H w.Hi hHH w.b
  have hμU : ∀ g u : SL4, u ∈ unitriangular 4 (ZMod 2) →
      Φ (MulAut.conj (g * u)) m₀ = Φ (MulAut.conj g) m₀ := fun g u hu => by
    rw [map_mul, map_mul, MulAut.mul_apply, hU u hu]
  have hq1 : ((q1⁻¹ : SL4) : M4) = q1M := by
    rw [inv_eq_of_mul_eq_one_right q1_mul_self]
    rfl
  have htq1 : ((tauW q1 : SL4) : M4) = tq1M := by
    rw [tauW_matrix, hq1]
  have hZ : q2⁻¹ * (Y * cond w.b'.e (tauW q1) q1) ∈ unitriangular 4 (ZMod 2) := by
    rw [← isUB_iff, inv_eq_of_mul_eq_one_right q2_mul_self, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_mul, hYm]
    cases hbe : w.b'.e
    · rw [hbe] at hT1
      exact hT1
    · rw [hbe] at hT1
      rw [Bool.cond_true, htq1]
      exact hT1
  have hyq : Φ (nf Y w.b'.e) (Φ (MulAut.conj q1) m₀) = Φ (MulAut.conj q2) m₀ := by
    rw [← MulAut.mul_apply, ← map_mul, ← nf_false q1, nf_mul, hnf, ← hμU q2 _ hZ,
      mul_inv_cancel_left]
  have hcomm₀ : Φ (nf Y w.b'.e) (Φ (MulAut.conj q1) m₀) * (Φ (MulAut.conj q1) m₀)⁻¹ = m₀ := by
    rw [hyq, inv_eq_of_mul_eq_one_right (hsq _)]
    calc Φ (MulAut.conj q2) m₀ * Φ (MulAut.conj q1) m₀
        = m₀ * (m₀ * Φ (MulAut.conj q1) m₀ * Φ (MulAut.conj q2) m₀) := by
          rw [← mul_assoc, ← mul_assoc, hsq, one_mul, mul_comm]
      _ = m₀ := by rw [hrel, mul_one]
  have hquad := hq (MulAut.conj (L4Ind.mkSL w.H w.Hi hHH)) _ (hmemE _ hb) _ (hmemE _ hb')
    (Φ (MulAut.conj q1) m₀)
  rw [hX, hY, hcomm₀, hnf] at hquad
  refine ⟨X, fun hXU => ?_, hquad⟩
  have h1 := (isUB_iff X).2 hXU
  rw [hXm, hT2] at h1
  exact Bool.false_ne_true h1


end CFSG.Quasithin.H13.A6.L4Tw
