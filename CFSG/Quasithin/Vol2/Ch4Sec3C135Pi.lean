module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Quasithin.Vol2.Ch4Sec3C135V

public section

namespace CFSG.Quasithin.H13.Ch4.C135

open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.A4
open CFSG.Open hiding StatedSL
open CFSG.Assembly.LowTwoRank CFSG.Quasithin.H13.Ch4 Matrix
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {F : Type} [Field F] [CharP F 2]

namespace Hyp135.Adapted

variable {G₀ L : Subgroup G} {α : ↥L →* ↥(StatedSL 3 F)} {H : Hyp135 G₀ L α} (C : H.Adapted)

@[expose] noncomputable def qPart {t : G} (ht : t ∈ pCoreOf 2 G₀) : ↥(c134Q G₀ L) :=
  Classical.choose (C.exists_mul_mem_V ht)

theorem qPart_spec {t : G} (ht : t ∈ pCoreOf 2 G₀) :
    t * ((C.qPart ht : ↥(c134Q G₀ L)) : G)⁻¹ ∈ C.V :=
  Classical.choose_spec (C.exists_mul_mem_V ht)

@[expose] noncomputable def πf {t : G} (ht : t ∈ pCoreOf 2 G₀) : Fin 3 → F := C.e (C.qPart ht) 1

theorem πf_eq {t : G} (ht : t ∈ pCoreOf 2 G₀) (q : ↥(c134Q G₀ L)) (hq : t * (q : G)⁻¹ ∈ C.V) :
    C.πf ht = C.e q 1 := by
  have h1 : ((C.qPart ht : ↥(c134Q G₀ L)) : G) * (q : G)⁻¹ ∈ C.V := by
    have := C.V.mul_mem (C.V.inv_mem (C.qPart_spec ht)) hq
    simpa [mul_assoc] using this
  have h2 : (((C.qPart ht) * q⁻¹ : ↥(c134Q G₀ L)) : G) ∈ C.W :=
    C.mem_W_of_mem_V_Q h1 ((C.qPart ht) * q⁻¹).2
  rw [C.mem_W_iff, C.mul, C.e_inv] at h2
  have h3 := congrArg (fun x => x + C.e q 1) h2
  simp only [Pi.add_apply, Pi.neg_apply, neg_add_cancel_right, zero_add] at h3
  exact h3

theorem πf_of_mem_V {t : G} (ht : t ∈ pCoreOf 2 G₀) (htV : t ∈ C.V) : C.πf ht = 0 := by
  rw [C.πf_eq ht 1 (by simpa using htV), C.e_one]
  rfl

theorem mem_V_of_πf {t : G} (ht : t ∈ pCoreOf 2 G₀) (h : C.πf ht = 0) : t ∈ C.V := by
  have hW : ((C.qPart ht : ↥(c134Q G₀ L)) : G) ∈ C.W := (C.mem_W_iff _).mpr h
  have := C.V.mul_mem (C.qPart_spec ht) (C.W_le_V hW)
  simpa using this

theorem πf_mul {t t' : G} (ht : t ∈ pCoreOf 2 G₀) (ht' : t' ∈ pCoreOf 2 G₀) :
    C.πf ((pCoreOf 2 G₀).mul_mem ht ht') = C.πf ht + C.πf ht' := by
  set q := C.qPart ht with hq
  set q' := C.qPart ht' with hq'
  have hv := C.qPart_spec ht
  have hv' := C.qPart_spec ht'
  set v := t * (q : G)⁻¹ with hvdef
  set v' := t' * (q' : G)⁻¹ with hv'def
  have hv'T : v' ∈ pCoreOf 2 G₀ := hv'.1
  have hv'inv := (pCoreOf 2 G₀).inv_mem hv'T
  set r := cnj (H.pCoreOf_le_normalizer_Q hv'inv) q with hr
  have hrq : C.e r 1 = C.e q 1 := (C.lam_spec hv'inv q).2
  have hmem : t * t' * (((r * q' : ↥(c134Q G₀ L)) : G))⁻¹ ∈ C.V := by
    have e : t * t' * (((r * q' : ↥(c134Q G₀ L)) : G))⁻¹ = v * v' := by
      simp only [Subgroup.coe_mul, coe_cnj, hr, hvdef, hv'def]
      group
    rw [e]
    exact C.V.mul_mem hv hv'
  rw [C.πf_eq _ (r * q') hmem, C.mul, Pi.add_apply, hrq]
  rfl

theorem πf_conj {a t : G} (haG : a ∈ G₀) (haV : a ∈ Subgroup.normalizer (C.V : Set G))
    (ht : t ∈ pCoreOf 2 G₀) (hat : a * t * a⁻¹ ∈ pCoreOf 2 G₀) :
    C.πf hat = C.e (cnj (H.le_normalizer_Q haG) (C.qPart ht)) 1 := by
  refine C.πf_eq hat _ ?_
  have h1 := (Subgroup.mem_normalizer_iff.mp haV _).mp (C.qPart_spec ht)
  convert h1 using 1
  simp only [coe_cnj]
  group

end Hyp135.Adapted

end CFSG.Quasithin.H13.Ch4.C135

end
