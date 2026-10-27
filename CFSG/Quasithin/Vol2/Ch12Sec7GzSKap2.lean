module

public import CFSG.Quasithin.Vol2.Ch12Sec7GzSMLine
public import Certificates.Data.S1277Struct

public section

namespace CFSG.Quasithin.H13.I1277

open CFSG.Quasithin.H13.S127.Mod Certificates.Data.S1277Struct
open scoped IsMulCommutative

structure SplitHyp {G : Type} [Group G] (V M M₀ : Subgroup G) : Prop where
  hVM : V ≤ M
  hMV : M ≤ Subgroup.normalizer (V : Set G)
  hM0 : M₀ ≤ M
  hinf : V ⊓ M₀ = ⊥
  hdec : ∀ m ∈ M, ∃ v ∈ V, ∃ h ∈ M₀, m = v * h
  hCV : Subgroup.centralizer (V : Set G) = V

section Kap2

open scoped Classical

variable {G : Type} [Group G] [Finite G] {V M M₀ : Subgroup G} [IsMulCommutative ↥V]

@[expose] noncomputable def vOf (S : SplitHyp V M M₀) (m : G) : G :=
  if hm : m ∈ M then Classical.choose (S.hdec m hm) else 1

theorem vOf_mem (S : SplitHyp V M M₀) {m : G} (hm : m ∈ M) : vOf S m ∈ V := by
  unfold vOf; rw [dif_pos hm]; exact (Classical.choose_spec (S.hdec m hm)).1

theorem vOf_spec (S : SplitHyp V M M₀) {m : G} (hm : m ∈ M) :
    ∃ h ∈ M₀, m = vOf S m * h := by
  unfold vOf; rw [dif_pos hm]
  obtain ⟨h, hh, e⟩ := (Classical.choose_spec (S.hdec m hm)).2
  exact ⟨h, hh, e⟩

theorem decomp_unique (S : SplitHyp V M M₀) {v v' h h' : G} (hv : v ∈ V) (hv' : v' ∈ V)
    (hh : h ∈ M₀) (hh' : h' ∈ M₀) (e : v * h = v' * h') : v = v' ∧ h = h' := by
  have h1 : v'⁻¹ * v = h' * h⁻¹ := by
    have : v * h = v' * h' := e
    calc v'⁻¹ * v = v'⁻¹ * (v * h) * h⁻¹ := by group
      _ = v'⁻¹ * (v' * h') * h⁻¹ := by rw [e]
      _ = h' * h⁻¹ := by group
  have h2 : v'⁻¹ * v ∈ V ⊓ M₀ := Subgroup.mem_inf.2 ⟨V.mul_mem (V.inv_mem hv') hv, by
    rw [h1]; exact M₀.mul_mem hh' (M₀.inv_mem hh)⟩
  rw [S.hinf, Subgroup.mem_bot] at h2
  have hvv : v = v' := by
    calc v = v' * (v'⁻¹ * v) := by group
      _ = v' := by rw [h2, mul_one]
  refine ⟨hvv, ?_⟩
  rw [hvv] at e
  exact mul_left_cancel e

theorem vOf_mul_of (S : SplitHyp V M M₀) {v h : G} (hv : v ∈ V) (hh : h ∈ M₀) :
    vOf S (v * h) = v := by
  have hm : v * h ∈ M := M.mul_mem (S.hVM hv) (S.hM0 hh)
  obtain ⟨h', hh', e⟩ := vOf_spec S hm
  exact ((decomp_unique S (vOf_mem S hm) hv hh' hh e.symm).1)

@[expose] noncomputable def cpart (C : Coding ↥V) (S : SplitHyp V M M₀) (m : G) : Nat :=
  if hv : vOf S m ∈ V then C.cd ⟨vOf S m, hv⟩ else 0

@[expose] noncomputable def bpart (C : Coding ↥V) (S : SplitHyp V M M₀) (m : G) : B6 :=
  if hm : m ∈ M then C.cB (conjAct V ⟨m, S.hMV hm⟩) else B6.id

theorem bpart_mul (C : Coding ↥V) (S : SplitHyp V M M₀) {m m' : G} (hm : m ∈ M) (hm' : m' ∈ M) :
    bpart C S (m * m') = (bpart C S m).comp (bpart C S m') := by
  have hmm : m * m' ∈ M := M.mul_mem hm hm'
  unfold bpart
  rw [dif_pos hmm, dif_pos hm, dif_pos hm', ← C.cB_mul, ← map_mul]
  rfl

theorem bpart_of_mem (C : Coding ↥V) (S : SplitHyp V M M₀) {m : G} (hm : m ∈ M) :
    bpart C S m = cj C ⟨m, S.hMV hm⟩ := by
  unfold bpart; rw [dif_pos hm]; rfl

theorem bpart_V (C : Coding ↥V) (S : SplitHyp V M M₀) {v : G} (hv : v ∈ V) :
    bpart C S v = B6.id := by
  rw [bpart_of_mem C S (S.hVM hv), cj, conjAct_eq_one_of_mem (S.hMV (S.hVM hv)) hv, C.cB_one]

theorem bpart_one (C : Coding ↥V) (S : SplitHyp V M M₀) : bpart C S 1 = B6.id := by
  simpa using bpart_V C S (V.one_mem)

theorem cpart_V (C : Coding ↥V) (S : SplitHyp V M M₀) {v : G} (hv : v ∈ V) :
    cpart C S v = C.cd ⟨v, hv⟩ := by
  have h1 : vOf S v = v := by
    have := vOf_mul_of S hv M₀.one_mem
    simpa using this
  unfold cpart
  have hv' : vOf S v ∈ V := vOf_mem S (S.hVM hv)
  rw [dif_pos hv']
  congr 1
  exact Subtype.ext h1

theorem bpart_decomp (C : Coding ↥V) (S : SplitHyp V M M₀) {m v h : G} (hv : v ∈ V)
    (hh : h ∈ M₀) (e : m = v * h) :
    bpart C S m = cj C ⟨h, S.hMV (S.hM0 hh)⟩ := by
  have hm : m ∈ M := by rw [e]; exact M.mul_mem (S.hVM hv) (S.hM0 hh)
  rw [bpart_of_mem C S hm]
  have e2 : (⟨m, S.hMV hm⟩ : Subgroup.normalizer (V : Set G)) =
      ⟨v, S.hMV (S.hVM hv)⟩ * ⟨h, S.hMV (S.hM0 hh)⟩ := Subtype.ext e
  rw [e2, cj, map_mul, conjAct_eq_one_of_mem (S.hMV (S.hVM hv)) hv, one_mul]
  rfl

theorem cpart_mul (C : Coding ↥V) (S : SplitHyp V M M₀) {m m' : G} (hm : m ∈ M) (hm' : m' ∈ M) :
    cpart C S (m * m') = cpart C S m ^^^ (bpart C S m).app (cpart C S m') := by
  obtain ⟨h, hh, e⟩ := vOf_spec S hm
  obtain ⟨h', hh', e'⟩ := vOf_spec S hm'
  set v := vOf S m with hv
  set v' := vOf S m' with hv'
  have hvV : v ∈ V := vOf_mem S hm
  have hv'V : v' ∈ V := vOf_mem S hm'
  have hhM : h ∈ M := S.hM0 hh
  have hhN : h ∈ Subgroup.normalizer (V : Set G) := S.hMV hhM
  have hconj : h * v' * h⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp hhN v').mp hv'V
  have emm : m * m' = (v * (h * v' * h⁻¹)) * (h * h') := by
    rw [e, e']; group
  have hvm : vOf S (m * m') = v * (h * v' * h⁻¹) := by
    rw [emm]
    exact vOf_mul_of S (V.mul_mem hvV hconj) (M₀.mul_mem hh hh')
  unfold cpart
  have hvmV : vOf S (m * m') ∈ V := vOf_mem S (M.mul_mem hm hm')
  rw [dif_pos hvmV, dif_pos hvV, dif_pos hv'V]
  have hmain : (⟨vOf S (m * m'), hvmV⟩ : ↥V) = ⟨v, hvV⟩ * ⟨h * v' * h⁻¹, hconj⟩ :=
    Subtype.ext hvm
  rw [hmain, C.cd_mul]
  congr 1
  have hb : bpart C S m = cj C ⟨h, hhN⟩ := bpart_decomp C S hvV hh e
  rw [hb]
  have := cd_conj C ⟨h, hhN⟩ ⟨v', hv'V⟩
  exact this

theorem pair_inj (C : Coding ↥V) (S : SplitHyp V M M₀) {m m' : G} (hm : m ∈ M) (hm' : m' ∈ M)
    (hb : bpart C S m = bpart C S m') (hc : cpart C S m = cpart C S m') : m = m' := by
  obtain ⟨h, hh, e⟩ := vOf_spec S hm
  obtain ⟨h', hh', e'⟩ := vOf_spec S hm'
  have hvV : vOf S m ∈ V := vOf_mem S hm
  have hv'V : vOf S m' ∈ V := vOf_mem S hm'
  have hvv : vOf S m = vOf S m' := by
    have h1 : C.cd ⟨vOf S m, hvV⟩ = C.cd ⟨vOf S m', hv'V⟩ := by
      have := hc
      unfold cpart at this
      rwa [dif_pos hvV, dif_pos hv'V] at this
    have := C.cd_injective h1
    exact congrArg Subtype.val this
  have hhh : h = h' := by
    rw [bpart_decomp C S hvV hh e, bpart_decomp C S hv'V hh' e'] at hb
    have h1 : conjAct V ⟨h, S.hMV (S.hM0 hh)⟩ = conjAct V ⟨h', S.hMV (S.hM0 hh')⟩ :=
      C.cB_injective hb
    have h2 : conjAct V ⟨h⁻¹ * h', S.hMV (M.mul_mem (M.inv_mem (S.hM0 hh)) (S.hM0 hh'))⟩ = 1 := by
      have e3 : (⟨h⁻¹ * h', S.hMV (M.mul_mem (M.inv_mem (S.hM0 hh)) (S.hM0 hh'))⟩ :
          Subgroup.normalizer (V : Set G)) =
          (⟨h, S.hMV (S.hM0 hh)⟩ : Subgroup.normalizer (V : Set G))⁻¹ *
            ⟨h', S.hMV (S.hM0 hh')⟩ := rfl
      rw [e3, map_mul, map_inv, h1, inv_mul_cancel]
    have h3 : h⁻¹ * h' ∈ Subgroup.centralizer (V : Set G) := A4.conjAct_eq_one_iff.1 h2
    rw [S.hCV] at h3
    have h4 : h⁻¹ * h' ∈ V ⊓ M₀ := Subgroup.mem_inf.2 ⟨h3, M₀.mul_mem (M₀.inv_mem hh) hh'⟩
    rw [S.hinf, Subgroup.mem_bot] at h4
    exact (inv_mul_eq_one.1 h4)
  rw [e, e', hvv, hhh]

end Kap2

end CFSG.Quasithin.H13.I1277

end
