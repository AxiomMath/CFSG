module

public import CFSG.Quasithin.MS93.ML3Nat

public section

namespace CFSG.Quasithin.MS93

open Matrix

variable {F : Type} [Field F]

@[expose] def tLn (a b : F) : SL3 F := rootElt 0 2 a * rootElt 1 2 b

theorem tLn_zero_right (a : F) : tLn a 0 = rootElt 0 2 a := by
  simp [tLn]

theorem tLn_zero_left (b : F) : tLn 0 b = rootElt 1 2 b := by
  simp [tLn]

theorem tLn_mem_qLn (a b : F) : tLn a b ∈ (qLn : Subgroup (SL3 F)) :=
  mem_qLn_iff.mpr ⟨a, b, rfl⟩

theorem mem_qLn_iff_tLn {g : SL3 F} : g ∈ qLn ↔ ∃ a b : F, tLn a b = g :=
  mem_qLn_iff

theorem rootElt02_comm_rootElt12 (a b : F) :
    rootElt 0 2 a * rootElt 1 2 b = rootElt 1 2 b * rootElt 0 2 a :=
  (rootElt_commute (by decide) (by decide) a b).eq

theorem tLn_mul (a b a' b' : F) : tLn a b * tLn a' b' = tLn (a + a') (b + b') := by
  simp only [tLn, rootElt_add]
  rw [mul_assoc, ← mul_assoc (rootElt 1 2 b), ← rootElt02_comm_rootElt12 a' b]
  simp only [mul_assoc]

theorem tLn_comm (a b a' b' : F) : tLn a b * tLn a' b' = tLn a' b' * tLn a b := by
  rw [tLn_mul, tLn_mul, add_comm a, add_comm b]

theorem coe_mul_SL3 (A B : SL3 F) :
    ((A * B : SL3 F) : Matrix (Fin 3) (Fin 3) F) =
      (A : Matrix (Fin 3) (Fin 3) F) * (B : Matrix (Fin 3) (Fin 3) F) :=
  rfl

theorem tLn_mulVec (a b : F) (x : Fin 3 → F) :
    ((tLn a b : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ x = x + ![a * x 2, b * x 2, 0] := by
  rw [tLn, coe_mul_SL3, ← Matrix.mulVec_mulVec,
    rootElt_mulVec (show (1 : Fin 3) ≠ 2 by decide),
    rootElt_mulVec (show (0 : Fin 3) ≠ 2 by decide)]
  funext k
  fin_cases k <;> simp

theorem diagPt_mulVec (l : F) (hl : l ≠ 0) (x : Fin 3 → F) :
    ((diagPt l hl : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ x = ![l * x 0, l⁻¹ * x 1, x 2] := by
  rw [diagPt, SpecialLinearGroup.diag2n_coe]
  funext k
  fin_cases k <;> simp [Matrix.mulVec_diagonal]

theorem mulVec_inv_two {g : SL3 F}
    (hg : ∀ x : Fin 3 → F, (((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ x) 2 = x 2)
    (x : Fin 3 → F) : (((g⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ x) 2 = x 2 := by
  have h := hg (((g⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ x)
  rw [Matrix.mulVec_mulVec, ← coe_mul_SL3, mul_inv_cancel] at h
  rw [← h]
  simp

theorem rootElt01_mulVec_two (x : Fin 3 → F) :
    (((rootElt 0 1 (1 : F) : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ x) 2 = x 2 := by
  rw [rootElt_mulVec (by decide)]
  simp

theorem diagPt_mulVec_two (l : F) (hl : l ≠ 0) (x : Fin 3 → F) :
    (((diagPt l hl : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ x) 2 = x 2 := by
  rw [diagPt_mulVec]
  rfl

theorem rootElt01_comm_tLn (a : F) : rootElt 0 1 (1 : F) * tLn a 0 = tLn a 0 * rootElt 0 1 1 := by
  rw [tLn_zero_right]
  exact (rootElt_commute (by decide) (by decide) 1 a).eq

theorem rootElt01_conj_tLn (b : F) :
    rootElt 0 1 (1 : F) * tLn 0 b * (rootElt 0 1 1)⁻¹ = tLn b b := by
  have h := rootElt_commutator (show (0 : Fin 3) ≠ 1 by decide) (show (1 : Fin 3) ≠ 2 by decide)
    (show (0 : Fin 3) ≠ 2 by decide) (1 : F) b
  rw [commutatorElement_def, one_mul] at h
  rw [tLn_zero_left, tLn, ← h]
  group

theorem diagPt_conj_tLn (l : F) (hl : l ≠ 0) (a : F) :
    diagPt l hl * tLn a 0 * (diagPt l hl)⁻¹ = tLn (l * a) 0 := by
  rw [tLn_zero_right, tLn_zero_right, diagPt_conj_rootElt]

theorem tLn_split (a b : F) : tLn a b = tLn a 0 * tLn 0 b := by
  rw [tLn_mul, add_zero, zero_add]

section CharTwoLemmas

variable [CharP F 2]

theorem tLn_mul_self (a b : F) : tLn a b * tLn a b = 1 := by
  rw [tLn_mul, CharTwo.add_self_eq_zero, CharTwo.add_self_eq_zero, tLn, rootElt_zero,
    rootElt_zero, one_mul]

theorem phi_eq_zero [Finite F] (φ : F → F → F) (hadd : ∀ a a' b, φ (a + a') b = φ a b + φ a' b)
    (hadd' : ∀ a b b', φ a (b + b') = φ a b + φ a b') (halt : ∀ a, φ a a = 0)
    (hscale : ∀ l a b, l ≠ 0 → φ (l * a) (l * b) = l * φ a b) : ∀ a b, φ a b = 0 := by
  have h0l : ∀ b, φ 0 b = 0 := fun b => by simpa using hadd 0 0 b
  have hscale' : ∀ l a b, φ (l * a) (l * b) = l * φ a b := fun l a b => by
    by_cases hl : l = 0
    · simp [hl, h0l]
    · exact hscale l a b hl
  have key : ∀ l m a b, φ (l * a) (m * b) = φ (m * a) (l * b) := fun l m a b => by
    have e := hscale' (l + m) a b
    simp only [add_mul, hadd, hadd', hscale'] at e
    have e2 : φ (l * a) (m * b) + φ (m * a) (l * b) = 0 := by
      have : l * φ a b + φ (l * a) (m * b) + (φ (m * a) (l * b) + m * φ a b) =
          l * φ a b + m * φ a b := e
      linear_combination this
    rw [← CharTwo.sub_eq_add] at e2
    exact sub_eq_zero.mp e2
  have hsym : ∀ x y, φ x y = φ (y * x) 1 := fun x y => by
    have := key y 1 x 1
    simpa using this.symm
  have hz : ∀ z, φ z 1 = 0 := fun z => by
    obtain ⟨w, rfl⟩ := (surjective_frobenius F 2) z
    rw [frobenius_def, sq, ← hsym, halt]
  intro a b
  rw [hsym, hz]

theorem swap01_conj_tLn_left (a : F) : swap01 * tLn a 0 * swap01⁻¹ = tLn 0 a := by
  rw [tLn_zero_right, tLn_zero_left, swap01_conj_rootElt02]

theorem swap01_conj_tLn_right (b : F) : swap01 * tLn 0 b * swap01⁻¹ = tLn b 0 := by
  rw [tLn_zero_right, tLn_zero_left, swap01_conj_rootElt12]

end CharTwoLemmas

private theorem vec_zero (a b : F) : (![a * 0, b * 0, 0] : Fin 3 → F) = 0 := by
  funext k
  fin_cases k <;> simp

section Module

variable {V : Type*} [CommGroup V] {ρ : SL3 F →* MulAut V}

theorem act_dc_eq (g h : SL3 F) (w : V) : ρ g (dc ρ h w) = dc ρ (g * h * g⁻¹) (ρ g w) := by
  rw [dc_conj]
  congr 2
  rw [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one, MulAut.one_apply]

theorem act_dc_of_commute {g h : SL3 F} (hgh : g * h = h * g) (w : V) :
    ρ g (dc ρ h w) = dc ρ h (ρ g w) := by
  rw [act_dc_eq, hgh, mul_inv_cancel_right]

theorem dc_dc_tLn_mul_right (a b a' b' : F) (v w : V) :
    dc ρ (tLn a b) (dc ρ (tLn a' b') (v * w)) =
      dc ρ (tLn a b) (dc ρ (tLn a' b') v) * dc ρ (tLn a b) (dc ρ (tLn a' b') w) := by
  rw [dc_mul_right, dc_mul_right]

theorem dc_dc_conj (h g g' : SL3 F) (v : V) :
    dc ρ (h * g * h⁻¹) (dc ρ (h * g' * h⁻¹) v) = ρ h (dc ρ g (dc ρ g' (ρ h⁻¹ v))) := by
  rw [dc_conj, dc_conj]
  congr 2
  rw [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one, MulAut.one_apply]

namespace NatNatExt

variable (E : NatNatExt ρ)
include E

@[expose] def InL0 (v : V) : Prop := Multiplicative.toAdd (E.β v) 2 = 0

theorem toAdd_β_dc_tLn (a b : F) (v : V) :
    Multiplicative.toAdd (E.β (dc ρ (tLn a b) v)) =
      ![a * Multiplicative.toAdd (E.β v) 2, b * Multiplicative.toAdd (E.β v) 2, 0] := by
  rw [E.toAdd_β_dc, tLn_mulVec, add_sub_cancel_left]

theorem dc_tLn_ι (a b : F) (y : Fin 3 → F) :
    dc ρ (tLn a b) (E.ι (Multiplicative.ofAdd y)) =
      E.ι (Multiplicative.ofAdd ![a * y 2, b * y 2, 0]) := by
  rw [E.dc_ι, tLn_mulVec, add_sub_cancel_left]

theorem dc_tLn_ι_of_two {y : Fin 3 → F} (hy : y 2 = 0) (a b : F) :
    dc ρ (tLn a b) (E.ι (Multiplicative.ofAdd y)) = 1 := by
  rw [E.dc_tLn_ι, hy, vec_zero, ofAdd_zero, map_one E.ι]

theorem inL0_dc_tLn (a b : F) (v : V) : E.InL0 (dc ρ (tLn a b) v) := by
  rw [InL0, E.toAdd_β_dc_tLn]
  rfl

theorem inL0_dc_of_two {g : SL3 F}
    (hg : ∀ x : Fin 3 → F, (((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ x) 2 = x 2) (v : V) :
    E.InL0 (dc ρ g v) := by
  rw [InL0, E.toAdd_β_dc, Pi.sub_apply, hg, sub_self]

theorem exists_ι_eq {v : V} (hv : E.β v = 1) :
    ∃ y : Fin 3 → F, E.ι (Multiplicative.ofAdd y) = v := by
  obtain ⟨m, hm⟩ := (E.mem_range_ι_iff v).mpr hv
  exact ⟨Multiplicative.toAdd m, hm⟩

theorem ι_ofAdd_inj {y y' : Fin 3 → F}
    (h : E.ι (Multiplicative.ofAdd y) = E.ι (Multiplicative.ofAdd y')) : y = y' :=
  Multiplicative.ofAdd.injective (E.ι_injective h)

theorem ι_ofAdd_eq_one {y : Fin 3 → F} (h : E.ι (Multiplicative.ofAdd y) = 1) : y = 0 := by
  rw [← map_one E.ι, ← ofAdd_zero] at h
  exact E.ι_ofAdd_inj h

variable [CharP F 2]

variable (hV : ∀ v : V, v ^ 2 = 1)
include hV

theorem exists_dc_tLn_eq_of_inL0 {u : V} (hu : E.InL0 u) (a b : F) :
    ∃ y : Fin 3 → F, y 2 = 0 ∧ dc ρ (tLn a b) u = E.ι (Multiplicative.ofAdd y) := by
  have h1 : E.β (dc ρ (tLn a b) u) = 1 := by
    apply Multiplicative.toAdd.injective
    rw [E.toAdd_β_dc_tLn, show Multiplicative.toAdd (E.β u) 2 = 0 from hu, vec_zero, toAdd_one]
  obtain ⟨y, hy⟩ := E.exists_ι_eq h1
  by_cases hab : a = 0 ∧ b = 0
  · obtain ⟨rfl, rfl⟩ := hab
    refine ⟨0, rfl, ?_⟩
    rw [show tLn (0 : F) 0 = 1 by simp [tLn], dc_one_left, ofAdd_zero, map_one E.ι]
  · refine ⟨y, ?_, hy.symm⟩
    have h2 : dc ρ (tLn a b) (dc ρ (tLn a b) u) = 1 := dc_dc_self ρ hV (tLn_mul_self a b) u
    rw [← hy, E.dc_tLn_ι] at h2
    have h3 := E.ι_ofAdd_eq_one h2
    have ha : a * y 2 = 0 := by simpa using congrFun h3 0
    have hb : b * y 2 = 0 := by simpa using congrFun h3 1
    by_contra hy2
    exact hab ⟨(mul_eq_zero.mp ha).resolve_right hy2, (mul_eq_zero.mp hb).resolve_right hy2⟩

theorem exists_dc_dc_tLn_eq (a b a' b' : F) (v : V) :
    ∃ y : Fin 3 → F, y 2 = 0 ∧
      dc ρ (tLn a b) (dc ρ (tLn a' b') v) = E.ι (Multiplicative.ofAdd y) :=
  E.exists_dc_tLn_eq_of_inL0 hV (E.inL0_dc_tLn a' b' v) a b

theorem dc_dc_tLn_of_inL0 {u : V} (hu : E.InL0 u) (a b a' b' : F) :
    dc ρ (tLn a b) (dc ρ (tLn a' b') u) = 1 := by
  obtain ⟨y, hy2, hy⟩ := E.exists_dc_tLn_eq_of_inL0 hV hu a' b'
  rw [hy, E.dc_tLn_ι_of_two hy2]

theorem dc_dc_tLn_mul (a b a' b' a'' b'' : F) (v : V) :
    dc ρ (tLn a b * tLn a' b') (dc ρ (tLn a'' b'') v) =
      dc ρ (tLn a b) (dc ρ (tLn a'' b'') v) * dc ρ (tLn a' b') (dc ρ (tLn a'' b'') v) := by
  rw [dc_mul]
  obtain ⟨y, hy2, hy⟩ := E.exists_dc_dc_tLn_eq hV a' b' a'' b'' v
  rw [hy, E.dc_tLn_ι_of_two hy2, one_mul]

theorem dc_dc_tLn_mul' (a b a' b' a'' b'' : F) (v : V) :
    dc ρ (tLn a b) (dc ρ (tLn a' b' * tLn a'' b'') v) =
      dc ρ (tLn a b) (dc ρ (tLn a' b') v) * dc ρ (tLn a b) (dc ρ (tLn a'' b'') v) := by
  have hc : tLn a b * (tLn a' b' * tLn a'' b'') = (tLn a' b' * tLn a'' b'') * tLn a b := by
    rw [tLn_mul a' b' a'' b'', tLn_comm]
  rw [dc_dc_comm ρ hc, E.dc_dc_tLn_mul hV, dc_dc_comm ρ (tLn_comm a' b' a b),
    dc_dc_comm ρ (tLn_comm a'' b'' a b)]

theorem dc_dc_tLn_act {g : SL3 F}
    (hg : ∀ x : Fin 3 → F, (((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ x) 2 = x 2)
    (a b a' b' : F) (v : V) :
    dc ρ (tLn a b) (dc ρ (tLn a' b') (ρ g v)) = dc ρ (tLn a b) (dc ρ (tLn a' b') v) := by
  rw [act_eq_mul_dc, dc_dc_tLn_mul_right, E.dc_dc_tLn_of_inL0 hV (E.inL0_dc_of_two hg v),
    mul_one]

omit [CharP F 2] hV in
theorem ι_fixed_two {y : Fin 3 → F} (h : ρ (rootElt 0 1 (1 : F)) (E.ι (Multiplicative.ofAdd y)) =
    E.ι (Multiplicative.ofAdd y)) : y 1 = 0 := by
  rw [E.ι_equiv] at h
  have h2 := congrFun (E.ι_ofAdd_inj h) 0
  rw [rootElt_mulVec (by decide)] at h2
  simpa using h2

theorem exists_dc_dc_tLn_left (a b : F) (v : V) :
    ∃ y : Fin 3 → F, y 1 = 0 ∧ y 2 = 0 ∧
      dc ρ (tLn a 0) (dc ρ (tLn b 0) v) = E.ι (Multiplicative.ofAdd y) := by
  obtain ⟨y, hy2, hy⟩ := E.exists_dc_dc_tLn_eq hV a 0 b 0 v
  refine ⟨y, E.ι_fixed_two ?_, hy2, hy⟩
  rw [← hy, act_dc_of_commute (rootElt01_comm_tLn a), act_dc_of_commute (rootElt01_comm_tLn b),
    E.dc_dc_tLn_act hV rootElt01_mulVec_two]

theorem dc_dc_tLn_left [Finite F] (a b : F) (v : V) : dc ρ (tLn a 0) (dc ρ (tLn b 0) v) = 1 := by
  classical
  choose y hy1 hy2 hy using fun a b => E.exists_dc_dc_tLn_left hV a b v
  have hyv : ∀ a b, y a b = ![y a b 0, 0, 0] := fun a b => by
    funext k
    fin_cases k
    · rfl
    · exact hy1 a b
    · exact hy2 a b
  have hadd : ∀ a a' b, y (a + a') b 0 = y a b 0 + y a' b 0 := fun a a' b => by
    have h := E.dc_dc_tLn_mul hV a 0 a' 0 b 0 v
    rw [tLn_mul, add_zero, hy, hy, hy, ← map_mul, ← ofAdd_add] at h
    have := congrFun (E.ι_ofAdd_inj h) 0
    simpa using this
  have hsymm : ∀ a b, y a b = y b a := fun a b => by
    have h := dc_dc_comm ρ (tLn_comm a 0 b 0) v
    rw [hy, hy] at h
    exact E.ι_ofAdd_inj h
  have hadd' : ∀ a b b', y a (b + b') 0 = y a b 0 + y a b' 0 := fun a b b' => by
    rw [hsymm, hadd, hsymm b, hsymm b']
  have halt : ∀ a, y a a 0 = 0 := fun a => by
    have h := dc_dc_self ρ hV (tLn_mul_self a 0) v
    rw [hy] at h
    rw [E.ι_ofAdd_eq_one h]
    rfl
  have hscale : ∀ l a b, l ≠ 0 → y (l * a) (l * b) 0 = l * y a b 0 := fun l a b hl => by
    have h := dc_dc_conj (ρ := ρ) (diagPt l hl) (tLn a 0) (tLn b 0) v
    rw [diagPt_conj_tLn, diagPt_conj_tLn,
      E.dc_dc_tLn_act hV (mulVec_inv_two (diagPt_mulVec_two l hl)), hy, hy, E.ι_equiv] at h
    have := congrFun (E.ι_ofAdd_inj h) 0
    rw [diagPt_mulVec] at this
    simpa using this
  have hφ := phi_eq_zero (fun a b => y a b 0) hadd hadd' halt hscale
  rw [hy, hyv, hφ]
  have : (![0, 0, 0] : Fin 3 → F) = 0 := by
    funext k
    fin_cases k <;> rfl
  rw [this, ofAdd_zero, map_one]

theorem dc_dc_tLn_right [Finite F] (a b : F) (v : V) : dc ρ (tLn 0 a) (dc ρ (tLn 0 b) v) = 1 := by
  rw [← swap01_conj_tLn_left a, ← swap01_conj_tLn_left b, dc_dc_conj, E.dc_dc_tLn_left hV,
    map_one]

theorem exists_dc_dc_tLn_mixed [Finite F] (a b : F) (v : V) :
    ∃ y : Fin 3 → F, y 1 = 0 ∧ y 2 = 0 ∧
      dc ρ (tLn a 0) (dc ρ (tLn 0 b) v) = E.ι (Multiplicative.ofAdd y) := by
  obtain ⟨y, hy2, hy⟩ := E.exists_dc_dc_tLn_eq hV a 0 0 b v
  refine ⟨y, E.ι_fixed_two ?_, hy2, hy⟩
  rw [← hy, act_dc_of_commute (rootElt01_comm_tLn a), act_dc_eq, rootElt01_conj_tLn,
    E.dc_dc_tLn_act hV rootElt01_mulVec_two, show tLn b b = tLn b 0 * tLn 0 b from tLn_split b b,
    E.dc_dc_tLn_mul' hV, E.dc_dc_tLn_left hV, one_mul]

theorem dc_dc_tLn_mixed [Finite F] (a b : F) (v : V) : dc ρ (tLn a 0) (dc ρ (tLn 0 b) v) = 1 := by
  obtain ⟨y, hy1, hy2, hy⟩ := E.exists_dc_dc_tLn_mixed hV a b v
  obtain ⟨y', hy1', hy2', hy'⟩ := E.exists_dc_dc_tLn_mixed hV b a (ρ swap01⁻¹ v)
  have h := dc_dc_conj (ρ := ρ) swap01 (tLn 0 a) (tLn b 0) v
  rw [swap01_conj_tLn_right, swap01_conj_tLn_left, dc_dc_comm ρ (tLn_comm 0 a b 0), hy', hy,
    E.ι_equiv, swap01_mulVec] at h
  have h0 := congrFun (E.ι_ofAdd_inj h) 0
  simp only [Matrix.cons_val_zero] at h0
  have hy0 : y = 0 := by
    funext k
    fin_cases k
    · simpa [hy1'] using h0
    · exact hy1
    · exact hy2
  rw [hy, hy0, ofAdd_zero, map_one]

theorem dc_dc_qLn [Finite F] {t t' : SL3 F} (ht : t ∈ qLn) (ht' : t' ∈ qLn) (v : V) :
    dc ρ t (dc ρ t' v) = 1 := by
  obtain ⟨a, b, rfl⟩ := mem_qLn_iff_tLn.mp ht
  obtain ⟨a', b', rfl⟩ := mem_qLn_iff_tLn.mp ht'
  rw [tLn_split a b, E.dc_dc_tLn_mul hV, tLn_split a' b', E.dc_dc_tLn_mul' hV,
    E.dc_dc_tLn_mul' hV, E.dc_dc_tLn_left hV, E.dc_dc_tLn_mixed hV,
    dc_dc_comm ρ (tLn_comm 0 b a' 0), E.dc_dc_tLn_mixed hV, E.dc_dc_tLn_right hV]
  simp

end NatNatExt

end Module

end CFSG.Quasithin.MS93
