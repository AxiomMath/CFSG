module

public import CFSG.Sporadic.Schreier.Co1OrbEnumCheck
public import CFSG.Sporadic.Schreier.Co1Base
public import CFSG.Sporadic.Th.TableSpec

public section

namespace CFSG.Sporadic.Co1Schreier

open CFSG.Sporadic.SmallF2 (toVecD toVecD_injective)
open CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Th CFSG.Sporadic.Th.Native Matrix

@[expose] def kOrbit (K : Subgroup GL24) (v : Vec24) : Set Vec24 :=
  {w | ∃ g ∈ K, ((g : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ v = w}

@[expose] def ActsBy (P : GL24) (c : Array ℕ) : Prop :=
  ∀ v, ((P : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ toVecD 24 v = toVecD 24 (vecMulN 24 c v)

theorem MRep.actsBy {X : Native.Rows} {g : GL24} (h : MRep X g) :
    ActsBy g (transposeRows 24 X) := fun v => MRep.mulVec h v

theorem mem_kOrbit_self (K : Subgroup GL24) (v : Vec24) : v ∈ kOrbit K v := ⟨1, K.one_mem, by
  rw [Units.val_one, one_mulVec]⟩

theorem kOrbit_eq_of_mem {K : Subgroup GL24} {v w : Vec24} (h : w ∈ kOrbit K v) :
    kOrbit K w = kOrbit K v := by
  obtain ⟨g, hg, rfl⟩ := h
  ext u
  constructor
  · rintro ⟨h', hh', rfl⟩
    exact ⟨h' * g, K.mul_mem hh' hg, by rw [Units.val_mul, ← mulVec_mulVec]⟩
  · rintro ⟨h', hh', rfl⟩
    refine ⟨h' * g⁻¹, K.mul_mem hh' (K.inv_mem hg), ?_⟩
    rw [Units.val_mul, ← mulVec_mulVec,
      mulVec_mulVec (M := ((g⁻¹ : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2))), ← Units.val_mul,
      inv_mul_cancel, Units.val_one, one_mulVec]

theorem kOrbit_mono {K L : Subgroup GL24} (h : K ≤ L) (v : Vec24) : kOrbit K v ⊆ kOrbit L v := by
  rintro _ ⟨g, hg, rfl⟩
  exact ⟨g, h hg, rfl⟩

theorem inv_mapsTo {T : Set Vec24} (hT : T.Finite) {g : GL24}
    (h : ∀ w ∈ T, ((g : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ w ∈ T) :
    ∀ w ∈ T, ((g⁻¹ : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ w ∈ T := by
  have hinj : Set.InjOn (fun w => ((g : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ w) T :=
    fun v _ w _ hvw => by
      have := congrArg (fun u => ((g⁻¹ : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ u) hvw
      simpa only [mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        one_mulVec] using this
  have hbij := (hT.injOn_iff_bijOn_of_mapsTo h).mp hinj
  intro w hw
  obtain ⟨v, hv, rfl⟩ := hbij.surjOn hw
  simpa only [mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec] using hv

theorem closure_mapsTo {P Q : GL24} {T : Set Vec24} (hT : T.Finite)
    (hP : ∀ w ∈ T, ((P : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ w ∈ T)
    (hQ : ∀ w ∈ T, ((Q : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ w ∈ T) {g : GL24}
    (hg : g ∈ Subgroup.closure {P, Q}) :
    ∀ w ∈ T, ((g : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ w ∈ T := by
  replace hg : g ∈ Submonoid.closure ({P, Q} ∪ {P, Q}⁻¹) := by
    rw [← Subgroup.closure_toSubmonoid]
    exact hg
  induction hg using Submonoid.closure_induction with
  | mem y hy =>
    have hgen : ∀ x ∈ ({P, Q} : Set GL24), (∀ w ∈ T,
        ((x : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ w ∈ T) ∧
        ∀ w ∈ T, ((x⁻¹ : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ w ∈ T := by
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact ⟨hP, inv_mapsTo hT hP⟩
      · exact ⟨hQ, inv_mapsTo hT hQ⟩
    rcases hy with hy | hy
    · exact (hgen y hy).1
    · have := (hgen _ (Set.mem_inv.mp hy)).2
      rwa [inv_inv] at this
  | one =>
    intro w hw
    rwa [Units.val_one, one_mulVec]
  | mul x y _ _ hx hy =>
    intro w hw
    rw [Units.val_mul, ← mulVec_mulVec]
    exact hx _ (hy w hw)

variable {P Q : GL24} {cP cQ : Array ℕ} {root n : ℕ} {O : VOrbit}

@[expose] def enumSet (O : VOrbit) (n : ℕ) : Set Vec24 :=
  {w | ∃ i < n, w = toVecD 24 (O.pts[i]!)}

theorem enumOK_parts (h : Native.enumOK cP cQ root n O = true) :
    O.pts.size = n ∧
    (∀ i < n, O.pts[i]! < 2 ^ 24 ∧ ((posTable 24 O.pts)[O.pts[i]!]!).toNat = i ∧
      ap O.alpha i < n ∧ O.pts[ap O.alpha i]! = vecMulN 24 cP O.pts[i]! ∧
      ap O.beta i < n ∧ O.pts[ap O.beta i]! = vecMulN 24 cQ O.pts[i]!) ∧
    O.pts[0]! = root ∧
    (∀ j, 1 ≤ j → j < n → (Native.parentsOf O n)[j]! < j ∧
      (ap O.alpha (Native.parentsOf O n)[j]! = j ∨ ap O.beta (Native.parentsOf O n)[j]! = j)) := by
  simp only [Native.enumOK, vOrbitOK, Native.connOK, Bool.and_eq_true, beq_iff_eq,
    allIn_eq_true, decide_eq_true_eq, Bool.or_eq_true, Nat.zero_le, true_implies] at h
  obtain ⟨⟨⟨⟨⟨hs, -⟩, -⟩, hall⟩, h0⟩, hconn⟩ := h
  refine ⟨hs, fun i hi => ?_, h0, hconn⟩
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := hall i hi
  exact ⟨h1, h2, h3, h4, h5, h6⟩

theorem enumSet_finite (O : VOrbit) (n : ℕ) : (enumSet O n).Finite := by
  have : enumSet O n = (fun i => toVecD 24 (O.pts[i]!)) '' Set.Iio n := by
    ext w
    simp only [enumSet, Set.mem_image, Set.mem_Iio, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact ⟨i, hi, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨i, hi, rfl⟩
  rw [this]
  exact (Set.finite_Iio _).image _

theorem root_mem_enumSet (h : Native.enumOK cP cQ root n O = true) (hn : 0 < n) :
    toVecD 24 root ∈ enumSet O n :=
  ⟨0, hn, by rw [(enumOK_parts h).2.2.1]⟩

theorem enumSet_closed (hP : ActsBy P cP) (hQ : ActsBy Q cQ)
    (h : Native.enumOK cP cQ root n O = true) {g : GL24} (hg : g ∈ Subgroup.closure {P, Q}) :
    ∀ w ∈ enumSet O n, ((g : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ w ∈ enumSet O n := by
  obtain ⟨-, hall, -, -⟩ := enumOK_parts h
  refine closure_mapsTo (enumSet_finite O n) ?_ ?_ hg
  · rintro _ ⟨i, hi, rfl⟩
    obtain ⟨-, -, ha, hpa, -, -⟩ := hall i hi
    exact ⟨_, ha, by rw [hP, hpa]⟩
  · rintro _ ⟨i, hi, rfl⟩
    obtain ⟨-, -, -, -, hb, hpb⟩ := hall i hi
    exact ⟨_, hb, by rw [hQ, hpb]⟩

theorem enumSet_subset (hP : ActsBy P cP) (hQ : ActsBy Q cQ)
    (h : Native.enumOK cP cQ root n O = true) :
    enumSet O n ⊆ kOrbit (Subgroup.closure {P, Q}) (toVecD 24 root) := by
  obtain ⟨-, hall, h0, hconn⟩ := enumOK_parts h
  have hPm : P ∈ Subgroup.closure {P, Q} := Subgroup.subset_closure (Set.mem_insert _ _)
  have hQm : Q ∈ Subgroup.closure {P, Q} :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  have key : ∀ j < n,
      toVecD 24 (O.pts[j]!) ∈ kOrbit (Subgroup.closure {P, Q}) (toVecD 24 root) := by
    intro j
    induction j using Nat.strong_induction_on with
    | _ j ih =>
      intro hj
      rcases Nat.eq_zero_or_pos j with rfl | hpos
      · rw [h0]
        exact mem_kOrbit_self _ _
      · obtain ⟨hp, hab⟩ := hconn j hpos hj
        obtain ⟨g, hg, hgv⟩ := ih _ hp (hp.trans hj)
        obtain ⟨-, -, -, hpa, -, hpb⟩ := hall _ (hp.trans hj)
        rcases hab with ha | ha
        · refine ⟨P * g, Subgroup.mul_mem _ hPm hg, ?_⟩
          rw [Units.val_mul, ← mulVec_mulVec, hgv, hP, ← hpa, ha]
        · refine ⟨Q * g, Subgroup.mul_mem _ hQm hg, ?_⟩
          rw [Units.val_mul, ← mulVec_mulVec, hgv, hQ, ← hpb, ha]
  rintro _ ⟨i, hi, rfl⟩
  exact key i hi

theorem kOrbit_eq_enumSet (hP : ActsBy P cP) (hQ : ActsBy Q cQ)
    (h : Native.enumOK cP cQ root n O = true) (hn : 0 < n) :
    kOrbit (Subgroup.closure {P, Q}) (toVecD 24 root) = enumSet O n := by
  refine le_antisymm ?_ (enumSet_subset hP hQ h)
  rintro _ ⟨g, hg, rfl⟩
  exact enumSet_closed hP hQ h hg _ (root_mem_enumSet h hn)

theorem enumSet_inj (h : Native.enumOK cP cQ root n O = true) {i j : ℕ} (hi : i < n)
    (hj : j < n) (hij : toVecD 24 (O.pts[i]!) = toVecD 24 (O.pts[j]!)) : i = j := by
  obtain ⟨-, hall, -, -⟩ := enumOK_parts h
  have hv := toVecD_injective (hall i hi).1 (hall j hj).1 hij
  rw [← (hall i hi).2.1, ← (hall j hj).2.1, hv]

@[expose] noncomputable def enumFin (O : VOrbit) (n : ℕ) : Finset Vec24 :=
  (Finset.range n).image fun i => toVecD 24 (O.pts[i]!)

theorem coe_enumFin (O : VOrbit) (n : ℕ) : (enumFin O n : Set Vec24) = enumSet O n := by
  ext w
  simp only [enumFin, Finset.coe_image, Finset.coe_range, Set.mem_image, Set.mem_Iio, enumSet,
    Set.mem_ofPred_eq]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, hi, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, hi, rfl⟩

theorem card_enumFin (h : Native.enumOK cP cQ root n O = true) : (enumFin O n).card = n := by
  rw [enumFin, Finset.card_image_of_injOn (fun i hi j hj hij => enumSet_inj h
    (Finset.mem_range.mp (Finset.mem_coe.mp hi)) (Finset.mem_range.mp (Finset.mem_coe.mp hj)) hij),
    Finset.card_range]

theorem ncard_enumSet (h : Native.enumOK cP cQ root n O = true) : (enumSet O n).ncard = n := by
  rw [← coe_enumFin, Set.ncard_coe_finset, card_enumFin h]

end CFSG.Sporadic.Co1Schreier
