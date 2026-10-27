module

public import CFSG.Quasithin.H13.L32NKGSp6Count

public section

namespace CFSG.Quasithin.H13.KGSp6

open CFSG.KGroups.Sp6

abbrev Mat6 : Type := Matrix (Fin 6) (Fin 6) (ZMod 2)

@[expose] def IsIso (M : Mat6) : Prop :=
  M.transpose * KGCert.g22Form * M = KGCert.g22Form

theorem isUnit_of_isIso {M : Mat6} (h : IsIso M) : IsUnit M := by
  have hJ := KGCert.g22Form_mul_self
  have h1 : (KGCert.g22Form * M.transpose * KGCert.g22Form) * M = 1 := by
    calc (KGCert.g22Form * M.transpose * KGCert.g22Form) * M
        = KGCert.g22Form * (M.transpose * KGCert.g22Form * M) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [h, hJ]
  have h2 : M * (KGCert.g22Form * M.transpose * KGCert.g22Form) = 1 := mul_eq_one_comm.1 h1
  exact ⟨⟨M, _, h2, h1⟩, rfl⟩

theorem IsIso.one : IsIso (1 : Mat6) := by
  unfold IsIso
  rw [Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one]

theorem IsIso.mul {A B : Mat6} (hA : IsIso A) (hB : IsIso B) : IsIso (A * B) := by
  unfold IsIso at *
  calc (A * B).transpose * KGCert.g22Form * (A * B)
      = B.transpose * (A.transpose * KGCert.g22Form * A) * B := by
        simp only [Matrix.transpose_mul, Matrix.mul_assoc]
    _ = KGCert.g22Form := by rw [hA, hB]

theorem IsIso.of_mul_eq_one {A A' : Mat6} (hA : IsIso A) (h : A * A' = 1) : IsIso A' := by
  unfold IsIso at *
  calc A'.transpose * KGCert.g22Form * A'
      = A'.transpose * (A.transpose * KGCert.g22Form * A) * A' := by rw [hA]
    _ = (A * A').transpose * KGCert.g22Form * (A * A') := by
        simp only [Matrix.transpose_mul, Matrix.mul_assoc]
    _ = KGCert.g22Form := by rw [h, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one]

@[expose] def SpU : Subgroup Mat6ˣ where
  carrier := {u | IsIso (u : Mat6)}
  one_mem' := IsIso.one
  mul_mem' := fun ha hb => IsIso.mul ha hb
  inv_mem' := fun {a} ha => IsIso.of_mul_eq_one ha (Units.mul_inv a)

theorem mem_SpU {u : Mat6ˣ} : u ∈ SpU ↔ IsIso (u : Mat6) := Iff.rfl

@[expose] def colsOf (M : Mat6) : List ℕ :=
  [KGCert.code6 fun i => M i 0, KGCert.code6 fun i => M i 1, KGCert.code6 fun i => M i 2,
    KGCert.code6 fun i => M i 3, KGCert.code6 fun i => M i 4, KGCert.code6 fun i => M i 5]

theorem validC_colsOf (M : Mat6) : KGCert.ValidC (colsOf M) := by
  refine ⟨rfl, fun c hc => ?_⟩
  simp only [colsOf, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> exact KGCert.code6_lt _

theorem decodeC_colsOf (M : Mat6) : KGCert.decodeC (colsOf M) = M := by
  ext i j
  fin_cases j <;> simp [KGCert.decodeC, colsOf, KGCert.vec6_code6]

theorem colsOf_decodeC {x : List ℕ} (hx : KGCert.ValidC x) : colsOf (KGCert.decodeC x) = x :=
  KGCert.decodeC_injOn (validC_colsOf _) hx (decodeC_colsOf _)

theorem colsOf_mem_spLeaves {u : Mat6ˣ} (hu : u ∈ SpU) : colsOf (u : Mat6) ∈ spLeaves 64 := by
  rw [mem_spLeaves_iff]
  refine ⟨validC_colsOf _, ?_⟩
  rw [decodeC_colsOf]
  exact hu

theorem exists_unit_of_mem_spLeaves {x : List ℕ} (hx : x ∈ spLeaves 64) :
    ∃ u ∈ SpU, colsOf (u : Mat6) = x := by
  obtain ⟨hv, hiso⟩ := mem_spLeaves_iff.1 hx
  obtain ⟨u, hu⟩ := isUnit_of_isIso hiso
  refine ⟨u, ?_, ?_⟩
  · rw [mem_SpU, hu]
    exact hiso
  · rw [hu]
    exact colsOf_decodeC hv

theorem colsOf_injective : Function.Injective fun u : Mat6ˣ => colsOf (u : Mat6) := by
  intro u v h
  apply Units.ext
  have := congrArg KGCert.decodeC h
  simpa [decodeC_colsOf] using this

theorem card_SpU_eq : Nat.card SpU = (spLeaves 64).length := by
  have himg : (fun u : Mat6ˣ => colsOf (u : Mat6)) '' (SpU : Set Mat6ˣ) =
      ↑(spLeaves 64).toFinset := by
    ext x
    simp only [Set.mem_image, SetLike.mem_coe, List.mem_toFinset]
    exact ⟨fun ⟨u, hu, hx⟩ => hx ▸ colsOf_mem_spLeaves hu, fun hx => exists_unit_of_mem_spLeaves hx⟩
  have h := Nat.card_coe_set_eq (SpU : Set Mat6ˣ)
  rw [← Set.ncard_image_of_injective _ colsOf_injective, himg, Set.ncard_coe_finset,
    List.toFinset_card_of_nodup (spLeaves_nodup 64)] at h
  exact h

theorem card_SpU (h1 : countCheck 64 1451520 = true) : Nat.card SpU = 1451520 := by
  rw [card_SpU_eq, length_of_countCheck h1]

@[expose] def Gsub : Subgroup Mat6ˣ where
  carrier := {u | (u : Mat6) ∈ KGCert.g22Mats}
  one_mem' := by simp
  mul_mem' := fun {a b} ha hb => by simpa using KGCert.g22Mats.mul_mem ha hb
  inv_mem' := fun {a} ha => by
    have hpow : (a⁻¹ : Mat6ˣ) = a ^ (orderOf a - 1) := by
      refine inv_eq_of_mul_eq_one_right ?_
      rw [← pow_succ', Nat.sub_add_cancel (orderOf_pos a)]
      exact pow_orderOf_eq_one a
    show ((a⁻¹ : Mat6ˣ) : Mat6) ∈ KGCert.g22Mats
    rw [hpow, Units.val_pow_eq_pow_val]
    exact KGCert.g22Mats.pow_mem ha _

theorem mem_Gsub {u : Mat6ˣ} : u ∈ Gsub ↔ (u : Mat6) ∈ KGCert.g22Mats := Iff.rfl

theorem card_Gsub : Nat.card Gsub = 12096 := by
  have e : Gsub ≃ KGCert.g22Mats := Equiv.ofBijective (fun u => ⟨(u : Mat6ˣ).val, u.2⟩)
    ⟨fun u v h => Subtype.ext (Units.ext (congrArg Subtype.val h)), fun M => by
      obtain ⟨u, hu⟩ := isUnit_of_isIso (KGCert.g22Mats_isometry _ M.2)
      exact ⟨⟨u, by rw [mem_Gsub, hu]; exact M.2⟩, Subtype.ext hu⟩⟩
  rw [Nat.card_congr e]
  exact KGCert.card_g22Mats

end CFSG.Quasithin.H13.KGSp6
