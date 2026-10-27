module

public import CFSG.Quasithin.Background.HFixSylBase
public import CFSG.Quasithin.Background.H16TwoM22Check

public section

namespace CFSG.Quasithin.H.FixSyl

open CFSG.Monster.Code CFSG.Quasithin.H.Mathieu

theorem permOfArr_mul_self {a : Array ℕ} (h : InvPairOK 24 a a = true) :
    permOfArr 24 a a h * permOfArr 24 a a h = 1 := by
  refine Equiv.ext fun i => Fin.ext ?_
  rw [Equiv.Perm.mul_apply, permOfArr_val, permOfArr_val, Equiv.Perm.one_apply]
  exact (invPairOK_spec h i i.2).2.2.1

theorem permOfArr_comm {a b : Array ℕ} (ha : InvPairOK 24 a a = true)
    (hb : InvPairOK 24 b b = true) (h : ∀ j < 24, a[b[j]!]! = b[a[j]!]!) :
    permOfArr 24 a a ha * permOfArr 24 b b hb = permOfArr 24 b b hb * permOfArr 24 a a ha := by
  refine Equiv.ext fun i => Fin.ext ?_
  rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, permOfArr_val, permOfArr_val, permOfArr_val,
    permOfArr_val]
  exact h i i.2

@[expose] def koT : Fin 4 → Fin 16 := ![1, 2, 4, 8]

theorem koArr_comm : ∀ i k : Fin 4, ∀ j < 24,
    (koArr (koT i))[(koArr (koT k))[j]!]! = (koArr (koT k))[(koArr (koT i))[j]!]! := by
  decide +kernel

theorem koPerm_comm (i k : Fin 4) :
    koPerm (koT i) * koPerm (koT k) = koPerm (koT k) * koPerm (koT i) :=
  permOfArr_comm _ _ (koArr_comm i k)

theorem koPerm_mul_self (t : Fin 16) : koPerm t * koPerm t = 1 :=
  permOfArr_mul_self _

theorem koRho_comm (i k : Fin 4) :
    koRho (koT i) * koRho (koT k) = koRho (koT k) * koRho (koT i) := by
  let a : ↥mog22 := ⟨koPerm (koT i), koPerm_mem_mog22 (koT i)⟩
  let b : ↥mog22 := ⟨koPerm (koT k), koPerm_mem_mog22 (koT k)⟩
  have h : a * b = b * a := Subtype.ext (koPerm_comm i k)
  have h2 := congrArg (rhoC10 mog22 mog22_le_mog22plus) h
  rw [map_mul, map_mul] at h2
  exact h2

theorem koRho_mul_self (t : Fin 16) : koRho t * koRho t = 1 := by
  let a : ↥mog22 := ⟨koPerm t, koPerm_mem_mog22 t⟩
  have h : a * a = 1 := Subtype.ext (koPerm_mul_self t)
  have h2 := congrArg (rhoC10 mog22 mog22_le_mog22plus) h
  rw [map_mul, map_one] at h2
  exact h2

theorem card_fixV_sylow_le_two_code22 {V : Type*} [CommGroup V]
    [Finite V] {H S : Subgroup (MulAut V)} (h : MathieuCode22 H ⊤ ⊥) (hSH : S ≤ H)
    (hS : Nat.card ↥S = 2 ^ (Nat.card ↥H).factorization 2) : Nat.card ↥(fixV S) ≤ 2 := by
  obtain ⟨e, he⟩ := code22_std h
  refine card_fixV_le_two_of_gens e hSH hS (s := Set.range fun i => koRho (koT i)) ?_ ?_ ?_
    (toW 10 1) fun w hw => (fix_koRho w).1 ⟨hw _ ⟨0, rfl⟩, hw _ ⟨1, rfl⟩, hw _ ⟨2, rfl⟩,
      hw _ ⟨3, rfl⟩⟩
  · rw [he]
    rintro _ ⟨i, rfl⟩
    exact ⟨_, rfl⟩
  · rintro _ ⟨i, rfl⟩ _ ⟨k, rfl⟩
    exact koRho_comm i k
  · rintro _ ⟨i, rfl⟩
    exact koRho_mul_self _

@[expose] def koMat11 (i : ℕ) : List ℕ :=
  [[514, 513, 519, 523, 531, 47, 87, 143, 280, 512, 1027],
    [1026, 1025, 1031, 1035, 1043, 56, 79, 151, 271, 515, 1024],
    [1, 2, 8, 4, 31, 544, 1088, 640, 1280, 512, 1024],
    [1, 2, 16, 31, 4, 1568, 576, 1152, 1792, 512, 1024]].getD i []

theorem koMat11_eq : ∀ i : Fin 4, matOf 11 (actC11 (koArr (koT i))) = koMat11 i := by
  decide +kernel

theorem koMat11_fix : ∀ m < 2 ^ 11, (∀ i < 4, actM (koMat11 i) m = m) → m = 0 ∨ m = 3 := by
  decide +kernel

@[expose] noncomputable def koRho11 (i : Fin 4) : MulAut W11 :=
  rhoC11 AutPerm le_rfl ⟨koPerm (koT i), (koPerm_mem_mog22 (koT i)).1.1⟩

theorem koRho11_comm (i k : Fin 4) : koRho11 i * koRho11 k = koRho11 k * koRho11 i := by
  let a : ↥AutPerm := ⟨koPerm (koT i), (koPerm_mem_mog22 (koT i)).1.1⟩
  let b : ↥AutPerm := ⟨koPerm (koT k), (koPerm_mem_mog22 (koT k)).1.1⟩
  have h : a * b = b * a := Subtype.ext (koPerm_comm i k)
  have h2 := congrArg (rhoC11 AutPerm le_rfl) h
  rw [map_mul, map_mul] at h2
  exact h2

theorem koRho11_mul_self (i : Fin 4) : koRho11 i * koRho11 i = 1 := by
  let a : ↥AutPerm := ⟨koPerm (koT i), (koPerm_mem_mog22 (koT i)).1.1⟩
  have h : a * a = 1 := Subtype.ext (koPerm_mul_self _)
  have h2 := congrArg (rhoC11 AutPerm le_rfl) h
  rw [map_mul, map_one] at h2
  exact h2

theorem fix_koRho11 (w : W11) (hw : ∀ i, koRho11 i w = w) : w = 1 ∨ w = toW 11 3 := by
  obtain ⟨m, hm, rfl⟩ := toW_surj 11 w
  have key : ∀ i : Fin 4, actC11 (koArr (koT i)) m = m := fun i =>
    toW_inj (actC11_lt _ _) hm (by
      rw [← rhoC11_toW AutPerm le_rfl ⟨koPerm (koT i), (koPerm_mem_mog22 (koT i)).1.1⟩
        (hasArr_permOfArr (koArr_ok (koT i)).1) m]
      exact hw i)
  rcases koMat11_fix m hm fun i hi => by
      rw [← koMat11_eq ⟨i, hi⟩, actM_matOf (xorLin_actC11 _) 11 m hm]
      exact key ⟨i, hi⟩ with h | h
  · left
    rw [h, toW_zero]
  · right
    rw [h]

theorem card_fixV_sylow_le_two_code24 {V : Type*} [CommGroup V] [Finite V]
    {H S : Subgroup (MulAut V)} (h : MathieuCode24 H ⊤ ⊥) (hSH : S ≤ H)
    (hS : Nat.card ↥S = 2 ^ (Nat.card ↥H).factorization 2) : Nat.card ↥(fixV S) ≤ 2 := by
  obtain ⟨e, he⟩ := code24_std h
  refine card_fixV_le_two_of_gens e hSH hS (s := Set.range koRho11) ?_ ?_ ?_ (toW 11 3)
    fun w hw => fix_koRho11 w fun i => hw _ ⟨i, rfl⟩
  · rw [he]
    rintro _ ⟨i, rfl⟩
    exact ⟨_, rfl⟩
  · rintro _ ⟨i, rfl⟩ _ ⟨k, rfl⟩
    exact koRho11_comm i k
  · rintro _ ⟨i, rfl⟩
    exact koRho11_mul_self i

@[expose] def ksWord (i : ℕ) : List ℕ :=
  [[0, 0, 1, 1, 1, 1], [0, 0, 2, 2, 2, 2], [0, 1, 0, 1, 2, 3], [0, 2, 0, 2, 3, 1],
    [1, 0, 0, 1, 3, 2], [2, 0, 0, 2, 1, 3]].getD i []

@[expose] def ksArr (i : ℕ) : Array ℕ :=
  ((List.range 24).map fun p => (p % 4 ^^^ (ksWord i).getD (p / 4) 0) + 4 * (p / 4)).toArray

theorem ksArr_ok : ∀ i : Fin 6, InvPairOK 24 (ksArr i) (ksArr i) = true ∧
    autArrOK (ksArr i) (ksArr i) = true := by
  decide +kernel

theorem ksArr_comm : ∀ i k : Fin 6, ∀ j < 24,
    (ksArr i)[(ksArr k)[j]!]! = (ksArr k)[(ksArr i)[j]!]! := by
  decide +kernel

@[expose] def ksMat (i : ℕ) : List ℕ :=
  [[1278, 1277, 228, 424, 336, 32, 64, 128, 256, 543, 1024],
    [990, 989, 452, 360, 176, 32, 64, 128, 256, 512, 1055],
    [1854, 1570, 1851, 616, 1104, 32, 64, 159, 256, 512, 1024],
    [1278, 1122, 1275, 1608, 560, 32, 64, 128, 287, 512, 1024],
    [897, 989, 987, 1672, 1296, 63, 64, 128, 256, 512, 1024],
    [1793, 1853, 1851, 1416, 656, 32, 95, 128, 256, 512, 1024]].getD i []

theorem ksMat_eq : ∀ i : Fin 6, matOf 11 (act11 (ksArr i)) = ksMat i := by
  decide +kernel

theorem ksMat_fix : ∀ m < 2 ^ 11, (∀ i < 6, actM (ksMat i) m = m) → m = 0 ∨ m = 31 := by
  decide +kernel

@[expose] def ksPerm (i : Fin 6) : Equiv.Perm (Fin 24) :=
  permOfArr 24 (ksArr i) (ksArr i) (ksArr_ok i).1

theorem ksPerm_mem (i : Fin 6) : ksPerm i ∈ AutPerm :=
  mem_AutPerm_of_arr _ (ksArr_ok i).2

@[expose] noncomputable def ksRho (i : Fin 6) : MulAut W11 :=
  rho11 AutPerm le_rfl ⟨ksPerm i, ksPerm_mem i⟩

theorem ksRho_comm (i k : Fin 6) : ksRho i * ksRho k = ksRho k * ksRho i := by
  let a : ↥AutPerm := ⟨ksPerm i, ksPerm_mem i⟩
  let b : ↥AutPerm := ⟨ksPerm k, ksPerm_mem k⟩
  have h : a * b = b * a :=
    Subtype.ext (permOfArr_comm (ksArr_ok i).1 (ksArr_ok k).1 (ksArr_comm i k))
  have h2 := congrArg (rho11 AutPerm le_rfl) h
  rw [map_mul, map_mul] at h2
  exact h2

theorem ksRho_mul_self (i : Fin 6) : ksRho i * ksRho i = 1 := by
  let a : ↥AutPerm := ⟨ksPerm i, ksPerm_mem i⟩
  have h : a * a = 1 := Subtype.ext (permOfArr_mul_self (ksArr_ok i).1)
  have h2 := congrArg (rho11 AutPerm le_rfl) h
  rw [map_mul, map_one] at h2
  exact h2

theorem fix_ksRho (w : W11) (hw : ∀ i, ksRho i w = w) : w = 1 ∨ w = toW 11 31 := by
  obtain ⟨m, hm, rfl⟩ := toW_surj 11 w
  have key : ∀ i : Fin 6, act11 (ksArr i) m = m := fun i =>
    toW_inj (act11_lt _ _) hm (by
      rw [← rho11_toW AutPerm le_rfl ⟨ksPerm i, ksPerm_mem i⟩ (hasArr_permOfArr (ksArr_ok i).1) m]
      exact hw i)
  rcases ksMat_fix m hm fun i hi => by
      rw [← ksMat_eq ⟨i, hi⟩, actM_matOf (xorLin_act11 _) 11 m hm]
      exact key ⟨i, hi⟩ with h | h
  · left
    rw [h, toW_zero]
  · right
    rw [h]

theorem card_fixV_sylow_le_two_cocode24 {V : Type*} [CommGroup V] [Finite V]
    {H S : Subgroup (MulAut V)} (h : MathieuCocode24 H ⊤ ⊥) (hSH : S ≤ H)
    (hS : Nat.card ↥S = 2 ^ (Nat.card ↥H).factorization 2) : Nat.card ↥(fixV S) ≤ 2 := by
  obtain ⟨e, he⟩ := cocode24_std h
  refine card_fixV_le_two_of_gens e hSH hS (s := Set.range ksRho) ?_ ?_ ?_ (toW 11 31)
    fun w hw => fix_ksRho w fun i => hw _ ⟨i, rfl⟩
  · rw [he]
    rintro _ ⟨i, rfl⟩
    exact ⟨_, rfl⟩
  · rintro _ ⟨i, rfl⟩ _ ⟨k, rfl⟩
    exact ksRho_comm i k
  · rintro _ ⟨i, rfl⟩
    exact ksRho_mul_self i

end CFSG.Quasithin.H.FixSyl
