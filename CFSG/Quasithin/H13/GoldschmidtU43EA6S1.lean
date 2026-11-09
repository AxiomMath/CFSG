module

public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import CFSG.Permutation.FinPackDec

public section

namespace CFSG.Quasithin.H13.U43

open CFSG.Permutation.FinPack

@[expose] def a6CubeCodes : List ℕ :=
  [5517840, 3490320, 4411920, 5391120, 2380560, 5448720, 2438160, 3417360, 4338960, 5509920,
    5321760, 1324320, 5513520, 5325360, 1331760, 5386560, 5444160, 1389120, 2371920, 3412560,
    4272720, 5517345, 3489825, 4411425, 5505585, 2425905, 4326705, 5255745, 2118465, 3155265,
    275025, 148305, 205905, 5517570, 3490050, 4411650, 5505810, 5256210, 275730, 1070130, 83250,
    1377090, 202050, 4260690, 3150930, 5509635, 2429955, 4330755, 5513235, 5259795, 283155, 87075,
    1066275, 1384515, 151875, 4268115, 2113875, 5321220, 2183940, 3220740, 5386260, 5440020, 340500,
    332580, 1246500, 1200180, 336180, 3280980, 2294100, 1323525, 1196805, 1254405, 2371605, 3408405,
    4207125, 4199205, 3212325, 2179125, 4202805, 2297925, 3277125]

local notation "e6" => enc (1 : Equiv.Perm (Fin 6))

@[expose] def a6Ord4Codes : List ℕ :=
  [2441985, 4346625, 3482625, 2315265, 4400385, 3294465, 4522785, 3167265, 214305, 4530225, 152625,
    2114865, 3297345, 336705, 2295105, 2310225, 4203345, 3277905, 4526850, 3232770, 1262850,
    1392690, 4280370, 4522290, 332850, 4199730, 3477570, 1265730, 3166530, 86850, 3212610, 4395090,
    3227730, 213330, 1065810, 1246290, 4530435, 1201155, 2180355, 4526115, 344355, 4215075, 1377315,
    4261155, 2183235, 2425155, 1180995, 2102595, 75075, 1196115, 4325715, 2163795, 136275, 1057875,
    3297540, 1385220, 2299140, 3231780, 3473700, 217380, 1069860, 3151140, 2428980, 2117940,
    2164020, 136500, 1058100, 1253460, 3154260, 1180500, 2102100, 74580, 2310405, 4268805, 3281925,
    1261605, 4391205, 3162405, 82725, 201765, 4329525, 147765, 1180725, 2102325, 74805, 3219525,
    205125, 2163525, 136005, 1057605]

theorem a6Ord4Codes_complete : ∀ v : Equiv.Perm (Fin 6), Equiv.Perm.sign v = 1 → v ^ 4 = 1 →
    v ^ 2 ≠ 1 → enc v ∈ a6Ord4Codes := by
  have hw : walkK 6 (fun b => !evenK 6 b || !Nat.beq (powK 6 e6 b 4) e6 || Nat.beq (powK 6 e6 b 2) e6 ||
      memK b a6Ord4Codes) 6 0 0 0 = true := by
    decide +kernel
  have hn : 6 ≤ 16 := by norm_num
  intro v hv hv4 hv2
  have h := walkK_sound hw v
  simp only [evenK_enc_eq_decide hn, beq_enc_eq_decide hn, powK_enc hn, hv, hv4, hv2, decide_true,
    decide_false, Bool.not_true, Bool.false_or] at h
  exact memK_iff.1 h

theorem A6_dihedral_cyclic_perm : ∀ u v : Equiv.Perm (Fin 6), Equiv.Perm.sign u = 1 →
    Equiv.Perm.sign v = 1 → u ^ 2 = 1 → v ^ 4 = 1 → v ^ 2 ≠ 1 → u * v * u⁻¹ = v⁻¹ →
    (∃ m : Equiv.Perm (Fin 6), m ^ 3 = 1 ∧ m * v ^ 2 = u * m ∧ m * u = (v ^ 2 * u) * m) ∧
    (∃ m : Equiv.Perm (Fin 6), m ^ 3 = 1 ∧ m * v ^ 2 = (u * v) * m ∧
      m * (u * v) = (v ^ 2 * (u * v)) * m) := by
  have hw : walkK 6 (fun a => !evenK 6 a || !Nat.beq (powK 6 e6 a 2) e6 ||
      allK (fun b => !Nat.beq (mulK 6 (mulK 6 a b) (invCK 6 a)) (invCK 6 b) ||
        (anyK (fun d => permValidK 6 d && (Nat.beq (powK 6 e6 d 3) e6 &&
            Nat.beq (mulK 6 d (powK 6 e6 b 2)) (mulK 6 a d) &&
            Nat.beq (mulK 6 d a) (mulK 6 (mulK 6 (powK 6 e6 b 2) a) d))) a6CubeCodes &&
          anyK (fun d => permValidK 6 d && (Nat.beq (powK 6 e6 d 3) e6 &&
            Nat.beq (mulK 6 d (powK 6 e6 b 2)) (mulK 6 (mulK 6 a b) d) &&
            Nat.beq (mulK 6 d (mulK 6 a b)) (mulK 6 (mulK 6 (powK 6 e6 b 2) (mulK 6 a b)) d)))
            a6CubeCodes)) a6Ord4Codes) 6 0 0 0 = true := by
    decide +kernel
  have hn : 6 ≤ 16 := by norm_num
  intro u v hu hv hu2 hv4 hv2 huv
  have hvm := a6Ord4Codes_complete v hv hv4 hv2
  have h := walkK_sound hw u
  simp only [evenK_enc_eq_decide hn, beq_enc_eq_decide hn, powK_enc hn, hu, hu2, decide_true,
    Bool.not_true, Bool.false_or] at h
  have h' := allK_iff.1 h _ hvm
  simp only [beq_enc_eq_decide hn, powK_enc hn, mulK_enc hn, invCK_enc hn, huv, decide_true,
    Bool.not_true, Bool.false_or, Bool.and_eq_true] at h'
  obtain ⟨h1, h2⟩ := h'
  obtain ⟨m1, hm1⟩ := exists_of_anyK_valid h1
  obtain ⟨m2, hm2⟩ := exists_of_anyK_valid h2
  simp only [beq_enc_eq_decide hn, powK_enc hn, mulK_enc hn, Bool.and_eq_true,
    decide_eq_true_eq] at hm1 hm2
  exact ⟨⟨m1, hm1.1.1, hm1.1.2, hm1.2⟩, ⟨m2, hm2.1.1, hm2.1.2, hm2.2⟩⟩

set_option maxRecDepth 100000 in
set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 200000 in
theorem A6_dihedral_cyclic : ∀ u v : alternatingGroup (Fin 6), u ^ 2 = 1 → v ^ 4 = 1 →
    v ^ 2 ≠ 1 → u * v * u⁻¹ = v⁻¹ →
    (∃ m : alternatingGroup (Fin 6), m ^ 3 = 1 ∧ m * v ^ 2 = u * m ∧ m * u = (v ^ 2 * u) * m) ∧
    (∃ m : alternatingGroup (Fin 6), m ^ 3 = 1 ∧ m * v ^ 2 = (u * v) * m ∧
      m * (u * v) = (v ^ 2 * (u * v)) * m) := by
  intro u v hu2 hv4 hv2 huv
  have c := fun {x y : alternatingGroup (Fin 6)} (h : x = y) => congrArg Subtype.val h
  obtain ⟨⟨m1, h11, h12, h13⟩, ⟨m2, h21, h22, h23⟩⟩ := A6_dihedral_cyclic_perm u v
    (Equiv.Perm.mem_alternatingGroup.1 u.2) (Equiv.Perm.mem_alternatingGroup.1 v.2)
    (by simpa using c hu2) (by simpa using c hv4)
    (fun h => hv2 (Subtype.ext (by simpa using h))) (by simpa using c huv)
  have hm1 : Equiv.Perm.sign m1 = 1 := by
    have := congrArg Equiv.Perm.sign h11
    rw [map_pow, map_one] at this
    rcases Int.units_eq_one_or (Equiv.Perm.sign m1) with h | h
    · exact h
    · rw [h] at this; exact absurd this (by decide)
  have hm2 : Equiv.Perm.sign m2 = 1 := by
    have := congrArg Equiv.Perm.sign h21
    rw [map_pow, map_one] at this
    rcases Int.units_eq_one_or (Equiv.Perm.sign m2) with h | h
    · exact h
    · rw [h] at this; exact absurd this (by decide)
  refine ⟨⟨⟨m1, Equiv.Perm.mem_alternatingGroup.2 hm1⟩, ?_, ?_, ?_⟩,
    ⟨⟨m2, Equiv.Perm.mem_alternatingGroup.2 hm2⟩, ?_, ?_, ?_⟩⟩ <;>
    apply Subtype.ext <;> simpa

end CFSG.Quasithin.H13.U43
