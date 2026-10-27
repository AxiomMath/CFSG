module

public import CFSG.Quasithin.Background.HMathieuM21

public section

namespace CFSG.Quasithin.H.Mathieu.H16Pf

open CFSG.Monster.Code CFSG.Quasithin.H.Mathieu Pointwise

@[expose] def gArrs : List (Array ℕ) :=
  [#[0, 1, 14, 12, 4, 18, 16, 7, 23, 22, 9, 10, 5, 19, 6, 17, 2, 15, 3, 13, 21, 8, 11, 20],
    #[0, 1, 19, 18, 7, 6, 20, 21, 15, 9, 12, 11, 14, 8, 10, 13, 2, 3, 17, 16, 5, 4, 22, 23]]

@[expose] def gInvs : List (Array ℕ) :=
  [#[0, 1, 16, 18, 4, 12, 14, 7, 21, 10, 11, 22, 3, 19, 2, 17, 6, 15, 5, 13, 23, 20, 9, 8],
    #[0, 1, 16, 17, 21, 20, 5, 4, 13, 9, 14, 11, 10, 15, 12, 8, 19, 18, 3, 2, 6, 7, 22, 23]]

@[expose] def bfsH : List (ℕ × ℕ × ℕ) :=
  [(252, 0, 0), (348304, 0, 0), (3932352, 1, 0), (2245764, 1, 1), (2171272, 0, 2),
    (3342384, 1, 2), (50112, 0, 3), (2626584, 1, 3), (8917380, 0, 4), (2392340, 1, 4),
    (12779712, 0, 6), (3188224, 1, 6), (13104, 0, 7), (9461920, 0, 8), (11124736, 1, 8),
    (8536344, 0, 9), (696464, 1, 9), (1149060, 0, 10), (15728652, 1, 10), (6947584, 0, 11),
    (13369392, 0, 12), (10487136, 1, 13), (1188164, 0, 14), (8463380, 1, 14), (9474128, 0, 15),
    (8684680, 1, 15), (2631716, 1, 17), (3168512, 0, 18), (12626176, 0, 19), (4293144, 1, 19),
    (1320984, 0, 20), (9765632, 0, 21), (1605928, 1, 22), (1589780, 0, 23), (1184392, 0, 25),
    (10891264, 1, 25), (812288, 0, 26), (592208, 1, 26), (52272, 1, 27), (10095616, 0, 28),
    (4331540, 0, 29), (4465284, 1, 29), (395680, 1, 30), (8552996, 1, 31), (368736, 1, 32),
    (6316112, 0, 33), (591520, 1, 33), (6328480, 0, 34), (2376232, 1, 34), (8921672, 0, 36),
    (234752, 1, 36), (394832, 0, 38), (15552, 1, 38), (8460328, 1, 39), (4737160, 1, 40),
    (2263112, 1, 42), (5685248, 0, 43), (983052, 0, 44), (5244304, 1, 45), (2167364, 1, 46),
    (4460872, 0, 48), (5844992, 0, 49), (61452, 1, 50), (1315876, 0, 53), (8669252, 1, 53),
    (6622208, 1, 54), (4334632, 1, 56), (10488464, 0, 58), (4276516, 0, 59), (675936, 0, 62),
    (1131592, 0, 64), (3852, 0, 65), (825856, 0, 66), (4752452, 1, 68), (12604928, 0, 71),
    (223744, 1, 72), (5245536, 0, 74)]

@[expose] def bfs4 : List (ℕ × ℕ × ℕ) :=
  [(60, 0, 0), (282640, 0, 0), (786624, 1, 0), (120, 0, 1), (148608, 1, 1), (73864, 0, 2),
    (3342336, 1, 2), (331792, 0, 3), (1310912, 1, 3), (33472, 0, 4), (2102280, 1, 4),
    (528516, 0, 5), (2359556, 1, 5), (2130180, 0, 6), (147588, 1, 7), (2162824, 0, 8),
    (3276832, 1, 8), (4391040, 0, 9), (3154432, 1, 9), (4896, 0, 10), (24736, 0, 11),
    (2703360, 1, 11), (8405256, 0, 12), (688144, 1, 12), (8536320, 0, 13), (565264, 1, 13),
    (49344, 0, 14), (2622472, 1, 14), (4484, 0, 15), (2359316, 1, 15), (2392320, 0, 16),
    (34948, 0, 17), (6291468, 1, 17), (6816000, 0, 18), (816, 1, 18), (12845088, 0, 19),
    (49728, 1, 19), (2098496, 1, 20), (8516, 0, 21), (66580, 1, 21), (9441344, 0, 22),
    (8684544, 1, 22), (172048, 0, 23), (9470016, 0, 24), (8422408, 1, 24), (663568, 0, 25),
    (74112, 1, 25), (196800, 0, 26), (3154944, 1, 26), (13056, 0, 27), (8405152, 0, 28),
    (2670592, 1, 28), (16664, 0, 29), (655504, 1, 29), (8519944, 0, 30), (2631680, 1, 31),
    (22784, 0, 32), (4980752, 1, 32), (8399104, 0, 33), (4292624, 1, 33), (12845072, 0, 34),
    (1312776, 0, 35), (12714048, 1, 35), (4390976, 0, 36), (1058304, 1, 36), (8454912, 0, 37),
    (1085456, 1, 37), (8994816, 0, 38), (1605888, 1, 38), (16916, 0, 39), (3211296, 0, 40),
    (9453600, 1, 40), (1180168, 0, 41), (8531968, 1, 41), (8584, 1, 42), (9445408, 1, 43),
    (1184256, 0, 44), (8663040, 1, 44)]

@[expose] def bfs2 : List (ℕ × ℕ × ℕ) :=
  [(192, 0, 0), (65664, 0, 0), (3145728, 1, 0), (132, 0, 1), (2097156, 1, 1), (2097408, 0, 2),
    (48, 1, 2), (16512, 0, 3), (2621440, 1, 3), (16640, 0, 4), (524304, 1, 4), (8388864, 0, 5),
    (32784, 1, 5), (262160, 0, 6), (2098176, 1, 7), (8448, 0, 8), (65552, 1, 8), (8388672, 0, 9),
    (33792, 1, 9), (8208, 0, 10), (9437184, 0, 11), (8421376, 1, 11), (131088, 0, 12),
    (8320, 1, 12), (24, 0, 13), (131200, 1, 13), (768, 0, 14), (4112, 1, 14), (8912896, 0, 15),
    (33024, 1, 15), (20, 0, 16), (1114112, 0, 17), (131584, 0, 18), (12288, 1, 18), (384, 1, 19),
    (8388640, 1, 20), (1179648, 0, 21), (8396800, 1, 21), (136, 1, 22), (524416, 0, 23),
    (262272, 1, 24), (32896, 0, 25), (2097160, 1, 25), (12582912, 0, 26), (33280, 1, 26),
    (1056768, 0, 28), (8454144, 1, 28), (8519680, 0, 29), (40960, 1, 29), (16400, 0, 30),
    (36, 1, 31), (4227072, 0, 32), (520, 1, 32), (524320, 0, 33), (8388736, 0, 34),
    (2129920, 1, 34), (1310720, 0, 35), (40, 1, 36), (1572864, 0, 37), (4224, 0, 38),
    (2359296, 1, 38), (2162688, 1, 39), (2228224, 1, 40), (2105344, 1, 41), (4352, 0, 42),
    (1050624, 0, 43), (4325376, 0, 44), (8704, 1, 44), (288, 1, 45), (1048580, 0, 46),
    (8388612, 1, 46), (1081344, 0, 47), (8388616, 1, 47), (655360, 0, 48), (80, 0, 49),
    (1152, 1, 49), (278528, 0, 50), (524352, 1, 50)]


theorem gArrs_ok : ∀ j : Fin 2, InvPairOK 24 (gArrs.getD j #[]) (gInvs.getD j #[]) = true ∧
    autArrOK (gArrs.getD j #[]) (gInvs.getD j #[]) = true ∧
    (gArrs.getD j #[])[0]! = 0 ∧ (gArrs.getD j #[])[1]! = 1 := by
  decide +kernel

@[expose] def gPerm (j : Fin 2) : Equiv.Perm (Fin 24) :=
  permOfArr 24 (gArrs.getD j #[]) (gInvs.getD j #[]) (gArrs_ok j).1

theorem gPerm_mem_mog22 (j : Fin 2) : gPerm j ∈ mog22 :=
  mem_mog22_of_arr (mem_AutPerm_of_arr (gArrs_ok j).1 (gArrs_ok j).2.1)
    (hasArr_permOfArr (gArrs_ok j).1) (gArrs_ok j).2.2.1 (gArrs_ok j).2.2.2

@[expose] def maskSet (m : ℕ) : Finset (Fin 24) := Finset.univ.filter fun i => m.testBit i = true

theorem mem_maskSet (m : ℕ) (i : Fin 24) : i ∈ maskSet m ↔ m.testBit i = true := by
  simp [maskSet]

theorem smul_maskSet {σ : Equiv.Perm (Fin 24)} {a : Array ℕ} (hσ : HasArr σ a) (m : ℕ) :
    σ • maskSet m = maskSet (permM a m) := by
  ext j
  rw [← Finset.inv_smul_mem_iff, Equiv.Perm.smul_def, mem_maskSet, mem_maskSet,
    ← bvec_ne_zero_iff, ← bvec_ne_zero_iff, ← permWord_bvec hσ]
  exact Iff.rfl

theorem maskSet_inj {m m' : ℕ} (hm : m < 2 ^ 24) (hm' : m' < 2 ^ 24)
    (h : maskSet m = maskSet m') : m = m' := by
  refine Nat.eq_of_testBit_eq fun i => ?_
  by_cases hi : i < 24
  · have := congrArg (fun S => (⟨i, hi⟩ : Fin 24) ∈ S) h
    simpa [mem_maskSet] using this
  · rw [Nat.testBit_eq_false_of_lt (hm.trans_le (Nat.pow_le_pow_right (by norm_num) (by omega))),
      Nat.testBit_eq_false_of_lt (hm'.trans_le (Nat.pow_le_pow_right (by norm_num) (by omega)))]

@[expose] def bfsOK (m₀ : ℕ) (L : List (ℕ × ℕ × ℕ)) : Bool :=
  (List.range L.length).all fun k =>
    if k = 0 then (L.getD 0 (0, 0, 0)).1 == m₀ else
      decide ((L.getD k (0, 0, 0)).2.2 < k) && decide ((L.getD k (0, 0, 0)).2.1 < 2) &&
        (L.getD k (0, 0, 0)).1 == permM (gArrs.getD (L.getD k (0, 0, 0)).2.1 #[])
          (L.getD (L.getD k (0, 0, 0)).2.2 (0, 0, 0)).1

theorem mem_orbit_of_bfs {m₀ : ℕ} {L : List (ℕ × ℕ × ℕ)} (hL : bfsOK m₀ L = true) :
    ∀ k < L.length, maskSet (L.getD k (0, 0, 0)).1 ∈ MulAction.orbit ↥mog22 (maskSet m₀) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    have hc := List.all_eq_true.1 hL k (List.mem_range.2 hk)
    by_cases h0 : k = 0
    · subst h0
      simp only [↓reduceIte, beq_iff_eq] at hc
      rw [hc]
      exact MulAction.mem_orbit_self _
    simp only [h0, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hc
    obtain ⟨⟨hq, hj⟩, he⟩ := hc
    have hmem := ih _ hq (hq.trans hk)
    rw [he, ← smul_maskSet (hasArr_permOfArr (gArrs_ok ⟨_, hj⟩).1)]
    exact MulAction.mem_orbit_of_mem_orbit (⟨gPerm ⟨_, hj⟩, gPerm_mem_mog22 _⟩ : ↥mog22) hmem

theorem le_card_orbit_of_bfs {m₀ : ℕ} {L : List (ℕ × ℕ × ℕ)} (hL : bfsOK m₀ L = true)
    (hnd : (L.map Prod.fst).Nodup) (hlt : ∀ e ∈ L, e.1 < 2 ^ 24) :
    L.length ≤ Nat.card (MulAction.orbit ↥mog22 (maskSet m₀)) := by
  let f : Fin L.length → MulAction.orbit ↥mog22 (maskSet m₀) := fun k =>
    ⟨maskSet (L.getD k (0, 0, 0)).1, mem_orbit_of_bfs hL k k.2⟩
  have hf : Function.Injective f := by
    intro k k' hkk
    have hm : ∀ i : Fin L.length, L.getD i (0, 0, 0) ∈ L := fun i => by
      rw [List.getD_eq_getElem _ _ i.2]
      exact List.getElem_mem i.2
    have h := maskSet_inj (hlt _ (hm k)) (hlt _ (hm k')) (congrArg Subtype.val hkk)
    rw [List.getD_eq_getElem _ _ k.2, List.getD_eq_getElem _ _ k'.2] at h
    have h' : (L.map Prod.fst)[(k : ℕ)]'(by simp) = (L.map Prod.fst)[(k' : ℕ)]'(by simp) := by
      simpa using h
    exact Fin.ext ((List.Nodup.getElem_inj_iff hnd).1 h')
  simpa using Nat.card_le_card_of_injective f hf

theorem card_stab_mul_le
    {m₀ : ℕ} {L : List (ℕ × ℕ × ℕ)} (hL : bfsOK m₀ L = true) (hnd : (L.map Prod.fst).Nodup)
    (hlt : ∀ e ∈ L, e.1 < 2 ^ 24) :
    Nat.card (MulAction.stabilizer ↥mog22 (maskSet m₀)) * L.length ≤ 443520 := by
  have h := (MulAction.stabilizer ↥mog22 (maskSet m₀)).card_mul_index
  rw [MulAction.index_stabilizer, card_mog22] at h
  rw [← h]
  exact Nat.mul_le_mul_left _ (le_card_orbit_of_bfs hL hnd hlt)

theorem bfs_checks : bfsOK 252 bfsH = true ∧ bfsOK 60 bfs4 = true ∧ bfsOK 192 bfs2 = true ∧
    (bfsH.map Prod.fst).Nodup ∧ (bfs4.map Prod.fst).Nodup ∧ (bfs2.map Prod.fst).Nodup ∧
    (∀ e ∈ bfsH, e.1 < 2 ^ 24) ∧ (∀ e ∈ bfs4, e.1 < 2 ^ 24) ∧ (∀ e ∈ bfs2, e.1 < 2 ^ 24) ∧
    bfsH.length = 77 ∧ bfs4.length = 78 ∧ bfs2.length = 78 := by
  decide +kernel

end CFSG.Quasithin.H.Mathieu.H16Pf
