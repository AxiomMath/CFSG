module

public import CFSG.Quasithin.Vol2.Ch12Sec2OrbitG2Base

public section

namespace CFSG.Quasithin.H13.Orbit

open CFSG.Open
open scoped commutatorElement

@[expose] def bitZ (c k : ℕ) : ZMod 2 := if c.testBit k then 1 else 0

@[expose] def decodeZ (c : ℕ) : quasithinZorn (ZMod 2) :=
  (bitZ c 0, fun i => bitZ c (1 + i), fun i => bitZ c (4 + i), bitZ c 7)

theorem decodeZ_injective {a b : ℕ} (ha : a < 256) (hb : b < 256)
    (h : decodeZ a = decodeZ b) : a = b := by
  have key : ∀ k < 8, a.testBit k = b.testBit k := by
    intro k hk
    have hbit : ∀ c, bitZ c k = 1 ↔ c.testBit k = true := fun c => by
      unfold bitZ
      split_ifs with h' <;> simp [h']
    have hk' : bitZ a k = bitZ b k := by
      interval_cases k
      · exact congrArg Prod.fst h
      · exact congrFun (congrArg (fun x => x.2.1) h) 0
      · exact congrFun (congrArg (fun x => x.2.1) h) 1
      · exact congrFun (congrArg (fun x => x.2.1) h) 2
      · exact congrFun (congrArg (fun x => x.2.2.1) h) 0
      · exact congrFun (congrArg (fun x => x.2.2.1) h) 1
      · exact congrFun (congrArg (fun x => x.2.2.1) h) 2
      · exact congrArg (fun x => x.2.2.2) h
    cases ha' : a.testBit k <;> cases hb' : b.testBit k
    · rfl
    · simp [bitZ, ha', hb'] at hk'
    · simp [bitZ, ha', hb'] at hk'
    · rfl
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 8
  · exact key i hi
  · have h2 : 256 ≤ 2 ^ i := by
      calc 256 = 2 ^ 8 := by norm_num
        _ ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [Nat.testBit_eq_false_of_lt (by omega), Nat.testBit_eq_false_of_lt (by omega)]

theorem decodeZ_surjective (x : quasithinZorn (ZMod 2)) : ∃ c < 256, decodeZ c = x := by
  have hbij : Function.Bijective (fun c : Fin 256 => decodeZ c) :=
    (Fintype.bijective_iff_injective_and_card _).2
      ⟨fun a b h => Fin.ext (decodeZ_injective a.2 b.2 h), by simp⟩
  obtain ⟨c, hc⟩ := hbij.2 x
  exact ⟨c, c.2, hc⟩

@[expose] def g2C1Tab : Array ℕ := #[
  0, 1, 6, 7, 2, 3, 4, 5, 8, 9, 14, 15, 10, 11, 12, 13, 32, 33, 38, 39, 34, 35, 36, 37, 40, 41, 46,
  47, 42, 43, 44, 45, 48, 49, 54, 55, 50, 51, 52, 53, 56, 57, 62, 63, 58, 59, 60, 61, 16, 17, 22,
  23, 18, 19, 20, 21, 24, 25, 30, 31, 26, 27, 28, 29, 64, 65, 70, 71, 66, 67, 68, 69, 72, 73, 78,
  79, 74, 75, 76, 77, 96, 97, 102, 103, 98, 99, 100, 101, 104, 105, 110, 111, 106, 107, 108, 109,
  112, 113, 118, 119, 114, 115, 116, 117, 120, 121, 126, 127, 122, 123, 124, 125, 80, 81, 86, 87,
  82, 83, 84, 85, 88, 89, 94, 95, 90, 91, 92, 93, 128, 129, 134, 135, 130, 131, 132, 133, 136, 137,
  142, 143, 138, 139, 140, 141, 160, 161, 166, 167, 162, 163, 164, 165, 168, 169, 174, 175, 170,
  171, 172, 173, 176, 177, 182, 183, 178, 179, 180, 181, 184, 185, 190, 191, 186, 187, 188, 189,
  144, 145, 150, 151, 146, 147, 148, 149, 152, 153, 158, 159, 154, 155, 156, 157, 192, 193, 198,
  199, 194, 195, 196, 197, 200, 201, 206, 207, 202, 203, 204, 205, 224, 225, 230, 231, 226, 227,
  228, 229, 232, 233, 238, 239, 234, 235, 236, 237, 240, 241, 246, 247, 242, 243, 244, 245, 248,
  249, 254, 255, 250, 251, 252, 253, 208, 209, 214, 215, 210, 211, 212, 213, 216, 217, 222, 223,
  218, 219, 220, 221]

@[expose] def g2C2Tab : Array ℕ := #[
  0, 144, 16, 128, 68, 212, 84, 196, 40, 184, 56, 168, 108, 252, 124, 236, 147, 3, 131, 19, 215,
  71, 199, 87, 187, 43, 171, 59, 255, 111, 239, 127, 8, 152, 24, 136, 76, 220, 92, 204, 32, 176,
  48, 160, 100, 244, 116, 228, 155, 11, 139, 27, 223, 79, 207, 95, 179, 35, 163, 51, 247, 103, 231,
  119, 4, 148, 20, 132, 64, 208, 80, 192, 44, 188, 60, 172, 104, 248, 120, 232, 151, 7, 135, 23,
  211, 67, 195, 83, 191, 47, 175, 63, 251, 107, 235, 123, 12, 156, 28, 140, 72, 216, 88, 200, 36,
  180, 52, 164, 96, 240, 112, 224, 159, 15, 143, 31, 219, 75, 203, 91, 183, 39, 167, 55, 243, 99,
  227, 115, 17, 129, 1, 145, 85, 197, 69, 213, 57, 169, 41, 185, 125, 237, 109, 253, 130, 18, 146,
  2, 198, 86, 214, 70, 170, 58, 186, 42, 238, 126, 254, 110, 25, 137, 9, 153, 93, 205, 77, 221, 49,
  161, 33, 177, 117, 229, 101, 245, 138, 26, 154, 10, 206, 94, 222, 78, 162, 50, 178, 34, 230, 118,
  246, 102, 21, 133, 5, 149, 81, 193, 65, 209, 61, 173, 45, 189, 121, 233, 105, 249, 134, 22, 150,
  6, 194, 82, 210, 66, 174, 62, 190, 46, 234, 122, 250, 106, 29, 141, 13, 157, 89, 201, 73, 217,
  53, 165, 37, 181, 113, 225, 97, 241, 142, 30, 158, 14, 202, 90, 218, 74, 166, 54, 182, 38, 226,
  114, 242, 98]

@[expose] def g2Words : Array (List ℕ) := #[
  [], [], [], [], [1, 1], [], [1], [], [2, 1, 2], [], [2, 2, 1, 2, 2, 1, 2], [],
  [2, 1, 2, 1, 1, 2, 1, 1], [], [1, 2, 2, 1, 2, 2, 1, 2], [], [2], [], [], [], [2, 1, 2, 1, 1], [],
  [2, 1, 1, 2, 1, 2, 1, 1], [], [1, 1, 2, 2, 1, 2], [], [2, 1, 1, 2, 2], [], [2, 1, 2, 1], [],
  [2, 1, 2, 1, 2, 1, 1], [], [1, 2], [], [1, 2, 1, 2, 1, 1], [], [2, 1, 2, 1, 2, 2, 1, 2], [], [1],
  [], [2, 2, 1, 2], [], [1, 2, 1, 2, 1], [], [1, 2, 1, 2, 1, 2, 1, 1], [], [1, 2, 1, 1, 2, 2], [],
  [1, 1, 2], [], [2, 1, 2, 2, 1, 2, 2], [], [1, 1], [], [1, 1, 2, 1, 2, 1, 1], [], [1, 2, 2, 1, 2],
  [], [2, 1, 1, 2, 2, 1, 2, 2], [], [2, 2, 1, 1, 2, 1, 2], [], [1, 1, 2, 1, 2, 1], [],
  [2, 2, 1, 1], [], [1, 2, 1, 1], [], [2, 1, 1], [], [1, 1, 2, 1, 1], [],
  [2, 1, 2, 2, 1, 2, 1, 1, 2], [], [2, 1, 1, 2, 1, 2], [], [1, 1, 2, 1, 1, 2, 1, 2], [],
  [1, 2, 1, 1, 2, 1, 2], [], [2, 1, 1, 2, 1, 1], [], [2, 2, 1, 2], [], [2, 1], [],
  [2, 2, 1, 2, 1, 1, 2], [], [2, 1, 2, 2, 1, 2], [], [2, 1, 1, 2, 2, 1], [], [2, 1], [],
  [2, 1, 1, 2, 2], [], [1, 2, 1, 1, 2, 1, 1], [], [1, 2, 1], [], [1, 2, 2, 1, 2, 1, 1, 2], [],
  [1, 2, 2, 1, 2], [], [1, 2, 1, 2, 2, 1, 2], [], [1, 2, 1], [], [1, 2, 1, 1, 2, 2], [],
  [1, 2, 1, 1, 2, 2, 1], [], [1, 1, 2, 1, 1, 2, 1, 1], [], [1, 1, 2, 2, 1, 2, 1, 1, 2], [],
  [1, 1, 2, 2, 1, 2], [], [1, 1, 2, 1], [], [2, 1, 2, 1, 1, 2, 1, 2], [], [2, 2, 1, 2, 2], [],
  [1, 1, 2, 1, 1, 2, 2, 1], [], [1, 1, 2, 1], [], [], [], [], [2], [], [1, 1, 2], [], [1, 2], [],
  [2, 1, 2, 2], [], [1, 2, 2, 1, 2, 1, 1], [], [2, 2, 1, 2, 1, 1], [], [1, 1, 2, 2, 1, 2, 1, 1],
  [], [2, 2], [], [2, 2], [], [2, 1, 2, 1, 1, 2], [], [2, 2, 1, 1, 2, 1, 1], [],
  [1, 1, 2, 2, 1, 2, 2], [], [2, 1, 1, 2], [], [2, 1, 2, 1, 2], [], [1, 2, 1, 1, 2, 2, 1, 2], [],
  [1, 2, 2], [], [1, 2, 1, 2, 1, 1, 2], [], [2, 1, 2, 1, 2, 2, 1], [], [1, 2, 2], [],
  [2, 2, 1, 2, 2], [], [1, 2, 1, 2, 1, 2], [], [2, 2, 1, 2, 2, 1, 2, 1, 1], [], [1, 2, 1, 1, 2],
  [], [1, 1, 2, 2], [], [2, 1, 2, 2, 1, 2], [], [1, 1, 2, 2], [], [1, 1, 2, 1, 2, 1, 1, 2], [],
  [1, 2, 2, 1, 2, 2], [], [2, 1, 1, 2, 2, 1, 2], [], [2, 2, 1, 1, 2, 1], [], [1, 1, 2, 1, 2, 1, 2],
  [], [2, 2, 1, 1, 2], [], [1, 2, 1, 1, 2], [], [2, 1, 1, 2], [], [1, 1, 2, 1, 1, 2], [],
  [2, 1, 2, 2, 1, 2, 1, 1], [], [2, 1, 1, 2, 1], [], [1, 1, 2, 1, 1, 2, 1], [], [1, 2, 1, 1, 2, 1],
  [], [1, 1, 2, 1, 2, 1, 1], [], [2, 2, 1], [], [2, 1, 2], [], [2, 2, 1, 2, 1, 1], [],
  [2, 1, 2, 2, 1], [], [2, 1, 1, 2, 2, 1, 2], [], [2, 1, 2, 2], [], [2, 1, 1], [], [2, 1, 2, 1, 1],
  [], [1, 2, 1, 2], [], [1, 2, 2, 1, 2, 1, 1], [], [1, 2, 2, 1], [], [1, 2, 1, 2, 2, 1], [],
  [1, 2, 1, 2, 2], [], [1, 2, 1, 1], [], [2, 2, 1, 2, 1, 2, 1, 1], [], [1, 2, 1, 2, 1, 1], [],
  [1, 1, 2, 2, 1, 2, 1, 1], [], [1, 1, 2, 2, 1], [], [1, 1, 2, 1, 2], [], [2, 1, 2, 1, 1, 2, 1],
  [], [2, 2, 1], [], [1, 2, 2, 1, 2, 1, 2, 1, 1], [], [2, 2, 1, 2, 1]]

instance decEqZMod2 : DecidableEq (ZMod 2) := inferInstance

instance decEqZorn2 : DecidableEq (quasithinZorn (ZMod 2)) := inferInstance

@[expose] def actG (t c : ℕ) : ℕ := if t = 1 then g2C1Tab.getD c 0 else g2C2Tab.getD c 0

@[expose] def applyG (l : List ℕ) (c : ℕ) : ℕ := l.foldr actG c

theorem applyG_cons (t : ℕ) (l : List ℕ) (c : ℕ) : applyG (t :: l) c = actG t (applyG l c) :=
  rfl

theorem actG_one (c : ℕ) : actG 1 c = g2C1Tab.getD c 0 := by simp [actG]

theorem actG_two (c : ℕ) : actG 2 c = g2C2Tab.getD c 0 := by simp [actG]

theorem g2_tabs : ∀ c < 256,
    decodeZ (g2C1Tab.getD c 0) = fT01 (fT10 (gT01 (gT10 (decodeZ c)))) ∧
      decodeZ (g2C2Tab.getD c 0) = fTau (fX (fTau (gX (decodeZ c)))) ∧
        g2C1Tab.getD c 0 < 256 ∧ g2C2Tab.getD c 0 < 256 := by
  decide +kernel

theorem g2_cert : ∀ c < 256, (decodeZ c).1 + (decodeZ c).2.2.2 = 0 → decodeZ c ≠ 0 →
    decodeZ c ≠ zornOne →
      applyG (g2Words.getD c []) (if zornNorm (decodeZ c) = 0 then 2 else 18) = c := by
  decide +kernel

theorem g2_words : ∀ c < 256, ∀ t ∈ g2Words.getD c [], t = 1 ∨ t = 2 := by
  decide +kernel

@[expose] def genG {R : Type*} [CommRing R] (t : ℕ) : quasithinZorn R ≃ₗ[R] quasithinZorn R :=
  if t = 1 then zC1 else zC2

@[expose] def wordG {R : Type*} [CommRing R] (l : List ℕ) : quasithinZorn R ≃ₗ[R] quasithinZorn R :=
  (l.map genG).prod

theorem wordG_mem {R : Type*} [CommRing R] (l : List ℕ) :
    wordG (R := R) l ∈ ⁅quasithinG2 R, quasithinG2 R⁆ := by
  apply Subgroup.list_prod_mem
  intro g hg
  obtain ⟨t, -, rfl⟩ := List.mem_map.1 hg
  unfold genG
  split_ifs
  · exact zC1_mem
  · exact zC2_mem

theorem wordG_cons {R : Type*} [CommRing R] (t : ℕ) (l : List ℕ) (x : quasithinZorn R) :
    wordG (t :: l) x = genG t (wordG l x) := by
  simp [wordG]

theorem decodeZ_applyG {l : List ℕ} (hl : ∀ t ∈ l, t = 1 ∨ t = 2) {c : ℕ} (hc : c < 256) :
    decodeZ (applyG l c) = wordG l (decodeZ c) ∧ applyG l c < 256 := by
  induction l with
  | nil => exact ⟨rfl, hc⟩
  | cons t l ih =>
    obtain ⟨ih1, ih2⟩ := ih fun s hs => hl s (List.mem_cons_of_mem _ hs)
    have htabs := g2_tabs _ ih2
    rcases hl t List.mem_cons_self with rfl | rfl
    · have e1 : applyG (1 :: l) c = g2C1Tab.getD (applyG l c) 0 :=
        (applyG_cons 1 l c).trans (actG_one _)
      refine ⟨?_, e1 ▸ htabs.2.2.1⟩
      calc decodeZ (applyG (1 :: l) c) = decodeZ (g2C1Tab.getD (applyG l c) 0) := by rw [e1]
        _ = fT01 (fT10 (gT01 (gT10 (decodeZ (applyG l c))))) := htabs.1
        _ = wordG (1 :: l) (decodeZ c) := by
            rw [wordG_cons, ← ih1, genG, ite_eq_left rfl, zC1_apply]
    · have e2 : applyG (2 :: l) c = g2C2Tab.getD (applyG l c) 0 :=
        (applyG_cons 2 l c).trans (actG_two _)
      refine ⟨?_, e2 ▸ htabs.2.2.2⟩
      calc decodeZ (applyG (2 :: l) c) = decodeZ (g2C2Tab.getD (applyG l c) 0) := by rw [e2]
        _ = fTau (fX (fTau (gX (decodeZ (applyG l c))))) := htabs.2.1
        _ = wordG (2 :: l) (decodeZ c) := by
            rw [wordG_cons, ← ih1, genG, ite_eq_right (by norm_num), zC2_apply]

theorem zornMap_wordG {R S : Type*} [CommRing R] [CommRing S] (ψ : R →+* S) (l : List ℕ)
    (x : quasithinZorn R) : wordG l (zornMap ψ x) = zornMap ψ (wordG l x) := by
  induction l with
  | nil => rfl
  | cons t l ih =>
    rw [wordG_cons, wordG_cons, ih]
    unfold genG
    split_ifs
    · exact zornMap_zC1 ψ _
    · exact zornMap_zC2 ψ _

section Two

variable {K : Type} [Field K]

@[expose] def zornE (K : Type) [Field K] : quasithinZorn K := (0, Pi.single 0 1, 0, 0)

@[expose] def zornEF (K : Type) [Field K] : quasithinZorn K := (0, Pi.single 0 1, Pi.single 0 1, 0)

theorem two_eq_zero_of_card_two (hK : Nat.card K = 2) : (2 : K) = 0 := by
  have : Finite K := Nat.finite_of_card_ne_zero (by omega)
  have : Fintype K := Fintype.ofFinite K
  classical
  by_contra h
  have h1 : (2 : K) ≠ 1 := by
    intro h'
    have : (1 : K) + 1 = 1 := by rw [← one_add_one_eq_two] at h'; exact h'
    exact one_ne_zero (add_eq_left.1 this)
  have h3 : ({0, 1, 2} : Finset K).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_pair h1.symm]
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨zero_ne_one, Ne.symm h⟩
  have := Finset.card_le_univ ({0, 1, 2} : Finset K)
  rw [h3, ← Nat.card_eq_fintype_card, hK] at this
  omega

theorem charP_two_of_card_two (hK : Nat.card K = 2) : CharP K 2 := by
  have h := two_eq_zero_of_card_two hK
  exact (CharP.charP_iff_prime_eq_zero Nat.prime_two).2 (by exact_mod_cast h)

@[expose] noncomputable def castTwo (hK : Nat.card K = 2) : ZMod 2 →+* K :=
  have := charP_two_of_card_two hK
  ZMod.castHom (dvd_refl 2) K

theorem castTwo_bijective (hK : Nat.card K = 2) : Function.Bijective (castTwo hK) := by
  have : Finite K := Nat.finite_of_card_ne_zero (by omega)
  refine (Function.Injective.bijective_of_nat_card_le (castTwo hK).injective ?_)
  rw [hK, Nat.card_zmod]

theorem exists_zornMap_eq (hK : Nat.card K = 2) (m : quasithinZorn K) :
    ∃ m₀ : quasithinZorn (ZMod 2), zornMap (castTwo hK) m₀ = m := by
  have hs := (castTwo_bijective hK).2
  choose f hf using hs
  refine ⟨(f m.1, fun i => f (m.2.1 i), fun i => f (m.2.2.1 i), f m.2.2.2), ?_⟩
  apply zorn_ext <;> (try intro i) <;> simp [zornMap, hf]

theorem zornMap_injective (hK : Nat.card K = 2) :
    Function.Injective (zornMap (castTwo hK)) := by
  intro x y h
  have hi := (castTwo_bijective hK).1
  apply zorn_ext
  · exact hi (congrArg Prod.fst h)
  · intro i
    exact hi (congrFun (congrArg (fun x => x.2.1) h) i)
  · intro i
    exact hi (congrFun (congrArg (fun x => x.2.2.1) h) i)
  · exact hi (congrArg (fun x => x.2.2.2) h)

theorem zornMap_zero (hK : Nat.card K = 2) : zornMap (castTwo hK) 0 = 0 := by
  apply zorn_ext <;> intros <;> simp [zornMap]

theorem zornMap_one (hK : Nat.card K = 2) : zornMap (castTwo hK) zornOne = zornOne := by
  apply zorn_ext <;> (try intro i) <;> simp [zornMap, zornOne]

theorem zornMap_tr (hK : Nat.card K = 2) (x : quasithinZorn (ZMod 2)) :
    (zornMap (castTwo hK) x).1 + (zornMap (castTwo hK) x).2.2.2 =
      castTwo hK (x.1 + x.2.2.2) := by
  simp [zornMap]

theorem zornMap_norm (hK : Nat.card K = 2) (x : quasithinZorn (ZMod 2)) :
    zornNorm (zornMap (castTwo hK) x) = castTwo hK (zornNorm x) := by
  simp [zornMap, zornNorm, Fin.sum_univ_three]

theorem zornMap_e (hK : Nat.card K = 2) : zornMap (castTwo hK) (decodeZ 2) = zornE K := by
  apply zorn_ext <;> (try intro i) <;> (try fin_cases i) <;> simp [zornMap, zornE, decodeZ, bitZ]
  all_goals decide

theorem zornMap_ef (hK : Nat.card K = 2) : zornMap (castTwo hK) (decodeZ 18) = zornEF K := by
  apply zorn_ext <;> (try intro i) <;> (try fin_cases i) <;> simp [zornMap, zornEF, decodeZ, bitZ]
  all_goals decide

theorem exists_g2Derived_apply_eq (hK : Nat.card K = 2) {m : quasithinZorn K}
    (hm : m.1 + m.2.2.2 = 0) (hm0 : m ≠ 0) (hm1 : m ≠ zornOne) :
    (zornNorm m = 0 → ∃ γ ∈ ⁅quasithinG2 K, quasithinG2 K⁆, γ (zornE K) = m) ∧
      (zornNorm m ≠ 0 → ∃ γ ∈ ⁅quasithinG2 K, quasithinG2 K⁆, γ (zornEF K) = m) := by
  obtain ⟨m₀, rfl⟩ := exists_zornMap_eq hK m
  obtain ⟨c, hc, hcm⟩ := decodeZ_surjective m₀
  have hinj := (castTwo_bijective hK).1
  have h1 : (decodeZ c).1 + (decodeZ c).2.2.2 = 0 := by
    rw [hcm]
    rw [zornMap_tr] at hm
    exact hinj (hm.trans (map_zero _).symm)
  have h2 : decodeZ c ≠ 0 := by
    rw [hcm]
    rintro rfl
    exact hm0 (zornMap_zero hK)
  have h3 : decodeZ c ≠ zornOne := by
    rw [hcm]
    rintro rfl
    exact hm1 (zornMap_one hK)
  have hw1 := g2_cert c hc h1 h2 h3
  have hw2 := g2_words c hc
  have hn : zornNorm (zornMap (castTwo hK) m₀) = 0 ↔ zornNorm m₀ = 0 := by
    rw [zornMap_norm]
    exact ⟨fun h => hinj (h.trans (map_zero _).symm), fun h => by rw [h, map_zero]⟩
  have key : ∀ b : ℕ, b < 256 → applyG (g2Words.getD c []) b = c →
      wordG (g2Words.getD c []) (zornMap (castTwo hK) (decodeZ b)) = zornMap (castTwo hK) m₀ := by
    intro b hb hab
    rw [zornMap_wordG, ← (decodeZ_applyG hw2 hb).1, hab, hcm]
  refine ⟨fun h => ⟨wordG (g2Words.getD c []), wordG_mem _, ?_⟩,
    fun h => ⟨wordG (g2Words.getD c []), wordG_mem _, ?_⟩⟩
  · have hc0 : zornNorm (decodeZ c) = 0 := by rw [hcm]; exact hn.1 h
    rw [ite_eq_left hc0] at hw1
    rw [← zornMap_e hK]
    exact key 2 (by norm_num) hw1
  · have hc0 : zornNorm (decodeZ c) ≠ 0 := by rw [hcm]; exact fun h' => h (hn.2 h')
    rw [ite_eq_right hc0] at hw1
    rw [← zornMap_ef hK]
    exact key 18 (by norm_num) hw1

end Two

end CFSG.Quasithin.H13.Orbit
