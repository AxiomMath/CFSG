module

public import Certificates.Data.A5GL42

public section

open Matrix

namespace Certificates.A5GL42

attribute [local instance 2000] Finset.decidableDforallFinset Finset.decidableExistsAndFinset
  Finset.decidableDExistsFinset

@[expose, irreducible] def codesNHN : List ℕ := [
  4680, 4698, 4715, 4729, 4748, 4766, 4783, 4797, 4804, 4822, 4839, 4853, 4940, 4959, 4973, 4990,
  4996, 5015, 5029, 5046, 5064, 5083, 5097, 5114, 8524, 8543, 8557, 8574, 8580, 8599, 8613, 8630,
  8648, 8667, 8681, 8698, 9032, 9050, 9067, 9081, 9100, 9118, 9135, 9149, 9156, 9174, 9191, 9205,
  12616, 12634, 12651, 12665, 12684, 12702, 12719, 12733, 12740, 12758, 12775, 12789, 12876,
  12895, 12909, 12926, 12932, 12951, 12965, 12982, 13000, 13019, 13033, 13050, 18450, 18467,
  18481, 18522, 18539, 18553, 18590, 18607, 18621, 18646, 18663, 18677, 19475, 19489, 19506,
  19551, 19565, 19582, 19607, 19621, 19638, 19675, 19689, 19706, 23058, 23075, 23089, 23112,
  23147, 23161, 23180, 23198, 23229, 23236, 23254, 23271, 24339, 24353, 24370, 24396, 24429,
  24446, 24452, 24471, 24502, 24520, 24539, 24553, 27410, 27427, 27441, 27464, 27482, 27513,
  27532, 27550, 27567, 27588, 27623, 27637, 27923, 27937, 27954, 27980, 27999, 28030, 28036,
  28055, 28069, 28104, 28137, 28154, 30994, 31011, 31025, 31048, 31066, 31083, 31116, 31151,
  31165, 31172, 31190, 31221, 32275, 32289, 32306, 32332, 32351, 32365, 32388, 32421, 32438,
  32456, 32475, 32506, 33811, 33825, 33842, 33887, 33901, 33918, 33943, 33957, 33974, 34011,
  34025, 34042, 35858, 35875, 35889, 35930, 35947, 35961, 35998, 36015, 36029, 36054, 36071,
  36085, 38675, 38689, 38706, 38732, 38751, 38765, 38788, 38821, 38838, 38856, 38875, 38906,
  40466, 40483, 40497, 40520, 40538, 40555, 40588, 40623, 40637, 40644, 40662, 40693, 42259,
  42273, 42290, 42316, 42349, 42366, 42372, 42391, 42422, 42440, 42459, 42473, 44818, 44835,
  44849, 44872, 44907, 44921, 44940, 44958, 44989, 44996, 45014, 45031, 46611, 46625, 46642,
  46668, 46687, 46718, 46724, 46743, 46757, 46792, 46825, 46842, 48402, 48419, 48433, 48456,
  48474, 48505, 48524, 48542, 48559, 48580, 48615, 48629, 50194, 50211, 50225, 50266, 50283,
  50297, 50334, 50351, 50365, 50390, 50407, 50421, 51219, 51233, 51250, 51295, 51309, 51326,
  51351, 51365, 51382, 51419, 51433, 51450, 54802, 54819, 54833, 54856, 54874, 54905, 54924,
  54942, 54959, 54980, 55015, 55029, 56083, 56097, 56114, 56140, 56159, 56190, 56196, 56215,
  56229, 56264, 56297, 56314, 59154, 59171, 59185, 59208, 59226, 59243, 59276, 59311, 59325,
  59332, 59350, 59381, 59667, 59681, 59698, 59724, 59743, 59757, 59780, 59813, 59830, 59848,
  59867, 59898, 62738, 62755, 62769, 62792, 62827, 62841, 62860, 62878, 62909, 62916, 62934,
  62951, 64019, 64033, 64050, 64076, 64109, 64126, 64132, 64151, 64182, 64200, 64219, 64233]

@[expose, irreducible] def codesNHO : List ℕ := [
  4680, 4687, 4740, 4751, 4852, 4856, 5160, 5167, 5250, 5263, 5362, 5368, 6180, 6191, 6210, 6223,
  6386, 6388, 7972, 7976, 8002, 8008, 8066, 8068, 8520, 8527, 8580, 8591, 8692, 8696, 9240, 9247,
  9345, 9359, 9457, 9464, 10260, 10271, 10305, 10319, 10481, 10484, 12052, 12056, 12097, 12104,
  12161, 12164, 16680, 16687, 16770, 16783, 16882, 16888, 16920, 16927, 17025, 17039, 17137,
  17144, 18450, 18463, 18465, 18479, 18673, 18674, 20242, 20248, 20257, 20264, 20353, 20354,
  33060, 33071, 33090, 33103, 33266, 33268, 33300, 33311, 33345, 33359, 33521, 33524, 33810,
  33823, 33825, 33839, 34033, 34034, 36626, 36628, 36641, 36644, 36673, 36674, 61732, 61736,
  61762, 61768, 61826, 61828, 61972, 61976, 62017, 62024, 62081, 62084, 62482, 62488, 62497,
  62504, 62593, 62594, 63506, 63508, 63521, 63524, 63553, 63554]

@[expose, irreducible] def codesT0N : List ℕ := [
  18481, 23089, 27441, 31025, 33825, 38689, 42273, 46625]

@[expose, irreducible] def codesT0O : List ℕ := [
  10481, 12161, 18673, 20353, 33345, 33825, 62017, 62497]


@[expose, irreducible] def NHN : Finset Mat4 := (codesNHN.map ofCode).toFinset

@[expose, irreducible] def NHO : Finset Mat4 := (codesNHO.map ofCode).toFinset

@[expose, irreducible] def T0N : Finset Mat4 := (codesT0N.map ofCode).toFinset

@[expose, irreducible] def T0O : Finset Mat4 := (codesT0O.map ofCode).toFinset

theorem HN_eq : HN = (codesN.map ofCode).toFinset := by unfold HN; rfl

theorem HO_eq : HO = (codesO.map ofCode).toFinset := by unfold HO; rfl

theorem NHN_eq : NHN = (codesNHN.map ofCode).toFinset := by unfold NHN; rfl

theorem NHO_eq : NHO = (codesNHO.map ofCode).toFinset := by unfold NHO; rfl

theorem T0N_eq : T0N = (codesT0N.map ofCode).toFinset := by unfold T0N; rfl

theorem T0O_eq : T0O = (codesT0O.map ofCode).toFinset := by unfold T0O; rfl

structure NormFacts (H NH T0 : Finset Mat4) : Prop where
  one_mem : 1 ∈ NH
  mul_mem : ∀ x ∈ NH, ∀ y ∈ NH, x * y ∈ NH
  inv_ex : ∀ x ∈ NH, ∃ y ∈ NH, x * y = 1
  card_mod : NH.card % 16 = 8
  complete : ∀ g : Mat4, (∃ g' : Mat4, g * g' = 1) → (∀ h ∈ H, ∃ h' ∈ H, g * h = h' * g) → g ∈ NH
  t0_sub : T0 ⊆ NH
  t0_one : 1 ∈ T0
  t0_mul : ∀ s ∈ T0, ∀ t ∈ T0, s * t ∈ T0
  t0_inv : ∀ x ∈ T0, ∃ y ∈ T0, x * y = 1
  t0_card : T0.card = 8
  t0_free : ∀ d ∈ NH, d ≠ 1 → d * d * d = 1 → ∃ t ∈ T0, ∀ t' ∈ T0, d * t ≠ t' * d

@[expose] def NoInvCent (H : Finset Mat4) : Prop :=
  ∀ g : Mat4, g * g = 1 → (∀ h ∈ H, g * h = h * g) → g = 1

@[expose] def FixZero (H : Finset Mat4) : Prop :=
  ∀ v : Vec4, (∀ h ∈ H, h *ᵥ v = v) → v = 0

instance (H : Finset Mat4) : Decidable (FixZero H) := by unfold FixZero; infer_instance

@[expose, irreducible] def O1 : Finset Vec4 :=
  (([1, 2, 3, 4, 5, 6, 8, 9, 10, 12] : List ℕ).map vecOfCode).toFinset

@[expose, irreducible] def O2 : Finset Vec4 :=
  (([7, 11, 13, 14, 15] : List ℕ).map vecOfCode).toFinset

@[expose] def Qab (a b : ZMod 2) (v : Vec4) : ZMod 2 :=
  if v ∈ O1 then a else if v ∈ O2 then b else 0

@[expose] def ThirdDiff (Q : Vec4 → ZMod 2) : Prop :=
  ∀ u v w : Vec4, Q (u + v + w) + Q (u + v) + Q (u + w) + Q (v + w) + Q u + Q v + Q w = 0

@[expose] def NonAdd (Q : Vec4 → ZMod 2) : Prop := ∃ u w : Vec4, Q (u + w) ≠ Q u + Q w

structure OrthForms : Prop where
  zero_o1 : (0 : Vec4) ∉ O1
  zero_o2 : (0 : Vec4) ∉ O2
  disj : ∀ v ∈ O1, v ∉ O2
  cover : ∀ v : Vec4, v = 0 ∨ v ∈ O1 ∨ v ∈ O2
  trans1 : ∀ v ∈ O1, ∃ h ∈ HO, h *ᵥ vecOfCode 1 = v
  trans2 : ∀ v ∈ O2, ∃ h ∈ HO, h *ᵥ vecOfCode 7 = v
  reps : vecOfCode 1 ∈ O1 ∧ vecOfCode 7 ∈ O2
  unique : ∀ a b : ZMod 2, ThirdDiff (Qab a b) → NonAdd (Qab a b) → a = 1 ∧ b = 0
  count : (Finset.univ.filter fun v : Vec4 => Qab 1 0 v = 0).card = 6

set_option synthInstance.maxSize 4096 in
instance (Q : Vec4 → ZMod 2) : Decidable (ThirdDiff Q) := by unfold ThirdDiff; infer_instance

instance (Q : Vec4 → ZMod 2) : Decidable (NonAdd Q) := by unfold NonAdd; infer_instance

structure Facts2 : Prop where
  normN : NormFacts HN NHN T0N
  normO : NormFacts HO NHO T0O
  centN : NoInvCent HN
  centO : NoInvCent HO
  fixN : FixZero HN
  fixO : FixZero HO
  forms : OrthForms

end Certificates.A5GL42
