module

public import Certificates.Data.Y2L.Words

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23.Y63Chk

open CFSG.OddStandard.HigherRank.G2Three.Sec2

structure Wit where
  x : ℕ
  typ : ℕ
  a : ℕ
  b : ℕ

structure Data where
  T : ℕ → ℕ → ℕ
  W : ℕ → List ℕ
  mt : ℕ → ℕ → ℕ
  iv : ℕ → ℕ
  m0 : List ℕ
  reps : List ℕ
  sk : ℕ → List ℕ
  cj : ℕ → ℕ → ℕ × ℕ
  tau : ℕ → ℕ → ℕ
  z : ℕ
  u0 : ℕ → List ℕ
  cw : ℕ → List Wit

@[expose] def letterOf (p : Fin 5 × Bool) : ℕ := 2 * p.1.val + (if p.2 then 0 else 1)

@[expose] def relCodes (_ : Unit := ()) : List (List ℕ) :=
  (y2l_ws26 2 false).map fun w => w.map letterOf

@[expose] def Crit (n : ℕ) (d : List ℕ) (bad : ℕ → ℕ → Prop) : Prop :=
  d.length < n ∨ (d.length = n ∧ ∃ a ∈ d, ∃ b ∈ d, bad a b)

instance (n : ℕ) (d : List ℕ) (bad : ℕ → ℕ → Prop) [∀ a b, Decidable (bad a b)] :
    Decidable (Crit n d bad) := by
  unfold Crit
  infer_instance

@[expose] def Data.TabSpec (D : Data) : Prop :=
  (∀ x < 512, ∀ c < 10, D.T x c < 512) ∧
  (∀ x < 512, ∀ c < 10, D.T (D.T x c) (if c % 2 = 0 then c + 1 else c - 1) = x) ∧
  ∀ r ∈ relCodes (), ∀ x < 512, r.foldl D.T x = x

instance (D : Data) : Decidable D.TabSpec := by
  unfold Data.TabSpec
  infer_instance

@[expose] def Data.WordSpec (D : Data) : Prop :=
  ∀ y < 512, (∀ c ∈ D.W y, c < 10) ∧ (D.W y).foldl D.T 0 = y

instance (D : Data) : Decidable D.WordSpec := by
  unfold Data.WordSpec
  infer_instance

@[expose] def Data.MulSpec (D : Data) : Prop :=
  ∀ x < 512, ∀ y < 512, D.mt x y = (D.W y).foldl D.T x ∧ D.mt x y < 512

instance (D : Data) : Decidable D.MulSpec := by
  unfold Data.MulSpec
  infer_instance

@[expose] def Data.InvSpec (D : Data) : Prop :=
  ∀ x < 512, D.iv x < 512 ∧ D.mt x (D.iv x) = 0

instance (D : Data) : Decidable D.InvSpec := by
  unfold Data.InvSpec
  infer_instance

@[expose] def Data.pow4 (D : Data) (x : ℕ) : ℕ := D.mt (D.mt x x) (D.mt x x)

@[expose] def Data.D4 (D : Data) (x : ℕ) : List ℕ :=
  (List.range 512).filter fun y => D.pow4 y == 0 && D.mt x y == D.mt y x

@[expose] def Data.MSpec (D : Data) : Prop :=
  D.m0.Nodup ∧ D.m0.length = 64 ∧ (∀ a ∈ D.m0, a < 512) ∧
  D.T 0 0 ∈ D.m0 ∧ D.T 0 2 ∈ D.m0 ∧ D.T 0 4 ∈ D.m0 ∧
  ∀ x < 512, D.pow4 x = 0 → x ∉ D.m0 → Crit 64 (D.D4 x) fun a b => D.mt a b ≠ D.mt b a

instance (D : Data) : Decidable D.MSpec := by
  unfold Data.MSpec
  infer_instance

@[expose] def Data.nn (D : Data) : List ℕ := D.m0.filter fun x => D.mt x x == 0

@[expose] def Data.pa (D : Data) (i : ℕ) : ℕ := D.mt (D.T 0 6) i

@[expose] def Data.pb (D : Data) (j : ℕ) : ℕ := D.mt (D.T 0 8) j

@[expose] def Data.PairOK (D : Data) (i j : ℕ) : Prop :=
  (D.mt (D.pa i) (D.pa i) ∈ D.m0 ∧ D.mt (D.pa i) (D.pa i) ∉ D.nn) ∨
  (D.pow4 (D.pb j) ∈ D.m0 ∧ D.pow4 (D.pb j) ∉ D.nn) ∨
  (D.mt (D.mt (D.pa i) (D.pb j)) (D.mt (D.pa i) (D.pb j)) ∈ D.m0 ∧
    D.mt (D.mt (D.pa i) (D.pb j)) (D.mt (D.pa i) (D.pb j)) ∉ D.nn) ∨
  ((D.cj i j).1 < 4 ∧ (D.cj i j).2 < 512 ∧
    D.mt (D.mt (D.iv (D.cj i j).2) (D.pa i)) (D.cj i j).2 ∈ D.sk (D.cj i j).1 ∧
    D.mt (D.mt (D.iv (D.cj i j).2) (D.pb j)) (D.cj i j).2 ∈ D.sk (D.cj i j).1)

instance (D : Data) (i j : ℕ) : Decidable (D.PairOK i j) := by
  unfold Data.PairOK
  infer_instance

@[expose] def Data.SSpec (D : Data) : Prop :=
  D.nn.length = 8 ∧
  (∀ k < 4, (D.sk k).Nodup ∧ (D.sk k).length = 64 ∧ (∀ a ∈ D.sk k, a < 512) ∧ 0 ∈ D.sk k ∧
    (∀ a ∈ D.sk k, ∀ b ∈ D.sk k, D.mt a b ∈ D.sk k) ∧ (∀ a ∈ D.sk k, D.iv a ∈ D.sk k) ∧
    ∀ n ∈ D.nn, n ∈ D.sk k) ∧
  (∀ i ∈ D.reps, i ∈ D.m0) ∧ (∀ m ∈ D.m0, ∃ i ∈ D.reps, ∃ n ∈ D.nn, D.mt i n = m) ∧
  ∀ i ∈ D.reps, ∀ j ∈ D.reps, D.PairOK i j

instance (D : Data) : Decidable D.SSpec := by
  unfold Data.SSpec
  infer_instance

@[expose] def Data.mq (D : Data) (k x y : ℕ) : ℕ :=
  D.mt (x % 512) (if x / 512 = 1 then D.tau k (y % 512) else y % 512) +
    512 * (if x / 512 = y / 512 then 0 else 1)

@[expose] def Data.TauSpec (D : Data) (k : ℕ) : Prop :=
  (∀ x < 512, D.tau k x < 512) ∧ ∀ s ∈ D.sk k, ∀ m ∈ D.m0, D.tau k (D.mt s m) = D.mt s (D.iv m)

instance (D : Data) (k : ℕ) : Decidable (D.TauSpec k) := by
  unfold Data.TauSpec
  infer_instance

@[expose] def Data.CenSpec (D : Data) (k : ℕ) : Prop :=
  D.z < 1024 ∧ D.z ≠ 0 ∧ (∀ y < 1024, D.mq k D.z y = D.mq k y D.z) ∧
  ∀ x < 1024, (∀ y < 1024, D.mq k x y = D.mq k y x) → x = 0 ∨ x = D.z

instance (D : Data) (k : ℕ) : Decidable (D.CenSpec k) := by
  unfold Data.CenSpec
  infer_instance

@[expose] def Data.cz (D : Data) (k a b : ℕ) : Prop :=
  D.mq k a b = D.mq k b a ∨ D.mq k a b = D.mq k D.z (D.mq k b a)

instance (D : Data) (k a b : ℕ) : Decidable (D.cz k a b) := by
  unfold Data.cz
  infer_instance

@[expose] def Data.sqz (D : Data) (k y : ℕ) : Prop := D.mq k y y = 0 ∨ D.mq k y y = D.z

instance (D : Data) (k y : ℕ) : Decidable (D.sqz k y) := by
  unfold Data.sqz
  infer_instance

@[expose] def Data.Dz (D : Data) (k x : ℕ) : List ℕ :=
  (List.range 1024).filter fun y => decide (D.sqz k y ∧ D.cz k x y)

@[expose] def Data.USpec (D : Data) (k : ℕ) : Prop :=
  (D.u0 k).Nodup ∧ (D.u0 k).length = 128 ∧ (∀ a ∈ D.u0 k, a < 1024) ∧ 0 ∈ D.u0 k ∧
  D.z ∈ D.u0 k ∧ (∀ a ∈ D.u0 k, ∀ b ∈ D.u0 k, D.mq k a b ∈ D.u0 k) ∧
  (∀ a ∈ D.u0 k, ∃ b ∈ D.u0 k, D.mq k a b = 0) ∧ (∀ a ∈ D.u0 k, D.sqz k a) ∧
  (∀ a ∈ D.u0 k, ∀ b ∈ D.u0 k, D.cz k a b) ∧
  ∀ x < 1024, D.sqz k x → x ∉ D.u0 k → Crit 128 (D.Dz k x) fun a b => ¬ D.cz k a b

instance (D : Data) (k : ℕ) : Decidable (D.USpec k) := by
  unfold Data.USpec
  infer_instance

@[expose] def Data.Cen (D : Data) (k x : ℕ) : List ℕ :=
  (List.range 1024).filter fun y => D.mq k x y == D.mq k y x

@[expose] def Data.WitOK (D : Data) (k : ℕ) (w : Wit) : Prop :=
  w.a < 1024 ∧ w.b < 1024 ∧ D.mq k w.x w.a = D.mq k w.a w.x ∧ D.mq k w.x w.b = D.mq k w.b w.x ∧
  ((w.typ = 0 ∧ D.mq k w.a w.b = D.mq k w.x (D.mq k w.b w.a)) ∨
    (w.typ = 1 ∧ w.x ∈ D.u0 k ∧ D.mq k w.a w.b = D.mq k D.z (D.mq k w.b w.a)))

instance (D : Data) (k : ℕ) (w : Wit) : Decidable (D.WitOK k w) := by
  unfold Data.WitOK
  infer_instance

@[expose] def Data.CandSpec (D : Data) (k : ℕ) : Prop :=
  (∀ w ∈ D.cw k, D.WitOK k w) ∧
  ∀ x < 512, x ≠ 0 → D.mq k x x = 0 → 128 ≤ (D.Cen k x).length → ∃ w ∈ D.cw k, w.x = x

instance (D : Data) (k : ℕ) : Decidable (D.CandSpec k) := by
  unfold Data.CandSpec
  infer_instance

@[expose] def Data.QSpec (D : Data) (k : ℕ) : Prop :=
  D.TauSpec k ∧ D.CenSpec k ∧ D.USpec k ∧ D.CandSpec k

instance (D : Data) (k : ℕ) : Decidable (D.QSpec k) := by
  unfold Data.QSpec
  infer_instance

@[expose] def Data.Spec (D : Data) : Prop :=
  D.TabSpec ∧ D.WordSpec ∧ D.MulSpec ∧ D.InvSpec ∧ D.MSpec ∧ D.SSpec ∧ ∀ k < 4, D.QSpec k

instance (D : Data) : Decidable D.Spec := by
  unfold Data.Spec
  infer_instance

end CFSG.OddStandard.HigherRank.YamadaG23.Y63Chk
