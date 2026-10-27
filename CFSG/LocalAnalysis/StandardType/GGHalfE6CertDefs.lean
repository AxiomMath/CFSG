module

public import CFSG.Blueprint.ChevalleyRoots
public import CFSG.LieType.Steinberg.Minuscule.Group

public section

namespace CFSG.StandardType

open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg

abbrev GGE6Root := Fin (Tag.rank .E6) → ℤ

@[expose] def ggE6ip (r s : GGE6Root) : ℤ := ∑ i, ∑ j, r i * Tag.cartan .E6 i j * s j

@[expose] def ggE6Refl (g v : GGE6Root) : GGE6Root := v - ggE6ip v g • g

inductive GGHalfBlk
  | L | K | M
  deriving DecidableEq

@[expose] def GGHalfBlk.Lab : GGHalfBlk → Fin 8 → Prop
  | .L, a => a.val < 6
  | .K, a => 2 ≤ a.val
  | .M, a => 2 ≤ a.val

@[expose] def ggHalfSigma (a : Fin 8) : Fin 8 := (![2, 3, 0, 1, 4, 5, 6, 7] : Fin 8 → Fin 8) a

@[expose] def ggHalfPi (a : Fin 8) : Fin 8 := (![0, 1, 2, 3, 5, 4, 7, 6] : Fin 8 → Fin 8) a

@[expose] def ggHalfS (a : Fin 8) : Fin 8 := (![0, 1, 1, 0, 5, 4, 3, 2] : Fin 8 → Fin 8) a

structure GGHalfE6Model where
  frame : GGHalfBlk → Fin 8 → Fin 8 → GGE6Root

namespace GGHalfE6Model

@[expose] def Y (m : GGHalfE6Model) (b : GGHalfBlk) : Set GGE6Root :=
  {r | ∃ c d, b.Lab c ∧ b.Lab d ∧ c ≠ d ∧ m.frame b c d = r}

@[expose] def FrameOK (m : GGHalfE6Model) (b : GGHalfBlk) : Prop :=
  (∀ c d, b.Lab c → b.Lab d → c ≠ d → m.frame b c d ∈ rootFinset .E6) ∧
  (∀ c d, b.Lab c → b.Lab d → c ≠ d → m.frame b d c = -m.frame b c d) ∧
  (∀ c d e, b.Lab c → b.Lab d → b.Lab e → c ≠ d → d ≠ e → c ≠ e →
    m.frame b c d + m.frame b d e = m.frame b c e) ∧
  (∀ i j k l, b.Lab i → b.Lab j → b.Lab k → b.Lab l → i ≠ j → k ≠ l → ¬ (k = j ∧ l = i) →
    m.frame b i j + m.frame b k l ≠ 0) ∧
  (∀ i j k l, b.Lab i → b.Lab j → b.Lab k → b.Lab l → i ≠ j → k ≠ l → ¬ (k = j ∧ l = i) →
    j ≠ k → i ≠ l → m.frame b i j + m.frame b k l ∉ rootFinset .E6)

@[expose] def Perp (m : GGHalfE6Model) (b : GGHalfBlk) : Prop :=
  ∃ δ ∈ rootFinset .E6, ∀ r, r ∈ m.Y b ↔ r ∈ rootFinset .E6 ∧ ggE6ip r δ = 0

@[expose] def Overlap (m : GGHalfE6Model) : Prop :=
  (∀ c d : Fin 8, 2 ≤ c.val → c.val < 6 → 2 ≤ d.val → d.val < 6 → c ≠ d →
    m.frame .L c d = m.frame .K c d) ∧
  (∀ c d : Fin 8, 2 ≤ c.val → c.val < 6 → 2 ≤ d.val → d.val < 6 → c ≠ d →
    m.frame .M c d = m.frame .L (ggHalfSigma c) (ggHalfSigma d)) ∧
  (∀ c d : Fin 8, 4 ≤ c.val → 4 ≤ d.val → c ≠ d →
    m.frame .M c d = m.frame .K (ggHalfPi d) (ggHalfPi c)) ∧
  m.Y .L ∩ m.Y .K = {r | ∃ c d : Fin 8, 2 ≤ c.val ∧ c.val < 6 ∧ 2 ≤ d.val ∧ d.val < 6 ∧ c ≠ d ∧
    m.frame .L c d = r} ∧
  m.Y .L ∩ m.Y .M = {r | ∃ c d : Fin 8, 2 ≤ c.val ∧ c.val < 6 ∧ 2 ≤ d.val ∧ d.val < 6 ∧ c ≠ d ∧
    m.frame .M c d = r} ∧
  m.Y .K ∩ m.Y .M = {r | ∃ c d : Fin 8, 4 ≤ c.val ∧ 4 ≤ d.val ∧ c ≠ d ∧ m.frame .M c d = r}

@[expose] def wg (m : GGHalfE6Model) (r : GGE6Root) : GGE6Root :=
  ggE6Refl (m.frame .L 0 2) (ggE6Refl (m.frame .L 1 3) r)

@[expose] def wh (m : GGHalfE6Model) (r : GGE6Root) : GGE6Root :=
  ggE6Refl (m.frame .K 6 2) (ggE6Refl (m.frame .K 7 3) r)

@[expose] def Weyl (m : GGHalfE6Model) : Prop :=
  (∀ c d : Fin 8, 2 ≤ c.val → 2 ≤ d.val → c ≠ d → m.frame .M c d = m.wg (m.frame .K c d)) ∧
  (∀ c d : Fin 8, 2 ≤ c.val → 2 ≤ d.val → c ≠ d →
    m.frame .M c d = m.wh (m.frame .L (ggHalfS d) (ggHalfS c)))

@[expose] def simpleRoot (i : Fin (Tag.rank .E6)) : GGE6Root := Pi.single i 1

inductive Der (m : GGHalfE6Model) : GGHalfBlk → GGE6Root → Prop
  | base {b : GGHalfBlk} {i : Fin (Tag.rank .E6)} {r : GGE6Root} (hr : r ∈ m.Y b)
      (hi : r = simpleRoot i ∨ r = -simpleRoot i) : Der m b r
  | refl {b : GGHalfBlk} {g h : GGE6Root} (hg : Der m b g) (hng : Der m b (-g)) (hh : Der m b h)
      (hhg : h ≠ g) (hhn : h ≠ -g) (hr : ggE6Refl g h ∈ m.Y b) : Der m b (ggE6Refl g h)
  | add {b : GGHalfBlk} {g h : GGE6Root} (hg : Der m b g) (hh : Der m b h)
      (hs : g + h ∈ rootFinset .E6) (hY : g + h ∈ m.Y b) : Der m b (g + h)
  | transfer {b c : GGHalfBlk} {r : GGE6Root} (hb : Der m b r) (hc : r ∈ m.Y c) : Der m c r
  | transportG {b c : GGHalfBlk} {r : GGE6Root} (hL : ∀ s ∈ m.Y .L, Der m .L s) (hb : Der m b r)
      (hbc : (b = .K ∧ c = .M ∧ m.wg r ∈ m.Y .M) ∨ (b = .M ∧ c = .K ∧ m.wg r ∈ m.Y .K)) :
      Der m c (m.wg r)
  | transportH {b c : GGHalfBlk} {r : GGE6Root} (hK : ∀ s ∈ m.Y .K, Der m .K s) (hb : Der m b r)
      (hbc : (b = .L ∧ c = .M ∧ m.wh r ∈ m.Y .M) ∨ (b = .M ∧ c = .L ∧ m.wh r ∈ m.Y .L)) :
      Der m c (m.wh r)

@[expose] def Good (m : GGHalfE6Model) : Prop :=
  m.FrameOK .L ∧ m.FrameOK .K ∧ m.FrameOK .M ∧ m.Perp .L ∧ m.Perp .K ∧ m.Perp .M ∧ m.Overlap ∧
    m.Weyl ∧ (∀ i j, ∃ b, simpleRoot i ∈ m.Y b ∧ simpleRoot j ∈ m.Y b) ∧
    ∀ b, ∀ r ∈ m.Y b, Der m b r

end GGHalfE6Model

abbrev GGE6Two :
    Type :=
  ↥(Minuscule.e6Data_valid.minGroup (GaloisField 2 1))

@[expose] noncomputable def ggE6x
    (γ : GGE6Root) : GGE6Two :=
  Minuscule.e6Data_valid.xm (GaloisField 2 1) γ 1

@[expose] noncomputable def ggE6u
    (δ : GGE6Root) : GGE6Two :=
  ggE6x δ * ggE6x (-δ)

@[expose] noncomputable def GGHalfE6Model.J0
    (m : GGHalfE6Model) : Subgroup GGE6Two :=
  Subgroup.closure {g | ∃ c d : Fin 8, 2 ≤ c.val ∧ c.val < 6 ∧ 2 ≤ d.val ∧ d.val < 6 ∧ c ≠ d ∧
    g = ggE6x (m.frame .L c d)}

@[expose] def GGHalfX0
    (m : GGHalfE6Model) (ε : ℤ) :
    Prop :=
  ∃ r : GGE6Two,
    r * (ggE6u (m.frame .L 0 1) * ggE6u (m.frame .K 6 7) ^ ε) =
      (ggE6u (m.frame .L 0 1) * ggE6u (m.frame .K 6 7) ^ ε) * r ∧
    (∃ P : Subgroup GGE6Two, P ≤ m.J0 ⊓ m.J0.map (MulAut.conj r).toMonoidHom ∧ ⁅P, P⁆ = P ∧
      3 ∣ Nat.card P) ∧
    (∃ z ∈ m.J0 ⊔ m.J0.map (MulAut.conj r).toMonoidHom, orderOf z = 17 ∧
      ∃ j ∈ m.J0, z * j ≠ j * z) ∧
    197406720 ≤ Nat.card ↥(m.J0 ⊔ m.J0.map (MulAut.conj r).toMonoidHom)

@[expose] def GGHalfE6Cert :
    Prop :=
  ∃ m : GGHalfE6Model, m.Good ∧ GGHalfX0 m 1 ∧ GGHalfX0 m (-1)

end CFSG.StandardType

end
