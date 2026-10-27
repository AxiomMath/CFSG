module

public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.Group

public section

namespace CFSG.Quasithin.Loc442Q

section Orb

variable {H : Type*} [Group H]

@[expose] def sig (a b : H) : Set H := {c | IsConj b c ∧ c * a = a * c}

@[expose] def orbSetoid (A : Subgroup H) (S : Set H) : Setoid S where
  r c d := ∃ x ∈ A, (d : H) = x⁻¹ * c * x
  iseqv :=
    { refl := fun c => ⟨1, A.one_mem, by simp⟩
      symm := fun {c d} ⟨x, hx, h⟩ => ⟨x⁻¹, A.inv_mem hx, by rw [h]; group⟩
      trans := fun {c d e} ⟨x, hx, h⟩ ⟨y, hy, h'⟩ =>
        ⟨x * y, A.mul_mem hx hy, by rw [h', h]; group⟩ }

@[expose] def OrbSet (A : Subgroup H) (S : Set H) : Type _ := Quotient (orbSetoid A S)

instance {A : Subgroup H} {S : Set H} [Finite S] : Finite (OrbSet A S) :=
  inferInstanceAs (Finite (Quotient (orbSetoid A S)))

@[expose] def OrbSet.mk {A : Subgroup H} {S : Set H} (c : S) : OrbSet A S :=
  Quotient.mk (orbSetoid A S) c

theorem OrbSet.mk_eq_mk {A : Subgroup H} {S : Set H} {c d : S} :
    (OrbSet.mk c : OrbSet A S) = OrbSet.mk d ↔ ∃ x ∈ A, (d : H) = x⁻¹ * c * x :=
  Quotient.eq (r := orbSetoid A S)

theorem OrbSet.mk_surjective {A : Subgroup H} {S : Set H} :
    Function.Surjective (OrbSet.mk : S → OrbSet A S) :=
  Quotient.mk_surjective

@[expose] def OrbSet.congr {H' : Type*} [Group H'] {A : Subgroup H} {A' : Subgroup H'}
    {S : Set H} {S' : Set H'} (e : S ≃ S')
    (he : ∀ c d : S, (∃ x ∈ A, (d : H) = x⁻¹ * c * x) ↔
      ∃ x ∈ A', ((e d : S') : H') = x⁻¹ * ((e c : S') : H') * x) :
    OrbSet A S ≃ OrbSet A' S' :=
  Quotient.congr e he

@[expose] def OrbSet.map {A A' : Subgroup H} {S S' : Set H} (hA : A ≤ A') (hS : S ⊆ S') :
    OrbSet A S → OrbSet A' S' :=
  Quotient.map (sa := orbSetoid A S) (sb := orbSetoid A' S')
    (fun c : S => (⟨c, hS c.2⟩ : S')) fun _ _ ⟨x, hx, h⟩ => ⟨x, hA hx, h⟩

theorem OrbSet.map_mk {A A' : Subgroup H} {S S' : Set H} (hA : A ≤ A') (hS : S ⊆ S') (c : S) :
    OrbSet.map hA hS (OrbSet.mk c) = (OrbSet.mk (⟨c, hS c.2⟩ : S') : OrbSet A' S') :=
  rfl

theorem OrbSet.map_injective_of_surjective {A A' : Subgroup H} {S S' : Set H} [Finite S]
    (hA : A ≤ A') (hS : S ⊆ S') (hsurj : Function.Surjective (OrbSet.map hA hS))
    (hcard : Nat.card (OrbSet A S) ≤ Nat.card (OrbSet A' S')) :
    ∀ c d : S, (∃ x ∈ A', (d : H) = x⁻¹ * c * x) → ∃ x ∈ A, (d : H) = x⁻¹ * c * x := by
  intro c d h
  have hbij := hsurj.bijective_of_nat_card_le hcard
  have h1 : OrbSet.map hA hS (OrbSet.mk c) = OrbSet.map hA hS (OrbSet.mk d) := by
    rw [OrbSet.map_mk, OrbSet.map_mk, OrbSet.mk_eq_mk]
    exact h
  exact OrbSet.mk_eq_mk.mp (hbij.1 h1)

end Orb

section Pairs

variable {H : Type*} [Group H]

@[expose] def pairSet (a b : H) : Set (H × H) :=
  {p | IsConj a p.1 ∧ IsConj b p.2 ∧ p.1 * p.2 = p.2 * p.1}

@[expose] def pairSetoid (a b : H) : Setoid (pairSet a b) where
  r p q := ∃ h : H, (q : H × H).1 = h⁻¹ * (p : H × H).1 * h ∧
    (q : H × H).2 = h⁻¹ * (p : H × H).2 * h
  iseqv :=
    { refl := fun p => ⟨1, by simp, by simp⟩
      symm := fun {p q} ⟨h, h1, h2⟩ => ⟨h⁻¹, by rw [h1]; group, by rw [h2]; group⟩
      trans := fun {p q r} ⟨h, h1, h2⟩ ⟨k, k1, k2⟩ =>
        ⟨h * k, by rw [k1, h1]; group, by rw [k2, h2]; group⟩ }

@[expose] def toPair (a b : H) (c : sig a b) : pairSet a b :=
  ⟨(a, c), IsConj.refl a, c.2.1, c.2.2.symm⟩

theorem toPair_rel (a b : H) {c d : sig a b}
    (h : orbSetoid (Subgroup.centralizer ({a} : Set H)) (sig a b) c d) :
    pairSetoid a b (toPair a b c) (toPair a b d) := by
  obtain ⟨x, hx, hd⟩ := h
  have hxa : x * a = a * x := Subgroup.mem_centralizer_singleton_iff.mp hx
  refine ⟨x, ?_, hd⟩
  show a = x⁻¹ * a * x
  calc a = x⁻¹ * (x * a) := by group
    _ = x⁻¹ * (a * x) := by rw [hxa]
    _ = x⁻¹ * a * x := by group

theorem toPair_injective (a b : H) :
    Function.Injective (Quotient.map (sa := orbSetoid (Subgroup.centralizer ({a} : Set H))
      (sig a b)) (sb := pairSetoid a b) (toPair a b) fun _ _ h => toPair_rel a b h) := by
  intro u v
  induction u using Quotient.inductionOn with | _ c => ?_
  induction v using Quotient.inductionOn with | _ d => ?_
  intro huv
  obtain ⟨h, h1, h2⟩ := Quotient.exact huv
  refine Quotient.sound ⟨h, ?_, h2⟩
  have h1' : a = h⁻¹ * a * h := h1
  rw [Subgroup.mem_centralizer_singleton_iff]
  calc h * a = h * (h⁻¹ * a * h) := by rw [← h1']
    _ = a * h := by group

theorem toPair_surjective (a b : H) :
    Function.Surjective (Quotient.map (sa := orbSetoid (Subgroup.centralizer ({a} : Set H))
      (sig a b)) (sb := pairSetoid a b) (toPair a b) fun _ _ h => toPair_rel a b h) := by
  intro u
  induction u using Quotient.inductionOn with | _ p => ?_
  obtain ⟨⟨a', b'⟩, hp1, hp2, hp3⟩ := p
  obtain ⟨k, hk⟩ := isConj_iff.mp hp1
  have hk' : k * a * k⁻¹ = a' := hk
  have hcb : IsConj b (k⁻¹ * b' * k) := by
    refine hp2.trans (isConj_iff.mpr ⟨k⁻¹, ?_⟩)
    group
  have hcomm : (k⁻¹ * b' * k) * a = a * (k⁻¹ * b' * k) := by
    have h3 : a' * b' = b' * a' := hp3
    rw [← hk'] at h3
    calc k⁻¹ * b' * k * a = k⁻¹ * (b' * (k * a * k⁻¹)) * k := by group
      _ = k⁻¹ * ((k * a * k⁻¹) * b') * k := by rw [← h3]
      _ = a * (k⁻¹ * b' * k) := by group
  refine ⟨Quotient.mk _ ⟨k⁻¹ * b' * k, hcb, hcomm⟩, Quotient.sound ⟨k⁻¹, ?_, ?_⟩⟩
  · show a' = (k⁻¹)⁻¹ * a * k⁻¹
    rw [← hk']
    group
  · show b' = (k⁻¹)⁻¹ * (k⁻¹ * b' * k) * k⁻¹
    group

noncomputable def orbPairEquiv (a b : H) :
    OrbSet (Subgroup.centralizer ({a} : Set H)) (sig a b) ≃ Quotient (pairSetoid a b) :=
  Equiv.ofBijective _ ⟨toPair_injective a b, toPair_surjective a b⟩

@[expose] def pairSwap (a b : H) : pairSet a b ≃ pairSet b a where
  toFun p := ⟨((p : H × H).2, (p : H × H).1), p.2.2.1, p.2.1, p.2.2.2.symm⟩
  invFun p := ⟨((p : H × H).2, (p : H × H).1), p.2.2.1, p.2.1, p.2.2.2.symm⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable def pairSwapEquiv (a b : H) :
    Quotient (pairSetoid a b) ≃ Quotient (pairSetoid b a) :=
  Quotient.congr (pairSwap a b) fun p q => by
    constructor
    · rintro ⟨h, h1, h2⟩
      exact ⟨h, h2, h1⟩
    · rintro ⟨h, h1, h2⟩
      exact ⟨h, h2, h1⟩

noncomputable def orbDuality (a b : H) :
    OrbSet (Subgroup.centralizer ({a} : Set H)) (sig a b) ≃
      OrbSet (Subgroup.centralizer ({b} : Set H)) (sig b a) :=
  (orbPairEquiv a b).trans ((pairSwapEquiv a b).trans (orbPairEquiv b a).symm)

theorem card_orbSet_comm (a b : H) :
    Nat.card (OrbSet (Subgroup.centralizer ({a} : Set H)) (sig a b)) =
      Nat.card (OrbSet (Subgroup.centralizer ({b} : Set H)) (sig b a)) :=
  Nat.card_congr (orbDuality a b)

end Pairs

section Hom

variable {Mb : Type*} [Group Mb] {M : Type*} [Group M]

@[expose] noncomputable def OrbSet.congrHom {K : Subgroup Mb} (bK : K →* M)
    (hinj : Function.Injective bK) {A : Subgroup Mb} (hAK : A ≤ K) {A' : Subgroup M}
    (hA : ∀ y : M, y ∈ A' ↔ ∃ x : K, (x : Mb) ∈ A ∧ bK x = y) {S : Set Mb} (hS : S ⊆ K)
    {S' : Set M} (hSS' : ∀ (c : Mb) (h : c ∈ S), bK ⟨c, hS h⟩ ∈ S')
    (hS'S : ∀ c' ∈ S', ∃ (c : Mb) (h : c ∈ S), bK ⟨c, hS h⟩ = c') :
    OrbSet A S ≃ OrbSet A' S' :=
  OrbSet.congr
    (Equiv.ofBijective (fun c : S => (⟨bK ⟨c, hS c.2⟩, hSS' c c.2⟩ : S'))
      ⟨fun c d h => Subtype.ext (by
        have h1 : bK ⟨c, hS c.2⟩ = bK ⟨d, hS d.2⟩ := congrArg Subtype.val h
        have h2 : (⟨c, hS c.2⟩ : K) = ⟨d, hS d.2⟩ := hinj h1
        have h3 : ((⟨c, hS c.2⟩ : K) : Mb) = ((⟨d, hS d.2⟩ : K) : Mb) :=
          congrArg (fun w : K => (w : Mb)) h2
        exact h3), fun y => by
        obtain ⟨c, h, hc⟩ := hS'S y y.2
        exact ⟨⟨c, h⟩, Subtype.ext hc⟩⟩)
    (fun c d => by
      constructor
      · rintro ⟨x, hx, hd⟩
        refine ⟨bK ⟨x, hAK hx⟩, (hA _).mpr ⟨⟨x, hAK hx⟩, hx, rfl⟩, ?_⟩
        have e : (⟨d, hS d.2⟩ : K) = (⟨x, hAK hx⟩ : K)⁻¹ * ⟨c, hS c.2⟩ * ⟨x, hAK hx⟩ :=
          Subtype.ext hd
        show bK ⟨d, hS d.2⟩ = (bK ⟨x, hAK hx⟩)⁻¹ * bK ⟨c, hS c.2⟩ * bK ⟨x, hAK hx⟩
        rw [e, map_mul, map_mul, map_inv]
      · rintro ⟨y, hy, hd⟩
        obtain ⟨xK, hxA, rfl⟩ := (hA y).mp hy
        refine ⟨(xK : Mb), hxA, ?_⟩
        have e : bK ⟨d, hS d.2⟩ = bK (xK⁻¹ * ⟨c, hS c.2⟩ * xK) := by
          rw [map_mul, map_mul, map_inv]
          exact hd
        exact congrArg Subtype.val (hinj e))

end Hom

end CFSG.Quasithin.Loc442Q
