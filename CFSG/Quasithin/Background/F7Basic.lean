module

public import CFSG.LocalAnalysis.QuasithinUnique.Defs
import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.LieType.BorelTits.Basic

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique

variable {G : Type*} [Group G]

@[expose] def conjSub (g : G) (H : Subgroup G) : Subgroup G := H.map (MulAut.conj g).toMonoidHom

theorem mem_conjSub {g x : G} {H : Subgroup G} : x ∈ conjSub g H ↔ g⁻¹ * x * g ∈ H := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    have : g⁻¹ * (g * y * g⁻¹) * g = y := by group
    simpa [this] using hy
  · intro h
    exact ⟨g⁻¹ * x * g, h, by simp [mul_assoc]⟩

theorem mul_mem_conjSub {g x : G} {H : Subgroup G} (hx : x ∈ H) : g * x * g⁻¹ ∈ conjSub g H :=
  mem_conjSub.mpr (by simpa [mul_assoc] using hx)

theorem conjSub_one (H : Subgroup G) : conjSub 1 H = H := by
  ext x; simp [mem_conjSub]

theorem conjSub_mul (g h : G) (H : Subgroup G) : conjSub (g * h) H = conjSub g (conjSub h H) := by
  ext x
  simp only [mem_conjSub, mul_inv_rev, mul_assoc]

theorem conjSub_conjSub_inv (g : G) (H : Subgroup G) : conjSub g⁻¹ (conjSub g H) = H := by
  rw [← conjSub_mul, inv_mul_cancel, conjSub_one]

theorem conjSub_inv_conjSub (g : G) (H : Subgroup G) : conjSub g (conjSub g⁻¹ H) = H := by
  rw [← conjSub_mul, mul_inv_cancel, conjSub_one]

theorem conjSub_mono (g : G) {H K : Subgroup G} (h : H ≤ K) : conjSub g H ≤ conjSub g K :=
  Subgroup.map_mono h

theorem conjSub_le_iff (g : G) {H K : Subgroup G} : conjSub g H ≤ K ↔ H ≤ conjSub g⁻¹ K := by
  constructor
  · intro h x hx
    rw [mem_conjSub]
    apply h
    rw [mem_conjSub]
    have : g⁻¹ * (g * x * g⁻¹) * g = x := by group
    simpa [this] using hx
  · intro h x hx
    have := h (mem_conjSub.mp hx)
    rw [mem_conjSub] at this
    have h2 : g * (g⁻¹ * x * g) * g⁻¹ = x := by group
    simpa [h2] using this

theorem le_conjSub_iff (g : G) {H K : Subgroup G} : H ≤ conjSub g K ↔ conjSub g⁻¹ H ≤ K := by
  rw [conjSub_le_iff, inv_inv]

theorem conjSub_inj (g : G) {H K : Subgroup G} : conjSub g H = conjSub g K ↔ H = K := by
  refine ⟨fun h => ?_, fun h => h ▸ rfl⟩
  have := congrArg (conjSub g⁻¹) h
  simpa [conjSub_conjSub_inv] using this

theorem conjSub_inf (g : G) (H K : Subgroup G) : conjSub g (H ⊓ K) = conjSub g H ⊓ conjSub g K := by
  ext x; simp [mem_conjSub]

theorem conjSub_sup (g : G) (H K : Subgroup G) : conjSub g (H ⊔ K) = conjSub g H ⊔ conjSub g K :=
  Subgroup.map_sup _ _ _

theorem conjSub_bot (g : G) : conjSub g (⊥ : Subgroup G) = ⊥ := by
  ext x
  simp only [mem_conjSub, Subgroup.mem_bot]
  constructor
  · intro h
    have : x = g * (g⁻¹ * x * g) * g⁻¹ := by group
    rw [this, h]; group
  · rintro rfl; group

theorem conjSub_eq_bot_iff (g : G) {H : Subgroup G} : conjSub g H = ⊥ ↔ H = ⊥ := by
  have := conjSub_inj g (H := H) (K := ⊥)
  rwa [conjSub_bot] at this

theorem conjSub_iSup {ι : Sort*} (g : G) (f : ι → Subgroup G) :
    conjSub g (⨆ i, f i) = ⨆ i, conjSub g (f i) := Subgroup.map_iSup _ _

theorem conjSub_iInf {ι : Sort*} (g : G) (f : ι → Subgroup G) :
    conjSub g (⨅ i, f i) = ⨅ i, conjSub g (f i) := by
  ext x
  simp only [mem_conjSub, Subgroup.mem_iInf]

theorem conjSub_closure (g : G) (S : Set G) :
    conjSub g (Subgroup.closure S) = Subgroup.closure ((fun x => g * x * g⁻¹) '' S) := by
  unfold conjSub
  rw [MonoidHom.map_closure]
  rfl

theorem conjSub_le_normalizer {g : G} {H K : Subgroup G} (h : H ≤ Subgroup.normalizer (K : Set G)) :
    conjSub g H ≤ Subgroup.normalizer (conjSub g K : Set G) := by
  intro z hz
  have hx : g⁻¹ * z * g ∈ H := mem_conjSub.mp hz
  rw [Subgroup.mem_normalizer_iff]
  intro y
  have hx' := (Subgroup.mem_normalizer_iff.mp (h hx)) (g⁻¹ * y * g)
  have e : g⁻¹ * (z * y * z⁻¹) * g = (g⁻¹ * z * g) * (g⁻¹ * y * g) * (g⁻¹ * z * g)⁻¹ := by group
  rw [mem_conjSub, mem_conjSub, e]
  exact hx'

theorem conjSub_normalizer (g : G) (H : Subgroup G) :
    Subgroup.normalizer (conjSub g H : Set G) = conjSub g (Subgroup.normalizer (H : Set G)) := by
  apply le_antisymm
  · intro x hx
    rw [mem_conjSub]
    rw [Subgroup.mem_normalizer_iff] at hx ⊢
    intro y
    have := hx (g * y * g⁻¹)
    rw [mem_conjSub, mem_conjSub] at this
    have e1 : g⁻¹ * (g * y * g⁻¹) * g = y := by group
    have e2 : g⁻¹ * (x * (g * y * g⁻¹) * x⁻¹) * g = (g⁻¹ * x * g) * y * (g⁻¹ * x * g)⁻¹ := by
      group
    rw [e1, e2] at this
    exact this
  · have h := conjSub_le_normalizer (g := g) (H := Subgroup.normalizer (H : Set G)) (K := H)
      le_rfl
    exact h

theorem conjSub_centralizer (g : G) (H : Subgroup G) :
    Subgroup.centralizer (conjSub g H : Set G) = conjSub g (Subgroup.centralizer (H : Set G)) := by
  ext x
  rw [mem_conjSub, Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro h y hy
    have := h (g * y * g⁻¹) (mul_mem_conjSub hy)
    have e : g⁻¹ * ((g * y * g⁻¹) * x) * g = y * (g⁻¹ * x * g) := by group
    have e' : g⁻¹ * (x * (g * y * g⁻¹)) * g = (g⁻¹ * x * g) * y := by group
    calc y * (g⁻¹ * x * g) = g⁻¹ * ((g * y * g⁻¹) * x) * g := e.symm
      _ = g⁻¹ * (x * (g * y * g⁻¹)) * g := by rw [this]
      _ = (g⁻¹ * x * g) * y := e'
  · intro h y hy
    have hy' := mem_conjSub.mp (SetLike.mem_coe.mp hy)
    have := h (g⁻¹ * y * g) hy'
    have e : (y * x) = g * ((g⁻¹ * y * g) * (g⁻¹ * x * g)) * g⁻¹ := by group
    have e' : (x * y) = g * ((g⁻¹ * x * g) * (g⁻¹ * y * g)) * g⁻¹ := by group
    rw [e, e', this]

theorem conjSub_commutator (g : G) (H K : Subgroup G) :
    ⁅conjSub g H, conjSub g K⁆ = conjSub g ⁅H, K⁆ :=
  (Subgroup.map_commutator H K _).symm

theorem pCoreOf_conjSub (g : G) (H : Subgroup G) :
    pCoreOf 2 (conjSub g H) = conjSub g (pCoreOf 2 H) :=
  pCoreOf_map_mulEquiv 2 (MulAut.conj g) H

namespace F7

theorem isPGroup_conjSub {p : ℕ} {g : G} {H : Subgroup G} (h : IsPGroup p H) :
    IsPGroup p (conjSub g H) := h.map _

theorem isPGroup_conjSub_iff {p : ℕ} (g : G) {H : Subgroup G} :
    IsPGroup p (conjSub g H) ↔ IsPGroup p H := by
  refine ⟨fun h => ?_, isPGroup_conjSub⟩
  have := isPGroup_conjSub (g := g⁻¹) h
  rwa [conjSub_conjSub_inv] at this

theorem isElemAbelian_iff {p : ℕ} {X : Subgroup G} :
    IsElemAbelian p X ↔ (∀ x ∈ X, ∀ y ∈ X, x * y = y * x) ∧ ∀ x ∈ X, x ^ p = 1 := by
  constructor
  · rintro ⟨hc, hp⟩
    exact ⟨fun x hx y hy => setLike_mul_comm (s := X) hx hy, hp⟩
  · rintro ⟨hc, hp⟩
    exact ⟨⟨⟨fun a b => Subtype.ext (hc a a.2 b b.2)⟩⟩, hp⟩

theorem isElemAbelian_comm {p : ℕ} {X : Subgroup G} (h : IsElemAbelian p X) {x y : G}
    (hx : x ∈ X) (hy : y ∈ X) : x * y = y * x := CFSG.Open.IsElemAbelian.comm h hx hy

theorem isElemAbelian_pow_eq_one {p : ℕ} {X : Subgroup G} (h : IsElemAbelian p X) {x : G}
    (hx : x ∈ X) : x ^ p = 1 :=
  (isElemAbelian_iff.mp h).2 x hx

theorem isElemAbelian_mono {p : ℕ} {X Y : Subgroup G} (h : IsElemAbelian p Y) (hXY : X ≤ Y) :
    IsElemAbelian p X := CFSG.Open.IsElemAbelian.mono h hXY

theorem isElemAbelian_conjSub {p : ℕ} {g : G} {X : Subgroup G} (h : IsElemAbelian p X) :
    IsElemAbelian p (conjSub g X) := by
  rw [isElemAbelian_iff] at h ⊢
  refine ⟨fun x hx y hy => ?_, fun x hx => ?_⟩
  · rw [mem_conjSub] at hx hy
    have := h.1 _ hx _ hy
    have e : x * y = g * ((g⁻¹ * x * g) * (g⁻¹ * y * g)) * g⁻¹ := by group
    have e' : y * x = g * ((g⁻¹ * y * g) * (g⁻¹ * x * g)) * g⁻¹ := by group
    rw [e, e', this]
  · rw [mem_conjSub] at hx
    have := h.2 _ hx
    have e := conj_pow (a := g) (b := g⁻¹ * x * g) (i := p)
    rw [show g * (g⁻¹ * x * g) * g⁻¹ = x by group, this] at e
    simpa using e

theorem isElemAbelian_conjSub_iff {p : ℕ} (g : G) {X : Subgroup G} :
    IsElemAbelian p (conjSub g X) ↔ IsElemAbelian p X := by
  refine ⟨fun h => ?_, isElemAbelian_conjSub⟩
  have := isElemAbelian_conjSub (g := g⁻¹) h
  rwa [conjSub_conjSub_inv] at this

end F7

open F7

namespace F7

theorem mem_normalizer_inf {A B : Subgroup G} {g : G} (hA : g ∈ Subgroup.normalizer (A : Set G))
    (hB : g ∈ Subgroup.normalizer (B : Set G)) : g ∈ Subgroup.normalizer ((A ⊓ B : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at *
  intro y
  simp only [Subgroup.mem_inf]
  exact and_congr (hA y) (hB y)

theorem le_normalizer_inf {X A B : Subgroup G} (hA : X ≤ Subgroup.normalizer (A : Set G))
    (hB : X ≤ Subgroup.normalizer (B : Set G)) :
    X ≤ Subgroup.normalizer ((A ⊓ B : Subgroup G) : Set G) :=
  fun _ hx => mem_normalizer_inf (hA hx) (hB hx)

theorem commutator_le_inf_of_normalizes {A B : Subgroup G}
    (hA : A ≤ Subgroup.normalizer (B : Set G)) (hB : B ≤ Subgroup.normalizer (A : Set G)) :
    ⁅A, B⁆ ≤ A ⊓ B := by
  rw [Subgroup.commutator_le]
  intro a ha b hb
  refine ⟨?_, ?_⟩
  · have h1 : b * a⁻¹ * b⁻¹ ∈ A := by
      have := (Subgroup.mem_normalizer_iff.mp (hB hb)) a⁻¹
      exact this.mp (A.inv_mem ha)
    rw [commutatorElement_def]
    simpa [mul_assoc] using A.mul_mem ha h1
  · have h1 : a * b * a⁻¹ ∈ B := by
      have := (Subgroup.mem_normalizer_iff.mp (hA ha)) b
      exact this.mp hb
    rw [commutatorElement_def]
    exact B.mul_mem h1 (B.inv_mem hb)

theorem le_normalizer_pCoreOf_of_le_normalizer {H K : Subgroup G}
    (h : H ≤ Subgroup.normalizer (K : Set G)) : H ≤ Subgroup.normalizer (pCoreOf 2 K : Set G) :=
  h.trans (normalizer_le_normalizer_pCoreOf 2 K)

end F7

open F7

@[expose] def coreIn (K H : Subgroup G) : Subgroup G where
  carrier := {x | x ∈ H ∧ ∀ h ∈ H, h⁻¹ * x * h ∈ K}
  one_mem' := ⟨H.one_mem, fun h _ => by simp⟩
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨H.mul_mem ha hb, fun h hh => ?_⟩
    have := K.mul_mem (ha' h hh) (hb' h hh)
    simpa [mul_assoc] using this
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨H.inv_mem ha, fun h hh => ?_⟩
    have := K.inv_mem (ha' h hh)
    simpa [mul_assoc] using this

theorem mem_coreIn {K H : Subgroup G} {x : G} :
    x ∈ coreIn K H ↔ x ∈ H ∧ ∀ h ∈ H, h⁻¹ * x * h ∈ K := Iff.rfl

theorem coreIn_le_left (K H : Subgroup G) : coreIn K H ≤ H := fun _ hx => hx.1

theorem coreIn_le_right (K H : Subgroup G) : coreIn K H ≤ K := fun x hx => by
  simpa using hx.2 1 H.one_mem

theorem le_normalizer_coreIn (K H : Subgroup G) : H ≤ Subgroup.normalizer (coreIn K H : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  have key : ∀ g ∈ H, ∀ x ∈ coreIn K H, g * x * g⁻¹ ∈ coreIn K H := by
    intro g hg x hx
    refine ⟨H.mul_mem (H.mul_mem hg hx.1) (H.inv_mem hg),
      fun h hh => ?_⟩
    have := hx.2 (g⁻¹ * h) (H.mul_mem (H.inv_mem hg) hh)
    simpa [mul_assoc] using this
  intro x
  refine ⟨fun hx => key g hg x hx, fun hx => ?_⟩
  have := key g⁻¹ (H.inv_mem hg) _ hx
  simpa [mul_assoc] using this

theorem le_coreIn {N K H : Subgroup G} (hNH : N ≤ H) (hN : H ≤ Subgroup.normalizer (N : Set G))
    (hNK : N ≤ K) : N ≤ coreIn K H := by
  intro x hx
  refine ⟨hNH hx, fun h hh => hNK ?_⟩
  have := (Subgroup.mem_normalizer_iff.mp (hN (H.inv_mem hh))) x
  simpa using this.mp hx

theorem conjSub_coreIn (g : G) (K H : Subgroup G) :
    conjSub g (coreIn K H) = coreIn (conjSub g K) (conjSub g H) := by
  ext x
  rw [mem_conjSub, mem_coreIn, mem_coreIn]
  constructor
  · rintro ⟨hx, hx'⟩
    refine ⟨mem_conjSub.mpr hx, fun h hh => ?_⟩
    rw [mem_conjSub] at hh ⊢
    have := hx' (g⁻¹ * h * g) hh
    have e : g⁻¹ * (h⁻¹ * x * h) * g = (g⁻¹ * h * g)⁻¹ * (g⁻¹ * x * g) * (g⁻¹ * h * g) := by
      group
    rw [e]; exact this
  · rintro ⟨hx, hx'⟩
    refine ⟨mem_conjSub.mp hx, fun h hh => ?_⟩
    have := hx' (g * h * g⁻¹) (mul_mem_conjSub hh)
    rw [mem_conjSub] at this
    have e : g⁻¹ * ((g * h * g⁻¹)⁻¹ * x * (g * h * g⁻¹)) * g = h⁻¹ * (g⁻¹ * x * g) * h := by
      group
    rw [e] at this; exact this

namespace F7

theorem mem_normalizer_of_conj_le {g : G} {N : Subgroup G} (h1 : conjSub g N ≤ N)
    (h2 : conjSub g⁻¹ N ≤ N) : g ∈ Subgroup.normalizer (N : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    exact h1 (mul_mem_conjSub hy)
  · intro hy
    have := h2 (mul_mem_conjSub hy)
    simpa [mul_assoc] using this

theorem le_normalizer_closure {X : Subgroup G} (S : Set G)
    (hS : ∀ g ∈ X, ∀ s ∈ S, g * s * g⁻¹ ∈ S) :
    X ≤ Subgroup.normalizer (Subgroup.closure S : Set G) := by
  have key : ∀ g ∈ X, conjSub g (Subgroup.closure S) ≤ Subgroup.closure S := by
    intro g hg
    rw [conjSub_closure, Subgroup.closure_le]
    rintro _ ⟨s, hs, rfl⟩
    exact Subgroup.subset_closure (hS g hg s hs)
  intro g hg
  exact mem_normalizer_of_conj_le (key g hg) (key g⁻¹ (X.inv_mem hg))

end F7

open F7

@[expose] def oTwoPrime (X : Subgroup G) : Subgroup G :=
  Subgroup.closure {x | x ∈ X ∧ ∃ n : ℕ, x ^ 2 ^ n = 1}

@[expose] def oTwoRes (X : Subgroup G) : Subgroup G :=
  Subgroup.closure {x | x ∈ X ∧ ∃ m : ℕ, Odd m ∧ x ^ m = 1}

theorem oTwoPrime_le (X : Subgroup G) : oTwoPrime X ≤ X :=
  (Subgroup.closure_le X).mpr fun _ hx => hx.1

theorem oTwoRes_le (X : Subgroup G) : oTwoRes X ≤ X :=
  (Subgroup.closure_le X).mpr fun _ hx => hx.1

theorem le_normalizer_oTwoPrime (X : Subgroup G) :
    X ≤ Subgroup.normalizer (oTwoPrime X : Set G) := by
  refine le_normalizer_closure _ fun g hg s hs => ⟨?_, ?_⟩
  · exact X.mul_mem (X.mul_mem hg hs.1) (X.inv_mem hg)
  · obtain ⟨n, hn⟩ := hs.2
    exact ⟨n, by rw [conj_pow, hn]; group⟩

theorem le_normalizer_oTwoRes (X : Subgroup G) :
    X ≤ Subgroup.normalizer (oTwoRes X : Set G) := by
  refine le_normalizer_closure _ fun g hg s hs => ⟨?_, ?_⟩
  · exact X.mul_mem (X.mul_mem hg hs.1) (X.inv_mem hg)
  · obtain ⟨m, hm, hn⟩ := hs.2
    exact ⟨m, hm, by rw [conj_pow, hn]; group⟩

theorem conjSub_oTwoPrime (g : G) (X : Subgroup G) :
    conjSub g (oTwoPrime X) = oTwoPrime (conjSub g X) := by
  unfold oTwoPrime
  rw [conjSub_closure]
  congr 1
  ext y
  constructor
  · rintro ⟨x, ⟨hx, n, hn⟩, rfl⟩
    refine ⟨mul_mem_conjSub hx, n, ?_⟩
    rw [conj_pow, hn]; group
  · rintro ⟨hy, n, hn⟩
    refine ⟨g⁻¹ * y * g, ⟨mem_conjSub.mp hy, n, ?_⟩, by group⟩
    have e := conj_pow (a := g⁻¹) (b := y) (i := 2 ^ n)
    simp only [inv_inv] at e
    rw [e, hn]; group

theorem conjSub_oTwoRes (g : G) (X : Subgroup G) :
    conjSub g (oTwoRes X) = oTwoRes (conjSub g X) := by
  unfold oTwoRes
  rw [conjSub_closure]
  congr 1
  ext y
  constructor
  · rintro ⟨x, ⟨hx, m, hm, hn⟩, rfl⟩
    refine ⟨mul_mem_conjSub hx, m, hm, ?_⟩
    rw [conj_pow, hn]; group
  · rintro ⟨hy, m, hm, hn⟩
    refine ⟨g⁻¹ * y * g, ⟨mem_conjSub.mp hy, m, hm, ?_⟩, by group⟩
    have e := conj_pow (a := g⁻¹) (b := y) (i := m)
    simp only [inv_inv] at e
    rw [e, hn]; group

theorem le_oTwoPrime_of_isPGroup {P X : Subgroup G} (hP : IsPGroup 2 P) (hPX : P ≤ X) :
    P ≤ oTwoPrime X := by
  intro x hx
  refine Subgroup.subset_closure ⟨hPX hx, ?_⟩
  obtain ⟨n, hn⟩ := hP ⟨x, hx⟩
  exact ⟨n, by simpa using congrArg Subtype.val hn⟩

@[expose] def weakClosureW0 (T V : Subgroup G) : Subgroup G :=
  ⨆ (g : G) (_ : conjSub g V ≤ T), conjSub g V

theorem conjSub_le_weakClosureW0 {T V : Subgroup G} {g : G} (h : conjSub g V ≤ T) :
    conjSub g V ≤ weakClosureW0 T V :=
  le_iSup₂_of_le g h le_rfl

namespace F7

theorem isSylowTwoOf_odd_relIndex {T H : Subgroup G} (h : IsSylowTwoOf T H) :
    ¬ 2 ∣ T.relIndex H := h.2.2

theorem isSylowTwoOf_of_relIndex {T H : Subgroup G} (hle : T ≤ H) (hp : IsPGroup 2 T)
    (hodd : ¬ 2 ∣ T.relIndex H) : IsSylowTwoOf T H := ⟨hle, hp, hodd⟩

theorem isSylowTwoOf_mono_right {T H K : Subgroup G} (h : IsSylowTwoOf T H) (hTK : T ≤ K)
    (hKH : K ≤ H) : IsSylowTwoOf T K := by
  refine isSylowTwoOf_of_relIndex hTK h.2.1 fun hd => isSylowTwoOf_odd_relIndex h ?_
  rw [← Subgroup.relIndex_mul_relIndex T K H hTK hKH]
  exact hd.mul_right _

theorem isSylowTwoOf_conj {T H : Subgroup G} (h : IsSylowTwoOf T H) (g : G) :
    IsSylowTwoOf (conjSub g T) (conjSub g H) := by
  refine isSylowTwoOf_of_relIndex (conjSub_mono g h.1) (isPGroup_conjSub h.2.1) ?_
  have : (conjSub g T).relIndex (conjSub g H) = T.relIndex H :=
    Subgroup.relIndex_map_map_of_injective (f := (MulAut.conj g).toMonoidHom) T H
      (MulEquiv.injective (MulAut.conj g))
  rw [this]
  exact isSylowTwoOf_odd_relIndex h

theorem isSylowTwoOf_conj_iff {T H : Subgroup G} (g : G) :
    IsSylowTwoOf (conjSub g T) (conjSub g H) ↔ IsSylowTwoOf T H := by
  refine ⟨fun h => ?_, fun h => isSylowTwoOf_conj h g⟩
  have := isSylowTwoOf_conj h g⁻¹
  rwa [conjSub_conjSub_inv, conjSub_conjSub_inv] at this

theorem isSylowTwoOf_exists_sylow {T H : Subgroup G} (h : IsSylowTwoOf T H) :
    ∃ S : Sylow 2 H, (S : Subgroup H) = T.subgroupOf H := by
  have hT' : IsPGroup 2 (T.subgroupOf H) :=
    h.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe h.1).symm
  exact ⟨hT'.toSylow h.2.2, rfl⟩

end F7

private theorem relIndex_sup_eq_of_le_normalizer {D T : Subgroup G}
    (hT : T ≤ Subgroup.normalizer (D : Set G)) : D.relIndex (T ⊔ D) = D.relIndex T := by
  have := Subgroup.normal_subgroupOf_of_le_normalizer hT
  have := Subgroup.normal_subgroupOf_sup_of_le_normalizer hT
  exact Nat.card_congr (QuotientGroup.quotientInfEquivProdNormalizerQuotient T D hT).toEquiv.symm

section Finite

variable [Finite G]

private theorem not_two_dvd_relIndex_inf {T H D : Subgroup G} (hTH : T ≤ H) (hDH : D ≤ H)
    (hT : ¬ 2 ∣ T.relIndex H) (hTN : T ≤ Subgroup.normalizer (D : Set G)) :
    ¬ 2 ∣ (T ⊓ D).relIndex D := by
  have h1 : (T ⊓ D).relIndex T * T.relIndex (T ⊔ D) = (T ⊓ D).relIndex (T ⊔ D) :=
    Subgroup.relIndex_mul_relIndex _ _ _ inf_le_left le_sup_left
  have h2 : (T ⊓ D).relIndex D * D.relIndex (T ⊔ D) = (T ⊓ D).relIndex (T ⊔ D) :=
    Subgroup.relIndex_mul_relIndex _ _ _ inf_le_right le_sup_right
  have h3 : D.relIndex (T ⊔ D) = (T ⊓ D).relIndex T :=
    (relIndex_sup_eq_of_le_normalizer hTN).trans (Subgroup.inf_relIndex_left T D).symm
  have h4 : 0 < (T ⊓ D).relIndex T :=
    Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite (H := ((T ⊓ D).subgroupOf T)))
  have h5 : (T ⊓ D).relIndex D = T.relIndex (T ⊔ D) := by
    refine Nat.eq_of_mul_eq_mul_left h4 ?_
    rw [h3] at h2
    rw [mul_comm ((T ⊓ D).relIndex T) ((T ⊓ D).relIndex D), h2, ← h1]
  rw [h5]
  intro hd
  apply hT
  rw [← Subgroup.relIndex_mul_relIndex T (T ⊔ D) H le_sup_left (sup_le hTH hDH)]
  exact hd.mul_right _

private theorem exists_relIndex_eq_two_pow {K D : Subgroup G}
    (hDK : D ≤ Subgroup.normalizer (K : Set G)) (hD : ∀ d ∈ D, ∃ k : ℕ, d ^ (2 ^ k) ∈ K) :
    ∃ n : ℕ, K.relIndex D = 2 ^ n := by
  have := Subgroup.normal_subgroupOf_of_le_normalizer hDK
  have hp : IsPGroup 2 (D ⧸ K.subgroupOf D) := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H d =>
      obtain ⟨k, hk⟩ := hD d d.2
      refine ⟨k, ?_⟩
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      simpa using hk
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hp
  exact ⟨n, hn⟩

namespace F7

theorem isSylowTwoOf_exists_conj_le {T H : Subgroup G} (h : IsSylowTwoOf T H)
    {P : Subgroup G} (hPH : P ≤ H) (hP : IsPGroup 2 P) : ∃ x ∈ H, P ≤ conjSub x T := by
  obtain ⟨S, hS⟩ := isSylowTwoOf_exists_sylow h
  have hP' : IsPGroup 2 (P.subgroupOf H) :=
    hP.of_equiv (Subgroup.subgroupOfEquivOfLe hPH).symm
  obtain ⟨Q, hQ⟩ := hP'.exists_le_sylow
  obtain ⟨x, hx⟩ := MulAction.exists_smul_eq H S Q
  refine ⟨x, x.2, fun y hy => ?_⟩
  have h1 : (⟨y, hPH hy⟩ : H) ∈ Q := hQ (by simpa [Subgroup.mem_subgroupOf] using hy)
  rw [← hx] at h1
  have h2 : (⟨y, hPH hy⟩ : H) ∈ ((x • S : Sylow 2 H) : Subgroup H) := h1
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at h2
  have h3 : (MulAut.conj x)⁻¹ • (⟨y, hPH hy⟩ : H) ∈ (S : Subgroup H) := h2
  rw [hS] at h3
  rw [mem_conjSub]
  simpa [Subgroup.mem_subgroupOf, MulAut.conj_inv_apply, mul_assoc] using h3

theorem isSylowTwoOf_pCoreOf_le {T H : Subgroup G} (h : IsSylowTwoOf T H) :
    pCoreOf 2 H ≤ T := by
  obtain ⟨S, hS⟩ := isSylowTwoOf_exists_sylow h
  have : (pCore 2 H).Normal := pCore_normal 2
  have hle : pCore 2 H ≤ (S : Subgroup H) := (pCore_isPGroup 2).le_sylow_of_normal S
  rintro _ ⟨y, hy, rfl⟩
  have := hle hy
  rw [hS] at this
  simpa [Subgroup.mem_subgroupOf] using this

theorem isSylowTwoOf_inf_normal {T H N : Subgroup G} (h : IsSylowTwoOf T H) (hNH : N ≤ H)
    (hTN : T ≤ Subgroup.normalizer (N : Set G)) : IsSylowTwoOf (T ⊓ N) N :=
  isSylowTwoOf_of_relIndex inf_le_right (h.2.1.to_le inf_le_left)
    (not_two_dvd_relIndex_inf h.1 hNH (isSylowTwoOf_odd_relIndex h) hTN)

theorem isSylowTwoOf_le_sup_of_two_power {P X N : Subgroup G} (hP : IsSylowTwoOf P X)
    (hXN : X ≤ Subgroup.normalizer (N : Set G))
    (h2 : ∀ x ∈ X, ∃ k : ℕ, x ^ (2 ^ k) ∈ N) : X ≤ N ⊔ P := by
  obtain ⟨n, hn⟩ := exists_relIndex_eq_two_pow hXN h2
  rw [← Subgroup.relIndex_eq_one]
  have h1 : (N ⊔ P).relIndex X ∣ 2 ^ n := hn ▸ Subgroup.relIndex_dvd_of_le_left X le_sup_left
  have h2' : (N ⊔ P).relIndex X ∣ P.relIndex X := Subgroup.relIndex_dvd_of_le_left X le_sup_right
  have hcop : Nat.Coprime (2 ^ n) (P.relIndex X) :=
    Nat.Coprime.pow_left n ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr
      (isSylowTwoOf_odd_relIndex hP))
  exact Nat.eq_one_of_dvd_coprimes hcop h1 h2'

theorem pCoreOf_mono_of_le_normalizer {K H : Subgroup G} (hKH : K ≤ H)
    (hN : H ≤ Subgroup.normalizer (K : Set G)) : pCoreOf 2 K ≤ pCoreOf 2 H :=
  le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 K).trans hKH)
    (hN.trans (normalizer_le_normalizer_pCoreOf 2 K)) (pCoreOf_isPGroup 2 K)

theorem pCoreOf_inf_le {K H : Subgroup G} (hKH : K ≤ H) : pCoreOf 2 H ⊓ K ≤ pCoreOf 2 K := by
  refine le_pCoreOf_of_le_normalizer 2 inf_le_right ?_ ((pCoreOf_isPGroup 2 H).to_le inf_le_left)
  refine le_normalizer_inf ?_ Subgroup.le_normalizer
  exact hKH.trans (le_normalizer_pCoreOf 2 H)

theorem pCoreOf_le_pCoreOf_of_isSylowTwoOf {T H K : Subgroup G} (hT : IsSylowTwoOf T H)
    (hTK : T ≤ K) (hKH : K ≤ H) : pCoreOf 2 H ≤ pCoreOf 2 K :=
  le_pCoreOf_of_le_normalizer 2 ((isSylowTwoOf_pCoreOf_le hT).trans hTK)
    (hKH.trans (le_normalizer_pCoreOf 2 H)) (pCoreOf_isPGroup 2 H)

end F7

open F7

theorem oTwoPrime_eq_of_normal_sylow {Q X : Subgroup G} (hQ : IsSylowTwoOf Q X)
    (hn : X ≤ Subgroup.normalizer (Q : Set G)) : oTwoPrime X = Q := by
  refine le_antisymm ?_ (le_oTwoPrime_of_isPGroup hQ.2.1 hQ.1)
  rw [oTwoPrime, Subgroup.closure_le]
  rintro x ⟨hxX, n, hn2⟩
  have hz : IsPGroup 2 (Subgroup.zpowers x) := by
    have hd : orderOf x ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one hn2
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
    refine IsPGroup.of_card (n := k) ?_
    rw [Nat.card_zpowers, hk]
  have hzX : Subgroup.zpowers x ≤ X := by
    rw [Subgroup.zpowers_le]; exact hxX
  obtain ⟨h, hhX, hle⟩ := isSylowTwoOf_exists_conj_le hQ hzX hz
  have hx' : x ∈ conjSub h Q := hle (Subgroup.mem_zpowers x)
  rw [mem_conjSub] at hx'
  have := (Subgroup.mem_normalizer_iff.mp (hn hhX) (h⁻¹ * x * h)).mp hx'
  simpa [mul_assoc] using this

theorem le_oTwoRes_sup_of_isSylowTwoOf {P X : Subgroup G} (hP : IsSylowTwoOf P X) :
    X ≤ oTwoRes X ⊔ P := by
  refine isSylowTwoOf_le_sup_of_two_power hP (le_normalizer_oTwoRes X) fun x hx => ?_
  obtain ⟨a, m, hm, hxm⟩ := Nat.exists_eq_two_pow_mul_odd (n := orderOf x)
    (orderOf_pos x).ne'
  refine ⟨a, Subgroup.subset_closure ⟨X.pow_mem hx _, m, hm, ?_⟩⟩
  rw [← pow_mul, ← hxm]
  exact pow_orderOf_eq_one x

end Finite

end CFSG.Quasithin
