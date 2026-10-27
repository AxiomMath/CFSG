module

public import CFSG.Quasithin.Vol2.Ch5Sec1L34SecFix

public section

namespace CFSG.Quasithin.H13.SecFix

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open scoped commutatorElement

variable {G : Type*} [Group G]

@[expose] def Cg (N : Subgroup G) (a b : G) : Prop := a⁻¹ * b ∈ N

theorem Cg.refl (N : Subgroup G) (a : G) : Cg N a a := by
  rw [Cg, inv_mul_cancel]
  exact N.one_mem

theorem Cg.symm {N : Subgroup G} {a b : G} (h : Cg N a b) : Cg N b a := by
  have := N.inv_mem h
  rwa [mul_inv_rev, inv_inv] at this

theorem Cg.trans {N : Subgroup G} {a b c : G} (h₁ : Cg N a b) (h₂ : Cg N b c) : Cg N a c := by
  have := N.mul_mem h₁ h₂
  rwa [show a⁻¹ * b * (b⁻¹ * c) = a⁻¹ * c by group] at this

theorem Cg.mul {N : Subgroup G} {a b c d : G} (h₁ : Cg N a b) (h₂ : Cg N c d)
    (hc : c ∈ Subgroup.normalizer (N : Set G)) : Cg N (a * c) (b * d) := by
  have h3 : c⁻¹ * (a⁻¹ * b) * c⁻¹⁻¹ ∈ N :=
    (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hc) _).mp h₁
  have := N.mul_mem h3 h₂
  rw [Cg]
  rwa [show c⁻¹ * (a⁻¹ * b) * c⁻¹⁻¹ * (c⁻¹ * d) = (a * c)⁻¹ * (b * d) by group] at this

theorem Cg.inv {N : Subgroup G} {a b : G} (h : Cg N a b)
    (ha : a ∈ Subgroup.normalizer (N : Set G)) : Cg N a⁻¹ b⁻¹ := by
  have := (Subgroup.mem_normalizer_iff.mp ha _).mp (N.inv_mem h)
  rw [Cg]
  rwa [show a * (a⁻¹ * b)⁻¹ * a⁻¹ = a⁻¹⁻¹ * b⁻¹ by group] at this

theorem Cg.mono {N N' : Subgroup G} {a b : G} (h : Cg N a b) (hN : N ≤ N') : Cg N' a b := hN h

theorem Cg.conj {N : Subgroup G} {a b g : G} (h : Cg N a b)
    (hg : g ∈ Subgroup.normalizer (N : Set G)) : Cg N (g * a * g⁻¹) (g * b * g⁻¹) := by
  have := (Subgroup.mem_normalizer_iff.mp hg _).mp h
  rw [Cg]
  rwa [show g * (a⁻¹ * b) * g⁻¹ = (g * a * g⁻¹)⁻¹ * (g * b * g⁻¹) by group] at this

theorem cg_one_iff {N : Subgroup G} {a : G} : Cg N a 1 ↔ a ∈ N := by
  rw [Cg, mul_one]
  exact ⟨fun h => by simpa using N.inv_mem h, fun h => N.inv_mem h⟩

theorem cg_mul_mem_left {N : Subgroup G} {p q : G} (hq : q ∈ N) : Cg N (p * q) p := by
  rw [Cg, show (p * q)⁻¹ * p = q⁻¹ by group]
  exact N.inv_mem hq

theorem mem_of_cg {N : Subgroup G} {a b : G} (h : Cg N a b) (hb : b ∈ N) : a ∈ N := by
  have := N.mul_mem hb (N.inv_mem h)
  rwa [show b * (a⁻¹ * b)⁻¹ = a by group] at this

@[expose] def nrm (y w : G) : G := w * (y * w * y⁻¹) * (y ^ 2 * w * (y ^ 2)⁻¹)

@[expose] def cmod (S X Y : Subgroup G) : Subgroup G where
  carrier := {x | x ∈ X ∧ x ∈ Subgroup.normalizer (Y : Set G) ∧ ∀ s ∈ S, s * x * s⁻¹ * x⁻¹ ∈ Y}
  mul_mem' := by
    rintro a b ⟨haX, haN, ha⟩ ⟨hbX, hbN, hb⟩
    refine ⟨X.mul_mem haX hbX, Subgroup.mul_mem _ haN hbN, fun s hs => ?_⟩
    have e : s * (a * b) * s⁻¹ * (a * b)⁻¹ =
        (s * a * s⁻¹ * a⁻¹) * (a * (s * b * s⁻¹ * b⁻¹) * a⁻¹) := by group
    rw [e]
    exact Y.mul_mem (ha s hs) ((Subgroup.mem_normalizer_iff.mp haN _).mp (hb s hs))
  one_mem' := ⟨X.one_mem, Subgroup.one_mem _, fun s _ => by simp⟩
  inv_mem' := by
    rintro a ⟨haX, haN, ha⟩
    refine ⟨X.inv_mem haX, Subgroup.inv_mem _ haN, fun s hs => ?_⟩
    have e : s * a⁻¹ * s⁻¹ * a⁻¹⁻¹ = a⁻¹ * (s * a * s⁻¹ * a⁻¹)⁻¹ * a⁻¹⁻¹ := by group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ haN) _).mp (Y.inv_mem (ha s hs))

theorem conj_mem_iff_commutator_mem {Y : Subgroup G} {s x : G} :
    s * x * s⁻¹ * x⁻¹ ∈ Y ↔ ⁅x, s⁆ ∈ Y := by
  rw [commutatorElement_def]
  constructor
  · intro hc
    have := Y.inv_mem hc
    rwa [show (s * x * s⁻¹ * x⁻¹)⁻¹ = x * s * x⁻¹ * s⁻¹ by group] at this
  · intro hc
    have := Y.inv_mem hc
    rwa [show (x * s * x⁻¹ * s⁻¹)⁻¹ = s * x * s⁻¹ * x⁻¹ by group] at this

namespace ElemSec

variable {A B : Subgroup G} (h : ElemSec A B)
include h

theorem cg_comm {N : Subgroup G} (hBN : B ≤ N) {a b : G} (ha : a ∈ A) (hb : b ∈ A) :
    Cg N (a * b) (b * a) := by
  rw [Cg]
  have h1 := hBN (h.comm b⁻¹ (A.inv_mem hb) a⁻¹ (A.inv_mem ha))
  rwa [show b⁻¹ * a⁻¹ * b⁻¹⁻¹ * a⁻¹⁻¹ = (a * b)⁻¹ * (b * a) by group] at h1

theorem cg_conj {N : Subgroup G} (hBN : B ≤ N) {x w : G} (hx : x ∈ A) (hw : w ∈ A) :
    Cg N (x * w * x⁻¹) w := by
  rw [Cg]
  have h1 := h.comm x hx w⁻¹ (A.inv_mem hw)
  have h2 := hBN h1
  rwa [show x * w⁻¹ * x⁻¹ * w⁻¹⁻¹ = (x * w * x⁻¹)⁻¹ * w by group] at h2

end ElemSec

@[expose] def nxt (U B X : Subgroup G) : Subgroup G := ⁅X, U⁆ ⊔ B

theorem le_nxt (U B X : Subgroup G) : B ≤ nxt U B X := le_sup_right

theorem commutator_le_nxt (U B X : Subgroup G) : ⁅X, U⁆ ≤ nxt U B X := le_sup_left

theorem commutator_mem_nxt {U B X : Subgroup G} {x u : G} (hx : x ∈ X) (hu : u ∈ U) :
    ⁅x, u⁆ ∈ nxt U B X :=
  commutator_le_nxt U B X (Subgroup.commutator_mem_commutator hx hu)

theorem nxt_le {U B X : Subgroup G} (hUX : U ≤ Subgroup.normalizer (X : Set G)) (hBX : B ≤ X) :
    nxt U B X ≤ X :=
  sup_le (F112W.commutator_le_self_of_le_normalizer hUX) hBX

theorem mem_normalizer_nxt {U B X : Subgroup G} {g : G}
    (hX : g ∈ Subgroup.normalizer (X : Set G)) (hU : g ∈ Subgroup.normalizer (U : Set G))
    (hB : g ∈ Subgroup.normalizer (B : Set G)) :
    g ∈ Subgroup.normalizer (nxt U B X : Set G) := by
  have hc := A4.mem_normalizer_commutator hX hU
  have hle : Subgroup.zpowers g ≤ Subgroup.normalizer (nxt U B X : Set G) :=
    F1.le_normalizer_sup (Subgroup.zpowers_le.mpr hc) (Subgroup.zpowers_le.mpr hB)
  exact hle (Subgroup.mem_zpowers g)

theorem le_normalizer_nxt {U B X : Subgroup G} (hUX : U ≤ Subgroup.normalizer (X : Set G))
    (hUB : U ≤ Subgroup.normalizer (B : Set G)) :
    U ≤ Subgroup.normalizer (nxt U B X : Set G) := fun _ hu =>
  mem_normalizer_nxt (hUX hu) (Subgroup.le_normalizer hu) (hUB hu)

theorem cg_conj_nxt {U B X : Subgroup G} {u w : G} (hu : u ∈ U) (hw : w ∈ X) :
    Cg (nxt U B X) (u * w * u⁻¹) w := by
  rw [Cg]
  have h0 : ⁅u, w⁻¹⁆ ∈ ⁅U, X⁆ := Subgroup.commutator_mem_commutator hu (X.inv_mem hw)
  rw [Subgroup.commutator_comm] at h0
  have h1 := commutator_le_nxt U B X h0
  rwa [commutatorElement_def, show u * w⁻¹ * u⁻¹ * w⁻¹⁻¹ = (u * w * u⁻¹)⁻¹ * w by group] at h1

theorem mem_normalizer_cmod {S X Y : Subgroup G} {g : G}
    (hS : g ∈ Subgroup.normalizer (S : Set G)) (hX : g ∈ Subgroup.normalizer (X : Set G))
    (hY : g ∈ Subgroup.normalizer (Y : Set G)) :
    g ∈ Subgroup.normalizer (cmod S X Y : Set G) := by
  have key : ∀ g : G, g ∈ Subgroup.normalizer (S : Set G) → g ∈ Subgroup.normalizer (X : Set G) →
      g ∈ Subgroup.normalizer (Y : Set G) → ∀ x ∈ cmod S X Y, g * x * g⁻¹ ∈ cmod S X Y := by
    intro g hS hX hY x ⟨hxX, hxN, hx⟩
    refine ⟨(Subgroup.mem_normalizer_iff.mp hX x).mp hxX,
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hY hxN) (Subgroup.inv_mem _ hY), fun s hs => ?_⟩
    have hs' : g⁻¹ * s * g⁻¹⁻¹ ∈ S :=
      (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hS) s).mp hs
    have h1 := (Subgroup.mem_normalizer_iff.mp hY _).mp (hx _ hs')
    rwa [show g * (g⁻¹ * s * g⁻¹⁻¹ * x * (g⁻¹ * s * g⁻¹⁻¹)⁻¹ * x⁻¹) * g⁻¹ =
      s * (g * x * g⁻¹) * s⁻¹ * (g * x * g⁻¹)⁻¹ by group] at h1
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => key g hS hX hY x hx, fun hx => ?_⟩
  have := key g⁻¹ (Subgroup.inv_mem _ hS) (Subgroup.inv_mem _ hX) (Subgroup.inv_mem _ hY) _ hx
  simpa [mul_assoc] using this

namespace ElemSec

variable {A B : Subgroup G} (h : ElemSec A B)
include h

theorem nxt_facts {U X : Subgroup G} (hBX : B ≤ X) (hXA : X ≤ A)
    (hUX : U ≤ Subgroup.normalizer (X : Set G)) (hUB : U ≤ Subgroup.normalizer (B : Set G)) :
    nxt U B X ≤ X ∧ nxt U B (nxt U B X) ≤ nxt U B X ∧
      A ≤ Subgroup.normalizer (nxt U B X : Set G) ∧
      A ≤ Subgroup.normalizer (nxt U B (nxt U B X) : Set G) := by
  have h1 := nxt_le hUX hBX
  have hU1 := le_normalizer_nxt hUX hUB
  have h2 := nxt_le hU1 (le_nxt U B X)
  exact ⟨h1, h2, h.le_normalizer (le_nxt U B X) (h1.trans hXA),
    h.le_normalizer (le_nxt U B _) (h2.trans (h1.trans hXA))⟩

theorem cg_commutator_mul {U X : Subgroup G} (hBX : B ≤ X) (hXA : X ≤ A)
    (hUX : U ≤ Subgroup.normalizer (X : Set G)) (hUB : U ≤ Subgroup.normalizer (B : Set G))
    {x u v : G} (hx : x ∈ X) (hu : u ∈ U) (hv : v ∈ U) :
    Cg (nxt U B (nxt U B X)) (⁅x, u * v⁆) (⁅x, u⁆ * ⁅x, v⁆) := by
  obtain ⟨h1, -, -, hA2⟩ := h.nxt_facts hBX hXA hUX hUB
  have e : ⁅x, u * v⁆ = ⁅x, u⁆ * (u * ⁅x, v⁆ * u⁻¹) := by
    simp only [commutatorElement_def]
    group
  rw [e]
  have hxv : ⁅x, v⁆ ∈ nxt U B X := commutator_mem_nxt hx hv
  have hc : u * ⁅x, v⁆ * u⁻¹ ∈ A :=
    hXA ((Subgroup.mem_normalizer_iff.mp (hUX hu) _).mp (h1 hxv))
  exact Cg.mul (Cg.refl _ _) (cg_conj_nxt hu hxv) (hA2 hc)

theorem cg_swap {N : Subgroup G} (hBN : B ≤ N) (hNA : N ≤ A) {p a b : G} (ha : a ∈ A)
    (hb : b ∈ A) : Cg N (p * a * b) (p * b * a) := by
  have hNn := h.le_normalizer hBN hNA
  have := Cg.mul (Cg.refl N p) (h.cg_comm hBN ha hb) (hNn (A.mul_mem ha hb))
  simpa only [mul_assoc] using this

theorem cg_mul_right {N : Subgroup G} (hBN : B ≤ N) (hNA : N ≤ A) {u v z : G} (h₁ : Cg N u v)
    (hz : z ∈ A) : Cg N (u * z) (v * z) :=
  Cg.mul h₁ (Cg.refl N z) (h.le_normalizer hBN hNA hz)

theorem cg_nrm_mul {N : Subgroup G} (hBN : B ≤ N) (hNA : N ≤ A) {y : G}
    (hyA : y ∈ Subgroup.normalizer (A : Set G)) {w w' : G} (hw : w ∈ A) (hw' : w' ∈ A) :
    Cg N (nrm y (w * w')) (nrm y w * nrm y w') := by
  have hc : ∀ z ∈ A, y * z * y⁻¹ ∈ A := fun z hz => (Subgroup.mem_normalizer_iff.mp hyA z).mp hz
  have hc2 : ∀ z ∈ A, y ^ 2 * z * (y ^ 2)⁻¹ ∈ A := fun z hz =>
    (Subgroup.mem_normalizer_iff.mp (Subgroup.pow_mem _ hyA 2) z).mp hz
  set a := y * w * y⁻¹
  set a' := y * w' * y⁻¹
  set b := y ^ 2 * w * (y ^ 2)⁻¹
  set b' := y ^ 2 * w' * (y ^ 2)⁻¹
  have ha := hc w hw
  have ha' := hc w' hw'
  have hb := hc2 w hw
  have hb' := hc2 w' hw'
  have e1 : nrm y (w * w') = w * w' * a * a' * b * b' := by
    simp only [nrm, a, a', b, b']
    group
  have e2 : nrm y w * nrm y w' = w * a * b * w' * a' * b' := by
    simp only [nrm, a, a', b, b']
    group
  rw [e1, e2]
  have s1 : Cg N (w * w' * a * a' * b * b') (w * a * w' * a' * b * b') :=
    h.cg_mul_right hBN hNA (h.cg_mul_right hBN hNA (h.cg_mul_right hBN hNA
      (h.cg_swap hBN hNA hw' ha) ha') hb) hb'
  have s2 : Cg N (w * a * w' * a' * b * b') (w * a * w' * b * a' * b') :=
    h.cg_mul_right hBN hNA (h.cg_swap hBN hNA ha' hb) hb'
  have s3 : Cg N (w * a * w' * b * a' * b') (w * a * b * w' * a' * b') :=
    h.cg_mul_right hBN hNA (h.cg_mul_right hBN hNA
      (h.cg_swap hBN hNA hw' hb) ha') hb'
  exact s1.trans (s2.trans s3)

theorem cg_shift {U X : Subgroup G} (hBX : B ≤ X) (hXA : X ≤ A)
    (hUX : U ≤ Subgroup.normalizer (X : Set G)) (hUB : U ≤ Subgroup.normalizer (B : Set G))
    {e x v : G} (he : e ∈ nxt U B X) (hx : x ∈ X) (hv : v ∈ U) :
    Cg (nxt U B (nxt U B X)) (⁅e * x, v⁆) (⁅x, v⁆) := by
  obtain ⟨h1, -, -, -⟩ := h.nxt_facts hBX hXA hUX hUB
  have e1 : ⁅e * x, v⁆ = (e * ⁅x, v⁆ * e⁻¹) * ⁅e, v⁆ := by
    simp only [commutatorElement_def]
    group
  rw [e1]
  exact (cg_mul_mem_left (commutator_mem_nxt he hv)).trans
    (h.cg_conj (le_nxt U B _) (h1.trans hXA he) (h1.trans hXA (commutator_mem_nxt hx hv)))

theorem nrm_commutator_mem {U X O : Subgroup G} {y : G} (hBX : B ≤ X) (hXA : X ≤ A)
    (hUX : U ≤ Subgroup.normalizer (X : Set G)) (hUB : U ≤ Subgroup.normalizer (B : Set G))
    (hyX : y ∈ Subgroup.normalizer (X : Set G)) (hyU : y ∈ Subgroup.normalizer (U : Set G))
    (hyB : y ∈ Subgroup.normalizer (B : Set G))
    (hO : ∀ o ∈ O, ∀ x ∈ A, o * x * o⁻¹ * x⁻¹ ∈ B)
    (hnorm : ∀ u ∈ U, u * (y * u * y⁻¹) * (y ^ 2 * u * (y ^ 2)⁻¹) ∈ O)
    (hyc : ∀ x ∈ X, y * x * y⁻¹ * x⁻¹ ∈ nxt U B X) {x u : G} (hx : x ∈ X) (hu : u ∈ U) :
    nrm y ⁅x, u⁆ ∈ nxt U B (nxt U B X) := by
  obtain ⟨h1, h2, hA1, hA2⟩ := h.nxt_facts hBX hXA hUX hUB
  set X₁ := nxt U B X with hX₁
  set X₂ := nxt U B X₁ with hX₂
  have hBX₂ : B ≤ X₂ := le_nxt U B X₁
  have hX₂A : X₂ ≤ A := h2.trans (h1.trans hXA)
  have hyX₁ : y ∈ Subgroup.normalizer (X₁ : Set G) := mem_normalizer_nxt hyX hyU hyB
  have hcU : ∀ v ∈ U, y * v * y⁻¹ ∈ U := fun v hv => (Subgroup.mem_normalizer_iff.mp hyU v).mp hv
  have hcU2 : ∀ v ∈ U, y ^ 2 * v * (y ^ 2)⁻¹ ∈ U := fun v hv =>
    (Subgroup.mem_normalizer_iff.mp (Subgroup.pow_mem _ hyU 2) v).mp hv
  set u₁ := y * u * y⁻¹ with hu₁
  set u₂ := y ^ 2 * u * (y ^ 2)⁻¹ with hu₂
  have hu₁U : u₁ ∈ U := hcU u hu
  have hu₂U : u₂ ∈ U := hcU2 u hu
  have hxA := hXA hx
  set d := y * x * y⁻¹ * x⁻¹ with hd
  have hdX₁ : d ∈ X₁ := hyc x hx
  set d₂ := y ^ 2 * x * (y ^ 2)⁻¹ * x⁻¹ with hd₂
  have hd₂X₁ : d₂ ∈ X₁ := by
    have e : d₂ = (y * d * y⁻¹) * d := by
      simp only [d₂, d, pow_two]
      group
    rw [e]
    exact X₁.mul_mem ((Subgroup.mem_normalizer_iff.mp hyX₁ d).mp hdX₁) hdX₁
  have hcomm_mem : ∀ v ∈ U, ⁅x, v⁆ ∈ X₁ := fun v hv => commutator_mem_nxt hx hv
  have hcA : ∀ v ∈ U, ⁅x, v⁆ ∈ A := fun v hv => h1.trans hXA (hcomm_mem v hv)
  have shift : ∀ e ∈ X₁, ∀ v ∈ U, Cg X₂ (⁅e * x, v⁆) (⁅x, v⁆) := by
    intro e he v hv
    have e1 : ⁅e * x, v⁆ = (e * ⁅x, v⁆ * e⁻¹) * ⁅e, v⁆ := by
      simp only [commutatorElement_def]
      group
    rw [e1]
    have hev : ⁅e, v⁆ ∈ X₂ := commutator_mem_nxt he hv
    have heA : e ∈ A := h1.trans hXA he
    have c1 : Cg X₂ (e * ⁅x, v⁆ * e⁻¹ * ⁅e, v⁆) (e * ⁅x, v⁆ * e⁻¹) := cg_mul_mem_left hev
    exact c1.trans (h.cg_conj hBX₂ heA (hcA v hv))
  have ey : y * ⁅x, u⁆ * y⁻¹ = ⁅d * x, u₁⁆ := by
    simp only [commutatorElement_def, d, u₁]
    group
  have ey2 : y ^ 2 * ⁅x, u⁆ * (y ^ 2)⁻¹ = ⁅d₂ * x, u₂⁆ := by
    simp only [commutatorElement_def, d₂, u₂, pow_two]
    group
  have hN := h.le_normalizer hBX₂ hX₂A
  have hyc1 : y * ⁅x, u⁆ * y⁻¹ ∈ A :=
    hXA ((Subgroup.mem_normalizer_iff.mp hyX _).mp (h1 (hcomm_mem u hu)))
  have hyc2 : y ^ 2 * ⁅x, u⁆ * (y ^ 2)⁻¹ ∈ A :=
    hXA ((Subgroup.mem_normalizer_iff.mp (Subgroup.pow_mem _ hyX 2) _).mp (h1 (hcomm_mem u hu)))
  have c2 : Cg X₂ (nrm y ⁅x, u⁆) (⁅x, u⁆ * ⁅x, u₁⁆ * ⁅x, u₂⁆) := by
    rw [nrm, ey, ey2]
    refine Cg.mul (Cg.mul (Cg.refl _ _) (shift d hdX₁ u₁ hu₁U) ?_) (shift d₂ hd₂X₁ u₂ hu₂U) ?_
    · rw [← ey]
      exact hN hyc1
    · rw [← ey2]
      exact hN hyc2
  have c3 : Cg X₂ (⁅x, u * u₁ * u₂⁆) (⁅x, u⁆ * ⁅x, u₁⁆ * ⁅x, u₂⁆) := by
    have m1 := h.cg_commutator_mul hBX hXA hUX hUB hx (U.mul_mem hu hu₁U) hu₂U
    have m2 := h.cg_commutator_mul hBX hXA hUX hUB hx hu hu₁U
    exact m1.trans (h.cg_mul_right hBX₂ hX₂A m2 (hcA u₂ hu₂U))
  have hfin : ⁅x, u * u₁ * u₂⁆ ∈ X₂ := by
    have ho := hO _ (hnorm u hu) x hxA
    have e : ⁅x, u * u₁ * u₂⁆ = (u * u₁ * u₂ * x * (u * u₁ * u₂)⁻¹ * x⁻¹)⁻¹ := by
      rw [commutatorElement_def]
      group
    rw [e]
    exact hBX₂ (B.inv_mem ho)
  exact mem_of_cg (c2.trans c3.symm) hfin

theorem desc_fpf {U X O : Subgroup G} {y : G} (hBX : B ≤ X) (hXA : X ≤ A)
    (hUX : U ≤ Subgroup.normalizer (X : Set G)) (hUB : U ≤ Subgroup.normalizer (B : Set G))
    (hyA : y ∈ Subgroup.normalizer (A : Set G))
    (hyX : y ∈ Subgroup.normalizer (X : Set G)) (hyU : y ∈ Subgroup.normalizer (U : Set G))
    (hyB : y ∈ Subgroup.normalizer (B : Set G))
    (hO : ∀ o ∈ O, ∀ x ∈ A, o * x * o⁻¹ * x⁻¹ ∈ B)
    (hnorm : ∀ u ∈ U, u * (y * u * y⁻¹) * (y ^ 2 * u * (y ^ 2)⁻¹) ∈ O)
    (hyc : ∀ x ∈ X, y * x * y⁻¹ * x⁻¹ ∈ nxt U B X) :
    fixMod y (nxt U B X) (nxt U B (nxt U B X)) = nxt U B (nxt U B X) := by
  obtain ⟨h1, h2, hA1, hA2⟩ := h.nxt_facts hBX hXA hUX hUB
  set X₁ := nxt U B X with hX₁
  set X₂ := nxt U B X₁ with hX₂
  have hBX₂ : B ≤ X₂ := le_nxt U B X₁
  have hX₁A : X₁ ≤ A := h1.trans hXA
  have hX₂A : X₂ ≤ A := h2.trans hX₁A
  have hyX₁ : y ∈ Subgroup.normalizer (X₁ : Set G) := mem_normalizer_nxt hyX hyU hyB
  have hyX₂ : y ∈ Subgroup.normalizer (X₂ : Set G) := mem_normalizer_nxt hyX₁ hyU hyB
  have hcA : ∀ z ∈ A, y * z * y⁻¹ ∈ A := fun z hz => (Subgroup.mem_normalizer_iff.mp hyA z).mp hz
  have hnrm : ∀ w ∈ X₁, nrm y w ∈ X₂ := by
    let S : Subgroup G :=
      { carrier := {w | w ∈ X₁ ∧ nrm y w ∈ X₂}
        mul_mem' := by
          rintro w w' ⟨hw, hnw⟩ ⟨hw', hnw'⟩
          exact ⟨X₁.mul_mem hw hw', mem_of_cg (h.cg_nrm_mul hBX₂ hX₂A hyA (hX₁A hw) (hX₁A hw'))
            (X₂.mul_mem hnw hnw')⟩
        one_mem' := ⟨X₁.one_mem, by simp [nrm]⟩
        inv_mem' := by
          rintro w ⟨hw, hnw⟩
          refine ⟨X₁.inv_mem hw, ?_⟩
          have hc := h.cg_nrm_mul hBX₂ hX₂A hyA (hX₁A (X₁.inv_mem hw)) (hX₁A hw)
          rw [inv_mul_cancel, show nrm y 1 = 1 by simp [nrm], Cg, inv_one, one_mul] at hc
          have := X₂.mul_mem hc (X₂.inv_mem hnw)
          rwa [mul_inv_cancel_right] at this }
    have hle : X₁ ≤ S := by
      refine sup_le ?_ ?_
      · rw [Subgroup.commutator_le]
        intro x hx u hu
        exact ⟨commutator_mem_nxt hx hu,
          h.nrm_commutator_mem hBX hXA hUX hUB hyX hyU hyB hO hnorm hyc hx hu⟩
      · intro b hb
        refine ⟨le_nxt U B X hb, hBX₂ ?_⟩
        have hb1 : y * b * y⁻¹ ∈ B := (Subgroup.mem_normalizer_iff.mp hyB b).mp hb
        have hb2 : y ^ 2 * b * (y ^ 2)⁻¹ ∈ B :=
          (Subgroup.mem_normalizer_iff.mp (Subgroup.pow_mem _ hyB 2) b).mp hb
        exact B.mul_mem (B.mul_mem hb hb1) hb2
    exact fun w hw => (hle hw).2
  apply le_antisymm
  · intro x hx
    rw [h.mem_fixMod_iff hBX₂ h2 hX₁A] at hx
    obtain ⟨hxX₁, hc⟩ := hx
    have hxA := hX₁A hxX₁
    have hN := h.le_normalizer hBX₂ hX₂A
    have c1 : Cg X₂ (y * x * y⁻¹) x := by
      rw [Cg]
      have := (Subgroup.mem_normalizer_iff.mp (hN (A.inv_mem hxA)) _).mp (X₂.inv_mem hc)
      rwa [show x⁻¹ * (y * x * y⁻¹ * x⁻¹)⁻¹ * x⁻¹⁻¹ = (y * x * y⁻¹)⁻¹ * x by group] at this
    have c2 : Cg X₂ (y ^ 2 * x * (y ^ 2)⁻¹) x := by
      have c0 : Cg X₂ (y * (y * x * y⁻¹) * y⁻¹) (y * x * y⁻¹) := by
        rw [Cg]
        have := (Subgroup.mem_normalizer_iff.mp hyX₂ _).mp c1
        rwa [show y * ((y * x * y⁻¹)⁻¹ * x) * y⁻¹ =
          (y * (y * x * y⁻¹) * y⁻¹)⁻¹ * (y * x * y⁻¹) by
            simp only [mul_assoc, mul_inv_rev, inv_inv, inv_mul_cancel_left]] at this
      rw [show y ^ 2 * x * (y ^ 2)⁻¹ = y * (y * x * y⁻¹) * y⁻¹ by rw [pow_two]; group]
      exact c0.trans c1
    have c3 : Cg X₂ (nrm y x) (x * x * x) :=
      Cg.mul (Cg.mul (Cg.refl _ _) c1 (hN (hcA x hxA))) c2
        (hN ((Subgroup.mem_normalizer_iff.mp (Subgroup.pow_mem _ hyA 2) x).mp hxA))
    have c4 : Cg X₂ (x * x * x) x := by
      rw [Cg]
      have := X₂.inv_mem (hBX₂ (h.sq x hxA))
      rwa [show (x * x)⁻¹ = (x * x * x)⁻¹ * x by group] at this
    exact mem_of_cg (c3.trans c4).symm (hnrm x hxX₁)
  · exact h.le_fixMod hBX₂ h2 hX₁A hyX₂

theorem commutator_mem_of_invariant {U O : Subgroup G} {y x : G} (hx : x ∈ A)
    (hUA : U ≤ Subgroup.normalizer (A : Set G)) (hOU : O ≤ U)
    (hxU : ∀ u ∈ U, ⁅x, u⁆ ∈ cmod U A B)
    (hinv : ∀ u ∈ U, Cg B (⁅x, y * u * y⁻¹⁆) (⁅x, u⁆))
    (hO : ∀ o ∈ O, ∀ x ∈ A, o * x * o⁻¹ * x⁻¹ ∈ B)
    (hsurj : ∀ u ∈ U, ∃ s ∈ U, u⁻¹ * (s * (y * s * y⁻¹)⁻¹) ∈ O)
    (hyU : ∀ u ∈ U, y * u * y⁻¹ ∈ U) :
    ∀ u ∈ U, ⁅x, u⁆ ∈ B := by
  have hNB := h.normalizes
  have hcA : ∀ u ∈ U, ⁅x, u⁆ ∈ A := fun u hu => (hxU u hu).1
  have hmul : ∀ u ∈ U, ∀ v ∈ U, Cg B (⁅x, u * v⁆) (⁅x, u⁆ * ⁅x, v⁆) := by
    intro u hu v hv
    have e : ⁅x, u * v⁆ = ⁅x, u⁆ * (u * ⁅x, v⁆ * u⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [e]
    set w := ⁅x, v⁆ with hw
    have hwA : w ∈ A := hcA v hv
    have hc : Cg B (u * w * u⁻¹) w := by
      rw [Cg]
      have h1 := (hxU v hv).2.2 u hu
      have h2 := (Subgroup.mem_normalizer_iff.mp (hNB (A.inv_mem hwA)) _).mp (B.inv_mem h1)
      rwa [show w⁻¹ * (u * w * u⁻¹ * w⁻¹)⁻¹ * w⁻¹⁻¹ = (u * w * u⁻¹)⁻¹ * w by group] at h2
    exact Cg.mul (Cg.refl _ _) hc (hNB ((Subgroup.mem_normalizer_iff.mp (hUA hu) _).mp hwA))
  have hinv' : ∀ v ∈ U, Cg B (⁅x, v⁻¹⁆) (⁅x, v⁆⁻¹) := by
    intro v hv
    have h1 := hmul v hv v⁻¹ (U.inv_mem hv)
    have e0 : ⁅x, v * v⁻¹⁆ = 1 := by
      rw [mul_inv_cancel, commutatorElement_def]
      group
    rw [e0, Cg, inv_one, one_mul] at h1
    rw [Cg]
    have := B.inv_mem h1
    rwa [show (⁅x, v⁆ * ⁅x, v⁻¹⁆)⁻¹ = (⁅x, v⁻¹⁆)⁻¹ * ⁅x, v⁆⁻¹ by group] at this
  intro u hu
  obtain ⟨s, hs, ho⟩ := hsurj u hu
  set t := y * s * y⁻¹ with ht
  have htU : t ∈ U := hyU s hs
  set o := u⁻¹ * (s * t⁻¹) with hodef
  have hoU : o ∈ U := hOU ho
  have hu' : u = s * t⁻¹ * o⁻¹ := by
    rw [hodef]
    group
  have hob : ⁅x, o⁻¹⁆ ∈ B :=
    conj_mem_iff_commutator_mem.mp (hO o⁻¹ (O.inv_mem ho) x hx)
  have hstU : s * t⁻¹ ∈ U := U.mul_mem hs (U.inv_mem htU)
  have c1 : Cg B (⁅x, u⁆) (⁅x, s⁆ * ⁅x, t⁻¹⁆ * ⁅x, o⁻¹⁆) := by
    rw [hu']
    have m1 := hmul _ hstU _ (U.inv_mem hoU)
    have m2 := hmul _ hs _ (U.inv_mem htU)
    exact m1.trans (h.cg_mul_right le_rfl h.le m2 (hcA _ (U.inv_mem hoU)))
  have c2 : Cg B (⁅x, t⁻¹⁆) (⁅x, s⁆⁻¹) :=
    (hinv' t htU).trans ((hinv s hs).inv (hNB (hcA t htU)))
  have c3 : Cg B (⁅x, s⁆ * ⁅x, t⁻¹⁆ * ⁅x, o⁻¹⁆) (⁅x, s⁆ * ⁅x, s⁆⁻¹ * ⁅x, o⁻¹⁆) :=
    h.cg_mul_right le_rfl h.le (Cg.mul (Cg.refl _ _) c2 (hNB (hcA _ (U.inv_mem htU))))
      (hcA _ (U.inv_mem hoU))
  rw [mul_inv_cancel, one_mul] at c3
  exact mem_of_cg (c1.trans c3) hob

theorem asc_core {U : Subgroup G} {y x : G}
    (hxU : ∀ u ∈ U, ⁅x, u⁆ ∈ A)
    (hyx : y * x * y⁻¹ * x⁻¹ ∈ cmod U A B)
    (hyc : ∀ u ∈ U, y * ⁅x, u⁆ * y⁻¹ * (⁅x, u⁆)⁻¹ ∈ B)
    (hyU : ∀ u ∈ U, y * u * y⁻¹ ∈ U) :
    ∀ u ∈ U, Cg B (⁅x, y * u * y⁻¹⁆) (⁅x, u⁆) := by
  intro u hu
  set e := y * x * y⁻¹ * x⁻¹ with he
  set v := y * u * y⁻¹ with hv
  have hvU : v ∈ U := hyU u hu
  have heA : e ∈ A := hyx.1
  have hev : ⁅e, v⁆ ∈ B := conj_mem_iff_commutator_mem.mp (hyx.2.2 v hvU)
  have e1 : y * ⁅x, u⁆ * y⁻¹ = (e * ⁅x, v⁆ * e⁻¹) * ⁅e, v⁆ := by
    simp only [commutatorElement_def, e, v]
    group
  have c1 : Cg B (y * ⁅x, u⁆ * y⁻¹) (⁅x, v⁆) := by
    rw [e1]
    exact (cg_mul_mem_left hev).trans (h.cg_conj le_rfl heA (hxU v hvU))
  have c2 : Cg B (y * ⁅x, u⁆ * y⁻¹) (⁅x, u⁆) := by
    rw [Cg]
    have hb := hyc u hu
    have := (Subgroup.mem_normalizer_iff.mp (h.normalizes (A.inv_mem (hxU u hu))) _).mp
      (B.inv_mem hb)
    rwa [show (⁅x, u⁆)⁻¹ * (y * ⁅x, u⁆ * y⁻¹ * (⁅x, u⁆)⁻¹)⁻¹ * (⁅x, u⁆)⁻¹⁻¹ =
      (y * ⁅x, u⁆ * y⁻¹)⁻¹ * ⁅x, u⁆ by group] at this
  exact c1.symm.trans c2

theorem le_cmod {U : Subgroup G} (hUB : U ≤ Subgroup.normalizer (B : Set G)) :
    B ≤ cmod U A B := fun b hb =>
  ⟨h.le hb, h.normalizes (h.le hb), fun _ hu =>
    B.mul_mem ((Subgroup.mem_normalizer_iff.mp (hUB hu) b).mp hb) (B.inv_mem hb)⟩

theorem asc_fpf {U O : Subgroup G} {y : G} (hUA : U ≤ Subgroup.normalizer (A : Set G))
    (hUB : U ≤ Subgroup.normalizer (B : Set G))
    (hOU : O ≤ U) (hAU : ∀ x ∈ A, ∀ u ∈ U, ⁅x, u⁆ ∈ cmod U A B)
    (hyZ : ∀ z ∈ cmod U A B, y * z * y⁻¹ * z⁻¹ ∈ B)
    (hO : ∀ o ∈ O, ∀ x ∈ A, o * x * o⁻¹ * x⁻¹ ∈ B)
    (hsurj : ∀ u ∈ U, ∃ s ∈ U, u⁻¹ * (s * (y * s * y⁻¹)⁻¹) ∈ O)
    (hyA : y ∈ Subgroup.normalizer (A : Set G)) (hyU : y ∈ Subgroup.normalizer (U : Set G))
    (hyB : y ∈ Subgroup.normalizer (B : Set G)) :
    fixMod y A (cmod U A B) = cmod U A B := by
  have hBZ := h.le_cmod hUB
  have hZA : cmod U A B ≤ A := fun _ hz => hz.1
  have hyU' : ∀ u ∈ U, y * u * y⁻¹ ∈ U := fun u hu => (Subgroup.mem_normalizer_iff.mp hyU u).mp hu
  apply le_antisymm
  · intro x hx
    rw [h.mem_fixMod_iff hBZ hZA le_rfl] at hx
    obtain ⟨hxA, hyx⟩ := hx
    have hinv := h.asc_core (fun u hu => hZA (hAU x hxA u hu)) hyx
      (fun u hu => hyZ _ (hAU x hxA u hu)) hyU'
    have hc := h.commutator_mem_of_invariant hxA hUA hOU (hAU x hxA) hinv hO hsurj hyU'
    exact ⟨hxA, h.normalizes hxA, fun u hu => conj_mem_iff_commutator_mem.mpr (hc u hu)⟩
  · exact h.le_fixMod hBZ hZA le_rfl (mem_normalizer_cmod hyU hyA hyB)

theorem asc_zero {U O : Subgroup G} {y : G} (hUA : U ≤ Subgroup.normalizer (A : Set G))
    (hOU : O ≤ U) (hA₁Z : nxt U B A ≤ cmod U A B)
    (hyA : ∀ x ∈ A, y * x * y⁻¹ * x⁻¹ ∈ cmod U A B)
    (hyA₁ : ∀ w ∈ nxt U B A, y * w * y⁻¹ * w⁻¹ ∈ B)
    (hO : ∀ o ∈ O, ∀ x ∈ A, o * x * o⁻¹ * x⁻¹ ∈ B)
    (hsurj : ∀ u ∈ U, ∃ s ∈ U, u⁻¹ * (s * (y * s * y⁻¹)⁻¹) ∈ O)
    (hyU : y ∈ Subgroup.normalizer (U : Set G)) :
    ∀ x ∈ A, ∀ u ∈ U, ⁅x, u⁆ ∈ B := by
  have hyU' : ∀ u ∈ U, y * u * y⁻¹ ∈ U := fun u hu => (Subgroup.mem_normalizer_iff.mp hyU u).mp hu
  intro x hx
  have hxU : ∀ u ∈ U, ⁅x, u⁆ ∈ cmod U A B := fun u hu => hA₁Z (commutator_mem_nxt hx hu)
  have hinv := h.asc_core (fun u hu => (hxU u hu).1) (hyA x hx)
    (fun u hu => hyA₁ _ (commutator_mem_nxt hx hu)) hyU'
  exact h.commutator_mem_of_invariant hx hUA hOU hxU hinv hO hsurj hyU'

end ElemSec

end CFSG.Quasithin.H13.SecFix
