module

public import CFSG.LocalAnalysis.UniquenessCase.UC6K36OddCount
public import CFSG.LocalAnalysis.UniquenessCase.UC6K36OddAlg
public import CFSG.LocalAnalysis.UniquenessCase.UC6K36Cent

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK

open CFSG.Open Subgroup

namespace Odd

variable {G : Type} [Group G] [Finite G]

def centerOf (L : Subgroup G) : Subgroup G := (Subgroup.center ↥L).map L.subtype

theorem mem_centerOf {L : Subgroup G} {z : G} :
    z ∈ centerOf L ↔ z ∈ L ∧ ∀ y ∈ L, y * z = z * y := by
  constructor
  · rintro ⟨⟨z', hz'L⟩, hz', rfl⟩
    refine ⟨hz'L, fun y hy => ?_⟩
    have := Subgroup.mem_center_iff.1 hz' ⟨y, hy⟩
    exact congrArg Subtype.val this
  · rintro ⟨hzL, hz⟩
    exact ⟨⟨z, hzL⟩, Subgroup.mem_center_iff.2 fun g => Subtype.ext (hz g g.2), rfl⟩

theorem centerOf_le (L : Subgroup G) : centerOf L ≤ L := fun _ hz => (mem_centerOf.1 hz).1

variable (L : Subgroup G) [L.Normal]

theorem conj_mem_centerOf {z : G} (hz : z ∈ centerOf L) (g : G) : g * z * g⁻¹ ∈ centerOf L := by
  rw [mem_centerOf] at hz ⊢
  obtain ⟨hzL, hzc⟩ := hz
  refine ⟨Subgroup.Normal.conj_mem inferInstance z hzL g, fun y hy => ?_⟩
  have hy' : g⁻¹ * y * g ∈ L := by
    simpa using Subgroup.Normal.conj_mem inferInstance y hy g⁻¹
  have h1 := hzc _ hy'
  calc y * (g * z * g⁻¹) = g * ((g⁻¹ * y * g) * z) * g⁻¹ := by group
    _ = g * (z * (g⁻¹ * y * g)) * g⁻¹ := by rw [h1]
    _ = (g * z * g⁻¹) * y := by group

instance centerOf_normal : (centerOf L).Normal := ⟨fun _ hz g => conj_mem_centerOf L hz g⟩

theorem comm_mem {e y : G} (hy : y ∈ L) : e * y * e⁻¹ * y⁻¹ ∈ L :=
  L.mul_mem (Subgroup.Normal.conj_mem inferInstance y hy e) (L.inv_mem hy)

theorem comm_mul {e y y' : G} (hy : y ∈ L) (hy' : e * y' * e⁻¹ * y'⁻¹ ∈ centerOf L) :
    e * (y * y') * e⁻¹ * (y * y')⁻¹ = (e * y * e⁻¹ * y⁻¹) * (e * y' * e⁻¹ * y'⁻¹) := by
  set a := e * y' * e⁻¹ * y'⁻¹ with ha
  have hayt : e * y' * e⁻¹ = a * y' := by rw [ha]; group
  have hc : a * y⁻¹ = y⁻¹ * a := ((mem_centerOf.1 hy').2 y⁻¹ (L.inv_mem hy)).symm
  calc e * (y * y') * e⁻¹ * (y * y')⁻¹
      = (e * y * e⁻¹) * (e * y' * e⁻¹) * y'⁻¹ * y⁻¹ := by group
    _ = (e * y * e⁻¹) * (a * y') * y'⁻¹ * y⁻¹ := by rw [hayt]
    _ = (e * y * e⁻¹) * (a * y⁻¹) := by group
    _ = (e * y * e⁻¹) * (y⁻¹ * a) := by rw [hc]
    _ = (e * y * e⁻¹ * y⁻¹) * a := by group

theorem comm_inv {e y : G} (hy : y ∈ L) (hy' : e * y * e⁻¹ * y⁻¹ ∈ centerOf L) :
    e * y⁻¹ * e⁻¹ * (y⁻¹)⁻¹ = (e * y * e⁻¹ * y⁻¹)⁻¹ := by
  set a := e * y * e⁻¹ * y⁻¹ with ha
  have hayt : e * y * e⁻¹ = a * y := by rw [ha]; group
  have hc : a⁻¹ * y = y * a⁻¹ := ((mem_centerOf.1 ((centerOf L).inv_mem hy')).2 y hy).symm
  calc e * y⁻¹ * e⁻¹ * (y⁻¹)⁻¹ = (e * y * e⁻¹)⁻¹ * y := by group
    _ = (a * y)⁻¹ * y := by rw [hayt]
    _ = y⁻¹ * (a⁻¹ * y) := by group
    _ = y⁻¹ * (y * a⁻¹) := by rw [hc]
    _ = a⁻¹ := by group

def Kp (p : ℕ) (e : G) : Subgroup G where
  carrier := {y | y ∈ L ∧ e * y * e⁻¹ * y⁻¹ ∈ centerOf L ∧
    ∃ n : ℕ, (e * y * e⁻¹ * y⁻¹) ^ (p ^ n) = 1}
  mul_mem' := by
    rintro y y' ⟨hyL, hyZ, n, hn⟩ ⟨hy'L, hy'Z, n', hn'⟩
    refine ⟨L.mul_mem hyL hy'L, ?_, n + n', ?_⟩
    · rw [comm_mul L hyL hy'Z]
      exact (centerOf L).mul_mem hyZ hy'Z
    · rw [comm_mul L hyL hy'Z]
      have hcomm : Commute (e * y * e⁻¹ * y⁻¹) (e * y' * e⁻¹ * y'⁻¹) :=
        (mem_centerOf.1 hy'Z).2 _ (comm_mem L (e := e) hyL)
      rw [hcomm.mul_pow, pow_add, pow_mul, hn, one_pow, one_mul, mul_comm, pow_mul, hn', one_pow]
  one_mem' := ⟨L.one_mem, by simpa using (centerOf L).one_mem, 0, by simp⟩
  inv_mem' := by
    rintro y ⟨hyL, hyZ, n, hn⟩
    refine ⟨L.inv_mem hyL, ?_, n, ?_⟩
    · rw [comm_inv L hyL hyZ]
      exact (centerOf L).inv_mem hyZ
    · rw [comm_inv L hyL hyZ, inv_pow, hn, inv_one]

theorem conj_mem_Kp {p : ℕ} {e e' y : G} (hee' : e * e' = e' * e) (hy : y ∈ Kp L p e) :
    e' * y * e'⁻¹ ∈ Kp L p e := by
  obtain ⟨hyL, hyZ, n, hn⟩ := hy
  have hcomm : e * (e' * y * e'⁻¹) * e⁻¹ * (e' * y * e'⁻¹)⁻¹ =
      e' * (e * y * e⁻¹ * y⁻¹) * e'⁻¹ := by
    have h1 : e⁻¹ * e' = e' * e⁻¹ := by
      calc e⁻¹ * e' = e⁻¹ * e' * e * e⁻¹ := by group
        _ = e⁻¹ * (e' * e) * e⁻¹ := by group
        _ = e⁻¹ * (e * e') * e⁻¹ := by rw [hee']
        _ = e' * e⁻¹ := by group
    calc e * (e' * y * e'⁻¹) * e⁻¹ * (e' * y * e'⁻¹)⁻¹
        = (e * e') * y * (e'⁻¹ * e⁻¹) * e' * y⁻¹ * e'⁻¹ := by group
      _ = (e' * e) * y * (e'⁻¹ * e⁻¹) * e' * y⁻¹ * e'⁻¹ := by rw [hee']
      _ = e' * (e * y * (e'⁻¹ * e⁻¹ * e') * y⁻¹) * e'⁻¹ := by group
      _ = e' * (e * y * e⁻¹ * y⁻¹) * e'⁻¹ := by
          have h2 : e'⁻¹ * e⁻¹ * e' = e⁻¹ := by
            calc e'⁻¹ * e⁻¹ * e' = e'⁻¹ * (e⁻¹ * e') := by group
              _ = e'⁻¹ * (e' * e⁻¹) := by rw [h1]
              _ = e⁻¹ := by group
          rw [h2]
  refine ⟨Subgroup.Normal.conj_mem inferInstance y hyL e', ?_, n, ?_⟩
  · rw [hcomm]
    exact conj_mem_centerOf L hyZ e'
  · rw [hcomm, conj_pow, hn]
    simp

def psiHom (p : ℕ) (e : G) : ↥(Kp L p e) →* G where
  toFun y := e * (y : G) * e⁻¹ * (y : G)⁻¹
  map_one' := by simp
  map_mul' y y' := by
    have := comm_mul L (e := e) y.2.1 y'.2.2.1
    simpa only [Subgroup.coe_mul] using this

theorem psiHom_ker (p : ℕ) (e : G) :
    (psiHom L p e).ker = ((Subgroup.centralizer ({e} : Set G)) ⊓ L).subgroupOf (Kp L p e) := by
  ext y
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
    Subgroup.mem_centralizer_singleton_iff]
  change e * (y : G) * e⁻¹ * (y : G)⁻¹ = 1 ↔ _
  constructor
  · intro h1
    refine ⟨?_, y.2.1⟩
    have h2 : e * (y : G) = (y : G) * e := by
      calc e * (y : G) = (e * (y : G) * e⁻¹ * (y : G)⁻¹) * (y : G) * e := by group
        _ = (y : G) * e := by rw [h1, one_mul]
    exact h2.symm
  · rintro ⟨h1, -⟩
    have h2 : e * (y : G) = (y : G) * e := h1.symm
    calc e * (y : G) * e⁻¹ * (y : G)⁻¹ = (y : G) * e * e⁻¹ * (y : G)⁻¹ := by rw [h2]
      _ = 1 := by group

theorem relIndex_Kp (p : ℕ) [Fact p.Prime] (e : G) :
    ∃ k : ℕ, ((Subgroup.centralizer ({e} : Set G)) ⊓ L).relIndex (Kp L p e) = p ^ k := by
  have hp : IsPGroup p ↥(psiHom L p e).range := by
    intro g
    obtain ⟨y, hy⟩ := g.2
    obtain ⟨n, hn⟩ := y.2.2.2
    refine ⟨n, Subtype.ext ?_⟩
    have : (g : G) = e * (y : G) * e⁻¹ * (y : G)⁻¹ := hy.symm
    rw [Subgroup.coe_pow, this, hn]
    rfl
  obtain ⟨k, hk⟩ := hp.exists_card_eq
  refine ⟨k, ?_⟩
  rw [Subgroup.relIndex, ← psiHom_ker, Subgroup.index_ker, hk]

open scoped IsMulCommutative

instance : IsMulCommutative ↥(centerOf L) :=
  ⟨⟨fun a b => Subtype.ext ((mem_centerOf.1 b.2).2 a (centerOf_le L a.2))⟩⟩

def conjHom (e : G) : ↥(centerOf L) →* ↥(centerOf L) where
  toFun z := ⟨e * z * e⁻¹, conj_mem_centerOf L z.2 e⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp [mul_assoc])

theorem conjHom_iterate (e : G) (n : ℕ) (a : ↥(centerOf L)) :
    (((⇑(conjHom L e))^[n] a : ↥(centerOf L)) : G) = e ^ n * a * (e ^ n)⁻¹ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    change e * (((⇑(conjHom L e))^[n] a : ↥(centerOf L)) : G) * e⁻¹ = _
    rw [ih, pow_succ']
    group

theorem nrm_conjHom (e : G) {x : G} (hx : x ∈ L) (hz : e * x * e⁻¹ * x⁻¹ ∈ centerOf L) (n : ℕ) :
    ((nrm (conjHom L e) ⟨e * x * e⁻¹ * x⁻¹, hz⟩ n : ↥(centerOf L)) : G) =
      e ^ n * x * (e ^ n)⁻¹ * x⁻¹ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hN : e * (e ^ n * x * (e ^ n)⁻¹ * x⁻¹) * e⁻¹ ∈ L :=
      Subgroup.Normal.conj_mem inferInstance _ (comm_mem L (e := e ^ n) hx) e
    have hcN : (e * (e ^ n * x * (e ^ n)⁻¹ * x⁻¹) * e⁻¹) * (e * x * e⁻¹ * x⁻¹) =
        (e * x * e⁻¹ * x⁻¹) * (e * (e ^ n * x * (e ^ n)⁻¹ * x⁻¹) * e⁻¹) :=
      (mem_centerOf.1 hz).2 _ hN
    rw [nrm_succ]
    change (e * x * e⁻¹ * x⁻¹) *
        (e * ((nrm (conjHom L e) ⟨e * x * e⁻¹ * x⁻¹, hz⟩ n : ↥(centerOf L)) : G) * e⁻¹) = _
    rw [ih, ← hcN, pow_succ']
    group

end Odd

namespace Hyp36

open Odd
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {M E : Subgroup G} {p : ℕ}

theorem mem_mul_centerOf_of_fixed (h : Hyp36 G M p E) (L : Subgroup G) [L.Normal] {e : G} (he : e ∈ E)
    (he1 : e ≠ 1) {x : G} (hx : x ∈ L) (hz : e * x * e⁻¹ * x⁻¹ ∈ centerOf L) :
    ∃ m ∈ M ⊓ L, ∃ z ∈ centerOf L, x = m * z := by
  classical
  haveI : Fact p.Prime := ⟨h.prime⟩
  have hep : e ^ p = 1 := h.elem.2 e he
  have hcE : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := by
    haveI := h.elem.1
    intro a ha b hb
    exact congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : ↥E) ⟨b, hb⟩)
  let σ := conjHom L e
  have hσ : ∀ a, (⇑σ)^[p] a = a := fun a => Subtype.ext (by rw [conjHom_iterate, hep]; simp)
  let a : ↥(centerOf L) := ⟨e * x * e⁻¹ * x⁻¹, hz⟩
  have hN : nrm σ a p = 1 := Subtype.ext (by rw [nrm_conjHom L e hx hz, hep]; simp)
  obtain ⟨w, n, hw⟩ := exists_mul_pPower σ hσ hN
  have hwL : (w : G) ∈ L := centerOf_le L w.2
  have hψw : e * (w : G) * e⁻¹ * (w : G)⁻¹ ∈ centerOf L := (σ w * w⁻¹).2
  have hw' : (e * x * e⁻¹ * x⁻¹ * (e * (w : G) * e⁻¹ * (w : G)⁻¹)) ^ (p ^ n) = 1 :=
    congrArg Subtype.val hw
  have hxK : x * (w : G) ∈ Kp L p e := by
    refine ⟨L.mul_mem hx hwL, ?_, n, ?_⟩
    · rw [comm_mul L hx hψw]
      exact (centerOf L).mul_mem hz hψw
    · rw [comm_mul L hx hψw]
      exact hw'
  have hKM : Kp L p e ≤ M := by
    obtain ⟨k, hk⟩ := relIndex_Kp L p e
    refine h.le_of_relIndex_pow (C := Subgroup.centralizer ({e} : Set G) ⊓ L) ?_ ?_ hk
    · intro e' he'
      rw [Subgroup.mem_normalizer_iff]
      intro y
      constructor
      · exact fun hy => conj_mem_Kp L (hcE e he e' he') hy
      · intro hy
        have h1 := conj_mem_Kp L (hcE e he e'⁻¹ (E.inv_mem he')) hy
        have h2 : e'⁻¹ * (e' * y * e'⁻¹) * e'⁻¹⁻¹ = y := by group
        rwa [h2] at h1
    · exact inf_le_left.trans (h.centralizer_le_of_ne_one he he1)
  refine ⟨x * (w : G), ⟨hKM hxK, hxK.1⟩, (w : G)⁻¹, (centerOf L).inv_mem w.2, ?_⟩
  group

end Hyp36

end CFSG.LocalAnalysis.UniquenessCase.UCK
