module

public import CFSG.Open.StatedDefs
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.Coset.Card

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG.Open
open scoped commutatorElement Matrix

@[expose, reducible] def sec717CommGroup {X : Type} [Group X] (h : ∀ a b : X, a * b = b * a) :
    CommGroup X :=
  { (inferInstance : Group X) with mul_comm := h }

@[expose] def sec717ConjA {G : Type} [Group G] (A : Subgroup G) (h : G)
    (h1 : ∀ a ∈ A, h * a * h⁻¹ ∈ A) (h2 : ∀ a ∈ A, h⁻¹ * a * h ∈ A) : A ≃* A where
  toFun a := ⟨h * a * h⁻¹, h1 a a.2⟩
  invFun a := ⟨h⁻¹ * a * h, h2 a a.2⟩
  left_inv a := Subtype.ext (by simp [mul_assoc])
  right_inv a := Subtype.ext (by simp [mul_assoc])
  map_mul' a b := Subtype.ext (by simp [mul_assoc])


@[expose] def IrrQ4NoPairingStatement : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (H : Type) [Group H]
    (φ : H →* GL (Fin 3 ⊕ Fin 3) K) (X : Type) [CommGroup X] (ρ : H → MulAut X),
    φ.range = StatedOmega (StatedQuadPlus 3 K) → (∀ h k : H, ρ (h * k) = ρ h * ρ k) →
    (∀ h : H, φ h = 1 → ρ h = 1) → Nat.card X = Nat.card K ^ 4 →
    (∀ S : Subgroup X, (∀ h : H, ∀ x ∈ S, ρ h x ∈ S) → S = ⊥ ∨ S = ⊤) →
    ∀ (Y : Type) [CommGroup Y] (β : X → X → Y),
      (∀ x x' y : X, β (x * x') y = β x y * β x' y) →
      (∀ x y y' : X, β x (y * y') = β x y * β x y') →
      (∀ h : H, ∀ x y : X, β (ρ h x) (ρ h y) = β x y) → ∀ x y : X, β x y = 1

section Pairing

variable {G : Type} [Group G]

theorem sec717_mk_conj {R Z0 Q : Subgroup G} (hZR : ∀ z ∈ Z0, ∀ r ∈ R, ⁅z, r⁆ ∈ Q)
    (z : Z0) {r : G} (hr : r ∈ R) (hz' : r * z * r⁻¹ ∈ Z0) :
    (QuotientGroup.mk ⟨r * z * r⁻¹, hz'⟩ : Z0 ⧸ Q.subgroupOf Z0) = QuotientGroup.mk z := by
  rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
  have h := hZR ((z : G)⁻¹) (Z0.inv_mem z.2) r hr
  have h' : ⁅r, (z : G)⁻¹⁆ ∈ Q := by
    have := Q.inv_mem h
    rwa [commutatorElement_inv] at this
  have key : (r * z * r⁻¹)⁻¹ * (z : G) = ⁅r, (z : G)⁻¹⁆ := by
    rw [commutatorElement_def]
    group
  show (r * z * r⁻¹)⁻¹ * (z : G) ∈ Q
  rw [key]
  exact h'

@[expose] def sec717Zc {G : Type} [Group G] {A Z0 : Subgroup G}
    (hAcomm : ∀ a ∈ A, ∀ a' ∈ A, ⁅a, a'⁆ ∈ Z0) (x a : A) : Z0 :=
  ⟨⁅(x : G), (a : G)⁆, hAcomm x x.2 a a.2⟩

@[expose] def sec717Zconj {G : Type} [Group G] {R Z0 : Subgroup G}
    (hRZ : ∀ r ∈ R, ∀ z ∈ Z0, r * z * r⁻¹ ∈ Z0) (r : G) (hr : r ∈ R) (z : Z0) : Z0 :=
  ⟨r * z * r⁻¹, hRZ r hr z z.2⟩

theorem sec717_zc_mul {G : Type} [Group G] {R A Z0 : Subgroup G}
    (hAcomm : ∀ a ∈ A, ∀ a' ∈ A, ⁅a, a'⁆ ∈ Z0) (hRZ : ∀ r ∈ R, ∀ z ∈ Z0, r * z * r⁻¹ ∈ Z0)
    (x a b : A) (ha : (a : G) ∈ R) :
    sec717Zc hAcomm x (a * b) = sec717Zc hAcomm x a * sec717Zconj hRZ (a : G) ha (sec717Zc hAcomm x
        b) := by
  apply Subtype.ext
  simp only [sec717Zc, sec717Zconj, Subgroup.coe_mul, commutatorElement_def]
  group

theorem sec717_zc_mul_left {G : Type} [Group G] {R A Z0 : Subgroup G}
    (hAcomm : ∀ a ∈ A, ∀ a' ∈ A, ⁅a, a'⁆ ∈ Z0) (hRZ : ∀ r ∈ R, ∀ z ∈ Z0, r * z * r⁻¹ ∈ Z0)
    (x x' a : A) (hx : (x : G) ∈ R) :
    sec717Zc hAcomm (x * x') a = sec717Zconj hRZ (x : G) hx (sec717Zc hAcomm x' a) * sec717Zc
        hAcomm x a := by
  apply Subtype.ext
  simp only [sec717Zc, sec717Zconj, Subgroup.coe_mul, commutatorElement_def]
  group

theorem sec717_zc_conj {G : Type} [Group G] {R A Z0 : Subgroup G}
    (hAcomm : ∀ a ∈ A, ∀ a' ∈ A, ⁅a, a'⁆ ∈ Z0) (hRZ : ∀ r ∈ R, ∀ z ∈ Z0, r * z * r⁻¹ ∈ Z0)
    (h : G) (hh : h ∈ R) (a a' : A) (ha : h * a * h⁻¹ ∈ A) (ha' : h * a' * h⁻¹ ∈ A) :
    sec717Zc hAcomm ⟨h * a * h⁻¹, ha⟩ ⟨h * a' * h⁻¹, ha'⟩ = sec717Zconj hRZ h hh (sec717Zc hAcomm a
        a') := by
  apply Subtype.ext
  simp only [sec717Zc, sec717Zconj, commutatorElement_def]
  group

theorem sec717_pairing_trivial {K : Type} [Field K] [Finite K] [CharP K 2] [Finite G]
    (cited : IrrQ4NoPairingStatement)
    {R A B Z0 Q : Subgroup G} (φ : ↥R →* GL (Fin 3 ⊕ Fin 3) K)
    (hφr : φ.range = StatedOmega (StatedQuadPlus 3 K))
    (hAR : A ≤ R) (hBA : B ≤ A) (hZB : Z0 ≤ B)
    (hRA : ∀ r ∈ R, ∀ a ∈ A, r * a * r⁻¹ ∈ A)
    (hRB : ∀ r ∈ R, ∀ b ∈ B, r * b * r⁻¹ ∈ B)
    (hRZ : ∀ r ∈ R, ∀ z ∈ Z0, r * z * r⁻¹ ∈ Z0)
    (hQR : ∀ r ∈ R, ∀ q ∈ Q, r * q * r⁻¹ ∈ Q)
    (hZR : ∀ z ∈ Z0, ∀ r ∈ R, ⁅z, r⁆ ∈ Q)
    (hAcomm : ∀ a ∈ A, ∀ a' ∈ A, ⁅a, a'⁆ ∈ Z0)
    (hBQ : ∀ b ∈ B, ∀ a ∈ A, ⁅b, a⁆ ∈ Q)
    (hφ : ∀ h : ↥R, φ h = 1 → ∀ a ∈ A, (h * a * h⁻¹)⁻¹ * a ∈ B)
    (hlat : ∀ C : Subgroup G, B ≤ C → C ≤ A →
      (∀ r ∈ R, ∀ c ∈ C, r * c * r⁻¹ ∈ C) → C = B ∨ C = A)
    (hcard : Nat.card A = Nat.card B * Nat.card K ^ 4) :
    ∀ a ∈ A, ∀ a' ∈ A, ⁅a, a'⁆ ∈ Q := by
  have hZ0R : ∀ z ∈ Z0, z ∈ R := fun z hz => hAR (hBA (hZB hz))
  have hRA' : ∀ r ∈ R, ∀ a ∈ A, r⁻¹ * a * r ∈ A := fun r hr a ha => by
    simpa using hRA r⁻¹ (R.inv_mem hr) a ha
  have hRB' : ∀ r ∈ R, ∀ b ∈ B, r⁻¹ * b * r ∈ B := fun r hr b hb => by
    simpa using hRB r⁻¹ (R.inv_mem hr) b hb
  haveI hBn : (B.subgroupOf A).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simpa using hRB (g : G) (hAR g.2) _ hn⟩
  haveI hQn : (Q.subgroupOf Z0).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simpa using hQR (g : G) (hZ0R (g : G) g.2) _ hn⟩
  have hXcomm : ∀ a b : A ⧸ B.subgroupOf A, a * b = b * a := by
    intro a b
    induction a using QuotientGroup.induction_on with
    | H a =>
    induction b using QuotientGroup.induction_on with
    | H b =>
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq,
      Subgroup.mem_subgroupOf]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    have key : ((a : G) * b)⁻¹ * ((b : G) * a) = ⁅(b : G)⁻¹, (a : G)⁻¹⁆ := by
      rw [commutatorElement_def]
      group
    rw [key]
    exact hZB (hAcomm _ (A.inv_mem b.2) _ (A.inv_mem a.2))
  letI : CommGroup (A ⧸ B.subgroupOf A) := sec717CommGroup hXcomm
  have hYcomm : ∀ y1 y2 : Z0 ⧸ Q.subgroupOf Z0, y1 * y2 = y2 * y1 := by
    intro y1 y2
    induction y1 using QuotientGroup.induction_on with
    | H z1 =>
    induction y2 using QuotientGroup.induction_on with
    | H z2 =>
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq,
      Subgroup.mem_subgroupOf]
    have h := hZR ((z2 : G)⁻¹) (Z0.inv_mem z2.2) ((z1 : G)⁻¹)
      (R.inv_mem (hZ0R z1 z1.2))
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    have key : ((z1 : G) * z2)⁻¹ * ((z2 : G) * z1) = ⁅(z2 : G)⁻¹, (z1 : G)⁻¹⁆ := by
      rw [commutatorElement_def]
      group
    rw [key]
    exact h
  letI : CommGroup (Z0 ⧸ Q.subgroupOf Z0) := sec717CommGroup hYcomm
  have hmkconj : ∀ (r : G) (hr : r ∈ R) (z : Z0),
      (QuotientGroup.mk (sec717Zconj hRZ r hr z) : Z0 ⧸ Q.subgroupOf Z0) =
        QuotientGroup.mk z := by
    intro r hr z
    exact sec717_mk_conj hZR z hr (hRZ r hr z z.2)
  have hcm_mul : ∀ x a b : A,
      (QuotientGroup.mk (sec717Zc hAcomm x (a * b)) : Z0 ⧸ Q.subgroupOf Z0) =
        QuotientGroup.mk (sec717Zc hAcomm x a) * QuotientGroup.mk (sec717Zc hAcomm x b) := by
    intro x a b
    rw [sec717_zc_mul hAcomm hRZ x a b (hAR a.2), QuotientGroup.mk_mul, hmkconj]
  let fx : A → (A →* (Z0 ⧸ Q.subgroupOf Z0)) := fun x =>
    MonoidHom.mk' (fun a => QuotientGroup.mk (sec717Zc hAcomm x a)) (fun a b => hcm_mul x a b)
  have hkill : ∀ x : A, ∀ n ∈ B.subgroupOf A, fx x n = 1 := by
    intro x n hn
    show (QuotientGroup.mk (sec717Zc hAcomm x n) : Z0 ⧸ Q.subgroupOf Z0) = 1
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    have h := hBQ (n : G) (Subgroup.mem_subgroupOf.mp hn) (x : G) x.2
    show ⁅(x : G), (n : G)⁆ ∈ Q
    rw [← commutatorElement_inv]
    exact Q.inv_mem h
  let βx : A → (A ⧸ B.subgroupOf A) →* (Z0 ⧸ Q.subgroupOf Z0) := fun x =>
    QuotientGroup.lift (B.subgroupOf A) (fx x) (fun n hn => MonoidHom.mem_ker.mpr (hkill x n hn))
  have hβx_mk : ∀ x a : A,
      βx x (QuotientGroup.mk a) = QuotientGroup.mk (sec717Zc hAcomm x a) := by
    intro x a
    rfl
  have hkill2 : ∀ n ∈ B.subgroupOf A, βx n = 1 := by
    intro n hn
    apply MonoidHom.ext
    intro q
    induction q using QuotientGroup.induction_on with
    | H a =>
    rw [hβx_mk, MonoidHom.one_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact hBQ (n : G) (Subgroup.mem_subgroupOf.mp hn) (a : G) a.2
  have hβmul : ∀ x x' : A, βx (x * x') = βx x * βx x' := by
    intro x x'
    apply MonoidHom.ext
    intro q
    induction q using QuotientGroup.induction_on with
    | H a =>
    rw [MonoidHom.mul_apply, hβx_mk, hβx_mk, hβx_mk,
      sec717_zc_mul_left hAcomm hRZ x x' a (hAR x.2), QuotientGroup.mk_mul, hmkconj, mul_comm]
  let F : A →* ((A ⧸ B.subgroupOf A) →* (Z0 ⧸ Q.subgroupOf Z0)) := MonoidHom.mk' βx hβmul
  let Bh : (A ⧸ B.subgroupOf A) →* ((A ⧸ B.subgroupOf A) →* (Z0 ⧸ Q.subgroupOf Z0)) :=
    QuotientGroup.lift (B.subgroupOf A) F
      (fun n hn => MonoidHom.mem_ker.mpr (hkill2 n hn))
  have hBh : ∀ x a : A,
      Bh (QuotientGroup.mk x) (QuotientGroup.mk a) =
        QuotientGroup.mk (sec717Zc hAcomm x a) := by
    intro x a
    rfl
  let conjA : ↥R → (A ≃* A) := fun h => sec717ConjA A (h : G) (hRA _ h.2) (hRA' _ h.2)
  have hmapB : ∀ h : ↥R, (B.subgroupOf A).map (conjA h : A →* A) = B.subgroupOf A := by
    intro h
    ext x
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [Subgroup.mem_subgroupOf] at hy ⊢
      exact hRB (h : G) h.2 _ hy
    · intro hx
      have hx' : (x : G) ∈ B := Subgroup.mem_subgroupOf.mp hx
      refine ⟨⟨(h : G)⁻¹ * x * h, hRA' _ h.2 x x.2⟩, ?_, ?_⟩
      · rw [Subgroup.mem_subgroupOf]
        exact hRB' _ h.2 _ hx'
      · apply Subtype.ext
        show (h : G) * ((h : G)⁻¹ * x * h) * (h : G)⁻¹ = x
        group
  let ρ : ↥R → MulAut (A ⧸ B.subgroupOf A) := fun h =>
    QuotientGroup.congr (B.subgroupOf A) (B.subgroupOf A) (conjA h) (hmapB h)
  have hρ_mk : ∀ (h : ↥R) (a : A),
      ρ h (QuotientGroup.mk a) = QuotientGroup.mk (conjA h a) := by
    intro h a
    rfl
  have hmul : ∀ h k : ↥R, ρ (h * k) = ρ h * ρ k := by
    intro h k
    apply MulEquiv.ext
    intro q
    induction q using QuotientGroup.induction_on with
    | H a =>
    rw [MulAut.mul_apply, hρ_mk, hρ_mk, hρ_mk]
    congr 1
    apply Subtype.ext
    show ((h * k : ↥R) : G) * a * ((h * k : ↥R) : G)⁻¹ = (h : G) * ((k : G) * a * (k : G)⁻¹) * (h :
        G)⁻¹
    rw [Subgroup.coe_mul]
    group
  have hker : ∀ h : ↥R, φ h = 1 → ρ h = 1 := by
    intro h hh
    apply MulEquiv.ext
    intro q
    induction q using QuotientGroup.induction_on with
    | H a =>
    rw [hρ_mk, MulAut.one_apply, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    show ((h : G) * a * (h : G)⁻¹)⁻¹ * a ∈ B
    exact hφ h hh a a.2
  have hirr : ∀ S : Subgroup (A ⧸ B.subgroupOf A), (∀ h : ↥R, ∀ x ∈ S, ρ h x ∈ S) →
      S = ⊥ ∨ S = ⊤ := by
    intro S hS
    let C : Subgroup G := (S.comap (QuotientGroup.mk' (B.subgroupOf A))).map A.subtype
    have hmemC : ∀ g : G, g ∈ C ↔ ∃ a : A,
        (QuotientGroup.mk a : A ⧸ B.subgroupOf A) ∈ S ∧ (a : G) = g := by
      intro g
      constructor
      · intro hg
        obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hg
        exact ⟨a, ha, rfl⟩
      · rintro ⟨a, ha, rfl⟩
        exact Subgroup.mem_map.mpr ⟨a, ha, rfl⟩
    have hBC : B ≤ C := by
      intro b hb
      refine (hmemC b).mpr ⟨⟨b, hBA hb⟩, ?_, rfl⟩
      have h1 : (QuotientGroup.mk (⟨b, hBA hb⟩ : A) : A ⧸ B.subgroupOf A) = 1 := by
        rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
        exact hb
      rw [h1]
      exact S.one_mem
    have hCA : C ≤ A := by
      intro g hg
      obtain ⟨a, -, rfl⟩ := (hmemC g).mp hg
      exact a.2
    have hCinv : ∀ r ∈ R, ∀ c ∈ C, r * c * r⁻¹ ∈ C := by
      intro r hr c hc
      obtain ⟨a, ha, rfl⟩ := (hmemC c).mp hc
      refine (hmemC _).mpr ⟨conjA ⟨r, hr⟩ a, ?_, rfl⟩
      have := hS ⟨r, hr⟩ _ ha
      rw [hρ_mk] at this
      exact this
    rcases hlat C hBC hCA hCinv with hCB | hCA'
    · left
      rw [Subgroup.eq_bot_iff_forall]
      intro s hs
      obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective s
      have haB : (a : G) ∈ B := by
        rw [← hCB]
        exact (hmemC (a : G)).mpr ⟨a, hs, rfl⟩
      exact (QuotientGroup.eq_one_iff a).mpr (Subgroup.mem_subgroupOf.mpr haB)
    · right
      rw [Subgroup.eq_top_iff']
      intro x
      obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
      have haC : (a : G) ∈ C := by
        rw [hCA']
        exact a.2
      obtain ⟨a', ha', he⟩ := (hmemC (a : G)).mp haC
      have hEq : a' = a := Subtype.ext he
      rw [hEq] at ha'
      exact ha'
  have hcardX : Nat.card (A ⧸ B.subgroupOf A) = Nat.card K ^ 4 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (B.subgroupOf A)
    have h2 : Nat.card (B.subgroupOf A) = Nat.card B :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBA).toEquiv
    rw [h2, hcard] at h1
    have hpos : 0 < Nat.card B := Nat.card_pos
    apply Nat.eq_of_mul_eq_mul_right hpos
    rw [← h1]
    ring
  have hInv : ∀ h : ↥R, ∀ x y : A ⧸ B.subgroupOf A, Bh (ρ h x) (ρ h y) = Bh x y := by
    intro h x y
    induction x using QuotientGroup.induction_on with
    | H a =>
    induction y using QuotientGroup.induction_on with
    | H a' =>
    rw [hρ_mk, hρ_mk, hBh, hBh]
    rw [show sec717Zc hAcomm (conjA h a) (conjA h a') =
        sec717Zconj hRZ (h : G) h.2 (sec717Zc hAcomm a a') from
      sec717_zc_conj hAcomm hRZ (h : G) h.2 a a' (hRA _ h.2 a a.2) (hRA _ h.2 a' a'.2)]
    exact hmkconj _ h.2 _
  have hfinal := cited K ↥R φ (A ⧸ B.subgroupOf A) ρ hφr hmul hker hcardX hirr
    (Z0 ⧸ Q.subgroupOf Z0) (fun x y => Bh x y)
    (fun x x' y => by rw [map_mul, MonoidHom.mul_apply])
    (fun x y y' => map_mul (Bh x) y y') hInv
  intro a ha a' ha'
  have h1 : Bh (QuotientGroup.mk ⟨a, ha⟩) (QuotientGroup.mk ⟨a', ha'⟩) = 1 :=
    hfinal _ _
  rw [hBh, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h1
  exact h1

end Pairing

end CFSG.RankThree.GF2n.Stroth80
