module

public import CFSG.LocalAnalysis.UniquenessCase.UC6S29
public import CFSG.LocalAnalysis.UniquenessCase.UCKInputs2
public import CFSG.LocalAnalysis.UniquenessCase.UC6C623d

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6

open Subgroup CFSG.Open
open scoped Matrix

variable {G : Type*} [Group G]

structure IrrTriple (A W N Z P : Subgroup G) : Prop where
  elem : IsElemAbelian 3 A
  card_A : Nat.card A = 3 ^ 3
  inf_eq_bot : Z ⊓ P = ⊥
  Z_le : Z ≤ A
  P_le : P ≤ A
  card_Z : Nat.card Z = 3
  card_P : Nat.card P = 3 ^ 2
  W_le : W ≤ normalizer (A : Set G)
  N_le : N ≤ W
  N_P : N ≤ normalizer (P : Set G)
  N_Z : ∀ n ∈ N, ∀ z ∈ Z, n * z = z * n
  irr : ∀ B : Subgroup G, B ≤ P → N ≤ normalizer (B : Set G) → B = ⊥ ∨ B = P

section Rep3

variable {A : Subgroup G}

private instance instCommGroupA3 [hA : Fact (IsElemAbelian 3 A)] : CommGroup A :=
  @IsMulCommutative.instCommGroup _ _ hA.out.1

private theorem cube_eq_one3 [hA : Fact (IsElemAbelian 3 A)] (a : A) : a ^ 3 = 1 :=
  Subtype.ext (by simpa using hA.out.2 a a.2)

private instance instModuleA3 [Fact (IsElemAbelian 3 A)] : Module (ZMod 3) (Additive A) :=
  AddCommGroup.zmodModule fun x => by
    have := cube_eq_one3 (Additive.toMul x)
    apply Additive.toMul.injective
    simpa [toMul_nsmul] using this

private def conjAut3 {X : Subgroup G} (hX : X ≤ normalizer (A : Set G)) (x : X) : A ≃* A where
  toFun a := ⟨(x : G) * a * (x : G)⁻¹, (mem_normalizer_iff.mp (hX x.2) a).mp a.2⟩
  invFun a := ⟨(x : G)⁻¹ * a * (x : G), by
    simpa using (mem_normalizer_iff.mp (hX (X.inv_mem x.2)) a).mp a.2⟩
  left_inv a := Subtype.ext (by simp [mul_assoc])
  right_inv a := Subtype.ext (by simp [mul_assoc])
  map_mul' a b := Subtype.ext (by simp [mul_assoc])

private def conjRep3 [Fact (IsElemAbelian 3 A)] {X : Subgroup G} (hX : X ≤ normalizer (A : Set G)) :
    X →* (Additive A ≃ₗ[ZMod 3] Additive A) where
  toFun x := AddEquiv.toLinearEquiv (MulEquiv.toAdditive (conjAut3 hX x))
    (fun c v => ZMod.map_smul (MulEquiv.toAdditive (conjAut3 hX x)) c v)
  map_one' := LinearEquiv.ext fun v => by
    apply Additive.toMul.injective
    apply Subtype.ext
    simp [conjAut3]
  map_mul' a b := LinearEquiv.ext fun v => by
    apply Additive.toMul.injective
    apply Subtype.ext
    simp [conjAut3, mul_assoc]

section
variable [Fact (IsElemAbelian 3 A)] {X : Subgroup G} (hX : X ≤ normalizer (A : Set G))

private theorem conjRep3_apply (x : X) (v : Additive A) :
    ((Additive.toMul (conjRep3 hX x v) : A) : G) = (x : G) * (Additive.toMul v : A) * (x : G)⁻¹ :=
  rfl

private theorem ker_conjRep3 :
    (conjRep3 hX).ker = (X ⊓ centralizer (A : Set G)).subgroupOf X := by
  ext x
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  simp only [x.2, true_and]
  constructor
  · intro h1
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    have := congrArg (fun f : Additive A ≃ₗ[ZMod 3] Additive A =>
      ((Additive.toMul (f (Additive.ofMul ⟨a, ha⟩)) : A) : G)) h1
    simp only [conjRep3_apply, LinearEquiv.coe_one, id, toMul_ofMul] at this
    calc a * (x : G) = (x : G) * a * (x : G)⁻¹ * x := by rw [this]
      _ = x * a := by group
  · intro h1
    apply LinearEquiv.ext
    intro v
    apply Additive.toMul.injective
    apply Subtype.ext
    rw [conjRep3_apply, LinearEquiv.coe_one, id]
    have := Subgroup.mem_centralizer_iff.mp h1 _ (Additive.toMul v : A).2
    rw [← this]
    group

private theorem conjRep3_eq_one_iff (x : X) :
    conjRep3 hX x = 1 ↔ (x : G) ∈ centralizer (A : Set G) := by
  rw [← MonoidHom.mem_ker, ker_conjRep3, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  simp [x.2]

end

end Rep3

section Coord3

private def conjLin3 {V : Type*} [AddCommGroup V] [Module (ZMod 3) V] (e : V ≃ₗ[ZMod 3] (Fin 3 → ZMod 3)) :
    (V ≃ₗ[ZMod 3] V) ≃* ((Fin 3 → ZMod 3) ≃ₗ[ZMod 3] (Fin 3 → ZMod 3)) where
  toFun f := e.symm.trans (f.trans e)
  invFun f := e.trans (f.trans e.symm)
  left_inv f := LinearEquiv.ext fun v => by simp
  right_inv f := LinearEquiv.ext fun v => by simp
  map_mul' f g := LinearEquiv.ext fun v => by simp [LinearEquiv.mul_apply]

private noncomputable def toGL3 {V : Type*} [AddCommGroup V] [Module (ZMod 3) V]
    (e : V ≃ₗ[ZMod 3] (Fin 3 → ZMod 3)) : (V ≃ₗ[ZMod 3] V) ≃* GL (Fin 3) (ZMod 3) :=
  (conjLin3 e).trans ((LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 3)
    (Fin 3 → ZMod 3)).symm.trans Matrix.GeneralLinearGroup.toLin.symm)

private theorem toGL3_mulVec {V : Type*} [AddCommGroup V] [Module (ZMod 3) V]
    (e : V ≃ₗ[ZMod 3] (Fin 3 → ZMod 3)) (f : V ≃ₗ[ZMod 3] V) (x : Fin 3 → ZMod 3) :
    ((toGL3 e f : GL (Fin 3) (ZMod 3)) : Matrix (Fin 3) (Fin 3) (ZMod 3)) *ᵥ x =
      e (f (e.symm x)) := by
  rw [← Matrix.mulVecLin_apply, ← Matrix.GeneralLinearGroup.coe_toLin, toGL3, MulEquiv.trans_apply,
    MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
  rfl

end Coord3

section Rep3b

variable {A : Subgroup G} [Fact (IsElemAbelian 3 A)]

private def subOf3 (S : Submodule (ZMod 3) (Additive A)) : Subgroup G where
  carrier := {g | ∃ hg : g ∈ A, Additive.ofMul (⟨g, hg⟩ : A) ∈ S}
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    exact ⟨A.mul_mem ha hb, S.add_mem ha' hb'⟩
  one_mem' := ⟨A.one_mem, S.zero_mem⟩
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    exact ⟨A.inv_mem ha, S.neg_mem ha'⟩

private theorem subOf3_le (S : Submodule (ZMod 3) (Additive A)) : subOf3 S ≤ A := fun _ ⟨hg, _⟩ => hg

private theorem mem_iff_mem_subOf3 {S : Submodule (ZMod 3) (Additive A)} (v : Additive A) :
    v ∈ S ↔ ((Additive.toMul v : A) : G) ∈ subOf3 S :=
  ⟨fun h => ⟨(Additive.toMul v : A).2, h⟩, fun ⟨_, h⟩ => h⟩

private def sub3 (H : Subgroup G) : Submodule (ZMod 3) (Additive A) :=
  AddSubgroup.toZModSubmodule 3
    { carrier := {v | ((Additive.toMul v : A) : G) ∈ H}
      add_mem' := fun {a b} ha hb => by simpa using H.mul_mem ha hb
      zero_mem' := by simp
      neg_mem' := fun {a} ha => by simpa using H.inv_mem ha }

private theorem mem_sub3 {H : Subgroup G} {v : Additive A} :
    v ∈ sub3 H ↔ ((Additive.toMul v : A) : G) ∈ H := Iff.rfl

private theorem card_sub3 (H : Subgroup G) : Nat.card (sub3 H : Submodule (ZMod 3) (Additive A)) =
    Nat.card (A ⊓ H : Subgroup G) :=
  Nat.card_congr
    { toFun := fun v => ⟨((Additive.toMul v.1 : A) : G), (Additive.toMul v.1 : A).2, v.2⟩
      invFun := fun x => ⟨Additive.ofMul ⟨x, x.2.1⟩, x.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

private theorem finrank_additive3 [Finite G] (hAcard : Nat.card A = 3 ^ 3) :
    Module.finrank (ZMod 3) (Additive A) = 3 := by
  haveI : Finite (Additive A) := inferInstanceAs (Finite A)
  haveI : Module.Finite (ZMod 3) (Additive A) := Module.Finite.of_finite
  have h := Module.natCard_eq_pow_finrank (K := ZMod 3) (V := Additive A)
  have h1 : Nat.card (Additive A) = Nat.card A := Nat.card_congr Additive.toMul
  rw [h1, hAcard, Nat.card_zmod] at h
  exact (Nat.pow_right_injective (by norm_num : 2 ≤ 3) h).symm

end Rep3b

namespace IrrTriple

variable {A W N Z P : Subgroup G} (h : IrrTriple A W N Z P)

include h

theorem comm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
  congrArg Subtype.val (h.elem.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)

theorem cube : ∀ a ∈ A, a ^ 3 = 1 := h.elem.2

theorem conj_mem {w : G} (hw : w ∈ W) {a : G} (ha : a ∈ A) : w * a * w⁻¹ ∈ A :=
  (mem_normalizer_iff.1 (h.W_le hw) a).1 ha

theorem exists_mul [Finite G] : ∀ a ∈ A, ∃ z ∈ Z, ∃ p ∈ P, a = z * p := by
  have hc : ∀ x ∈ Z, ∀ k ∈ P, x * k = k * x := fun x hx k hk => h.comm x (h.Z_le hx) k (h.P_le hk)
  have hsup : Z ⊔ P = A := by
    refine Subgroup.eq_of_le_of_card_ge (sup_le h.Z_le h.P_le) ?_
    rw [card_sup_of_commute_of_disjoint hc h.inf_eq_bot, h.card_Z, h.card_P, h.card_A]
    norm_num
  intro a ha
  rw [← hsup] at ha
  obtain ⟨z, hz, p, hp, e⟩ := exists_mul_of_mem_sup_of_commute hc ha
  exact ⟨z, hz, p, hp, e⟩

theorem eq_Z_of_le [Finite G] {B : Subgroup G} (hBZ : B ≤ Z) (hB : B ≠ ⊥) : B = Z := by
  have hdvd : Nat.card B ∣ Nat.card Z := Subgroup.card_dvd_of_le hBZ
  rw [h.card_Z] at hdvd
  have h1 : Nat.card B ≠ 1 := fun e => hB (Subgroup.eq_bot_of_card_eq B e)
  have h3 : Nat.card B = 3 := ((Nat.dvd_prime Nat.prime_three).1 hdvd).resolve_left h1
  exact Subgroup.eq_of_le_of_card_ge hBZ (by rw [h.card_Z, h3])

theorem le_Z_of_inf_eq_bot [Finite G] {B : Subgroup G} (hBA : B ≤ A)
    (hNB : N ≤ normalizer (B : Set G)) (hB : B ⊓ P = ⊥) : B ≤ Z := by
  intro b hb
  obtain ⟨z, hz, p, hp, rfl⟩ := h.exists_mul b (hBA hb)
  have hpA : p ∈ A := h.P_le hp
  have hzA : z ∈ A := h.Z_le hz
  have hcomm : ∀ n ∈ N, n * p * n⁻¹ = p := by
    intro n hn
    have h1 : n * (z * p) * n⁻¹ ∈ B := (mem_normalizer_iff.1 (hNB hn) (z * p)).1 hb
    have hnz : n * z * n⁻¹ = z := by rw [h.N_Z n hn z hz]; group
    have hnp : n * p * n⁻¹ ∈ P := (mem_normalizer_iff.1 (h.N_P hn) p).1 hp
    have hnpA : n * p * n⁻¹ ∈ A := h.P_le hnp
    have e1 : n * (z * p) * n⁻¹ = z * (n * p * n⁻¹) :=
      calc n * (z * p) * n⁻¹ = (n * z * n⁻¹) * (n * p * n⁻¹) := by group
        _ = z * (n * p * n⁻¹) := by rw [hnz]
    have hzqp : z * ((n * p * n⁻¹) * p⁻¹) = ((n * p * n⁻¹) * p⁻¹) * z :=
      h.comm z hzA _ (A.mul_mem hnpA (A.inv_mem hpA))
    have e2 : n * (z * p) * n⁻¹ * (z * p)⁻¹ = (n * p * n⁻¹) * p⁻¹ :=
      calc n * (z * p) * n⁻¹ * (z * p)⁻¹ = z * ((n * p * n⁻¹) * p⁻¹) * z⁻¹ := by rw [e1]; group
        _ = (((n * p * n⁻¹) * p⁻¹) * z) * z⁻¹ := by rw [hzqp]
        _ = (n * p * n⁻¹) * p⁻¹ := by group
    have h2 : (n * p * n⁻¹) * p⁻¹ ∈ B := by
      have := B.mul_mem h1 (B.inv_mem hb)
      rwa [e2] at this
    have h3 : (n * p * n⁻¹) * p⁻¹ ∈ B ⊓ P := ⟨h2, P.mul_mem hnp (P.inv_mem hp)⟩
    rw [hB, Subgroup.mem_bot] at h3
    exact mul_inv_eq_one.1 h3
  have hzp : Subgroup.zpowers p ≤ P := Subgroup.zpowers_le.2 hp
  have hN : N ≤ normalizer ((Subgroup.zpowers p : Subgroup G) : Set G) := by
    intro n hn
    refine Subgroup.centralizer_le_normalizer _ ?_
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
    have hpn : p * n = n * p := by
      have := hcomm n hn
      calc p * n = (n * p * n⁻¹) * n := by rw [this]
        _ = n * p := by group
    exact (Commute.zpow_left (show Commute p n from hpn) k).eq
  have hp1 : p = 1 := by
    rcases h.irr _ hzp hN with h0 | h0
    · exact Subgroup.zpowers_eq_bot.1 h0
    · exfalso
      have h9 : Nat.card P ≤ 3 := by
        rw [← h0, Nat.card_zpowers]
        exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one (h.cube p hpA))
      rw [h.card_P] at h9
      norm_num at h9
  rw [hp1, mul_one]
  exact hz

theorem normalizes_Z_of_normalizes_P [Finite G] (hWP : W ≤ normalizer (P : Set G))
    (hcop : ∀ g ∈ W, g ^ 3 ∈ centralizer (A : Set G) → g ∈ centralizer (A : Set G))
    {x : G} (hxW : x ∈ W) (hx4 : x ^ 4 ∈ centralizer (A : Set G))
    (hxZ : ∀ a ∈ A, x ^ 2 * a * (x ^ 2)⁻¹ = a ↔ a ∈ Z) : W ≤ normalizer (Z : Set G) := by
  obtain ⟨y, hy⟩ : ∃ y : G, y = x ^ 2 := ⟨_, rfl⟩
  rw [← hy] at hxZ
  have hyW : y ∈ W := hy ▸ W.pow_mem hxW 2
  have hy2 : ∀ a ∈ A, y * (y * a * y⁻¹) * y⁻¹ = a := by
    intro a ha
    have hc := Subgroup.mem_centralizer_iff.1 hx4 a ha
    calc y * (y * a * y⁻¹) * y⁻¹ = x ^ 4 * a * (x ^ 4)⁻¹ := by rw [hy]; group
      _ = a := by rw [← hc]; group
  have hY1 : ∀ p ∈ P, y * p * y⁻¹ = p⁻¹ := by
    intro p hp
    obtain ⟨q, hq⟩ : ∃ q : G, q = y * p * y⁻¹ := ⟨_, rfl⟩
    have hqP : q ∈ P := hq ▸ (mem_normalizer_iff.1 (hWP hyW) p).1 hp
    have hpA : p ∈ A := h.P_le hp
    have hqA : q ∈ A := h.P_le hqP
    have hyq : y * q * y⁻¹ = p := by rw [hq]; exact hy2 p hpA
    have hfix : y * (p * q) * y⁻¹ = p * q :=
      calc y * (p * q) * y⁻¹ = (y * p * y⁻¹) * (y * q * y⁻¹) := by group
        _ = q * p := by rw [← hq, hyq]
        _ = p * q := h.comm q hqA p hpA
    have hZ : p * q ∈ Z := (hxZ (p * q) (A.mul_mem hpA hqA)).1 hfix
    have h1 : p * q ∈ Z ⊓ P := ⟨hZ, P.mul_mem hp hqP⟩
    rw [h.inf_eq_bot, Subgroup.mem_bot] at h1
    rw [← hq]
    exact eq_inv_of_mul_eq_one_right h1
  have hY3 : ∀ a ∈ A, y * a * y⁻¹ * a⁻¹ ∈ P := by
    intro a ha
    obtain ⟨z, hz, p, hp, rfl⟩ := h.exists_mul a ha
    have hzA : z ∈ A := h.Z_le hz
    have hpA : p ∈ A := h.P_le hp
    have hyz : y * z * y⁻¹ = z := (hxZ z hzA).2 hz
    have e1 : y * (z * p) * y⁻¹ = z * p⁻¹ :=
      calc y * (z * p) * y⁻¹ = (y * z * y⁻¹) * (y * p * y⁻¹) := by group
        _ = z * p⁻¹ := by rw [hyz, hY1 p hp]
    have e2 : y * (z * p) * y⁻¹ * (z * p)⁻¹ = p⁻¹ * p⁻¹ := by
      rw [e1]
      have hc := h.comm z hzA (p⁻¹ * p⁻¹) (A.mul_mem (A.inv_mem hpA) (A.inv_mem hpA))
      calc z * p⁻¹ * (z * p)⁻¹ = (z * (p⁻¹ * p⁻¹)) * z⁻¹ := by group
        _ = ((p⁻¹ * p⁻¹) * z) * z⁻¹ := by rw [hc]
        _ = p⁻¹ * p⁻¹ := by group
    rw [e2]
    exact P.mul_mem (P.inv_mem hp) (P.inv_mem hp)
  intro w hw
  have hw' : w⁻¹ ∈ W := W.inv_mem hw
  have hPw : ∀ p ∈ P, w * p * w⁻¹ ∈ P := fun p hp => (mem_normalizer_iff.1 (hWP hw) p).1 hp
  have hPw' : ∀ p ∈ P, w⁻¹ * p * w ∈ P := fun p hp => by
    have := (mem_normalizer_iff.1 (hWP hw') p).1 hp
    simpa using this
  obtain ⟨y', hy'⟩ : ∃ y' : G, y' = w * y * w⁻¹ := ⟨_, rfl⟩
  have hy'W : y' ∈ W := hy' ▸ W.mul_mem (W.mul_mem hw hyW) hw'
  have hY1' : ∀ p ∈ P, y' * p * y'⁻¹ = p⁻¹ := by
    intro p hp
    have h1 := hY1 _ (hPw' p hp)
    calc y' * p * y'⁻¹ = w * (y * (w⁻¹ * p * w) * y⁻¹) * w⁻¹ := by rw [hy']; group
      _ = w * (w⁻¹ * p * w)⁻¹ * w⁻¹ := by rw [h1]
      _ = p⁻¹ := by group
  have hY3' : ∀ a ∈ A, y' * a * y'⁻¹ * a⁻¹ ∈ P := by
    intro a ha
    have h1 := hY3 _ (h.conj_mem hw' ha)
    have e : y' * a * y'⁻¹ * a⁻¹ = w * (y * (w⁻¹ * a * w) * y⁻¹ * (w⁻¹ * a * w)⁻¹) * w⁻¹ := by
      rw [hy']; group
    rw [e]
    simpa using hPw _ h1
  obtain ⟨g, hg⟩ : ∃ g : G, g = y * y' := ⟨_, rfl⟩
  have hgW : g ∈ W := hg ▸ W.mul_mem hyW hy'W
  have hgP : ∀ p ∈ P, g * p * g⁻¹ = p := by
    intro p hp
    calc g * p * g⁻¹ = y * (y' * p * y'⁻¹) * y⁻¹ := by rw [hg]; group
      _ = y * p⁻¹ * y⁻¹ := by rw [hY1' p hp]
      _ = p := by rw [hY1 p⁻¹ (P.inv_mem hp)]; group
  have hg3 : g ^ 3 ∈ centralizer (A : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    obtain ⟨c, hc⟩ : ∃ c : G, c = y * a * y⁻¹ * a⁻¹ := ⟨_, rfl⟩
    obtain ⟨c', hc'⟩ : ∃ c' : G, c' = y' * a * y'⁻¹ * a⁻¹ := ⟨_, rfl⟩
    have hcP : c ∈ P := hc ▸ hY3 a ha
    have hc'P : c' ∈ P := hc' ▸ hY3' a ha
    obtain ⟨d, hd⟩ : ∃ d : G, d = c'⁻¹ * c := ⟨_, rfl⟩
    have hdP : d ∈ P := hd ▸ P.mul_mem (P.inv_mem hc'P) hcP
    have hga : g * a * g⁻¹ = d * a := by
      have e1 : y' * a * y'⁻¹ = c' * a := by rw [hc']; group
      have e2 : y * a * y⁻¹ = c * a := by rw [hc]; group
      calc g * a * g⁻¹ = y * (y' * a * y'⁻¹) * y⁻¹ := by rw [hg]; group
        _ = y * (c' * a) * y⁻¹ := by rw [e1]
        _ = (y * c' * y⁻¹) * (y * a * y⁻¹) := by group
        _ = c'⁻¹ * (c * a) := by rw [hY1 c' hc'P, e2]
        _ = d * a := by rw [hd]; group
    have hd3 : d ^ 3 = 1 := h.cube d (h.P_le hdP)
    have e3 : g ^ 3 * a * (g ^ 3)⁻¹ = a :=
      calc g ^ 3 * a * (g ^ 3)⁻¹ = g * (g * (g * a * g⁻¹) * g⁻¹) * g⁻¹ := by rw [pow_three]; group
        _ = g * (g * (d * a) * g⁻¹) * g⁻¹ := by rw [hga]
        _ = g * ((g * d * g⁻¹) * (g * a * g⁻¹)) * g⁻¹ := by group
        _ = g * (d * (d * a)) * g⁻¹ := by rw [hgP d hdP, hga]
        _ = (g * d * g⁻¹) * ((g * d * g⁻¹) * (g * a * g⁻¹)) := by group
        _ = d * (d * (d * a)) := by rw [hgP d hdP, hga]
        _ = d ^ 3 * a := by rw [pow_three]; group
        _ = a := by rw [hd3, one_mul]
    calc a * g ^ 3 = (g ^ 3 * a * (g ^ 3)⁻¹) * g ^ 3 := by rw [e3]
      _ = g ^ 3 * a := by group
  have hgC : g ∈ centralizer (A : Set G) := hcop g hgW hg3
  refine mem_normalizer_of_forward_uc6 fun z hz => ?_
  have haA : w * z * w⁻¹ ∈ A := h.conj_mem hw (h.Z_le hz)
  have hfix' : y' * (w * z * w⁻¹) * y'⁻¹ = w * z * w⁻¹ := by
    have hyz : y * z * y⁻¹ = z := (hxZ z (h.Z_le hz)).2 hz
    calc y' * (w * z * w⁻¹) * y'⁻¹ = w * (y * z * y⁻¹) * w⁻¹ := by rw [hy']; group
      _ = w * z * w⁻¹ := by rw [hyz]
  have hcg := Subgroup.mem_centralizer_iff.1 hgC _ haA
  have hfix : y * (w * z * w⁻¹) * y⁻¹ = w * z * w⁻¹ := by
    have e : y * (y' * (w * z * w⁻¹) * y'⁻¹) * y⁻¹ = g * (w * z * w⁻¹) * g⁻¹ := by rw [hg]; group
    rw [hfix'] at e
    rw [e, ← hcg]
    group
  exact (hxZ _ haA).1 hfix

theorem irreducible [Finite G] (hmove : ¬ W ≤ normalizer (Z : Set G))
    (hcop : ∀ g ∈ W, g ^ 3 ∈ centralizer (A : Set G) → g ∈ centralizer (A : Set G))
    {x : G} (hxW : x ∈ W) (hx4 : x ^ 4 ∈ centralizer (A : Set G))
    (hxZ : ∀ a ∈ A, x ^ 2 * a * (x ^ 2)⁻¹ = a ↔ a ∈ Z) {B : Subgroup G} (hBA : B ≤ A)
    (hWB : W ≤ normalizer (B : Set G)) : B = ⊥ ∨ B = A := by
  have hNB : N ≤ normalizer (B : Set G) := fun n hn => hWB (h.N_le hn)
  have hBP : N ≤ normalizer ((B ⊓ P : Subgroup G) : Set G) := by
    intro n hn
    refine mem_normalizer_of_forward_uc6 fun b hb => ?_
    exact ⟨(mem_normalizer_iff.1 (hNB hn) b).1 hb.1, (mem_normalizer_iff.1 (h.N_P hn) b).1 hb.2⟩
  rcases h.irr (B ⊓ P) inf_le_right hBP with h0 | h0
  ·
    left
    by_contra hB0
    have hBZ : B ≤ Z := h.le_Z_of_inf_eq_bot hBA hNB h0
    have hBeq : B = Z := h.eq_Z_of_le hBZ hB0
    exact hmove (hBeq ▸ hWB)
  ·
    have hPB : P ≤ B := h0 ▸ inf_le_left
    by_cases hBA' : B = A
    · exact Or.inr hBA'
    · exfalso
      have hBP' : B ≤ P := by
        intro b hb
        obtain ⟨z, hz, p, hp, rfl⟩ := h.exists_mul b (hBA hb)
        have hzB : z ∈ B := by
          have := B.mul_mem hb (B.inv_mem (hPB hp))
          simpa using this
        by_cases hz1 : z = 1
        · rw [hz1, one_mul]
          exact hp
        · exfalso
          have hzp : Subgroup.zpowers z ≤ Z := Subgroup.zpowers_le.2 hz
          have hne : Subgroup.zpowers z ≠ ⊥ := fun e => hz1 (Subgroup.zpowers_eq_bot.1 e)
          have hZeq : Subgroup.zpowers z = Z := h.eq_Z_of_le hzp hne
          have hZB : Z ≤ B := hZeq ▸ Subgroup.zpowers_le.2 hzB
          apply hBA'
          refine le_antisymm hBA fun a ha => ?_
          obtain ⟨z', hz', p', hp', rfl⟩ := h.exists_mul a ha
          exact B.mul_mem (hZB hz') (hPB hp')
      have hBeq : B = P := le_antisymm hBP' hPB
      exact hmove (h.normalizes_Z_of_normalizes_P (hBeq ▸ hWB) hcop hxW hx4 hxZ)

end IrrTriple

theorem false_of_irreducible_triple {G : Type*} [Group G] [Finite G]
    {A W N Z P : Subgroup G}
    (hA : IsElemAbelian 3 A) (hAcard : Nat.card A = 3 ^ 3)
    (hZP : Z ⊓ P = ⊥) (hZA : Z ≤ A) (hPA : P ≤ A) (hZcard : Nat.card Z = 3)
    (hPcard : Nat.card P = 3 ^ 2)
    (hWA : W ≤ normalizer (A : Set G)) (hNW : N ≤ W) (hNP : N ≤ normalizer (P : Set G))
    (hNZ : ∀ n ∈ N, ∀ z ∈ Z, n * z = z * n)
    (hNirr : ∀ B : Subgroup G, B ≤ P → N ≤ normalizer (B : Set G) → B = ⊥ ∨ B = P)
    (hcop : ¬ 3 ∣ (centralizer (A : Set G) ⊓ W).relIndex W)
    (hmove : ¬ W ≤ normalizer (Z : Set G))
    (x : G) (hxW : x ∈ W) (hx4 : x ^ 4 ∈ centralizer (A : Set G))
    (hxZ : ∀ a ∈ A, x ^ 2 * a * (x ^ 2)⁻¹ = a ↔ a ∈ Z) : False := by
  classical
  haveI hAF : Fact (IsElemAbelian 3 A) := ⟨hA⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have htriple : IrrTriple A W N Z P :=
    ⟨hA, hAcard, hZP, hZA, hPA, hZcard, hPcard, hWA, hNW, hNP, hNZ, hNirr⟩
  haveI : Finite (Additive A) := inferInstanceAs (Finite A)
  haveI : Module.Finite (ZMod 3) (Additive A) := Module.Finite.of_finite
  let e : Additive A ≃ₗ[ZMod 3] (Fin 3 → ZMod 3) :=
    LinearEquiv.ofFinrankEq _ _ (by rw [finrank_additive3 hAcard, Module.finrank_fin_fun])
  let ρ0 : W →* (Additive A ≃ₗ[ZMod 3] Additive A) := conjRep3 hWA
  haveI : Finite ρ0.range := Finite.of_surjective ρ0.rangeRestrict ρ0.rangeRestrict_surjective
  have hcard : ¬ 3 ∣ Nat.card ρ0.range := by
    have h1 : Nat.card ρ0.range = ρ0.ker.index := (Subgroup.index_ker ρ0).symm
    rw [h1, ker_conjRep3 hWA, inf_comm]
    exact hcop
  have hcop' : ∀ g ∈ W, g ^ 3 ∈ centralizer (A : Set G) → g ∈ centralizer (A : Set G) := by
    intro g hg hg3
    have h1 : ρ0 ⟨g, hg⟩ ^ 3 = 1 := by
      rw [← map_pow]
      exact (conjRep3_eq_one_iff hWA _).2 (by simpa using hg3)
    have h2 : orderOf (ρ0 ⟨g, hg⟩) ∣ 3 := orderOf_dvd_of_pow_eq_one h1
    have h3 : orderOf (ρ0 ⟨g, hg⟩) ∣ Nat.card ρ0.range :=
      (dvd_of_eq (Subgroup.orderOf_coe (⟨ρ0 ⟨g, hg⟩, ⟨⟨g, hg⟩, rfl⟩⟩ : ρ0.range))).trans
        (orderOf_dvd_natCard _)
    have h4 : orderOf (ρ0 ⟨g, hg⟩) = 1 := by
      rcases (Nat.dvd_prime Nat.prime_three).1 h2 with h5 | h5
      · exact h5
      · exact absurd ((dvd_of_eq h5.symm).trans h3) hcard
    exact (conjRep3_eq_one_iff hWA ⟨g, hg⟩).1 (orderOf_eq_one_iff.1 h4)
  let Gs : Subgroup (GL (Fin 3) (ZMod 3)) := ρ0.range.map (toGL3 e).toMonoidHom
  have hGs : ∀ f ∈ ρ0.range, toGL3 e f ∈ Gs := fun f hf => ⟨f, hf, rfl⟩
  have hGscard : ¬ 3 ∣ Nat.card Gs := by
    have : Nat.card Gs = Nat.card ρ0.range := Subgroup.card_map_of_injective (toGL3 e).injective
    rw [this]
    exact hcard
  have hirr : UCK.IrredGL3 3 Gs := by
    intro S hS
    let S' : Submodule (ZMod 3) (Additive A) := S.comap (e : Additive A →ₗ[ZMod 3] (Fin 3 → ZMod 3))
    have hS' : ∀ f ∈ ρ0.range, ∀ v ∈ S', f v ∈ S' := by
      intro f hf v hv
      have := hS _ (hGs f hf) (e v) hv
      rw [toGL3_mulVec, LinearEquiv.symm_apply_apply] at this
      exact this
    have hWB : W ≤ normalizer ((subOf3 S' : Subgroup G) : Set G) := by
      intro w hw
      refine mem_normalizer_of_forward_uc6 fun b hb => ?_
      obtain ⟨hbA, hbS⟩ := hb
      have hwA : w * b * w⁻¹ ∈ A := htriple.conj_mem hw hbA
      exact ⟨hwA, hS' _ ⟨⟨w, hw⟩, rfl⟩ _ hbS⟩
    rcases htriple.irreducible hmove hcop' hxW hx4 hxZ (subOf3_le S') hWB with h0 | h0
    · left
      rw [Submodule.eq_bot_iff]
      intro v hv
      have hu : e.symm v ∈ S' := by
        show e (e.symm v) ∈ S
        rwa [LinearEquiv.apply_symm_apply]
      have := (mem_iff_mem_subOf3 (e.symm v)).1 hu
      rw [h0, Subgroup.mem_bot] at this
      have h1 : e.symm v = 0 := by
        apply Additive.toMul.injective
        exact Subtype.ext this
      simpa using congrArg e h1
    · right
      rw [Submodule.eq_top_iff']
      intro v
      have : ((Additive.toMul (e.symm v) : A) : G) ∈ subOf3 S' := by
        rw [h0]
        exact (Additive.toMul (e.symm v) : A).2
      have hu := (mem_iff_mem_subOf3 (e.symm v)).2 this
      have hu' : e (e.symm v) ∈ S := hu
      rwa [LinearEquiv.apply_symm_apply] at hu'
  obtain ⟨x0, hx0⟩ : ∃ x0 : GL (Fin 3) (ZMod 3), x0 = toGL3 e (ρ0 ⟨x, hxW⟩) := ⟨_, rfl⟩
  have hx0G : x0 ∈ Gs := hx0 ▸ hGs _ ⟨⟨x, hxW⟩, rfl⟩
  have hpow : ∀ k : ℕ, x0 ^ k = toGL3 e (ρ0 (⟨x, hxW⟩ ^ k)) := fun k => by
    rw [hx0, ← map_pow, ← map_pow]
  have hx4' : x0 ^ 2 ^ (1 + 1) = 1 := by
    rw [hpow, (conjRep3_eq_one_iff hWA _).2 (by simpa using hx4), map_one]
  have hx2' : ¬ x0 ^ 2 ^ 1 = 1 := by
    intro h1
    rw [hpow] at h1
    have h2 : ρ0 (⟨x, hxW⟩ ^ 2 ^ 1) = 1 := (toGL3 e).injective (h1.trans (map_one _).symm)
    have h3 := (conjRep3_eq_one_iff hWA _).1 h2
    obtain ⟨a, haA, haZ⟩ : ∃ a ∈ A, a ∉ Z := by
      by_contra hcon
      have hAZ : A ≤ Z := fun a ha => by
        by_contra haZ
        exact hcon ⟨a, ha, haZ⟩
      have := Subgroup.card_le_of_le hAZ
      rw [hAcard, hZcard] at this
      omega
    have h4 := Subgroup.mem_centralizer_iff.1 h3 a haA
    apply haZ
    refine (hxZ a haA).1 ?_
    have h5 : x ^ 2 * a * (x ^ 2)⁻¹ = a * x ^ 2 * (x ^ 2)⁻¹ := by
      have := h4
      simp only [pow_one, Subgroup.coe_pow] at this
      rw [this]
    rw [h5]
    group
  have hord : orderOf x0 = 4 := by
    have := orderOf_eq_prime_pow hx2' hx4'
    simpa using this
  let Z0 : Submodule (ZMod 3) (Fin 3 → ZMod 3) :=
    (sub3 Z : Submodule (ZMod 3) (Additive A)).map (e : Additive A →ₗ[ZMod 3] (Fin 3 → ZMod 3))
  have hZ0 : Module.finrank (ZMod 3) Z0 = 1 := by
    have h1 : Module.finrank (ZMod 3) Z0 = Module.finrank (ZMod 3) (sub3 Z : Submodule (ZMod 3) (Additive A)) :=
      LinearEquiv.finrank_map_eq e _
    rw [h1]
    haveI : Finite (sub3 Z : Submodule (ZMod 3) (Additive A)) := inferInstance
    haveI : Module.Finite (ZMod 3) (sub3 Z : Submodule (ZMod 3) (Additive A)) := Module.Finite.of_finite
    have h2 := Module.natCard_eq_pow_finrank (K := ZMod 3) (V := (sub3 Z : Submodule (ZMod 3) (Additive A)))
    rw [card_sub3, inf_eq_right.2 hZA, hZcard, Nat.card_zmod] at h2
    exact Nat.pow_right_injective (by norm_num : 2 ≤ 3) (h2.symm.trans (pow_one 3).symm)
  have hfix : {v : Fin 3 → ZMod 3 | (((x0 ^ 2 : GL (Fin 3) (ZMod 3)) :
      Matrix (Fin 3) (Fin 3) (ZMod 3)) *ᵥ v = v)} = (Z0 : Set (Fin 3 → ZMod 3)) := by
    ext v
    simp only [Set.mem_setOf_eq, SetLike.mem_coe]
    have hmv : ((x0 ^ 2 : GL (Fin 3) (ZMod 3)) : Matrix (Fin 3) (Fin 3) (ZMod 3)) *ᵥ v =
        e (ρ0 (⟨x, hxW⟩ ^ 2) (e.symm v)) := by
      rw [hpow]
      exact toGL3_mulVec e _ v
    rw [hmv]
    show _ ↔ v ∈ (sub3 Z : Submodule (ZMod 3) (Additive A)).map (e : Additive A →ₗ[ZMod 3] (Fin 3 → ZMod 3))
    rw [Submodule.mem_map_equiv, mem_sub3]
    obtain ⟨u, hu⟩ : ∃ u : Additive A, u = e.symm v := ⟨_, rfl⟩
    have hv : v = e u := by rw [hu]; simp
    rw [← hu, hv]
    have hconj : ((Additive.toMul (ρ0 (⟨x, hxW⟩ ^ 2) u) : A) : G) =
        x ^ 2 * (Additive.toMul u : A) * (x ^ 2)⁻¹ := by
      have h := conjRep3_apply hWA (⟨x, hxW⟩ ^ 2) u
      have hc : (((⟨x, hxW⟩ : W) ^ 2 : W) : G) = x ^ 2 := by simp
      rw [hc] at h
      exact h
    have huA : ((Additive.toMul u : A) : G) ∈ A := (Additive.toMul u : A).2
    constructor
    · intro h1
      have h2 : ρ0 (⟨x, hxW⟩ ^ 2) u = u := e.injective h1
      refine (hxZ _ huA).1 ?_
      rw [← hconj, h2]
    · intro h1
      have h2 := (hxZ _ huA).2 h1
      have h3 : ρ0 (⟨x, hxW⟩ ^ 2) u = u := by
        apply Additive.toMul.injective
        apply Subtype.ext
        rw [hconj, h2]
      rw [h3]
  exact false_of_irreducible_threePrime hirr hGscard hx0G hord hZ0 hfix

end CFSG.LocalAnalysis.UniquenessCase.UC6
