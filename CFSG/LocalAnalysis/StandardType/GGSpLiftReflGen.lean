module

public import CFSG.LocalAnalysis.StandardType.GGSpJoinPlaneTorusLift
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentySpModel
public import CFSG.LocalAnalysis.StandardType.GGSpNonsplitFrameTorus
public import CFSG.CGT.PushingUpLit.BHS6.FaithfulSL
public import CFSG.CGT.PushingUpLit.BHS.TwoSixteenSL
public import CFSG.Quasithin.Background.B15P4LayerDict
public import CFSG.Quasithin.Background.B1MoreElevenB
public import CFSG.Quasithin.Background.B1MoreNineG
public import CFSG.Quasithin.Background.D2Conj
public import CFSG.Quasithin.Background.D2Cyclic

public section

namespace CFSG.StandardType.SpJoinRefl

open CFSG.Open

section Pure

variable {G : Type} [Group G] [Finite G]

section Helpers

private lemma lrg_eq_one_of_mem_centralizer_of_center_eq_bot {X : Subgroup G}
    (hX : Subgroup.center X = ⊥) {z : G} (hzX : z ∈ X)
    (hzC : z ∈ Subgroup.centralizer (X : Set G)) : z = 1 := by
  have hz : (⟨z, hzX⟩ : X) ∈ Subgroup.center X := by
    rw [Subgroup.mem_center_iff]
    intro w
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp hzC (w : G) w.2
  have hz1 : (⟨z, hzX⟩ : X) ∈ (⊥ : Subgroup X) := by
    rw [← hX]
    exact hz
  simpa using Subgroup.mem_bot.mp hz1

private def lrg_prodHom (Bs X : Subgroup G) :
    ↥(Bs ⊓ X) × ↥(Bs ⊓ Subgroup.centralizer (X : Set G)) →* ↥Bs where
  toFun q := ⟨(q.1 : G) * (q.2 : G), Bs.mul_mem q.1.2.1 q.2.2.1⟩
  map_one' := Subtype.ext (by simp)
  map_mul' q r := by
    apply Subtype.ext
    simp only [Prod.fst_mul, Prod.snd_mul, Subgroup.coe_mul]
    have h : (r.1 : G) * (q.2 : G) = (q.2 : G) * (r.1 : G) :=
      Subgroup.mem_centralizer_iff.mp q.2.2.2 (r.1 : G) r.1.2.2
    calc ((q.1 : G) * (r.1 : G)) * ((q.2 : G) * (r.2 : G))
        = (q.1 : G) * ((r.1 : G) * (q.2 : G)) * (r.2 : G) := by group
      _ = (q.1 : G) * ((q.2 : G) * (r.1 : G)) * (r.2 : G) := by rw [h]
      _ = ((q.1 : G) * (q.2 : G)) * ((r.1 : G) * (r.2 : G)) := by group

private lemma lrg_prodHom_bijective {p : ℕ} {B Bs X : Subgroup G} (hBs : GGBstar p B Bs)
    (hZ : Subgroup.center X = ⊥) (hnorm : Bs ≤ Subgroup.normalizer (X : Set G))
    (hinner : ∀ b ∈ Bs, ∃ x ∈ X, ∀ y ∈ X, b * y * b⁻¹ = x * y * x⁻¹) :
    Function.Bijective (lrg_prodHom Bs X) := by
  refine ⟨?_, ?_⟩
  · rintro ⟨⟨x, hx⟩, ⟨c, hc⟩⟩ ⟨⟨x', hx'⟩, ⟨c', hc'⟩⟩ h
    have h' : x * c = x' * c' := congrArg Subtype.val h
    have hxX : x ∈ X := hx.2
    have hx'X : x' ∈ X := hx'.2
    have hcC : c ∈ Subgroup.centralizer (X : Set G) := hc.2
    have hc'C : c' ∈ Subgroup.centralizer (X : Set G) := hc'.2
    have hz_eq : x'⁻¹ * x = c' * c⁻¹ := by
      calc x'⁻¹ * x = x'⁻¹ * (x * c) * c⁻¹ := by group
        _ = x'⁻¹ * (x' * c') * c⁻¹ := by rw [h']
        _ = c' * c⁻¹ := by group
    have hzX : x'⁻¹ * x ∈ X := X.mul_mem (X.inv_mem hx'X) hxX
    have hzC : x'⁻¹ * x ∈ Subgroup.centralizer (X : Set G) := by
      rw [hz_eq]
      exact (Subgroup.centralizer (X : Set G)).mul_mem hc'C
        ((Subgroup.centralizer (X : Set G)).inv_mem hcC)
    have hz1 : x'⁻¹ * x = 1 := lrg_eq_one_of_mem_centralizer_of_center_eq_bot hZ hzX hzC
    have hxeq : x = x' := (inv_mul_eq_one.mp hz1).symm
    have hceq : c = c' := by
      apply mul_left_cancel (a := x)
      rw [← hxeq] at h'
      exact h'
    exact Prod.ext (Subtype.ext hxeq) (Subtype.ext hceq)
  · intro b
    obtain ⟨x, hx, c, hc, hbc⟩ := ggBstar_split_of_inner hBs hZ hnorm hinner b.1 b.2
    exact ⟨(⟨x, hx⟩, ⟨c, hc⟩), Subtype.ext hbc.symm⟩

private noncomputable def lrg_prodEquiv {p : ℕ} {B Bs X : Subgroup G} (hBs : GGBstar p B Bs)
    (hZ : Subgroup.center X = ⊥) (hnorm : Bs ≤ Subgroup.normalizer (X : Set G))
    (hinner : ∀ b ∈ Bs, ∃ x ∈ X, ∀ y ∈ X, b * y * b⁻¹ = x * y * x⁻¹) :
    ↥(Bs ⊓ X) × ↥(Bs ⊓ Subgroup.centralizer (X : Set G)) ≃* ↥Bs :=
  MulEquiv.ofBijective (lrg_prodHom Bs X) (lrg_prodHom_bijective hBs hZ hnorm hinner)

private noncomputable def lrg_subgroupOfEquiv (Bs X : Subgroup G) :
    ↥((Bs ⊓ X).subgroupOf X) ≃* ↥(Bs ⊓ X) where
  toFun x := ⟨((x : ↥X) : G), Subgroup.mem_subgroupOf.mp x.2⟩
  invFun x := ⟨⟨(x : G), x.2.2⟩, Subgroup.mem_subgroupOf.mpr x.2⟩
  left_inv x := Subtype.ext (Subtype.ext rfl)
  right_inv x := Subtype.ext rfl
  map_mul' x y := Subtype.ext rfl

private lemma lrg_card_subgroupOf (Bs X : Subgroup G) :
    Nat.card ↥((Bs ⊓ X).subgroupOf X) = Nat.card ↥(Bs ⊓ X) :=
  Nat.card_congr (lrg_subgroupOfEquiv Bs X).toEquiv

private def lrg_SignedData (p : ℕ) (Bs X : Subgroup G) : Prop :=
  ∃ (k : ℕ) (τ : (Fin k → Multiplicative (ZMod p)) →* ↥(Bs ⊓ X)),
    Function.Injective τ ∧ Function.Surjective τ ∧
    (∀ i : Fin k, ∃ w : X, ∀ f,
      (w : G) * (τ f : G) * (w : G)⁻¹ = (τ (SpCoord.sgnAut i f) : G)) ∧
    (∀ σ : Equiv.Perm (Fin k), ∃ w : X, ∀ f,
      (w : G) * (τ f : G) * (w : G)⁻¹ = (τ (SpCoord.permAut σ f) : G)) ∧
    ∀ g : X, (∀ e : ↥(Bs ⊓ X), ∃ e' : ↥(Bs ⊓ X),
        (g : G) * (e : G) * (g : G)⁻¹ = (e' : G)) →
      ∃ (π : Equiv.Perm (Fin k)) (ε : Fin k → ZMod p),
        (∀ i, ε i = 1 ∨ ε i = -1) ∧
        ∀ f f', (g : G) * (τ f : G) * (g : G)⁻¹ = (τ f' : G) →
          ∀ i, Multiplicative.toAdd (f' (π i)) = ε i * Multiplicative.toAdd (f i)

private lemma lrg_signedData_of_signedElt {p n : ℕ} {Bs X : Subgroup G}
    (h : GGTorusSignedElt p n ↥X) (hEab : IsElemAbelian p (Bs ⊓ X))
    (hr : p ^ n ≤ Nat.card ↥(Bs ⊓ X)) (h3 : p ^ 3 ≤ Nat.card ↥(Bs ⊓ X)) :
    lrg_SignedData p Bs X := by
  have hEab' : IsElemAbelian p ((Bs ⊓ X).subgroupOf X) := hEab.subgroupOf X
  have hr' : p ^ n ≤ Nat.card ↥((Bs ⊓ X).subgroupOf X) := by
    rw [lrg_card_subgroupOf]; exact hr
  have h3' : p ^ 3 ≤ Nat.card ↥((Bs ⊓ X).subgroupOf X) := by
    rw [lrg_card_subgroupOf]; exact h3
  obtain ⟨k, τ, hτinj, hτrange, hsgn, hperm, hnorm⟩ :=
    h ((Bs ⊓ X).subgroupOf X) hEab' hr' h3'
  let eτ : (Fin k → Multiplicative (ZMod p)) ≃* ↥(Bs ⊓ X) :=
    (MonoidHom.ofInjective hτinj).trans
      ((MulEquiv.subgroupCongr hτrange).trans (lrg_subgroupOfEquiv Bs X))
  have hcoe : ∀ f, (eτ.toMonoidHom f : G) = (τ f : G) := fun f => rfl
  refine ⟨k, eτ.toMonoidHom, eτ.injective, eτ.surjective, ?_, ?_, ?_⟩
  · intro i
    obtain ⟨w, hw⟩ := hsgn i
    refine ⟨w, fun f => ?_⟩
    rw [hcoe f, hcoe (SpCoord.sgnAut i f)]
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using congrArg Subtype.val (hw f)
  · intro σ
    obtain ⟨w, hw⟩ := hperm σ
    refine ⟨w, fun f => ?_⟩
    rw [hcoe f, hcoe (SpCoord.permAut σ f)]
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using congrArg Subtype.val (hw f)
  · intro g hg
    have hg' : ∀ e ∈ (Bs ⊓ X).subgroupOf X, g * e * g⁻¹ ∈ (Bs ⊓ X).subgroupOf X := by
      intro e he
      rw [Subgroup.mem_subgroupOf] at he
      obtain ⟨e', he'⟩ := hg ⟨(e : G), he⟩
      rw [Subgroup.mem_subgroupOf]
      have h1 : ((g * e * g⁻¹ : ↥X) : G) = (e' : G) := by
        simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using he'
      rw [h1]
      exact e'.2
    obtain ⟨π, ε, hε, hrel⟩ := hnorm g hg'
    refine ⟨π, ε, hε, fun f f' hff' => hrel f f' ?_⟩
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [hcoe f, hcoe f'] at hff'
    exact hff'

private lemma lrg_signedData_of_signedEltSC {p : ℕ} {B Bs X : Subgroup G}
    (hBs : GGBstar p B Bs) (hZ : Subgroup.center X = ⊥)
    (hnorm : Bs ≤ Subgroup.normalizer (X : Set G))
    (hinner : ∀ b ∈ Bs, ∃ x ∈ X, ∀ y ∈ X, b * y * b⁻¹ = x * y * x⁻¹)
    (hEab : IsElemAbelian p (Bs ⊓ X)) (h3 : p ^ 3 ≤ Nat.card ↥(Bs ⊓ X))
    (h : GGTorusSignedEltSC p ↥X) : lrg_SignedData p Bs X := by
  have hEab' : IsElemAbelian p ((Bs ⊓ X).subgroupOf X) := hEab.subgroupOf X
  have h3' : p ^ 3 ≤ Nat.card ↥((Bs ⊓ X).subgroupOf X) := by
    rw [lrg_card_subgroupOf]; exact h3
  have hsc : ∀ g : ↥X, (∀ e ∈ (Bs ⊓ X).subgroupOf X, g * e = e * g) → g ^ p = 1 →
      g ∈ (Bs ⊓ X).subgroupOf X := by
    intro g hgc hgp
    rw [Subgroup.mem_subgroupOf] at ⊢
    refine Subgroup.mem_inf.mpr ⟨hBs.2.2.2 (g : G) ?_ ?_, g.2⟩
    · rw [Subgroup.mem_centralizer_iff]
      intro b hb
      obtain ⟨e, he, c, hc, rfl⟩ := ggBstar_split_of_inner hBs hZ hnorm hinner b hb
      have hge : (g : G) * (e : G) = (e : G) * (g : G) := by
        have h1 := hgc ⟨(e : G), he.2⟩ (Subgroup.mem_subgroupOf.mpr he)
        simpa only [Subgroup.coe_mul] using congrArg Subtype.val h1
      have hgc' : (g : G) * (c : G) = (c : G) * (g : G) :=
        Subgroup.mem_centralizer_iff.mp hc.2 (g : G) g.2
      have key : (g : G) * ((e : G) * (c : G)) = ((e : G) * (c : G)) * (g : G) := by
        calc (g : G) * ((e : G) * (c : G)) = ((g : G) * e) * c := by group
          _ = ((e : G) * g) * c := by rw [hge]
          _ = (e : G) * ((g : G) * c) := by group
          _ = (e : G) * ((c : G) * (g : G)) := by rw [hgc']
          _ = ((e : G) * (c : G)) * (g : G) := by group
      exact key.symm
    · simpa only [Subgroup.coe_pow, Subgroup.coe_one] using congrArg Subtype.val hgp
  obtain ⟨k, τ, hτinj, hτrange, hsgn, hperm, hnorm⟩ :=
    h ((Bs ⊓ X).subgroupOf X) hEab' h3' hsc
  let eτ : (Fin k → Multiplicative (ZMod p)) ≃* ↥(Bs ⊓ X) :=
    (MonoidHom.ofInjective hτinj).trans
      ((MulEquiv.subgroupCongr hτrange).trans (lrg_subgroupOfEquiv Bs X))
  have hcoe : ∀ f, (eτ.toMonoidHom f : G) = (τ f : G) := fun f => rfl
  refine ⟨k, eτ.toMonoidHom, eτ.injective, eτ.surjective, ?_, ?_, ?_⟩
  · intro i
    obtain ⟨w, hw⟩ := hsgn i
    refine ⟨w, fun f => ?_⟩
    rw [hcoe f, hcoe (SpCoord.sgnAut i f)]
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using congrArg Subtype.val (hw f)
  · intro σ
    obtain ⟨w, hw⟩ := hperm σ
    refine ⟨w, fun f => ?_⟩
    rw [hcoe f, hcoe (SpCoord.permAut σ f)]
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using congrArg Subtype.val (hw f)
  · intro g hg
    have hg' : ∀ e ∈ (Bs ⊓ X).subgroupOf X, g * e * g⁻¹ ∈ (Bs ⊓ X).subgroupOf X := by
      intro e he
      rw [Subgroup.mem_subgroupOf] at he
      obtain ⟨e', he'⟩ := hg ⟨(e : G), he⟩
      rw [Subgroup.mem_subgroupOf]
      have h1 : ((g * e * g⁻¹ : ↥X) : G) = (e' : G) := by
        simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using he'
      rw [h1]
      exact e'.2
    obtain ⟨π, ε, hε, hrel⟩ := hnorm g hg'
    refine ⟨π, ε, hε, fun f f' hff' => hrel f f' ?_⟩
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [hcoe f, hcoe f'] at hff'
    exact hff'

private def lrg_prodAut {V C : Type} [Group V] [Group C] (α : MulAut V) : MulAut (V × C) where
  toFun q := (α q.1, q.2)
  invFun q := (α.symm q.1, q.2)
  left_inv q := by obtain ⟨f, c⟩ := q; simp
  right_inv q := by obtain ⟨f, c⟩ := q; simp
  map_mul' q r := by obtain ⟨f, c⟩ := q; obtain ⟨g, d⟩ := r; simp [mul_assoc]

private lemma lrg_prodAut_apply {V C : Type} [Group V] [Group C] (α : MulAut V) (f : V) (c : C) :
    lrg_prodAut (C := C) α (f, c) = (α f, c) := rfl

private def lrg_prodAutHom (V C : Type) [Group V] [Group C] : MulAut V →* MulAut (V × C) where
  toFun := lrg_prodAut (C := C)
  map_one' := by
    ext q <;> simp [lrg_prodAut]
  map_mul' α β := by
    ext q <;> simp [lrg_prodAut]

private noncomputable def lrg_fixProdEquiv {V C : Type} [Group V] [Group C] (α : MulAut V) :
    {q : V × C // lrg_prodAut (C := C) α q = q} ≃ {f : V // α f = f} × C where
  toFun q := (⟨q.1.1, by
    change α q.1.1 = q.1.1
    exact congrArg Prod.fst q.2⟩, q.1.2)
  invFun q := ⟨(q.1.1, q.2), by
    rw [lrg_prodAut_apply, q.1.2]⟩
  left_inv q := by
    obtain ⟨⟨f, c⟩, hq⟩ := q
    rfl
  right_inv q := by
    obtain ⟨⟨f, hf⟩, c⟩ := q
    rfl

private noncomputable def lrg_liftHom {V C : Type} [Group V] [Group C] {Bs : Type} [Group Bs]
    (Φ : V × C ≃* Bs) : MulAut V →* MulAut Bs :=
  (MulAut.congr Φ).toMonoidHom.comp (lrg_prodAutHom V C)

private lemma lrg_liftHom_apply {V C : Type} [Group V] [Group C] {Bs : Type} [Group Bs]
    (Φ : V × C ≃* Bs) (α : MulAut V) (f : V) (c : C) :
    lrg_liftHom Φ α (Φ (f, c)) = Φ (α f, c) := by
  change (MulAut.congr Φ) ((lrg_prodAutHom V C) α) (Φ (f, c)) = Φ (α f, c)
  rw [MulAut.congr_apply]
  simp [lrg_prodAutHom, lrg_prodAut]

private lemma lrg_isReflection_lift {p : ℕ} {G : Type} [Group G] {V C : Type} [Group V] [Group C]
    {Bs : Subgroup G} (Φ : V × C ≃* ↥Bs) (α : MulAut V) (hα2 : α ^ 2 = 1)
    (hαfix : Nat.card {f : V // α f = f} * p = Nat.card V) :
    GGIsReflection p (lrg_liftHom Φ α) := by
  constructor
  · rw [← map_pow, hα2, map_one]
  · have h1 : Nat.card {b : ↥Bs // lrg_liftHom Φ α b = b} =
        Nat.card {q : V × C // lrg_prodAut (C := C) α q = q} := by
      refine (Nat.card_congr (Equiv.subtypeEquiv Φ.toEquiv fun q => ?_)).symm
      change (lrg_prodAut (C := C) α q = q) ↔ (lrg_liftHom Φ α (Φ q) = Φ q)
      rw [lrg_liftHom_apply Φ α q.1 q.2]
      exact (Φ.injective.eq_iff).symm
    have h2 : Nat.card ↥Bs = Nat.card V * Nat.card C := by
      rw [← Nat.card_congr Φ.toEquiv, Nat.card_prod]
    rw [h1, Nat.card_congr (lrg_fixProdEquiv (C := C) α), Nat.card_prod, h2]
    calc Nat.card {f : V // α f = f} * Nat.card C * p
        = (Nat.card {f : V // α f = f} * p) * Nat.card C := by ring
      _ = Nat.card V * Nat.card C := by rw [hαfix]

private theorem lrg_main_of_signedData {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {B Bs X : Subgroup G} (hBs : GGBstar p B Bs) (hZ : Subgroup.center X = ⊥)
    (hNK : Bs ≤ Subgroup.normalizer (X : Set G))
    (hinner : ∀ b ∈ Bs, ∃ x ∈ X, ∀ y ∈ X, b * y * b⁻¹ = x * y * x⁻¹)
    (hSD : lrg_SignedData p Bs X) :
    GGReflGenerated p (ggAutomizer X Bs) ∧
      ∀ b : ↥Bs, (∀ ψ ∈ ggAutomizer X Bs, ψ b = b) →
        (b : G) ∈ Subgroup.centralizer (X : Set G) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, τ, hinj, hsurj, hsgn, hperm, hnorm⟩ := hSD
  let V := Fin k → Multiplicative (ZMod p)
  let C : Subgroup G := Bs ⊓ Subgroup.centralizer (X : Set G)
  let τE : V ≃* ↥(Bs ⊓ X) := MulEquiv.ofBijective τ ⟨hinj, hsurj⟩
  let Φ : V × ↥C ≃* ↥Bs :=
    (MulEquiv.prodCongr τE (MulEquiv.refl ↥C)).trans (lrg_prodEquiv hBs hZ hNK hinner)
  have hΦval : ∀ (f : V) (c : ↥C), ((Φ (f, c) : ↥Bs) : G) = (τ f : G) * (c : G) := by
    intro f c
    change ((lrg_prodHom Bs X (τE f, c) : ↥Bs) : G) = (τ f : G) * (c : G)
    rfl
  have hmem_normalizer : ∀ {w : X} {s : MulAut V},
      (∀ f, (w : G) * (τ f : G) * (w : G)⁻¹ = (τ (s f) : G)) →
      (w : G) ∈ Subgroup.normalizer (Bs : Set G) := by
    intro w s hconj
    rw [Subgroup.mem_normalizer_iff]
    intro b
    constructor
    · intro hb
      obtain ⟨e, he, c, hc, rfl⟩ := ggBstar_split_of_inner hBs hZ hNK hinner b hb
      obtain ⟨f, hf⟩ := hsurj ⟨e, he⟩
      have hfval : (τ f : G) = e := congrArg Subtype.val hf
      have hwe : (w : G) * (e : G) * (w : G)⁻¹ = (τ (s f) : G) := by
        rw [← hfval]; exact hconj f
      have hwc : (w : G) * (c : G) * (w : G)⁻¹ = (c : G) := by
        have hcomm : (w : G) * (c : G) = (c : G) * (w : G) :=
          Subgroup.mem_centralizer_iff.mp hc.2 (w : G) w.2
        rw [hcomm]; group
      rw [show (w : G) * ((e : G) * (c : G)) * (w : G)⁻¹ =
          ((w : G) * (e : G) * (w : G)⁻¹) * ((w : G) * (c : G) * (w : G)⁻¹) by group,
        hwe, hwc]
      exact Bs.mul_mem (τ (s f)).2.1 hc.1
    · intro hb
      obtain ⟨e, he, c, hc, hbc⟩ :=
        ggBstar_split_of_inner hBs hZ hNK hinner (w * b * w⁻¹) hb
      obtain ⟨f, hf⟩ := hsurj ⟨e, he⟩
      have hfval : (τ f : G) = e := congrArg Subtype.val hf
      have hwe : (w : G)⁻¹ * (e : G) * (w : G) = (τ (s⁻¹ f) : G) := by
        have h := hconj (s⁻¹ f)
        rw [show s (s⁻¹ f) = f from MulAut.apply_inv_self V s f, hfval] at h
        rw [← h]
        group
      have hwc : (w : G)⁻¹ * (c : G) * (w : G) = (c : G) := by
        have hcomm : (w : G) * (c : G) = (c : G) * (w : G) :=
          Subgroup.mem_centralizer_iff.mp hc.2 (w : G) w.2
        calc (w : G)⁻¹ * (c : G) * (w : G)
            = (w : G)⁻¹ * ((c : G) * (w : G)) := by group
          _ = (w : G)⁻¹ * ((w : G) * (c : G)) := by rw [hcomm]
          _ = (c : G) := by group
      have hb_eq2 : b = (w : G)⁻¹ * ((e : G) * (c : G)) * (w : G) := by
        rw [← hbc]
        simp only [Subgroup.coe_inv, Subgroup.coe_mul]
        group
      have hb_eq : b = (τ (s⁻¹ f) : G) * (c : G) := by
        rw [hb_eq2,
          show (w : G)⁻¹ * ((e : G) * (c : G)) * (w : G) =
            ((w : G)⁻¹ * (e : G) * (w : G)) *
              ((w : G)⁻¹ * (c : G) * (w : G)) by group, hwe, hwc]
      rw [hb_eq]
      exact Bs.mul_mem (τ (s⁻¹ f)).2.1 hc.1
  have hlift_of_conj : ∀ {w : X} (hwN : (w : G) ∈ Subgroup.normalizer (Bs : Set G))
      (s : MulAut V),
      (∀ f, (w : G) * (τ f : G) * (w : G)⁻¹ = (τ (s f) : G)) →
      lrg_liftHom Φ s = ggConjAut Bs hwN := by
    intro w hwN s hconj
    apply MulEquiv.ext
    intro b
    obtain ⟨⟨f, c⟩, rfl⟩ := Φ.surjective b
    rw [lrg_liftHom_apply]
    apply Subtype.ext
    rw [ggConjAut_apply]
    have hwc : (w : G) * (c : G) * (w : G)⁻¹ = (c : G) := by
      have hcomm : (w : G) * (c : G) = (c : G) * (w : G) :=
        Subgroup.mem_centralizer_iff.mp c.2.2 (w : G) w.2
      rw [hcomm]; group
    rw [hΦval, hΦval]
    calc (τ (s f) : G) * (c : G)
        = ((w : G) * (τ f : G) * (w : G)⁻¹) * (c : G) := by rw [← hconj f]
      _ = ((w : G) * (τ f : G) * (w : G)⁻¹) *
            ((w : G) * (c : G) * (w : G)⁻¹) := by rw [hwc]
      _ = (w : G) * ((τ f : G) * (c : G)) * (w : G)⁻¹ := by group
  let W : Subgroup (MulAut ↥Bs) :=
    Subgroup.closure {φ : MulAut ↥Bs | φ ∈ ggAutomizer X Bs ∧ GGIsReflection p φ}
  let H : Subgroup (MulAut V) := W.comap (lrg_liftHom Φ)
  have hsH : ∀ i : Fin k, SpCoord.sgnAut i ∈ H := by
    intro i
    obtain ⟨w, hw⟩ := hsgn i
    have hwN : (w : G) ∈ Subgroup.normalizer (Bs : Set G) := hmem_normalizer hw
    have hlift := hlift_of_conj hwN (SpCoord.sgnAut i) hw
    rw [Subgroup.mem_comap, hlift]
    exact Subgroup.subset_closure ⟨ggConjAut_mem_ggAutomizer w.2 hwN,
      hlift ▸ lrg_isReflection_lift Φ (SpCoord.sgnAut i) (SpCoord.sgnAut_sq i)
        (SpCoord.card_fix_sgnAut hp hp2 i)⟩
  have htH : ∀ a b : Fin k, a ≠ b → SpCoord.permAut (Equiv.swap a b) ∈ H := by
    intro a b hab
    obtain ⟨w, hw⟩ := hperm (Equiv.swap a b)
    have hwN : (w : G) ∈ Subgroup.normalizer (Bs : Set G) := hmem_normalizer hw
    have hlift := hlift_of_conj hwN (SpCoord.permAut (Equiv.swap a b)) hw
    rw [Subgroup.mem_comap, hlift]
    exact Subgroup.subset_closure ⟨ggConjAut_mem_ggAutomizer w.2 hwN,
      hlift ▸ lrg_isReflection_lift Φ (SpCoord.permAut (Equiv.swap a b))
        (SpCoord.permAut_swap_sq a b) (SpCoord.card_fix_permAut_swap hp hp2 hab)⟩
  have hgen : ∀ (g : X) (hgN : (g : G) ∈ Subgroup.normalizer (Bs : Set G)),
      ggConjAut Bs hgN ∈ W := by
    intro g hgN
    have hgE : ∀ e : ↥(Bs ⊓ X), ∃ e' : ↥(Bs ⊓ X),
        (g : G) * (e : G) * (g : G)⁻¹ = (e' : G) := by
      intro e
      refine ⟨⟨(g : G) * (e : G) * (g : G)⁻¹, Subgroup.mem_inf.mpr ⟨?_, ?_⟩⟩, rfl⟩
      · exact (Subgroup.mem_normalizer_iff.mp hgN (e : G)).mp e.2.1
      · exact X.mul_mem (X.mul_mem g.2 e.2.2) (X.inv_mem g.2)
    obtain ⟨π, ε, hε, hrel⟩ := hnorm g hgE
    let conjEHom : ↥(Bs ⊓ X) →* ↥(Bs ⊓ X) :=
      { toFun := fun e => ⟨(g : G) * (e : G) * (g : G)⁻¹, Subgroup.mem_inf.mpr
          ⟨(Subgroup.mem_normalizer_iff.mp hgN (e : G)).mp e.2.1,
            X.mul_mem (X.mul_mem g.2 e.2.2) (X.inv_mem g.2)⟩⟩
        map_one' := Subtype.ext (by simp)
        map_mul' := fun a b => Subtype.ext (by simp only [Subgroup.coe_mul]; group) }
    have hconjE_inj : Function.Injective conjEHom := by
      intro a b h
      apply Subtype.ext
      have h1 : (g : G) * (a : G) * (g : G)⁻¹ = (g : G) * (b : G) * (g : G)⁻¹ :=
        congrArg Subtype.val h
      exact mul_left_cancel (mul_right_cancel h1)
    have hconjE_surj : Function.Surjective conjEHom :=
      (Finite.injective_iff_surjective.mp hconjE_inj)
    let conjE : MulAut ↥(Bs ⊓ X) :=
      MulEquiv.ofBijective conjEHom ⟨hconjE_inj, hconjE_surj⟩
    let α : MulAut V := (MulAut.congr τE).symm conjE
    have hατ : ∀ f : V, (τ (α f) : G) = (g : G) * (τ f : G) * (g : G)⁻¹ := by
      intro f
      have h1 : τE (α f) = conjE (τE f) := by
        have h := congrArg (fun φ : MulAut ↥(Bs ⊓ X) => φ (τE f))
          (MulEquiv.apply_symm_apply (MulAut.congr τE) conjE)
        rw [MulAut.congr_apply] at h
        simpa only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply] using h
      have h2 : ((τE (α f) : ↥(Bs ⊓ X)) : G) = (g : G) * (τ f : G) * (g : G)⁻¹ := by
        rw [h1]
        rfl
      exact h2
    have hαsigned : SpCoord.IsSignedPerm (α : V → V) :=
      ⟨π, ε, hε, fun f i => hrel f (α f) (hατ f).symm i⟩
    have hαlift : lrg_liftHom Φ α = ggConjAut Bs hgN :=
      hlift_of_conj hgN α fun f => (hατ f).symm
    have hαH : α ∈ H := SpCoord.mem_of_isSignedPerm hsH htH hαsigned
    rw [Subgroup.mem_comap, hαlift] at hαH
    exact hαH
  refine ⟨?_, ?_⟩
  · change ggAutomizer X Bs = W
    apply le_antisymm
    · change Subgroup.closure (ggInduced X Bs) ≤ W
      refine (Subgroup.closure_le W).mpr ?_
      rintro φ ⟨g, hgX, hgN, hφ⟩
      have hφeq : φ = ggConjAut Bs hgN := MulEquiv.ext fun b => Subtype.ext (hφ b)
      rw [hφeq]
      exact hgen ⟨g, hgX⟩ hgN
    · exact (Subgroup.closure_le _).mpr fun φ hφ => hφ.1
  · intro b hfix
    obtain ⟨⟨f, c⟩, hb⟩ := Φ.surjective b
    have hf : f = 1 := by
      funext i
      obtain ⟨w, hw⟩ := hsgn i
      have hwN : (w : G) ∈ Subgroup.normalizer (Bs : Set G) := hmem_normalizer hw
      have hlift : lrg_liftHom Φ (SpCoord.sgnAut i) = ggConjAut Bs hwN :=
        hlift_of_conj hwN (SpCoord.sgnAut i) hw
      have hfixi := hfix (ggConjAut Bs hwN) (ggConjAut_mem_ggAutomizer w.2 hwN)
      rw [← hlift, ← hb] at hfixi
      have h1 : SpCoord.sgnAut i f = f := by
        have h2 : Φ (SpCoord.sgnAut i f, c) = Φ (f, c) := by
          rw [← lrg_liftHom_apply Φ (SpCoord.sgnAut i) f c]
          exact hfixi
        exact congrArg Prod.fst (Φ.injective h2)
      have h3 : (f i)⁻¹ = f i := by
        have h4 := congrFun h1 i
        rw [SpCoord.sgnAut_apply, Function.update_self] at h4
        exact h4
      have h5 : Multiplicative.toAdd (f i) = 0 := by
        have h7 : -Multiplicative.toAdd (f i) = Multiplicative.toAdd (f i) := by
          have h6 := congrArg Multiplicative.toAdd h3
          rwa [toAdd_inv] at h6
        have hxx : Multiplicative.toAdd (f i) + Multiplicative.toAdd (f i) = 0 :=
          neg_eq_iff_add_eq_zero.mp h7
        have h2x : (2 : ZMod p) * Multiplicative.toAdd (f i) = 0 := by
          rw [two_mul, hxx]
        have h2nz : (2 : ZMod p) ≠ 0 := by
          intro h
          have hd : p ∣ 2 := (CharP.cast_eq_zero_iff (ZMod p) p 2).mp h
          exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hd)
        exact (mul_eq_zero.mp h2x).resolve_left h2nz
      show f i = 1
      exact Multiplicative.toAdd.injective (by simpa using h5)
    rw [← hb, hf]
    simpa [hΦval] using c.2.2

end Helpers

theorem dvd_card_sub_one_or_add_one_of_planeTorus {F : Type} [Field F] [Finite F] [CharP F 2]
    {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hn : 1 ≤ n) {Bs X : Subgroup G}
    {ζ : Multiplicative (ZMod p) →* Matrix.SpecialLinearGroup (Fin 2) F} {φ : StatedSp n F →* G}
    (hl : IsPlaneTorusLift p Bs X ζ φ) :
    p ∣ Nat.card F - 1 ∨ p ∣ Nat.card F + 1 := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  have hτinj : Function.Injective (CFSG.StandardType.SpJoin.spPlaneTorus n ζ) :=
    Function.Injective.of_comp (f := φ) (g := CFSG.StandardType.SpJoin.spPlaneTorus n ζ)
      (by simpa only [MonoidHom.coe_comp] using hl.torus_injective)
  have hζinj : Function.Injective ζ := by
    intro a b hab
    have h1 : Pi.mulSingle (M := fun _ : Fin n => Multiplicative (ZMod p))
        (⟨0, hn⟩ : Fin n) a =
        Pi.mulSingle (M := fun _ : Fin n => Multiplicative (ZMod p)) (⟨0, hn⟩ : Fin n) b := by
      apply hτinj
      rw [CFSG.StandardType.SpJoin.spPlaneTorus_mulSingle,
        CFSG.StandardType.SpJoin.spPlaneTorus_mulSingle, hab]
    simpa using congrFun h1 (⟨0, hn⟩ : Fin n)
  have hcardζ : Nat.card ↥ζ.range = p := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hζinj).toEquiv,
      Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
  have hpSL : p ∣ Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) := by
    have h := Subgroup.card_subgroup_dvd_card ζ.range
    rwa [hcardζ] at h
  rw [CFSG.CGT.PushingUpLit.BHS6.card_SL2_eq] at hpSL
  obtain ⟨k, -, hk⟩ := FiniteField.card F 2
  have hqpow : Nat.card F = 2 ^ (k : ℕ) := by
    rw [Nat.card_eq_fintype_card, hk]
  have hp_dvd_two : p ∣ 2 ↔ p = 2 := Nat.prime_dvd_prime_iff_eq hp Nat.prime_two
  have hpq : ¬ p ∣ Nat.card F := by
    rw [hqpow]
    intro h
    exact hp2 (hp_dvd_two.mp (hp.dvd_of_dvd_pow h))
  have hfac : Nat.card F ^ 2 - 1 = (Nat.card F + 1) * (Nat.card F - 1) := by
    simpa using Nat.sq_sub_sq (Nat.card F) 1
  rw [hfac] at hpSL
  have hprod : p ∣ (Nat.card F + 1) * (Nat.card F - 1) :=
    (hp.dvd_mul.mp hpSL).resolve_left hpq
  rcases hp.dvd_mul.mp hprod with h | h
  · exact Or.inr h
  · exact Or.inl h


theorem ggReflGenerated_of_spLift {F : Type} [Field F] [Finite F] [CharP F 2] {p n : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hn : 3 ≤ n) (φ' : StatedSp n F →* G)
    (hinj : Function.Injective φ') {B Bs X : Subgroup G} (hBs : GGBstar p B Bs)
    (hrange : φ'.range = X) (hNK : Bs ≤ Subgroup.normalizer (X : Set G))
    (hinner : ∀ b ∈ Bs, ∃ x ∈ X, ∀ y ∈ X, b * y * b⁻¹ = x * y * x⁻¹)
    (hcent : Nat.card ↥(Bs ⊓ Subgroup.centralizer (X : Set G)) ≤ p)
    (hrank : p ^ (n + 1) ≤ Nat.card Bs) :
    GGReflGenerated p (ggAutomizer X Bs) ∧
      ∀ b : ↥Bs, (∀ ψ ∈ ggAutomizer X Bs, ψ b = b) →
        (b : G) ∈ Subgroup.centralizer (X : Set G) := by
  classical
  have hZ : Subgroup.center X = ⊥ := by
    rw [← hrange]
    have hZsp : Subgroup.center (StatedSp n F) = ⊥ := by
      rw [CFSG.LieType.Universal.Symplectic.center_eq,
        CFSG.Open.StatedAPI.statedScalars_subgroupOf_statedSp_eq_bot]
    have he := Subgroup.map_center_eq (MonoidHom.ofInjective hinj)
    rw [hZsp, Subgroup.map_bot] at he
    exact he.symm
  have hcard_split := card_ggBstar_split (X := X) hBs hZ hNK hinner
  have hcardX : p ^ n ≤ Nat.card ↥(Bs ⊓ X) := by
    have hle : p ^ n * p ≤ Nat.card ↥(Bs ⊓ X) * p := by
      calc p ^ n * p = p ^ (n + 1) := by rw [← pow_succ]
        _ ≤ Nat.card Bs := hrank
        _ = Nat.card ↥(Bs ⊓ X) *
              Nat.card ↥(Bs ⊓ Subgroup.centralizer (X : Set G)) := hcard_split
        _ ≤ Nat.card ↥(Bs ⊓ X) * p := Nat.mul_le_mul_left _ hcent
    exact Nat.le_of_mul_le_mul_right hle hp.pos
  have hcard3 : p ^ 3 ≤ Nat.card ↥(Bs ⊓ X) :=
    le_trans (Nat.pow_le_pow_right hp.pos hn) hcardX
  have hEab : IsElemAbelian p (Bs ⊓ X) := hBs.2.1.mono inf_le_left
  haveI : NeZero n := ⟨by omega⟩
  let e₁ : ↥(CFSG.Assembly.LargeEvenSpGroup F n) ≃*
      CFSG.Assembly.LargeEvenProj (CFSG.Assembly.LargeEvenSpGroup F n) :=
    MulEquiv.ofBijective (CFSG.Assembly.LargeEvenProjMk (CFSG.Assembly.LargeEvenSpGroup F n))
      ⟨AutPSp.proj_injective (n := n) (K := F), QuotientGroup.mk'_surjective _⟩
  let eX : ↥X ≃* ↥(StatedSp n F) :=
    ((MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)).symm
  have hLS : CFSG.Assembly.LargeEvenSpGroup F n = StatedSp n F := rfl
  let e : ↥X ≃* CFSG.Assembly.LargeEvenProj (CFSG.Assembly.LargeEvenSpGroup F n) :=
    (eX.trans (MulEquiv.subgroupCongr hLS.symm)).trans e₁
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  obtain ⟨ζ, φ, hl⟩ :=
    exists_plane_torus_lift_of_range hp hp2 h2 φ' hinj hBs hrange hNK hinner hcent hrank
  have hcase := dvd_card_sub_one_or_add_one_of_planeTorus hp hp2 (by omega : 1 ≤ n) hl
  have hSD : lrg_SignedData p Bs X := by
    rcases hcase with hpq | hpq
    · exact lrg_signedData_of_signedElt
        (ggTorusSignedElt_of_mulEquiv e
          (SpModel.ggTorusSignedElt_sp (K := F) (m := n) hp hp2 hpq)) hEab hcardX hcard3
    · exact lrg_signedData_of_signedEltSC hBs hZ hNK hinner hEab hcard3
        (ggTorusSignedEltSC_of_mulEquiv e
          (ggSpNonsplitSignedEltInput_holds F n p (by omega) hp hpq))
  exact lrg_main_of_signedData hp hp2 hBs hZ hNK hinner hSD


end Pure

end CFSG.StandardType.SpJoinRefl
