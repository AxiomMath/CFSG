module

public import CFSG.LocalAnalysis.StandardType.FF81.PropOne.AStarSylow
import CFSG.LocalAnalysis.StandardType.FF81.PropOne.RankBound
import CFSG.LocalAnalysis.StandardType.FF81.PropOne.LMonomial
import CFSG.LocalAnalysis.StandardType.FF81.LocalSetupCen

@[expose] public section

namespace CFSG.StandardType.FF81.PropOne

open scoped IsMulCommutative

open CFSG.RankThree.PartTwo.Sec4.Item434Kit (vecElt)

private theorem card_cen_eq_mul_card_cen_ker_range {G : Type*} [Group G] {t : G}
    (ht : t * t = 1) {X : Subgroup G} (hXt : ∀ x ∈ X, t * x * t⁻¹ ∈ X)
    (hXc : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x) (hX3 : ∀ x ∈ X, x ^ 3 = 1)
    (f : X →* X)
    (heq : ∀ x : X, f ⟨t * (x : G) * t⁻¹, hXt _ x.2⟩ =
      ⟨t * ((f x : X) : G) * t⁻¹, hXt _ (f x).2⟩) :
    Nat.card ↥(X ⊓ Subgroup.centralizer ({t} : Set G)) =
      Nat.card ↥(f.ker.map X.subtype ⊓ Subgroup.centralizer ({t} : Set G)) *
        Nat.card ↥(f.range.map X.subtype ⊓ Subgroup.centralizer ({t} : Set G)) := by
  let CX : Subgroup G := X ⊓ Subgroup.centralizer ({t} : Set G)
  let CK : Subgroup G := f.ker.map X.subtype ⊓ Subgroup.centralizer ({t} : Set G)
  let CR : Subgroup G := f.range.map X.subtype ⊓ Subgroup.centralizer ({t} : Set G)
  change Nat.card ↥CX = Nat.card ↥CK * Nat.card ↥CR
  have htinv : t⁻¹ * t⁻¹ = 1 := by rw [← mul_inv_rev, ht, inv_one]
  have hfixCX : ∀ x : CX, t * (x : G) * t⁻¹ = (x : G) := by
    intro x
    have hx := (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp x.2).2) t
      (Set.mem_singleton t)
    calc t * (x : G) * t⁻¹ = (x : G) * t * t⁻¹ := by rw [hx]
      _ = (x : G) := by group
  have hfixCR : ∀ y : CR, t * (y : G) * t⁻¹ = (y : G) := by
    intro y
    have hy := (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp y.2).2) t
      (Set.mem_singleton t)
    calc t * (y : G) * t⁻¹ = (y : G) * t * t⁻¹ := by rw [hy]
      _ = (y : G) := by group
  have hmemX : ∀ x : CX, (x : G) ∈ X := fun x => (Subgroup.mem_inf.mp x.2).1
  have hmaps : ∀ x : CX, ((f ⟨(x : G), hmemX x⟩ : X) : G) ∈ CR := by
    intro x
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · rw [Subgroup.mem_map]
      exact ⟨f ⟨(x : G), hmemX x⟩, ⟨⟨(x : G), hmemX x⟩, rfl⟩, rfl⟩
    · rw [Subgroup.mem_centralizer_iff]
      intro s hs
      rw [Set.mem_singleton_iff] at hs
      rw [hs]
      have harg : (⟨t * (x : G) * t⁻¹, hXt _ (hmemX x)⟩ : X) = ⟨(x : G), hmemX x⟩ :=
        Subtype.ext (hfixCX x)
      have h2 : (f ⟨(x : G), hmemX x⟩ : X) =
          ⟨t * ((f ⟨(x : G), hmemX x⟩ : X) : G) * t⁻¹,
            hXt _ (f ⟨(x : G), hmemX x⟩).2⟩ :=
        (congrArg f harg).symm.trans (heq ⟨(x : G), hmemX x⟩)
      have h3 : t * ((f ⟨(x : G), hmemX x⟩ : X) : G) * t⁻¹ = (f ⟨(x : G), hmemX x⟩ : X) :=
        (congrArg Subtype.val h2).symm
      calc t * ((f ⟨(x : G), hmemX x⟩ : X) : G)
          = t * ((f ⟨(x : G), hmemX x⟩ : X) : G) * t⁻¹ * t := by group
        _ = (f ⟨(x : G), hmemX x⟩ : X) * t := by rw [h3]
  let gfun : CX → CR := fun x => ⟨((f ⟨(x : G), hmemX x⟩ : X) : G), hmaps x⟩
  have gmul : ∀ x y : CX, gfun (x * y) = gfun x * gfun y := by
    intro x y
    apply Subtype.ext
    have harg : (⟨((x * y : CX) : G), hmemX (x * y)⟩ : X) =
        ⟨(x : G), hmemX x⟩ * ⟨(y : G), hmemX y⟩ := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
    change ((f ⟨((x * y : CX) : G), hmemX (x * y)⟩ : X) : G) =
      ((f ⟨(x : G), hmemX x⟩ : X) : G) * ((f ⟨(y : G), hmemX y⟩ : X) : G)
    rw [harg]
    exact congrArg Subtype.val (map_mul f ⟨(x : G), hmemX x⟩ ⟨(y : G), hmemX y⟩)
  let g : CX →* CR := MonoidHom.mk' gfun gmul
  have hsurj : Function.Surjective g := by
    intro y
    have hyR : (y : G) ∈ f.range.map X.subtype := (Subgroup.mem_inf.mp y.2).1
    obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.mp hyR
    have hyX : (y : G) ∈ X := hzy ▸ z.2
    obtain ⟨x, hx⟩ : ∃ x : X, (f x : G) = (y : G) := by
      rcases hz with ⟨w, hw⟩
      exact ⟨w, by rw [hw]; exact hzy⟩
    let u : X := x * ⟨t * (x : G) * t⁻¹, hXt _ x.2⟩
    have huval : (u : G) = (x : G) * (t * (x : G) * t⁻¹) := by
      simp only [u, Subgroup.coe_mul]
    have hconj : t * (t * (x : G) * t⁻¹) * t⁻¹ = (x : G) := by
      calc t * (t * (x : G) * t⁻¹) * t⁻¹ = (t * t) * (x : G) * (t⁻¹ * t⁻¹) := by group
        _ = (x : G) := by rw [ht, htinv, one_mul, mul_one]
    have hufix : t * (u : G) * t⁻¹ = (u : G) := by
      rw [huval]
      calc t * ((x : G) * (t * (x : G) * t⁻¹)) * t⁻¹
          = (t * (x : G) * t⁻¹) * (t * (t * (x : G) * t⁻¹) * t⁻¹) := by group
        _ = (t * (x : G) * t⁻¹) * (x : G) := by rw [hconj]
        _ = (x : G) * (t * (x : G) * t⁻¹) := hXc _ (hXt _ x.2) _ x.2
    have hfu : (f u : G) = (y : G) * (y : G) := by
      have h1 : (f u : G) = (f x : G) * ((f ⟨t * (x : G) * t⁻¹, hXt _ x.2⟩ : X) : G) := by
        change (f (x * ⟨t * (x : G) * t⁻¹, hXt _ x.2⟩) : G) = _
        exact congrArg Subtype.val (map_mul f x ⟨t * (x : G) * t⁻¹, hXt _ x.2⟩)
      have h2 : ((f ⟨t * (x : G) * t⁻¹, hXt _ x.2⟩ : X) : G) = t * (f x : G) * t⁻¹ :=
        congrArg Subtype.val (heq x)
      rw [h1, h2, hx, hfixCR y]
    have hy3 : (y : G) ^ 3 = 1 := hX3 _ hyX
    have huzC : (((u * u : X)) : G) ∈ Subgroup.centralizer ({t} : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro s hs
      rw [Set.mem_singleton_iff] at hs
      rw [hs]
      have hucomm : t * (u : G) = (u : G) * t := by
        calc t * (u : G) = t * (u : G) * t⁻¹ * t := by group
          _ = (u : G) * t := by rw [hufix]
      have huv : (((u * u : X)) : G) = (u : G) * (u : G) := by
        simp only [Subgroup.coe_mul]
      rw [huv]
      calc t * ((u : G) * (u : G)) = (t * (u : G)) * (u : G) := by group
        _ = ((u : G) * t) * (u : G) := by rw [hucomm]
        _ = (u : G) * (t * (u : G)) := by group
        _ = (u : G) * ((u : G) * t) := by rw [hucomm]
        _ = ((u : G) * (u : G)) * t := by group
    refine ⟨⟨(((u * u : X)) : G), ⟨(u * u : X).2, huzC⟩⟩, ?_⟩
    apply Subtype.ext
    change (f (u * u) : G) = (y : G)
    rw [congrArg Subtype.val (map_mul f u u), Subgroup.coe_mul, hfu]
    calc ((y : G) * (y : G)) * ((y : G) * (y : G))
        = (y : G) * ((y : G) * (y : G) * (y : G)) := by group
      _ = (y : G) * 1 := by rw [← pow_three' (y : G), hy3]
      _ = (y : G) := mul_one _
  have hker : g.ker.map CX.subtype = CK := by
    ext z
    constructor
    · intro hz
      rcases Subgroup.mem_map.mp hz with ⟨a, ha, haz⟩
      have ha' : f ⟨(a : G), hmemX a⟩ = 1 := by
        apply Subtype.ext
        have hga : g a = 1 := ha
        change (g a : G) = 1
        rw [hga]
        rfl
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · rw [Subgroup.mem_map]
        exact ⟨⟨(a : G), hmemX a⟩, ha', haz⟩
      · rw [← haz]
        exact (Subgroup.mem_inf.mp a.2).2
    · intro hz
      rcases (Subgroup.mem_inf.mp hz) with ⟨hzK, hzC⟩
      rw [Subgroup.mem_map] at hzK
      rcases hzK with ⟨yX, hyX, hyXz⟩
      have hzX : z ∈ X := by rw [← hyXz]; exact yX.2
      refine Subgroup.mem_map.mpr ⟨⟨z, hzX, hzC⟩, ?_, rfl⟩
      apply Subtype.ext
      change (f ⟨z, hzX⟩ : G) = 1
      have harg : (⟨z, hzX⟩ : X) = yX := Subtype.ext hyXz.symm
      calc (f ⟨z, hzX⟩ : G) = (f yX : G) := congrArg Subtype.val (congrArg f harg)
        _ = 1 := congrArg Subtype.val hyX
  have hcard : Nat.card ↥(g.ker.map CX.subtype) = Nat.card ↥g.ker :=
    Subgroup.card_map_of_injective CX.subtype_injective
  rw [hker] at hcard
  have hmain := Subgroup.card_ker_mul_card_of_surjective hsurj
  rw [hcard]
  exact hmain.symm

private def commEnd {G : Type*} [Group G] (b : G) (X : Subgroup G)
    (hnor : ∀ x ∈ X, b * x * b⁻¹ ∈ X)
    (hcomm : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x) : X →* X := by
  haveI : IsMulCommutative X :=
    IsMulCommutative.of_comm (fun (x : X) (y : X) => Subtype.ext (hcomm x x.2 y y.2))
  let φ : X →* X :=
    { toFun := fun x => ⟨b * (x : G) * b⁻¹, hnor x x.2⟩
      map_one' := by ext; simp
      map_mul' := by intro x y; ext; simp only [Subgroup.coe_mul]; group }
  exact φ * (MonoidHom.id X)⁻¹

private theorem commEnd_apply {G : Type*} [Group G] {b : G} {X : Subgroup G}
    (hnor : ∀ x ∈ X, b * x * b⁻¹ ∈ X)
    (hcomm : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x) (x : X) :
    ((commEnd b X hnor hcomm x : X) : G) = b * (x : G) * b⁻¹ * (x : G)⁻¹ :=
  letI : IsMulCommutative X :=
    IsMulCommutative.of_comm (fun (x : X) (y : X) => Subtype.ext (hcomm x x.2 y y.2))
  by
    simp only [commEnd]
    erw [MonoidHom.mul_apply, MonoidHom.inv_apply, MonoidHom.id_apply]
    rfl

private theorem commEnd_mem_ker {G : Type*} [Group G] {b : G} {X : Subgroup G}
    (hnor : ∀ x ∈ X, b * x * b⁻¹ ∈ X)
    (hcomm : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x) (x : X) :
    x ∈ (commEnd b X hnor hcomm).ker ↔ b * (x : G) = (x : G) * b := by
  rw [MonoidHom.mem_ker]
  constructor
  · intro h
    have h' := congrArg Subtype.val h
    simp only [commEnd_apply, Subgroup.coe_one] at h'
    have : b * (x : G) * b⁻¹ = (x : G) := mul_inv_eq_one.mp h'
    calc b * (x : G) = b * (x : G) * b⁻¹ * b := by group
      _ = (x : G) * b := by rw [this]
  · intro h
    apply Subtype.ext
    simp only [commEnd_apply, Subgroup.coe_one]
    rw [h]; group

private theorem commEnd_equivariant {G : Type*} [Group G] {b g : G} {X : Subgroup G}
    (hnor : ∀ x ∈ X, b * x * b⁻¹ ∈ X)
    (hcomm : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x)
    (hgnor : ∀ x ∈ X, g * x * g⁻¹ ∈ X) (hgb : g * b = b * g) (x : X) :
    commEnd b X hnor hcomm ⟨g * (x : G) * g⁻¹, hgnor x x.2⟩ =
      ⟨g * ((commEnd b X hnor hcomm x : X) : G) * g⁻¹,
        hgnor _ (commEnd b X hnor hcomm x).2⟩ := by
  apply Subtype.ext
  simp only [commEnd_apply]
  have h2 : g⁻¹ * b⁻¹ = b⁻¹ * g⁻¹ := by rw [← mul_inv_rev, ← mul_inv_rev, hgb]
  calc b * (g * (x : G) * g⁻¹) * b⁻¹ * (g * (x : G) * g⁻¹)⁻¹
      = (b * g) * (x : G) * (g⁻¹ * b⁻¹) * (g * (x : G)⁻¹ * g⁻¹) := by group
    _ = (g * b) * (x : G) * (b⁻¹ * g⁻¹) * (g * (x : G)⁻¹ * g⁻¹) := by rw [hgb, h2]
    _ = g * (b * (x : G) * b⁻¹ * (x : G)⁻¹) * g⁻¹ := by group

private theorem commEnd_cube_aux {G : Type*} [Group G] {b : G} (hb : b ^ 3 = 1)
    {X : Subgroup G} [IsMulCommutative X]
    (hnor : ∀ x ∈ X, b * x * b⁻¹ ∈ X)
    (hcomm : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x)
    (hX3 : ∀ x ∈ X, x ^ 3 = 1)
    (x : X) :
    commEnd b X hnor hcomm (commEnd b X hnor hcomm (commEnd b X hnor hcomm x)) = 1 := by
  let φ : X →* X :=
    { toFun := fun x => ⟨b * (x : G) * b⁻¹, hnor x x.2⟩
      map_one' := by ext; simp
      map_mul' := by intro x y; ext; simp only [Subgroup.coe_mul]; group }
  have hT : commEnd b X hnor hcomm = φ * (MonoidHom.id X)⁻¹ := rfl
  have hTz : ∀ z : X, commEnd b X hnor hcomm z = φ z * z⁻¹ := by
    intro z
    rw [hT, MonoidHom.mul_apply, MonoidHom.inv_apply, MonoidHom.id_apply]
  have hcube : ∀ z : X, z * z = z⁻¹ := by
    intro z
    have h3 : z * z * z = 1 := by
      apply Subtype.ext
      simpa [pow_succ, pow_two, mul_assoc] using hX3 (z : G) z.2
    calc z * z = ((z * z)⁻¹)⁻¹ := by rw [inv_inv]
      _ = z⁻¹ := by rw [inv_eq_of_mul_eq_one_right h3]
  have hcube' : ∀ z : X, z⁻¹ * z⁻¹ = z := by
    intro z
    rw [← mul_inv_rev, hcube z, inv_inv]
  have hb3 : b * b * b = 1 := by
    have h : b ^ 3 = b * b * b := by rw [pow_succ, pow_two]
    rw [← h]; exact hb
  have hkey : ∀ w : G,
      b * (b * (b * w * b⁻¹) * b⁻¹) * b⁻¹ = (b * b * b) * w * (b * b * b)⁻¹ := by
    intro w
    group
  have hφ3 : ∀ z : X, φ (φ (φ z)) = z := by
    intro z
    apply Subtype.ext
    change b * (b * (b * (z : G) * b⁻¹) * b⁻¹) * b⁻¹ = (z : G)
    rw [hkey (z : G), hb3, one_mul, inv_one, mul_one]
  have hT2 : ∀ y : X,
      commEnd b X hnor hcomm (commEnd b X hnor hcomm y) = φ (φ y) * y * φ y := by
    intro y
    rw [hTz (commEnd b X hnor hcomm y), hTz y, map_mul, map_inv, mul_inv_rev, inv_inv]
    rw [show (φ (φ y) * (φ y)⁻¹) * (y * (φ y)⁻¹)
          = φ (φ y) * y * ((φ y)⁻¹ * (φ y)⁻¹) by ac_rfl]
    rw [hcube' (φ y)]
  have hT3 : ∀ y : X,
      commEnd b X hnor hcomm (commEnd b X hnor hcomm (commEnd b X hnor hcomm y)) = 1 := by
    intro y
    rw [hTz (commEnd b X hnor hcomm (commEnd b X hnor hcomm y)), hT2 y, map_mul, map_mul,
      hφ3 y, mul_inv_rev, mul_inv_rev]
    rw [show (y * φ y * φ (φ y)) * ((φ y)⁻¹ * (y⁻¹ * (φ (φ y))⁻¹))
          = (y * y⁻¹) * (φ y * (φ y)⁻¹) * (φ (φ y) * (φ (φ y))⁻¹) by ac_rfl]
    simp
  exact hT3 x

private theorem commEnd_cube {G : Type*} [Group G] {b : G} (hb : b ^ 3 = 1)
    {X : Subgroup G} (hnor : ∀ x ∈ X, b * x * b⁻¹ ∈ X)
    (hcomm : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x)
    (hX3 : ∀ x ∈ X, x ^ 3 = 1)
    (x : X) :
    commEnd b X hnor hcomm (commEnd b X hnor hcomm (commEnd b X hnor hcomm x)) = 1 :=
  @commEnd_cube_aux G _ b hb X
    (IsMulCommutative.of_comm (fun x y => Subtype.ext (hcomm x x.2 y y.2))) hnor hcomm hX3 x

private theorem conj_pow_apply {G : Type*} [Group G] (g : G) : ∀ (x : G) (n : ℕ),
    g ^ n * x * (g ^ n)⁻¹ = ((MulAut.conj g) ^ n) x := by
  intro x n
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, pow_succ, MulAut.mul_apply, MulAut.conj_apply]
      rw [show (g ^ n * g) * x * (g ^ n * g)⁻¹ = g ^ n * (g * x * g⁻¹) * (g ^ n)⁻¹ by group]
      exact ih (g * x * g⁻¹)

private def wOf (p : Fin 2 → ZMod 3) : Fin 3 → ZMod 3 :=
  fun i => if i = 0 then 0 else if i = 1 then p 0 else p 1

private theorem wOf_zero (p : Fin 2 → ZMod 3) : wOf p 0 = 0 := by simp [wOf]

private theorem wOf_one (p : Fin 2 → ZMod 3) : wOf p 1 = p 0 := by
  simp [wOf, show (1 : Fin 3) ≠ 0 by decide]

private theorem wOf_two (p : Fin 2 → ZMod 3) : wOf p 2 = p 1 := by
  simp [wOf, show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide]

attribute [local simp] wOf_zero wOf_one wOf_two

structure AStar {G : Type} [Group G] (b : G) {L : Subgroup G} (z : Fin 3 → ↥L)
    (B₂ A : Subgroup G) : Prop where
  le_cen : A ≤ Subgroup.centralizer (B₂ : Set G)
  isP : IsPGroup 3 A
  max : ∀ P : Subgroup G, P ≤ Subgroup.centralizer (B₂ : Set G) → IsPGroup 3 P → A ≤ P → P = A
  comm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x
  B₂_le : B₂ ≤ A
  omega : ∀ x ∈ A, x ^ 3 = 1 → x ∈ B₂
  nor : ∀ g ∈ dGrp b z, ∀ x ∈ A, g * x * g⁻¹ ∈ A

theorem exists_aStar {G : Type} [Group G] [Finite G] {n : ℕ} {b : G} {L : Subgroup G}
    {z : Fin 3 → ↥L} (h : Counterexample G n b L z) {B₂ : Subgroup G}
    (hB₂ : B2Package b z B₂) : ∃ A : Subgroup G, AStar b z B₂ A := by
  obtain ⟨A, hA⟩ := exists_aStarBase h hB₂
  have st : GGFF.SettingCore b L z := h.settingCore
  have hb3 : b ^ 3 = 1 := by
    have := pow_orderOf_eq_one b
    rwa [h.hypA.ord] at this
  have hbc : ∀ x ∈ L, b * x = x * b := fun x hx =>
    (Subgroup.mem_centralizer_iff.mp (h.hypA.le hx)) b (Set.mem_singleton b)
  have hB₁L : bOne z ≤ L := GGFF.SettingCore.tor_le z
  let V : Subgroup G :=
    { carrier := {x | x ∈ A ∧ x ^ 3 = 1}
      mul_mem' := by
        rintro x y ⟨hxA, hx3⟩ ⟨hyA, hy3⟩
        refine ⟨A.mul_mem hxA hyA, ?_⟩
        have hc : Commute x y := hA.comm x hxA y hyA
        rw [hc.mul_pow 3, hx3, hy3, one_mul]
      one_mem' := ⟨A.one_mem, one_pow 3⟩
      inv_mem' := by
        rintro x ⟨hxA, hx3⟩
        exact ⟨A.inv_mem hxA, by rw [inv_pow, hx3, inv_one]⟩ }
  have hmemV : ∀ x, x ∈ V ↔ x ∈ A ∧ x ^ 3 = 1 := fun x => Iff.rfl
  have hB₂V : B₂ ≤ V := fun x hx => ⟨hA.B₂_le hx, hB₂.abel.2 x hx⟩
  have hB₁V : bOne z ≤ V := fun x hx => ⟨hA.B₂_le (hB₂.B₁_le hx),
    (GGFF.isElemAbelian_tor st.zs_pow st.zs_comm).2 x hx⟩
  have hVc : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x := fun x hx y hy => hA.comm x hx.1 y hy.1
  have hV3 : ∀ x ∈ V, x ^ 3 = 1 := fun x hx => hx.2
  have hbD : b ∈ dGrp b z := Subgroup.mem_sup_left (Subgroup.mem_zpowers b)
  have hVb : ∀ x ∈ V, b * x * b⁻¹ ∈ V := by
    intro x hx
    refine ⟨hA.nor b hbD x hx.1, ?_⟩
    rw [conj_pow, hx.2, mul_one, mul_inv_cancel]
  let Tv : V →* V := commEnd b V hVb hVc
  let Tb : B₂ →* B₂ := commEnd b B₂ hB₂.b_nor (fun x hx y hy => hB₂.abel.comm hx hy)
  have hTvker : Tv.ker.map V.subtype = bOne z := by
    apply le_antisymm
    · intro x hx
      rw [Subgroup.mem_map] at hx
      rcases hx with ⟨y, hy, hyx⟩
      rw [← hyx]
      exact hA.cen_b y y.2.1 ((commEnd_mem_ker hVb hVc y).mp hy).symm
    · intro x hx
      rw [Subgroup.mem_map]
      refine ⟨⟨x, hB₁V hx⟩, ?_, rfl⟩
      rw [commEnd_mem_ker]
      exact hbc x (hB₁L hx)
  have hTbker : Tb.ker.map B₂.subtype = bOne z := by
    apply le_antisymm
    · intro x hx
      rw [Subgroup.mem_map] at hx
      rcases hx with ⟨y, hy, hyx⟩
      rw [← hyx]
      exact hB₂.fix y y.2
        (((commEnd_mem_ker hB₂.b_nor (fun x hx y hy => hB₂.abel.comm hx hy) y).mp hy).symm)
    · intro x hx
      rw [Subgroup.mem_map]
      refine ⟨⟨x, hB₂.B₁_le hx⟩, ?_, rfl⟩
      rw [commEnd_mem_ker]
      exact hbc x (hB₁L hx)
  have hTbrange : Tb.range.map B₂.subtype = bOne z := by
    have hle : Tb.range.map B₂.subtype ≤ bOne z := by
      intro x hx
      rw [Subgroup.mem_map] at hx
      rcases hx with ⟨y, hy, hyx⟩
      rw [MonoidHom.mem_range] at hy
      rcases hy with ⟨w, rfl⟩
      rw [← hyx]
      exact hB₂.comm w w.2
    have hker_card : Nat.card Tb.ker = 27 := by
      rw [← Subgroup.card_map_of_injective B₂.subtype_injective, hTbker]
      exact st.card_torG
    have hrange_card : Nat.card (Tb.range.map B₂.subtype) = 27 := by
      have hmain := Subgroup.card_ker_mul_card_range Tb
      rw [hker_card, hB₂.card, show (3 : ℕ) ^ 6 = 729 by norm_num] at hmain
      have h2 : Nat.card Tb.range = 27 := by omega
      rw [Subgroup.card_map_of_injective B₂.subtype_injective, h2]
    exact Subgroup.eq_of_le_of_card_ge hle (by rw [st.card_torG, hrange_card])
  have hTv2ker : (Tv.comp Tv).ker.map V.subtype = B₂ := by
    have hB₂_le : B₂ ≤ (Tv.comp Tv).ker.map V.subtype := by
      intro x hx
      rw [Subgroup.mem_map]
      refine ⟨⟨x, hB₂V hx⟩, ?_, rfl⟩
      show Tv (Tv ⟨x, hB₂V hx⟩) = 1
      have hy : ((Tv ⟨x, hB₂V hx⟩ : V) : G) ∈ Tv.ker.map V.subtype := by
        rw [hTvker, commEnd_apply]
        exact hB₂.comm x hx
      rw [Subgroup.mem_map] at hy
      rcases hy with ⟨w, hw, hwv⟩
      have hweq : Tv ⟨x, hB₂V hx⟩ = w := Subtype.ext hwv.symm
      rw [hweq]; exact hw
    have hcount : Nat.card ((Tv.comp Tv).ker.map V.subtype) ≤ 729 := by
      let f : (Tv.comp Tv).ker →* V := Tv.comp (Tv.comp Tv).ker.subtype
      have hfk_le : f.ker.map (Tv.comp Tv).ker.subtype ≤ Tv.ker := by
        intro x hx
        rw [Subgroup.mem_map] at hx
        rcases hx with ⟨y, hy, hyx⟩
        change Tv x = 1
        rw [← hyx]
        exact hy
      have hfr_le : f.range ≤ Tv.ker := by
        intro x hx
        rw [MonoidHom.mem_range] at hx
        rcases hx with ⟨y, rfl⟩
        change Tv (Tv (y : V)) = 1
        exact y.2
      have hker_card : Nat.card f.ker ≤ 27 := by
        calc Nat.card f.ker = Nat.card (f.ker.map (Tv.comp Tv).ker.subtype) :=
              (Subgroup.card_map_of_injective (Tv.comp Tv).ker.subtype_injective).symm
          _ ≤ Nat.card Tv.ker := Subgroup.card_le_of_le hfk_le
          _ = 27 := by
              rw [← Subgroup.card_map_of_injective V.subtype_injective, hTvker]
              exact st.card_torG
      have hrange_card : Nat.card f.range ≤ 27 := by
        calc Nat.card f.range ≤ Nat.card Tv.ker := Subgroup.card_le_of_le hfr_le
          _ = 27 := by
              rw [← Subgroup.card_map_of_injective V.subtype_injective, hTvker]
              exact st.card_torG
      have hmain := Subgroup.card_ker_mul_card_range f
      calc Nat.card ((Tv.comp Tv).ker.map V.subtype) = Nat.card (Tv.comp Tv).ker :=
            Subgroup.card_map_of_injective V.subtype_injective
        _ = Nat.card f.ker * Nat.card f.range := hmain.symm
        _ ≤ 27 * 27 := Nat.mul_le_mul hker_card hrange_card
        _ = 729 := by norm_num
    have hcardB : Nat.card ((Tv.comp Tv).ker.map V.subtype) ≤ Nat.card B₂ :=
      hcount.trans (le_of_eq (by rw [hB₂.card]; norm_num))
    exact (Subgroup.eq_of_le_of_card_ge hB₂_le hcardB).symm
  obtain ⟨τ, ι₁, ι₂, ι₃, σ₁₂, σ₂₃, γ, hmemL, hmono, hirr⟩ := exists_mono_irreducible h
  have hι₁L : ι₁ ∈ L := hmemL ι₁ (by simp)
  have hι₁sqL : ι₁ ^ 2 ∈ L := L.pow_mem hι₁L 2
  have hb₁_ne : GGFF.zs z 0 ≠ 1 := by
    intro h1
    exact st.model.z_ne_one 0 (Subtype.ext (by simpa [GGFF.zs] using h1))
  have hφ0 : MulAut.conj ι₁ (GGFF.zs z 0) = (GGFF.zs z 0)⁻¹ := by
    rw [MulAut.conj_apply]; exact hmono.s₁.1
  have hφ0inv : MulAut.conj ι₁ ((GGFF.zs z 0)⁻¹) = GGFF.zs z 0 := by
    rw [map_inv, hφ0, inv_inv]
  have hφ1 : MulAut.conj ι₁ (GGFF.zs z 1) = GGFF.zs z 1 := by
    rw [MulAut.conj_apply]; exact hmono.s₁.2.1
  have hφ2 : MulAut.conj ι₁ (GGFF.zs z 2) = GGFF.zs z 2 := by
    rw [MulAut.conj_apply]; exact hmono.s₁.2.2
  have hφ2_0 : ((MulAut.conj ι₁) ^ 2) (GGFF.zs z 0) = GGFF.zs z 0 := by
    rw [pow_two, MulAut.mul_apply, hφ0, hφ0inv]
  have hφ2_1 : ((MulAut.conj ι₁) ^ 2) (GGFF.zs z 1) = GGFF.zs z 1 := by
    rw [pow_two, MulAut.mul_apply, hφ1, hφ1]
  have hφ2_2 : ((MulAut.conj ι₁) ^ 2) (GGFF.zs z 2) = GGFF.zs z 2 := by
    rw [pow_two, MulAut.mul_apply, hφ2, hφ2]
  have hsq0 : ι₁ ^ 2 * GGFF.zs z 0 = GGFF.zs z 0 * ι₁ ^ 2 := by
    have h : ι₁ ^ 2 * GGFF.zs z 0 * (ι₁ ^ 2)⁻¹ = GGFF.zs z 0 := by
      rw [conj_pow_apply, hφ2_0]
    calc ι₁ ^ 2 * GGFF.zs z 0 = ι₁ ^ 2 * GGFF.zs z 0 * (ι₁ ^ 2)⁻¹ * ι₁ ^ 2 := by group
      _ = GGFF.zs z 0 * ι₁ ^ 2 := by rw [h]
  have hsq1 : ι₁ ^ 2 * GGFF.zs z 1 = GGFF.zs z 1 * ι₁ ^ 2 := by
    have h : ι₁ ^ 2 * GGFF.zs z 1 * (ι₁ ^ 2)⁻¹ = GGFF.zs z 1 := by
      rw [conj_pow_apply, hφ2_1]
    calc ι₁ ^ 2 * GGFF.zs z 1 = ι₁ ^ 2 * GGFF.zs z 1 * (ι₁ ^ 2)⁻¹ * ι₁ ^ 2 := by group
      _ = GGFF.zs z 1 * ι₁ ^ 2 := by rw [h]
  have hsq2 : ι₁ ^ 2 * GGFF.zs z 2 = GGFF.zs z 2 * ι₁ ^ 2 := by
    have h : ι₁ ^ 2 * GGFF.zs z 2 * (ι₁ ^ 2)⁻¹ = GGFF.zs z 2 := by
      rw [conj_pow_apply, hφ2_2]
    calc ι₁ ^ 2 * GGFF.zs z 2 = ι₁ ^ 2 * GGFF.zs z 2 * (ι₁ ^ 2)⁻¹ * ι₁ ^ 2 := by group
      _ = GGFF.zs z 2 * ι₁ ^ 2 := by rw [h]
  obtain ⟨v, hv⟩ := CFSG.StandardType.FF81.cen_of_model h.hypA.n_cases h.hypA.model h.model
    ⟨ι₁ ^ 2, hι₁sqL⟩ (fun i => by
      apply Subtype.ext
      fin_cases i
      · exact hsq0
      · exact hsq1
      · exact hsq2)
  have hι₁sq3 : (ι₁ ^ 2) ^ 3 = 1 := by
    have hv' : ι₁ ^ 2 = vecElt (GGFF.zs z) v := by
      have := congrArg Subtype.val hv
      rw [← GGFF.SettingCore.vecElt_zs] at this
      exact this
    rw [hv']
    exact (GGFF.isElemAbelian_tor st.zs_pow st.zs_comm).2 _ (GGFF.vecElt_mem_tor _ v)
  let t : G := ι₁ ^ 3
  have ht2 : t * t = 1 := by
    change ι₁ ^ 3 * ι₁ ^ 3 = 1
    have h : ι₁ ^ 3 * ι₁ ^ 3 = (ι₁ ^ 2) ^ 3 := by
      rw [← pow_add, ← pow_mul]
    exact h.trans hι₁sq3
  have htL : t ∈ L := L.pow_mem hι₁L 3
  have htb : t * b = b * t := (hbc t htL).symm
  have hφ2_0inv : ((MulAut.conj ι₁) ^ 2) ((GGFF.zs z 0)⁻¹) = (GGFF.zs z 0)⁻¹ := by
    rw [pow_two, MulAut.mul_apply, hφ0inv, hφ0]
  have ht1 : t * GGFF.zs z 0 * t⁻¹ = (GGFF.zs z 0)⁻¹ := by
    change ι₁ ^ 3 * GGFF.zs z 0 * (ι₁ ^ 3)⁻¹ = (GGFF.zs z 0)⁻¹
    rw [conj_pow_apply]
    rw [show (MulAut.conj ι₁) ^ 3 = (MulAut.conj ι₁) ^ 2 * MulAut.conj ι₁ by rw [pow_succ]]
    rw [MulAut.mul_apply, hφ0, hφ2_0inv]
  have ht2' : t * GGFF.zs z 1 * t⁻¹ = GGFF.zs z 1 := by
    change ι₁ ^ 3 * GGFF.zs z 1 * (ι₁ ^ 3)⁻¹ = GGFF.zs z 1
    rw [conj_pow_apply]
    rw [show (MulAut.conj ι₁) ^ 3 = (MulAut.conj ι₁) ^ 2 * MulAut.conj ι₁ by rw [pow_succ]]
    rw [MulAut.mul_apply, hφ1, hφ2_1]
  have ht3' : t * GGFF.zs z 2 * t⁻¹ = GGFF.zs z 2 := by
    change ι₁ ^ 3 * GGFF.zs z 2 * (ι₁ ^ 3)⁻¹ = GGFF.zs z 2
    rw [conj_pow_apply]
    rw [show (MulAut.conj ι₁) ^ 3 = (MulAut.conj ι₁) ^ 2 * MulAut.conj ι₁ by rw [pow_succ]]
    rw [MulAut.mul_apply, hφ2, hφ2_2]
  have htne : t ≠ 1 := by
    intro h1
    have hb1inv : (GGFF.zs z 0)⁻¹ = GGFF.zs z 0 := by rw [← ht1, h1]; group
    have hb1sq : GGFF.zs z 0 * GGFF.zs z 0 = 1 := by
      nth_rewrite 2 [← hb1inv]
      exact mul_inv_cancel _
    have hb1one : GGFF.zs z 0 = 1 := by
      calc GGFF.zs z 0 = (GGFF.zs z 0) ^ 3 * (GGFF.zs z 0 * GGFF.zs z 0)⁻¹ := by
            rw [pow_succ, pow_two]; group
        _ = 1 := by rw [st.zs_pow 0, hb1sq, inv_one, mul_one]
    exact hb₁_ne hb1one
  have nor_of_conj : ∀ g : G,
      (∀ i, g * GGFF.zs z i * g⁻¹ ∈
        Subgroup.closure {GGFF.zs z 0, GGFF.zs z 1, GGFF.zs z 2}) →
      g ∈ Subgroup.normalizer ((bOne z : Subgroup G) : Set G) := by
    intro g hg
    change g ∈ Subgroup.normalizer ((GGFF.tor (GGFF.zs z) : Subgroup G) : Set G)
    rw [GGFF.SettingCore.tor_eq_closure z]
    exact GGFF.mem_nor_of_closure (fun s hs => by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
      rcases hs with rfl | rfl | rfl
      · exact hg 0
      · exact hg 1
      · exact hg 2)
  have gen_mem : ∀ i, GGFF.zs z i ∈
      Subgroup.closure {GGFF.zs z 0, GGFF.zs z 1, GGFF.zs z 2} := fun i =>
    Subgroup.subset_closure (by fin_cases i <;> simp)
  have gen_inv_mem : ∀ i, (GGFF.zs z i)⁻¹ ∈
      Subgroup.closure {GGFF.zs z 0, GGFF.zs z 1, GGFF.zs z 2} := fun i =>
    Subgroup.inv_mem _ (gen_mem i)
  have htN : t ∈ Subgroup.normalizer ((bOne z : Subgroup G) : Set G) :=
    nor_of_conj t (fun i => by
      fin_cases i
      · change t * GGFF.zs z 0 * t⁻¹ ∈
          Subgroup.closure {GGFF.zs z 0, GGFF.zs z 1, GGFF.zs z 2}
        rw [ht1]; exact gen_inv_mem 0
      · change t * GGFF.zs z 1 * t⁻¹ ∈
          Subgroup.closure {GGFF.zs z 0, GGFF.zs z 1, GGFF.zs z 2}
        rw [ht2']; exact gen_mem 1
      · change t * GGFF.zs z 2 * t⁻¹ ∈
          Subgroup.closure {GGFF.zs z 0, GGFF.zs z 1, GGFF.zs z 2}
        rw [ht3']; exact gen_mem 2)
  have htd : t ∈ dGrp b z := Subgroup.mem_sup_right ⟨htL, htN⟩
  have hVt : ∀ x ∈ V, t * x * t⁻¹ ∈ V := by
    intro x hx
    refine ⟨hA.nor t htd x hx.1, ?_⟩
    rw [conj_pow, hx.2, mul_one, mul_inv_cancel]
  have hB₂t : ∀ x ∈ B₂, t * x * t⁻¹ ∈ B₂ :=
    fun x hx => hB₂.D_nor t ⟨htL, htN⟩ x hx
  have hHinv : ∀ g ∈ ({ι₁, ι₂, ι₃, σ₁₂, σ₂₃, γ} : Set G),
      ∀ y ∈ (Tv.comp Tv).range.map V.subtype, g * y * g⁻¹ ∈
        (Tv.comp Tv).range.map V.subtype := by
    intro g hg y hy
    have hgL : g ∈ L := by
      apply hmemL g
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg ⊢
      tauto
    have hgb : g * b = b * g := (hbc g hgL).symm
    have hgnor : ∀ x ∈ V, g * x * g⁻¹ ∈ V := by
      intro x hx
      have hgd : g ∈ dGrp b z := by
        apply Subgroup.mem_sup_right
        refine ⟨hgL, ?_⟩
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
        rcases hg with h | h | h | h | h | h
        · rw [h]; apply nor_of_conj ι₁
          intro i; fin_cases i
          · change ι₁ * GGFF.zs z 0 * ι₁⁻¹ ∈
              Subgroup.closure {GGFF.zs z 0, GGFF.zs z 1, GGFF.zs z 2}
            rw [hmono.s₁.1]; exact gen_inv_mem 0
          · change ι₁ * GGFF.zs z 1 * ι₁⁻¹ ∈
              Subgroup.closure {GGFF.zs z 0, GGFF.zs z 1, GGFF.zs z 2}
            rw [hmono.s₁.2.1]; exact gen_mem 1
          · change ι₁ * GGFF.zs z 2 * ι₁⁻¹ ∈
              Subgroup.closure {GGFF.zs z 0, GGFF.zs z 1, GGFF.zs z 2}
            rw [hmono.s₁.2.2]; exact gen_mem 2
        · rw [h]; apply nor_of_conj ι₂
          intro i; fin_cases i
          · change ι₂ * GGFF.zs z 0 * ι₂⁻¹ ∈
              Subgroup.closure {GGFF.zs z 0, GGFF.zs z 1, GGFF.zs z 2}
            rw [hmono.s₂.1]; exact gen_mem 0
          · change ι₂ * GGFF.zs z 1 * ι₂⁻¹ ∈
              Subgroup.closure {GGFF.zs z 0, GGFF.zs z 1, GGFF.zs z 2}
            rw [hmono.s₂.2.1]; exact gen_inv_mem 1
          · change ι₂ * GGFF.zs z 2 * ι₂⁻¹ ∈
              Subgroup.closure {GGFF.zs z 0, GGFF.zs z 1, GGFF.zs z 2}
            rw [hmono.s₂.2.2]; exact gen_mem 2
        · rw [h]; apply nor_of_conj ι₃
          intro i; fin_cases i
          · change ι₃ * GGFF.zs z 0 * ι₃⁻¹ ∈
              Subgroup.closure {GGFF.zs z 0, GGFF.zs z 1, GGFF.zs z 2}
            rw [hmono.s₃.1]; exact gen_mem 0
          · change ι₃ * GGFF.zs z 1 * ι₃⁻¹ ∈
              Subgroup.closure {GGFF.zs z 0, GGFF.zs z 1, GGFF.zs z 2}
            rw [hmono.s₃.2.1]; exact gen_mem 1
          · change ι₃ * GGFF.zs z 2 * ι₃⁻¹ ∈
              Subgroup.closure {GGFF.zs z 0, GGFF.zs z 1, GGFF.zs z 2}
            rw [hmono.s₃.2.2]; exact gen_inv_mem 2
        · rw [h]; apply nor_of_conj σ₁₂
          intro i; fin_cases i
          · change σ₁₂ * GGFF.zs z 0 * σ₁₂⁻¹ ∈
              Subgroup.closure {GGFF.zs z 0, GGFF.zs z 1, GGFF.zs z 2}
            rw [hmono.p₁₂.1]; exact gen_mem 1
          · change σ₁₂ * GGFF.zs z 1 * σ₁₂⁻¹ ∈
              Subgroup.closure {GGFF.zs z 0, GGFF.zs z 1, GGFF.zs z 2}
            rw [hmono.p₁₂.2.1]; exact gen_mem 0
          · change σ₁₂ * GGFF.zs z 2 * σ₁₂⁻¹ ∈
              Subgroup.closure {GGFF.zs z 0, GGFF.zs z 1, GGFF.zs z 2}
            rw [hmono.p₁₂.2.2]; exact gen_mem 2
        · rw [h]; apply nor_of_conj σ₂₃
          intro i; fin_cases i
          · change σ₂₃ * GGFF.zs z 0 * σ₂₃⁻¹ ∈
              Subgroup.closure {GGFF.zs z 0, GGFF.zs z 1, GGFF.zs z 2}
            rw [hmono.p₂₃.1]; exact gen_mem 0
          · change σ₂₃ * GGFF.zs z 1 * σ₂₃⁻¹ ∈
              Subgroup.closure {GGFF.zs z 0, GGFF.zs z 1, GGFF.zs z 2}
            rw [hmono.p₂₃.2.1]; exact gen_mem 2
          · change σ₂₃ * GGFF.zs z 2 * σ₂₃⁻¹ ∈
              Subgroup.closure {GGFF.zs z 0, GGFF.zs z 1, GGFF.zs z 2}
            rw [hmono.p₂₃.2.2]; exact gen_mem 1
        · rw [h]; apply nor_of_conj γ
          intro i; fin_cases i
          · change γ * GGFF.zs z 0 * γ⁻¹ ∈
              Subgroup.closure {GGFF.zs z 0, GGFF.zs z 1, GGFF.zs z 2}
            rw [hmono.cyc.1]; exact gen_mem 1
          · change γ * GGFF.zs z 1 * γ⁻¹ ∈
              Subgroup.closure {GGFF.zs z 0, GGFF.zs z 1, GGFF.zs z 2}
            rw [hmono.cyc.2.1]; exact gen_mem 2
          · change γ * GGFF.zs z 2 * γ⁻¹ ∈
              Subgroup.closure {GGFF.zs z 0, GGFF.zs z 1, GGFF.zs z 2}
            rw [hmono.cyc.2.2]; exact gen_mem 0
      exact ⟨hA.nor g hgd x hx.1, by rw [conj_pow, hx.2, mul_one, mul_inv_cancel]⟩
    rw [Subgroup.mem_map] at hy ⊢
    rcases hy with ⟨w, hw, hwy⟩
    rw [MonoidHom.mem_range] at hw
    rcases hw with ⟨u, rfl⟩
    rw [← hwy]
    refine ⟨Tv (Tv ⟨g * (u : G) * g⁻¹, hgnor u u.2⟩), ?_, ?_⟩
    · rw [MonoidHom.mem_range]
      exact ⟨⟨g * (u : G) * g⁻¹, hgnor u u.2⟩, rfl⟩
    · change ((Tv (Tv ⟨g * (u : G) * g⁻¹, hgnor u u.2⟩) : V) : G) =
        g * ((Tv (Tv u) : V) : G) * g⁻¹
      rw [commEnd_equivariant hVb hVc hgnor hgb u]
      rw [commEnd_equivariant hVb hVc hgnor hgb (Tv u)]
  refine ⟨A, ⟨hA.le_cen, hA.isP, hA.max, hA.comm, hA.B₂_le, ?_, hA.nor⟩⟩
  intro x hxA hx3
  by_contra hxB₂
  have hxV : x ∈ V := ⟨hxA, hx3⟩
  have hxnotker : (⟨x, hxV⟩ : V) ∉ (Tv.comp Tv).ker := by
    intro hk
    apply hxB₂
    rw [← hTv2ker]
    rw [Subgroup.mem_map]
    exact ⟨⟨x, hxV⟩, hk, rfl⟩
  have hne : Tv (Tv ⟨x, hxV⟩) ≠ 1 := by
    intro h1
    exact hxnotker (MonoidHom.mem_ker.mpr h1)
  have hTv2range : (Tv.comp Tv).range.map V.subtype = bOne z := by
    have hHle : (Tv.comp Tv).range.map V.subtype ≤ bOne z := by
      intro y hy
      rw [Subgroup.mem_map] at hy
      rcases hy with ⟨w, hw, hwy⟩
      rw [MonoidHom.mem_range] at hw
      rcases hw with ⟨u, rfl⟩
      rw [← hwy, ← hTvker, Subgroup.mem_map]
      refine ⟨Tv (Tv u), ?_, rfl⟩
      change Tv (Tv (Tv u)) = 1
      exact commEnd_cube hb3 hVb hVc hV3 u
    have hHle' : (Tv.comp Tv).range.map V.subtype ≤
        CFSG.RankThree.PartTwo.Sec21.FF81.Lift.BO (GGFF.zs z 0) (GGFF.zs z 1) (GGFF.zs z 2) :=
      hHle.trans (le_of_eq (GGFF.SettingCore.tor_eq_closure z))
    have hHne : (Tv.comp Tv).range.map V.subtype ≠ ⊥ := by
      intro hbot
      have hmem : ((Tv (Tv ⟨x, hxV⟩) : V) : G) ∈ (⊥ : Subgroup G) := by
        rw [← hbot]
        rw [Subgroup.mem_map]
        exact ⟨Tv (Tv ⟨x, hxV⟩), ⟨⟨x, hxV⟩, rfl⟩, rfl⟩
      rw [Subgroup.mem_bot] at hmem
      exact hne (Subtype.ext hmem)
    have hres := hirr ((Tv.comp Tv).range.map V.subtype) hHle' hHne hHinv
    exact hres.trans (GGFF.SettingCore.tor_eq_closure z).symm
  have hliftV := card_cen_eq_mul_card_cen_ker_range ht2 hVt hVc hV3 (Tv.comp Tv)
    (fun y => by
      rw [MonoidHom.comp_apply]
      rw [commEnd_equivariant hVb hVc hVt htb y]
      rw [commEnd_equivariant hVb hVc hVt htb (Tv y)]
      rfl)
  have hliftB := card_cen_eq_mul_card_cen_ker_range ht2 hB₂t
    (fun x hx y hy => hB₂.abel.comm hx hy) (fun x hx => hB₂.abel.2 x hx) Tb
    (fun y => commEnd_equivariant hB₂.b_nor (fun x hx y hy => hB₂.abel.comm hx hy) hB₂t htb y)
  rw [hTv2ker, hTv2range] at hliftV
  rw [hTbker, hTbrange] at hliftB
  have hVcard : Nat.card ↥(V ⊓ Subgroup.centralizer ({t} : Set G)) =
      Nat.card ↥(bOne z ⊓ Subgroup.centralizer ({t} : Set G)) ^ 3 := by
    rw [hliftV, hliftB]; ring
  have h9 : 9 ≤ Nat.card ↥(bOne z ⊓ Subgroup.centralizer ({t} : Set G)) := by
    have hcard9 : Nat.card (Fin 2 → ZMod 3) = 9 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card, Fintype.card_fin]
      norm_num
    rw [← hcard9]
    let e : (Fin 2 → ZMod 3) → ↥(bOne z ⊓ Subgroup.centralizer ({t} : Set G)) := fun p =>
      ⟨vecElt (GGFF.zs z) (wOf p),
        Subgroup.mem_inf.mpr ⟨GGFF.vecElt_mem_tor _ _, by
          rw [Subgroup.mem_centralizer_iff]
          intro s hs
          rw [Set.mem_singleton_iff] at hs
          subst hs
          have hfix : t * vecElt (GGFF.zs z) (wOf p) * t⁻¹ = vecElt (GGFF.zs z) (wOf p) := by
            simp only [vecElt, wOf_zero, wOf_one, wOf_two, ZMod.val_zero, pow_zero, one_mul]
            rw [show t * ((GGFF.zs z 1) ^ ((p 0)).val * (GGFF.zs z 2) ^ ((p 1)).val) * t⁻¹
                = (t * (GGFF.zs z 1) ^ ((p 0)).val * t⁻¹) *
                  (t * (GGFF.zs z 2) ^ ((p 1)).val * t⁻¹) by group]
            rw [← conj_pow, ← conj_pow, ht2', ht3']
          calc t * vecElt (GGFF.zs z) (wOf p) = t * vecElt (GGFF.zs z) (wOf p) * t⁻¹ * t := by group
            _ = vecElt (GGFF.zs z) (wOf p) * t := by rw [hfix]⟩⟩
    have he : Function.Injective e := by
      intro p q hpq
      have hv : wOf p = wOf q :=
        GGFF.vecElt_injective st.zs_pow st.zs_comm st.inj' (congrArg Subtype.val hpq)
      have h1 : (p 0) = (q 0) := by
        have := congrFun hv 1
        simpa using this
      have h2 : (p 1) = (q 1) := by
        have := congrFun hv 2
        simpa using this
      exact funext fun i => by fin_cases i <;> assumption
    exact Nat.card_le_card_of_injective e he
  have hge : 3 ^ 6 ≤ Nat.card ↥(V ⊓ Subgroup.centralizer ({t} : Set G)) := by
    rw [hVcard]
    calc (3 : ℕ) ^ 6 = 9 ^ 3 := by norm_num
      _ ≤ Nat.card ↥(bOne z ⊓ Subgroup.centralizer ({t} : Set G)) ^ 3 :=
          Nat.pow_le_pow_left h9 3
  have hEa : CFSG.Open.IsElemAbelian 3 (V ⊓ Subgroup.centralizer ({t} : Set G)) :=
    ⟨IsMulCommutative.of_comm (fun a b => Subtype.ext (hVc a a.2.1 b b.2.1)),
      fun y hy => hy.1.2⟩
  have hEnor : V ⊓ Subgroup.centralizer ({t} : Set G) ≤
      Subgroup.normalizer ((Subgroup.zpowers t : Subgroup G) : Set G) := by
    intro y hy
    have hyc : y ∈ Subgroup.centralizer ({t} : Set G) := hy.2
    apply Subgroup.centralizer_le_normalizer
    rw [Subgroup.mem_centralizer_iff] at hyc ⊢
    intro s hs
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hs
    exact (Commute.zpow_left (hyc t (Set.mem_singleton t)) k).eq
  have htord : orderOf t = 2 := orderOf_eq_prime (by rwa [pow_two]) htne
  have hT2 : IsPGroup 2 (Subgroup.zpowers t) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, htord]; norm_num)
  have hTne : Subgroup.zpowers t ≠ ⊥ := by
    intro h
    rw [Subgroup.zpowers_eq_bot] at h
    exact htne h
  have hle := card_le_of_normalizer_isPGroup_two h.hypA h.model hTne hT2 hEnor hEa
  have : ¬ (3 : ℕ) ^ 6 ≤ 3 ^ 4 := by norm_num
  exact this (le_trans hge hle)
end CFSG.StandardType.FF81.PropOne

end
