module

public import CFSG.Quasithin.SteinbergCDChiefFactorTools
public import CFSG.Quasithin.SteinbergBQStrictFixedSpaceThompson
public import CFSG.Quasithin.H13.A7SharedSolvableOvergroup
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.ReducedChar
public import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.C5Counting
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellNatSeed
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.WreathTransfer4

public section

open scoped Pointwise commutatorElement

namespace CFSG.Quasithin.SteinbergCD

open Subgroup CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup CFSG.QuasithinUnique.Setup.Campbell

variable {G : Type*} [Group G]

section Closure

variable {H X Y : Subgroup G}

theorem conj_mem_iSup_conj {h x : G} (hh : h ∈ H) (hx : x ∈ X) :
    h * x * h⁻¹ ∈ ⨆ (g : G) (_ : g ∈ H), X.map (MulAut.conj g).toMonoidHom :=
  (le_iSup₂ (f := fun (g : G) (_ : g ∈ H) => X.map (MulAut.conj g).toMonoidHom) h hh)
    ⟨x, hx, rfl⟩

theorem le_iSup_conj : X ≤ ⨆ (g : G) (_ : g ∈ H), X.map (MulAut.conj g).toMonoidHom :=
  fun x hx => by simpa using conj_mem_iSup_conj (H := H) H.one_mem hx

theorem iSup_conj_le_of_forall (h : ∀ g ∈ H, ∀ x ∈ X, g * x * g⁻¹ ∈ Y) :
    ⨆ (g : G) (_ : g ∈ H), X.map (MulAut.conj g).toMonoidHom ≤ Y :=
  iSup₂_le fun g hg => by
    rintro _ ⟨x, hx, rfl⟩
    exact h g hg x hx

theorem iSup_conj_le (hXY : X ≤ Y) (hHY : H ≤ normalizer (Y : Set G)) :
    ⨆ (g : G) (_ : g ∈ H), X.map (MulAut.conj g).toMonoidHom ≤ Y :=
  iSup_conj_le_of_forall fun _ hg x hx => (mem_normalizer_iff.mp (hHY hg) x).mp (hXY hx)

theorem le_normalizer_iSup_conj [Finite G] :
    H ≤ normalizer ((⨆ (g : G) (_ : g ∈ H), X.map (MulAut.conj g).toMonoidHom : Subgroup G) :
      Set G) := by
  apply le_normalizer_of_conj_mem_of_finite
  intro g hg y hy
  have hle : (⨆ (h : G) (_ : h ∈ H), X.map (MulAut.conj h).toMonoidHom).map
      (MulAut.conj g).toMonoidHom ≤ ⨆ (h : G) (_ : h ∈ H), X.map (MulAut.conj h).toMonoidHom := by
    rw [Subgroup.map_iSup]
    refine iSup_le fun h => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun hh => ?_
    rw [map_le_iff_le_comap]
    rintro _ ⟨z, hz, rfl⟩
    rw [mem_comap]
    have e : (MulAut.conj g).toMonoidHom ((MulAut.conj h).toMonoidHom z) =
        (g * h) * z * (g * h)⁻¹ := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rw [e]
    exact conj_mem_iSup_conj (H.mul_mem hg hh) hz
  exact hle ⟨y, hy, rfl⟩

end Closure

section Action

variable {V B : Subgroup G}

theorem exists_of_mem_map_normalizerMonoidHom {σ : MulAut ↥V}
    (hσ : σ ∈ (B.subgroupOf (normalizer (V : Set G))).map V.normalizerMonoidHom) :
    ∃ b ∈ B, ∀ v : ↥V, ((σ v : ↥V) : G) = b * v * b⁻¹ := by
  obtain ⟨b, hb, rfl⟩ := hσ
  exact ⟨b, hb, fun v => normalizerMonoidHom_apply_apply_coe V b v⟩

theorem mem_map_normalizerMonoidHom {b : G} (hb : b ∈ B) (hbN : b ∈ normalizer (V : Set G)) :
    V.normalizerMonoidHom ⟨b, hbN⟩ ∈
      (B.subgroupOf (normalizer (V : Set G))).map V.normalizerMonoidHom :=
  ⟨⟨b, hbN⟩, hb, rfl⟩

theorem normalizerMonoidHom_eq_one_iff {x : ↥(normalizer (V : Set G))} :
    V.normalizerMonoidHom x = 1 ↔ (x : G) ∈ centralizer (V : Set G) := by
  constructor
  · intro h
    rw [mem_centralizer_iff]
    intro v hv
    have h1 := congrArg (fun σ : MulAut ↥V => ((σ ⟨v, hv⟩ : ↥V) : G)) h
    simp only [normalizerMonoidHom_apply_apply_coe, MulAut.one_apply] at h1
    calc v * x = (x * v * (x : G)⁻¹) * x := by rw [h1]
      _ = x * v := by group
  · intro h
    refine MulEquiv.ext fun v => Subtype.ext ?_
    rw [normalizerMonoidHom_apply_apply_coe, MulAut.one_apply, ← mem_centralizer_iff.mp h v v.2,
      mul_inv_cancel_right]

theorem map_normalizerMonoidHom_eq_bot_iff (hBN : B ≤ normalizer (V : Set G)) :
    (B.subgroupOf (normalizer (V : Set G))).map V.normalizerMonoidHom = ⊥ ↔
      B ≤ centralizer (V : Set G) := by
  rw [Subgroup.map_eq_bot_iff]
  constructor
  · intro h b hb
    have hb' : (⟨b, hBN hb⟩ : ↥(normalizer (V : Set G))) ∈ B.subgroupOf _ := hb
    exact normalizerMonoidHom_eq_one_iff.mp (MonoidHom.mem_ker.mp (h hb'))
  · intro h x hx
    exact MonoidHom.mem_ker.mpr (normalizerMonoidHom_eq_one_iff.mpr (h hx))

theorem card_map_normalizerMonoidHom_mul [Finite G] (hBN : B ≤ normalizer (V : Set G)) :
    Nat.card ↥((B.subgroupOf (normalizer (V : Set G))).map V.normalizerMonoidHom) *
      Nat.card ↥(B ⊓ centralizer (V : Set G)) = Nat.card ↥B := by
  have h1 := Wreath.card_map_mul_card_inf_ker V.normalizerMonoidHom
    (B.subgroupOf (normalizer (V : Set G)))
  have h2 : Nat.card ↥(B.subgroupOf (normalizer (V : Set G))) = Nat.card ↥B :=
    Nat.card_congr (subgroupOfEquivOfLe hBN).toEquiv
  have h3 : B.subgroupOf (normalizer (V : Set G)) ⊓ V.normalizerMonoidHom.ker =
      (B ⊓ centralizer (V : Set G)).subgroupOf (normalizer (V : Set G)) := by
    ext x
    simp only [mem_inf, mem_subgroupOf, MonoidHom.mem_ker, normalizerMonoidHom_eq_one_iff]
  have h4 : Nat.card ↥((B ⊓ centralizer (V : Set G)).subgroupOf (normalizer (V : Set G))) =
      Nat.card ↥(B ⊓ centralizer (V : Set G)) :=
    Nat.card_congr (subgroupOfEquivOfLe (inf_le_left.trans hBN)).toEquiv
  rw [h3, h4, h2] at h1
  exact h1

theorem card_fixedPoints_map_normalizerMonoidHom (hBN : B ≤ normalizer (V : Set G)) :
    Nat.card ↥(FixedPoints.subgroup
        ↥((B.subgroupOf (normalizer (V : Set G))).map V.normalizerMonoidHom) ↥V) =
      Nat.card ↥(V ⊓ centralizer (B : Set G)) := by
  have key : ∀ v : ↥V, v ∈ FixedPoints.subgroup
      ↥((B.subgroupOf (normalizer (V : Set G))).map V.normalizerMonoidHom) ↥V ↔
        (v : G) ∈ centralizer (B : Set G) := by
    intro v
    rw [SteinbergBQ.mem_fixedPoints_subgroup_mulAut_iff, mem_centralizer_iff]
    constructor
    · intro h b hb
      have h1 := congrArg Subtype.val (h _ (mem_map_normalizerMonoidHom hb (hBN hb)))
      rw [normalizerMonoidHom_apply_apply_coe] at h1
      calc b * (v : G) = (b * v * b⁻¹) * b := by group
        _ = v * b := by rw [h1]
    · intro h σ hσ
      obtain ⟨b, hb, hσb⟩ := exists_of_mem_map_normalizerMonoidHom hσ
      apply Subtype.ext
      rw [hσb, h b hb, mul_inv_cancel_right]
  exact Nat.card_congr
    { toFun := fun v => ⟨((v : ↥V) : G), (v : ↥V).2, (key v).mp v.2⟩
      invFun := fun v => ⟨⟨v, v.2.1⟩, (key ⟨v, v.2.1⟩).mpr v.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

theorem card_dual_le_card_commutator_mul [Finite G] (hVe : CFSG.Open.IsElemAbelian 2 V)
    (hBN : B ≤ normalizer (V : Set G)) :
    Nat.card (↥V →* Multiplicative (ZMod 2)) ≤ Nat.card ↥⁅V, B⁆ *
      Nat.card {φ : ↥V →* Multiplicative (ZMod 2) //
        ∀ σ ∈ (B.subgroupOf (normalizer (V : Set G))).map V.normalizerMonoidHom,
          ∀ v, φ (σ v) = φ v} := by
  have hXV : ⁅V, B⁆ ≤ V := le_normalizer_iff_commutator_le_left.mp hBN
  have h1 := card_monoidHom_le_card_mul_card_ker (⁅V, B⁆.subgroupOf V)
  have h2 : Nat.card (↥(⁅V, B⁆.subgroupOf V) →* Multiplicative (ZMod 2)) ≤ Nat.card ↥⁅V, B⁆ := by
    rw [← Nat.card_congr (subgroupOfEquivOfLe hXV).toEquiv]
    have := hVe.1
    let _ : CommGroup ↥(⁅V, B⁆.subgroupOf V) :=
      { (inferInstance : Group ↥(⁅V, B⁆.subgroupOf V)) with
        mul_comm := fun a b => Subtype.ext (Subtype.ext (setLike_mul_comm (a : ↥V).2 (b : ↥V).2)) }
    exact card_monoidHom_le_of_sq_eq_one fun x =>
      Subtype.ext (Subtype.ext (by simpa using hVe.2 _ (x : ↥V).2))
  have hfix : ∀ φ : ↥V →* Multiplicative (ZMod 2), (∀ x ∈ ⁅V, B⁆.subgroupOf V, φ x = 1) →
      ∀ σ ∈ (B.subgroupOf (normalizer (V : Set G))).map V.normalizerMonoidHom,
        ∀ v, φ (σ v) = φ v := by
    intro φ hφ σ hσ v
    obtain ⟨b, hb, hσb⟩ := exists_of_mem_map_normalizerMonoidHom hσ
    have hx : ⁅b, (v : G)⁆ ∈ ⁅V, B⁆ := by
      rw [← commutatorElement_inv]
      exact inv_mem (commutator_mem_commutator v.2 hb)
    have e : σ v = ⟨⁅b, (v : G)⁆, hXV hx⟩ * v := Subtype.ext (by
      rw [hσb]
      show b * (v : G) * b⁻¹ = ⁅b, (v : G)⁆ * v
      rw [commutatorElement_def]
      group)
    rw [e, map_mul, hφ _ (show (⟨⁅b, (v : G)⁆, hXV hx⟩ : ↥V) ∈ ⁅V, B⁆.subgroupOf V from hx),
      one_mul]
  have h3 : Nat.card {φ : ↥V →* Multiplicative (ZMod 2) // ∀ x ∈ ⁅V, B⁆.subgroupOf V, φ x = 1} ≤
      Nat.card {φ : ↥V →* Multiplicative (ZMod 2) //
        ∀ σ ∈ (B.subgroupOf (normalizer (V : Set G))).map V.normalizerMonoidHom,
          ∀ v, φ (σ v) = φ v} := by
    have : Finite (↥V →* Multiplicative (ZMod 2)) := Finite.of_injective _ DFunLike.coe_injective
    refine Nat.card_le_card_of_injective (fun φ => ⟨φ.1, hfix φ.1 φ.2⟩) ?_
    intro φ ψ h
    exact Subtype.ext (Subtype.mk.inj h)
  calc Nat.card (↥V →* Multiplicative (ZMod 2))
      ≤ Nat.card (↥(⁅V, B⁆.subgroupOf V) →* Multiplicative (ZMod 2)) *
          Nat.card {φ : ↥V →* Multiplicative (ZMod 2) //
            ∀ x ∈ ⁅V, B⁆.subgroupOf V, φ x = 1} := h1
    _ ≤ _ := Nat.mul_le_mul h2 h3

end Action


section Strict

variable [Finite G] {T V B : Subgroup G}

omit [Finite G] in
theorem isElementaryAbelian_subgroupOf_of_isElemAbelian {A : Subgroup G}
    (hA : CFSG.Open.IsElemAbelian 2 A) (K : Subgroup G) :
    CFSG.IsElementaryAbelian 2 ↥(A.subgroupOf K) := by
  have := hA.1
  exact BlueprintB2.isElementaryAbelian_iff.mpr
    ⟨fun a ha b hb => Subtype.ext (setLike_mul_comm (mem_subgroupOf.mp ha) (mem_subgroupOf.mp hb)),
      fun a ha => Subtype.ext (by simpa using hA.2 _ ha)⟩

theorem le_centralizer_of_isMaxElemAbelian_of_strict {A : Subgroup G} (hVT : V ≤ T)
    (hTV : T ≤ normalizer (V : Set G)) (hVe : CFSG.Open.IsElemAbelian 2 V)
    (hstrict : ∀ E : Subgroup (MulAut ↥V),
      (∀ σ ∈ E, ∃ t ∈ T, ∀ v : ↥V, ((σ v : ↥V) : G) = t * v * t⁻¹) → E ≠ ⊥ →
        CFSG.IsElementaryAbelian 2 ↥E →
          Nat.card ↥E * Nat.card ↥(FixedPoints.subgroup ↥E ↥V) < Nat.card ↥V)
    (hA : IsMaxElemAbelian T A) : A ≤ centralizer (V : Set G) := by
  by_contra hAV
  have hAN : A ≤ normalizer (V : Set G) := hA.1.trans hTV
  have hEΓ : ∀ σ ∈ (A.subgroupOf (normalizer (V : Set G))).map V.normalizerMonoidHom,
      ∃ t ∈ T, ∀ v : ↥V, ((σ v : ↥V) : G) = t * v * t⁻¹ := fun σ hσ => by
    obtain ⟨b, hb, h⟩ := exists_of_mem_map_normalizerMonoidHom hσ
    exact ⟨b, hA.1 hb, h⟩
  have hE1 : (A.subgroupOf (normalizer (V : Set G))).map V.normalizerMonoidHom ≠ ⊥ := fun h =>
    hAV ((map_normalizerMonoidHom_eq_bot_iff hAN).mp h)
  have hEe := BlueprintB2.isElementaryAbelian_map
    (isElementaryAbelian_subgroupOf_of_isElemAbelian hA.2.1 (normalizer (V : Set G)))
    V.normalizerMonoidHom
  have h1 := hstrict _ hEΓ hE1 hEe
  rw [card_fixedPoints_map_normalizerMonoidHom hAN] at h1
  have h2 := card_map_normalizerMonoidHom_mul hAN
  have h3 := (action_inequality hA hVT hVe).2
  have hpos : 0 < Nat.card ↥(A ⊓ centralizer (V : Set G)) := Nat.card_pos
  rw [← h2] at h3
  have h4 : Nat.card ↥V ≤ Nat.card ↥((A.subgroupOf (normalizer (V : Set G))).map
      V.normalizerMonoidHom) * Nat.card ↥(V ⊓ centralizer (A : Set G)) := by
    refine Nat.le_of_mul_le_mul_right (h3.trans (le_of_eq ?_)) hpos
    ring
  omega

theorem le_centralizer_of_dual_strict (hVe : CFSG.Open.IsElemAbelian 2 V) (hBT : B ≤ T)
    (hTV : T ≤ normalizer (V : Set G))
    (hdual : ∀ E : Subgroup (MulAut ↥V),
      (∀ σ ∈ E, ∃ t ∈ T, ∀ v : ↥V, ((σ v : ↥V) : G) = t * v * t⁻¹) → E ≠ ⊥ →
        CFSG.IsElementaryAbelian 2 ↥E →
          Nat.card ↥E * Nat.card {φ : ↥V →* Multiplicative (ZMod 2) //
            ∀ σ ∈ E, ∀ v, φ (σ v) = φ v} < Nat.card (↥V →* Multiplicative (ZMod 2)))
    (hEe : CFSG.IsElementaryAbelian 2
      ↥((B.subgroupOf (normalizer (V : Set G))).map V.normalizerMonoidHom))
    (hcard : Nat.card ↥⁅V, B⁆ ≤
      Nat.card ↥((B.subgroupOf (normalizer (V : Set G))).map V.normalizerMonoidHom)) :
    B ≤ centralizer (V : Set G) := by
  by_contra hBV
  have hBN : B ≤ normalizer (V : Set G) := hBT.trans hTV
  have hEΓ : ∀ σ ∈ (B.subgroupOf (normalizer (V : Set G))).map V.normalizerMonoidHom,
      ∃ t ∈ T, ∀ v : ↥V, ((σ v : ↥V) : G) = t * v * t⁻¹ := fun σ hσ => by
    obtain ⟨b, hb, h⟩ := exists_of_mem_map_normalizerMonoidHom hσ
    exact ⟨b, hBT hb, h⟩
  have hE1 : (B.subgroupOf (normalizer (V : Set G))).map V.normalizerMonoidHom ≠ ⊥ := fun h =>
    hBV ((map_normalizerMonoidHom_eq_bot_iff hBN).mp h)
  have h1 := hdual _ hEΓ hE1 hEe
  have h2 := card_dual_le_card_commutator_mul hVe hBN
  have h3 := Nat.mul_le_mul_right (Nat.card {φ : ↥V →* Multiplicative (ZMod 2) //
    ∀ σ ∈ (B.subgroupOf (normalizer (V : Set G))).map V.normalizerMonoidHom,
      ∀ v, φ (σ v) = φ v}) hcard
  omega

end Strict

section Quadratic

variable {D : Subgroup G}

theorem conj_conj_comm_of_quadratic {q₁ q₂ x : G} (hD : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a)
    (hq₁ : q₁ * x * q₁⁻¹ * x⁻¹ ∈ D) (hq₂ : q₂ * x * q₂⁻¹ * x⁻¹ ∈ D)
    (hc₁ : ∀ d ∈ D, q₁ * d = d * q₁) (hc₂ : ∀ d ∈ D, q₂ * d = d * q₂) :
    q₁ * (q₂ * x * q₂⁻¹) * q₁⁻¹ = q₂ * (q₁ * x * q₁⁻¹) * q₂⁻¹ := by
  obtain ⟨d₁, hd₁, e₁⟩ : ∃ d₁ ∈ D, q₁ * x * q₁⁻¹ = d₁ * x := ⟨_, hq₁, by group⟩
  obtain ⟨d₂, hd₂, e₂⟩ : ∃ d₂ ∈ D, q₂ * x * q₂⁻¹ = d₂ * x := ⟨_, hq₂, by group⟩
  have f₁ : q₁ * d₂ * q₁⁻¹ = d₂ := by rw [hc₁ d₂ hd₂, mul_inv_cancel_right]
  have f₂ : q₂ * d₁ * q₂⁻¹ = d₁ := by rw [hc₂ d₁ hd₁, mul_inv_cancel_right]
  calc q₁ * (q₂ * x * q₂⁻¹) * q₁⁻¹ = (q₁ * d₂ * q₁⁻¹) * (q₁ * x * q₁⁻¹) := by rw [e₂]; group
    _ = d₂ * (d₁ * x) := by rw [f₁, e₁]
    _ = d₁ * (d₂ * x) := by rw [← mul_assoc, ← mul_assoc, hD d₂ hd₂ d₁ hd₁]
    _ = (q₂ * d₁ * q₂⁻¹) * (q₂ * x * q₂⁻¹) := by rw [f₂, e₂]
    _ = q₂ * (q₁ * x * q₁⁻¹) * q₂⁻¹ := by rw [e₁]; group

theorem conj_conj_eq_of_quadratic {q x : G} (hD2 : ∀ d ∈ D, d * d = 1)
    (hq : q * x * q⁻¹ * x⁻¹ ∈ D) (hc : ∀ d ∈ D, q * d = d * q) :
    q * (q * x * q⁻¹) * q⁻¹ = x := by
  obtain ⟨d, hd, e⟩ : ∃ d ∈ D, q * x * q⁻¹ = d * x := ⟨_, hq, by group⟩
  have f : q * d * q⁻¹ = d := by rw [hc d hd, mul_inv_cancel_right]
  calc q * (q * x * q⁻¹) * q⁻¹ = q * (d * x) * q⁻¹ := by rw [e]
    _ = (q * d * q⁻¹) * (q * x * q⁻¹) := by group
    _ = d * d * x := by rw [f, e, mul_assoc]
    _ = x := by rw [hD2 d hd, one_mul]

end Quadratic

theorem exists_subgroup_forall_commutator_mem_left [Finite G] {H U P C : Subgroup G}
    (hU : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a) (hHU : H ≤ normalizer (U : Set G))
    (hPU : P ≤ normalizer (U : Set G)) (hHP : H ≤ normalizer (P : Set G))
    (hHC : H ≤ normalizer (C : Set G)) :
    ∃ Z : Subgroup G, Z ≤ U ∧ H ≤ normalizer (Z : Set G) ∧
      ∀ u, u ∈ Z ↔ u ∈ U ∧ ∀ q ∈ P, ⁅u, q⁆ ∈ C := by
  have hcU : ∀ q ∈ P, ∀ u ∈ U, q * u * q⁻¹ ∈ U := fun q hq u hu =>
    (mem_normalizer_iff.mp (hPU hq) u).mp hu
  have hinv : ∀ q ∈ P, ∀ u ∈ U, ⁅u⁻¹, q⁆ = ⁅u, q⁆⁻¹ := by
    intro q hq u hu
    have h := commutatorElement_mul_of_mem hU (hcU q hq) hu (U.inv_mem hu)
    rw [mul_inv_cancel, commutatorElement_one_left] at h
    exact eq_inv_of_mul_eq_one_left h.symm
  let Z : Subgroup G :=
    { carrier := {u | u ∈ U ∧ ∀ q ∈ P, ⁅u, q⁆ ∈ C}
      one_mem' := ⟨U.one_mem, fun q _ => by rw [commutatorElement_one_left]; exact C.one_mem⟩
      mul_mem' := fun {a b} ha hb => ⟨U.mul_mem ha.1 hb.1, fun q hq => by
        rw [commutatorElement_mul_of_mem hU (hcU q hq) ha.1 hb.1]
        exact C.mul_mem (hb.2 q hq) (ha.2 q hq)⟩
      inv_mem' := fun {a} ha => ⟨U.inv_mem ha.1, fun q hq => by
        rw [hinv q hq a ha.1]
        exact C.inv_mem (ha.2 q hq)⟩ }
  refine ⟨Z, fun u hu => hu.1, le_normalizer_of_conj_mem_of_finite fun g hg u hu =>
    ⟨(mem_normalizer_iff.mp (hHU hg) u).mp hu.1, fun q hq => ?_⟩, fun u => Iff.rfl⟩
  have hq' : g⁻¹ * q * g ∈ P := by simpa using (mem_normalizer_iff.mp (hHP (H.inv_mem hg)) q).mp hq
  have e : ⁅g * u * g⁻¹, q⁆ = g * ⁅u, g⁻¹ * q * g⁆ * g⁻¹ := by
    simp only [commutatorElement_def]; group
  rw [e]
  exact (mem_normalizer_iff.mp (hHC hg) _).mp (hu.2 _ hq')


theorem iSup_conj_le_centralizer_of_single_chief_factor [Finite G] {H T K Q V U : Subgroup G}
    (hTH : T ≤ H) (hT2 : IsPGroup 2 T) (hTV : T ≤ normalizer (V : Set G))
    (hKH : K ≤ H) (hHK : H ≤ normalizer (K : Set G)) (hKT : H ≤ K ⊔ T)
    (hQT : Q ≤ T) (hHQ : H ≤ normalizer (Q : Set G))
    (hVQ : V ≤ Q) (hVe : CFSG.Open.IsElemAbelian 2 V) (hVH : ¬ H ≤ normalizer (V : Set G))
    (hU : U = ⨆ (h : G) (_ : h ∈ H), V.map (MulAut.conj h).toMonoidHom)
    (hUe : CFSG.Open.IsElemAbelian 2 U)
    (hP1 : ∀ W : Subgroup G, W ≤ U → H ≤ normalizer (W : Set G) → ⁅W, K⁆ ≠ ⊥ → ⁅U, K⁆ ≤ W)
    (hdual : ∀ E : Subgroup (MulAut ↥V),
      (∀ σ ∈ E, ∃ t ∈ T, ∀ v : ↥V, ((σ v : ↥V) : G) = t * v * t⁻¹) → E ≠ ⊥ →
        CFSG.IsElementaryAbelian 2 ↥E →
          Nat.card ↥E * Nat.card {φ : ↥V →* Multiplicative (ZMod 2) //
            ∀ σ ∈ E, ∀ v, φ (σ v) = φ v} < Nat.card (↥V →* Multiplicative (ZMod 2))) :
    ⨆ (h : G) (_ : h ∈ H), (T ⊓ centralizer (V : Set G) ⊓ Q).map (MulAut.conj h).toMonoidHom ≤
      centralizer (V : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q₀ := T ⊓ centralizer (V : Set G) ⊓ Q with hQ₀
  set Q₁ := ⨆ (h : G) (_ : h ∈ H), Q₀.map (MulAut.conj h).toMonoidHom with hQ₁
  have hVc : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := fun a ha b hb => by
    have := hVe.1
    exact setLike_mul_comm ha hb
  have hUc : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a := fun a ha b hb => by
    have := hUe.1
    exact setLike_mul_comm ha hb
  have hconj : ∀ {X : Subgroup G} {g : G}, g ∈ normalizer (X : Set G) → ∀ x ∈ X,
      g * x * g⁻¹ ∈ X := fun hg x hx => (mem_normalizer_iff.mp hg x).mp hx
  have hVT : V ≤ T := hVQ.trans hQT
  have hVQ₀ : V ≤ Q₀ := le_inf (le_inf hVT fun v hv =>
    mem_centralizer_iff.mpr fun w hw => hVc w hw v hv) hVQ
  have hQ₀Q₁ : Q₀ ≤ Q₁ := le_iSup_conj
  have hQ₁Q : Q₁ ≤ Q := iSup_conj_le inf_le_right hHQ
  have hHQ₁ : H ≤ normalizer (Q₁ : Set G) := le_normalizer_iSup_conj
  have hHU : H ≤ normalizer (U : Set G) := hU ▸ le_normalizer_iSup_conj
  have hVU : V ≤ U := hU ▸ le_iSup_conj
  have hUQ₁ : U ≤ Q₁ := hU ▸ iSup_conj_le_of_forall fun g hg x hx =>
    conj_mem_iSup_conj hg (hVQ₀ hx)
  have hQ₁T : Q₁ ≤ T := hQ₁Q.trans hQT
  have hQ₁2 : IsPGroup 2 Q₁ := hT2.to_le hQ₁T
  have hQ₁V : Q₁ ≤ normalizer (V : Set G) := hQ₁T.trans hTV
  have hQ₁U : Q₁ ≤ normalizer (U : Set G) := (hQ₁T.trans hTH).trans hHU
  have hIU : ⁅U, K⁆ ≤ U := le_normalizer_iff_commutator_le_left.mp (hKH.trans hHU)
  set D := V ⊓ centralizer (K : Set G) with hD
  have hKD : K ≤ normalizer (D : Set G) := by
    apply le_normalizer_of_conj_mem_of_finite
    intro k hk d hd
    rw [mem_centralizer_iff.mp hd.2 k hk, mul_inv_cancel_right]
    exact hd
  have hHD : H ≤ normalizer (D : Set G) := hKT.trans (sup_le hKD
    (le_normalizer_inf_of_le hTV fun t ht =>
      mem_normalizer_centralizer_of_mem_normalizer (hHK (hTH ht))))
  have hQ₁D : Q₁ ≤ centralizer (D : Set G) := by
    refine iSup_conj_le_of_forall fun g hg x hx => ?_
    rw [mem_centralizer_iff]
    intro d hd
    have hd' : g⁻¹ * d * g ∈ D := by simpa using hconj (hHD (H.inv_mem hg)) d hd
    have hxd : (g⁻¹ * d * g) * x = x * (g⁻¹ * d * g) := mem_centralizer_iff.mp hx.1.2 _ hd'.1
    calc d * (g * x * g⁻¹) = g * ((g⁻¹ * d * g) * x) * g⁻¹ := by group
      _ = g * (x * (g⁻¹ * d * g)) * g⁻¹ := by rw [hxd]
      _ = g * x * g⁻¹ * d := by group
  have hUVI : U ≤ V ⊔ ⁅U, K⁆ := by
    refine hU.le.trans (iSup_conj_le_of_forall fun g hg v hv => ?_)
    obtain ⟨k, hk, t, ht, rfl⟩ := Layer.mem_sup_mul (hTH.trans hHK) (hKT hg)
    have hv' : t * v * t⁻¹ ∈ V := hconj (hTV ht) v hv
    have e : k * t * v * (k * t)⁻¹ = ⁅t * v * t⁻¹, k⁆⁻¹ * (t * v * t⁻¹) := by
      rw [commutatorElement_def]; group
    rw [e]
    exact mul_mem (mem_sup_right (inv_mem (commutator_mem_commutator (hVU hv') hk)))
      (mem_sup_left hv')
  have hVD : ¬ V ≤ D := by
    intro hle
    apply hVH
    refine hKT.trans (sup_le ?_ hTV)
    apply le_normalizer_of_conj_mem_of_finite
    intro k hk v hv
    rw [mem_centralizer_iff.mp (hle hv).2 k hk, mul_inv_cancel_right]
    exact hv
  have hclaim : ⁅V, Q₁⁆ ≤ D := by
    by_contra hne
    have hWU : ⁅U, Q₁⁆ ≤ U := le_normalizer_iff_commutator_le_left.mp hQ₁U
    have hHW : H ≤ normalizer ((⁅U, Q₁⁆ : Subgroup G) : Set G) :=
      le_normalizer_commutator_of_le hHU hHQ₁
    have hWK : ⁅⁅U, Q₁⁆, K⁆ ≠ ⊥ := by
      intro h0
      apply hne
      exact le_inf (le_normalizer_iff_commutator_le_left.mp hQ₁V)
        ((commutator_mono hVU le_rfl).trans (commutator_eq_bot_iff_le_centralizer.mp h0))
    have hI := hP1 _ hWU hHW hWK
    have hUV : U ≤ V := le_of_le_sup_commutator hQ₁2 hUQ₁ hUc hVU hQ₁V hQ₁U
      (hUVI.trans (sup_le_sup_left hI _))
    apply hVH
    rw [← le_antisymm hUV hVU]
    exact hHU
  obtain ⟨v, hvV, hvD, hvT⟩ := exists_mem_not_mem_forall_commutator_mem hT2 hVT hTV hVD
  have hvK : v ∉ centralizer (K : Set G) := fun h => hvD ⟨hvV, h⟩
  have hvq : ∀ q ∈ Q₁, ⁅v, q⁆ ∈ D := fun q hq => hclaim (commutator_mem_commutator hvV hq)
  let ψ : ↥Q₁ →* G := MonoidHom.mk' (fun q => ⁅v, (q : G)⁆) (fun q₁ q₂ => by
    have h1 : (q₁ : G) * ⁅v, (q₂ : G)⁆ * (q₁ : G)⁻¹ = ⁅v, (q₂ : G)⁆ := by
      rw [← mem_centralizer_iff.mp (hQ₁D q₁.2) _ (hvq _ q₂.2), mul_inv_cancel_right]
    calc ⁅v, ((q₁ * q₂ : ↥Q₁) : G)⁆ = ⁅v, (q₁ : G)⁆ * ((q₁ : G) * ⁅v, (q₂ : G)⁆ * (q₁ : G)⁻¹) := by
          push_cast
          simp only [commutatorElement_def]
          group
      _ = ⁅v, (q₁ : G)⁆ * ⁅v, (q₂ : G)⁆ := by rw [h1])
  have hψ : ∀ q : ↥Q₁, ψ q = ⁅v, (q : G)⁆ := fun _ => rfl
  have hCvD : ψ.range ≤ D := by
    rintro _ ⟨q, rfl⟩
    exact hvq q q.2
  have hHCv : H ≤ normalizer (ψ.range : Set G) := by
    refine hKT.trans (sup_le ?_ ?_)
    · apply le_normalizer_of_conj_mem_of_finite
      intro k hk c hc
      rw [mem_centralizer_iff.mp (hCvD hc).2 k hk, mul_inv_cancel_right]
      exact hc
    · apply le_normalizer_of_conj_mem_of_finite
      intro t ht c hc
      obtain ⟨q, rfl⟩ := hc
      have htq : t * (q : G) * t⁻¹ ∈ Q₁ := hconj (hHQ₁ (hTH ht)) q q.2
      refine ⟨⟨t * q * t⁻¹, htq⟩, ?_⟩
      rw [hψ, hψ]
      have hd := hvT t ht
      have e1 : t * v * t⁻¹ = ⁅v, t⁆⁻¹ * v := by rw [commutatorElement_def]; group
      have hdq : (t * (q : G) * t⁻¹) * ⁅v, t⁆ * (t * (q : G) * t⁻¹)⁻¹ = ⁅v, t⁆ := by
        rw [← mem_centralizer_iff.mp (hQ₁D htq) _ hd, mul_inv_cancel_right]
      have hcomm : ⁅v, t⁆⁻¹ * ⁅v, t * (q : G) * t⁻¹⁆ = ⁅v, t * (q : G) * t⁻¹⁆ * ⁅v, t⁆⁻¹ :=
        hVc _ (inv_mem hd.1) _ (hvq _ htq).1
      show ⁅v, t * (q : G) * t⁻¹⁆ = t * ⁅v, (q : G)⁆ * t⁻¹
      calc ⁅v, t * (q : G) * t⁻¹⁆ = ⁅v, t⁆⁻¹ * ⁅v, t * (q : G) * t⁻¹⁆ * ⁅v, t⁆ := by
            rw [hcomm, inv_mul_cancel_right]
        _ = ⁅v, t⁆⁻¹ * ⁅v, t * (q : G) * t⁻¹⁆ *
              ((t * (q : G) * t⁻¹) * ⁅v, t⁆ * (t * (q : G) * t⁻¹)⁻¹) := by rw [hdq]
        _ = ⁅⁅v, t⁆⁻¹ * v, t * (q : G) * t⁻¹⁆ := by simp only [commutatorElement_def]; group
        _ = ⁅t * v * t⁻¹, t * (q : G) * t⁻¹⁆ := by rw [e1]
        _ = t * ⁅v, (q : G)⁆ * t⁻¹ := by simp only [commutatorElement_def]; group
  obtain ⟨Z, hZU, hHZ, hZ⟩ := exists_subgroup_forall_commutator_mem_left hUc hHU hQ₁U hHQ₁ hHCv
  have hvZ : v ∈ Z := (hZ v).mpr ⟨hVU hvV, fun q hq => ⟨⟨q, hq⟩, rfl⟩⟩
  have hZK : ⁅Z, K⁆ ≠ ⊥ := fun h0 => hvK (commutator_eq_bot_iff_le_centralizer.mp h0 hvZ)
  have hIZ := hP1 Z hZU hHZ hZK
  obtain ⟨Y, hHY, hY⟩ := exists_subgroup_forall_commutator_mem (A := U) hHU hHCv
  have hQ₀Y : Q₀ ≤ Y := by
    intro q hq
    have hqH : q ∈ H := hTH hq.1.1
    refine (hY q).mpr ⟨hqH, fun u hu => ?_⟩
    have hcomm : ∀ a ∈ V, ∀ b ∈ ⁅U, K⁆, a * b = b * a := fun a ha b hb =>
      hUc a (hVU ha) b (hIU hb)
    have hu' : u ∈ ((V ⊔ ⁅U, K⁆ : Subgroup G) : Set G) := hUVI hu
    rw [(CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ hcomm).2] at hu'
    obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.mp hu'
    rw [commutatorElement_mul_of_mem hUc (fun x hx => hconj (hHU hqH) x hx) (hVU ha) (hIU hb),
      commutatorElement_eq_one_iff_mul_comm.mpr (mem_centralizer_iff.mp hq.1.2 a ha), mul_one]
    exact ((hZ b).mp (hIZ hb)).2 q (hQ₀Q₁ hq)
  have hQ₁Y : Q₁ ≤ Y := iSup_conj_le hQ₀Y hHY
  have hUQ₁Cv : ⁅U, Q₁⁆ ≤ ψ.range := by
    rw [commutator_le]
    intro u hu q hq
    exact ((hY q).mp (hQ₁Y hq)).2 u hu
  have hD2 : ∀ d ∈ D, d * d = 1 := fun d hd => by rw [← pow_two]; exact hVe.2 d hd.1
  have hDc : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a := fun a ha b hb => hVc a ha.1 b hb.1
  have hqx : ∀ q ∈ Q₁, ∀ x ∈ V, q * x * q⁻¹ * x⁻¹ ∈ D := fun q hq x hx => by
    have h1 : q * x * q⁻¹ * x⁻¹ = ⁅x, q⁆⁻¹ := by rw [commutatorElement_def]; group
    rw [h1]
    exact inv_mem (hclaim (commutator_mem_commutator hx hq))
  have hqD : ∀ q ∈ Q₁, ∀ d ∈ D, q * d = d * q := fun q hq d hd =>
    (mem_centralizer_iff.mp (hQ₁D hq) d hd).symm
  have hEe : CFSG.IsElementaryAbelian 2
      ↥((Q₁.subgroupOf (normalizer (V : Set G))).map V.normalizerMonoidHom) := by
    refine BlueprintB2.isElementaryAbelian_iff.mpr ⟨fun a ha b hb => ?_, fun a ha => ?_⟩
    · obtain ⟨q₁, hq₁, ha'⟩ := exists_of_mem_map_normalizerMonoidHom ha
      obtain ⟨q₂, hq₂, hb'⟩ := exists_of_mem_map_normalizerMonoidHom hb
      refine MulEquiv.ext fun x => Subtype.ext ?_
      rw [MulAut.mul_apply, MulAut.mul_apply, ha' (b x), hb' x, hb' (a x), ha' x]
      exact conj_conj_comm_of_quadratic hDc (hqx q₁ hq₁ x x.2) (hqx q₂ hq₂ x x.2)
        (hqD q₁ hq₁) (hqD q₂ hq₂)
    · obtain ⟨q, hq, ha'⟩ := exists_of_mem_map_normalizerMonoidHom ha
      refine MulEquiv.ext fun x => Subtype.ext ?_
      rw [pow_two, MulAut.mul_apply, ha', ha', MulAut.one_apply]
      exact conj_conj_eq_of_quadratic hD2 (hqx q hq x x.2) (hqD q hq)
  have hcardE : Nat.card ↥ψ.range ≤
      Nat.card ↥((Q₁.subgroupOf (normalizer (V : Set G))).map V.normalizerMonoidHom) := by
    have hv' : ((⟨v, hvV⟩ : ↥V) : G) = v := rfl
    have hf : ∀ σ : ↥((Q₁.subgroupOf (normalizer (V : Set G))).map V.normalizerMonoidHom),
        v * ((σ.1 ⟨v, hvV⟩ : ↥V) : G)⁻¹ ∈ ψ.range := by
      intro σ
      obtain ⟨q, hq, hσq⟩ := exists_of_mem_map_normalizerMonoidHom σ.2
      refine ⟨⟨q, hq⟩, ?_⟩
      rw [hψ, hσq, hv', commutatorElement_def]
      group
    refine Nat.card_le_card_of_surjective (fun σ => ⟨_, hf σ⟩) ?_
    rintro ⟨_, ⟨q, rfl⟩⟩
    refine ⟨⟨V.normalizerMonoidHom ⟨q, hQ₁V q.2⟩, mem_map_normalizerMonoidHom q.2 (hQ₁V q.2)⟩,
      Subtype.ext ?_⟩
    show v * ((V.normalizerMonoidHom ⟨q, hQ₁V q.2⟩ ⟨v, hvV⟩ : ↥V) : G)⁻¹ = ψ q
    rw [normalizerMonoidHom_apply_apply_coe, hψ, hv', commutatorElement_def]
    group
  have hVQ₁ : Nat.card ↥⁅V, Q₁⁆ ≤ Nat.card ↥ψ.range :=
    card_le_of_le ((commutator_mono hVU le_rfl).trans hUQ₁Cv)
  exact le_centralizer_of_dual_strict hVe hQ₁T hTV hdual hEe (hVQ₁.trans hcardE)


theorem solvable_unique_maximal_bridge [Finite G] {H T MH : Subgroup G} (hT : IsSylowTwoOf T H)
    (hHs : Group.IsSolvable ↥H) (hTn : ¬ H ≤ normalizer (T : Set G)) (hMH : MH < H)
    (hMHmax : ∀ Y : Subgroup G, MH < Y → Y ≤ H → Y = H) (hTMH : T ≤ MH)
    (hMHu : ∀ Y : Subgroup G, Y < H → (∀ Z : Subgroup G, Y < Z → Z ≤ H → Z = H) → T ≤ Y →
      Y = MH) :
    (∀ L : Subgroup G, L ≤ MH → H ≤ normalizer (L : Set G) → ∀ A ≤ L, IsPGroup 2 A →
      A ≤ (CFSG.pCore 2 ↥H).map H.subtype) ∧
    ∃ C : Subgroup G, C ≤ oddOrderSubgroup H ∧ Odd (Nat.card ↥C) ∧
      ∀ k ∈ oddOrderSubgroup H, ∃ c ∈ C, c⁻¹ * k ∈ (CFSG.pCore 2 ↥H).map H.subtype := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTH : T ≤ H := hT.1
  have hMHH : MH ≤ H := hMH.le
  have hback : ∀ Y' : Subgroup ↥H, (Y'.map H.subtype).subgroupOf H = Y' := fun Y' => by
    ext x
    rw [mem_subgroupOf]
    exact mem_map_iff_mem H.subtype_injective
  have hfwd : ∀ {Y : Subgroup G}, Y ≤ H → (Y.subgroupOf H).map H.subtype = Y := fun hY =>
    map_subgroupOf_eq_of_le hY
  have hmapH : ∀ Y' : Subgroup ↥H, Y'.map H.subtype ≤ H := fun Y' => by
    rintro _ ⟨y, -, rfl⟩
    exact y.2
  have hT2' : IsPGroup 2 ↥(T.subgroupOf H) := hT.2.1.of_equiv (subgroupOfEquivOfLe hTH).symm
  let T' : Sylow 2 ↥H := hT2'.toSylow hT.2.2
  have hT'coe : (T' : Subgroup ↥H) = T.subgroupOf H := rfl
  have hTn' : ¬ (T' : Subgroup ↥H).Normal := by
    rw [hT'coe]
    intro hn
    exact hTn ((normal_subgroupOf_iff_le_normalizer hTH).mp hn)
  have hX : IsCoatom (MH.subgroupOf H) := by
    refine ⟨fun h => hMH.ne (le_antisymm hMHH (subgroupOf_eq_top.mp h)), fun Y' hY' => ?_⟩
    have hlt : MH < Y'.map H.subtype := by
      refine lt_of_le_of_ne ?_ fun h => hY'.ne ?_
      · rw [← hfwd hMHH]
        exact map_mono hY'.le
      · rw [h, hback]
    have hY : Y'.map H.subtype = H := hMHmax _ hlt (hmapH Y')
    rw [← hback Y', hY, subgroupOf_self]
  have hTX : (T' : Subgroup ↥H) ≤ MH.subgroupOf H := by
    rw [hT'coe]
    intro x hx
    exact hTMH hx
  have huniq : ∀ Y' : Subgroup ↥H, IsCoatom Y' → (T' : Subgroup ↥H) ≤ Y' →
      Y' = MH.subgroupOf H := by
    intro Y' hY' hTY'
    have hlt : Y'.map H.subtype < H := by
      refine lt_of_le_of_ne (hmapH Y') fun h => hY'.1 ?_
      rw [← hback Y', h, subgroupOf_self]
    have hmax : ∀ Z : Subgroup G, Y'.map H.subtype < Z → Z ≤ H → Z = H := by
      intro Z hZ hZH
      have hlt' : Y' < Z.subgroupOf H := by
        refine lt_of_le_of_ne ?_ fun h => hZ.ne ?_
        · rw [← hback Y']
          exact fun x hx => hZ.le hx
        · rw [h, hfwd hZH]
      have h1 := hY'.2 _ hlt'
      calc Z = (Z.subgroupOf H).map H.subtype := (hfwd hZH).symm
        _ = H := by rw [h1, ← MonoidHom.range_eq_map, range_subtype]
    have hTY : T ≤ Y'.map H.subtype := by
      rw [← hfwd hTH]
      exact map_mono (hT'coe ▸ hTY')
    have h1 := hMHu _ hlt hmax hTY
    rw [← hback Y', h1]
  obtain ⟨p, hp, hp2, P, -, hPn, hPp, hPS, -, -, -, -, -, hcore⟩ :=
    CFSG.Quasithin.H13.A7.A7_solvable_unique_Sylow_overgroup_structure hHs T' hTn' hX hTX huniq
  have : Fact p.Prime := ⟨hp⟩
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥H) with hπ
  have hπker : π.ker = CFSG.pCore 2 ↥H := QuotientGroup.ker_mk' _
  have hQ2 : IsPGroup 2 ↥(CFSG.pCore 2 ↥H) := CFSG.pCore_isPGroup
  have hS2 : IsPGroup 2 ↥((T' : Subgroup ↥H).map π) := T'.isPGroup'.map π
  refine ⟨fun L hLMH hHL A hAL hA2 => ?_, ?_⟩
  ·
    have hLH : L ≤ H := hLMH.trans hMHH
    have hLn : (L.subgroupOf H).Normal := (normal_subgroupOf_iff_le_normalizer hLH).mpr hHL
    have hLn' : ((L.subgroupOf H).map π).Normal := hLn.map π (QuotientGroup.mk'_surjective _)
    have hLX : (L.subgroupOf H).map π ≤ (MH.subgroupOf H).map π :=
      map_mono fun x hx => hLMH hx
    have hLP : (L.subgroupOf H).map π ≤ P := by
      have h1 := (normal_le_normalCore (hN := hLn')).mpr hLX
      rw [hcore] at h1
      exact h1.trans (Subgroup.map_subtype_le _)
    have hAp : IsPGroup p ↥((A.subgroupOf H).map π) :=
      hPp.to_le ((map_mono (show A.subgroupOf H ≤ L.subgroupOf H from
        fun x hx => hAL hx)).trans hLP)
    have hA2' : IsPGroup 2 ↥((A.subgroupOf H).map π) :=
      (hA2.of_equiv (subgroupOfEquivOfLe (hAL.trans hLH)).symm).map π
    have hbot : (A.subgroupOf H).map π = ⊥ := by
      obtain ⟨a, ha⟩ := hAp.exists_card_eq
      obtain ⟨b, hb⟩ := hA2'.exists_card_eq
      have h1 : Nat.card ↥((A.subgroupOf H).map π) = 1 := by
        refine Nat.eq_one_of_dvd_coprimes (a := p ^ a) (b := 2 ^ b)
          (Nat.Coprime.pow a b ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)) ?_ ?_
        · rw [ha]
        · rw [hb]
      exact card_eq_one.mp h1
    have hAQ : A.subgroupOf H ≤ CFSG.pCore 2 ↥H := by
      rw [← hπker, ← Subgroup.map_eq_bot_iff]
      exact hbot
    rw [← hfwd (hAL.trans hLH)]
    exact map_mono hAQ
  ·
    have hodd : ∀ x : ↥H, Odd (orderOf x) → π x ∈ P := by
      intro x hx
      have hxo : Odd (orderOf (π x)) := Odd.of_dvd_nat hx (orderOf_map_dvd π x)
      have hmem : π x ∈ P ⊔ (T' : Subgroup ↥H).map π := by rw [hPS]; exact mem_top _
      obtain ⟨a, ha, s, hs, hxs⟩ := Layer.mem_sup_mul
        (fun y _ => (normalizer_eq_top_iff.mpr hPn).ge (mem_top y)) hmem
      obtain ⟨m, hm⟩ := hS2 ⟨s, hs⟩
      have hm' : s ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
      set φ := QuotientGroup.mk' P with hφ
      have h1 : φ (π x) = φ s := by
        rw [hxs, map_mul, show φ a = 1 from (QuotientGroup.eq_one_iff a).mpr ha, one_mul]
      have h2 : orderOf (φ s) ∣ 2 ^ m := orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hm', map_one])
      have h3 : orderOf (φ s) ∣ orderOf (π x) := h1 ▸ orderOf_map_dvd φ (π x)
      have h4 : orderOf (φ s) = 1 :=
        Nat.eq_one_of_dvd_coprimes (Nat.Coprime.pow_left m (Nat.coprime_two_left.mpr hxo)) h2 h3
      rw [orderOf_eq_one_iff, ← h1] at h4
      exact (QuotientGroup.eq_one_iff _).mp h4
    have hKH : oddOrderSubgroup H ≤ H := oddOrderSubgroup_le H
    set K' := (oddOrderSubgroup H).subgroupOf H with hK'
    have hK'P : K'.map π ≤ P := by
      rintro _ ⟨k, hk, rfl⟩
      have key : ∀ y (hy : y ∈ oddOrderSubgroup H), π ⟨y, hKH hy⟩ ∈ P := by
        intro y hy
        induction hy using Subgroup.closure_induction with
        | mem x hx => exact hodd _ (by rw [Subgroup.orderOf_mk]; exact hx.2)
        | one =>
          show π 1 ∈ P
          rw [map_one]
          exact P.one_mem
        | mul x y hx hy ihx ihy =>
          have e : (⟨x * y, hKH (mul_mem hx hy)⟩ : ↥H) = ⟨x, hKH hx⟩ * ⟨y, hKH hy⟩ := rfl
          rw [e, map_mul]
          exact P.mul_mem ihx ihy
        | inv x hx ihx =>
          have e : (⟨x⁻¹, hKH (inv_mem hx)⟩ : ↥H) = (⟨x, hKH hx⟩ : ↥H)⁻¹ := rfl
          rw [e, map_inv]
          exact P.inv_mem ihx
      exact key k hk
    obtain ⟨a, ha⟩ := (hPp.to_le hK'P).exists_card_eq
    have hker : IsPGroup 2 ↥(K' ⊓ π.ker) := by
      rw [hπker]
      exact hQ2.to_le inf_le_right
    obtain ⟨C', hC'K, hC'c, hC'map⟩ := exists_le_card_eq_map_eq_of_prime π hp hp2 hker ha
    refine ⟨C'.map H.subtype, ?_, ?_, fun k hk => ?_⟩
    · rw [← hfwd hKH]
      exact map_mono hC'K
    · rw [card_map_of_injective H.subtype_injective, hC'c]
      exact Odd.pow (hp.eq_two_or_odd'.resolve_left hp2)
    · have hk' : π ⟨k, hKH hk⟩ ∈ C'.map π := by
        rw [hC'map]
        exact ⟨⟨k, hKH hk⟩, hk, rfl⟩
      obtain ⟨c, hc, hck⟩ := hk'
      have hmem : c⁻¹ * ⟨k, hKH hk⟩ ∈ π.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hck, inv_mul_cancel]
      rw [hπker] at hmem
      exact ⟨c, ⟨c, hc, rfl⟩, ⟨c⁻¹ * ⟨k, hKH hk⟩, hmem, rfl⟩⟩


theorem exists_mul_pow_eq {L : Subgroup G} {l t : G} (hl : l ∈ L)
    (ht : t ∈ normalizer (L : Set G)) (n : ℕ) : ∃ l' ∈ L, (l * t) ^ n = l' * t ^ n := by
  induction n with
  | zero => exact ⟨1, L.one_mem, by simp⟩
  | succ n ih =>
    obtain ⟨l', hl', e⟩ := ih
    have h1 : t ^ n * l * (t ^ n)⁻¹ ∈ L :=
      (mem_normalizer_iff.mp (pow_mem ht n) l).mp hl
    refine ⟨l' * (t ^ n * l * (t ^ n)⁻¹), L.mul_mem hl' h1, ?_⟩
    rw [pow_succ, e, pow_succ]
    group

theorem le_oddOrderSubgroup_sup_of_isSylowTwoOf [Finite G] {H T : Subgroup G}
    (hT : IsSylowTwoOf T H) : H ≤ oddOrderSubgroup H ⊔ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKH : oddOrderSubgroup H ≤ H := oddOrderSubgroup_le H
  have hHK : H ≤ normalizer ((oddOrderSubgroup H : Subgroup G) : Set G) :=
    le_normalizer.trans (normalizer_le_normalizer_oddOrderSubgroup H)
  have hn : ((oddOrderSubgroup H).subgroupOf H).Normal :=
    (normal_subgroupOf_iff_le_normalizer hKH).mpr hHK
  have h2 : IsPGroup 2 (↥H ⧸ (oddOrderSubgroup H).subgroupOf H) := by
    intro x
    induction x using QuotientGroup.induction_on with
    | H x =>
      obtain ⟨k, hk⟩ := exists_pow_mem_oddOrderSubgroup x.2
      exact ⟨k, by
        rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, mem_subgroupOf]
        simpa using hk⟩
  obtain ⟨m, hm⟩ := h2.exists_card_eq
  have hKidx : (oddOrderSubgroup H).relIndex H = 2 ^ m := by
    rw [relIndex, index_eq_card, hm]
  have hd1 : (oddOrderSubgroup H ⊔ T).relIndex H ∣ 2 ^ m :=
    hKidx ▸ relIndex_dvd_of_le_left H le_sup_left
  have hd2 : (oddOrderSubgroup H ⊔ T).relIndex H ∣ T.relIndex H :=
    relIndex_dvd_of_le_left H le_sup_right
  have hTodd : ¬ 2 ∣ T.relIndex H := hT.2.2
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd1
  have hj0 : j = 0 := by
    by_contra hj0
    exact hTodd ((hj ▸ dvd_pow_self 2 hj0).trans hd2)
  rw [hj0, pow_zero] at hj
  exact relIndex_eq_one.mp hj

theorem le_iSup_conj_and_eq_commutator [Finite G] {H T MH Q A : Subgroup G}
    (hTH : T ≤ H) (hT2 : IsPGroup 2 T) (hKT : H ≤ oddOrderSubgroup H ⊔ T)
    (hMHT : ∀ Y : Subgroup G, T ≤ Y → Y < H → Y ≤ MH)
    (hU1 : ∀ L : Subgroup G, L ≤ MH → H ≤ normalizer (L : Set G) → ∀ B ≤ L, IsPGroup 2 B →
      B ≤ Q)
    (hAT : A ≤ T) (hTA : T ≤ normalizer (A : Set G)) (hAQ : ¬ A ≤ Q) :
    oddOrderSubgroup H ≤ ⨆ (h : G) (_ : h ∈ H), A.map (MulAut.conj h).toMonoidHom ∧
      oddOrderSubgroup H = ⁅oddOrderSubgroup H, A⁆ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKH : oddOrderSubgroup H ≤ H := oddOrderSubgroup_le H
  have hHK : H ≤ normalizer ((oddOrderSubgroup H : Subgroup G) : Set G) :=
    le_normalizer.trans (normalizer_le_normalizer_oddOrderSubgroup H)
  have hconj : ∀ {X : Subgroup G} {g : G}, g ∈ normalizer (X : Set G) → ∀ x ∈ X,
      g * x * g⁻¹ ∈ X := fun hg x hx => (mem_normalizer_iff.mp hg x).mp hx
  set L := ⨆ (h : G) (_ : h ∈ H), A.map (MulAut.conj h).toMonoidHom with hL
  have hHL : H ≤ normalizer (L : Set G) := le_normalizer_iSup_conj
  have hAL : A ≤ L := le_iSup_conj
  have hLH : L ≤ H := iSup_conj_le (hAT.trans hTH) le_normalizer
  have hLMH : ¬ L ≤ MH := fun h => hAQ (hU1 L h hHL A hAL (hT2.to_le hAT))
  have hLT : H ≤ L ⊔ T := by
    by_contra hne
    have hlt : L ⊔ T < H := lt_of_le_of_ne (sup_le hLH hTH) fun h => hne h.ge
    exact hLMH (le_sup_left.trans (hMHT _ le_sup_right hlt))
  have hKL : oddOrderSubgroup H ≤ L := by
    refine oddOrderSubgroup_le_of_pow_mem fun h hh => ?_
    obtain ⟨l, hl, t, ht, rfl⟩ := Layer.mem_sup_mul (hTH.trans hHL) (hLT hh)
    obtain ⟨m, hm⟩ := hT2 ⟨t, ht⟩
    have hm' : t ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
    obtain ⟨l', hl', e⟩ := exists_mul_pow_eq hl (hHL (hTH ht)) (2 ^ m)
    exact ⟨m, by rw [e, hm', mul_one]; exact hl'⟩
  have hLKA : L ≤ A ⊔ ⁅oddOrderSubgroup H, A⁆ := iSup_conj_le_of_forall fun g hg a ha => by
    obtain ⟨k, hk, t, ht, rfl⟩ := Layer.mem_sup_mul (hTH.trans hHK) (hKT hg)
    have ha' : t * a * t⁻¹ ∈ A := hconj (hTA ht) a ha
    have e : k * t * a * (k * t)⁻¹ = ⁅k, t * a * t⁻¹⁆ * (t * a * t⁻¹) := by
      rw [commutatorElement_def]; group
    rw [e]
    exact mul_mem (mem_sup_right (commutator_mem_commutator hk ha')) (mem_sup_left ha')
  have hKAK : ⁅oddOrderSubgroup H, A⁆ ≤ oddOrderSubgroup H :=
    le_normalizer_iff_commutator_le_left.mp ((hAT.trans hTH).trans hHK)
  refine ⟨hKL, le_antisymm ?_ hKAK⟩
  have hn : (⁅oddOrderSubgroup H, A⁆.subgroupOf (oddOrderSubgroup H)).Normal :=
    (normal_subgroupOf_iff_le_normalizer hKAK).mpr (normalizer_commutator_ge_left _ _)
  have h2 : IsPGroup 2 (↥(oddOrderSubgroup H) ⧸
      ⁅oddOrderSubgroup H, A⁆.subgroupOf (oddOrderSubgroup H)) := by
    intro x
    induction x using QuotientGroup.induction_on with
    | H x =>
      have hx : (x : G) ∈ ⁅oddOrderSubgroup H, A⁆ ⊔ A := by
        rw [sup_comm]
        exact (hKL.trans hLKA) x.2
      obtain ⟨c, hc, a, ha, hca⟩ := Layer.mem_sup_mul (normalizer_commutator_ge_right _ _) hx
      obtain ⟨m, hm⟩ := hT2 ⟨a, hAT ha⟩
      have hm' : a ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
      obtain ⟨c', hc', e⟩ := exists_mul_pow_eq hc (normalizer_commutator_ge_right _ _ ha) (2 ^ m)
      refine ⟨m, ?_⟩
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, mem_subgroupOf, SubgroupClass.coe_pow,
        hca, e, hm', mul_one]
      exact hc'
  have htop := hasNoTwoQuotient_oddOrderSubgroup H _ h2
  exact subgroupOf_eq_top.mp htop

theorem le_commutator_of_hasNoTwoQuotient [Finite G] {K P₀ C : Subgroup G}
    (hK : HasNoTwoQuotient K) (hP₀K : P₀ ≤ K) (hKP₀ : K ≤ normalizer (P₀ : Set G))
    (hP₀2 : IsPGroup 2 P₀) (hCK : C ≤ K) (hCo : Odd (Nat.card ↥C))
    (hKC : ∀ k ∈ K, ∃ c ∈ C, c⁻¹ * k ∈ P₀) : P₀ ≤ ⁅P₀, K⁆ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLP₀ : ⁅P₀, K⁆ ≤ P₀ := le_normalizer_iff_commutator_le_left.mp hKP₀
  have hKL : K ≤ normalizer ((⁅P₀, K⁆ : Subgroup G) : Set G) := normalizer_commutator_ge_right _ _
  have hMK : ⁅P₀, K⁆ ⊔ C ≤ K := sup_le (hLP₀.trans hP₀K) hCK
  have hCM : C ≤ normalizer ((⁅P₀, K⁆ ⊔ C : Subgroup G) : Set G) :=
    le_normalizer_sup_of_le (hCK.trans hKL) le_normalizer
  have hP₀M : P₀ ≤ normalizer ((⁅P₀, K⁆ ⊔ C : Subgroup G) : Set G) := by
    apply le_normalizer_of_conj_mem_of_finite
    intro x hx y hy
    have hle : (⁅P₀, K⁆ ⊔ C).map (MulAut.conj x).toMonoidHom ≤ ⁅P₀, K⁆ ⊔ C := by
      rw [Subgroup.map_sup]
      refine sup_le ?_ ?_
      · rw [RankThree.GroupTheory.SteinbergBY.map_conj_eq_of_mem_normalizer (hKL (hP₀K hx))]
        exact le_sup_left
      · rintro _ ⟨c, hc, rfl⟩
        have e : (MulAut.conj x).toMonoidHom c = ⁅x, c⁆ * c := by
          simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, commutatorElement_def]
          group
        rw [e]
        exact mul_mem (mem_sup_left (commutator_mem_commutator hx (hCK hc))) (mem_sup_right hc)
    exact hle ⟨y, hy, rfl⟩
  have hKM : K ≤ normalizer ((⁅P₀, K⁆ ⊔ C : Subgroup G) : Set G) := by
    intro k hk
    obtain ⟨c, hc, hck⟩ := hKC k hk
    have e : k = c * (c⁻¹ * k) := by group
    rw [e]
    exact mul_mem (hCM hc) (hP₀M hck)
  have hn : ((⁅P₀, K⁆ ⊔ C).subgroupOf K).Normal :=
    (normal_subgroupOf_iff_le_normalizer hMK).mpr hKM
  have h2 : IsPGroup 2 (↥K ⧸ (⁅P₀, K⁆ ⊔ C).subgroupOf K) := by
    intro x
    induction x using QuotientGroup.induction_on with
    | H x =>
      obtain ⟨c, hc, hcx⟩ := hKC x x.2
      obtain ⟨m, hm⟩ := hP₀2 ⟨_, hcx⟩
      have hm' : (c⁻¹ * x) ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
      have hcxK : c⁻¹ * (x : G) ∈ K := hP₀K hcx
      refine ⟨m, ?_⟩
      have e : x = (⟨c, hCK hc⟩ : ↥K) * ⟨c⁻¹ * x, hcxK⟩ := Subtype.ext (by simp)
      rw [e, QuotientGroup.mk_mul,
        (QuotientGroup.eq_one_iff _).mpr (show (⟨c, hCK hc⟩ : ↥K) ∈ (⁅P₀, K⁆ ⊔ C).subgroupOf K
          from mem_sup_right hc), one_mul, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff,
        mem_subgroupOf]
      rw [SubgroupClass.coe_pow]
      show (c⁻¹ * (x : G)) ^ 2 ^ m ∈ _
      rw [hm']
      exact one_mem _
  have hKM' : K ≤ ⁅P₀, K⁆ ⊔ C := subgroupOf_eq_top.mp (hK _ h2)
  intro y hy
  obtain ⟨l, hl, c, hc, rfl⟩ := Layer.mem_sup_mul (hCK.trans hKL) (hKM' (hP₀K hy))
  have hcP : c ∈ P₀ := by
    have e : c = l⁻¹ * (l * c) := by group
    rw [e]
    exact P₀.mul_mem (P₀.inv_mem (hLP₀ hl)) hy
  have hc1 : c = 1 := by
    obtain ⟨m, hm⟩ := hP₀2 ⟨c, hcP⟩
    have hm' : c ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
    have h1 : orderOf c ∣ 2 ^ m := orderOf_dvd_of_pow_eq_one hm'
    have h2 : orderOf c ∣ Nat.card ↥C := by
      rw [← Subgroup.orderOf_mk c hc]
      exact orderOf_dvd_natCard _
    have h3 : orderOf c = 1 := Nat.eq_one_of_dvd_coprimes
      (Nat.Coprime.pow_left m (Nat.coprime_two_left.mpr hCo)) h1 h2
    exact orderOf_eq_one_iff.mp h3
  rw [hc1, mul_one]
  exact hl

theorem le_centralizer_of_irreducible [Finite G] {H I D : Subgroup G}
    (hHI : H ≤ normalizer (I : Set G)) (hIe : CFSG.Open.IsElemAbelian 2 I)
    (hirr : ∀ X : Subgroup G, X ≤ I → H ≤ normalizer (X : Set G) → X = ⊥ ∨ X = I)
    (hDH : D ≤ H) (hHD : H ≤ normalizer (D : Set G))
    (hD2 : ∀ d ∈ D, ∃ k : ℕ, d ^ 2 ^ k ∈ centralizer (I : Set G)) :
    D ≤ centralizer (I : Set G) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_cases hI : I = ⊥
  · intro d _
    rw [mem_centralizer_iff]
    intro x hx
    have hxI : x ∈ I := hx
    rw [hI] at hxI
    rw [mem_bot.mp hxI, one_mul, mul_one]
  have hX : H ≤ normalizer ((I ⊓ centralizer (D : Set G) : Subgroup G) : Set G) :=
    le_normalizer_inf_of_le hHI fun h hh => mem_normalizer_centralizer_of_mem_normalizer (hHD hh)
  rcases hirr _ inf_le_left hX with h0 | h1
  · exfalso
    obtain ⟨S⟩ := (inferInstance : Nonempty (Sylow 2 ↥D))
    have hS₂D : (S : Subgroup ↥D).map D.subtype ≤ D := Subgroup.map_subtype_le _
    have hS₂2 : IsPGroup 2 ↥((S : Subgroup ↥D).map D.subtype) := S.isPGroup'.map _
    have hS₂idx : ¬ 2 ∣ ((S : Subgroup ↥D).map D.subtype).relIndex D := by
      have e : (((S : Subgroup ↥D).map D.subtype).subgroupOf D) = (S : Subgroup ↥D) := by
        ext x
        rw [mem_subgroupOf]
        exact mem_map_iff_mem D.subtype_injective
      rw [relIndex, e]
      exact S.not_dvd_index
    have hDCc : D ≤ normalizer ((D ⊓ centralizer (I : Set G) : Subgroup G) : Set G) :=
      le_normalizer_inf_of_le le_normalizer fun d hd =>
        mem_normalizer_centralizer_of_mem_normalizer (hHI (hDH hd))
    have hn : ((D ⊓ centralizer (I : Set G)).subgroupOf D).Normal :=
      (normal_subgroupOf_iff_le_normalizer inf_le_left).mpr hDCc
    have h2 : IsPGroup 2 (↥D ⧸ (D ⊓ centralizer (I : Set G)).subgroupOf D) := by
      intro x
      induction x using QuotientGroup.induction_on with
      | H x =>
        obtain ⟨k, hk⟩ := hD2 x x.2
        exact ⟨k, by
          rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, mem_subgroupOf,
            SubgroupClass.coe_pow]
          exact ⟨D.pow_mem x.2 _, hk⟩⟩
    obtain ⟨m, hm⟩ := h2.exists_card_eq
    have hCcidx : (D ⊓ centralizer (I : Set G)).relIndex D = 2 ^ m := by
      rw [relIndex, index_eq_card, hm]
    have hd1 : ((S : Subgroup ↥D).map D.subtype ⊔ D ⊓ centralizer (I : Set G)).relIndex D ∣
        2 ^ m := hCcidx ▸ relIndex_dvd_of_le_left D le_sup_right
    have hd2 : ((S : Subgroup ↥D).map D.subtype ⊔ D ⊓ centralizer (I : Set G)).relIndex D ∣
        ((S : Subgroup ↥D).map D.subtype).relIndex D := relIndex_dvd_of_le_left D le_sup_left
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd1
    have hj0 : j = 0 := by
      by_contra hj0
      exact hS₂idx ((hj ▸ dvd_pow_self 2 hj0).trans hd2)
    rw [hj0, pow_zero] at hj
    have hDS : D ≤ (S : Subgroup ↥D).map D.subtype ⊔ D ⊓ centralizer (I : Set G) :=
      relIndex_eq_one.mp hj
    have hSI : (S : Subgroup ↥D).map D.subtype ≤ normalizer (I : Set G) :=
      hS₂D.trans (hDH.trans hHI)
    have hI2 : IsPGroup 2 I := fun x =>
      ⟨1, Subtype.ext (by simpa using hIe.2 _ x.2)⟩
    have hP2 : IsPGroup 2 ↥((S : Subgroup ↥D).map D.subtype ⊔ I) :=
      hS₂2.to_sup_of_normal_right' hI2 hSI
    obtain ⟨v, hvI, hv1, hvS⟩ := exists_mem_not_mem_forall_commutator_mem hP2 le_sup_right
      (sup_le hSI le_normalizer) (fun h => hI (le_bot_iff.mp h))
    have hvD : v ∈ centralizer (D : Set G) := by
      rw [mem_centralizer_iff]
      intro d hd
      have hd' : d ∈ D ⊓ centralizer (I : Set G) ⊔ (S : Subgroup ↥D).map D.subtype := by
        rw [sup_comm]
        exact hDS hd
      obtain ⟨c, hc, s, hs, rfl⟩ := Layer.mem_sup_mul (hS₂D.trans hDCc) hd'
      have hsv : s * v = v * s := by
        have := hvS s (mem_sup_left hs)
        rw [mem_bot] at this
        exact (commutatorElement_eq_one_iff_mul_comm.mp this).symm
      have hcv : c * v = v * c := (mem_centralizer_iff.mp hc.2 v hvI).symm
      rw [mul_assoc, hsv, ← mul_assoc, hcv, mul_assoc]
    have hmem : v ∈ I ⊓ centralizer (D : Set G) := ⟨hvI, hvD⟩
    rw [h0, mem_bot] at hmem
    exact hv1 (by rw [hmem]; exact one_mem _)
  · intro d hd
    rw [mem_centralizer_iff]
    intro x hx
    have hx' := (h1.ge hx).2
    exact (mem_centralizer_iff.mp hx' d hd).symm


end SteinbergCD

open Subgroup SteinbergCD CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup
  CFSG.QuasithinUnique.Setup.Campbell

theorem single_noncentral_chief_factor_forces_normal_core_intersection_and_residual_Sylow
    {G : Type*} [Group G] [Finite G] {F H T V : Subgroup G}
    (hTF : T ≤ F) (hT : IsSylowTwoOf T H) (hHs : Group.IsSolvable ↥H)
    (hTn : ¬ (T.subgroupOf H).Normal) {MH : Subgroup G} (hMH : MH < H)
    (hMHmax : ∀ Y : Subgroup G, MH < Y → Y ≤ H → Y = H) (hTMH : T ≤ MH)
    (hMHu : ∀ Y : Subgroup G, Y < H → (∀ Z : Subgroup G, Y < Z → Z ≤ H → Z = H) → T ≤ Y →
      Y = MH)
    {Q R : Subgroup G} (hQ : Q = (CFSG.pCore 2 ↥H).map H.subtype)
    (hVF : V ≤ F) (hVn : (V.subgroupOf F).Normal) (hVe : CFSG.Open.IsElemAbelian 2 V)
    (hV1 : V ≠ ⊥) (hVQ : V ≤ Q) (hR : R = T ⊓ centralizer (V : Set G))
    (hRFn : (R.subgroupOf F).Normal)
    (hRn : ∀ X : Subgroup G, X ≤ R → X ≠ ⊥ → ¬ (X.subgroupOf (F ⊔ H)).Normal)
    (hstrict : ∀ E : Subgroup (MulAut ↥V),
      (∀ σ ∈ E, ∃ t ∈ T, ∀ v : ↥V, ((σ v : ↥V) : G) = t * v * t⁻¹) → E ≠ ⊥ →
        CFSG.IsElementaryAbelian 2 ↥E →
          Nat.card ↥E * Nat.card ↥(FixedPoints.subgroup ↥E ↥V) < Nat.card ↥V ∧
          Nat.card ↥E * Nat.card {φ : ↥V →* Multiplicative (ZMod 2) //
            ∀ σ ∈ E, ∀ v, φ (σ v) = φ v} < Nat.card (↥V →* Multiplicative (ZMod 2)))
    {U : Subgroup G} (hU : U = ⨆ (h : G) (_ : h ∈ H), V.map (MulAut.conj h).toMonoidHom)
    (hUe : CFSG.Open.IsElemAbelian 2 U)
    (hU1 : ∃ (n : ℕ) (C : Fin (n + 1) → Subgroup G), C 0 = ⊥ ∧ C (Fin.last n) = U ∧
      (∀ i, H ≤ normalizer (C i : Set G)) ∧
      (∀ i : Fin n, C i.castSucc < C i.succ ∧ ∀ X : Subgroup G, H ≤ normalizer (X : Set G) →
        C i.castSucc ≤ X → X ≤ C i.succ → X = C i.castSucc ∨ X = C i.succ) ∧
      ∃! i : Fin n, ¬ ⁅C i.succ, H⁆ ≤ C i.castSucc)
    {K Q₀ I : Subgroup G} (hK : K = oddOrderSubgroup H) (hQ₀ : Q₀ = R ⊓ Q)
    (hI : I = ⁅U, K⁆) :
    (Q₀ ≤ H ∧ (Q₀.subgroupOf H).Normal) ∧ U ≤ Q₀ ⊓ centralizer (Q₀ : Set G) ∧
      K = ⁅K, R⁆ ∧ K = ⁅K, elemThompsonIn 2 R⁆ ∧
      (CFSG.pCore 2 ↥K).map K.subtype ≤ Q₀ ∧ IsSylowTwoOf R (K ⊔ R) ∧
      elemThompsonIn 2 T = elemThompsonIn 2 R ∧ ¬ elemThompsonIn 2 T ≤ Q ∧
      I ≠ ⊥ ∧ H ≤ normalizer (I : Set G) ∧
      (∀ X : Subgroup G, X ≤ I → H ≤ normalizer (X : Set G) → X = ⊥ ∨ X = I) ∧
      I ≤ Q ⊓ centralizer (Q : Set G) ∧ I ≤ H ∧ IsPrimeReduced 2 (I.subgroupOf H) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, C, hC0, hCn, hCH, hCs, hone⟩ := hU1
  subst hK hI
  have hconj : ∀ {X : Subgroup G} {g : G}, g ∈ normalizer (X : Set G) → ∀ x ∈ X,
      g * x * g⁻¹ ∈ X := fun hg x hx => (mem_normalizer_iff.mp hg x).mp hx
  have hTH : T ≤ H := hT.1
  have hT2 : IsPGroup 2 T := hT.2.1
  have hFV : F ≤ normalizer (V : Set G) := (normal_subgroupOf_iff_le_normalizer hVF).mp hVn
  have hRF : F ≤ normalizer (R : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (hR ▸ inf_le_left.trans hTF)).mp hRFn
  have hTV : T ≤ normalizer (V : Set G) := hTF.trans hFV
  have hRn' : ∀ X : Subgroup G, X ≤ R → X ≠ ⊥ → ¬ F ⊔ H ≤ normalizer (X : Set G) :=
    fun X hXR hX1 hXn => hRn X hXR hX1 ((normal_subgroupOf_iff_le_normalizer
      (hXR.trans ((hR ▸ inf_le_left : R ≤ T).trans (hTF.trans le_sup_left)))).mpr hXn)
  have hTn' : ¬ H ≤ normalizer (T : Set G) := fun h =>
    hTn ((normal_subgroupOf_iff_le_normalizer hTH).mpr h)
  have hQH : Q ≤ H := hQ ▸ Subgroup.map_subtype_le _
  have hHQ : H ≤ normalizer (Q : Set G) := hQ ▸ le_normalizer.trans
    (CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic (CFSG.pCore 2 ↥H))
  have hQ2 : IsPGroup 2 Q := hQ ▸ (CFSG.pCore_isPGroup (p := 2) (G := ↥H)).map _
  have hQT : Q ≤ T := by
    have hT2' : IsPGroup 2 ↥(T.subgroupOf H) := hT2.of_equiv (subgroupOfEquivOfLe hTH).symm
    have h1 : CFSG.pCore 2 ↥H ≤ T.subgroupOf H :=
      IsPGroup.le_sylow_of_normal CFSG.pCore_isPGroup (hT2'.toSylow hT.2.2)
    rw [hQ, ← map_subgroupOf_eq_of_le hTH]
    exact map_mono h1
  have hQmax : ∀ X : Subgroup G, X ≤ H → H ≤ normalizer (X : Set G) → IsPGroup 2 X → X ≤ Q := by
    intro X hXH hHX hX2
    have hn : (X.subgroupOf H).Normal := (normal_subgroupOf_iff_le_normalizer hXH).mpr hHX
    have h1 : X.subgroupOf H ≤ CFSG.pCore 2 ↥H :=
      le_sSup ⟨hn, hX2.of_equiv (subgroupOfEquivOfLe hXH).symm⟩
    rw [hQ, ← map_subgroupOf_eq_of_le hXH]
    exact map_mono h1
  have hKH : oddOrderSubgroup H ≤ H := oddOrderSubgroup_le H
  have hHK : H ≤ normalizer ((oddOrderSubgroup H : Subgroup G) : Set G) :=
    le_normalizer.trans (normalizer_le_normalizer_oddOrderSubgroup H)
  have hKT : H ≤ oddOrderSubgroup H ⊔ T := le_oddOrderSubgroup_sup_of_isSylowTwoOf hT
  have hVc : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := fun a ha b hb => by
    have := hVe.1
    exact setLike_mul_comm ha hb
  have hVT : V ≤ T := hVQ.trans hQT
  have hVCV : V ≤ centralizer (V : Set G) := fun v hv =>
    mem_centralizer_iff.mpr fun w hw => hVc w hw v hv
  have hVR : V ≤ R := hR ▸ le_inf hVT hVCV
  have hVH : ¬ H ≤ normalizer (V : Set G) := fun h => hRn' V hVR hV1 (sup_le hFV h)
  have hHU : H ≤ normalizer (U : Set G) := hU ▸ le_normalizer_iSup_conj
  have hVU : V ≤ U := hU ▸ le_iSup_conj
  have hUc : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a := fun a ha b hb => by
    have := hUe.1
    exact setLike_mul_comm ha hb
  have hP1 : ∀ W : Subgroup G, W ≤ U → H ≤ normalizer (W : Set G) →
      ⁅W, oddOrderSubgroup H⁆ ≠ ⊥ → ⁅U, oddOrderSubgroup H⁆ ≤ W := fun W hWU hHW hWK =>
    commutator_oddOrderSubgroup_le_of_compositionSeries hUe hHU hWU hHW hC0 hCn hCH hCs hone hWK
  have hA := iSup_conj_le_centralizer_of_single_chief_factor hTH hT2 hTV hKH hHK hKT hQT hHQ hVQ
    hVe hVH hU hUe hP1 fun E h1 h2 h3 => (hstrict E h1 h2 h3).2
  have hQ₀Q : Q₀ ≤ Q := hQ₀ ▸ inf_le_right
  have hQ₀R : Q₀ ≤ R := hQ₀ ▸ inf_le_left
  have hRT : R ≤ T := hR ▸ inf_le_left
  rw [← hR] at hA
  have hQ₀eq : ⨆ (h : G) (_ : h ∈ H), Q₀.map (MulAut.conj h).toMonoidHom = Q₀ := by
    refine le_antisymm ?_ le_iSup_conj
    have hle : ⨆ (h : G) (_ : h ∈ H), Q₀.map (MulAut.conj h).toMonoidHom ≤ Q :=
      iSup_conj_le hQ₀Q hHQ
    rw [hQ₀] at hle ⊢
    exact le_inf ((le_inf (hle.trans hQT) hA).trans hR.ge) hle
  have hHQ₀ : H ≤ normalizer (Q₀ : Set G) := hQ₀eq ▸ le_normalizer_iSup_conj
  have hQ₀H : Q₀ ≤ H := hQ₀Q.trans hQH
  have hVQ₀ : V ≤ Q₀ := hQ₀ ▸ le_inf hVR hVQ
  have hUQ₀ : U ≤ Q₀ := hU ▸ iSup_conj_le hVQ₀ hHQ₀
  have hUCQ₀ : U ≤ centralizer (Q₀ : Set G) := by
    rw [hU]
    refine iSup_conj_le_of_forall fun g hg v hv => ?_
    rw [mem_centralizer_iff]
    intro q hq
    have hq' : g⁻¹ * q * g ∈ Q₀ := by simpa using hconj (hHQ₀ (H.inv_mem hg)) q hq
    have h1 : v * (g⁻¹ * q * g) = (g⁻¹ * q * g) * v :=
      mem_centralizer_iff.mp (hR ▸ hQ₀R hq' : g⁻¹ * q * g ∈ T ⊓ centralizer (V : Set G)).2 v hv
    calc q * (g * v * g⁻¹) = g * ((g⁻¹ * q * g) * v) * g⁻¹ := by group
      _ = g * (v * (g⁻¹ * q * g)) * g⁻¹ := by rw [h1]
      _ = g * v * g⁻¹ * q := by group
  have hJTR : thompsonJ T ≤ R := by
    rw [hR]
    refine le_inf (CFSG.Quasithin.B6.thompsonJ_le T) (iSup₂_le fun A hA => ?_)
    exact le_centralizer_of_isMaxElemAbelian_of_strict hVT hTV hVe
      (fun E h1 h2 h3 => (hstrict E h1 h2 h3).1) hA
  have hJRT : elemThompsonIn 2 R = elemThompsonIn 2 T :=
    elemThompsonIn_eq_of_le 2 (by rw [Wreath.elemThompsonIn_two_eq]; exact hJTR) hRT
  have hT1 : T ≠ ⊥ := fun h => hTn' (by
    rw [h, normalizer_eq_top_iff.mpr (inferInstance : (⊥ : Subgroup G).Normal)]
    exact le_top)
  have hJQ : ¬ thompsonJ T ≤ Q := by
    intro hle
    have hJQ₀ : thompsonJ T ≤ Q₀ := hQ₀ ▸ le_inf hJTR hle
    have hQ₀T : Q₀ ≤ T := hQ₀R.trans hRT
    have hJ₀ : elemThompsonIn 2 Q₀ = elemThompsonIn 2 T :=
      elemThompsonIn_eq_of_le 2 (by rw [Wreath.elemThompsonIn_two_eq]; exact hJQ₀) hQ₀T
    rw [Wreath.elemThompsonIn_two_eq, Wreath.elemThompsonIn_two_eq] at hJ₀ hJRT
    have hHJ : H ≤ normalizer ((thompsonJ T : Subgroup G) : Set G) :=
      hJ₀ ▸ hHQ₀.trans (normalizer_le_normalizer_thompsonJ Q₀)
    have hFJ : F ≤ normalizer ((thompsonJ T : Subgroup G) : Set G) :=
      hJRT ▸ hRF.trans (normalizer_le_normalizer_thompsonJ R)
    exact hRn' _ hJTR (thompsonJ_ne_bot hT2 hT1) (sup_le hFJ hHJ)
  obtain ⟨hU1', Cc, hCcK, hCco, hKCc⟩ :=
    solvable_unique_maximal_bridge hT hHs hTn' hMH hMHmax hTMH hMHu
  rw [← hQ] at hU1' hKCc
  have hMHT : ∀ Y : Subgroup G, T ≤ Y → Y < H → Y ≤ MH := by
    intro Y hTY hYH
    obtain ⟨Y', hY'⟩ := (Set.toFinite {Z : Subgroup G | Y ≤ Z ∧ Z < H}).exists_maximal
      ⟨Y, le_rfl, hYH⟩
    have hmax : ∀ Z : Subgroup G, Y' < Z → Z ≤ H → Z = H := by
      intro Z hZ hZH
      by_contra hne
      have hZm : Z ∈ {Z : Subgroup G | Y ≤ Z ∧ Z < H} :=
        ⟨hY'.1.1.trans hZ.le, lt_of_le_of_ne hZH hne⟩
      exact (not_le_of_gt hZ) (hY'.2 hZm hZ.le)
    have h1 := hMHu Y' hY'.1.2 hmax (hTY.trans hY'.1.1)
    rw [← h1]
    exact hY'.1.1
  have hTR : T ≤ normalizer (R : Set G) := hR ▸ le_normalizer_inf_of_le le_normalizer
    fun t ht => mem_normalizer_centralizer_of_mem_normalizer (hTV ht)
  have hRQ : ¬ R ≤ Q := fun h => hJQ (hJTR.trans h)
  obtain ⟨hKLR, hKR⟩ := le_iSup_conj_and_eq_commutator hTH hT2 hKT hMHT hU1' hRT hTR hRQ
  have hJRR : thompsonJ R ≤ R := CFSG.Quasithin.B6.thompsonJ_le R
  have hTJ : T ≤ normalizer ((thompsonJ R : Subgroup G) : Set G) :=
    hTR.trans (normalizer_le_normalizer_thompsonJ R)
  have hJRQ : ¬ thompsonJ R ≤ Q := by
    rw [← Wreath.elemThompsonIn_two_eq, hJRT, Wreath.elemThompsonIn_two_eq]
    exact hJQ
  obtain ⟨-, hKJ⟩ := le_iSup_conj_and_eq_commutator hTH hT2 hKT hMHT hU1' (hJRR.trans hRT) hTJ hJRQ
  have hQRQ₀ : ⁅Q, R⁆ ≤ Q₀ := hQ₀ ▸ le_inf
    (le_normalizer_iff_commutator_le_right.mp (hQT.trans hTR))
    (le_normalizer_iff_commutator_le_left.mp ((hRT.trans hTH).trans hHQ))
  obtain ⟨XQ, hHXQ, hXQ⟩ := exists_subgroup_forall_commutator_mem (A := Q) hHQ hHQ₀
  have hRXQ : R ≤ XQ := fun r hr =>
    (hXQ r).mpr ⟨hRT.trans hTH hr, fun q hq => hQRQ₀ (commutator_mem_commutator hq hr)⟩
  have hKXQ : oddOrderSubgroup H ≤ XQ := hKLR.trans (iSup_conj_le hRXQ hHXQ)
  have hQKQ₀ : ⁅Q, oddOrderSubgroup H⁆ ≤ Q₀ := by
    rw [commutator_le]
    intro q hq k hk
    exact ((hXQ k).mp (hKXQ hk)).2 q hq
  have hP₀K : oddOrderSubgroup H ⊓ Q ≤ oddOrderSubgroup H := inf_le_left
  have hKP₀ : oddOrderSubgroup H ≤ normalizer ((oddOrderSubgroup H ⊓ Q : Subgroup G) : Set G) :=
    le_normalizer_inf_of_le le_normalizer (hKH.trans hHQ)
  have hP₀2 : IsPGroup 2 ↥(oddOrderSubgroup H ⊓ Q) := hQ2.to_le inf_le_right
  have hKCc' : ∀ k ∈ oddOrderSubgroup H, ∃ c ∈ Cc, c⁻¹ * k ∈ oddOrderSubgroup H ⊓ Q := by
    intro k hk
    obtain ⟨c, hc, hck⟩ := hKCc k hk
    exact ⟨c, hc, Subgroup.mem_inf.mpr ⟨mul_mem (inv_mem (hCcK hc)) hk, hck⟩⟩
  have hP₀L := le_commutator_of_hasNoTwoQuotient (hasNoTwoQuotient_oddOrderSubgroup H) hP₀K hKP₀
    hP₀2 hCcK hCco hKCc'
  have hP₀Q₀ : oddOrderSubgroup H ⊓ Q ≤ Q₀ :=
    hP₀L.trans ((commutator_mono inf_le_right le_rfl).trans hQKQ₀)
  have hO2K : (CFSG.pCore 2 ↥(oddOrderSubgroup H)).map (oddOrderSubgroup H).subtype ≤
      oddOrderSubgroup H ⊓ Q := by
    refine le_inf (Subgroup.map_subtype_le _) (hQmax _ ((Subgroup.map_subtype_le _).trans hKH)
      (hHK.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic _))
      ((CFSG.pCore_isPGroup (p := 2) (G := ↥(oddOrderSubgroup H))).map _))
  have hCcP₀ : Cc ⊓ (oddOrderSubgroup H ⊓ Q) = ⊥ := by
    obtain ⟨a, ha⟩ := hP₀2.exists_card_eq
    have h1 : Nat.card ↥(Cc ⊓ (oddOrderSubgroup H ⊓ Q)) = 1 := by
      refine Nat.eq_one_of_dvd_coprimes (a := Nat.card ↥Cc) (b := 2 ^ a)
        (Nat.Coprime.pow_right a (Nat.coprime_two_right.mpr hCco)) ?_ ?_
      · exact card_dvd_of_le inf_le_left
      · rw [← ha]
        exact card_dvd_of_le inf_le_right
    exact card_eq_one.mp h1
  have hKeq : oddOrderSubgroup H = Cc ⊔ (oddOrderSubgroup H ⊓ Q) := by
    refine le_antisymm (fun k hk => ?_) (sup_le hCcK inf_le_left)
    obtain ⟨c, hc, hck⟩ := hKCc' k hk
    have e : k = c * (c⁻¹ * k) := by group
    rw [e]
    exact mul_mem (mem_sup_left hc) (mem_sup_right hck)
  have hcardK : Nat.card ↥(oddOrderSubgroup H) =
      Nat.card ↥Cc * Nat.card ↥(oddOrderSubgroup H ⊓ Q) := by
    have h1 := C5.card_sup_mul_card_inf_of_le_normalizer (hCcK.trans hKP₀)
    rw [hCcP₀, card_bot, mul_one, ← hKeq] at h1
    exact h1
  have hP₀idx : (oddOrderSubgroup H ⊓ Q).relIndex (oddOrderSubgroup H) = Nat.card ↥Cc := by
    have h1 := relIndex_mul_card (oddOrderSubgroup H ⊓ Q) (oddOrderSubgroup H)
    rw [inf_eq_left.mpr hP₀K, hcardK] at h1
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h1
  have hSyl : IsSylowTwoOf R (oddOrderSubgroup H ⊔ R) := by
    refine ⟨le_sup_right, hT2.to_le hRT, ?_⟩
    show ¬ 2 ∣ R.relIndex (oddOrderSubgroup H ⊔ R)
    have hRK : R ≤ normalizer ((oddOrderSubgroup H : Subgroup G) : Set G) :=
      (hRT.trans hTH).trans hHK
    have h1 := C5.card_sup_mul_card_inf_of_le_normalizer hRK
    rw [sup_comm R, inf_comm R] at h1
    have h2 := relIndex_mul_card R (oddOrderSubgroup H ⊔ R)
    rw [inf_eq_left.mpr le_sup_right] at h2
    have h3 := relIndex_mul_card (oddOrderSubgroup H ⊓ R) (oddOrderSubgroup H)
    rw [inf_eq_left.mpr inf_le_left] at h3
    have h4 : R.relIndex (oddOrderSubgroup H ⊔ R) =
        (oddOrderSubgroup H ⊓ R).relIndex (oddOrderSubgroup H) := by
      have hpos : 0 < Nat.card ↥R * Nat.card ↥(oddOrderSubgroup H ⊓ R) :=
        Nat.mul_pos Nat.card_pos Nat.card_pos
      apply Nat.eq_of_mul_eq_mul_right hpos
      calc R.relIndex (oddOrderSubgroup H ⊔ R) * (Nat.card ↥R * Nat.card ↥(oddOrderSubgroup H ⊓ R))
          = (R.relIndex (oddOrderSubgroup H ⊔ R) * Nat.card ↥R) *
              Nat.card ↥(oddOrderSubgroup H ⊓ R) := by ring
        _ = Nat.card ↥(oddOrderSubgroup H ⊔ R) * Nat.card ↥(oddOrderSubgroup H ⊓ R) := by
          rw [h2]
        _ = Nat.card ↥R * Nat.card ↥(oddOrderSubgroup H) := h1
        _ = Nat.card ↥R * ((oddOrderSubgroup H ⊓ R).relIndex (oddOrderSubgroup H) *
              Nat.card ↥(oddOrderSubgroup H ⊓ R)) := by rw [h3]
        _ = (oddOrderSubgroup H ⊓ R).relIndex (oddOrderSubgroup H) *
              (Nat.card ↥R * Nat.card ↥(oddOrderSubgroup H ⊓ R)) := by ring
    rw [h4]
    intro h2d
    have hP₀R : oddOrderSubgroup H ⊓ Q ≤ oddOrderSubgroup H ⊓ R :=
      le_inf inf_le_left (hP₀Q₀.trans hQ₀R)
    have := h2d.trans (relIndex_dvd_of_le_left (oddOrderSubgroup H) hP₀R)
    rw [hP₀idx] at this
    exact (Nat.not_even_iff_odd.mpr hCco) (even_iff_two_dvd.mpr this)
  have hIU : ⁅U, oddOrderSubgroup H⁆ ≤ U := le_normalizer_iff_commutator_le_left.mp (hKH.trans hHU)
  have hHI : H ≤ normalizer ((⁅U, oddOrderSubgroup H⁆ : Subgroup G) : Set G) :=
    le_normalizer_commutator_of_le hHU hHK
  have hIne : ⁅U, oddOrderSubgroup H⁆ ≠ ⊥ := by
    intro h0
    apply hVH
    have hKU : oddOrderSubgroup H ≤ centralizer (U : Set G) := by
      rw [commutator_comm] at h0
      exact commutator_eq_bot_iff_le_centralizer.mp h0
    refine hKT.trans (sup_le ?_ hTV)
    apply le_normalizer_of_conj_mem_of_finite
    intro k hk v hv
    rw [← mem_centralizer_iff.mp (hKU hk) v (hVU hv), mul_inv_cancel_right]
    exact hv
  have hCcU : Cc ≤ normalizer (U : Set G) := (hCcK.trans hKH).trans hHU
  have hICK : ⁅U, oddOrderSubgroup H⁆ ⊓
      centralizer ((oddOrderSubgroup H : Subgroup G) : Set G) = ⊥ := by
    have h1 := commutator_inf_centralizer_eq_bot_of_odd hUe hCcU hCco
    refine eq_bot_iff.mpr ((inf_le_inf ?_ (centralizer_le hCcK)).trans h1.le)
    rw [commutator_le]
    intro u hu k hk
    obtain ⟨c, hc, hck⟩ := hKCc' k hk
    have hx : ⁅u, c⁻¹ * k⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr
      ((mem_centralizer_iff.mp (hUCQ₀ hu) _ (hP₀Q₀ hck)).symm)
    have e : ⁅u, k⁆ = ⁅u, c⁆ * (c * ⁅u, c⁻¹ * k⁆ * c⁻¹) := by
      simp only [commutatorElement_def]; group
    rw [e, hx, mul_one, mul_inv_cancel, mul_one]
    exact commutator_mem_commutator hu hc
  have hirr : ∀ X : Subgroup G, X ≤ ⁅U, oddOrderSubgroup H⁆ → H ≤ normalizer (X : Set G) →
      X = ⊥ ∨ X = ⁅U, oddOrderSubgroup H⁆ := by
    intro X hXI hHX
    by_cases hX : X = ⊥
    · exact Or.inl hX
    · refine Or.inr (le_antisymm hXI (hP1 X (hXI.trans hIU) hHX fun h0 => hX ?_))
      have := commutator_eq_bot_iff_le_centralizer.mp h0
      rw [← le_bot_iff, ← hICK]
      exact le_inf hXI this
  have hIQ : ⁅U, oddOrderSubgroup H⁆ ≤ Q := hIU.trans (hUQ₀.trans hQ₀Q)
  have hIe : CFSG.Open.IsElemAbelian 2 ⁅U, oddOrderSubgroup H⁆ := isElemAbelian_mono hUe hIU
  have hICQ : ⁅U, oddOrderSubgroup H⁆ ≤ centralizer (Q : Set G) := by
    have hX : H ≤ normalizer ((⁅U, oddOrderSubgroup H⁆ ⊓ centralizer (Q : Set G) : Subgroup G) :
        Set G) := le_normalizer_inf_of_le hHI fun h hh =>
      mem_normalizer_centralizer_of_mem_normalizer (hHQ hh)
    rcases hirr _ inf_le_left hX with h0 | h1
    · exfalso
      obtain ⟨v, hvI, hv1, hvQ⟩ := exists_mem_not_mem_forall_commutator_mem hQ2 hIQ
        (hQH.trans hHI) (fun h => hIne (le_bot_iff.mp h))
      have hvC : v ∈ centralizer (Q : Set G) := mem_centralizer_iff.mpr fun q hq =>
        (commutatorElement_eq_one_iff_mul_comm.mp (mem_bot.mp (hvQ q hq))).symm
      have hmem : v ∈ ⁅U, oddOrderSubgroup H⁆ ⊓ centralizer (Q : Set G) := ⟨hvI, hvC⟩
      rw [h0] at hmem
      exact hv1 hmem
    · exact h1 ▸ inf_le_right
  have hIH : ⁅U, oddOrderSubgroup H⁆ ≤ H := hIQ.trans hQH
  have hred : IsPrimeReduced 2 (⁅U, oddOrderSubgroup H⁆.subgroupOf H) := by
    refine (isPrimeReduced_iff_forall 2).mpr ⟨(normal_subgroupOf_iff_le_normalizer hIH).mpr hHI,
      isElementaryAbelian_subgroupOf_of_isElemAbelian hIe H, fun D' hD'n hD'2 => ?_⟩
    have hcent : ∀ y : ↥H, y ∈ centralizer ((⁅U, oddOrderSubgroup H⁆.subgroupOf H : Subgroup ↥H) :
        Set ↥H) ↔ (y : G) ∈ centralizer ((⁅U, oddOrderSubgroup H⁆ : Subgroup G) : Set G) := by
      intro y
      rw [mem_centralizer_iff, mem_centralizer_iff]
      constructor
      · intro h x hx
        exact congrArg Subtype.val (h ⟨x, hIH hx⟩ hx)
      · intro h x hx
        exact Subtype.ext (h x hx)
    have hDH : D'.map H.subtype ≤ H := Subgroup.map_subtype_le _
    have hHD : H ≤ normalizer ((D'.map H.subtype : Subgroup G) : Set G) := by
      apply le_normalizer_of_conj_mem_of_finite
      rintro h hh _ ⟨d, hd, rfl⟩
      exact ⟨⟨h, hh⟩ * d * ⟨h, hh⟩⁻¹, hD'n.conj_mem d hd _, rfl⟩
    have hD2 : ∀ d ∈ D'.map H.subtype, ∃ k : ℕ, d ^ 2 ^ k ∈
        centralizer ((⁅U, oddOrderSubgroup H⁆ : Subgroup G) : Set G) := by
      rintro _ ⟨d, hd, rfl⟩
      obtain ⟨k, hk⟩ := hD'2 d hd
      exact ⟨k, by simpa using (hcent _).mp hk⟩
    have hle := le_centralizer_of_irreducible hHI hIe hirr hDH hHD hD2
    intro d hd
    exact (hcent d).mpr (hle ⟨d, hd, rfl⟩)
  refine ⟨⟨hQ₀H, (normal_subgroupOf_iff_le_normalizer hQ₀H).mpr hHQ₀⟩, le_inf hUQ₀ hUCQ₀, hKR, ?_,
    hO2K.trans hP₀Q₀, hSyl, hJRT.symm, ?_, hIne, hHI, hirr, le_inf hIQ hICQ, hIH, hred⟩
  · rw [Wreath.elemThompsonIn_two_eq]
    exact hKJ
  · rw [Wreath.elemThompsonIn_two_eq]
    exact hJQ

end CFSG.Quasithin
