module

public import CFSG.Quasithin.Recognition.St84.J2LocalData
public import CFSG.Quasithin.Recognition.J2RecCzAut
public import CFSG.GH74.Uniqueness.SU.KI1r4QAbs
public import CFSG.Quasithin.Recognition.Kleidman.OrdinaryProofs.ModelFacts
public import CFSG.Quasithin.Background.GoldschmidtAmalgamNBasic
public import CFSG.ClassicalInvolution.RouteD.GapsAut

public section

namespace CFSG.Quasithin.F112R.St84

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits
open CFSG.Quasithin.J2Cz CFSG.Quasithin.J2Cz.QM
open Equiv F2

variable {G : Type} [Group G]

structure AutJ2Vertex (P L : Subgroup G) : Prop where
  le : L ≤ P
  relIndex : L.relIndex P = 2
  model : Nonempty (↥L ≃* Model)
  oTwo_le : pCoreOf 2 P ≤ L
  twist : ∃ u ∈ P, u ∉ L ∧ u ^ 2 = 1 ∧ ∃ v ∈ pCoreOf 2 L, v ^ 2 = 1 ∧
    v ∉ Subgroup.centralizer (pCoreOf 2 L : Set G) ∧ u * v = v * u

private noncomputable abbrev inrM : L0 →* Model := SemidirectProduct.inr

local instance decidableLiftRel (w : QM) (y : Fin 4 → QM) : Decidable (LiftRel w y) :=
  decidable_of_iff
    (w * w = 1 ∧ (∀ j, w * y j = y j * w) ∧ (∀ j, y j * y j = 1) ∧
      (∀ i j, i < j → y j * y i = w * (y i * y j)))
    ⟨fun h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩,
     fun h => ⟨h.w_sq, h.w_comm, h.y_sq, h.anti⟩⟩

theorem liftRel_signed : ∀ (σ : Perm (Fin 5)) (s : Fin 4 → F2),
    LiftRel z (fun j : Fin 4 => pw z (s j) * x (σ j.succ)) := by
  decide +kernel

@[expose] def thetaOneHom : QM →* QM :=
  (liftRel_signed (swap 0 1) (sgn4 o i o o)).liftHom

theorem thetaOneHom_sq : ∀ p : QM, thetaOneHom (thetaOneHom p) = p := by
  decide +kernel

@[expose] def thetaOne : MulAut QM where
  toFun := thetaOneHom
  invFun := thetaOneHom
  left_inv := thetaOneHom_sq
  right_inv := thetaOneHom_sq
  map_mul' := map_mul thetaOneHom

@[expose] def IsThetaExt (Θ : MulAut Model) : Prop :=
  ∀ q : QM, Θ (SemidirectProduct.inl q) = SemidirectProduct.inl (thetaOne q)

end CFSG.Quasithin.F112R.St84

namespace CFSG.Quasithin.J2Cz

open CFSG.Open CFSG.Quasithin.J2Cz.QM

theorem pCore_L0_eq_bot : CFSG.Open.pCore 2 L0 = ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  haveI : IsSimpleGroup ↥L0 := lineEquiv.isSimpleGroup
  rcases Subgroup.Normal.eq_bot_or_eq_top (CFSG.Open.pCore 2 L0) with h | h
  · exact h
  · exfalso
    have hL0 : Nat.card L0 = 60 := by
      rw [Nat.card_congr lineEquiv.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
      norm_num
    have hcard : Nat.card (CFSG.Open.pCore 2 L0) = 60 := by
      rw [h, Subgroup.card_top, hL0]
    obtain ⟨n, hn⟩ := (CFSG.LieType.BorelTits.pCore_isPGroup (G := ↥L0) 2).exists_card_eq
    rw [hcard] at hn
    have hn6 : n < 6 := by
      by_contra hge
      have hle : 2 ^ 6 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    interval_cases n <;> norm_num at hn

theorem pCore_model_eq_range_inl :
    CFSG.Open.pCore 2 Model = (SemidirectProduct.inl : QM →* Model).range := by
  apply le_antisymm
  · intro x hx
    have hmap := CFSG.LieType.BorelTits.map_pCore_le 2
      (SemidirectProduct.rightHom : Model →* L0) SemidirectProduct.rightHom_surjective
    have hx' : SemidirectProduct.rightHom x ∈ CFSG.Open.pCore 2 L0 := hmap ⟨x, hx, rfl⟩
    rw [pCore_L0_eq_bot, Subgroup.mem_bot] at hx'
    have hxker : x ∈ (SemidirectProduct.rightHom : Model →* L0).ker := MonoidHom.mem_ker.mpr hx'
    rwa [← SemidirectProduct.range_inl_eq_ker_rightHom] at hxker
  · have hnormal : (SemidirectProduct.inl : QM →* Model).range.Normal := by
      rw [SemidirectProduct.range_inl_eq_ker_rightHom]
      infer_instance
    have hp : IsPGroup 2 (SemidirectProduct.inl : QM →* Model).range := by
      have hcard : Nat.card (SemidirectProduct.inl : QM →* Model).range = 32 := by
        have e : QM ≃* (SemidirectProduct.inl : QM →* Model).range :=
          MonoidHom.ofInjective (f := (SemidirectProduct.inl : QM →* Model))
            SemidirectProduct.inl_injective
        rw [← Nat.card_congr e.toEquiv, card_QM]
      exact IsPGroup.of_card (n := 5) (by rw [hcard]; norm_num)
    exact CFSG.LieType.BorelTits.le_pCore (r := 2) hnormal hp

theorem eq_one_or_eq_inl_z_of_commute_inl {m : Model}
    (h : ∀ q : QM, m * SemidirectProduct.inl q = SemidirectProduct.inl q * m) :
    m = 1 ∨ m = SemidirectProduct.inl z := by
  let a : QM := m.left
  let l : L0 := m.right
  have hm : m = SemidirectProduct.inl a * SemidirectProduct.inr l :=
    (SemidirectProduct.inl_left_mul_inr_right m).symm
  have hcomm : ∀ q : QM, a * (l : MulAut QM) q = q * a := by
    intro q
    have hq := h q
    rw [hm] at hq
    have h1 : (SemidirectProduct.inr l * SemidirectProduct.inl q : Model) =
        SemidirectProduct.inl ((l : MulAut QM) q) * SemidirectProduct.inr l := by
      ext <;> simp
    have hq2 : (SemidirectProduct.inl (a * (l : MulAut QM) q) *
        SemidirectProduct.inr l : Model) =
        SemidirectProduct.inl (q * a) * SemidirectProduct.inr l := by
      calc (SemidirectProduct.inl (a * (l : MulAut QM) q) *
            SemidirectProduct.inr l : Model)
          = SemidirectProduct.inl a *
              (SemidirectProduct.inl ((l : MulAut QM) q) *
                SemidirectProduct.inr l) := by rw [map_mul]; group
        _ = SemidirectProduct.inl a *
              (SemidirectProduct.inr l * SemidirectProduct.inl q) := by rw [h1]
        _ = (SemidirectProduct.inl a * SemidirectProduct.inr l) *
              SemidirectProduct.inl q := by group
        _ = SemidirectProduct.inl q *
              (SemidirectProduct.inl a * SemidirectProduct.inr l) := hq
        _ = SemidirectProduct.inl q * SemidirectProduct.inl a *
              SemidirectProduct.inr l := by group
        _ = SemidirectProduct.inl (q * a) * SemidirectProduct.inr l := by rw [map_mul]
    have h2 : (SemidirectProduct.inl (a * (l : MulAut QM) q) : Model) =
        (SemidirectProduct.inl (q * a) : Model) := by
      have := congrArg (fun x : Model => x * (SemidirectProduct.inr l)⁻¹) hq2
      simpa [mul_assoc] using this
    exact SemidirectProduct.inl_injective h2
  have hl : (l : MulAut QM) = MulAut.conj a⁻¹ := by
    refine MulEquiv.ext fun q => ?_
    have hq := hcomm q
    rw [MulAut.conj_apply]
    calc (l : MulAut QM) q = a⁻¹ * (a * (l : MulAut QM) q) := by group
      _ = a⁻¹ * (q * a) := by rw [hq]
      _ = a⁻¹ * q * (a⁻¹)⁻¹ := by group
  have hl1 : MulAut.conj a⁻¹ = 1 := by
    apply eq_one_of_conj_mem_L0
    rw [← hl]
    exact l.2
  have hlsub : l = 1 := by
    apply Subtype.ext
    rw [hl, hl1]
    rfl
  have hacent : ∀ q : QM, a * q = q * a := by
    intro q
    have h1 : a⁻¹ * q * a = q := by
      have := congrArg (fun f : MulAut QM => f q) hl1
      rw [MulAut.conj_apply, MulAut.one_apply] at this
      simpa using this
    calc a * q = a * (a⁻¹ * q * a) := by rw [h1]
      _ = q * a := by group
  rcases eq_of_comm_x a (fun j => hacent (x j)) with ha | ha
  · left
    rw [hm, hlsub, ha]
    simp
  · right
    rw [hm, hlsub, ha]
    simp

variable {G : Type} [Group G]

theorem map_pCore_eq_inl_range {L : Subgroup G} (Ψ : ↥L ≃* Model) :
    (CFSG.Open.pCore 2 ↥L).map Ψ.toMonoidHom =
      (SemidirectProduct.inl : QM →* Model).range := by
  rw [CFSG.LieType.BorelTits.map_pCore_mulEquiv, pCore_model_eq_range_inl]

theorem mem_pCoreOf_iff_mem_range_inl {L : Subgroup G} (Ψ : ↥L ≃* Model) {c : G}
    (hcL : c ∈ L) :
    c ∈ pCoreOf 2 L ↔
      Ψ ⟨c, hcL⟩ ∈ (SemidirectProduct.inl : QM →* Model).range := by
  constructor
  · intro hcQ
    obtain ⟨x, hx, hxc⟩ := Subgroup.mem_map.mp hcQ
    have hxeq : x = ⟨c, hcL⟩ := Subtype.ext hxc
    rw [← hxeq, ← map_pCore_eq_inl_range Ψ]
    exact Subgroup.mem_map_of_mem Ψ.toMonoidHom hx
  · intro hΨ
    rw [← map_pCore_eq_inl_range Ψ] at hΨ
    obtain ⟨x, hx, hxeq⟩ := Subgroup.mem_map.mp hΨ
    have hxeq' : x = ⟨c, hcL⟩ := Ψ.injective hxeq
    rw [hxeq'] at hx
    exact Subgroup.mem_map_of_mem L.subtype hx

end CFSG.Quasithin.J2Cz

namespace CFSG.Quasithin.F112R.St84

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits
open CFSG.Quasithin.J2Cz CFSG.Quasithin.J2Cz.QM
open Equiv F2

variable {G : Type} [Group G]

private theorem inv_mul_apply_mem_center_of_fixes_inl {Δ : MulAut Model}
    (hΔ : ∀ q : QM, Δ (SemidirectProduct.inl q : Model) = SemidirectProduct.inl q) (m : Model) :
    m⁻¹ * Δ m ∈ Subgroup.center Model := by
  have hcomm : ∀ q : QM,
      (m⁻¹ * Δ m) * (SemidirectProduct.inl q : Model) =
        SemidirectProduct.inl q * (m⁻¹ * Δ m) := by
    intro q
    have hnormal : (SemidirectProduct.inl : QM →* Model).range.Normal := by
      rw [SemidirectProduct.range_inl_eq_ker_rightHom]
      infer_instance
    have hmem : (m * SemidirectProduct.inl q * m⁻¹ : Model) ∈
        (SemidirectProduct.inl : QM →* Model).range :=
      hnormal.conj_mem _ ⟨q, rfl⟩ m
    obtain ⟨q', hq'⟩ := hmem
    have hq'm : (m * SemidirectProduct.inl q : Model) =
        SemidirectProduct.inl q' * m := by
      calc (m * SemidirectProduct.inl q : Model)
          = (m * SemidirectProduct.inl q * m⁻¹) * m := by group
        _ = SemidirectProduct.inl q' * m := by
            rw [show (m * SemidirectProduct.inl q * m⁻¹ : Model) = SemidirectProduct.inl q'
              from hq'.symm]
    calc (m⁻¹ * Δ m) * (SemidirectProduct.inl q : Model)
        = m⁻¹ * (Δ m * SemidirectProduct.inl q) := by group
      _ = m⁻¹ * (Δ m * Δ (SemidirectProduct.inl q)) := by rw [hΔ q]
      _ = m⁻¹ * Δ (m * SemidirectProduct.inl q) := by rw [map_mul]
      _ = m⁻¹ * Δ (SemidirectProduct.inl q' * m) := by rw [hq'm]
      _ = m⁻¹ * (Δ (SemidirectProduct.inl q') * Δ m) := by rw [map_mul]
      _ = m⁻¹ * (SemidirectProduct.inl q' * Δ m) := by rw [hΔ q']
      _ = (m⁻¹ * SemidirectProduct.inl q') * Δ m := by group
      _ = (SemidirectProduct.inl q * m⁻¹) * Δ m := by
        have hq'' : (m⁻¹ * SemidirectProduct.inl q' : Model) =
            SemidirectProduct.inl q * m⁻¹ := by
          calc (m⁻¹ * SemidirectProduct.inl q' : Model)
              = m⁻¹ * (m * SemidirectProduct.inl q * m⁻¹) := by rw [hq']
            _ = SemidirectProduct.inl q * m⁻¹ := by group
        rw [hq'']
      _ = SemidirectProduct.inl q * (m⁻¹ * Δ m) := by group
  rcases eq_one_or_eq_inl_z_of_commute_inl hcomm with h | h
  · rw [h]
    exact Subgroup.one_mem _
  · rw [h]
    exact CFSG.Quasithin.Recognition.Kleidman.OrdinaryProofs.inl_z_mem_center

theorem IsThetaExt.unique {Θ Θ' : MulAut Model} (h : IsThetaExt Θ) (h' : IsThetaExt Θ') :
    Θ = Θ' := by
  let Δ : MulAut Model := Θ⁻¹ * Θ'
  have hperfL0 : Group.IsPerfect ↥L0 := by
    have h5 : 5 ≤ Nat.card (Fin 5) := by simp
    have hperfAlt : Group.IsPerfect (alternatingGroup (Fin 5)) :=
      Subgroup.isPerfect_iff.mpr (commutator_alternatingGroup_eq_self h5)
    exact Group.IsPerfect.ofSurjective (f := lineEquiv.symm.toMonoidHom)
      lineEquiv.symm.surjective
  haveI : Group.IsPerfect ↥L0 := hperfL0
  have hΔ : ∀ q : QM, Δ (SemidirectProduct.inl q : Model) = SemidirectProduct.inl q := by
    intro q
    calc Δ (SemidirectProduct.inl q : Model)
        = Θ⁻¹ (Θ' (SemidirectProduct.inl q)) := rfl
      _ = Θ⁻¹ (SemidirectProduct.inl (thetaOne q)) := by rw [h' q]
      _ = SemidirectProduct.inl q := by
        rw [← h q, MulAut.inv_apply, MulEquiv.symm_apply_apply]
  have hperf : Group.IsPerfect inrM.range := Group.IsPerfect.range _
  haveI : Group.IsPerfect ↥inrM.range := hperf
  have hfix : ∀ f ∈ inrM.range, Δ f = f := by
    refine CFSG.ClassicalInvolution.RouteD.Gaps.fixed_of_perfect_of_central
      Δ.toMonoidHom (N := inrM.range) hperf (Z := Subgroup.center Model) le_rfl ?_
    intro f _
    exact inv_mul_apply_mem_center_of_fixes_inl hΔ f
  have hΔ1 : Δ = 1 := by
    refine MulEquiv.ext fun m => ?_
    conv_lhs => rw [← SemidirectProduct.inl_left_mul_inr_right m]
    rw [map_mul, hΔ m.left, hfix _ ⟨m.right, rfl⟩]
    exact SemidirectProduct.inl_left_mul_inr_right m
  have h : Θ⁻¹ * Θ' = 1 := hΔ1
  calc Θ = Θ * (Θ⁻¹ * Θ') := by rw [h, mul_one]
    _ = Θ' := by group

private def c3 : Perm (Fin 5) := swap 2 3 * swap 3 4

private theorem check_transp_sign : ∀ σ : Perm (Fin 5), σ * σ = 1 → Perm.sign σ ≠ 1 →
    ∃ c : Perm (Fin 5), Perm.sign c = 1 ∧ c * σ * c⁻¹ = swap 0 1 := by
  decide +kernel

private theorem check_transp : ∀ σ : Perm (Fin 5), σ * σ = 1 → σ ∉ alternatingGroup (Fin 5) →
    ∃ c ∈ alternatingGroup (Fin 5), c * σ * c⁻¹ = swap 0 1 := by
  intro σ hσ hodd
  obtain ⟨c, hc, hconj⟩ := check_transp_sign σ hσ (fun hs => hodd (by
    rw [Equiv.Perm.mem_alternatingGroup]; exact hs))
  exact ⟨c, by rw [Equiv.Perm.mem_alternatingGroup]; exact hc, hconj⟩

private theorem check_twist : ∀ s₀ s₁ s₂ s₃ : F2,
    (∀ j : Fin 4, autS (swap 0 1) (sgn4 s₀ s₁ s₂ s₃)
      (autS (swap 0 1) (sgn4 s₀ s₁ s₂ s₃) (x j.succ)) = x j.succ) →
    (∃ j : Fin 5, autS (swap 0 1) (sgn4 s₀ s₁ s₂ s₃) (x j) = x j) →
    ∃ n : Fin 3, ∃ t₀ t₁ t₂ t₃ : F2, ∀ j : Fin 4,
      innerOf t₀ t₁ t₂ t₃ * autS (c3 ^ (n : ℕ)) (sgn4 o o o o)
          (autS (swap 0 1) (sgn4 s₀ s₁ s₂ s₃) (x j.succ)) * (innerOf t₀ t₁ t₂ t₃)⁻¹ =
        thetaOne (innerOf t₀ t₁ t₂ t₃ * autS (c3 ^ (n : ℕ)) (sgn4 o o o o) (x j.succ) *
          (innerOf t₀ t₁ t₂ t₃)⁻¹) := by
  decide +kernel

private noncomputable def zmodTwoAct (Θ : MulAut Model) (hΘ : Θ * Θ = 1) :
    Multiplicative (ZMod 2) →* MulAut Model where
  toFun c := if c = 1 then 1 else Θ
  map_one' := by simp
  map_mul' := by
    intro a b
    have hcases : ∀ c : Multiplicative (ZMod 2),
        c = 1 ∨ c = Multiplicative.ofAdd 1 := by decide
    have hne : (Multiplicative.ofAdd (1 : ZMod 2)) ≠ 1 := by decide
    have hsq : (Multiplicative.ofAdd (1 : ZMod 2)) * Multiplicative.ofAdd 1 = 1 := by decide
    rcases hcases a with rfl | rfl <;> rcases hcases b with rfl | rfl
    · simp
    · simp
    · simp
    · rw [hsq]
      simp [hne, hΘ]

private theorem zmodTwoAct_one (Θ : MulAut Model) (hΘ : Θ * Θ = 1) :
    zmodTwoAct Θ hΘ (Multiplicative.ofAdd 1) = Θ := by
  simp [zmodTwoAct]

theorem AutJ2Vertex.le_normalizer {P L : Subgroup G} (h : AutJ2Vertex P L) :
    P ≤ Subgroup.normalizer (L : Set G) := by
  have hnorm : (L.subgroupOf P).Normal := Subgroup.normal_of_index_eq_two h.relIndex
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer h.le).mp hnorm

private theorem AutJ2Vertex.inf_centralizer_le {P L : Subgroup G} (h : AutJ2Vertex P L) :
    (P ⊓ Subgroup.centralizer (pCoreOf 2 L : Set G)) ⊓ L ≤ pCoreOf 2 L := by
  obtain ⟨Ψ₀⟩ := h.model
  let Q : Subgroup G := pCoreOf 2 L
  let C : Subgroup G := P ⊓ Subgroup.centralizer (Q : Set G)
  change C ⊓ L ≤ Q
  intro c hc
  obtain ⟨hcC, hcL⟩ := hc
  obtain ⟨hcP, hcCent⟩ := hcC
  apply (mem_pCoreOf_iff_mem_range_inl Ψ₀ hcL).mpr
  have hcomm : ∀ q : QM,
      Ψ₀ ⟨c, hcL⟩ * (SemidirectProduct.inl q : Model) =
        (SemidirectProduct.inl q : Model) * Ψ₀ ⟨c, hcL⟩ := by
    intro q
    have hq : (SemidirectProduct.inl q : Model) ∈
        (SemidirectProduct.inl : QM →* Model).range := ⟨q, rfl⟩
    rw [← map_pCore_eq_inl_range Ψ₀] at hq
    obtain ⟨x, hx, hxeq⟩ := Subgroup.mem_map.mp hq
    have hxQ : (x : G) ∈ Q := Subgroup.mem_map_of_mem L.subtype hx
    have hc_x : c * (x : G) = (x : G) * c :=
      ((Subgroup.mem_centralizer_iff.mp hcCent) (x : G) hxQ).symm
    have hc_xL : (⟨c, hcL⟩ : ↥L) * x = x * ⟨c, hcL⟩ := Subtype.ext hc_x
    calc (Ψ₀ ⟨c, hcL⟩ * (SemidirectProduct.inl q : Model))
        = Ψ₀ ⟨c, hcL⟩ * Ψ₀ x := by
            rw [show (SemidirectProduct.inl q : Model) = Ψ₀.toMonoidHom x from hxeq.symm]
            rfl
      _ = Ψ₀ ((⟨c, hcL⟩ : ↥L) * x) := by rw [map_mul]
      _ = Ψ₀ (x * ⟨c, hcL⟩) := by rw [hc_xL]
      _ = Ψ₀ x * Ψ₀ ⟨c, hcL⟩ := by rw [map_mul]
      _ = (SemidirectProduct.inl q : Model) * Ψ₀ ⟨c, hcL⟩ := by
            change Ψ₀.toMonoidHom x * Ψ₀ ⟨c, hcL⟩ = _
            rw [hxeq]
  rcases eq_one_or_eq_inl_z_of_commute_inl hcomm with hm | hm
  · rw [hm]
    exact ⟨1, rfl⟩
  · rw [hm]
    exact ⟨z, rfl⟩

theorem AutJ2Vertex.centralizer_le [Finite G] {P L : Subgroup G} (h : AutJ2Vertex P L) :
    P ⊓ Subgroup.centralizer (pCoreOf 2 L : Set G) ≤ L := by
  let Q : Subgroup G := pCoreOf 2 L
  let C : Subgroup G := P ⊓ Subgroup.centralizer (Q : Set G)
  have hCL : C ⊓ L ≤ Q := AutJ2Vertex.inf_centralizer_le h
  have hPnormQ : P ≤ Subgroup.normalizer (Q : Set G) :=
    h.le_normalizer.trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
        (H := L) (K := CFSG.Open.pCore 2 ↥L))
  have hPnormCQ : P ≤ Subgroup.normalizer (Subgroup.centralizer (Q : Set G) : Set G) :=
    hPnormQ.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer
      (Subgroup.centralizer_le_normalizer (Q : Set G))).mp
      (Subgroup.normal_subgroupOf_centralizer_normalizer (Q : Set G)))
  have hCnorm : P ≤ Subgroup.normalizer (C : Set G) := by
    have h1 : P ≤ Subgroup.normalizer (Subgroup.centralizer (Q : Set G) : Set G) ⊓
        Subgroup.normalizer (P : Set G) :=
      le_inf hPnormCQ Subgroup.le_normalizer
    have h2 := h1.trans (Subgroup.inf_normalizer_le_normalizer_inf
      (H := Subgroup.centralizer (Q : Set G)) (K := P))
    simpa [C, inf_comm] using h2
  have hQ2 : IsPGroup 2 Q := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L
  have hD2 : IsPGroup 2 ↥(C ⊓ L) := hQ2.to_le hCL
  have hLCnorm : (L.subgroupOf C).Normal := by
    rw [← Subgroup.inf_subgroupOf_right L C]
    rw [Subgroup.normal_subgroupOf_iff inf_le_right]
    intro x y hx hy
    exact ⟨(Subgroup.mem_normalizer_iff.mp
      (h.le_normalizer ((show C ≤ P from inf_le_left) hy)) x).mp hx.1,
      C.mul_mem (C.mul_mem hy hx.2) (C.inv_mem hy)⟩
  have hDnorm : ((C ⊓ L).subgroupOf C).Normal := by
    rw [inf_comm, Subgroup.inf_subgroupOf_right]
    exact hLCnorm
  haveI : ((C ⊓ L).subgroupOf C).Normal := hDnorm
  have hrelC : (C ⊓ L).relIndex C ≤ 2 := by
    rw [Subgroup.inf_relIndex_left]
    have hle : L.relIndex C ≤ L.relIndex P :=
      Subgroup.relIndex_le_of_le_right (show C ≤ P from inf_le_left) (by
        rw [h.relIndex]; norm_num)
    exact hle.trans (le_of_eq h.relIndex)
  have hquot : IsPGroup 2 (C ⧸ ((C ⊓ L : Subgroup G).subgroupOf C)) := by
    apply IsPGroup.of_card_dvd_pow (n := 1)
    have hcard : Nat.card (C ⧸ ((C ⊓ L : Subgroup G).subgroupOf C)) =
        ((C ⊓ L : Subgroup G).subgroupOf C).index := rfl
    have hle : Nat.card (C ⧸ ((C ⊓ L : Subgroup G).subgroupOf C)) ≤ 2 := by
      rw [hcard]
      exact hrelC
    have hpos : 0 < Nat.card (C ⧸ ((C ⊓ L : Subgroup G).subgroupOf C)) := Nat.card_pos
    have hcases : Nat.card (C ⧸ ((C ⊓ L : Subgroup G).subgroupOf C)) = 1 ∨
        Nat.card (C ⧸ ((C ⊓ L : Subgroup G).subgroupOf C)) = 2 := by omega
    rcases hcases with hcase | hcase <;> rw [hcase] <;> norm_num
  have hC2 : IsPGroup 2 C :=
    CFSG.BenderSuzuki.External.hkt_isPGroup_of_normal_quotient
      ((C ⊓ L : Subgroup G).subgroupOf C)
      (hD2.of_equiv (Subgroup.subgroupOfEquivOfLe inf_le_left).symm) hquot
  exact (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer (r := 2)
    (N := C) (H := P) inf_le_left hCnorm hC2).trans h.oTwo_le

private theorem exists_inl_restrict (Θ : MulAut Model) :
    ∃ φ : MulAut QM, ∀ q : QM,
      Θ (SemidirectProduct.inl q) = SemidirectProduct.inl (φ q) := by
  let eInl : QM ≃* (SemidirectProduct.inl : QM →* Model).range :=
    MonoidHom.ofInjective (f := (SemidirectProduct.inl : QM →* Model))
      SemidirectProduct.inl_injective
  have hΘmap : ((SemidirectProduct.inl : QM →* Model).range).map Θ.toMonoidHom =
      (SemidirectProduct.inl : QM →* Model).range := by
    rw [← pCore_model_eq_range_inl]
    exact CFSG.LieType.BorelTits.map_pCore_mulEquiv (r := 2) Θ
  let Θr : MulAut (SemidirectProduct.inl : QM →* Model).range :=
    (MulEquiv.subgroupMap Θ (SemidirectProduct.inl : QM →* Model).range).trans
      (MulEquiv.subgroupCongr hΘmap)
  let φ : MulAut QM := (MulAut.congr eInl).symm Θr
  refine ⟨φ, fun q => ?_⟩
  have h2 : eInl (φ q) = Θr (eInl q) := by
    simp [φ, MulAut.congr]
  have h3 : ((eInl (φ q) : (SemidirectProduct.inl : QM →* Model).range) : Model) =
      Θ (SemidirectProduct.inl q) := by
    rw [h2]
    rfl
  exact h3.symm

private theorem parAct_mul_self {P L : Subgroup G}
    (hPL : P ≤ Subgroup.normalizer (L : Set G)) (Ψ : ↥L ≃* Model) (x : ↥P)
    (hx : x * x = 1) : parAct hPL Ψ x * parAct hPL Ψ x = 1 := by
  rw [← map_mul, hx, map_one]

private theorem parAct_conj_apply {P L : Subgroup G}
    (hPL : P ≤ Subgroup.normalizer (L : Set G)) (Ψ : ↥L ≃* Model) (x : ↥P) (n : Model) :
    ((Ψ.symm (parAct hPL Ψ x n) : ↥L) : G) =
      (x : G) * ((Ψ.symm n : ↥L) : G) * (x : G)⁻¹ := by
  rw [parAct_apply, MulEquiv.symm_apply_apply]

private theorem linePerm_not_mem_alternating [Finite G] {P L : Subgroup G}
    (h : AutJ2Vertex P L) {u : G} (huP : u ∈ P) (huL : u ∉ L) (Ψ : ↥L ≃* Model)
    (φ : MulAut QM)
    (hφ : ∀ q : QM, parAct h.le_normalizer Ψ ⟨u, huP⟩ (SemidirectProduct.inl q) =
      SemidirectProduct.inl (φ q)) :
    linePerm φ ∉ alternatingGroup (Fin 5) := by
  intro hline
  let l0 : ↥L0 := lineEquiv.symm ⟨linePerm φ, hline⟩
  have hl0' : linePerm (l0 : MulAut QM) = linePerm φ :=
    linePerm_lineEquiv_symm ⟨linePerm φ, hline⟩
  have h1 : linePerm ((l0 : MulAut QM)⁻¹ * φ) = 1 := by
    change linePermHom ((l0 : MulAut QM)⁻¹ * φ) = 1
    rw [map_mul, map_inv]
    rw [show linePermHom (l0 : MulAut QM) = linePerm φ from hl0']
    exact inv_mul_cancel _
  obtain ⟨a, ha⟩ := eq_conj_of_linePerm_eq_one h1
  have hφeq : φ = MulAut.conj ((l0 : MulAut QM) a) * l0 := by
    have h2 : φ = (l0 : MulAut QM) * MulAut.conj a := by
      calc φ = (l0 : MulAut QM) * ((l0 : MulAut QM)⁻¹ * φ) := by group
        _ = (l0 : MulAut QM) * MulAut.conj a := by rw [ha]
    rw [h2]
    refine MulEquiv.ext fun q => ?_
    simp [MulAut.conj_apply, map_mul, map_inv, mul_assoc]
  let g : Model :=
    SemidirectProduct.inl ((l0 : MulAut QM) a) * SemidirectProduct.inr l0
  have hΘg : ∀ q : QM, parAct h.le_normalizer Ψ ⟨u, huP⟩ (SemidirectProduct.inl q) =
      g * SemidirectProduct.inl q * g⁻¹ := by
    intro q
    rw [hφ q, hφeq]
    have hg : (g * SemidirectProduct.inl q * g⁻¹ : Model) =
        SemidirectProduct.inl ((MulAut.conj ((l0 : MulAut QM) a) * l0) q) := by
      ext <;> simp [g, MulAut.conj_apply, map_mul, map_inv, mul_assoc]
    rw [hg]
  let gL : ↥L := Ψ.symm g
  have hΨg : Ψ gL = g := MulEquiv.apply_symm_apply Ψ g
  have hwCent : gL⁻¹ * u ∈ Subgroup.centralizer (pCoreOf 2 L : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro c hc
    have hcL : c ∈ L := CFSG.LieType.BorelTits.pCoreOf_le 2 L hc
    let x : ↥L := ⟨c, hcL⟩
    obtain ⟨q, hq⟩ := (mem_pCoreOf_iff_mem_range_inl Ψ hcL).mp hc
    have huc : u * c * u⁻¹ = (gL : G) * c * (gL : G)⁻¹ := by
      have hxeq : (⟨u * c * u⁻¹,
          (Subgroup.mem_normalizer_iff.mp (h.le_normalizer huP) c).mp hcL⟩ : ↥L) =
          gL * x * gL⁻¹ := by
        apply Ψ.injective
        have hpar := parAct_apply (P := P) (Q := L) (hPQ := h.le_normalizer) (χ := Ψ)
          ⟨u, huP⟩ (Ψ x)
        have hpar' : Ψ ⟨u * c * u⁻¹,
            (Subgroup.mem_normalizer_iff.mp (h.le_normalizer huP) c).mp hcL⟩ =
            parAct h.le_normalizer Ψ ⟨u, huP⟩ (Ψ x) := by
          simpa [x, MulEquiv.symm_apply_apply] using hpar.symm
        calc Ψ ⟨u * c * u⁻¹,
              (Subgroup.mem_normalizer_iff.mp (h.le_normalizer huP) c).mp hcL⟩
            = parAct h.le_normalizer Ψ ⟨u, huP⟩ (Ψ x) := hpar'
          _ = g * (SemidirectProduct.inl q : Model) * g⁻¹ := by
              rw [show Ψ x = (SemidirectProduct.inl q : Model) from hq.symm]
              exact hΘg q
          _ = Ψ (gL * x * gL⁻¹) := by
              calc g * (SemidirectProduct.inl q : Model) * g⁻¹
                  = g * Ψ x * g⁻¹ := by
                      rw [show (SemidirectProduct.inl q : Model) = Ψ x from hq]
                _ = Ψ gL * Ψ x * (Ψ gL)⁻¹ := by rw [hΨg]
                _ = Ψ (gL * x * gL⁻¹) := by rw [map_mul, map_mul, map_inv]
      exact congrArg Subtype.val hxeq
    have hconj : ((gL : G)⁻¹ * u) * c * ((gL : G)⁻¹ * u)⁻¹ = c := by
      calc ((gL : G)⁻¹ * u) * c * ((gL : G)⁻¹ * u)⁻¹
          = (gL : G)⁻¹ * (u * c * u⁻¹) * (gL : G) := by group
        _ = (gL : G)⁻¹ * ((gL : G) * c * (gL : G)⁻¹) * (gL : G) := by rw [huc]
        _ = c := by group
    calc c * ((gL : G)⁻¹ * u) = (((gL : G)⁻¹ * u) * c * ((gL : G)⁻¹ * u)⁻¹) *
          ((gL : G)⁻¹ * u) := by rw [hconj]
      _ = ((gL : G)⁻¹ * u) * c := by group
  have hwP : (gL : G)⁻¹ * u ∈ P := P.mul_mem (P.inv_mem (h.le gL.2)) huP
  have hwL : (gL : G)⁻¹ * u ∈ L := h.centralizer_le ⟨hwP, hwCent⟩
  have huL' : u ∈ L := by
    have h : u = (gL : G) * ((gL : G)⁻¹ * u) := by group
    rw [h]
    exact L.mul_mem gL.2 hwL
  exact huL huL'

private theorem exists_fixed_line {P L : Subgroup G} (h : AutJ2Vertex P L) {u v : G}
    (huP : u ∈ P) (hvQ : v ∈ pCoreOf 2 L) (hv2 : v ^ 2 = 1)
    (hvn : v ∉ Subgroup.centralizer (pCoreOf 2 L : Set G)) (huv : u * v = v * u)
    (Ψ : ↥L ≃* Model) (φ : MulAut QM)
    (hφ : ∀ q : QM, parAct h.le_normalizer Ψ ⟨u, huP⟩ (SemidirectProduct.inl q) =
      SemidirectProduct.inl (φ q)) :
    ∃ j : Fin 5, φ (x j) = x j := by
  have hvL : v ∈ L := CFSG.LieType.BorelTits.pCoreOf_le 2 L hvQ
  obtain ⟨q, hq⟩ := (mem_pCoreOf_iff_mem_range_inl Ψ hvL).mp hvQ
  have hv2' : (⟨v, hvL⟩ : ↥L) * ⟨v, hvL⟩ = 1 := by
    ext
    simpa [pow_two] using hv2
  have hq2 : q * q = 1 := by
    apply SemidirectProduct.inl_injective (φ := L0.subtype)
    calc SemidirectProduct.inl (q * q)
        = SemidirectProduct.inl q * SemidirectProduct.inl q := by rw [map_mul]
      _ = Ψ ⟨v, hvL⟩ * Ψ ⟨v, hvL⟩ := by rw [hq]
      _ = Ψ (⟨v, hvL⟩ * ⟨v, hvL⟩) := by rw [map_mul]
      _ = Ψ 1 := by rw [hv2']
      _ = 1 := map_one Ψ
  have hq_ne_one : q ≠ 1 := by
    intro hq1
    have hv1 : v = 1 := by
      have h1 : (⟨v, hvL⟩ : ↥L) = 1 := by
        apply Ψ.injective
        rw [← hq, hq1, map_one]
        exact (map_one Ψ).symm
      exact congrArg Subtype.val h1
    apply hvn
    rw [hv1]
    exact Subgroup.one_mem _
  have hq_ne_z : q ≠ z := by
    intro hqz
    apply hvn
    rw [Subgroup.mem_centralizer_iff]
    intro c hc
    have hcL : c ∈ L := CFSG.LieType.BorelTits.pCoreOf_le 2 L hc
    obtain ⟨qc, hqc⟩ := (mem_pCoreOf_iff_mem_range_inl Ψ hcL).mp hc
    have hcomm : (⟨v, hvL⟩ : ↥L) * ⟨c, hcL⟩ = ⟨c, hcL⟩ * ⟨v, hvL⟩ := by
      apply Ψ.injective
      calc Ψ ((⟨v, hvL⟩ : ↥L) * ⟨c, hcL⟩)
          = Ψ ⟨v, hvL⟩ * Ψ ⟨c, hcL⟩ := by rw [map_mul]
        _ = (SemidirectProduct.inl z : Model) * (SemidirectProduct.inl qc : Model) := by
            rw [← hq, hqz, ← hqc]
        _ = (SemidirectProduct.inl qc : Model) * (SemidirectProduct.inl z : Model) := by
            exact (Subgroup.mem_center_iff.mp
              CFSG.Quasithin.Recognition.Kleidman.OrdinaryProofs.inl_z_mem_center
              (SemidirectProduct.inl qc)).symm
        _ = Ψ ⟨c, hcL⟩ * Ψ ⟨v, hvL⟩ := by rw [hqc, ← hq, hqz]
        _ = Ψ ((⟨c, hcL⟩ : ↥L) * ⟨v, hvL⟩) := by rw [map_mul]
    exact (congrArg Subtype.val hcomm).symm
  have hfix_q : φ q = q := by
    apply SemidirectProduct.inl_injective (φ := L0.subtype)
    rw [← hφ q]
    have hpar := parAct_apply (P := P) (Q := L) (hPQ := h.le_normalizer) (χ := Ψ)
      ⟨u, huP⟩ (Ψ ⟨v, hvL⟩)
    rw [show (SemidirectProduct.inl q : Model) = Ψ ⟨v, hvL⟩ from hq]
    rw [hpar]
    simp only [MulEquiv.symm_apply_apply]
    congr 1
    ext
    calc u * v * u⁻¹ = v * u * u⁻¹ := by rw [huv]
      _ = v := by group
  rcases eq_x_of_sq q hq2 hq_ne_one hq_ne_z with ⟨j, hqj | hqj⟩
  · refine ⟨j, ?_⟩
    rw [← hqj, hfix_q]
  · refine ⟨j, ?_⟩
    have h1 : φ (z * x j) = z * x j := by rw [← hqj, hfix_q]
    rw [map_mul, aut_z] at h1
    exact mul_left_cancel h1

private theorem exists_conj_perm_swap_of_odd (φ : MulAut QM) (hφsq : φ * φ = 1)
    (hline_odd : linePerm φ ∉ alternatingGroup (Fin 5))
    (hfixline : ∃ j : Fin 5, φ (x j) = x j) :
    ∃ l0 : ↥L0, ∃ φ₁ : MulAut QM,
      φ₁ = (l0 : MulAut QM) * φ * (l0 : MulAut QM)⁻¹ ∧
      linePerm φ₁ = swap 0 1 ∧ φ₁ * φ₁ = 1 ∧ ∃ j, φ₁ (x j) = x j := by
  have hσ2 : linePerm φ * linePerm φ = 1 := by
    change linePermHom φ * linePermHom φ = 1
    rw [← map_mul, hφsq, map_one]
  obtain ⟨c, hc, hconj⟩ := check_transp (linePerm φ) hσ2 hline_odd
  let l0 : ↥L0 := lineEquiv.symm ⟨c, hc⟩
  have hl0 : linePerm (l0 : MulAut QM) = c := linePerm_lineEquiv_symm ⟨c, hc⟩
  let φ₁ : MulAut QM := (l0 : MulAut QM) * φ * (l0 : MulAut QM)⁻¹
  have hφ₁perm : linePerm φ₁ = swap 0 1 := by
    change linePermHom ((l0 : MulAut QM) * φ * (l0 : MulAut QM)⁻¹) = swap 0 1
    rw [map_mul, map_mul, map_inv]
    rw [show linePermHom (l0 : MulAut QM) = c from hl0]
    exact hconj
  have hφ₁sq : φ₁ * φ₁ = 1 := by
    change ((l0 : MulAut QM) * φ * (l0 : MulAut QM)⁻¹) *
      ((l0 : MulAut QM) * φ * (l0 : MulAut QM)⁻¹) = 1
    calc ((l0 : MulAut QM) * φ * (l0 : MulAut QM)⁻¹) *
        ((l0 : MulAut QM) * φ * (l0 : MulAut QM)⁻¹)
        = (l0 : MulAut QM) * (φ * φ) * (l0 : MulAut QM)⁻¹ := by group
      _ = 1 := by rw [hφsq]; group
  obtain ⟨jfix, hfix⟩ := hfixline
  refine ⟨l0, φ₁, rfl, hφ₁perm, hφ₁sq, c jfix, ?_⟩
  have hlj : (l0 : MulAut QM) (x jfix) = x (c jfix) := by
    rw [show (l0 : MulAut QM) (x jfix) =
      x (linePerm (l0 : MulAut QM) jfix) from (mem_L0.mp l0.2) jfix]
    rw [hl0]
  have hlinv : (l0 : MulAut QM)⁻¹ (x (c jfix)) = x jfix := by
    calc (l0 : MulAut QM)⁻¹ (x (c jfix))
        = (l0 : MulAut QM)⁻¹ ((l0 : MulAut QM) (x jfix)) := by rw [hlj]
      _ = x jfix := by rw [MulAut.inv_apply, MulEquiv.symm_apply_apply]
  change ((l0 : MulAut QM) * φ * (l0 : MulAut QM)⁻¹) (x (c jfix)) = x (c jfix)
  calc ((l0 : MulAut QM) * φ * (l0 : MulAut QM)⁻¹) (x (c jfix))
      = (l0 : MulAut QM) (φ ((l0 : MulAut QM)⁻¹ (x (c jfix)))) := rfl
    _ = (l0 : MulAut QM) (φ (x jfix)) := by rw [hlinv]
    _ = (l0 : MulAut QM) (x jfix) := by rw [hfix]
    _ = x (c jfix) := hlj

private theorem exists_mulAut_conj_mul_eq_thetaOne (φ₁ : MulAut QM)
    (hφ₁perm : linePerm φ₁ = swap 0 1) (hφ₁sq : φ₁ * φ₁ = 1)
    (hφ₁_fix : ∃ j : Fin 5, φ₁ (x j) = x j) :
    ∃ (h : QM) (l : ↥L0),
      (MulAut.conj h * (l : MulAut QM)) * φ₁ =
        thetaOne * (MulAut.conj h * (l : MulAut QM)) := by
  obtain ⟨s₀, s₁, s₂, s₃, hs⟩ := eq_autS (σ := swap 0 1) (fun j => by
    have h := linePerm_spec φ₁ j
    rwa [hφ₁perm] at h)
  have hφ₁_inv : ∀ j : Fin 4, autS (swap 0 1) (sgn4 s₀ s₁ s₂ s₃)
      (autS (swap 0 1) (sgn4 s₀ s₁ s₂ s₃) (x j.succ)) = x j.succ := by
    intro j
    rw [← hs, ← hs]
    simpa using DFunLike.congr_fun hφ₁sq (x j.succ)
  obtain ⟨jfix, hfix⟩ := hφ₁_fix
  have hφ₁_fix' : ∃ j : Fin 5,
      autS (swap 0 1) (sgn4 s₀ s₁ s₂ s₃) (x j) = x j := by
    refine ⟨jfix, ?_⟩
    rw [← hs]
    exact hfix
  obtain ⟨n, t₀, t₁, t₂, t₃, htwist⟩ :=
    check_twist s₀ s₁ s₂ s₃ hφ₁_inv hφ₁_fix'
  have hc3 : c3 ∈ alternatingGroup (Fin 5) := by
    rw [Equiv.Perm.mem_alternatingGroup]
    decide
  let lβ : ↥L0 := lineEquiv.symm ⟨c3 ^ (n : ℕ), pow_mem hc3 (n : ℕ)⟩
  have hβx : ∀ j : Fin 4, (lβ : MulAut QM) (x j.succ) = x ((c3 ^ (n : ℕ)) j.succ) := by
    intro j
    rw [show (lβ : MulAut QM) (x j.succ) =
      x (linePerm (lβ : MulAut QM) j.succ) from (mem_L0.mp lβ.2) j.succ]
    rw [linePerm_lineEquiv_symm]
  have hautS : ∀ p : QM, autS (c3 ^ (n : ℕ)) (sgn4 o o o o) p = (lβ : MulAut QM) p := by
    intro p
    rw [show (lβ : MulAut QM) p =
      liftT ((lβ : MulAut QM) z) (fun j => (lβ : MulAut QM) (x j.succ)) p 1 from
        eq_liftT (f := (lβ : MulAut QM).toMonoidHom) p]
    simp only [autS, liftT, pw, sgn4, aut_z, hβx 0, hβx 1, hβx 2, hβx 3, one_mul]
  let β : MulAut QM := MulAut.conj (innerOf t₀ t₁ t₂ t₃) * (lβ : MulAut QM)
  have htwist' : ∀ j : Fin 4, β (φ₁ (x j.succ)) = thetaOne (β (x j.succ)) := by
    intro j
    have h := htwist j
    rw [show autS (swap 0 1) (sgn4 s₀ s₁ s₂ s₃) (x j.succ) =
      φ₁ (x j.succ) from (hs (x j.succ)).symm] at h
    simpa [β, hautS, MulAut.mul_apply] using h
  have hβ : β * φ₁ = thetaOne * β := by
    apply aut_ext
    intro j
    exact htwist' j
  exact ⟨innerOf t₀ t₁ t₂ t₃, lβ, hβ⟩

private theorem exists_mulAut_conj_eq_thetaOne (φ : MulAut QM) (hφsq : φ * φ = 1)
    (hline_odd : linePerm φ ∉ alternatingGroup (Fin 5))
    (hfixline : ∃ j : Fin 5, φ (x j) = x j) :
    ∃ (h : QM) (l : ↥L0),
      (MulAut.conj h * (l : MulAut QM)) * φ * (MulAut.conj h * (l : MulAut QM))⁻¹ =
        thetaOne := by
  obtain ⟨l0, φ₁, hφ₁def, hφ₁perm, hφ₁sq, hφ₁fix⟩ :=
    exists_conj_perm_swap_of_odd φ hφsq hline_odd hfixline
  obtain ⟨h, l, hβ⟩ := exists_mulAut_conj_mul_eq_thetaOne φ₁ hφ₁perm hφ₁sq hφ₁fix
  refine ⟨h, l * l0, ?_⟩
  have hα : (MulAut.conj h * (l : MulAut QM) * (l0 : MulAut QM)) * φ *
      (MulAut.conj h * (l : MulAut QM) * (l0 : MulAut QM))⁻¹ = thetaOne := by
    calc (MulAut.conj h * (l : MulAut QM) * (l0 : MulAut QM)) * φ *
          (MulAut.conj h * (l : MulAut QM) * (l0 : MulAut QM))⁻¹
        = (MulAut.conj h * (l : MulAut QM)) *
            ((l0 : MulAut QM) * φ * (l0 : MulAut QM)⁻¹) *
            (MulAut.conj h * (l : MulAut QM))⁻¹ := by group
      _ = (MulAut.conj h * (l : MulAut QM)) * φ₁ *
            (MulAut.conj h * (l : MulAut QM))⁻¹ := by rw [hφ₁def]
      _ = thetaOne := by rw [hβ]; group
  simpa only [Subgroup.coe_mul, mul_assoc] using hα

private theorem exists_inner_conj_restrict (h : QM) (l : ↥L0) :
    ∃ g : Model, ∀ q : QM,
      MulAut.conj g (SemidirectProduct.inl q) =
        SemidirectProduct.inl ((MulAut.conj h * (l : MulAut QM)) q) := by
  let g : Model := SemidirectProduct.inl h * SemidirectProduct.inr l
  refine ⟨g, fun q => ?_⟩
  have h1 : (g * SemidirectProduct.inl q * g⁻¹ : Model) =
      SemidirectProduct.inl ((MulAut.conj h * (l : MulAut QM)) q) := by
    ext <;> simp [g, MulAut.conj_apply, map_mul, map_inv, mul_assoc]
  rw [MulAut.conj_apply, h1]

theorem AutJ2Vertex.exists_thetaExt [Finite G] {P L : Subgroup G} (h : AutJ2Vertex P L) :
    ∃ (u : G) (hu : u ∈ P) (Ψ : ↥L ≃* Model),
      u ∉ L ∧ u ^ 2 = 1 ∧ IsThetaExt (parAct h.le_normalizer Ψ ⟨u, hu⟩) := by
  classical
  obtain ⟨u, huP, huL, hu2, v, hvQ, hv2, hvn, huv⟩ := h.twist
  obtain ⟨Ψ₀⟩ := h.model
  let Θ : MulAut Model := parAct h.le_normalizer Ψ₀ ⟨u, huP⟩
  obtain ⟨φ, hφ⟩ := exists_inl_restrict Θ
  have huP2 : (⟨u, huP⟩ : ↥P) * ⟨u, huP⟩ = 1 := by
    ext
    simpa [pow_two] using hu2
  have hΘ2 : Θ * Θ = 1 := parAct_mul_self h.le_normalizer Ψ₀ ⟨u, huP⟩ huP2
  have hφsq : φ * φ = 1 := by
    refine MulEquiv.ext fun q => ?_
    apply SemidirectProduct.inl_injective (φ := L0.subtype)
    calc SemidirectProduct.inl ((φ * φ) q)
        = SemidirectProduct.inl (φ (φ q)) := rfl
      _ = Θ (SemidirectProduct.inl (φ q)) := (hφ (φ q)).symm
      _ = Θ (Θ (SemidirectProduct.inl q)) := by rw [← hφ q]
      _ = (Θ * Θ) (SemidirectProduct.inl q) := rfl
      _ = SemidirectProduct.inl q := by rw [hΘ2]; rfl
  have hline_odd := linePerm_not_mem_alternating h huP huL Ψ₀ φ hφ
  have hfixline := exists_fixed_line h huP hvQ hv2 hvn huv Ψ₀ φ hφ
  obtain ⟨h', l', hα⟩ := exists_mulAut_conj_eq_thetaOne φ hφsq hline_odd hfixline
  let α : MulAut QM := MulAut.conj h' * (l' : MulAut QM)
  obtain ⟨g₁, hg₁⟩ := exists_inner_conj_restrict h' l'
  let Ψ : ↥L ≃* Model := Ψ₀.trans (MulAut.conj g₁)
  refine ⟨u, huP, Ψ, huL, hu2, ?_⟩
  intro q
  have hinv : (MulAut.conj g₁)⁻¹ (SemidirectProduct.inl q) =
      SemidirectProduct.inl (α⁻¹ q) := by
    have h := hg₁ (α⁻¹ q)
    rw [MulAut.apply_inv_self] at h
    calc (MulAut.conj g₁)⁻¹ (SemidirectProduct.inl q)
        = (MulAut.conj g₁)⁻¹ ((MulAut.conj g₁) (SemidirectProduct.inl (α⁻¹ q))) := by
            rw [h]
      _ = SemidirectProduct.inl (α⁻¹ q) := by
            rw [MulAut.inv_apply, MulEquiv.symm_apply_apply]
  rw [show parAct h.le_normalizer Ψ ⟨u, huP⟩ =
      MulAut.conj g₁ * Θ * (MulAut.conj g₁)⁻¹ from
    parAct_trans (MulAut.conj g₁) ⟨u, huP⟩]
  calc (MulAut.conj g₁ * Θ * (MulAut.conj g₁)⁻¹) (SemidirectProduct.inl q)
      = MulAut.conj g₁ (Θ ((MulAut.conj g₁)⁻¹ (SemidirectProduct.inl q))) := rfl
    _ = MulAut.conj g₁ (Θ (SemidirectProduct.inl (α⁻¹ q))) := by rw [hinv]
    _ = MulAut.conj g₁ (SemidirectProduct.inl (φ (α⁻¹ q))) := by rw [hφ]
    _ = SemidirectProduct.inl (α (φ (α⁻¹ q))) := hg₁ _
    _ = SemidirectProduct.inl (thetaOne q) := by
          change SemidirectProduct.inl ((α * φ * α⁻¹) q) = _
          rw [hα]

theorem AutJ2Vertex.nonempty_mulEquiv {G₁ G₂ : Type} [Group G₁] [Group G₂] [Finite G₁] [Finite G₂]
    {P L : Subgroup G₁} {P' L' : Subgroup G₂} (h : AutJ2Vertex P L) (h' : AutJ2Vertex P' L') :
    Nonempty (↥P ≃* ↥P') := by
  obtain ⟨u, huP, Ψ, huL, hu2w, hΘ⟩ := h.exists_thetaExt
  obtain ⟨u', huP', Ψ', huL', hu2w', hΘ'⟩ := h'.exists_thetaExt
  let Θ : MulAut Model := parAct h.le_normalizer Ψ ⟨u, huP⟩
  let Θ' : MulAut Model := parAct h'.le_normalizer Ψ' ⟨u', huP'⟩
  have hΘeq : Θ = Θ' := IsThetaExt.unique hΘ hΘ'
  have hu2 : u * u = 1 := by simpa [pow_two] using hu2w
  have hu2' : u' * u' = 1 := by simpa [pow_two] using hu2w'
  have hΘ2 : Θ * Θ = 1 := by
    apply parAct_mul_self h.le_normalizer Ψ ⟨u, huP⟩
    ext
    simpa using hu2
  let ψ : Multiplicative (ZMod 2) →* MulAut Model := zmodTwoAct Θ hΘ2
  have hψ1 : ψ (Multiplicative.ofAdd 1) = Θ := zmodTwoAct_one Θ hΘ2
  have hψ1' : ψ (Multiplicative.ofAdd 1) = Θ' := by rw [hψ1, hΘeq]
  have hgen : P = L ⊔ Subgroup.zpowers u :=
    (CFSG.Quasithin.F6.GoldAmN.sup_zpowers_eq_of_relIndex_two h.le h.relIndex huP huL).symm
  have hgen' : P' = L' ⊔ Subgroup.zpowers u' :=
    (CFSG.Quasithin.F6.GoldAmN.sup_zpowers_eq_of_relIndex_two h'.le h'.relIndex huP' huL').symm
  have hcomp : ∀ n : Model,
      ((Ψ.symm ((1 : MulAut Model) ((ψ (Multiplicative.ofAdd 1)) n)) : ↥L) : G₁) =
        u * ((Ψ.symm ((1 : MulAut Model) n) : ↥L) : G₁) * u⁻¹ := by
    intro n
    rw [hψ1]
    simpa using parAct_conj_apply h.le_normalizer Ψ ⟨u, huP⟩ n
  have hcomp' : ∀ n : Model,
      ((Ψ'.symm ((1 : MulAut Model) ((ψ (Multiplicative.ofAdd 1)) n)) : ↥L') : G₂) =
        u' * ((Ψ'.symm ((1 : MulAut Model) n) : ↥L') : G₂) * u'⁻¹ := by
    intro n
    rw [hψ1']
    simpa using parAct_conj_apply h'.le_normalizer Ψ' ⟨u', huP'⟩ n
  obtain ⟨e₁⟩ := CFSG.GH74.Uniqueness.SU.K.R4.Q64.nonempty_mulEquiv_semidirect
    P L u h.le huP hu2 huL hgen Ψ 1 ψ hcomp
  obtain ⟨e₂⟩ := CFSG.GH74.Uniqueness.SU.K.R4.Q64.nonempty_mulEquiv_semidirect
    P' L' u' h'.le huP' hu2' huL' hgen' Ψ' 1 ψ hcomp'
  exact ⟨e₁.trans e₂.symm⟩

theorem AutJ2LocalData.autJ2Vertex [Finite G] {L1 L2 S : Subgroup G}
    (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) (h2 : VA5 L2) (hD : AutJ2LocalData L1 L2 S) :
    AutJ2Vertex (L2 ⊔ bigB L2 L1 S) L2 := by
  let P : Subgroup G := L2 ⊔ bigB L2 L1 S
  have hcardP : Nat.card P = 3840 := AutJ2LocalData.card_parabolic_right hF h1 h2 hD
  have hcardL : Nat.card L2 = 1920 := AutJ2LocalData.card_right h2 hD
  have hrel : L2.relIndex P = 2 := by
    have hcard := Subgroup.card_mul_index (L2.subgroupOf P)
    rw [show Nat.card ↥(L2.subgroupOf P) = Nat.card L2 from
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_left).toEquiv,
        hcardL, hcardP] at hcard
    change 1920 * L2.relIndex P = 3840 at hcard
    refine Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 1920) ?_
    rw [mul_comm (L2.relIndex P) 1920, hcard]
  have hcharP : CharTwo P := F1.parabolic_charTwo (hyp111R_of_vs3_va5 hF h1 h2).symm
  haveI : (L2.subgroupOf P).Normal := Subgroup.normal_of_index_eq_two hrel
  have hcharL : CharTwo L2 :=
    CFSG.QuasithinUnique.CharTwo.of_normal hcharP le_sup_left inferInstance
  obtain ⟨K, hKL2, hKQ, hK⟩ := hD.split_right
  have hmodel : Nonempty (↥L2 ≃* Model) :=
    CFSG.Quasithin.nonempty_mulEquiv_model_of_complement (P := L2) (K := K)
      hD.q8d8_right.nonempty_mulEquiv_QM hcharL hcardL hKL2 hKQ hK
  have hoTwo : pCoreOf 2 P ≤ L2 := by
    rw [AutJ2LocalData.pCoreOf_parabolic_right hF h1 h2 hD]
    exact CFSG.LieType.BorelTits.pCoreOf_le 2 L2
  refine ⟨le_sup_left, hrel, hmodel, hoTwo, ?_⟩
  obtain ⟨u, huS, huL, hu2, v, hvQ, hv2, hvn, huv⟩ := hD.twist_right
  have huB : u ∈ bigB L2 L1 S := by
    rw [bigB]
    exact Subgroup.mem_sup_right huS
  exact ⟨u, Subgroup.mem_sup_right huB, huL, hu2, v, hvQ, hv2, hvn, huv⟩

end CFSG.Quasithin.F112R.St84
