module

public import CFSG.GroupTheory.QuasisimpleCommutingProductBound
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.Actor
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.WreathAct
public import CFSG.Quasithin.SteinbergCDExactPlaneWreathResidual
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

open scoped Pointwise commutatorElement

namespace CFSG.Quasithin.SteinbergCD

open Subgroup CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup

variable {G : Type*} [Group G]

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent in
theorem card_monoidHom_le_of_sq_eq_one {X : Type*} [CommGroup X] [Finite X]
    (hX : ∀ x : X, x ^ 2 = 1) : Nat.card (X →* Multiplicative (ZMod 2)) ≤ Nat.card X := by
  let _ : Module (ZMod 2) (Additive X) := AddCommGroup.zmodModule (fun a => by
    apply Additive.toMul.injective
    rw [toMul_nsmul, toMul_zero]
    exact hX _)
  have e : (X →* Multiplicative (ZMod 2)) ≃ Module.Dual (ZMod 2) (Additive X) :=
    MonoidHom.toAdditiveLeft.trans (AddMonoidHom.toZModLinearMapEquiv 2).toEquiv
  have : Module.Finite (ZMod 2) (Additive X) := Module.Finite.of_finite
  have : Finite (Module.Dual (ZMod 2) (Additive X)) := Module.finite_of_finite (ZMod 2)
  let _ : Fintype (Additive X) := Fintype.ofFinite _
  let _ : Fintype (Module.Dual (ZMod 2) (Additive X)) := Fintype.ofFinite _
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod 2),
    Subspace.dual_finrank_eq, ← Module.card_eq_pow_finrank (K := ZMod 2),
    ← Nat.card_eq_fintype_card]
  rfl

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent in
theorem card_monoidHom_le_card_mul_card_ker {Y : Type*} [Group Y] [Finite Y] (X : Subgroup Y) :
    Nat.card (Y →* Multiplicative (ZMod 2)) ≤ Nat.card (↥X →* Multiplicative (ZMod 2)) *
      Nat.card {φ : Y →* Multiplicative (ZMod 2) // ∀ x ∈ X, φ x = 1} := by
  have : Finite (Y →* Multiplicative (ZMod 2)) := Finite.of_injective _ DFunLike.coe_injective
  have : Finite (↥X →* Multiplicative (ZMod 2)) := Finite.of_injective _ DFunLike.coe_injective
  let res : (Y →* Multiplicative (ZMod 2)) →* (↥X →* Multiplicative (ZMod 2)) :=
    MonoidHom.mk' (fun φ : Y →* Multiplicative (ZMod 2) => φ.comp X.subtype) (fun _ _ => rfl)
  have h1 := card_mul_index res.ker
  rw [index_ker] at h1
  have h2 : Nat.card res.ker =
      Nat.card {φ : Y →* Multiplicative (ZMod 2) // ∀ x ∈ X, φ x = 1} := by
    refine Nat.card_congr (Equiv.subtypeEquivRight fun φ => ?_)
    rw [MonoidHom.mem_ker]
    constructor
    · intro h x hx
      exact DFunLike.congr_fun h ⟨x, hx⟩
    · intro h
      ext x
      exact h x x.2
  have h3 : Nat.card res.range ≤ Nat.card (↥X →* Multiplicative (ZMod 2)) := card_le_card_group _
  rw [← h1, ← h2, mul_comm]
  exact Nat.mul_le_mul_right _ h3

theorem iterate_commutator_le_lowerCentralSeries {P X : Subgroup G} (hXP : X ≤ P) (n : ℕ) :
    (fun Y : Subgroup G => ⁅Y, P⁆)^[n] X ≤ P.lowerCentralSeries n := by
  induction n with
  | zero => simpa using hXP
  | succ n ih =>
    rw [Function.iterate_succ_apply', Subgroup.lowerCentralSeries_succ]
    exact commutator_mono ih le_rfl

theorem iterate_commutator_le {P V : Subgroup G} (hPV : P ≤ normalizer (V : Set G)) (n : ℕ) :
    (fun Y : Subgroup G => ⁅Y, P⁆)^[n] V ≤ V := by
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact (commutator_mono ih le_rfl).trans (le_normalizer_iff_commutator_le_left.mp hPV)

theorem exists_iterate_commutator_eq_bot [Finite G] {p : ℕ} [Fact p.Prime] {P X : Subgroup G}
    (hP : IsPGroup p P) (hXP : X ≤ P) : ∃ n : ℕ, (fun Y : Subgroup G => ⁅Y, P⁆)^[n] X = ⊥ := by
  have : Group.IsNilpotent ↥P := hP.isNilpotent
  exact ⟨Group.nilpotencyClass ↥P, eq_bot_iff.mpr
    ((iterate_commutator_le_lowerCentralSeries hXP _).trans
      (lowerCentralSeries_eq_bot_of_nilpotencyClass_le le_rfl).le)⟩

theorem exists_mem_not_mem_forall_commutator_mem [Finite G] {p : ℕ} [Fact p.Prime]
    {P V D : Subgroup G} (hP : IsPGroup p P) (hVP : V ≤ P) (hPV : P ≤ normalizer (V : Set G))
    (hVD : ¬ V ≤ D) : ∃ v ∈ V, v ∉ D ∧ ∀ t ∈ P, ⁅v, t⁆ ∈ D := by
  classical
  obtain ⟨n, hn⟩ := exists_iterate_commutator_eq_bot hP hVP
  have hex : ∃ j, (fun Y : Subgroup G => ⁅Y, P⁆)^[j + 1] V ≤ D := ⟨n, by
    rw [Function.iterate_succ_apply', hn, commutator_bot_left]
    exact bot_le⟩
  have hjD : ¬ (fun Y : Subgroup G => ⁅Y, P⁆)^[Nat.find hex] V ≤ D := by
    rcases h : Nat.find hex with _ | j'
    · simpa using hVD
    · exact Nat.find_min hex (show j' < Nat.find hex by omega)
  obtain ⟨v, hv, hvD⟩ : ∃ v ∈ (fun Y : Subgroup G => ⁅Y, P⁆)^[Nat.find hex] V, v ∉ D := by
    by_contra hcon
    exact hjD fun v hv => by_contra fun h => hcon ⟨v, hv, h⟩
  refine ⟨v, iterate_commutator_le hPV _ hv, hvD, fun t ht => ?_⟩
  have h1 := Nat.find_spec hex
  rw [Function.iterate_succ_apply'] at h1
  exact h1 (commutator_mem_commutator hv ht)

theorem commutatorElement_mul_of_mem {U : Subgroup G} (hU : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a)
    {k a b : G} (hkU : ∀ u ∈ U, k * u * k⁻¹ ∈ U) (ha : a ∈ U) (hb : b ∈ U) :
    ⁅a * b, k⁆ = ⁅b, k⁆ * ⁅a, k⁆ := by
  have h1 : k * b⁻¹ * k⁻¹ ∈ U := hkU _ (U.inv_mem hb)
  have e1 : ⁅a * b, k⁆ = a * (b * (k * b⁻¹ * k⁻¹)) * (k * a⁻¹ * k⁻¹) := by
    rw [commutatorElement_def]; group
  have e2 : ⁅b, k⁆ * ⁅a, k⁆ = b * (k * b⁻¹ * k⁻¹) * (a * (k * a⁻¹ * k⁻¹)) := by
    rw [commutatorElement_def, commutatorElement_def]; group
  rw [e1, e2, hU a ha _ (U.mul_mem hb h1)]
  group

theorem commutator_sup_le_of_abelian [Finite G] {U V Y P : Subgroup G}
    (hU : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a) (hVU : V ≤ U) (hYU : Y ≤ U)
    (hPU : P ≤ normalizer (U : Set G)) : ⁅V ⊔ Y, P⁆ ≤ ⁅V, P⁆ ⊔ ⁅Y, P⁆ := by
  rw [commutator_le]
  intro x hx p hp
  have hcomm : ∀ v ∈ V, ∀ y ∈ Y, v * y = y * v := fun v hv y hy => hU v (hVU hv) y (hYU hy)
  have hx' : x ∈ ((V ⊔ Y : Subgroup G) : Set G) := hx
  rw [(CFSG.GroupTheory.card_sup_mul_card_inf_of_commute V Y hcomm).2] at hx'
  obtain ⟨v, hv, y, hy, rfl⟩ := Set.mem_mul.mp hx'
  have hpU : ∀ u ∈ U, p * u * p⁻¹ ∈ U := fun u hu => (mem_normalizer_iff.mp (hPU hp) u).mp hu
  rw [commutatorElement_mul_of_mem hU hpU (hVU hv) (hYU hy)]
  exact mul_mem (mem_sup_right (commutator_mem_commutator hy hp))
    (mem_sup_left (commutator_mem_commutator hv hp))

theorem le_of_le_sup_commutator [Finite G] {p : ℕ} [Fact p.Prime] {P U V : Subgroup G}
    (hP : IsPGroup p P) (hUP : U ≤ P) (hU : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a) (hVU : V ≤ U)
    (hPV : P ≤ normalizer (V : Set G)) (hPU : P ≤ normalizer (U : Set G))
    (h : U ≤ V ⊔ ⁅U, P⁆) : U ≤ V := by
  have key : ∀ j, U ≤ V ⊔ (fun Y : Subgroup G => ⁅Y, P⁆)^[j] U := by
    intro j
    induction j with
    | zero => exact le_sup_right
    | succ j ih =>
      calc U ≤ V ⊔ ⁅U, P⁆ := h
        _ ≤ V ⊔ ⁅V ⊔ (fun Y : Subgroup G => ⁅Y, P⁆)^[j] U, P⁆ :=
          sup_le_sup_left (commutator_mono ih le_rfl) _
        _ ≤ V ⊔ (⁅V, P⁆ ⊔ ⁅(fun Y : Subgroup G => ⁅Y, P⁆)^[j] U, P⁆) :=
          sup_le_sup_left
            (commutator_sup_le_of_abelian hU hVU (iterate_commutator_le hPU j) hPU) _
        _ ≤ V ⊔ (fun Y : Subgroup G => ⁅Y, P⁆)^[j + 1] U := by
          rw [Function.iterate_succ_apply']
          exact sup_le le_sup_left
            (sup_le ((le_normalizer_iff_commutator_le_left.mp hPV).trans le_sup_left)
              le_sup_right)
  obtain ⟨n, hn⟩ := exists_iterate_commutator_eq_bot hP hUP
  have := key n
  rwa [hn, sup_bot_eq] at this

theorem commutatorElement_pow_mem {W : Subgroup G} {x g : G}
    (hgW : ∀ w ∈ W, g * w * g⁻¹ ∈ W) (h : ⁅x, g⁆ ∈ W) (m : ℕ) : ⁅x, g ^ m⁆ ∈ W := by
  induction m with
  | zero => rw [pow_zero, commutatorElement_one_right]; exact W.one_mem
  | succ m ih =>
    have e : ⁅x, g ^ (m + 1)⁆ = ⁅x, g⁆ * (g * ⁅x, g ^ m⁆ * g⁻¹) := by
      rw [pow_succ', commutatorElement_def, commutatorElement_def, commutatorElement_def]; group
    rw [e]
    exact W.mul_mem h (hgW _ ih)

theorem commutator_mem_of_odd {U B W : Subgroup G} (hUe : CFSG.Open.IsElemAbelian 2 U)
    (hBU : B ≤ U) {k : G} (hk : Odd (orderOf k)) (hkU : ∀ u ∈ U, k * u * k⁻¹ ∈ U)
    (hkW : ∀ w ∈ W, k * w * k⁻¹ ∈ W) (hB : ∀ b ∈ B, ⁅b, k⁆ ∈ W) {x : G} (hxB : ⁅x, k⁆ ∈ B) :
    ⁅x, k⁆ ∈ W := by
  have := hUe.1
  obtain ⟨y, hy⟩ : ∃ y, y = ⁅x, k⁆ := ⟨_, rfl⟩
  obtain ⟨z, hz⟩ : ∃ z, z = ⁅y, k⁆ := ⟨_, rfl⟩
  have hyB : y ∈ B := hy ▸ hxB
  have hyU : y ∈ U := hBU hyB
  have hzW : z ∈ W := hz ▸ hB y hyB
  have hzU : z ∈ U := by
    have e : z = y * (k * y⁻¹ * k⁻¹) := by rw [hz, commutatorElement_def]; group
    rw [e]
    exact U.mul_mem hyU (hkU _ (U.inv_mem hyU))
  have e1 : k * x⁻¹ * k⁻¹ = x⁻¹ * y := by rw [hy, commutatorElement_def]; group
  have e2 : k * y * k⁻¹ = z⁻¹ * y := by rw [hz, commutatorElement_def]; group
  have e3 : ⁅x, k ^ 2⁆ = y * z⁻¹ * y := by
    rw [commutatorElement_def, pow_two]
    calc x * (k * k) * x⁻¹ * (k * k)⁻¹ = x * (k * (k * x⁻¹ * k⁻¹) * k⁻¹) := by group
      _ = x * (k * (x⁻¹ * y) * k⁻¹) := by rw [e1]
      _ = x * ((k * x⁻¹ * k⁻¹) * (k * y * k⁻¹)) := by group
      _ = x * ((x⁻¹ * y) * (z⁻¹ * y)) := by rw [e1, e2]
      _ = y * z⁻¹ * y := by group
  have hy2 : y * y = 1 := by rw [← pow_two]; exact hUe.2 y hyU
  have e4 : y * z⁻¹ * y = z⁻¹ := by
    rw [setLike_mul_comm hyU (U.inv_mem hzU), mul_assoc, hy2, mul_one]
  have hk2 : ⁅x, k ^ 2⁆ ∈ W := by
    rw [e3, e4]
    exact W.inv_mem hzW
  have hk2W : ∀ w ∈ W, k ^ 2 * w * (k ^ 2)⁻¹ ∈ W := by
    intro w hw
    have e : k ^ 2 * w * (k ^ 2)⁻¹ = k * (k * w * k⁻¹) * k⁻¹ := by rw [pow_two]; group
    rw [e]
    exact hkW _ (hkW w hw)
  obtain ⟨m, hm⟩ := hk
  have hkpow : (k ^ 2) ^ (m + 1) = k := by
    rw [← pow_mul, show 2 * (m + 1) = orderOf k + 1 by omega, pow_succ, pow_orderOf_eq_one,
      one_mul]
  have := commutatorElement_pow_mem hk2W hk2 (m + 1)
  rwa [hkpow] at this

theorem le_normalizer_sup_of_le {H A B : Subgroup G} (hA : H ≤ normalizer (A : Set G))
    (hB : H ≤ normalizer (B : Set G)) : H ≤ normalizer ((A ⊔ B : Subgroup G) : Set G) :=
  fun h hh => RankThree.GroupTheory.SteinbergBY.mem_normalizer_of_map_conj_eq (by
    rw [Subgroup.map_sup, RankThree.GroupTheory.SteinbergBY.map_conj_eq_of_mem_normalizer (hA hh),
      RankThree.GroupTheory.SteinbergBY.map_conj_eq_of_mem_normalizer (hB hh)])

theorem le_normalizer_inf_of_le {H A B : Subgroup G} (hA : H ≤ normalizer (A : Set G))
    (hB : H ≤ normalizer (B : Set G)) : H ≤ normalizer ((A ⊓ B : Subgroup G) : Set G) := by
  intro h hh
  rw [mem_normalizer_iff]
  intro x
  have h1 := mem_normalizer_iff.mp (hA hh) x
  have h2 := mem_normalizer_iff.mp (hB hh) x
  exact ⟨fun hx => ⟨h1.mp hx.1, h2.mp hx.2⟩, fun hx => ⟨h1.mpr hx.1, h2.mpr hx.2⟩⟩

theorem le_normalizer_commutator_of_le {H A B : Subgroup G} (hA : H ≤ normalizer (A : Set G))
    (hB : H ≤ normalizer (B : Set G)) : H ≤ normalizer ((⁅A, B⁆ : Subgroup G) : Set G) :=
  fun h hh => RankThree.GroupTheory.SteinbergBY.mem_normalizer_of_map_conj_eq (by
    rw [map_commutator, RankThree.GroupTheory.SteinbergBY.map_conj_eq_of_mem_normalizer (hA hh),
      RankThree.GroupTheory.SteinbergBY.map_conj_eq_of_mem_normalizer (hB hh)])

theorem exists_subgroup_forall_commutator_mem [Finite G] {H A W : Subgroup G}
    (hHA : H ≤ normalizer (A : Set G)) (hHW : H ≤ normalizer (W : Set G)) :
    ∃ X : Subgroup G, H ≤ normalizer (X : Set G) ∧
      ∀ x, x ∈ X ↔ x ∈ H ∧ ∀ a ∈ A, ⁅a, x⁆ ∈ W := by
  have hW : ∀ h ∈ H, ∀ w ∈ W, h * w * h⁻¹ ∈ W := fun h hh w hw =>
    (mem_normalizer_iff.mp (hHW hh) w).mp hw
  have hA : ∀ h ∈ H, ∀ a ∈ A, h * a * h⁻¹ ∈ A := fun h hh a ha =>
    (mem_normalizer_iff.mp (hHA hh) a).mp ha
  let X : Subgroup G :=
    { carrier := {x | x ∈ H ∧ ∀ a ∈ A, ⁅a, x⁆ ∈ W}
      one_mem' := ⟨H.one_mem, fun a _ => by rw [commutatorElement_one_right]; exact W.one_mem⟩
      mul_mem' := fun {x y} hx hy => ⟨H.mul_mem hx.1 hy.1, fun a ha => by
        have e : ⁅a, x * y⁆ = ⁅a, x⁆ * (x * ⁅a, y⁆ * x⁻¹) := by
          simp only [commutatorElement_def]; group
        rw [e]
        exact W.mul_mem (hx.2 a ha) (hW x hx.1 _ (hy.2 a ha))⟩
      inv_mem' := fun {x} hx => ⟨H.inv_mem hx.1, fun a ha => by
        have e : ⁅a, x⁻¹⁆ = x⁻¹ * ⁅a, x⁆⁻¹ * x⁻¹⁻¹ := by
          simp only [commutatorElement_def]; group
        rw [e]
        exact hW x⁻¹ (H.inv_mem hx.1) _ (W.inv_mem (hx.2 a ha))⟩ }
  refine ⟨X, le_normalizer_of_conj_mem_of_finite fun g hg x hx => ⟨?_, fun a ha => ?_⟩,
    fun x => Iff.rfl⟩
  · exact H.mul_mem (H.mul_mem hg hx.1) (H.inv_mem hg)
  · have hka : g⁻¹ * a * g ∈ A := by simpa using hA g⁻¹ (H.inv_mem hg) a ha
    have e : ⁅a, g * x * g⁻¹⁆ = g * ⁅g⁻¹ * a * g, x⁆ * g⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact hW g hg _ (hx.2 _ hka)

theorem commutator_oddOrderSubgroup_le_of_compositionSeries [Finite G] {H U W : Subgroup G}
    (hUe : CFSG.Open.IsElemAbelian 2 U) (hHU : H ≤ normalizer (U : Set G)) (hWU : W ≤ U)
    (hHW : H ≤ normalizer (W : Set G)) {n : ℕ} {C : Fin (n + 1) → Subgroup G}
    (hC0 : C 0 = ⊥) (hCn : C (Fin.last n) = U) (hCH : ∀ i, H ≤ normalizer (C i : Set G))
    (hCs : ∀ i : Fin n, C i.castSucc < C i.succ ∧ ∀ X : Subgroup G,
      H ≤ normalizer (X : Set G) → C i.castSucc ≤ X → X ≤ C i.succ →
        X = C i.castSucc ∨ X = C i.succ)
    (hone : ∃! i : Fin n, ¬ ⁅C i.succ, H⁆ ≤ C i.castSucc)
    (hWK : ⁅W, oddOrderSubgroup H⁆ ≠ ⊥) : ⁅U, oddOrderSubgroup H⁆ ≤ W := by
  have := hUe.1
  have hUc : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a := fun a ha b hb => setLike_mul_comm ha hb
  obtain ⟨i₀, -, hi₀u⟩ := hone
  have htriv : ∀ i : Fin n, i ≠ i₀ → ⁅C i.succ, H⁆ ≤ C i.castSucc := fun i hi => by
    by_contra h
    exact hi (hi₀u i h)
  have hmono : Monotone C := Fin.monotone_iff_le_succ.mpr fun i => (hCs i).1.le
  have hCU : ∀ i, C i ≤ U := fun i => hCn ▸ hmono (Fin.le_last i)
  have conj : ∀ {X : Subgroup G}, H ≤ normalizer (X : Set G) → ∀ h ∈ H, ∀ x ∈ X,
      h * x * h⁻¹ ∈ X := fun hX h hh x hx => (mem_normalizer_iff.mp (hX hh) x).mp hx
  have hcommW : ∀ {k : G}, k ∈ H → ∀ w ∈ W, ⁅w, k⁆ ∈ W := by
    intro k hk w hw
    have e : ⁅w, k⁆ = w * (k * w⁻¹ * k⁻¹) := by rw [commutatorElement_def]; group
    rw [e]
    exact W.mul_mem hw (conj hHW k hk _ (W.inv_mem hw))
  have hstep : C i₀.succ ≤ C i₀.castSucc ⊔ W := by
    by_contra hne
    have hYH : H ≤ normalizer ((C i₀.succ ⊓ W ⊔ C i₀.castSucc : Subgroup G) : Set G) :=
      le_normalizer_sup_of_le (le_normalizer_inf_of_le (hCH _) hHW) (hCH _)
    rcases (hCs i₀).2 _ hYH le_sup_right (sup_le inf_le_left (hCs i₀).1.le) with hY | hY
    · have hle : C i₀.succ ⊓ W ≤ C i₀.castSucc := le_sup_left.trans hY.le
      apply hWK
      have hodd : ∀ k ∈ H, Odd (orderOf k) → ∀ w ∈ W, ⁅w, k⁆ = 1 := by
        intro k hk hko
        have key : ∀ i : Fin (n + 1), ∀ w ∈ C i ⊓ W, ⁅w, k⁆ = 1 := by
          intro i
          induction i using Fin.induction with
          | zero =>
            intro w hw
            rw [hC0] at hw
            rw [mem_bot.mp hw.1, commutatorElement_one_left]
          | succ i ih =>
            intro w hw
            by_cases hi : i = i₀
            · subst hi
              exact ih w ⟨hle hw, hw.2⟩
            · have h1 : ⁅w, k⁆ ∈ C i.castSucc ⊓ W :=
                ⟨htriv i hi (commutator_mem_commutator hw.1 hk), hcommW hk w hw.2⟩
              have h2 := commutator_mem_of_odd (W := ⊥) hUe (inf_le_left.trans (hCU _)) hko
                (fun u hu => conj hHU k hk u hu) (fun x hx => by rw [mem_bot.mp hx]; simp)
                (fun b hb => mem_bot.mpr (ih b hb)) h1
              exact mem_bot.mp h2
        intro w hw
        exact key (Fin.last n) w ⟨hCn ▸ hWU hw, hw⟩
      have hKc : oddOrderSubgroup H ≤ centralizer (W : Set G) :=
        (closure_le _).mpr fun k hk => mem_centralizer_iff.mpr fun w hw =>
          commutatorElement_eq_one_iff_mul_comm.mp (hodd k hk.1 hk.2 w hw)
      exact commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp hKc)
    · apply hne
      calc C i₀.succ = C i₀.succ ⊓ W ⊔ C i₀.castSucc := hY.symm
        _ ≤ C i₀.castSucc ⊔ W := sup_le (inf_le_right.trans le_sup_right) le_sup_left
  have hall : ∀ k ∈ H, Odd (orderOf k) → ∀ u ∈ U, ⁅u, k⁆ ∈ W := by
    intro k hk hko
    have hkU : ∀ u ∈ U, k * u * k⁻¹ ∈ U := fun u hu => conj hHU k hk u hu
    have key : ∀ i : Fin (n + 1), ∀ x ∈ C i, ⁅x, k⁆ ∈ W := by
      intro i
      induction i using Fin.induction with
      | zero =>
        intro x hx
        rw [hC0, mem_bot] at hx
        rw [hx, commutatorElement_one_left]
        exact W.one_mem
      | succ i ih =>
        intro x hx
        by_cases hi : i = i₀
        · subst hi
          have hcomm : ∀ c ∈ C i.castSucc, ∀ w ∈ W, c * w = w * c := fun c hc w hw =>
            hUc c (hCU _ hc) w (hWU hw)
          have hx' : x ∈ ((C i.castSucc ⊔ W : Subgroup G) : Set G) := hstep hx
          rw [(CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ hcomm).2] at hx'
          obtain ⟨c, hc, w, hw, rfl⟩ := Set.mem_mul.mp hx'
          rw [commutatorElement_mul_of_mem hUc hkU (hCU _ hc) (hWU hw)]
          exact W.mul_mem (hcommW hk w hw) (ih c hc)
        · exact commutator_mem_of_odd hUe (hCU _) hko hkU (fun w hw => conj hHW k hk w hw) ih
            (htriv i hi (commutator_mem_commutator hx hk))
    intro u hu
    exact key (Fin.last n) u (hCn ▸ hu)
  obtain ⟨X, -, hX⟩ := exists_subgroup_forall_commutator_mem (A := U) hHU hHW
  have hKX : oddOrderSubgroup H ≤ X := (closure_le _).mpr fun k hk =>
    (hX k).mpr ⟨hk.1, fun u hu => hall k hk.1 hk.2 u hu⟩
  rw [commutator_le]
  intro u hu k hk
  exact ((hX k).mp (hKX hk)).2 u hu

theorem commutator_inf_centralizer_eq_bot_of_odd [Finite G] {A P : Subgroup G}
    (hAe : CFSG.Open.IsElemAbelian 2 A) (hPA : P ≤ normalizer (A : Set G))
    (hodd : Odd (Nat.card ↥P)) : ⁅A, P⁆ ⊓ centralizer (P : Set G) = ⊥ := by
  classical
  let _ : CommGroup ↥A := commGroupOfElemAbelian hAe
  have : Fintype ↥P := Fintype.ofFinite _
  have hconj : ∀ p ∈ P, ∀ x ∈ A, p * x * p⁻¹ ∈ A := fun p hp x hx =>
    (mem_normalizer_iff.mp (hPA hp) x).mp hx
  let φ : ↥P → (↥A →* ↥A) := fun q =>
    { toFun := fun x => ⟨q * x * q⁻¹, hconj q q.2 x x.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (by
        show (q : G) * ((x : G) * y) * (q : G)⁻¹ = (q * x * (q : G)⁻¹) * (q * y * (q : G)⁻¹)
        group) }
  have hφ : ∀ q : ↥P, ∀ x : ↥A, ((φ q x : ↥A) : G) = q * x * (q : G)⁻¹ := fun _ _ => rfl
  let π : ↥A →* ↥A := ∏ p, φ p
  have hπ : ∀ x, π x = ∏ p, φ p x := fun x => MonoidHom.finsetProd_apply _ _ _
  have hπφ : ∀ q x, π (φ q x) = π x := by
    intro q x
    rw [hπ, hπ]
    have e : ∀ p, φ p (φ q x) = φ (p * q) x := fun p => Subtype.ext (by
      rw [hφ, hφ, hφ]
      push_cast
      group)
    simp_rw [e]
    exact Fintype.prod_equiv (Equiv.mulRight q) _ _ (fun _ => rfl)
  have hker : ⁅A, P⁆ ≤ (π.ker).map A.subtype := by
    rw [commutator_le]
    intro a ha p hp
    refine ⟨⟨a, ha⟩ * φ ⟨p, hp⟩ ⟨a, ha⟩⁻¹, MonoidHom.mem_ker.mpr ?_, ?_⟩
    · rw [map_mul, hπφ, map_inv, mul_inv_cancel]
    · show (a : G) * ((p : G) * a⁻¹ * (p : G)⁻¹) = ⁅a, p⁆
      rw [commutatorElement_def]
      group
  rw [eq_bot_iff]
  rintro c ⟨hc, hcP⟩
  obtain ⟨c', hc', rfl⟩ := hker hc
  have hcP' : ∀ q ∈ P, q * (c' : G) = c' * q := fun q hq => mem_centralizer_iff.mp hcP q hq
  have hfix : ∀ p, φ p c' = c' := fun p => Subtype.ext (by
    rw [hφ, hcP' p p.2, mul_inv_cancel_right])
  have h1 : π c' = c' := by
    rw [hπ]
    simp_rw [hfix]
    rw [Finset.prod_const, Finset.card_univ, ← Nat.card_eq_fintype_card]
    obtain ⟨m, hm⟩ := hodd
    have hsq : c' ^ 2 = 1 := Subtype.ext (by simpa using hAe.2 _ c'.2)
    rw [hm, pow_succ, pow_mul, hsq, one_pow, one_mul]
  have hc'' : π c' = 1 := hc'
  rw [hc''] at h1
  rw [mem_bot, ← h1]
  rfl

theorem exists_le_card_eq_map_eq_of_prime [Finite G] {G' : Type*} [Group G'] (f : G →* G')
    {K : Subgroup G} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hker : IsPGroup 2 ↥(K ⊓ f.ker))
    {n : ℕ} (hcard : Nat.card ↥(K.map f) = p ^ n) :
    ∃ P : Subgroup G, P ≤ K ∧ Nat.card ↥P = p ^ n ∧ P.map f = K.map f := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact p.Prime := ⟨hp⟩
  have hK := Wreath.card_map_mul_card_inf_ker f K
  obtain ⟨P₀, hP₀⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥K) p (n := n)
    (by rw [← hK, hcard]; exact Dvd.intro _ rfl)
  have hPK : P₀.map K.subtype ≤ K := by
    rintro _ ⟨y, -, rfl⟩
    exact y.2
  have hPc : Nat.card ↥(P₀.map K.subtype) = p ^ n := by
    rw [card_map_of_injective K.subtype_injective, hP₀]
  refine ⟨P₀.map K.subtype, hPK, hPc, ?_⟩
  have h1 := Wreath.card_map_mul_card_inf_ker f (P₀.map K.subtype)
  obtain ⟨m, hm⟩ := hker.exists_card_eq
  have h2 : Nat.card ↥(P₀.map K.subtype ⊓ f.ker) = 1 := by
    refine Nat.eq_one_of_dvd_coprimes (a := p ^ n) (b := 2 ^ m)
      (Nat.Coprime.pow n m ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)) ?_ ?_
    · rw [← hPc]
      exact Subgroup.card_dvd_of_le inf_le_left
    · rw [← hm]
      exact Subgroup.card_dvd_of_le (inf_le_inf_right _ hPK)
  rw [h2, mul_one, hPc, ← hcard] at h1
  have : Finite ↥(K.map f) := Finite.of_surjective _ (f.subgroupMap_surjective K)
  exact eq_of_le_of_card_ge (map_mono hPK) h1.ge

end SteinbergCD

end CFSG.Quasithin
