module

public import CFSG.Quasithin.H13.A7SharedFourS5Binary
public import CFSG.LieType.SteinbergBRTwoRankBound

public section

namespace CFSG.Quasithin.H13.A7

open Equiv Equiv.Perm Subgroup Module

section Spaces

variable {H V : Type*} [Group H] [AddCommGroup V] [Module (ZMod 2) V]

@[expose] def fixSpace (ρ : H →* (V ≃ₗ[ZMod 2] V)) (X : Subgroup H) : Submodule (ZMod 2) V where
  carrier := {v | ∀ x ∈ X, ρ x v = v}
  add_mem' := fun {a b} ha hb x hx => by rw [map_add, ha x hx, hb x hx]
  zero_mem' := fun x _ => map_zero _
  smul_mem' := fun c {v} hv x hx => by rw [map_smul, hv x hx]

@[expose] def commSpace (ρ : H →* (V ≃ₗ[ZMod 2] V)) (X : Subgroup H) : Submodule (ZMod 2) V :=
  Submodule.span (ZMod 2) {w | ∃ x ∈ X, ∃ v : V, w = ρ x v - v}

theorem mem_fixSpace {ρ : H →* (V ≃ₗ[ZMod 2] V)} {X : Subgroup H} {v : V} :
    v ∈ fixSpace ρ X ↔ ∀ x ∈ X, ρ x v = v := Iff.rfl

end Spaces

theorem perm_three_facts :
    finRotate 3 ^ 3 = 1 ∧ sign (finRotate 3) = 1 ∧
      (∀ σ : Perm (Fin 3), sign σ = 1 → σ = 1 ∨ σ = finRotate 3 ∨ σ = finRotate 3 ^ 2) ∧
      ∀ σ : Perm (Fin 3), σ ≠ 1 → σ ^ 2 = 1 → σ * finRotate 3 * σ⁻¹ = finRotate 3 ^ 2 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

theorem orderOf_four_cycle_five :
    orderOf (swap (0 : Fin 5) 1 * swap 1 2 * swap 2 3) = 2 ^ 2 :=
  orderOf_eq_prime_pow (by decide) (by decide)

theorem card_le_eight_of_isElementaryAbelian (B : Subgroup (Perm (Fin 5) × Perm (Fin 3)))
    [IsElementaryAbelian 2 B] : Nat.card B ≤ 8 := by
  classical
  have h1 : Nat.card (B.map (MonoidHom.fst (Perm (Fin 5)) (Perm (Fin 3)))) ≤ 2 ^ 2 := by
    have : IsElementaryAbelian 2 (B.map (MonoidHom.fst (Perm (Fin 5)) (Perm (Fin 3)))) :=
      IsElementaryAbelian.map _
    refine CFSG.LieType.SteinbergBR.card_le_sq_of_orderOf (p := 2) orderOf_four_cycle_five ?_ _
    rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
    decide
  have h2 : Nat.card (B.map (MonoidHom.snd (Perm (Fin 5)) (Perm (Fin 3)))) ≤ 2 := by
    have : IsElementaryAbelian 2 (B.map (MonoidHom.snd (Perm (Fin 5)) (Perm (Fin 3)))) :=
      IsElementaryAbelian.map _
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.1
      (IsElementaryAbelian.isPGroup 2 (B.map (MonoidHom.snd (Perm (Fin 5)) (Perm (Fin 3)))))
    have hdvd := Subgroup.card_subgroup_dvd_card
      (B.map (MonoidHom.snd (Perm (Fin 5)) (Perm (Fin 3))))
    rw [Nat.card_perm, Nat.card_eq_fintype_card (α := Fin 3), Fintype.card_fin, hm] at hdvd
    rw [hm]
    rcases m with _ | _ | m
    · norm_num
    · norm_num
    · exfalso
      have h4 : 4 ∣ Nat.factorial 3 := (Dvd.intro (2 ^ m) (by ring)).trans hdvd
      exact absurd h4 (by decide)
  let e : B → (B.map (MonoidHom.fst (Perm (Fin 5)) (Perm (Fin 3)))) ×
      (B.map (MonoidHom.snd (Perm (Fin 5)) (Perm (Fin 3)))) :=
    fun b => (⟨b.1.1, b.1, b.2, rfl⟩, ⟨b.1.2, b.1, b.2, rfl⟩)
  have he : Function.Injective e := by
    intro a b hab
    have h1 := congrArg (fun q => (q.1 : Perm (Fin 5))) hab
    have h2 := congrArg (fun q => (q.2 : Perm (Fin 3))) hab
    exact Subtype.ext (Prod.ext h1 h2)
  have h := Nat.card_le_card_of_injective e he
  rw [Nat.card_prod] at h
  calc Nat.card B ≤ _ := h
    _ ≤ 2 ^ 2 * 2 := Nat.mul_le_mul h1 h2
    _ = 8 := by norm_num

theorem A7_S5_S3_action_inequality_commutator_split {V : Type*} [AddCommGroup V]
    [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Perm (Fin 5) × Perm (Fin 3) →* (V ≃ₗ[ZMod 2] V))
    (hB : ∃ B : Subgroup (Perm (Fin 5) × Perm (Fin 3)), IsElementaryAbelian 2 B ∧
      ∃ r : ℕ, Nat.card B = 2 ^ r ∧
        finrank (ZMod 2) V - finrank (ZMod 2) (fixSpace ρ B) ≤ r ∧ ∃ b ∈ B, b.2 ≠ 1) :
    let K := (alternatingGroup (Fin 5)).prod (⊥ : Subgroup (Perm (Fin 3)))
    let D := (⊥ : Subgroup (Perm (Fin 5))).prod (alternatingGroup (Fin 3))
    (∀ x ∈ K, ∀ w ∈ commSpace ρ D, ρ x w = w) ∧ IsCompl (fixSpace ρ D) (commSpace ρ D) ∧
      finrank (ZMod 2) (commSpace ρ D) ≤ 6 ∧ commSpace ρ K ≤ fixSpace ρ D ∧
      commSpace ρ K ⊓ commSpace ρ D = ⊥ := by
  classical
  intro K D
  obtain ⟨hc3, hcsign, hA3, hinv⟩ := perm_three_facts
  set c : Perm (Fin 3) := finRotate 3 with hcdef
  set d : Perm (Fin 5) × Perm (Fin 3) := (1, c) with hddef
  have hdD : d ∈ D := Subgroup.mem_prod.2 ⟨Subgroup.mem_bot.2 rfl, mem_alternatingGroup.2 hcsign⟩
  have hDel : ∀ x ∈ D, x = 1 ∨ x = d ∨ x = d ^ 2 := by
    intro x hx
    obtain ⟨hx1, hx2⟩ := Subgroup.mem_prod.1 hx
    rw [Subgroup.mem_bot] at hx1
    rcases hA3 x.2 (mem_alternatingGroup.1 hx2) with h | h | h
    · exact Or.inl (Prod.ext hx1 h)
    · exact Or.inr (Or.inl (Prod.ext hx1 h))
    · exact Or.inr (Or.inr (Prod.ext (by simp [hddef, hx1]) (by simp [hddef, h])))
  set ρ' : Perm (Fin 5) × Perm (Fin 3) →* Module.End (ZMod 2) V :=
    LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp ρ with hρ'
  set T := ρ' d with hT
  have hd3 : d ^ 3 = 1 := Prod.ext (by simp [hddef]) (by simp [hddef, hc3])
  have hT3 : T ^ 3 = 1 := by rw [hT, ← map_pow, hd3, map_one]
  have hTe : (T - 1) * (T ^ 2 + T + 1) = 0 := by
    have : (T - 1) * (T ^ 2 + T + 1) = T ^ 3 - 1 := by noncomm_ring
    rw [this, hT3, sub_self]
  have heT : (T ^ 2 + T + 1) * (T - 1) = 0 := by
    have : (T ^ 2 + T + 1) * (T - 1) = T ^ 3 - 1 := by noncomm_ring
    rw [this, hT3, sub_self]
  have hTinj : ∀ v : V, T v = 0 → v = 0 := by
    intro v hv
    have h1 : T ^ 2 * T = 1 := by rw [← pow_succ, hT3]
    calc v = (T ^ 2 * T) v := by rw [h1, Module.End.one_apply]
      _ = 0 := by rw [Module.End.mul_apply, hv, map_zero]
  have hTinj' : Function.Injective T := fun a b h =>
    sub_eq_zero.1 (hTinj _ (by rw [map_sub, h, sub_self]))
  have hCeq : fixSpace ρ D = LinearMap.ker (T - 1) := by
    ext v
    rw [mem_fixSpace, LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
    constructor
    · intro h
      exact h d hdD
    · intro h x hx
      rcases hDel x hx with rfl | rfl | rfl
      · show ρ' 1 v = v
        rw [map_one, Module.End.one_apply]
      · exact h
      · show ρ' (d ^ 2) v = v
        rw [map_pow, pow_two, Module.End.mul_apply]
        rw [← hT, h, h]
  have hWeq : commSpace ρ D = LinearMap.range (T - 1) := by
    apply le_antisymm
    · rw [commSpace, Submodule.span_le]
      rintro w ⟨x, hx, v, rfl⟩
      rw [SetLike.mem_coe, LinearMap.mem_range]
      rcases hDel x hx with rfl | rfl | rfl
      · refine ⟨0, ?_⟩
        show (T - 1) 0 = ρ' 1 v - v
        rw [map_one, Module.End.one_apply, sub_self, map_zero]
      · exact ⟨v, rfl⟩
      · refine ⟨T v + v, ?_⟩
        show (T - 1) (T v + v) = ρ' (d ^ 2) v - v
        rw [map_pow, pow_two, Module.End.mul_apply, LinearMap.sub_apply, Module.End.one_apply,
          map_add, ← hT]
        abel
    · intro w hw
      obtain ⟨v, rfl⟩ := LinearMap.mem_range.1 hw
      exact Submodule.subset_span ⟨d, hdD, v, rfl⟩
  set C := LinearMap.ker (T - 1) with hCdef
  set W := LinearMap.range (T - 1) with hWdef
  have hmemC : ∀ v : V, v ∈ C ↔ T v = v := fun v => by
    rw [hCdef, LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
  have hcompl : IsCompl C W := by
    constructor
    · rw [Submodule.disjoint_def]
      intro v hv hvW
      obtain ⟨u, rfl⟩ := LinearMap.mem_range.1 hvW
      have hTv := (hmemC _).1 hv
      have h1 := LinearMap.congr_fun heT u
      rw [Module.End.mul_apply, LinearMap.zero_apply, LinearMap.add_apply, LinearMap.add_apply,
        Module.End.one_apply, pow_two, Module.End.mul_apply, hTv, hTv, ZModModule.add_self,
        zero_add] at h1
      exact h1
    · rw [codisjoint_iff, eq_top_iff]
      intro v _
      rw [Submodule.mem_sup]
      refine ⟨(T ^ 2 + T + 1 : Module.End (ZMod 2) V) v, ?_,
        v - (T ^ 2 + T + 1 : Module.End (ZMod 2) V) v, ?_, add_sub_cancel _ _⟩
      · rw [hCdef, LinearMap.mem_ker, ← Module.End.mul_apply, hTe, LinearMap.zero_apply]
      · refine LinearMap.mem_range.2 ⟨T v, ?_⟩
        rw [LinearMap.sub_apply, Module.End.one_apply, LinearMap.add_apply, LinearMap.add_apply,
          Module.End.one_apply, pow_two, Module.End.mul_apply]
        calc T (T v) - T v = -T (T v) - T v := by rw [ZModModule.neg_eq_self]
          _ = v - (T (T v) + T v + v) := by abel
  have hcommT : ∀ x : Perm (Fin 5) × Perm (Fin 3), x * d = d * x → ρ' x * T = T * ρ' x := by
    intro x hx
    rw [hT, ← map_mul, ← map_mul, hx]
  have hpresW : ∀ x, x * d = d * x → ∀ w ∈ W, ρ x w ∈ W := by
    intro x hx w hw
    obtain ⟨u, rfl⟩ := LinearMap.mem_range.1 hw
    refine LinearMap.mem_range.2 ⟨ρ x u, ?_⟩
    show T (ρ' x u) - ρ' x u = ρ' x (T u - u)
    rw [map_sub, ← Module.End.mul_apply T, ← hcommT x hx, Module.End.mul_apply]
  have hpresC : ∀ x, x * d = d * x → ∀ v ∈ C, ρ x v ∈ C := by
    intro x hx v hv
    rw [hmemC] at hv ⊢
    show T (ρ' x v) = ρ' x v
    rw [← Module.End.mul_apply T, ← hcommT x hx, Module.End.mul_apply, hv]
  have hkd : ∀ g : Perm (Fin 5), ((g, 1) : Perm (Fin 5) × Perm (Fin 3)) * d = d * (g, 1) :=
    fun g => Prod.ext (by simp [hddef]) (by simp [hddef])
  have hTW : ∀ w ∈ W, T w ∈ W := hpresW d rfl
  obtain ⟨B, hBel, r, hcard, hineq, b, hbB, hb2⟩ := hB
  have hr : r ≤ 3 := by
    have h8 := card_le_eight_of_isElementaryAbelian B
    rw [hcard] at h8
    by_contra hr
    have : 2 ^ 4 ≤ 2 ^ r := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hbsq : b ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian b hbB
  have hσ2 : b.2 ^ 2 = 1 := by rw [← Prod.pow_snd, hbsq, Prod.snd_one]
  have hσc := hinv b.2 hb2 hσ2
  have hbd : b * d = d ^ 2 * b := by
    refine Prod.ext (by simp [hddef]) ?_
    simp only [Prod.snd_mul, Prod.pow_snd, hddef]
    calc b.2 * c = b.2 * c * b.2⁻¹ * b.2 := by group
      _ = c ^ 2 * b.2 := by rw [hσc]
  set τ := ρ' b with hτ
  have hτT : τ * T = T ^ 2 * τ := by rw [hτ, hT, ← map_mul, hbd, map_mul, map_pow]
  set Ub := LinearMap.ker (τ - 1) with hUb
  have hmemU : ∀ v : V, v ∈ Ub ↔ τ v = v := fun v => by
    rw [hUb, LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
  have hFT : (W ⊓ Ub) ⊓ (W ⊓ Ub).map T = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    obtain ⟨⟨-, hyU⟩, hyT⟩ := Submodule.mem_inf.1 hy
    obtain ⟨w, ⟨hwW, hwU⟩, rfl⟩ := Submodule.mem_map.1 hyT
    replace hyU := (hmemU _).1 hyU
    replace hwU := (hmemU _).1 hwU
    have h1 : τ (T w) = T (T w) := by
      rw [← Module.End.mul_apply, hτT, Module.End.mul_apply, hwU, pow_two, Module.End.mul_apply]
    have h2 : T w = w := by
      have : T (T w - w) = 0 := by rw [map_sub, ← h1, hyU, sub_self]
      exact sub_eq_zero.1 (hTinj _ this)
    have h3 : w = 0 := Submodule.disjoint_def.1 hcompl.disjoint w ((hmemC w).2 h2) hwW
    rw [h3, map_zero]
    exact Submodule.zero_mem _
  have hFTW : (W ⊓ Ub).map T ≤ W := by
    rintro _ ⟨w, ⟨hwW, -⟩, rfl⟩
    exact hTW w hwW
  have hrankF : 2 * finrank (ZMod 2) ↥(W ⊓ Ub) ≤ finrank (ZMod 2) W := by
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq (W ⊓ Ub) ((W ⊓ Ub).map T)
    rw [hFT, finrank_bot, add_zero,
      ← (Submodule.equivMapOfInjective T hTinj' (W ⊓ Ub)).finrank_eq] at h1
    have h2 : finrank (ZMod 2) ↥((W ⊓ Ub) ⊔ (W ⊓ Ub).map T) ≤ finrank (ZMod 2) W :=
      Submodule.finrank_mono (sup_le inf_le_left hFTW)
    omega
  have hrankU : finrank (ZMod 2) W + finrank (ZMod 2) Ub ≤
      finrank (ZMod 2) V + finrank (ZMod 2) ↥(W ⊓ Ub) := by
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq W Ub
    have h2 := Submodule.finrank_le (W ⊔ Ub)
    omega
  have hfixB : fixSpace ρ B ≤ Ub := fun v hv => (hmemU v).2 (hv b hbB)
  have hB1 := Submodule.finrank_mono hfixB
  have hU1 := Submodule.finrank_le Ub
  have hW6 : finrank (ZMod 2) W ≤ 6 := by omega
  have hmapW : ∀ g : Perm (Fin 5), W.map (ρ (g, 1) : V →ₗ[ZMod 2] V) = W := by
    intro g
    apply le_antisymm
    · rintro _ ⟨w, hw, rfl⟩
      exact hpresW _ (hkd g) w hw
    · intro w hw
      refine ⟨ρ (g⁻¹, 1) w, hpresW _ (hkd g⁻¹) w hw, ?_⟩
      show ρ' (g, 1) (ρ' (g⁻¹, 1) w) = w
      rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_inv_cancel, mul_one,
        ← Prod.one_eq_mk, map_one, Module.End.one_apply]
  let β : Perm (Fin 5) →* (W ≃ₗ[ZMod 2] W) :=
    { toFun := fun g => (ρ (g, 1)).ofSubmodules W W (hmapW g)
      map_one' := LinearEquiv.ext fun w => Subtype.ext (by
        rw [LinearEquiv.ofSubmodules_apply, ← Prod.one_eq_mk, map_one]
        rfl)
      map_mul' := fun g h => LinearEquiv.ext fun w => Subtype.ext (by
        rw [LinearEquiv.ofSubmodules_apply]
        show ρ' (g * h, 1) w = ρ' (g, 1) (ρ' (h, 1) w)
        rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]) }
  have hβapp : ∀ g (w : W), (β g w : V) = ρ (g, 1) w := fun _ _ => rfl
  set J : Module.End (ZMod 2) W := T.restrict hTW with hJdef
  have hJapp : ∀ w : W, (J w : V) = T w := fun _ => rfl
  have hJ : J ^ 2 + J + 1 = 0 := by
    refine LinearMap.ext fun w => Subtype.ext ?_
    obtain ⟨u, hu⟩ := LinearMap.mem_range.1 w.2
    have h := LinearMap.congr_fun heT u
    rw [Module.End.mul_apply, LinearMap.zero_apply, hu, LinearMap.add_apply,
      LinearMap.add_apply, Module.End.one_apply, pow_two, Module.End.mul_apply] at h
    rw [LinearMap.add_apply, LinearMap.add_apply, Module.End.one_apply, pow_two,
      Module.End.mul_apply, LinearMap.zero_apply, Submodule.coe_add, Submodule.coe_add,
      ZeroMemClass.coe_zero]
    simp only [hJapp]
    exact h
  have hβJ : ∀ g w, β g (J w) = J (β g w) := by
    intro g w
    apply Subtype.ext
    simp only [hβapp, hJapp]
    exact LinearMap.congr_fun (hcommT _ (hkd g)) (w : V)
  have hkill := A7_small_binary_S5_representations_kill_A5 hW6 J hJ β hβJ
  have hKx : ∀ x ∈ K, x = (x.1, 1) ∧ x.1 ∈ alternatingGroup (Fin 5) := by
    intro x hx
    obtain ⟨h1, h2⟩ := Subgroup.mem_prod.1 hx
    exact ⟨Prod.ext rfl (Subgroup.mem_bot.1 h2), h1⟩
  have hKW : ∀ x ∈ K, ∀ w ∈ W, ρ x w = w := by
    intro x hx w hw
    obtain ⟨hx1, hxA⟩ := hKx x hx
    have h := congrArg (fun e : W ≃ₗ[ZMod 2] W => (e ⟨w, hw⟩ : V)) (hkill x.1 hxA)
    rw [hx1]
    exact h
  have hKd : ∀ x ∈ K, x * d = d * x := by
    intro x hx
    rw [(hKx x hx).1]
    exact hkd x.1
  have hle : commSpace ρ K ≤ C := by
    rw [commSpace, Submodule.span_le]
    rintro _ ⟨x, hx, v, rfl⟩
    have hv : v ∈ C ⊔ W := by
      rw [hcompl.sup_eq_top]
      exact Submodule.mem_top
    obtain ⟨c', hc', w, hw, rfl⟩ := Submodule.mem_sup.1 hv
    rw [SetLike.mem_coe, map_add, hKW x hx w hw, add_sub_add_right_eq_sub]
    exact C.sub_mem (hpresC x (hKd x hx) c' hc') hc'
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hWeq]
    exact hKW
  · rw [hCeq, hWeq]
    exact hcompl
  · rw [hWeq]
    exact hW6
  · rw [hCeq]
    exact hle
  · rw [eq_bot_iff, hWeq]
    intro v hv
    obtain ⟨hvK, hvD⟩ := Submodule.mem_inf.1 hv
    exact (Submodule.mem_bot _).2 (Submodule.disjoint_def.1 hcompl.disjoint v (hle hvK) hvD)

end CFSG.Quasithin.H13.A7
