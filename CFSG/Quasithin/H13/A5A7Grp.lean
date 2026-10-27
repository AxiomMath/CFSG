module

public import CFSG.Quasithin.H13.A5L3Grp
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open Equiv

theorem cycleType_22 :
    (swap (0 : Fin 7) 1 * swap 2 3).cycleType = Multiset.replicate 2 2 := by
  have hd : Perm.Disjoint (swap (0 : Fin 7) 1) (swap 2 3) := fun x => by
    fin_cases x <;> decide
  rw [hd.cycleType_mul, (Perm.isCycle_swap (by decide)).cycleType,
    (Perm.isCycle_swap (by decide)).cycleType, Perm.card_support_swap (by decide),
    Perm.card_support_swap (by decide)]
  rfl

theorem cycleType_222 :
    (swap (0 : Fin 7) 1 * swap 2 3 * swap 4 5).cycleType = Multiset.replicate 3 2 := by
  have hd : Perm.Disjoint (swap (0 : Fin 7) 1 * swap 2 3) (swap 4 5) := fun x => by
    fin_cases x <;> decide
  rw [hd.cycleType_mul, cycleType_22, (Perm.isCycle_swap (by decide)).cycleType,
    Perm.card_support_swap (by decide)]
  rfl

theorem isSwap_of_pair {σ : Perm (Fin 7)} (h2 : σ * σ = 1) (h1 : σ ≠ 1)
    (hp : ∀ τ ∈ alternatingGroup (Fin 7), (∃ k : ℕ, (σ * (τ * σ * τ⁻¹)) ^ 2 ^ k = 1) ∨
      (σ * (τ * σ * τ⁻¹)) ^ 3 = 1) : σ.IsSwap := by
  have hord : orderOf σ = 2 := orderOf_eq_prime (by rw [pow_two]; exact h2) h1
  have hct : ∀ n ∈ σ.cycleType, n = 2 := fun n hn =>
    le_antisymm (Nat.le_of_dvd (by norm_num) (hord ▸ Perm.dvd_of_mem_cycleType hn))
      (Perm.two_le_of_mem_cycleType hn)
  set k := Multiset.card σ.cycleType with hk_def
  have hrep : σ.cycleType = Multiset.replicate k 2 := Multiset.eq_replicate.mpr ⟨rfl, hct⟩
  have hsum : 2 * k ≤ 7 := by
    have h := σ.sum_cycleType
    rw [hrep, Multiset.sum_replicate, smul_eq_mul] at h
    have h7 := σ.support.card_le_univ
    rw [Fintype.card_fin] at h7
    omega
  have hk0 : k ≠ 0 := by
    intro h0
    apply h1
    rw [← Perm.cycleType_eq_zero, hrep, h0, Multiset.replicate_zero]
  have hbad : ∀ σ₀ τ₀ : Perm (Fin 7), σ.cycleType = σ₀.cycleType → τ₀ ∈ alternatingGroup (Fin 7) →
      (σ₀ * (τ₀ * σ₀ * τ₀⁻¹)) ^ 5 = 1 → σ₀ * (τ₀ * σ₀ * τ₀⁻¹) ≠ 1 → False := by
    intro σ₀ τ₀ hc hτ h5 hne
    have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    obtain ⟨ρ, hρ⟩ := isConj_iff.mp (Perm.isConj_iff_cycleType_eq.mpr hc.symm)
    have hx₀ : orderOf (σ₀ * (τ₀ * σ₀ * τ₀⁻¹)) = 5 :=
      orderOf_eq_prime h5 hne
    have hτm : ρ * τ₀ * ρ⁻¹ ∈ alternatingGroup (Fin 7) :=
      (alternatingGroup.normal (α := Fin 7)).conj_mem _ hτ ρ
    have hx : σ * ((ρ * τ₀ * ρ⁻¹) * σ * (ρ * τ₀ * ρ⁻¹)⁻¹) =
        ρ * (σ₀ * (τ₀ * σ₀ * τ₀⁻¹)) * ρ⁻¹ := by
      rw [← hρ]
      group
    have hconj : ∀ m : ℕ, (σ * ((ρ * τ₀ * ρ⁻¹) * σ * (ρ * τ₀ * ρ⁻¹)⁻¹)) ^ m = 1 →
        (σ₀ * (τ₀ * σ₀ * τ₀⁻¹)) ^ m = 1 := by
      intro m hm
      rw [hx, conj_pow] at hm
      have := congrArg (fun z => ρ⁻¹ * z * ρ) hm
      simpa [mul_assoc] using this
    rcases hp _ hτm with ⟨m, hm⟩ | h3
    · have h := orderOf_dvd_of_pow_eq_one (hconj _ hm)
      rw [hx₀] at h
      exact absurd ((Nat.Prime.dvd_of_dvd_pow (by norm_num) h)) (by norm_num)
    · have h := orderOf_dvd_of_pow_eq_one (hconj _ h3)
      rw [hx₀] at h
      exact absurd h (by norm_num)
  obtain hk | hk | hk : k = 1 ∨ k = 2 ∨ k = 3 := by omega
  · rw [← Perm.card_support_eq_two, ← Perm.sum_cycleType, hrep, hk]
    rfl
  · exact (hbad (swap 0 1 * swap 2 3) (swap 1 2 * swap 3 4) (by rw [hrep, hk, cycleType_22])
      (Perm.mem_alternatingGroup.mpr (by decide)) (by decide +kernel) (by decide +kernel)).elim
  · exact (hbad (swap 0 1 * swap 2 3 * swap 4 5) (swap 3 4 * swap 5 6)
      (by rw [hrep, hk, cycleType_222])
      (Perm.mem_alternatingGroup.mpr (by decide)) (by decide +kernel) (by decide +kernel)).elim

abbrev P01 : Perm (Fin 7) := swap 0 1

theorem fix_iff_of_comm {g : Perm (Fin 7)} (hg : g * P01 = P01 * g) (x : Fin 7) :
    P01 (g x) = g x ↔ P01 x = x := by
  have h : ∀ y, P01 (g y) = g (P01 y) := fun y => by
    have := congrArg (fun f : Perm (Fin 7) => f y) hg
    simpa [Perm.mul_apply] using this.symm
  rw [h, g.injective.eq_iff]

@[expose] def restrP : Subgroup.centralizer {P01} →* Perm {x : Fin 7 // P01 x = x} where
  toFun g := (g : Perm (Fin 7)).subtypePerm (fix_iff_of_comm
    (Subgroup.mem_centralizer_singleton_iff.mp g.2))
  map_one' := by ext; rfl
  map_mul' _ _ := by ext; rfl

theorem card_fixP : Nat.card {x : Fin 7 // P01 x = x} = 5 := by
  rw [Nat.card_eq_fintype_card]
  decide


theorem mul_self_eq_one_of_fix {z : Perm (Fin 7)} (hz : z * P01 = P01 * z)
    (hfix : ∀ x, P01 x = x → z x = x) : z * z = 1 := by
  have h : ∀ y, P01 (z y) = z (P01 y) := fun y => by
    have := congrArg (fun f : Perm (Fin 7) => f y) hz
    simpa [Perm.mul_apply] using this.symm
  have hmoved : ∀ y : Fin 7, P01 y ≠ y → y = 0 ∨ y = 1 := by decide
  refine Equiv.ext fun x => ?_
  rw [Perm.mul_apply, Perm.one_apply]
  by_cases hx : P01 x = x
  · rw [hfix x hx, hfix x hx]
  · have hzx : P01 (z x) ≠ z x := by
      rw [h]
      exact fun h' => hx (z.injective h')
    rcases hmoved x hx with rfl | rfl <;> rcases hmoved _ hzx with h0 | h0
    · rw [h0, h0]
    · have h1 : z 1 = 0 := by
        have := h 0
        rw [h0] at this
        simpa using this.symm
      rw [h0, h1]
    · have h1 : z 0 = 1 := by
        have := h 1
        rw [h0] at this
        simpa using this.symm
      rw [h0, h1]
    · rw [h0, h0]

theorem ofSubtype_comm (π : Perm {x : Fin 7 // P01 x = x}) :
    Perm.ofSubtype π * P01 = P01 * Perm.ofSubtype π := by
  refine Equiv.ext fun x => ?_
  rw [Perm.mul_apply, Perm.mul_apply]
  by_cases hx : P01 x = x
  · rw [hx, Perm.ofSubtype_apply_of_mem π hx]
    exact ((π ⟨x, hx⟩).2).symm
  · have hPx : ¬ P01 (P01 x) = P01 x := fun h => hx (P01.injective h)
    rw [Perm.ofSubtype_apply_of_not_mem π hx, Perm.ofSubtype_apply_of_not_mem π hPx]

theorem mul_self_eq_one_of_normalized (Ŷ : Subgroup (Perm (Fin 7)))
    (hc : Ŷ ≤ Subgroup.centralizer {P01})
    (hn : ∀ τ ∈ alternatingGroup (Fin 7), τ * P01 = P01 * τ → ∀ z ∈ Ŷ, τ * z * τ⁻¹ ∈ Ŷ)
    (hs : Group.IsSolvable ↥Ŷ) : ∀ z ∈ Ŷ, z * z = 1 := by
  classical
  set C := Subgroup.centralizer {P01} with hC
  set H : Subgroup (Perm {x : Fin 7 // P01 x = x}) := (Ŷ.subgroupOf C).map restrP with hH
  have hYs : Group.IsSolvable ↥(Ŷ.subgroupOf C) :=
    Group.isSolvable_of_surjective (f := (Subgroup.subgroupOfEquivOfLe hc).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hc).symm.surjective
  have hHs : Group.IsSolvable ↥H := Group.isSolvable_of_surjective (restrP.subgroupMap_surjective _)
  have hHn : H.Normal := by
    refine ⟨fun h hh π => ?_⟩
    obtain ⟨⟨z, hzC⟩, hzY, rfl⟩ := hh
    have hzY' : z ∈ Ŷ := hzY
    let g := Perm.ofSubtype π
    have hg : g * P01 = P01 * g := ofSubtype_comm π
    have hsP : Perm.sign P01 = -1 := Perm.sign_swap (by decide)
    obtain ⟨τ, hτA, hτP, hτr⟩ : ∃ τ : Perm (Fin 7), τ ∈ alternatingGroup (Fin 7) ∧
        τ * P01 = P01 * τ ∧ ∀ x : {x : Fin 7 // P01 x = x}, τ x = π x := by
      rcases Int.units_eq_one_or (Perm.sign g) with h1 | h1
      · refine ⟨g, Perm.mem_alternatingGroup.mpr h1, hg, fun x => ?_⟩
        exact Perm.ofSubtype_apply_coe π x
      · refine ⟨g * P01, Perm.mem_alternatingGroup.mpr ?_, ?_, fun x => ?_⟩
        · rw [Perm.sign_mul, h1, hsP]
          rfl
        · calc g * P01 * P01 = P01 * g * P01 := by rw [hg]
            _ = P01 * (g * P01) := by rw [mul_assoc]
        · rw [Perm.mul_apply, x.2]
          exact Perm.ofSubtype_apply_coe π x
    have hτz : τ * z * τ⁻¹ ∈ Ŷ := hn τ hτA hτP z hzY'
    have hτzC : τ * z * τ⁻¹ ∈ C := hc hτz
    refine ⟨⟨τ * z * τ⁻¹, hτzC⟩, hτz, ?_⟩
    have hτinv : ∀ y : {x : Fin 7 // P01 x = x}, τ⁻¹ (y : Fin 7) = ((π⁻¹ y :
        {x : Fin 7 // P01 x = x}) : Fin 7) := by
      intro y
      have h1 := hτr (π⁻¹ y)
      have h2 : π (π⁻¹ y) = y := Equiv.apply_symm_apply π y
      rw [h2] at h1
      rw [← h1]
      exact Equiv.symm_apply_apply τ _
    refine Equiv.ext fun x => Subtype.ext ?_
    show τ (z (τ⁻¹ (x : Fin 7))) =
      ((π (restrP ⟨z, hzC⟩ (π⁻¹ x)) : {x : Fin 7 // P01 x = x}) : Fin 7)
    rw [hτinv]
    exact hτr (restrP ⟨z, hzC⟩ (π⁻¹ x))
  have hHb : H = ⊥ := by
    by_contra hne
    have hnt : Nontrivial ↥H := (Subgroup.nontrivial_iff_ne_bot H).mpr hne
    have hcard : 5 ≤ Nat.card {x : Fin 7 // P01 x = x} := card_fixP.ge
    have hA := Perm.alternatingGroup_le_of_normal hcard hnt
    have hAs : Group.IsSolvable ↥(alternatingGroup {x : Fin 7 // P01 x = x}) :=
      Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hA)
    have hPs : Group.IsSolvable (Perm {x : Fin 7 // P01 x = x}) :=
      Group.isSolvable_of_ker_le_range (alternatingGroup {x : Fin 7 // P01 x = x}).subtype Perm.sign
        (by rw [Subgroup.range_subtype]; exact le_rfl)
    apply Perm.not_isSolvable {x : Fin 7 // P01 x = x} _ hPs
    rw [Cardinal.mk_fintype, ← Nat.card_eq_fintype_card, card_fixP]
    norm_num
  intro z hz
  have hzC : z ∈ C := hc hz
  refine mul_self_eq_one_of_fix (Subgroup.mem_centralizer_singleton_iff.mp hzC) fun x hx => ?_
  have h1 : restrP ⟨z, hzC⟩ ∈ H := ⟨⟨z, hzC⟩, hz, rfl⟩
  rw [hHb, Subgroup.mem_bot] at h1
  have h2 := congrArg (fun f : Perm {x : Fin 7 // P01 x = x} => ((f ⟨x, hx⟩ : _) : Fin 7)) h1
  simpa [restrP] using h2

theorem factA7Grp1321 : FactA7Grp1321 := by
  intro K _ _ hK ⟨π, hπ⟩ v hv1 hv2 hpair Y hYc hYn hYs hY
  have : IsSimpleGroup ↥(alternatingGroup (Fin 7)) :=
    alternatingGroup.isSimpleGroup (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; norm_num)
  have hinj : Function.Injective π := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal π.ker with h | h
    · exact (MonoidHom.ker_eq_bot_iff π).1 h
    · exfalso
      obtain ⟨a, ha⟩ := exists_ne (1 : K)
      obtain ⟨g, rfl⟩ := hπ a
      exact ha (MonoidHom.mem_ker.1 (h ▸ Subgroup.mem_top g))
  let e : ↥(alternatingGroup (Fin 7)) ≃* K := MulEquiv.ofBijective π ⟨hinj, hπ⟩
  let Θ : Perm (Fin 7) ≃* MulAut ↥(alternatingGroup (Fin 7)) :=
    MulEquiv.ofBijective MulAut.conjNormal
      (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 7 (by norm_num)
        (by norm_num))
  let Ψ : MulAut K ≃* Perm (Fin 7) := (MulAut.congr e.symm).trans Θ.symm
  have hΘ : ∀ (σ : Perm (Fin 7)) (a : ↥(alternatingGroup (Fin 7))),
      ((Θ σ a : ↥(alternatingGroup (Fin 7))) : Perm (Fin 7)) = σ * a * σ⁻¹ :=
    fun σ a => MulAut.conjNormal_apply σ a
  have hΨ : ∀ (α : MulAut K) (k : K),
      ((e.symm (α k) : ↥(alternatingGroup (Fin 7))) : Perm (Fin 7)) =
        Ψ α * ((e.symm k : ↥(alternatingGroup (Fin 7))) : Perm (Fin 7)) * (Ψ α)⁻¹ := by
    intro α k
    have h1 : Θ (Ψ α) = MulAut.congr e.symm α := Θ.apply_symm_apply _
    rw [← hΘ, h1]
    show ((e.symm (α k) : ↥(alternatingGroup (Fin 7))) : Perm (Fin 7)) =
      ((e.symm (α (e.symm.symm (e.symm k))) : ↥(alternatingGroup (Fin 7))) : Perm (Fin 7))
    rw [MulEquiv.symm_symm, MulEquiv.apply_symm_apply]
  have hΨc : ∀ g : K, Ψ (MulAut.conj g) = ((e.symm g : ↥(alternatingGroup (Fin 7))) :
      Perm (Fin 7)) := by
    intro g
    apply Θ.injective
    rw [show Θ (Ψ (MulAut.conj g)) = MulAut.congr e.symm (MulAut.conj g) from
      Θ.apply_symm_apply _]
    refine MulEquiv.ext fun a => Subtype.ext ?_
    rw [hΘ]
    show ((e.symm (g * e a * g⁻¹) : ↥(alternatingGroup (Fin 7))) : Perm (Fin 7)) = _
    rw [map_mul, map_mul, map_inv, MulEquiv.symm_apply_apply]
    rfl
  set σ := Ψ v with hσ
  have hσ2 : σ * σ = 1 := by rw [hσ, ← map_mul, hv2, map_one]
  have hσ1 : σ ≠ 1 := fun h => hv1 (Ψ.injective (h.trans (map_one Ψ).symm))
  have hsw : σ.IsSwap := by
    refine isSwap_of_pair hσ2 hσ1 fun τ hτ => ?_
    have hmap : Ψ (v * (MulAut.conj (e ⟨τ, hτ⟩) * v * (MulAut.conj (e ⟨τ, hτ⟩))⁻¹)) =
        σ * (τ * σ * τ⁻¹) := by
      rw [map_mul, map_mul, map_mul, map_inv, hΨc, MulEquiv.symm_apply_apply]
    rcases hpair (e ⟨τ, hτ⟩) with ⟨k, hk⟩ | h3
    · exact Or.inl ⟨k, by rw [← hmap, ← map_pow, hk, map_one]⟩
    · exact Or.inr (by rw [← hmap, ← map_pow, h3, map_one])
  obtain ⟨a, b, hab, hσab⟩ := hsw
  obtain ⟨ρ, hρ⟩ := isConj_iff.mp (Perm.isConj_swap (show (0 : Fin 7) ≠ 1 by decide) hab)
  have hσρ : σ = ρ * P01 * ρ⁻¹ := by rw [hσab, ← hρ]
  set Ŷ : Subgroup (Perm (Fin 7)) :=
    (Y.map (Ψ : MulAut K →* Perm (Fin 7))).map (MulAut.conj ρ⁻¹).toMonoidHom with hŶ
  have hmemŶ : ∀ y ∈ Y, ρ⁻¹ * Ψ y * ρ ∈ Ŷ := by
    intro y hy
    refine ⟨Ψ y, ⟨y, hy, rfl⟩, ?_⟩
    show ρ⁻¹ * Ψ y * ρ⁻¹⁻¹ = ρ⁻¹ * Ψ y * ρ
    rw [inv_inv]
  have hŶmem : ∀ z ∈ Ŷ, ∃ y ∈ Y, z = ρ⁻¹ * Ψ y * ρ := by
    rintro z ⟨w, ⟨y, hy, rfl⟩, rfl⟩
    refine ⟨y, hy, ?_⟩
    show ρ⁻¹ * Ψ y * ρ⁻¹⁻¹ = ρ⁻¹ * Ψ y * ρ
    rw [inv_inv]
  have hcomm : ∀ y ∈ Y, Ψ y * σ = σ * Ψ y := by
    intro y hy
    have h1 : y * v = v * y := Subgroup.mem_centralizer_singleton_iff.mp (hYc hy)
    rw [hσ, ← map_mul, ← map_mul, h1]
  have hc : Ŷ ≤ Subgroup.centralizer {P01} := by
    intro z hz
    obtain ⟨y, hy, rfl⟩ := hŶmem z hz
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 := hcomm y hy
    rw [hσρ] at h1
    calc ρ⁻¹ * Ψ y * ρ * P01 = ρ⁻¹ * (Ψ y * (ρ * P01 * ρ⁻¹)) * ρ := by group
      _ = ρ⁻¹ * ((ρ * P01 * ρ⁻¹) * Ψ y) * ρ := by rw [h1]
      _ = P01 * (ρ⁻¹ * Ψ y * ρ) := by group
  have hn : ∀ τ ∈ alternatingGroup (Fin 7), τ * P01 = P01 * τ → ∀ z ∈ Ŷ,
      τ * z * τ⁻¹ ∈ Ŷ := by
    intro τ hτ hτP z hz
    obtain ⟨y, hy, rfl⟩ := hŶmem z hz
    have hτ' : ρ * τ * ρ⁻¹ ∈ alternatingGroup (Fin 7) :=
      (alternatingGroup.normal (α := Fin 7)).conj_mem _ hτ ρ
    set k : K := e ⟨ρ * τ * ρ⁻¹, hτ'⟩ with hk
    have hσk : σ * (ρ * τ * ρ⁻¹) = (ρ * τ * ρ⁻¹) * σ := by
      rw [hσρ]
      calc ρ * P01 * ρ⁻¹ * (ρ * τ * ρ⁻¹) = ρ * (P01 * τ) * ρ⁻¹ := by group
        _ = ρ * (τ * P01) * ρ⁻¹ := by rw [hτP]
        _ = ρ * τ * ρ⁻¹ * (ρ * P01 * ρ⁻¹) := by group
    have hvk : v k = k := by
      apply e.symm.injective
      apply Subtype.ext
      rw [hΨ, ← hσ, hk, MulEquiv.symm_apply_apply]
      show σ * (ρ * τ * ρ⁻¹) * σ⁻¹ = ρ * τ * ρ⁻¹
      rw [hσk, mul_assoc, mul_inv_cancel, mul_one]
    have h1 := hYn k hvk y hy
    have h2 := hmemŶ _ h1
    have h3 : Ψ (MulAut.conj k) = ρ * τ * ρ⁻¹ := by
      rw [hΨc, hk, MulEquiv.symm_apply_apply]
    rw [map_mul, map_mul, map_inv, h3] at h2
    have h4 : ρ⁻¹ * (ρ * τ * ρ⁻¹ * Ψ y * (ρ * τ * ρ⁻¹)⁻¹) * ρ = τ * (ρ⁻¹ * Ψ y * ρ) * τ⁻¹ := by
      group
    rwa [h4] at h2
  have hs : Group.IsSolvable ↥Ŷ := by
    have : Group.IsSolvable ↥(Y.map (Ψ : MulAut K →* Perm (Fin 7))) :=
      Group.isSolvable_of_surjective (MonoidHom.subgroupMap_surjective _ Y)
    exact Group.isSolvable_of_surjective (MonoidHom.subgroupMap_surjective _ _)
  have hinv := mul_self_eq_one_of_normalized Ŷ hc hn hs
  refine eq_bot_of_pow16 hY fun y hy => ?_
  have h1 := hinv _ (hmemŶ y hy)
  have h2 : Ψ (y * y) = 1 := by
    rw [map_mul]
    have := congrArg (fun z => ρ * z * ρ⁻¹) h1
    simpa [mul_assoc] using this
  rw [← map_one Ψ] at h2
  have h3 : y * y = 1 := Ψ.injective h2
  calc y ^ 16 = (y * y) ^ 8 := by rw [← pow_two, ← pow_mul]
    _ = 1 := by rw [h3, one_pow]

end CFSG.Quasithin.H13.A5
