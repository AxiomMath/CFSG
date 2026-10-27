module

public import CFSG.RankThree.PartOne.S11c.Sec66TFamily
public import CFSG.RankThree.PartOne.S11c.SuFiveGroup

public section

namespace CFSG.RankThree.PartOne.Sec66T

open Matrix CFSG CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne

section Congr

theorem localRankAut_congr {T X : Type} [Group T] [Group X] (e : T ≃* X) {p : ℕ}
    (hp : p.Prime) {α : MulAut T} (h : LocalRankAut p T α) :
    LocalRankAut p X (MulAut.congr e α) := by
  have : Fact p.Prime := ⟨hp⟩
  intro hα5 hαinn R hR hRcard hRfix U hU1 hU2 hUinv hRU
  have hα5' : α ^ p = 1 := by
    apply (MulAut.congr e).injective
    rw [map_pow, map_one]
    exact hα5
  have hαinn' : α ∉ innerAut T := fun hmem => hαinn ((mem_innerAut_congr e α).mpr hmem)
  have hcongr : ∀ x, MulAut.congr e α x = e (α (e.symm x)) := fun x => rfl
  refine h hα5' hαinn' (R.map e.symm.toMonoidHom) (IsElementaryAbelian.map (A := R) _) ?_ ?_
    (U.map e.symm.toMonoidHom) ?_ (hU2.map _) ?_ ?_
  · rw [Subgroup.card_map_of_injective e.symm.injective, hRcard]
  · rintro _ ⟨r, hr, rfl⟩
    have h1 := hRfix r hr
    rw [hcongr] at h1
    have h2 := congrArg e.symm h1
    rw [MulEquiv.symm_apply_apply] at h2
    exact h2
  · intro hbot
    exact hU1 ((Subgroup.map_eq_bot_iff_of_injective U e.symm.injective).mp hbot)
  · rintro _ ⟨u, hu, rfl⟩
    refine ⟨MulAut.congr e α u, hUinv u hu, ?_⟩
    rw [hcongr]
    simp
  · rintro _ ⟨r, hr, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have h1 := (Subgroup.mem_normalizer_iff.mp (hRU hr)) (e x)
    simp only [Subgroup.mem_map_equiv, MulEquiv.symm_symm, MulEquiv.coe_toMonoidHom, map_mul,
      map_inv, MulEquiv.apply_symm_apply]
    exact h1

end Congr

section Frame

variable {f : ℕ} {K : Type} [Field K]

abbrev psu5 (h : UnitaryFieldData 2 f K) : Type :=
  primeFormP h ((1 : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K)

noncomputable abbrev proj5 (h : UnitaryFieldData 2 f K) : gamma5 h →* psu5 h :=
  QuotientGroup.mk' (normOneScalars h (gamma5 h) 5)

variable (h : UnitaryFieldData 2 f K)

theorem normOneScalars_le_frameA (M : unit5 h) (i j : Fin 5) :
    normOneScalars h (gamma5 h) 5 ≤ frameA h M i j := by
  rintro z ⟨c, hc, hc5, hz⟩
  refine ⟨z, Subgroup.mem_subgroupOf.mpr ?_, ?_⟩
  · rw [mem_torusEq_iff]
    refine ⟨fun _ => c, fun _ => hc5, ?_, rfl, ?_⟩
    · simp [hc5]
    · rw [hz]
      apply Units.ext
      simp [KFU.diagU_val, Matrix.scalar_apply]
  · apply Subtype.ext
    show (M : GL (Fin 5) K) * (z : GL (Fin 5) K) * (M : GL (Fin 5) K)⁻¹ = z
    rw [hz]
    exact (commute_scalar c (M : GL (Fin 5) K)).mul_inv_cancel

theorem card_map_frameA (h5 : 5 ∣ 2 ^ f + 1) (M : unit5 h) {i j : Fin 5} (hij : i ≠ j) :
    Nat.card ((frameA h M i j).map (proj5 h)) = 5 ^ 2 := by
  have hfin : Finite K := h.finite
  let φ : ↥(frameA h M i j) →* psu5 h := (proj5 h).comp (frameA h M i j).subtype
  have hZle := normOneScalars_le_frameA h M i j
  have hker : φ.ker = (normOneScalars h (gamma5 h) 5).subgroupOf (frameA h M i j) := by
    ext ⟨a, ha⟩
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact QuotientGroup.eq_one_iff a
  have hrange : φ.range = (frameA h M i j).map (proj5 h) := by
    ext x
    constructor
    · rintro ⟨⟨a, ha⟩, rfl⟩
      exact ⟨a, ha, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨⟨a, ha⟩, rfl⟩
  have hZcard : Nat.card (normOneScalars h (gamma5 h) 5) = 5 := by
    rw [CFSG.RankThree.Classical.card_normOneScalars_one h (by norm_num)]
    exact Nat.gcd_eq_left h5
  have hkercard : Nat.card φ.ker = 5 := by
    rw [hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZle).toEquiv, hZcard]
  have h1 := Subgroup.card_ker_mul_card_range φ
  rw [hkercard, hrange, card_frameA h h5 M hij] at h1
  have h5pos : 0 < 5 := by norm_num
  have : 5 * Nat.card ((frameA h M i j).map (proj5 h)) = 5 * 5 ^ 2 := by
    rw [h1]
    norm_num
  exact Nat.eq_of_mul_eq_mul_left h5pos this

theorem not_localRankAut_of_frame (h5 : 5 ∣ 2 ^ f + 1) (M : unit5 h) {i j : Fin 5} (hij : i ≠ j)
    (ψ : MulAut (psu5 h)) (hψ5 : ψ ^ 5 = 1) (hψinn : ψ ∉ innerAut (psu5 h))
    (hA : ∀ a ∈ frameA h M i j, ψ (proj5 h a) = proj5 h a)
    (hr : ψ (proj5 h (frameR h M i j)) = proj5 h (frameR h M i j)) :
    ¬ LocalRankAut 5 (psu5 h) ψ := by
  intro hra
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hfin : Finite K := h.finite
  have hel := isElementaryAbelian_frameA h h5 M i j
  set r : gamma5 h := frameR h M i j with hrdef
  set x₀ : psu5 h := proj5 h r with hx₀
  have hr2 : r ^ 2 = 1 := by
    have := pow_orderOf_eq_one r
    rwa [orderOf_frameR h M hij] at this
  have hx₀2 : x₀ ^ 2 = 1 := by
    rw [hx₀, ← map_pow, hr2, map_one]
  have hx₀1 : x₀ ≠ 1 := by
    intro hx
    have hZ : r ∈ normOneScalars h (gamma5 h) 5 := (QuotientGroup.eq_one_iff r).mp hx
    obtain ⟨c, -, -, hc⟩ := hZ
    have hsw : KFSU5.swapUnit K i j = Matrix.GeneralLinearGroup.scalar (Fin 5) c := by
      have h1 : (M : GL (Fin 5) K) * KFSU5.swapUnit K i j * (M : GL (Fin 5) K)⁻¹ =
          Matrix.GeneralLinearGroup.scalar (Fin 5) c := by
        rw [← coe_frameR, ← hrdef, hc]
      have h2 : KFSU5.swapUnit K i j = (M : GL (Fin 5) K)⁻¹ *
          ((M : GL (Fin 5) K) * KFSU5.swapUnit K i j * (M : GL (Fin 5) K)⁻¹) *
            (M : GL (Fin 5) K) := by group
      rw [h2, h1, (commute_scalar c ((M : GL (Fin 5) K)⁻¹)).eq]
      group
    have := congrArg (fun g : GL (Fin 5) K => (g : Matrix (Fin 5) (Fin 5) K) i j) hsw
    simp [KFSU5.swapUnit_val, KFSU5.swapMatrix_apply, hij, Matrix.scalar_apply] at this
  refine hra hψ5 hψinn ((frameA h M i j).map (proj5 h)) (IsElementaryAbelian.map (A := _)
    (proj5 h)) (card_map_frameA h h5 M hij) ?_ (Subgroup.zpowers x₀) ?_ ?_ ?_ ?_
  · rintro _ ⟨a, ha, rfl⟩
    exact hA a ha
  · intro hbot
    apply hx₀1
    have : x₀ ∈ Subgroup.zpowers x₀ := Subgroup.mem_zpowers x₀
    rw [hbot] at this
    exact this
  · rintro ⟨_, k, rfl⟩
    refine ⟨1, Subtype.ext ?_⟩
    simp only [pow_one, Subgroup.coe_pow, OneMemClass.coe_one]
    rw [← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast, hx₀2,
      _root_.one_zpow]
  · rintro _ ⟨k, rfl⟩
    refine ⟨k, ?_⟩
    rw [map_zpow, hr]
  · have hcuU : ∀ b ∈ frameA h M i j, ∀ v ∈ Subgroup.zpowers x₀,
        proj5 h b * v * (proj5 h b)⁻¹ = v := by
      intro b hb v hv
      obtain ⟨k, rfl⟩ := hv
      have hcomm : Commute (proj5 h b) x₀ := by
        show proj5 h b * x₀ = x₀ * proj5 h b
        rw [hx₀, ← map_mul, ← map_mul, frameR_comm h M hb]
      exact (hcomm.zpow_right k).mul_inv_cancel
    rintro _ ⟨a, ha, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro u
    constructor
    · intro hu
      rw [hcuU a ha u hu]
      exact hu
    · intro hu
      have h1 := hcuU a⁻¹ ((frameA h M i j).inv_mem ha) _ hu
      rw [map_inv] at h1
      have h2 : (proj5 h a)⁻¹ * (proj5 h a * u * (proj5 h a)⁻¹) * ((proj5 h a)⁻¹)⁻¹ = u := by
        group
      rw [h2] at h1
      rw [h1]
      exact hu

end Frame

end CFSG.RankThree.PartOne.Sec66T
