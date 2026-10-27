module

public import CFSG.Quasithin.Vol2.Ch11L2Q5cL2Rank
public import CFSG.Quasithin.Vol2.Ch11L2Q5cOffender

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Open CFSG.QuasithinUnique
open CFSG.Quasithin.Vol2.Ch10.SecA (unipSL coe_unipSL unipSL_mulVec unipSL_zero diagSL coe_diagSL
  diagSL_conj diagSL_mulVec)

theorem orth_E_eq {K U : Type} [Field K] [CommGroup U] (hU : ∀ u : U, u * u = 1)
    (E : K → K → U) (hEadd : ∀ x s s', E x (s + s') = E x s * E x s')
    (hT : ∀ μ : K, μ ≠ 0 → ∀ x s, E (μ ^ 2 * x) s = E x (μ * s) * E (μ ^ 2) (x * s))
    {c d : K} (hc : c ≠ 0) (hd : d ≠ 0) (s : K) :
    E (d ^ 2) ((c + c ^ 2) * s) = E (c ^ 2) ((d + d ^ 2) * s) := by
  have key : ∀ x y z w : U, x * y = z * w → x * w = z * y := by
    intro x y z w h
    calc x * w = x * y * (y * w) := by rw [mul_assoc, ← mul_assoc y, hU, one_mul]
      _ = z * w * (y * w) := by rw [h]
      _ = z * y * (w * w) := by ac_rfl
      _ = z * y := by rw [hU, mul_one]
  have h1 := hT c hc (d ^ 2) s
  have h2 := hT d hd (c ^ 2) s
  rw [mul_comm (c ^ 2) (d ^ 2)] at h1
  rw [h1] at h2
  rw [add_mul, add_mul, hEadd, hEadd]
  exact key _ _ _ _ h2

section Core

variable {U : Type} [CommGroup U] [Finite U] {K : Type} [Field K] [CharP K 2] [Finite K]

theorem orth_core (hU : ∀ u : U, u ^ 2 = 1)
    (ρ : Matrix.SpecialLinearGroup (Fin 2) K →* MulAut U) (F : U →* Multiplicative (Fin 2 → K))
    (C : Subgroup U) (hFs : Function.Surjective F) (hFk : ∀ u, F u = 1 ↔ u ∈ C)
    (hFe : ∀ p u, Multiplicative.toAdd (F (ρ p u)) =
      (p : Matrix (Fin 2) (Fin 2) K).mulVec (Multiplicative.toAdd (F u)))
    (hC : ∀ p, ∀ c ∈ C, ρ p c = c)
    (hfixC : ∀ w, (∀ b, ρ (unipSL b) w * w⁻¹ ∈ C) → ∀ b, ρ (unipSL b) w = w)
    {c₀ : K} (hc0 : c₀ ≠ 0) (hc1 : c₀ ≠ 1)
    (hcard : Nat.card K * Nat.card K ≤
      Nat.card ↥(Subgroup.closure {w | ∃ b : K, ∃ v : U, ρ (unipSL b) v * v⁻¹ = w}))
    {α β : K} (hα : α ≠ 0) (hαβ : α ≠ β) {u v : U}
    (huv : ρ (unipSL α) u * u⁻¹ = ρ (unipSL β) v * v⁻¹) : ρ (unipSL α) u * u⁻¹ = 1 := by
  classical
  have hxx : ∀ x : U, x * x = 1 := fun x => by rw [← sq, hU]
  have h2K : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have hadd : ∀ x : K, x + x = 0 := fun x => by rw [← two_mul, h2K, zero_mul]
  set Y : U → K := fun w => Multiplicative.toAdd (F w) 1 with hYdef
  have hYmul : ∀ w w', Y (w * w') = Y w + Y w' := fun w w' => by
    simp only [hYdef, map_mul, toAdd_mul, Pi.add_apply]
  have hDmul : ∀ b w w', ρ (unipSL b) (w * w') * (w * w')⁻¹ =
      ρ (unipSL b) w * w⁻¹ * (ρ (unipSL b) w' * w'⁻¹) := fun b w w' => by
    rw [map_mul, mul_inv, mul_mul_mul_comm]
  have hFD : ∀ b w, Multiplicative.toAdd (F (ρ (unipSL b) w * w⁻¹)) = ![b * Y w, 0] := by
    intro b w
    rw [map_mul, map_inv, toAdd_mul, toAdd_inv, hFe, coe_unipSL, unipSL_mulVec]
    funext i
    fin_cases i <;> simp [hYdef]
  have hfix : ∀ w, Y w = 0 → ∀ b, ρ (unipSL b) w = w := by
    intro w hw
    refine hfixC w fun b => (hFk _).mp (Multiplicative.toAdd.injective ?_)
    rw [hFD, hw, mul_zero, toAdd_one]
    funext i
    fin_cases i <;> rfl
  have hA : ∀ b w w', Y w = Y w' → ρ (unipSL b) w * w⁻¹ = ρ (unipSL b) w' * w'⁻¹ := by
    intro b w w' h
    have hw0 : Y (w * w') = 0 := by rw [hYmul, h, hadd]
    have hw' : w' = w * (w * w') := by rw [← mul_assoc, hxx, one_mul]
    rw [hw', hDmul, hfix _ hw0, mul_inv_cancel, mul_one]
  choose σ hσ using fun s : K => hFs (Multiplicative.ofAdd ![0, s])
  have hYσ : ∀ s, Y (σ s) = s := fun s => by simp [hYdef, hσ]
  set δ : K → K → U := fun b s => ρ (unipSL b) (σ s) * (σ s)⁻¹ with hδdef
  have hDδ : ∀ b w, ρ (unipSL b) w * w⁻¹ = δ b (Y w) := fun b w =>
    hA b w (σ (Y w)) (hYσ _).symm
  have hδadd : ∀ b s s', δ b (s + s') = δ b s * δ b s' := by
    intro b s s'
    have h := hDδ b (σ s * σ s')
    rw [hDmul, hYmul, hYσ, hYσ] at h
    exact h.symm
  have hδ0 : ∀ b, δ b 0 = 1 := fun b => by
    have h := hδadd b 0 0
    rw [add_zero] at h
    exact mul_left_cancel (h.symm.trans (mul_one _).symm)
  have hδzero : ∀ s, δ 0 s = 1 := fun s => by
    show ρ (unipSL 0) (σ s) * (σ s)⁻¹ = 1
    rw [unipSL_zero, map_one, MulAut.one_apply, mul_inv_cancel]
  have hFδ : ∀ b s, Multiplicative.toAdd (F (δ b s)) = ![b * s, 0] := fun b s => by
    show Multiplicative.toAdd (F (ρ (unipSL b) (σ s) * (σ s)⁻¹)) = _
    rw [hFD, hYσ]
  have hYt : ∀ {μ : K} (hμ : μ ≠ 0) (w : U), Y (ρ (diagSL hμ) w) = μ⁻¹ * Y w := by
    intro μ hμ w
    simp only [hYdef]
    rw [hFe, coe_diagSL, diagSL_mulVec]
    simp
  have htD : ∀ {μ : K} (hμ : μ ≠ 0) (b : K) (w : U),
      ρ (diagSL hμ) (ρ (unipSL b) w * w⁻¹) = δ (μ ^ 2 * b) (μ⁻¹ * Y w) := by
    intro μ hμ b w
    have h1 : ρ (diagSL hμ) (ρ (unipSL b) w) = ρ (unipSL (μ ^ 2 * b)) (ρ (diagSL hμ) w) := by
      rw [← diagSL_conj hμ b, map_mul, map_mul, map_inv, MulAut.mul_apply, MulAut.mul_apply,
        MulAut.inv_apply_self]
    rw [map_mul, map_inv, h1, hDδ, hYt]
  have htδ : ∀ {μ : K} (hμ : μ ≠ 0) (b s : K),
      ρ (diagSL hμ) (δ b s) = δ (μ ^ 2 * b) (μ⁻¹ * s) := by
    intro μ hμ b s
    have h := htD hμ b (σ s)
    rw [hYσ] at h
    exact h
  set E : K → K → U := fun b s => δ b s * δ 1 (b * s) with hEdef
  have hEC : ∀ b s, E b s ∈ C := by
    intro b s
    refine (hFk _).mp (Multiplicative.toAdd.injective ?_)
    show Multiplicative.toAdd (F (δ b s * δ 1 (b * s))) = Multiplicative.toAdd 1
    rw [map_mul, toAdd_mul, hFδ, hFδ, one_mul, toAdd_one]
    funext i
    fin_cases i <;> simp [hadd]
  have hEadd : ∀ x s s', E x (s + s') = E x s * E x s' := by
    intro x s s'
    show δ x (s + s') * δ 1 (x * (s + s')) = δ x s * δ 1 (x * s) * (δ x s' * δ 1 (x * s'))
    rw [mul_add, hδadd, hδadd]
    exact mul_mul_mul_comm _ _ _ _
  have hE0 : ∀ x, E x 0 = 1 := fun x => by
    have h := hEadd x 0 0
    rw [add_zero] at h
    exact mul_left_cancel (h.symm.trans (mul_one _).symm)
  have hT : ∀ μ : K, μ ≠ 0 → ∀ x s, E (μ ^ 2 * x) s = E x (μ * s) * E (μ ^ 2) (x * s) := by
    intro μ hμ x s
    have h1 : ρ (diagSL hμ) (E x (μ * s)) = E x (μ * s) := hC _ _ (hEC _ _)
    have h2 : ρ (diagSL hμ) (E x (μ * s)) = δ (μ ^ 2 * x) s * δ (μ ^ 2) (x * s) := by
      show ρ (diagSL hμ) (δ x (μ * s) * δ 1 (x * (μ * s))) = _
      rw [map_mul, htδ, htδ, mul_one, inv_mul_cancel_left₀ hμ,
        show μ⁻¹ * (x * (μ * s)) = x * s by rw [mul_left_comm, inv_mul_cancel_left₀ hμ]]
    rw [h1] at h2
    rw [h2]
    show δ (μ ^ 2 * x) s * δ 1 (μ ^ 2 * x * s) =
      δ (μ ^ 2 * x) s * δ (μ ^ 2) (x * s) * (δ (μ ^ 2) (x * s) * δ 1 (μ ^ 2 * (x * s)))
    rw [← mul_assoc (μ ^ 2) x s, mul_assoc (δ (μ ^ 2 * x) s),
      ← mul_assoc (δ (μ ^ 2) (x * s)), hxx (δ (μ ^ 2) (x * s)), one_mul]
  have hk : c₀ + c₀ ^ 2 ≠ 0 := by
    intro h
    have h' : c₀ * (c₀ + 1) = 0 := by linear_combination h
    rcases mul_eq_zero.mp h' with h0 | h0
    · exact hc0 h0
    · exact hc1 (by linear_combination h0 - h2K)
  obtain ⟨rt, hrt⟩ : ∃ rt : K → K, ∀ x, x = rt x * rt x :=
    ⟨fun x => (FiniteField.isSquare_of_char_two (ringChar.eq K 2) x).choose,
      fun x => (FiniteField.isSquare_of_char_two (ringChar.eq K 2) x).choose_spec⟩
  have hrt2 : ∀ x, rt x ^ 2 = x := fun x => by rw [sq, ← hrt]
  let Ψ : Multiplicative K →* U :=
    { toFun := fun z => E (c₀ ^ 2) (Multiplicative.toAdd z / (c₀ + c₀ ^ 2))
      map_one' := by
        show E (c₀ ^ 2) (Multiplicative.toAdd 1 / (c₀ + c₀ ^ 2)) = 1
        rw [toAdd_one, zero_div]
        exact hE0 _
      map_mul' := fun z z' => by
        show E (c₀ ^ 2) (Multiplicative.toAdd (z * z') / (c₀ + c₀ ^ 2)) =
          E (c₀ ^ 2) (Multiplicative.toAdd z / (c₀ + c₀ ^ 2)) *
            E (c₀ ^ 2) (Multiplicative.toAdd z' / (c₀ + c₀ ^ 2))
        rw [toAdd_mul, add_div]
        exact hEadd _ _ _ }
  have hEform : ∀ x s, E x s = Ψ (Multiplicative.ofAdd ((rt x + x) * s)) := by
    intro x s
    show E x s = E (c₀ ^ 2)
      (Multiplicative.toAdd (Multiplicative.ofAdd ((rt x + x) * s)) / (c₀ + c₀ ^ 2))
    rw [toAdd_ofAdd]
    by_cases hd : rt x = 0
    · have hx : x = 0 := by rw [hrt x, hd, mul_zero]
      rw [hd, hx, zero_add, zero_mul, zero_div, hE0]
      show δ 0 s * δ 1 (0 * s) = 1
      rw [hδzero, zero_mul, hδ0, mul_one]
    · have h := orth_E_eq hxx E hEadd hT hc0 hd (s / (c₀ + c₀ ^ 2))
      have e1 : (c₀ + c₀ ^ 2) * (s / (c₀ + c₀ ^ 2)) = s := by
        rw [← mul_div_assoc, mul_div_cancel_left₀ s hk]
      rw [hrt2, e1, ← mul_div_assoc] at h
      exact h
  let Δ1 : Multiplicative K →* U :=
    { toFun := fun z => δ 1 (Multiplicative.toAdd z)
      map_one' := by
        show δ 1 (Multiplicative.toAdd 1) = 1
        rw [toAdd_one]
        exact hδ0 1
      map_mul' := fun z z' => by
        show δ 1 (Multiplicative.toAdd (z * z')) =
          δ 1 (Multiplicative.toAdd z) * δ 1 (Multiplicative.toAdd z')
        rw [toAdd_mul]
        exact hδadd 1 _ _ }
  have hgen : ∀ b w, ρ (unipSL b) w * w⁻¹ =
      Ψ.coprod Δ1 (Multiplicative.ofAdd ((rt b + b) * Y w), Multiplicative.ofAdd (b * Y w)) := by
    intro b w
    rw [MonoidHom.coprod_apply, hDδ]
    show δ b (Y w) = Ψ (Multiplicative.ofAdd ((rt b + b) * Y w)) *
      Δ1 (Multiplicative.ofAdd (b * Y w))
    rw [← hEform]
    show δ b (Y w) = δ b (Y w) * δ 1 (b * Y w) *
      δ 1 (Multiplicative.toAdd (Multiplicative.ofAdd (b * Y w)))
    rw [toAdd_ofAdd, mul_assoc, hxx (δ 1 (b * Y w)), mul_one]
  have hcl : Subgroup.closure {w | ∃ b : K, ∃ v : U, ρ (unipSL b) v * v⁻¹ = w} ≤
      (Ψ.coprod Δ1).range := by
    rw [Subgroup.closure_le]
    rintro _ ⟨b, w, rfl⟩
    exact ⟨_, (hgen b w).symm⟩
  have hΘi : Function.Injective (Ψ.coprod Δ1) := by
    have hle : Nat.card (Multiplicative K × Multiplicative K) ≤ Nat.card (Ψ.coprod Δ1).range := by
      rw [Nat.card_prod, Nat.card_congr (Multiplicative.toAdd (α := K))]
      exact hcard.trans (Subgroup.card_le_of_le hcl)
    have hbij := (Ψ.coprod Δ1).rangeRestrict_surjective.bijective_of_nat_card_le hle
    intro p q hpq
    exact hbij.1 (Subtype.ext hpq)
  rw [hgen, hgen] at huv
  have h12 := Prod.ext_iff.mp (hΘi huv)
  have h1 : (rt α + α) * Y u = (rt β + β) * Y v := Multiplicative.ofAdd.injective h12.1
  have h2 : α * Y u = β * Y v := Multiplicative.ofAdd.injective h12.2
  have hs : Y u = 0 := by
    by_contra hs0
    have e1 : rt α * Y u = rt β * Y v := by linear_combination h1 - h2
    have e2 : α * Y u * Y u = β * Y v * Y v := by
      linear_combination (rt α * Y u + rt β * Y v) * e1 + Y u ^ 2 * hrt α - Y v ^ 2 * hrt β
    have hβt : β * Y v ≠ 0 := by
      rw [← h2]
      exact mul_ne_zero hα hs0
    have e3 : Y u = Y v := mul_left_cancel₀ hβt (by linear_combination e2 - Y u * h2)
    rw [e3] at h2 hs0
    exact hαβ (mul_right_cancel₀ hs0 h2)
  rw [hDδ, hs, hδ0]

end Core

theorem factL2Orth_holds : FactL2Orth := by
  intro U _ _ hU Gm R e he _ hR hnat hcard a ha b hb ha1 _ hab
  classical
  have he1 : 1 ≤ e := by omega
  obtain ⟨K, _, _, _, hK, φ, Fh, ⟨-, hφs⟩, hFs, hFk, -, hFe, hφR⟩ :=
    exists_adapted_coord he1 hR hnat
  set ρ : Matrix.SpecialLinearGroup (Fin 2) K →* MulAut U := Gm.subtype.comp φ with hρ
  set F : U →* Multiplicative (Fin 2 → K) :=
    Fh.comp (Subgroup.topEquiv (G := U)).symm.toMonoidHom with hFdef
  have hFs' : Function.Surjective F := fun m => by
    obtain ⟨u, hu⟩ := hFs m
    exact ⟨u, hu⟩
  have hFk' : ∀ u, F u = 1 ↔ u ∈ fixV Gm := fun u => hFk ⟨u, Subgroup.mem_top u⟩
  have hFe' : ∀ p u, Multiplicative.toAdd (F (ρ p u)) =
      (p : Matrix (Fin 2) (Fin 2) K).mulVec (Multiplicative.toAdd (F u)) := fun p u =>
    hFe p ⟨u, Subgroup.mem_top u⟩ (Subgroup.mem_top _)
  have hC : ∀ p, ∀ c ∈ fixV Gm, ρ p c = c := fun p c hc => hc _ (φ p).2
  have hρR : ∀ b : K, ρ (unipSL b) ∈ R := fun b => (hφR _).mpr ⟨b, rfl⟩
  have hRρ : ∀ x ∈ R, ∃ b : K, x = ρ (unipSL b) := by
    intro x hx
    obtain ⟨p, hp⟩ := hφs ⟨x, hR.1 hx⟩
    have hxp : ((φ p : ↥Gm) : MulAut U) = x := by rw [hp]
    obtain ⟨b, rfl⟩ := (hφR p).mp (by rw [hxp]; exact hx)
    exact ⟨b, hxp.symm⟩
  have hCG : ∀ g ∈ Gm, ∀ c ∈ fixV Gm, g c = c := fun g hg c hc => hc g hg
  have hsyl := (natural_sylow_fix hU he1 hCG hR hnat).1
  have hfixC : ∀ w, (∀ b, ρ (unipSL b) w * w⁻¹ ∈ fixV Gm) → ∀ b, ρ (unipSL b) w = w := by
    intro w hw b
    have hwR : w ∈ fixV R := hsyl w (Subgroup.mem_top w) fun r hr => by
      obtain ⟨b', rfl⟩ := hRρ r hr
      exact hw b'
    exact hwR _ (hρR b)
  have hcl : Subgroup.closure {w | ∃ b : K, ∃ v : U, ρ (unipSL b) v * v⁻¹ = w} = commV R := by
    unfold commV
    congr 1
    ext w
    constructor
    · rintro ⟨b, v, rfl⟩
      exact ⟨_, hρR b, v, rfl⟩
    · rintro ⟨x, hx, v, rfl⟩
      obtain ⟨b, rfl⟩ := hRρ x hx
      exact ⟨b, v, rfl⟩
  have hcard' : Nat.card K * Nat.card K ≤
      Nat.card ↥(Subgroup.closure {w | ∃ b : K, ∃ v : U, ρ (unipSL b) v * v⁻¹ = w}) := by
    rw [hcl, hcard, hK]
    exact le_of_eq (by ring)
  obtain ⟨c₀, hc0, hc1⟩ : ∃ c₀ : K, c₀ ≠ 0 ∧ c₀ ≠ 1 := by
    by_contra hne
    have h01 : ∀ c : K, c = 0 ∨ c = 1 := fun c => by
      by_contra h
      exact hne ⟨c, fun h0 => h (Or.inl h0), fun h1 => h (Or.inr h1)⟩
    have hsurj : Function.Surjective (fun t : Bool => cond t (1 : K) 0) := by
      intro c
      rcases h01 c with rfl | rfl
      · exact ⟨false, rfl⟩
      · exact ⟨true, rfl⟩
    have h1 := Nat.card_le_card_of_surjective _ hsurj
    rw [show Nat.card Bool = 2 by simp, hK] at h1
    have h4 : 2 ^ 2 ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) he
    omega
  obtain ⟨α, rfl⟩ := hRρ a ha
  obtain ⟨β, rfl⟩ := hRρ b hb
  have hα : α ≠ 0 := by
    rintro rfl
    exact ha1 (by rw [unipSL_zero, map_one])
  have hαβ : α ≠ β := by
    rintro rfl
    exact hab rfl
  rw [eq_bot_iff]
  rintro z ⟨hza, hzb⟩
  rw [CFSG.Quasithin.commV_zpowers_eq_map] at hza hzb
  obtain ⟨u, -, rfl⟩ := hza
  obtain ⟨v, -, hv⟩ := hzb
  rw [CFSG.Quasithin.commHom_apply] at hv ⊢
  exact Subgroup.mem_bot.mpr (orth_core hU ρ F (fixV Gm) hFs' hFk' hFe' hC hfixC hc0 hc1 hcard'
    hα hαβ hv.symm)

theorem factsL2_holds : FactsL2 :=
  ⟨factL2Offender_holds, factL2NatRank_holds, factL2Orth_holds⟩

end CFSG.Quasithin.Vol2.Ch11.SecB
