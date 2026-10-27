module

public import CFSG.Quasithin.Background.F918Z3Cb
public import CFSG.Quasithin.Background.F918Z3CbReal
public import CFSG.Quasithin.Background.F918J3

public section

namespace CFSG.Quasithin

open CFSG.Assembly.LowTwoRank CFSG.Open

namespace OrthMinus

section Aux

theorem statedScalars_subgroupOf_eq_bot {K : Type} [Field K] [CharP K 2] :
    (StatedScalars (Fin 2) K).subgroupOf (StatedSL 2 K) = ⊥ :=
  CFSG.Open.StatedAPI.statedScalars_subgroupOf_statedSL_two_eq_bot

@[expose] def projEquiv (K : Type) [Field K] [CharP K 2] :
    ↥(StatedSL 2 K) ≃* StatedProj (StatedSL 2 K) :=
  (QuotientGroup.quotientBot (G := ↥(StatedSL 2 K))).symm.trans
    (QuotientGroup.quotientMulEquivOfEq statedScalars_subgroupOf_eq_bot.symm)

theorem card_inf_fixV_eq {V : Type} [CommGroup V] {I : Subgroup V} {j : MulAut V}
    (hj : j ∈ stabSub I) :
    Nat.card ↥(I ⊓ fixV (Subgroup.zpowers j)) =
      Nat.card {w : ↥I // resHom I ⟨j, hj⟩ w = w} := by
  refine Nat.card_congr
    { toFun := fun v => ⟨⟨v.1, v.2.1⟩, Subtype.ext (v.2.2 j (Subgroup.mem_zpowers j))⟩
      invFun := fun w => ⟨(w.1 : V), w.1.2, fun x hx => by
        have h : j ((w.1 : ↥I) : V) = (w.1 : V) := congrArg Subtype.val w.2
        have hle : Subgroup.zpowers j ≤ MulAction.stabilizer (MulAut V) ((w.1 : ↥I) : V) :=
          Subgroup.zpowers_le.mpr (MulAction.mem_stabilizer_iff.mpr h)
        exact MulAction.mem_stabilizer_iff.mp (hle hx)⟩
      left_inv := fun v => rfl
      right_inv := fun w => rfl }

end Aux

end OrthMinus

open OrthMinus

theorem orthMinusData_of_binaryOrthogonalFour {V : Type} [CommGroup V] [Finite V]
    {D : Subgroup (MulAut V)} {I : Subgroup V} (hI : ∀ y ∈ D, ∀ v ∈ I, y v ∈ I)
    (hfaith : ∀ y ∈ D, (∀ v ∈ I, y v = v) → y = 1) {a : ℕ} (ha : 1 ≤ a)
    (h : BinaryOrthogonalFour (autSub D I) ⊤ ⊥ a) : OrthMinusData D I a := by
  obtain ⟨K, hKf, hKfin, hKchar, hK, π, hπ⟩ := h
  obtain ⟨R⟩ := nonempty_hermReal hπ
  have hDs : D ≤ stabSub I := le_stabSub_of_forall_mem hI
  have hDc : D ⊓ centSub I = ⊥ := by
    rw [eq_bot_iff]
    rintro y ⟨hyD, hyc⟩
    exact Subgroup.mem_bot.mpr (hfaith y hyD hyc)
  have h4 : 4 ≤ 2 ^ (2 * a) :=
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (2 * a) := Nat.pow_le_pow_right (by norm_num) (by omega)
  refine ⟨ha, R.card_eq hK ha, ?_, ?_, R.exists_scalars hK ha⟩
  · refine ⟨⟨Nat.prime_two, by omega, by omega, ?_, ?_⟩, K, hKf, hKfin, hK, ⟨?_⟩⟩
    · intro hc
      have := congrArg Prod.snd hc
      simp only at this
      omega
    · intro hc
      have := congrArg Prod.snd hc
      simp only at this
      omega
    · exact (autSubEquivOfFaithful hDs hDc).trans
        ((MulEquiv.ofBijective R.π R.bij).symm.trans (projEquiv K))
  · intro j hj hj1 hjj
    have hjs : j ∈ stabSub I := hDs hj
    have hφH : resHom I ⟨j, hjs⟩ ∈ autSub D I := mem_autSub.mpr ⟨⟨j, hjs⟩, hj, rfl⟩
    have hφ1 : resHom I ⟨j, hjs⟩ ≠ 1 := by
      intro h1
      refine hj1 (hfaith j hj fun v hv => ?_)
      exact congrArg (fun ψ : MulAut ↥I => ((ψ ⟨v, hv⟩ : ↥I) : V)) h1
    have hφφ : resHom I ⟨j, hjs⟩ * resHom I ⟨j, hjs⟩ = 1 := by
      rw [← map_mul]
      have : (⟨j, hjs⟩ : ↥(stabSub I)) * ⟨j, hjs⟩ = 1 := Subtype.ext hjj
      rw [this, map_one]
    rw [card_inf_fixV_eq hjs]
    exact R.card_fixed_sq hK ha hφH hφ1 hφφ

end CFSG.Quasithin
