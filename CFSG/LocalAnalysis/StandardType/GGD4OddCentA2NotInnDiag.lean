module

public import CFSG.LocalAnalysis.StandardType.GGA2UnitaryIThreeRank
public import CFSG.LocalAnalysis.StandardType.GGD4OddCentKnownInputs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

private theorem ggD4A2NotInnDiag_labelAllGuard {K : Type*} [Group K]
    {S : LargeEvenLabel → Prop} {P' : LargeEvenLabel → LargeEvenRawCont}
    (h : ∀ lab, LargeEvenInLambda2 lab → S lab → LargeEvenLabelAll lab (P' lab)) :
    GGMarkingAll (K := K) fun lab R _ I F _ => S lab → P' lab R I F := by
  intro Q hQ
  obtain ⟨hX, lab, hlab, hraw⟩ := hQ
  by_cases hs : S lab
  · refine ⟨hX, lab, hlab, largeEvenRawDatum_mono ?_ (h lab hlab hs _ hraw)⟩
    rintro R _ I F ⟨⟨hsi, hna, θ, hθ⟩, hc⟩
    exact ⟨hsi, hna, θ, hθ, fun _ => hc⟩
  · refine ⟨hX, lab, hlab, largeEvenRawDatum_mono ?_ hraw⟩
    rintro R _ I F ⟨hsi, hna, θ, hθ⟩
    exact ⟨hsi, hna, θ, hθ, fun h' => absurd h' hs⟩

private noncomputable def ggD4A2Restrict {K : Type*} [Group K] (J : Subgroup K)
    (a : MulAut K) (ha : ∀ j : K, a j ∈ J ↔ j ∈ J) : MulAut ↥J where
  toFun j := ⟨a j, (ha j).2 j.2⟩
  invFun j := ⟨a⁻¹ j, (ha (a⁻¹ j)).1 (by simpa using j.2)⟩
  left_inv j := Subtype.ext (by simp)
  right_inv j := Subtype.ext (by simp)
  map_mul' j k := Subtype.ext (by simp [map_mul])

private noncomputable def ggD4A2RestrictHom {K : Type*} [Group K] (A : Subgroup (MulAut K))
    (J : Subgroup K) (hAJ : ∀ a ∈ A, ∀ j ∈ J, a j ∈ J) : A →* MulAut ↥J where
  toFun a := ggD4A2Restrict J a.1 fun j => ⟨fun h => by
      have h' := hAJ a.1⁻¹ (A.inv_mem a.2) (a.1 j) h
      simpa only [MulAut.inv_apply_self] using h', fun h => hAJ a.1 a.2 j h⟩
  map_one' := by
    ext j
    rfl
  map_mul' a b := by
    ext j
    rfl

@[expose] def GGD4OddCentGraphCore : Prop :=
  ∀ (K : Type) [Group K] [Finite K], commutator K = ⊤ →
    ∀ (A : Subgroup (MulAut K)) (σ : MulAut K) (J : Subgroup K), GGKLocal A σ J →
      (Nat.card A = 3 ^ 3 ∨ Nat.card A = 3 ^ 4) →
        GGMarkingAll (K := K) fun lab _ _ I F θ =>
          GGOddCentDatum A lab I F θ → ¬ GGInnField I F (ggInducedAut θ σ) →
            LargeEvenMarking J fun lab' _ _ _ _ _ =>
              GGLabelG2 lab' ∨ lab'.tag = .triD4 ∨
                (GGLabelA2 lab' ∧ lab'.tag = .twA ∧ Subgroup.center J = ⊥)

@[expose] def GGD4OddCentA2NotInnDiagInput : Prop :=
  ∀ (K : Type) [Group K] [Finite K], commutator K = ⊤ →
    ∀ (A : Subgroup (MulAut K)) (σ : MulAut K) (J : Subgroup K), GGKLocal A σ J →
      Nat.card A = 3 ^ 4 →
        GGMarkingAll (K := ↥J) fun lab' _ _ I' _ θ' =>
          (GGLabelA2 lab' ∧ lab'.tag = .twA) → ¬ GGAutsInduceOn A J θ' I'

theorem ggD4OddCentGraphInput_of_core (hcore : GGD4OddCentGraphCore)
    (hrk : GGD4OddCentA2NotInnDiagInput) : GGD4OddCentGraphInput := by
  intro K _ _ hK A σ J hl hcard
  refine ggMarkingAll_mono (fun lab R _ I F θ h => ?_) (hcore K hK A σ J hl hcard)
  intro hdat hnot
  have hJ := h hdat hnot
  by_cases h4 : Nat.card A = 3 ^ 4
  · have hall := hrk K hK A σ J hl h4
    refine largeEvenMarking_mono (fun lab' R' _ I' F' θ' hh => ?_) (ggMarkingAll_apply hall hJ)
    rcases hh.1 with h1 | h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr ⟨h1.1, h1.2.1, h1.2.2, fun _ => hh.2 ⟨h1.1, h1.2.1⟩⟩)
  · refine largeEvenMarking_mono (fun lab' R' _ I' F' θ' hh => ?_) hJ
    rcases hh with h1 | h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr ⟨h1.1, h1.2.1, h1.2.2, fun h => absurd h h4⟩)

theorem ggD4OddCentA2NotInnDiagInput_of_rank :
    GGD4OddCentA2NotInnDiagInput := by
  have h := ggA2UnitaryIThreeRank_holds
  intro K _ _ hK A σ J hl h81
  have hall : GGMarkingAll (K := ↥J) fun lab R _ I F _ =>
      (GGLabelA2 lab ∧ lab.tag = .twA) → GGRawIThreeRankLe 9 R I F :=
    ggD4A2NotInnDiag_labelAllGuard
      (S := fun lab => GGLabelA2 lab ∧ lab.tag = .twA)
      (P' := fun _ => GGRawIThreeRankLe 9)
      (fun lab hlab hs => h lab hlab hs.1 hs.2)
  refine ggMarkingAll_mono (fun lab R _ I F θ' hrk => ?_) hall
  intro hlab hind
  have hAJ : ∀ a ∈ A, ∀ j ∈ J, a j ∈ J := hl.1.2.2.2.2
  let res : A →* MulAut ↥J := ggD4A2RestrictHom A J hAJ
  let ρ : A →* MulAut R := (ggInducedAut θ').comp res
  have hperf : commutator ↥J = ⊤ := hl.1.2.2.2.1.2.2.1
  have hinj : Function.Injective (ggInducedAut θ') :=
    ggInducedAut_injective_of_perfect hperf θ'
  have hρI : ∀ a : A, ρ a ∈ I := by
    intro a
    obtain ⟨φ, hφI, hφind⟩ := hind a.1 a.2
    have hφeq : φ = ρ a := by
      ext x
      obtain ⟨q, rfl⟩ := θ'.surjective x
      obtain ⟨j, rfl⟩ := QuotientGroup.mk_surjective q
      calc φ (θ' (QuotientGroup.mk j))
          = θ' (QuotientGroup.mk (res a j)) := hφind j (res a j) rfl
        _ = ρ a (θ' (QuotientGroup.mk j)) := (ggInducedAut_apply θ' (res a) j).symm
    simpa [hφeq] using hφI
  have hEL : IsElemAbelian 3 ρ.range :=
    isElemAbelian_range_of_comm (fun a b => hl.1.1.1.is_comm.comm a b)
      (fun a => Subtype.ext (by simpa using hl.1.1.2 a a.2)) ρ
  have hker3 : Nat.card ρ.ker ≤ 3 := by
    haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    have hord : orderOf σ = 3 :=
      orderOf_eq_prime (hl.1.1.2 σ hl.1.2.1) hl.1.2.2.1
    have hcardz : Nat.card (Subgroup.zpowers σ) = 3 := by
      rw [Nat.card_zpowers, hord]
    have hmem : ∀ a : ρ.ker, a.1.1 ∈ Subgroup.zpowers σ := by
      intro a
      apply hl.2 a.1.1 a.1.2
      intro j hj
      have hres1 : res a.1 = 1 := by
        apply hinj
        rw [map_one]
        exact MonoidHom.mem_ker.mp a.2
      have h1 : res a.1 ⟨j, hj⟩ = ⟨j, hj⟩ := by
        simpa using congrArg (fun g : MulAut ↥J => g ⟨j, hj⟩) hres1
      exact congrArg Subtype.val h1
    have hinj2 : Function.Injective
        (fun a : ρ.ker => (⟨a.1.1, hmem a⟩ : Subgroup.zpowers σ)) := by
      intro a b hab
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun x : Subgroup.zpowers σ => (x : MulAut K)) hab
    calc Nat.card ρ.ker
        ≤ Nat.card (Subgroup.zpowers σ) := Nat.card_le_card_of_injective _ hinj2
      _ = 3 := hcardz
  have hcard : Nat.card ρ.ker * Nat.card ρ.range = Nat.card A :=
    Subgroup.card_ker_mul_card_range ρ
  have h81' : Nat.card A = 81 := by rw [h81]; norm_num
  have hle9 : Nat.card ρ.range ≤ 9 :=
    hrk hlab ρ.range hEL fun x hx => by
      obtain ⟨a, rfl⟩ := hx
      exact hρI a
  have h27 : 27 ≤ Nat.card ρ.range := by
    refine Nat.le_of_mul_le_mul_left ?_ (by norm_num : (0 : ℕ) < 3)
    calc 3 * 27 = 81 := by norm_num
      _ = Nat.card A := h81'.symm
      _ = Nat.card ρ.ker * Nat.card ρ.range := hcard.symm
      _ ≤ 3 * Nat.card ρ.range := Nat.mul_le_mul_right _ hker3
  omega

theorem ggD4OddCentA2NotInnDiagInput_holds : GGD4OddCentA2NotInnDiagInput :=
  ggD4OddCentA2NotInnDiagInput_of_rank

theorem ggD4OddCentGraphInput_of_graphCore (hcore : GGD4OddCentGraphCore) :
    GGD4OddCentGraphInput :=
  ggD4OddCentGraphInput_of_core hcore ggD4OddCentA2NotInnDiagInput_holds

end CFSG.StandardType
