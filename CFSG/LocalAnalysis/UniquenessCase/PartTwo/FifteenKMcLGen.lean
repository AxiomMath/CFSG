module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenKMcLDefs
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalMcLBasic
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThreeInputs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.ComponentClassification.OutcomeLocal

theorem s15k_mcl_card_commSub {W : Type} [CommGroup W] {J : Subgroup (MulAut W)}
    {R : Subgroup W} (D : McRep J R) (j : ↥J) :
    Nat.card ↥(commSub R (Subgroup.zpowers (j : MulAut W))) =
      Nat.card ↥(commutatorSpace (D.ρ j)) := by
  let C : Submodule (ZMod 2) D.V := commutatorSpace (D.ρ j)
  let F : ↥R → D.V := fun r => Multiplicative.toAdd (D.e r)
  let F' : D.V → ↥R := fun v => D.e.symm (Multiplicative.ofAdd v)
  have F_F' : ∀ v : D.V, F (F' v) = v := by
    intro v
    simp [F, F']
  have F'_F : ∀ r : ↥R, F' (F r) = r := by
    intro r
    simp [F, F']
  have F_inj : Function.Injective F := by
    intro a b h
    have := congrArg F' h
    simpa [F', F] using this
  have F_mul : ∀ a b : ↥R, F (a * b) = F a + F b := by
    intro a b
    simp [F, map_mul, toAdd_mul]
  have F_inv : ∀ a : ↥R, F a⁻¹ = -F a := by
    intro a
    simp [F, map_inv, toAdd_inv]
  let H : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) D.V) :=
    { carrier := {h | ∀ v : D.V, (h : D.V →ₗ[ZMod 2] D.V) v + v ∈ C}
      one_mem' := by
        intro v
        change (1 : D.V →ₗ[ZMod 2] D.V) v + v ∈ C
        rw [Module.End.one_apply, zmod2_add_self]
        exact C.zero_mem
      mul_mem' := by
        intro a b ha hb v
        change (a : D.V →ₗ[ZMod 2] D.V) ((b : D.V →ₗ[ZMod 2] D.V) v) + v ∈ C
        have h1 : (a : D.V →ₗ[ZMod 2] D.V) ((b : D.V →ₗ[ZMod 2] D.V) v)
            + (b : D.V →ₗ[ZMod 2] D.V) v ∈ C := ha _
        have h2 : (b : D.V →ₗ[ZMod 2] D.V) v + v ∈ C := hb v
        have hsum : ((a : D.V →ₗ[ZMod 2] D.V) ((b : D.V →ₗ[ZMod 2] D.V) v)
            + (b : D.V →ₗ[ZMod 2] D.V) v)
            + ((b : D.V →ₗ[ZMod 2] D.V) v + v) ∈ C := C.add_mem h1 h2
        have heq : ((a : D.V →ₗ[ZMod 2] D.V) ((b : D.V →ₗ[ZMod 2] D.V) v)
            + (b : D.V →ₗ[ZMod 2] D.V) v)
            + ((b : D.V →ₗ[ZMod 2] D.V) v + v)
            = (a : D.V →ₗ[ZMod 2] D.V) ((b : D.V →ₗ[ZMod 2] D.V) v) + v := by
          rw [add_assoc, ← add_assoc ((b : D.V →ₗ[ZMod 2] D.V) v)
            ((b : D.V →ₗ[ZMod 2] D.V) v) v, zmod2_add_self, zero_add]
        rw [heq] at hsum
        exact hsum
      inv_mem' := by
        intro a ha v
        change ((a⁻¹ : LinearMap.GeneralLinearGroup (ZMod 2) D.V) :
          D.V →ₗ[ZMod 2] D.V) v + v ∈ C
        have h1 : (a : D.V →ₗ[ZMod 2] D.V)
            (((a⁻¹ : LinearMap.GeneralLinearGroup (ZMod 2) D.V) :
              D.V →ₗ[ZMod 2] D.V) v)
            + ((a⁻¹ : LinearMap.GeneralLinearGroup (ZMod 2) D.V) :
              D.V →ₗ[ZMod 2] D.V) v ∈ C := ha _
        have hau : (a : D.V →ₗ[ZMod 2] D.V)
            (((a⁻¹ : LinearMap.GeneralLinearGroup (ZMod 2) D.V) :
              D.V →ₗ[ZMod 2] D.V) v) = v := by
          rw [← Module.End.mul_apply, ← Units.val_mul, mul_inv_cancel]
          rfl
        rw [hau] at h1
        rw [add_comm]
        exact h1 }
  have hgH : D.ρ j ∈ H := by
    intro v
    change (D.ρ j : D.V →ₗ[ZMod 2] D.V) v + v ∈ C
    have hmem : ((LinearMap.id : D.V →ₗ[ZMod 2] D.V) +
        (D.ρ j : D.V →ₗ[ZMod 2] D.V)) v ∈ C :=
      LinearMap.mem_range_self _ v
    rwa [LinearMap.add_apply, LinearMap.id_apply, add_comm] at hmem
  let P : Subgroup W :=
    { carrier := {w | ∃ hw : w ∈ R, F ⟨w, hw⟩ ∈ C}
      one_mem' := ⟨R.one_mem, by
        change Multiplicative.toAdd (D.e (⟨1, R.one_mem⟩ : ↥R)) ∈ C
        rw [show (⟨1, R.one_mem⟩ : ↥R) = 1 from rfl, map_one, toAdd_one]
        exact C.zero_mem⟩
      mul_mem' := by
        rintro a b ⟨ha, hCa⟩ ⟨hb, hCb⟩
        refine ⟨R.mul_mem ha hb, ?_⟩
        change Multiplicative.toAdd (D.e (⟨a * b, R.mul_mem ha hb⟩ : ↥R)) ∈ C
        rw [show (⟨a * b, R.mul_mem ha hb⟩ : ↥R) = ⟨a, ha⟩ * ⟨b, hb⟩ from rfl,
          map_mul, toAdd_mul]
        exact C.add_mem hCa hCb
      inv_mem' := by
        rintro a ⟨ha, hCa⟩
        refine ⟨R.inv_mem ha, ?_⟩
        change Multiplicative.toAdd (D.e (⟨a⁻¹, R.inv_mem ha⟩ : ↥R)) ∈ C
        rw [show (⟨a⁻¹, R.inv_mem ha⟩ : ↥R) = (⟨a, ha⟩ : ↥R)⁻¹ from rfl,
          map_inv, toAdd_inv]
        exact C.neg_mem hCa }
  have hP_le : P ≤ commSub R (Subgroup.zpowers (j : MulAut W)) := by
    intro w hw
    obtain ⟨hwR, hC⟩ := hw
    change F ⟨w, hwR⟩ ∈ commutatorSpace (D.ρ j) at hC
    rw [commutatorSpace, LinearMap.mem_range] at hC
    obtain ⟨v, hv⟩ := hC
    let w₀ : ↥R := F' v
    have hw₀ : F w₀ = v := F_F' v
    have h1R : (j : MulAut W) (w₀ : W) ∈ R := D.stable (j : MulAut W) j.2 (w₀ : W) w₀.2
    have hR : (j : MulAut W) (w₀ : W) * (w₀ : W)⁻¹ ∈ R :=
      R.mul_mem h1R (R.inv_mem w₀.2)
    have hgen : (j : MulAut W) (w₀ : W) * (w₀ : W)⁻¹ ∈
        commSub R (Subgroup.zpowers (j : MulAut W)) :=
      Subgroup.subset_closure
        ⟨(j : MulAut W), Subgroup.mem_zpowers _, (w₀ : W), w₀.2, rfl⟩
    have hsplit : (⟨(j : MulAut W) (w₀ : W) * (w₀ : W)⁻¹, hR⟩ : ↥R) =
        (⟨(j : MulAut W) (w₀ : W), h1R⟩ : ↥R) * (⟨(w₀ : W), w₀.2⟩ : ↥R)⁻¹ := rfl
    have hh : F (⟨(j : MulAut W) (w₀ : W), h1R⟩ : ↥R) =
        (D.ρ j : D.V →ₗ[ZMod 2] D.V) (F w₀) := by
      have hthis := D.hρ j ⟨(w₀ : W), w₀.2⟩ h1R
      simp only [F]
      rw [hthis, toAdd_ofAdd]
    have hval : F (⟨(j : MulAut W) (w₀ : W) * (w₀ : W)⁻¹, hR⟩ : ↥R) = F ⟨w, hwR⟩ := by
      rw [hsplit, F_mul, F_inv, hh]
      rw [show F (⟨(w₀ : W), w₀.2⟩ : ↥R) = F w₀ from rfl, zmod2_neg, hw₀, add_comm]
      simpa using hv
    have heq : (⟨(j : MulAut W) (w₀ : W) * (w₀ : W)⁻¹, hR⟩ : ↥R) = ⟨w, hwR⟩ :=
      F_inj hval
    have hweq : (j : MulAut W) (w₀ : W) * (w₀ : W)⁻¹ = w := congrArg Subtype.val heq
    simpa [hweq] using hgen
  have hcomm_le : commSub R (Subgroup.zpowers (j : MulAut W)) ≤ P := by
    rw [commSub, Subgroup.closure_le]
    rintro c ⟨x, hx, w, hw, rfl⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    have hjk : (j : MulAut W) ^ k ∈ J := Subgroup.zpow_mem J j.2 k
    have h1R : ((j : MulAut W) ^ k) w ∈ R := D.stable ((j : MulAut W) ^ k) hjk w hw
    have hR : ((j : MulAut W) ^ k) w * w⁻¹ ∈ R := R.mul_mem h1R (R.inv_mem hw)
    refine ⟨hR, ?_⟩
    have hsplit : (⟨((j : MulAut W) ^ k) w * w⁻¹, hR⟩ : ↥R) =
        (⟨((j : MulAut W) ^ k) w, h1R⟩ : ↥R) * (⟨w, hw⟩ : ↥R)⁻¹ := rfl
    rw [hsplit, F_mul, F_inv]
    have hF : F (⟨((j : MulAut W) ^ k) w, h1R⟩ : ↥R) =
        (((D.ρ j) ^ k : LinearMap.GeneralLinearGroup (ZMod 2) D.V) :
          D.V →ₗ[ZMod 2] D.V) (F ⟨w, hw⟩) := by
      have hxj : (⟨(j : MulAut W) ^ k, hjk⟩ : ↥J) = j ^ k := by
        apply Subtype.ext
        rw [Subgroup.coe_zpow J]
      have hρk : D.ρ (⟨(j : MulAut W) ^ k, hjk⟩ : ↥J) = (D.ρ j) ^ k := by
        rw [hxj, map_zpow]
      have hthis := D.hρ (⟨(j : MulAut W) ^ k, hjk⟩ : ↥J) ⟨w, hw⟩ h1R
      rw [hρk] at hthis
      simp only [F]
      rw [hthis, toAdd_ofAdd]
    rw [hF, zmod2_neg]
    exact Subgroup.zpow_mem H hgH k (F ⟨w, hw⟩)
  have hP : P = commSub R (Subgroup.zpowers (j : MulAut W)) := le_antisymm hP_le hcomm_le
  have hmemP : ∀ p : ↥P, ∃ hw : (p : W) ∈ R, F ⟨(p : W), hw⟩ ∈ C := fun p => p.2
  have hcard : Nat.card ↥P = Nat.card ↥C := by
    refine Nat.card_congr
      { toFun := fun p => ⟨F ⟨(p : W), (hmemP p).choose⟩, (hmemP p).choose_spec⟩
        invFun := fun c => ⟨((F' (c : D.V)) : W), ⟨(F' (c : D.V)).2, ?_⟩⟩
        left_inv := ?_
        right_inv := ?_ }
    · show F (F' (c : D.V)) ∈ C
      rw [F_F' (c : D.V)]
      exact c.2
    · intro p
      apply Subtype.ext
      show ((F' (F ⟨(p : W), (hmemP p).choose⟩) : ↥R) : W) = (p : W)
      rw [F'_F]
    · intro c
      apply Subtype.ext
      show F (F' (c : D.V)) = (c : D.V)
      rw [F_F']
  rw [← hP]
  exact hcard

theorem s15k_mcl_isF2Transvection {W : Type} [CommGroup W] {J : Subgroup (MulAut W)}
    {R : Subgroup W} (D : McRep J R) (j : ↥J) (h : InducesTransvection (j : MulAut W) R) :
    IsF2Transvection (D.ρ j) := by
  unfold IsF2Transvection
  constructor
  · intro hg
    have hcard := s15k_mcl_card_commSub D j
    have h2 : padicValNat 2
        (Nat.card ↥(commSub R (Subgroup.zpowers (j : MulAut W)))) = 1 := h.2
    rw [hcard] at h2
    have hbot : commutatorSpace (D.ρ j) = ⊥ := by
      rw [hg, commutatorSpace]
      apply le_antisymm _ bot_le
      intro v hv
      rw [LinearMap.mem_range] at hv
      obtain ⟨u, hu⟩ := hv
      rw [Submodule.mem_bot, ← hu]
      change ((LinearMap.id : D.V →ₗ[ZMod 2] D.V) +
        (1 : D.V →ₗ[ZMod 2] D.V)) u = 0
      rw [LinearMap.add_apply, LinearMap.id_apply, Module.End.one_apply, zmod2_add_self]
    rw [hbot, Nat.card_unique, padicValNat_one_right] at h2
    exact absurd h2 (by norm_num)
  · have hcard := s15k_mcl_card_commSub D j
    have h2 : padicValNat 2 (Nat.card ↥(commutatorSpace (D.ρ j))) = 1 := by
      rw [← hcard]
      exact h.2
    have hpow : Nat.card ↥(commutatorSpace (D.ρ j)) =
        2 ^ Module.finrank (ZMod 2) ↥(commutatorSpace (D.ρ j)) := by
      rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
    rw [hpow, padicValNat.prime_pow] at h2
    exact h2

theorem s15k_mcl_gen {W : Type} [CommGroup W] {J : Subgroup (MulAut W)} {R : Subgroup W}
    (D : McRep J R) (h : GenByTransvections J R) :
    ∃ S : Set (LinearMap.GeneralLinearGroup (ZMod 2) D.V),
      (∀ t ∈ S, IsF2Transvection t) ∧ D.ρ.range = Subgroup.closure S := by
  refine ⟨D.ρ '' {j : ↥J | InducesTransvection (j : MulAut W) R}, ?_, ?_⟩
  · rintro t ⟨j, hj, rfl⟩
    exact s15k_mcl_isF2Transvection D j hj
  · have hclosure :
        Subgroup.closure {j : ↥J | InducesTransvection (j : MulAut W) R} = ⊤ := by
      have h1 := Subgroup.closure_preimage_eq_top
        (s := {t : MulAut W | t ∈ J ∧ InducesTransvection t R})
      rw [← h] at h1
      convert h1 using 2
      ext j
      simp
    rw [MonoidHom.range_eq_map D.ρ, ← hclosure]
    exact MonoidHom.map_closure D.ρ _

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
