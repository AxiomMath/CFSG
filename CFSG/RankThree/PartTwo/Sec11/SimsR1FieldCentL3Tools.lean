module

public import CFSG.RankThree.PartTwo.Sec11.Item116H3KFact

public section

namespace CFSG.RankThree.PartTwo.Sec11.SimsR1.FieldCent.L3

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open scoped commutatorElement
open Matrix

@[expose] def powZMod {G : Type*} [Group G] (r : ℕ) [NeZero r] (g : G) (hg : g ^ r = 1) :
    Multiplicative (ZMod r) →* G where
  toFun x := g ^ (Multiplicative.toAdd x).val
  map_one' := by simp
  map_mul' x y := by
    simp only [toAdd_mul, ZMod.val_add, ← pow_add]
    exact (pow_eq_pow_mod _ hg).symm

theorem powZMod_injective {G : Type*} [Group G] {r : ℕ} [NeZero r] {g : G} (hg : g ^ r = 1)
    (hord : orderOf g = r) : Function.Injective (powZMod r g hg) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  change g ^ (Multiplicative.toAdd x).val = 1 at hx
  have hdvd : orderOf g ∣ (Multiplicative.toAdd x).val := orderOf_dvd_of_pow_eq_one hx
  rw [hord] at hdvd
  have h0 : (Multiplicative.toAdd x).val = 0 := Nat.eq_zero_of_dvd_of_lt hdvd (ZMod.val_lt _)
  have h1 : Multiplicative.toAdd x = 0 := (ZMod.val_eq_zero _).mp h0
  exact h1

@[expose] def rankOneHom {G : Type*} [Group G] (r : ℕ) (ι : Multiplicative (ZMod r) →* G) :
    Multiplicative (Fin 1 → ZMod r) →* G where
  toFun v := ι (Multiplicative.ofAdd (Multiplicative.toAdd v 0))
  map_one' := by simp
  map_mul' a b := by simp only [toAdd_mul, Pi.add_apply, ofAdd_add, map_mul]

theorem rankOneHom_injective {G : Type*} [Group G] {r : ℕ} {ι : Multiplicative (ZMod r) →* G}
    (hι : Function.Injective ι) : Function.Injective (rankOneHom r ι) := by
  intro v w hvw
  have h0 := Multiplicative.ofAdd.injective (hι hvw)
  apply Multiplicative.toAdd.injective
  funext i
  fin_cases i
  exact h0

@[expose] def rankTwoHom {G K : Type*} [Group G] [Field K] (Φ : Kˣ × Kˣ →* G) (r : ℕ)
    (ι : Multiplicative (ZMod r) →* Kˣ) : Multiplicative (Fin 2 → ZMod r) →* G where
  toFun v := Φ (ι (Multiplicative.ofAdd (Multiplicative.toAdd v 0)),
    ι (Multiplicative.ofAdd (Multiplicative.toAdd v 1)))
  map_one' := by
    simp only [toAdd_one, Pi.zero_apply, ofAdd_zero, map_one]
    exact map_one Φ
  map_mul' a b := by
    simp only [toAdd_mul, Pi.add_apply, ofAdd_add, map_mul]
    exact map_mul Φ (ι (Multiplicative.ofAdd (Multiplicative.toAdd a 0)),
      ι (Multiplicative.ofAdd (Multiplicative.toAdd a 1)))
      (ι (Multiplicative.ofAdd (Multiplicative.toAdd b 0)),
        ι (Multiplicative.ofAdd (Multiplicative.toAdd b 1)))

theorem rankTwoHom_injective {G K : Type*} [Group G] [Field K] {Φ : Kˣ × Kˣ →* G}
    (hΦ : Function.Injective Φ) {r : ℕ} {ι : Multiplicative (ZMod r) →* Kˣ}
    (hι : Function.Injective ι) : Function.Injective (rankTwoHom Φ r ι) := by
  intro v w hvw
  have h := hΦ hvw
  simp only [Prod.mk.injEq] at h
  have h0 := hι h.1
  have h1 := hι h.2
  apply Multiplicative.toAdd.injective
  funext i
  fin_cases i
  · exact Multiplicative.ofAdd.injective h0
  · exact Multiplicative.ofAdd.injective h1

theorem hasPRank_of_injective {X : Type*} [Group X] (S : Subgroup X) (r k : ℕ) [Fact r.Prime]
    (ψ : Multiplicative (Fin k → ZMod r) →* S) (hψ : Function.Injective ψ) :
    HasPRank S r k := by
  set ψ' : Multiplicative (Fin k → ZMod r) →* X := S.subtype.comp ψ with hψ'
  have hψ'inj : Function.Injective ψ' := Subtype.val_injective.comp hψ
  refine ⟨ψ'.range, ?_, ?_, ?_⟩
  · rintro _ ⟨v, rfl⟩
    exact (ψ v).2
  · rintro ⟨_, v, rfl⟩
    refine ⟨1, ?_⟩
    apply Subtype.ext
    change ψ' v ^ r ^ 1 = 1
    rw [pow_one, ← map_pow]
    have hv : v ^ r = 1 := by
      apply Multiplicative.toAdd.injective
      funext i
      simp
    rw [hv, map_one]
  · exact ⟨((MonoidHom.ofInjective hψ'inj).symm : ψ'.range ≃* _).toMonoidHom,
      (MonoidHom.ofInjective hψ'inj).symm.surjective⟩

theorem isSimpleGroup_of_quasisimple_center_eq_bot {K : Type*} [Group K] (hK : IsQuasisimple K)
    (hZ : Subgroup.center K = ⊥) : IsSimpleGroup K ∧ ∃ a b : K, a * b ≠ b * a := by
  obtain ⟨-, hs, a, b, hab⟩ := hK
  let e : K ⧸ Subgroup.center K ≃* K :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  refine ⟨e.symm.isSimpleGroup, e a, e b, fun h => hab (e.injective ?_)⟩
  rw [map_mul, map_mul, h]

theorem simple_nonab_of_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    (hs : IsSimpleGroup H) (hn : ∃ a b : H, a * b ≠ b * a) :
    IsSimpleGroup G ∧ ∃ a b : G, a * b ≠ b * a :=
  ⟨e.isSimpleGroup, by
    obtain ⟨a, b, hab⟩ := hn
    exact ⟨e.symm a, e.symm b, fun h => hab (by simpa using congrArg e h)⟩⟩

theorem isPerfect_of_simple {S : Type*} [Group S] [IsSimpleGroup S]
    (hnab : ∃ a b : S, a * b ≠ b * a) : Group.IsPerfect S := by
  rw [Group.isPerfect_def]
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator S) with h | h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnab
    apply hab
    have hc : ⁅a, b⁆ ∈ commutator S :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
    rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hc
    exact hc
  · exact h

theorem inSubgroup_perfectResidual_eq {X : Type*} [Group X] (Y : Subgroup X) [IsSimpleGroup Y]
    (hnab : ∃ a b : Y, a * b ≠ b * a) : inSubgroup perfectResidual Y = Y := by
  haveI : Group.IsPerfect Y := isPerfect_of_simple hnab
  have hP : perfectResidual Y = ⊤ := by
    unfold perfectResidual
    simp
  rw [inSubgroup, hP, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

theorem simpleFixedRank_of_simple {X : Type} [Group X] [Finite X] {α : MulAut X} {r k : ℕ}
    (hs : IsSimpleGroup (Sec11.fixedSub α)) (hnab : ∃ a b : Sec11.fixedSub α, a * b ≠ b * a)
    (hr : HasPRank (Sec11.fixedSub α) r k) : SimpleFixedRank X α r k := by
  have hP := inSubgroup_perfectResidual_eq (Sec11.fixedSub α) hnab
  unfold SimpleFixedRank
  rw [hP]
  refine ⟨hs, ?_, hr⟩
  intro h
  obtain ⟨a, b, hab⟩ := hnab
  exact hab (h a b)

@[expose] def torusMat (K : Type*) [Field K] : Kˣ × Kˣ →* Matrix (Fin 3) (Fin 3) K where
  toFun p := Matrix.diagonal ![(p.1 : K), (p.2 : K), (((p.1 * p.2)⁻¹ : Kˣ) : K)]
  map_one' := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  map_mul' p q := by
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    ext i
    fin_cases i
    · simp
    · simp
    · simp only [Fin.reduceFinMk, Matrix.cons_val, Prod.fst_mul, Prod.snd_mul]
      rw [mul_mul_mul_comm, mul_inv, Units.val_mul]

variable {K : Type*} [Field K]

theorem det_torusMat (p : Kˣ × Kˣ) : (torusMat K p).det = 1 := by
  have h1 : (p.1 : K) ≠ 0 := p.1.ne_zero
  have h2 : (p.2 : K) ≠ 0 := p.2.ne_zero
  simp [torusMat, Matrix.det_diagonal, Fin.prod_univ_three]
  field_simp

theorem torusMat_injective : Function.Injective (torusMat K) := by
  intro p q h
  have h00 := congrFun (congrFun h 0) 0
  have h11 := congrFun (congrFun h 1) 1
  simp [torusMat] at h00 h11
  exact Prod.ext (Units.ext h00) (Units.ext h11)

@[expose] def torusSL (K : Type*) [Field K] : Kˣ × Kˣ →* SpecialLinearGroup (Fin 3) K :=
  MonoidHom.mk' (fun p => ⟨torusMat K p, det_torusMat p⟩)
    (fun p q => Subtype.ext (map_mul (torusMat K) p q))

theorem torusSL_injective : Function.Injective (torusSL K) :=
  fun _ _ h => torusMat_injective (congrArg Subtype.val h)

@[expose] def torusGL (K : Type*) [Field K] : Kˣ × Kˣ →* GL (Fin 3) K :=
  (torusMat K).toHomUnits

theorem coe_torusGL (p : Kˣ × Kˣ) :
    ((torusGL K p : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = torusMat K p := rfl

theorem torusGL_injective : Function.Injective (torusGL K) := by
  intro p q h
  apply torusMat_injective
  rw [← coe_torusGL, ← coe_torusGL, h]

end CFSG.RankThree.PartTwo.Sec11.SimsR1.FieldCent.L3
