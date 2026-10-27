module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight63LieOrderParts
public import CFSG.Quasithin.Vol2.Ch11SecAKE13
public import CFSG.RankThree.PartOne.S12K.Rigidity

public noncomputable section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.Ree.ReeTag CFSG.LieType.Simplicity CFSG.Open CFSG.Quasithin.A318P
  CFSG.Quasithin.Vol2.Ch11.SecA.C10KH CFSG.SectionRank.LargeRee

theorem reeTorusHom_injective_of_exp_neg_one
    {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime] {a : ℕ}
    (hK : Nat.card K = ReeTag.F4.prime ^ (2 * a + 1))
    {j : Fin ReeTag.F4.tag.rank} (hj : j ∈ ReeTag.F4.longSet)
    (k : Fin ReeTag.F4.tag.rank) (hk : reeExp a j (Pi.single k 1) = -1) :
    Function.Injective (reeTorusHom a hK hj) := by
  intro u v huv
  have hmul : (reeTorusHom a hK hj v)⁻¹ * reeTorusHom a hK hj u = 1 := by
    rw [← huv, inv_mul_cancel]
  have h1 : (reeTorusHom a hK hj (v⁻¹ * u) : reeFixed ReeTag.F4 K a) = 1 := by
    rw [map_mul, map_inv]
    exact hmul
  have hc := congrArg (fun g : reeFixed ReeTag.F4 K a =>
    simpleChar (g : adjointGroup ReeTag.F4.tag K) k) h1
  rw [coe_reeTorusHom, simpleChar_reeTorus, hk] at hc
  simp only [Subgroup.coe_one] at hc
  have hcone : simpleChar (1 : adjointGroup ReeTag.F4.tag K) k = 1 := by simp [simpleChar]
  rw [hcone] at hc
  have hu : (v⁻¹ * u : Kˣ) ^ (-1 : ℤ) = 1 := Units.ext hc
  rw [zpow_neg_one, inv_eq_one] at hu
  calc u = v * (v⁻¹ * u) := by group
    _ = v := by rw [hu, mul_one]

theorem card_reeTorusPart
    {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime] {a : ℕ}
    (hK : Nat.card K = ReeTag.F4.prime ^ (2 * a + 1)) :
    Nat.card (reeTorusPart ReeTag.F4 K a) = (Nat.card K - 1) ^ 2 := by
  let T : Subgroup (reeFixed ReeTag.F4 K a) := reeTorusPart ReeTag.F4 K a
  let T₀ : Subgroup (reeFixed ReeTag.F4 K a) := reeTorusSub a hK fi_zero_mem_longSet
  let T₁ : Subgroup (reeFixed ReeTag.F4 K a) := reeTorusSub a hK fi_one_mem_longSet
  have hInj₀ : Function.Injective (reeTorusHom a hK fi_zero_mem_longSet) :=
    reeTorusHom_injective_of_exp_neg_one (K := K) (a := a) hK fi_zero_mem_longSet
      (fi 1) (reeExp_zero_one (a := a))
  have hInj₁ : Function.Injective (reeTorusHom a hK fi_one_mem_longSet) :=
    reeTorusHom_injective_of_exp_neg_one (K := K) (a := a) hK fi_one_mem_longSet
      (fi 0) (reeExp_one_zero (a := a))
  have hT₀le : T₀ ≤ T := reeTorusSub_le_reeTorusPart hK fi_zero_mem_longSet
  have hT₁le : T₁ ≤ T := reeTorusSub_le_reeTorusPart hK fi_one_mem_longSet
  let f : Kˣ × Kˣ → T := fun p =>
    ⟨(reeTorusHom a hK fi_zero_mem_longSet p.1 : reeFixed ReeTag.F4 K a) *
        (reeTorusHom a hK fi_one_mem_longSet p.2 : reeFixed ReeTag.F4 K a),
      T.mul_mem (hT₀le ⟨p.1, rfl⟩) (hT₁le ⟨p.2, rfl⟩)⟩
  have hf_inj : Function.Injective f := by
    intro p q hpq
    have hEq : (reeTorusHom a hK fi_zero_mem_longSet p.1 : reeFixed ReeTag.F4 K a) *
        (reeTorusHom a hK fi_one_mem_longSet p.2 : reeFixed ReeTag.F4 K a) =
        (reeTorusHom a hK fi_zero_mem_longSet q.1 : reeFixed ReeTag.F4 K a) *
        (reeTorusHom a hK fi_one_mem_longSet q.2 : reeFixed ReeTag.F4 K a) :=
      congrArg Subtype.val hpq
    have hInt : (reeTorusHom a hK fi_zero_mem_longSet (q.1⁻¹ * p.1) :
          reeFixed ReeTag.F4 K a) =
        (reeTorusHom a hK fi_one_mem_longSet (q.2 * p.2⁻¹) :
          reeFixed ReeTag.F4 K a) := by
      rw [map_mul, map_inv, map_mul, map_inv]
      calc (reeTorusHom a hK fi_zero_mem_longSet q.1)⁻¹ *
            reeTorusHom a hK fi_zero_mem_longSet p.1
          = (reeTorusHom a hK fi_zero_mem_longSet q.1)⁻¹ *
              ((reeTorusHom a hK fi_zero_mem_longSet p.1) *
                (reeTorusHom a hK fi_one_mem_longSet p.2)) *
              (reeTorusHom a hK fi_one_mem_longSet p.2)⁻¹ := by group
        _ = (reeTorusHom a hK fi_zero_mem_longSet q.1)⁻¹ *
              ((reeTorusHom a hK fi_zero_mem_longSet q.1) *
                (reeTorusHom a hK fi_one_mem_longSet q.2)) *
              (reeTorusHom a hK fi_one_mem_longSet p.2)⁻¹ := by rw [hEq]
        _ = reeTorusHom a hK fi_one_mem_longSet q.2 *
              (reeTorusHom a hK fi_one_mem_longSet p.2)⁻¹ := by group
    have hmem : (reeTorusHom a hK fi_zero_mem_longSet (q.1⁻¹ * p.1) :
        reeFixed ReeTag.F4 K a) ∈ T₀ ⊓ T₁ := by
      refine ⟨⟨q.1⁻¹ * p.1, rfl⟩, ?_⟩
      rw [hInt]
      exact ⟨q.2 * p.2⁻¹, rfl⟩
    rw [show T₀ ⊓ T₁ = ⊥ from reeTorusSub_inf hK, Subgroup.mem_bot] at hmem
    have hp1 : p.1 = q.1 := by
      have hu : q.1⁻¹ * p.1 = 1 := hInj₀ (by simpa using hmem)
      calc p.1 = q.1 * (q.1⁻¹ * p.1) := by group
        _ = q.1 := by rw [hu, mul_one]
    have hp2 : p.2 = q.2 := by
      have hv : q.2 * p.2⁻¹ = 1 := by
        apply hInj₁
        rw [show (reeTorusHom a hK fi_one_mem_longSet (q.2 * p.2⁻¹) :
          reeFixed ReeTag.F4 K a) = reeTorusHom a hK fi_one_mem_longSet 1 by
            rw [← hInt]
            simpa using hmem]
      exact (mul_inv_eq_one.mp hv).symm
    exact Prod.ext hp1 hp2
  have hf_surj : Function.Surjective f := by
    intro x
    obtain ⟨u, v, huv⟩ := exists_eq_reeTorus_mul (K := K) (a := a) hK x.2 x.1.2
    refine ⟨(u, v), ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    simpa [f, coe_reeTorusHom] using huv.symm
  have e : Kˣ × Kˣ ≃ T := Equiv.ofBijective f ⟨hf_inj, hf_surj⟩
  change Nat.card T = (Nat.card K - 1) ^ 2
  calc Nat.card T = Nat.card (Kˣ × Kˣ) := (Nat.card_congr e).symm
    _ = Nat.card Kˣ * Nat.card Kˣ := Nat.card_prod _ _
    _ = (Nat.card K - 1) * (Nat.card K - 1) := by rw [Nat.card_units]
    _ = (Nat.card K - 1) ^ 2 := by ring

section Certificates


theorem exists_sylow_abelian_of_lieModel_twistedF4
    {X : Type} [Group X] [Finite X] {f : ℕ}
    (h : CFSG.Blueprint.LieModel X .twistedF4 0 2 f) {r : ℕ} (hr : r.Prime) (hr3 : 3 < r)
    (hrd : r ∣ 2 ^ f - 1) :
    (∀ S : Sylow r X, IsMulCommutative ↥S) ∧ 2 ≤ CFSG.Open.pRank r (⊤ : Subgroup X) := by
  classical
  haveI : Fact r.Prime := ⟨hr⟩
  obtain ⟨-, hR⟩ := LieModel.reeTitsModel (G := X) (t := .twistedF4) (n := 0) (p := 2)
    (f := f) h (by simp [reeTitsTags])
  have hcardX : Nat.card X = ordTwistedF4 (2 ^ f) :=
    CFSG.RankThree.PartOne.S12K.card_of_reeTitsModel_twistedF4 hR
  obtain ⟨a, K, hKF, hKFin, hcp, ha, hfa, hK, ⟨e⟩⟩ :=
    CFSG.QuasithinUnique.Setup.X6.exists_mulEquiv_largeRee_model hR
  letI : Field K := hKF
  letI : Finite K := hKFin
  letI : CharP K ReeTag.F4.prime := hcp
  have hK2 : Nat.card K = 2 ^ (2 * a + 1) := by rw [hK, hfa]
  have hK' : Nat.card K = ReeTag.F4.prime ^ (2 * a + 1) := by
    rw [hK2]
    rfl
  have hq2 : 2 ≤ 2 ^ f := by
    rw [hfa]
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  let Gf : Type := reeFixed ReeTag.F4 K a
  let T : Subgroup Gf := reeTorusPart ReeTag.F4 K a
  have hΓcard : Nat.card (ReeTag.F4.reeGamma K a) = ordTwistedF4 (2 ^ f) :=
    calc Nat.card (ReeTag.F4.reeGamma K a) = Nat.card X :=
          (Nat.card_congr e.toEquiv).symm
      _ = ordTwistedF4 (2 ^ f) := hcardX
  have hGfcard : Nat.card Gf = ordTwistedF4 (2 ^ f) :=
    calc Nat.card Gf = Nat.card (ReeTag.F4.reeGamma K a) :=
          Nat.card_congr (reeFixedEquivGamma (K := K) a).toEquiv
      _ = ordTwistedF4 (2 ^ f) := hΓcard
  have hGfac : (Nat.card Gf).factorization r =
      2 * (Nat.card K - 1).factorization r := by
    rw [hGfcard, hK]
    exact factorization_ordTwistedF4_of_dvd_sub_one hr hr3 hq2 hrd
  have hTcard : Nat.card T = (Nat.card K - 1) ^ 2 :=
    card_reeTorusPart (K := K) (a := a) hK'
  have hTfac : (Nat.card T).factorization r = (Nat.card Gf).factorization r := by
    rw [hTcard, Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul, hGfac]
  have hTcomm : IsMulCommutative ↥T :=
    isMulCommutative_reeTorusPart (t := ReeTag.F4) (K := K) (a := a)
  obtain ⟨P⟩ := Sylow.nonempty (p := r) (G := T)
  have hPcard : Nat.card (P.map T.subtype) = r ^ (Nat.card Gf).factorization r := by
    rw [Subgroup.card_map_of_injective T.subtype_injective, P.card_eq_multiplicity, hTfac]
  let S : Sylow r Gf := Sylow.ofCard (P.map T.subtype) hPcard
  have hScomm : IsMulCommutative ↥S := by
    change IsMulCommutative ↥(S : Subgroup Gf)
    rw [Sylow.coe_ofCard]
    letI : IsMulCommutative ↥T := hTcomm
    infer_instance
  have hAllGf : ∀ Q : Sylow r Gf, IsMulCommutative ↥Q := by
    intro Q
    have eQS : Q ≃* S := Sylow.equiv Q S
    refine IsMulCommutative.of_comm fun a b => eQS.injective ?_
    rw [map_mul, map_mul]
    exact mul_comm' (eQS a) (eQS b)
  let E : X ≃* Gf := e.trans (reeFixedEquivGamma (K := K) a).symm
  have hAllX : ∀ Q : Sylow r X, IsMulCommutative ↥Q := by
    intro Q
    have hQcard : Nat.card (Q.map E.toMonoidHom) =
        r ^ (Nat.card Gf).factorization r := by
      rw [Subgroup.card_map_of_injective E.injective, Sylow.card_eq_multiplicity Q,
        show Nat.card X = Nat.card Gf from Nat.card_congr E.toEquiv]
    let Q' : Sylow r Gf := Sylow.ofCard (Q.map E.toMonoidHom) hQcard
    have hmapcomm : IsMulCommutative ↥(Q.map E.toMonoidHom) := by
      rw [← Sylow.coe_ofCard (Q.map E.toMonoidHom) hQcard]
      exact hAllGf Q'
    let eQ : Q ≃* Q.map E.toMonoidHom :=
      Subgroup.equivMapOfInjective Q E.toMonoidHom E.injective
    refine IsMulCommutative.of_comm fun a b => eQ.injective ?_
    rw [map_mul, map_mul]
    haveI : IsMulCommutative ↥(Q.map E.toMonoidHom) := hmapcomm
    exact mul_comm' (eQ a) (eQ b)
  refine ⟨hAllX, ?_⟩
  have hp2 : r ≠ 2 := by omega
  exact two_le_pRank_is2F4 (X := X) (f := f) hR hr hp2 hrd

end Certificates

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
