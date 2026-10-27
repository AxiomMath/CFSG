module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Corollary85Count
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section2.proposition_3

namespace CFSG
end CFSG
open CFSG

/-!
# Corollary 8.5 fixed-field calculation

This file derives the prime-order and product conclusions needed in Corollary
8.5 from Peterfalvi's semilinear field coordinates.
-/

noncomputable section

namespace CFSG.BenderSuzuki

open PFAppendixIII PFchapter1section1 PFchapter1section2
open scoped Pointwise

private theorem galoisField_finrank_of_subfield_eq_bot
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    {n : ℕ} (hFcard : Nat.card F = 2 ^ n)
    (E : Subfield F) (m : ℕ)
    (hfinrank : Module.finrank E F = m) (hfixed : E = ⊥) :
    m = n := by
  have hfinrankBot : Module.finrank (⊥ : Subfield F) F = m := by
    rw [← hfixed]
    exact hfinrank
  have hcard := Module.natCard_eq_pow_finrank (K := E) (V := F)
  have hpow : Nat.card F = 2 ^ m := by
    rw [hfixed, Subfield.card_bot F 2, hfinrankBot] at hcard
    exact hcard
  exact Nat.pow_right_injective (by norm_num : 2 ≤ 2)
    (hpow.symm.trans hFcard)

private theorem corollary85_k_action
    {G F : Type*} [Group G] [Field F]
    (D K V W Q0 : Subgroup G)
    (A : Subgroup (F ≃+* F))
    (hKleD : K ≤ D) (hVleD : V ≤ D)
    (hKnormal : (K.subgroupOf D).Normal)
    (hWV : (W.subgroupOf V).Normal)
    (hWD : (W.subgroupOf D).Normal)
    (rhoD : (D ⧸ W.subgroupOf D) →* MulAut Q0)
    (rhoMul : Fˣ →* MulAut (Multiplicative F))
    (rhoAut : A →* MulAut
      (SemidirectProduct (Multiplicative F) Fˣ rhoMul))
    (kUnits : K ≃* Fˣ)
    (vmodWAut : V ⧸ W.subgroupOf V ≃* A)
    (modelIso :
      SemidirectProduct Q0 (D ⧸ W.subgroupOf D) rhoD ≃*
        SemidirectProduct
          (SemidirectProduct (Multiplicative F) Fˣ rhoMul) A rhoAut)
    (hrhoAutInr : ∀ sigma : A, ∀ u : Fˣ,
      rhoAut sigma (SemidirectProduct.inr u) =
        SemidirectProduct.inr
          (Units.map (sigma : F ≃+* F).toMonoidWithZeroHom u))
    (hmodelK : ∀ k : K,
      modelIso
          (SemidirectProduct.inr
            (QuotientGroup.mk (⟨(k : G), hKleD k.property⟩ : D))) =
        SemidirectProduct.inl
          (SemidirectProduct.inr (kUnits k)))
    (hmodelV : ∀ v : V,
      modelIso
          (SemidirectProduct.inr
            (QuotientGroup.mk (⟨(v : G), hVleD v.property⟩ : D))) =
        SemidirectProduct.inr
          (vmodWAut (QuotientGroup.mk v)))
    (v : V) (k : K) :
    ∃ hk : rightConjugateElem (k : G) (v : G) ∈ K,
      kUnits ⟨rightConjugateElem (k : G) (v : G), hk⟩ =
        Units.map
          (vmodWAut (QuotientGroup.mk v) : F ≃+* F).symm.toMonoidWithZeroHom
          (kUnits k) := by
  letI : (W.subgroupOf V).Normal := hWV
  letI : (W.subgroupOf D).Normal := hWD
  let kD : D := ⟨(k : G), hKleD k.property⟩
  let vD : D := ⟨(v : G), hVleD v.property⟩
  have hkD : vD⁻¹ * kD * vD ∈ K.subgroupOf D := by
    simpa using hKnormal.conj_mem kD k.property vD⁻¹
  have hk : rightConjugateElem (k : G) (v : G) ∈ K := by
    change (⟨(v : G), hVleD v.property⟩ : D)⁻¹ *
          ⟨(k : G), hKleD k.property⟩ *
          (⟨(v : G), hVleD v.property⟩ : D) ∈ K.subgroupOf D at hkD
    exact hkD
  let kv : K := ⟨rightConjugateElem (k : G) (v : G), hk⟩
  let kbar : D ⧸ W.subgroupOf D := QuotientGroup.mk kD
  let vbar : D ⧸ W.subgroupOf D := QuotientGroup.mk vD
  let sigma : A := vmodWAut (QuotientGroup.mk v)
  let C := SemidirectProduct
    (SemidirectProduct (Multiplicative F) Fˣ rhoMul) A rhoAut
  have hkvbar :
      QuotientGroup.mk (⟨(kv : G), hKleD kv.property⟩ : D) =
        vbar⁻¹ * kbar * vbar := by
    apply Quotient.sound
    have heq :
        (⟨(kv : G), hKleD kv.property⟩ : D) = vD⁻¹ * kD * vD := by
      apply Subtype.ext
      rfl
    rw [heq]
  have himage :
      (SemidirectProduct.inl
          (SemidirectProduct.inr (kUnits kv)) : C) =
        (SemidirectProduct.inl
          (SemidirectProduct.inr
            (Units.map ((sigma : F ≃+* F).symm).toMonoidWithZeroHom
              (kUnits k))) : C) := by
    calc
      SemidirectProduct.inl (SemidirectProduct.inr (kUnits kv)) =
          modelIso (SemidirectProduct.inr
            (QuotientGroup.mk
              (⟨(kv : G), hKleD kv.property⟩ : D))) := (hmodelK kv).symm
      _ = modelIso
          ((SemidirectProduct.inr vbar)⁻¹ *
            SemidirectProduct.inr kbar * SemidirectProduct.inr vbar) := by
              rw [hkvbar]
              simp
      _ = (SemidirectProduct.inr sigma)⁻¹ *
            SemidirectProduct.inl (SemidirectProduct.inr (kUnits k)) *
              SemidirectProduct.inr sigma := by
              rw [map_mul, map_mul, map_inv]
              rw [show modelIso (SemidirectProduct.inr vbar) =
                    SemidirectProduct.inr sigma by
                  simpa [vbar, sigma, vD] using hmodelV v]
              rw [show modelIso (SemidirectProduct.inr kbar) =
                    SemidirectProduct.inl
                      (SemidirectProduct.inr (kUnits k)) by
                  simpa [kbar, kD] using hmodelK k]
      _ = SemidirectProduct.inl
          ((rhoAut sigma)⁻¹ (SemidirectProduct.inr (kUnits k))) := by
            simpa using
              (SemidirectProduct.inl_aut_inv (φ := rhoAut) sigma
                (SemidirectProduct.inr (kUnits k))).symm
      _ = SemidirectProduct.inl
          (SemidirectProduct.inr
            (Units.map ((sigma : F ≃+* F).symm).toMonoidWithZeroHom
              (kUnits k))) := by
            rw [show (rhoAut sigma)⁻¹ = rhoAut sigma⁻¹ by
              simpa using (map_inv rhoAut sigma).symm]
            have hunit :
                Units.map
                    (↑(((sigma⁻¹ : A) : F ≃+* F).toMonoidWithZeroHom) : F →* F)
                    (kUnits k) =
                    Units.map
                    (↑(((sigma : F ≃+* F).symm).toMonoidWithZeroHom) : F →* F)
                    (kUnits k) := by
              congr 1
            have h := congrArg
              (fun z : SemidirectProduct (Multiplicative F) Fˣ rhoMul =>
                (SemidirectProduct.inl z : C))
              (hrhoAutInr sigma⁻¹ (kUnits k))
            rw [hunit] at h
            exact h
  refine ⟨hk, ?_⟩
  change kUnits kv = _
  exact SemidirectProduct.inr_injective
    (SemidirectProduct.inl_injective himage)

set_option maxHeartbeats 800000 in
public theorem corollary85_fixedField_endpoints
    {G Omega : Type*} [Group G] [Finite G] [MulAction G Omega] [Finite Omega]
    (H D Q K V W Q0 : Subgroup G) (t : G)
    (hsec : Proposition3FieldModelA1Data (Ω := Omega) H D Q K V W Q0 t)
    (P : Subgroup G) (hPV : P ≤ V) (hPne : P ≠ ⊥) (hKne : K ≠ ⊥)
    (hfixed : ∀ p : G, p ∈ P → p ≠ 1 →
      ∀ k : G, k ∈ K → k * p = p * k → k = 1) :
    Nat.Prime (Nat.card P) ∧
      Nat.card K = 2 ^ Nat.card P - 1 ∧
      (V : Set G) = (W : Set G) * (P : Set G) ∧
      Nat.card Q0 = 2 ^ Nat.card P ∧
      Nat.card (Q0 ⊓ Subgroup.centralizer (P : Set G) : Subgroup G) = 2 := by
  classical
  rcases proposition_3_field_model_with_q0_card_of_hypothesisA1
      H D Q K V W Q0 t hsec with
    ⟨fieldN, hfieldN, _hQ0pow, A, hWV, hWD,
      rhoD, rhoMul, rhoAut, q0Add, kUnits, vmodWAut, modelIso,
      _hQ0card, _hrhoMul, _hrhoAutInl, hrhoAutInr, _hrhoD,
      _hmodelQ, hmodelK, hmodelV, _hkAction, hvAction⟩
  let F := GaloisField 2 fieldN
  letI : Field F := inferInstance
  letI : Finite F := inferInstance
  letI : Fintype F := Fintype.ofFinite F
  letI : Finite A :=
    Finite.of_injective vmodWAut.symm vmodWAut.symm.injective
  have hFcard : Nat.card F = 2 ^ fieldN := by
    simpa [F] using GaloisField.card 2 fieldN hfieldN
  letI : (W.subgroupOf V).Normal := hWV
  letI : (W.subgroupOf D).Normal := hWD
  have hPinfW : P ⊓ W = ⊥ := by
    apply le_antisymm
    · intro p hp
      rw [Subgroup.mem_bot]
      by_contra hpOne
      obtain ⟨k, hkOne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hKne
      have hpC : (p : G) ∈ Subgroup.centralizer (K : Set G) := by
        have hpW : (p : G) ∈ W := hp.2
        rw [hsec.W_eq] at hpW
        exact hpW.2
      have hcomm : (k : G) * (p : G) = (p : G) * (k : G) :=
        (Subgroup.mem_centralizer_iff.mp hpC) (k : G) k.property
      have hkG := hfixed (p : G) hp.1 hpOne (k : G) k.property hcomm
      exact hkOne (Subtype.ext hkG)
    · exact bot_le
  let pToV : P →* V := Subgroup.inclusion hPV
  let pToA : P →* A :=
    vmodWAut.toMonoidHom.comp
      ((QuotientGroup.mk' (W.subgroupOf V)).comp pToV)
  let rhoP : P →* (F ≃+* F) := A.subtype.comp pToA
  have hpToA_injective : Function.Injective pToA := by
    intro p q hpq
    have hquot :
        QuotientGroup.mk' (W.subgroupOf V) (pToV p) =
          QuotientGroup.mk' (W.subgroupOf V) (pToV q) := by
      apply vmodWAut.injective
      simpa [pToA] using hpq
    have hdivWV : pToV p / pToV q ∈ W.subgroupOf V :=
      (QuotientGroup.eq_iff_div_mem (N := W.subgroupOf V)).mp hquot
    have hdivW : ((pToV p / pToV q : V) : G) ∈ W := hdivWV
    have hdivP : (p : G) / (q : G) ∈ P := P.div_mem p.property q.property
    have hdivBot : (p : G) / (q : G) ∈ (⊥ : Subgroup G) := by
      rw [← hPinfW]
      exact ⟨hdivP, by simpa [pToV] using hdivW⟩
    have hdivOne : (p : G) / (q : G) = 1 := by simpa using hdivBot
    apply Subtype.ext
    exact div_eq_one.mp hdivOne
  have hrhoP_injective : Function.Injective rhoP := by
    intro p q hpq
    apply hpToA_injective
    apply Subtype.ext
    exact hpq
  letI : MulSemiringAction P F := MulSemiringAction.compHom F rhoP
  letI : FaithfulSMul P F :=
    ⟨fun {p q} hpq => hrhoP_injective (by
      ext x
      exact hpq x)⟩
  have hfixedElement : ∀ p : P, p ≠ 1 →
      ∀ x : F, rhoP p x = x → x ∈ (⊥ : Subfield F) := by
    intro p hpOne x hpx
    by_cases hxZero : x = 0
    · simpa [hxZero]
    · let ux : Fˣ := Units.mk0 x hxZero
      let k : K := kUnits.symm ux
      let v : V := pToV p
      let sigma : F ≃+* F := vmodWAut (QuotientGroup.mk v)
      have hsigmaX : sigma x = x := by
        simpa [sigma, rhoP, pToA, v, pToV] using hpx
      have hsigmaSymm : sigma.symm x = x := by
        apply sigma.injective
        simpa [hsigmaX]
      have huFix : Units.map sigma.symm.toMonoidWithZeroHom ux = ux := by
        apply Units.ext
        simpa [ux] using hsigmaSymm
      obtain ⟨hk, hkImage⟩ :=
        corollary85_k_action D K V W Q0 A
          hsec.K_le_D hsec.V_le_D hsec.K_normal_D hWV hWD
          rhoD rhoMul rhoAut kUnits vmodWAut modelIso
          hrhoAutInr hmodelK hmodelV v k
      let kv : K := ⟨rightConjugateElem (k : G) (v : G), hk⟩
      have hkv : kv = k := by
        apply kUnits.injective
        have huFix' :
            Units.map
              (vmodWAut (QuotientGroup.mk v) : F ≃+* F).symm.toMonoidWithZeroHom
              (kUnits k) = kUnits k := by
          simpa [sigma, k] using huFix
        exact hkImage.trans huFix'
      have hconj : rightConjugateElem (k : G) (p : G) = (k : G) :=
        congrArg Subtype.val hkv
      have hpGOne : (p : G) ≠ 1 := by
        intro hpG
        exact hpOne (Subtype.ext hpG)
      have hcomm : (k : G) * (p : G) = (p : G) * (k : G) := by
        calc
          (k : G) * (p : G) =
              (p : G) * ((p : G)⁻¹ * (k : G) * (p : G)) := by group
          _ = (p : G) * (k : G) := by
            simpa [rightConjugateElem] using
              congrArg (fun z => (p : G) * z) hconj
      have hkOne : (k : G) = 1 :=
        hfixed (p : G) p.property hpGOne (k : G) k.property hcomm
      have hkOne' : k = 1 := Subtype.ext hkOne
      have huOne : ux = 1 := by
        have h := congrArg kUnits hkOne'
        simpa [k, ux] using h
      have hxOne : x = 1 := by
        simpa [ux] using congrArg Units.val huOne
      simpa [hxOne]
  obtain ⟨p0, hp0⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hPne
  have hfixedP : FixedPoints.subfield P F = ⊥ := by
    apply le_antisymm
    · intro x hx
      exact hfixedElement p0 hp0 x (hx p0)
    · exact bot_le
  have hfinrankP :
      Module.finrank (FixedPoints.subfield P F) F = Nat.card P := by
    letI : Fintype P := Fintype.ofFinite P
    rw [FixedPoints.finrank_eq_card P F, Fintype.card_eq_nat_card]
  have hPcard : Nat.card P = fieldN :=
    galoisField_finrank_of_subfield_eq_bot
      (F := F) hFcard (FixedPoints.subfield P F) (Nat.card P)
        hfinrankP hfixedP
  have hKcard : Nat.card K = 2 ^ Nat.card P - 1 := by
    calc
      Nat.card K = Nat.card Fˣ := Nat.card_congr kUnits.toEquiv
      _ = Nat.card F - 1 := Nat.card_units F
      _ = 2 ^ fieldN - 1 := by rw [hFcard]
      _ = 2 ^ Nat.card P - 1 := by rw [hPcard]
  have hQ0cardP : Nat.card Q0 = 2 ^ Nat.card P := by
    calc
      Nat.card Q0 = 2 ^ fieldN := _hQ0pow
      _ = 2 ^ Nat.card P := by rw [hPcard]
  have hzpTop : ∀ p : P, p ≠ 1 → Subgroup.zpowers p = ⊤ := by
    intro p hpOne
    let Z : Subgroup P := Subgroup.zpowers p
    let zToP : Z →* P := Z.subtype
    have hfixedZ : FixedPoints.subfield Z F = ⊥ := by
      apply le_antisymm
      · intro x hx
        let pZ : Z := ⟨p, Subgroup.mem_zpowers p⟩
        apply hfixedElement p hpOne x
        change p • x = x
        exact hx pZ
      · exact bot_le
    have hfinrankZ :
        Module.finrank (FixedPoints.subfield Z F) F = Nat.card Z := by
      letI : Fintype Z := Fintype.ofFinite Z
      rw [FixedPoints.finrank_eq_card Z F, Fintype.card_eq_nat_card]
    have hZcard : Nat.card Z = fieldN :=
      galoisField_finrank_of_subfield_eq_bot
        (F := F) hFcard (FixedPoints.subfield Z F) (Nat.card Z)
          hfinrankZ hfixedZ
    apply Subgroup.eq_top_of_card_eq Z
    exact hZcard.trans hPcard.symm
  have hPprime : Nat.Prime (Nat.card P) := by
    have hPcardNe : Nat.card P ≠ 1 := by
      intro hcard
      exact hPne ((Subgroup.eq_bot_iff_card P).mpr hcard)
    obtain ⟨r, hrPrime, hrDvd⟩ := Nat.exists_prime_and_dvd hPcardNe
    letI : Fact (Nat.Prime r) := ⟨hrPrime⟩
    obtain ⟨p, hpOrder⟩ := exists_prime_orderOf_dvd_card' (G := P) r hrDvd
    have hpOne : p ≠ 1 := by
      intro hp
      exact hrPrime.ne_one (by simpa [hp] using hpOrder.symm)
    have htop := hzpTop p hpOne
    have hcardEq : Nat.card P = r := by
      calc
        Nat.card P = Nat.card (Subgroup.zpowers p) := by rw [htop]; simp
        _ = orderOf p := Nat.card_zpowers p
        _ = r := hpOrder
    simpa [hcardEq] using hrPrime
  have hfixedA : FixedPoints.subfield A F = ⊥ := by
    apply le_antisymm
    · intro x hx
      apply hfixedElement p0 hp0 x
      change pToA p0 • x = x
      exact hx (pToA p0)
    · exact bot_le
  have hfinrankA :
      Module.finrank (FixedPoints.subfield A F) F = Nat.card A := by
    letI : Fintype A := Fintype.ofFinite A
    rw [FixedPoints.finrank_eq_card A F, Fintype.card_eq_nat_card]
  have hAcard : Nat.card A = fieldN :=
    galoisField_finrank_of_subfield_eq_bot
      (F := F) hFcard (FixedPoints.subfield A F) (Nat.card A)
        hfinrankA hfixedA
  have hpToA_surjective : Function.Surjective pToA := by
    letI : Fintype P := Fintype.ofFinite P
    letI : Fintype A := Fintype.ofFinite A
    exact ((Fintype.bijective_iff_injective_and_card pToA).mpr
      ⟨hpToA_injective, by
        rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card]
        exact hPcard.trans hAcard.symm⟩).2
  have hVfactor : (V : Set G) = (W : Set G) * (P : Set G) := by
    apply Set.Subset.antisymm
    · intro v hv
      let vV : V := ⟨v, hv⟩
      obtain ⟨p, hp⟩ := hpToA_surjective
        (vmodWAut (QuotientGroup.mk vV))
      have hquot :
          QuotientGroup.mk' (W.subgroupOf V) vV =
            QuotientGroup.mk' (W.subgroupOf V) (pToV p) := by
        apply vmodWAut.injective
        exact hp.symm
      have hdivW : (vV / pToV p : V) ∈ W.subgroupOf V :=
        QuotientGroup.eq_iff_div_mem.mp hquot
      rw [Set.mem_mul]
      refine ⟨((vV / pToV p : V) : G), hdivW, (p : G), p.property, ?_⟩
      simp [vV, pToV, div_eq_mul_inv, mul_assoc]
    · intro x hx
      rw [Set.mem_mul] at hx
      rcases hx with ⟨w, hw, p, hp, rfl⟩
      exact V.mul_mem (hsec.W_le_V hw) (hPV hp)
  let fixedQ0Equiv : FixedPoints.subfield P F ≃
      ↥(Q0 ⊓ Subgroup.centralizer (P : Set G)) :=
    { toFun := fun x => by
        let q : Q0 := q0Add.symm (Multiplicative.ofAdd (x : F))
        refine ⟨(q : G), q.property, ?_⟩
        change (q : G) ∈ Subgroup.centralizer (P : Set G)
        rw [Subgroup.mem_centralizer_iff]
        intro y hyP
        let yP : P := ⟨y, hyP⟩
        let yV : V := pToV yP
        rcases hvAction yV q with ⟨hqConj, hqImage⟩
        have hfixF : rhoP yP (x : F) = (x : F) := by
          change pToA yP • (x : F) = (x : F)
          exact x.property yP
        have hforward :
            (vmodWAut (QuotientGroup.mk yV) : F ≃+* F)
                (Multiplicative.toAdd (q0Add q)) =
              Multiplicative.toAdd (q0Add q) := by
          simpa [q, MulAction.compHom_smul_def, rhoP, pToA, pToV, yP, yV] using hfixF
        have hbackward :
            (vmodWAut (QuotientGroup.mk yV) : F ≃+* F).symm
                (Multiplicative.toAdd (q0Add q)) =
              Multiplicative.toAdd (q0Add q) := by
          apply (vmodWAut (QuotientGroup.mk yV) : F ≃+* F).injective
          simpa using hforward.symm
        have hqImage' :
            q0Add ⟨rightConjugateElem (q : G) y, hqConj⟩ = q0Add q := by
          simpa [hbackward, yV, yP, pToV] using hqImage
        have hright : rightConjugateElem (q : G) y = (q : G) :=
          congrArg Subtype.val (q0Add.injective hqImage')
        calc
          y * (q : G) = y * rightConjugateElem (q : G) y := by rw [hright]
          _ = (q : G) * y := by simp [rightConjugateElem, mul_assoc]
      invFun := fun y => by
        let q : Q0 := ⟨(y : G), y.property.1⟩
        let a : F := Multiplicative.toAdd (q0Add q)
        refine ⟨a, ?_⟩
        change a ∈ MulAction.fixedPoints P F
        rw [MulAction.mem_fixedPoints]
        intro xP
        let xV : V := pToV xP
        rcases hvAction xV q with ⟨hqConj, hqImage⟩
        have hright : rightConjugateElem (q : G) (xP : G) = (q : G) := by
          have hcomm : (xP : G) * (q : G) = (q : G) * (xP : G) :=
            (Subgroup.mem_centralizer_iff.mp y.property.2)
              (xP : G) xP.property
          calc
            rightConjugateElem (q : G) (xP : G) =
                (xP : G)⁻¹ * ((q : G) * (xP : G)) := by
              simp [rightConjugateElem, mul_assoc]
            _ = (xP : G)⁻¹ * ((xP : G) * (q : G)) := by rw [← hcomm]
            _ = (q : G) := by simp
        have hsymm :
            (vmodWAut (QuotientGroup.mk xV) : F ≃+* F).symm a = a := by
          apply Multiplicative.ofAdd.injective
          calc
            Multiplicative.ofAdd
                ((vmodWAut (QuotientGroup.mk xV) : F ≃+* F).symm a) =
                q0Add ⟨rightConjugateElem (q : G) (xP : G), hqConj⟩ := by
              simpa [q, a, xV, pToV] using hqImage.symm
            _ = q0Add q := by simp [hright]
            _ = Multiplicative.ofAdd a := by simp [a]
        change rhoP xP a = a
        change (vmodWAut (QuotientGroup.mk xV) : F ≃+* F) a = a
        calc
          (vmodWAut (QuotientGroup.mk xV) : F ≃+* F) a =
              (vmodWAut (QuotientGroup.mk xV) : F ≃+* F)
                ((vmodWAut (QuotientGroup.mk xV) : F ≃+* F).symm a) := by
            rw [hsymm]
          _ = a :=
            (vmodWAut (QuotientGroup.mk xV) : F ≃+* F).apply_symm_apply a
      left_inv := by
        intro x
        apply Subtype.ext
        show Multiplicative.toAdd
            (q0Add (q0Add.symm (Multiplicative.ofAdd (x : F)))) = (x : F)
        simp
      right_inv := by
        intro y
        apply Subtype.ext
        show (q0Add.symm
            (Multiplicative.ofAdd
              (Multiplicative.toAdd
                (q0Add ⟨(y : G), y.property.1⟩))) : G) = (y : G)
        exact congrArg Subtype.val (by simp :
          q0Add.symm
              (Multiplicative.ofAdd
                (Multiplicative.toAdd
                  (q0Add ⟨(y : G), y.property.1⟩))) =
            ⟨(y : G), y.property.1⟩) }
  have hfixedFieldCard : Nat.card (FixedPoints.subfield P F) = 2 := by
    rw [hfixedP]
    exact Subfield.card_bot F 2
  have hfixedQ0Card :
      Nat.card (Q0 ⊓ Subgroup.centralizer (P : Set G) : Subgroup G) = 2 := by
    calc
      Nat.card (Q0 ⊓ Subgroup.centralizer (P : Set G) : Subgroup G) =
          Nat.card (FixedPoints.subfield P F) :=
        Nat.card_congr fixedQ0Equiv.symm
      _ = 2 := hfixedFieldCard
  exact ⟨hPprime, hKcard, hVfactor, hQ0cardP, hfixedQ0Card⟩

end CFSG.BenderSuzuki
