module

public import CFSG.Quasithin.Recognition.Stroth.WeissDelta.RankOneFacts2
public import CFSG.Quasithin.Recognition.Stroth.WeissDelta.RankOneLocalL2
public import CFSG.Quasithin.Recognition.Stroth.WeissDelta.RankOneLocalSz2

public section

open scoped Pointwise

namespace CFSG.Quasithin.Stroth.WeissDelta

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.Stroth CFSG.Geometry.GeneralizedPolygons
  CFSG.GH74.GLS.SP CFSG.GH74.BNPair CFSG.QuasithinUnique
  CFSG.Quasithin.H13.F431.TwoF4 CFSG.Quasithin.H13.F431.Un
  CFSG.LieType.Ree.ReeTag CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits

private theorem card_inf_stabilizer_psl2 {X Ω : Type} [Group X] [Finite X] [Fintype Ω]
    [MulAction X Ω] [FaithfulSMul X Ω] (h2 : MulAction.IsMultiplyPretransitive X Ω 2) (m : ℕ)
    (hm : 2 ≤ m) (N : Subgroup X) (hN : N.Normal)
    (e : ↥N ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 m))
    (hΩ : Fintype.card Ω = 2 ^ m + 1) {ω ω' : Ω} (hne : ω ≠ ω') :
    Nat.card ↥(N ⊓ MulAction.stabilizer X ω ⊓ MulAction.stabilizer X ω') = 2 ^ m - 1 := by
  classical
  obtain ⟨S⟩ := L2.exists_l2Setup h2 m hm N hN e hΩ
  obtain ⟨r, hr⟩ := S.exists_torus_conj hne
  have himg := inf_stabilizer_eq_map_subtype (X := X) (N := N)
    (H := S.T.map (MulAut.conj r).toMonoidHom) (x := ω) (y := ω') hr
  rw [himg, Subgroup.card_map_of_injective N.subtype_injective,
    Subgroup.card_map_of_injective (MulAut.conj r).injective, S.hTcard]

theorem rankOneTransitive_psl2 {X Ω : Type} [Group X] [Finite X] [Fintype Ω] [MulAction X Ω]
    [FaithfulSMul X Ω] (h2 : MulAction.IsMultiplyPretransitive X Ω 2) (m : ℕ) (hm : 2 ≤ m)
    (N : Subgroup X) (hN : N.Normal)
    (e : ↥N ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 m))
    (hΩ : Fintype.card Ω = 2 ^ m + 1) :
    RankOneTransitive X Ω N := by
  classical
  have hL : RankOneLocal X Ω N := rankOneLocal_psl2 h2 m hm N hN e hΩ
  have hZ : RankOneZassenhaus X Ω N := rankOneZassenhaus_psl2 h2 m hm N hN e hΩ
  have hΩcard : Nat.card Ω = 2 ^ m + 1 := by rw [Nat.card_eq_fintype_card, hΩ]
  have hTcard : ∀ ω ω' : Ω, ω ≠ ω' →
      Nat.card ↥(N ⊓ MulAction.stabilizer X ω ⊓ MulAction.stabilizer X ω') =
        2 ^ m - 1 :=
    fun _ _ hne => card_inf_stabilizer_psl2 h2 m hm N hN e hΩ hne
  refine RankOneLocal.rankOneTransitive_of_zassenhaus hL hZ ?_
  intro ω ω' hne
  rw [hΩcard, hTcard ω ω' hne]
  have hpos : 0 < 2 ^ m := pow_pos (by norm_num) m
  omega

theorem rankOneCenter_psl2 {X Ω : Type} [Group X] [Finite X] [Fintype Ω] [MulAction X Ω]
    [FaithfulSMul X Ω] (h2 : MulAction.IsMultiplyPretransitive X Ω 2) (m : ℕ) (hm : 2 ≤ m)
    (N : Subgroup X) (hN : N.Normal)
    (e : ↥N ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 m))
    (hΩ : Fintype.card Ω = 2 ^ m + 1) :
    RankOneCenter X Ω N 1 := by
  classical
  have hL : RankOneLocal X Ω N := rankOneLocal_psl2 h2 m hm N hN e hΩ
  have hZ : RankOneZassenhaus X Ω N := rankOneZassenhaus_psl2 h2 m hm N hN e hΩ
  have hωexists : ∀ ω : Ω, ∃ ω' : Ω, ω' ≠ ω := by
    intro ω
    have hlt : 1 < Fintype.card Ω := by
      rw [hΩ]
      have hpos : 0 < 2 ^ m := pow_pos (by norm_num) m
      omega
    exact Fintype.exists_ne_of_one_lt_card hlt ω
  have hTcard : ∀ ω ω' : Ω, ω ≠ ω' →
      Nat.card ↥(N ⊓ MulAction.stabilizer X ω ⊓ MulAction.stabilizer X ω') =
        2 ^ m - 1 :=
    fun _ _ hne => card_inf_stabilizer_psl2 h2 m hm N hN e hΩ hne
  refine RankOneLocal.rankOneCenter_of_zassenhaus hN hL hZ ?_
  intro ω ω' hne R hR hRn hR2 hreg
  let T : Subgroup X := N ⊓ MulAction.stabilizer X ω ⊓ MulAction.stabilizer X ω'
  have hcardT : Nat.card ↥T = 2 ^ m - 1 := by
    dsimp only [T]
    exact hTcard ω ω' hne
  have hRcard : Nat.card R = 2 ^ m := by
    have hreg' : CFSG.BenderSuzuki.IsRegularOn R {β : Ω | β ≠ ω} := hreg
    have h := CFSG.BenderSuzuki.IsRegularOn.natCard_compl_point (G := X) (Ω := Ω)
      (R := R) (α := ω) hreg' hR (hωexists ω)
    rw [h, Nat.card_eq_fintype_card, hΩ]
    have hpos : 0 < 2 ^ m := pow_pos (by norm_num) m
    omega
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2dvd : 2 ∣ Nat.card R := by
    rw [hRcard]
    exact dvd_pow_self 2 (by omega)
  obtain ⟨z₁, hz₁ord⟩ := exists_prime_orderOf_dvd_card' (G := R) 2 h2dvd
  have hz₁ne : z₁ ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hz₁ord
    omega
  have hz₁neX : (z₁ : X) ≠ 1 := by
    intro h
    exact hz₁ne (Subtype.ext (by simpa using h))
  have hz₁sq : z₁ * z₁ = 1 := by
    rw [← pow_two, ← hz₁ord]
    exact pow_orderOf_eq_one z₁
  have hz₁sqX : (z₁ : X) * (z₁ : X) = 1 := congrArg (fun r : R => (r : X)) hz₁sq
  have hfree : ∀ t : T, t ≠ 1 → ∀ z ∈ R, z ≠ 1 →
      (t : X) * z * (t : X)⁻¹ ≠ z := by
    intro t ht1 z hzR hz1 hconj
    have hzω : z • ω = ω := MulAction.mem_stabilizer_iff.mp (hR hzR)
    have hzω' : z • ω' ≠ ω' := by
      intro h
      have h1 : (⟨z, hzR⟩ : R) = 1 :=
        (hreg ω' ω' hne.symm hne.symm).unique (by simpa using h) (by simp)
      exact hz1 (congrArg Subtype.val h1)
    have hzω'neω : z • ω' ≠ ω := by
      intro h
      have h2 : ω' = ω := by
        calc ω' = z⁻¹ • (z • ω') := (inv_smul_smul z ω').symm
          _ = z⁻¹ • ω := by rw [h]
          _ = ω := by
            conv_lhs => rw [← hzω]
            exact inv_smul_smul z ω
      exact hne h2.symm
    have hcomm : (t : X) * z = z * (t : X) := by
      calc (t : X) * z = ((t : X) * z * (t : X)⁻¹) * (t : X) := by group
        _ = z * (t : X) := by rw [hconj]
    have hfix : (t : X) • (z • ω') = z • ω' := by
      rw [← mul_smul, hcomm, mul_smul]
      congr 1
      exact MulAction.mem_stabilizer_iff.mp t.2.2
    have htneX : (t : X) ≠ 1 := by
      intro h
      exact ht1 (Subtype.ext (by simpa using h))
    rcases hZ.fix_two ω ω' hne (t : X) t.2 htneX (z • ω') hfix with h | h
    · exact hzω'neω h
    · exact hzω' h
  have hconjR : ∀ t : T, (t : X) * (z₁ : X) * (t : X)⁻¹ ∈ R := by
    intro t
    exact (Subgroup.normal_subgroupOf_iff hR).mp hRn (z₁ : X) (t : X) z₁.2 t.2.1.2
  have hconj_ne : ∀ t : T, (t : X) * (z₁ : X) * (t : X)⁻¹ ≠ 1 := by
    intro t h
    apply hz₁neX
    calc (z₁ : X) = (t : X)⁻¹ * ((t : X) * (z₁ : X) * (t : X)⁻¹) * (t : X) := by group
      _ = 1 := by rw [h]; group
  have hconj_ne' : ∀ t : T,
      (⟨(t : X) * (z₁ : X) * (t : X)⁻¹, hconjR t⟩ : R) ≠ 1 := by
    intro t h
    exact hconj_ne t (by simpa using congrArg (fun r : R => (r : X)) h)
  let F : T → {z : R // z ≠ 1} := fun t =>
    ⟨⟨(t : X) * (z₁ : X) * (t : X)⁻¹, hconjR t⟩, hconj_ne' t⟩
  have hsubCard : Nat.card {z : R // z ≠ 1} = Nat.card R - 1 := by
    haveI : Fintype R := Fintype.ofFinite R
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
      Fintype.card_subtype_compl (fun z : R => z = 1)]
    simp
  have hcards : Nat.card {z : R // z ≠ 1} = Nat.card ↥T := by
    rw [hsubCard, hRcard, hcardT]
  have hFinj : Function.Injective F := by
    intro t₁ t₂ h
    have hconj : (t₁ : X) * (z₁ : X) * (t₁ : X)⁻¹ =
        (t₂ : X) * (z₁ : X) * (t₂ : X)⁻¹ := by
      simpa [F] using congrArg (fun z : {z : R // z ≠ 1} => ((z : R) : X)) h
    by_contra hneq
    have hu_ne : (t₂⁻¹ * t₁ : T) ≠ 1 := by
      intro hu
      apply hneq
      calc t₁ = t₂ * (t₂⁻¹ * t₁) := by group
        _ = t₂ * 1 := by rw [hu]
        _ = t₂ := mul_one t₂
    have hu_neX : ((t₂⁻¹ * t₁ : T) : X) ≠ 1 := by
      intro h1
      exact hu_ne (Subtype.ext (by simpa using h1))
    have hcomm : ((t₂⁻¹ * t₁ : T) : X) * (z₁ : X) =
        (z₁ : X) * ((t₂⁻¹ * t₁ : T) : X) := by
      have h1 : (t₂ : X)⁻¹ * (t₁ : X) * (z₁ : X) =
          (z₁ : X) * ((t₂ : X)⁻¹ * (t₁ : X)) := by
        have h2 : (t₂ : X)⁻¹ * (t₁ : X) * (z₁ : X) *
            ((t₂ : X)⁻¹ * (t₁ : X))⁻¹ = (z₁ : X) := by
          calc (t₂ : X)⁻¹ * (t₁ : X) * (z₁ : X) *
                ((t₂ : X)⁻¹ * (t₁ : X))⁻¹
              = (t₂ : X)⁻¹ * ((t₁ : X) * (z₁ : X) * (t₁ : X)⁻¹) * (t₂ : X) := by
                group
            _ = (t₂ : X)⁻¹ * ((t₂ : X) * (z₁ : X) * (t₂ : X)⁻¹) * (t₂ : X) := by
                rw [hconj]
            _ = (z₁ : X) := by group
        calc (t₂ : X)⁻¹ * (t₁ : X) * (z₁ : X)
            = ((t₂ : X)⁻¹ * (t₁ : X) * (z₁ : X) *
                ((t₂ : X)⁻¹ * (t₁ : X))⁻¹) * ((t₂ : X)⁻¹ * (t₁ : X)) := by group
          _ = (z₁ : X) * ((t₂ : X)⁻¹ * (t₁ : X)) := by rw [h2]
      simpa [Subgroup.coe_mul, Subgroup.coe_inv] using h1
    have hfix : ((t₂⁻¹ * t₁ : T) : X) * (z₁ : X) *
        ((t₂⁻¹ * t₁ : T) : X)⁻¹ = (z₁ : X) := by
      rw [hcomm]
      group
    exact hfree (t₂⁻¹ * t₁) hu_ne (z₁ : X) z₁.2 hz₁neX hfix
  have hFsurj : Function.Surjective F := by
    have hbij : Function.Bijective F :=
      (Nat.bijective_iff_injective_and_card F).mpr ⟨hFinj, hcards.symm⟩
    exact hbij.2
  have hsq : ∀ z : R, z * z = 1 := by
    intro z
    by_cases hz1 : z = 1
    · rw [hz1]
      simp
    · obtain ⟨t, ht⟩ := hFsurj ⟨z, hz1⟩
      have hzval : ((F t : {z : R // z ≠ 1}) : R) = z :=
        congrArg (fun w : {z : R // z ≠ 1} => (w : R)) ht
      have hzX : (z : X) = (t : X) * (z₁ : X) * (t : X)⁻¹ := by
        rw [← congrArg (fun r : R => (r : X)) hzval]
      apply Subtype.ext
      change (z : X) * (z : X) = 1
      rw [hzX]
      calc ((t : X) * (z₁ : X) * (t : X)⁻¹) * ((t : X) * (z₁ : X) * (t : X)⁻¹)
          = (t : X) * ((z₁ : X) * (z₁ : X)) * (t : X)⁻¹ := by group
        _ = 1 := by rw [hz₁sqX]; group
  have hcommR : ∀ a b : R, a * b = b * a := by
    intro a b
    have ha : a * a = 1 := hsq a
    have hb : b * b = 1 := hsq b
    have hab : (a * b) * (a * b) = 1 := hsq (a * b)
    calc a * b = a * ((a * b) * (a * b)) * b := by rw [hab]; group
      _ = (a * a) * b * a * (b * b) := by group
      _ = b * a := by rw [ha, hb]; group
  have hRcent : R ≤ Subgroup.centralizer (R : Set X) := by
    intro r hr
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    exact (congrArg (fun x : R => (x : X)) (hcommR ⟨r, hr⟩ ⟨s, hs⟩)).symm
  have hinf : R ⊓ Subgroup.centralizer (R : Set X) = R := inf_eq_left.mpr hRcent
  have hcardZR : Nat.card ↥(R ⊓ Subgroup.centralizer (R : Set X)) = Nat.card R := by
    rw [hinf]
  rw [hcardZR, hRcard, hcardT]
  have hpos : 0 < 2 ^ m := pow_pos (by norm_num) m
  omega

end CFSG.Quasithin.Stroth.WeissDelta

end
