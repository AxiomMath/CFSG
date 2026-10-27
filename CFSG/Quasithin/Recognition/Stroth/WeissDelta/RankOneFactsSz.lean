module

public import CFSG.Quasithin.Recognition.Stroth.WeissDelta.RankOneFacts2
public import CFSG.Quasithin.Recognition.Stroth.WeissDelta.RankOneLocalSz3
public import CFSG.StronglyEmbedded.BenderCentre

public section

open scoped Pointwise

namespace CFSG.Quasithin.Stroth.WeissDelta

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.Stroth CFSG.Geometry.GeneralizedPolygons
  CFSG.GH74.GLS.SP CFSG.GH74.BNPair CFSG.QuasithinUnique
  CFSG.Quasithin.H13.F431.TwoF4 CFSG.Quasithin.H13.F431.Un
  CFSG.LieType.Ree.ReeTag CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
  CFSG.LieType.Ree CFSG.ShultStronglyClosedTI.SuzukiModel
  CFSG.ComponentClassification.AschbacherToolkit.Bender

private theorem root_data_sz {X Ω : Type} [Group X] [Finite X]
    [Fintype Ω] [MulAction X Ω] [FaithfulSMul X Ω]
    (h2 : MulAction.IsMultiplyPretransitive X Ω 2) {a : ℕ} (ha : 1 ≤ a)
    (N : Subgroup X) (hN : N.Normal) (e : ↥N ≃* Sz a)
    (hΩ : Fintype.card Ω = 2 ^ (2 * (2 * a + 1)) + 1) (x : Ω) :
    ∃ (S : Sylow 2 ↥N) (U : Subgroup X),
      U = (S : Subgroup ↥N).map N.subtype ∧
      U ≤ MulAction.stabilizer X x ∧
      (U.subgroupOf (MulAction.stabilizer X x)).Normal ∧
      IsPGroup 2 U ∧
      Nat.card U = (2 ^ (2 * a + 1)) ^ 2 ∧
      Nat.card (U ⊓ Subgroup.centralizer (U : Set X) : Subgroup X) = 2 ^ (2 * a + 1) ∧
      (∀ α β : Ω, α ≠ x → β ≠ x → ∃! r : U, (r : X) • α = β) := by
  classical
  letI : N.Normal := hN
  let q := 2 ^ (2 * a + 1)
  obtain ⟨ω, β, Q, T, ψ, P, hψT, hψQ, hψB⟩ :=
    exists_szPointAction (X := X) (Ω := Ω) h2 ha N hN e hΩ
  haveI : MulAction.IsPretransitive ↥N Ω :=
    MulAction.isPretransitive_of_is_two_pretransitive (h2 := P.isMultiplyPretransitive)
  obtain ⟨n, hn⟩ := MulAction.exists_smul_eq (↥N) ω x
  subst hn
  let Q' : Subgroup ↥N := Q.map (MulAut.conj n).toMonoidHom
  let T' : Subgroup ↥N := T.map (MulAut.conj n).toMonoidHom
  let P' : SuzukiPointAction ↥N Ω q (n • ω) (n • β) Q' T' := P.conj n
  obtain ⟨S, hS⟩ := P'.exists_sylow
  let U : Subgroup X := Q'.map N.subtype
  have hUeq : U = (S : Subgroup ↥N).map N.subtype := by
    rw [hS]
  have hQ'le : Q' ≤ MulAction.stabilizer ↥N (n • ω) := P'.le_stabilizer_left
  have hQ'2 : IsPGroup 2 Q' := by
    rw [← hS]
    exact S.isPGroup'
  have hUle : U ≤ MulAction.stabilizer X (n • ω) := by
    intro u hu
    rcases Subgroup.mem_map.mp hu with ⟨s, hs, rfl⟩
    change ((s : ↥N) : X) • (n • ω) = n • ω
    rw [← Subgroup.smul_def]
    exact hQ'le hs
  have hUnormX : MulAction.stabilizer X (n • ω) ≤ Subgroup.normalizer (U : Set X) := by
    have h := root_normal_in_pointStabilizer (N := N) (ω := n • ω) (Q := Q') hQ'2
      ⟨S, hS⟩ hQ'le P'.stabilizer_le_normalizer
    simpa [U] using h
  have hUnorm : (U.subgroupOf (MulAction.stabilizer X (n • ω))).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hUle).mpr hUnormX
  have hU2 : IsPGroup 2 U := by
    rw [hUeq]
    exact S.isPGroup'.map N.subtype
  have hUcard : Nat.card U = q ^ 2 := by
    rw [hUeq, Subgroup.card_map_of_injective (K := (S : Subgroup ↥N)) N.subtype_injective, hS]
    exact P'.card_U
  let e' : ↥N ≃* CFSG.Theory.Comparator.SzModel a :=
    e.trans (MulEquiv.subgroupCongr (CFSG.Models.benderSzModel_eq_sz a).symm)
  have hScenter : Nat.card (Subgroup.center (S : Subgroup ↥N)) = q := by
    have h := CFSG.StronglyEmbedded.BenderCentre.card_sylowCenter_sz (n := a) ha e' S
    rw [← CFSG.ComponentClassification.AschbacherToolkit.Bender.map_center_eq_sylowCenter
      (S : Subgroup ↥N)] at h
    rwa [Subgroup.card_map_of_injective (K := Subgroup.center (S : Subgroup ↥N))
      (S : Subgroup ↥N).subtype_injective] at h
  have hUcenter : Nat.card (Subgroup.center U) = q := by
    rw [hUeq, ← Subgroup.map_center_eq
      (Subgroup.equivMapOfInjective (S : Subgroup ↥N) N.subtype N.subtype_injective)]
    rw [Subgroup.card_map_of_injective
      (Subgroup.equivMapOfInjective (S : Subgroup ↥N) N.subtype N.subtype_injective).injective]
    exact hScenter
  have hcenter : Nat.card (U ⊓ Subgroup.centralizer (U : Set X) : Subgroup X) = q := by
    change Nat.card (CFSG.ComponentClassification.AschbacherToolkit.Bender.sylowCenter U) = q
    rw [← CFSG.ComponentClassification.AschbacherToolkit.Bender.map_center_eq_sylowCenter U,
      Subgroup.card_map_of_injective (K := Subgroup.center U) U.subtype_injective]
    exact hUcenter
  have hUreg : ∀ α β : Ω, α ≠ n • ω → β ≠ n • ω → ∃! r : U, (r : X) • α = β := by
    intro α β hα hβ
    obtain ⟨r, hr, huniq⟩ := P'.regular α β hα hβ
    refine ⟨⟨(r : ↥N), Subgroup.mem_map_of_mem N.subtype r.2⟩, ?_, ?_⟩
    · change ((r : ↥N) : X) • α = β
      exact hr
    · intro s hs
      rcases Subgroup.mem_map.mp s.2 with ⟨r', hr', hval⟩
      have hact : ((r' : ↥N) : X) • α = β := by
        have hs' : (s : X) • α = β := hs
        rw [← hval] at hs'
        exact hs'
      have hr'eq : r' = (r : ↥N) := congrArg Subtype.val (huniq ⟨r', hr'⟩ hact)
      apply Subtype.ext
      change (s : X) = ((r : ↥N) : X)
      rw [← hval, hr'eq]
      rfl
  exact ⟨S, U, hUeq, hUle, hUnorm, hU2, hUcard, hcenter, hUreg⟩


private theorem root_card_sz {X Ω : Type} [Group X] [Finite X]
    [Fintype Ω] [MulAction X Ω] [FaithfulSMul X Ω]
    (h2 : MulAction.IsMultiplyPretransitive X Ω 2) {a : ℕ} (ha : 1 ≤ a)
    (N : Subgroup X) (hN : N.Normal) (e : ↥N ≃* Sz a)
    (hΩ : Fintype.card Ω = 2 ^ (2 * (2 * a + 1)) + 1)
    {ω : Ω} {R : Subgroup X} (hR : R ≤ MulAction.stabilizer X ω)
    (hRn : (R.subgroupOf (MulAction.stabilizer X ω)).Normal) (hR2 : IsPGroup 2 R)
    (hreg : ∀ α β : Ω, α ≠ ω → β ≠ ω → ∃! r : R, (r : X) • α = β) :
    Nat.card R = (2 ^ (2 * a + 1)) ^ 2 ∧
    Nat.card (R ⊓ Subgroup.centralizer (R : Set X) : Subgroup X) = 2 ^ (2 * a + 1) := by
  classical
  let q := 2 ^ (2 * a + 1)
  have h : RankOneLocal X Ω N := rankOneLocal_sz h2 a ha N hN e hΩ
  have hcardΩ : 1 < Fintype.card Ω := by
    rw [hΩ]
    have h1 : 1 ≤ 2 ^ (2 * (2 * a + 1)) := Nat.one_le_two_pow
    omega
  obtain ⟨ω₁, hω₁⟩ := Fintype.exists_ne_of_one_lt_card hcardΩ ω
  have hRleN : R ≤ N := RankOneLocal.le_socle hN h ⟨ω₁, hω₁⟩ hR hRn hR2 hreg
  obtain ⟨S, U, hUeq, hUle, hUnorm, hU2, hUcard, hUcenter, hUreg⟩ :=
    root_data_sz h2 ha N hN e hΩ ω
  have hUleN : U ≤ N := by
    rw [hUeq]
    simpa using Subgroup.map_le_range N.subtype (S : Subgroup ↥N)
  have hdisj : ∀ y : Ω, y ≠ ω →
      U ⊓ (N ⊓ MulAction.stabilizer X ω ⊓ MulAction.stabilizer X y : Subgroup X) = ⊥ := by
    intro y hy
    have hTodd : Odd (Nat.card ↥(N ⊓ MulAction.stabilizer X ω ⊓ MulAction.stabilizer X y)) :=
      h.torus_odd ω y hy.symm
    have hcop : Nat.Coprime (Nat.card U)
        (Nat.card ↥(N ⊓ MulAction.stabilizer X ω ⊓ MulAction.stabilizer X y)) := by
      obtain ⟨k, hk⟩ := hU2.exists_card_eq
      rw [hk]
      exact (Nat.coprime_two_left.mpr hTodd).pow_left k
    exact (Subgroup.disjoint_of_coprime_natCard hcop).eq_bot
  have hRnormU : R ≤ Subgroup.normalizer (U : Set X) := by
    have hGnorm : MulAction.stabilizer X ω ≤ Subgroup.normalizer (U : Set X) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hUle).mp hUnorm
    exact le_trans hR hGnorm
  have hsup2 : IsPGroup 2 (R ⊔ U : Subgroup X) :=
    hR2.to_sup_of_normal_right' hU2 hRnormU
  have hsupN : (R ⊔ U : Subgroup X) ≤ N := sup_le hRleN hUleN
  have hsup2N : IsPGroup 2 ((R ⊔ U : Subgroup X).subgroupOf N) :=
    hsup2.of_equiv (Subgroup.subgroupOfEquivOfLe hsupN).symm
  have hSle : (S : Subgroup ↥N) ≤ (R ⊔ U : Subgroup X).subgroupOf N := by
    intro s hs
    rw [Subgroup.mem_subgroupOf]
    have hmemU : N.subtype s ∈ U := by
      rw [hUeq]
      exact Subgroup.mem_map_of_mem N.subtype hs
    exact Subgroup.mem_sup_right hmemU
  have hSeq : (R ⊔ U : Subgroup X).subgroupOf N = (S : Subgroup ↥N) :=
    S.is_maximal' hsup2N hSle
  have hRleU : R ≤ U := by
    intro r hr
    have hrN : (r : X) ∈ N := hRleN hr
    have hmem : (⟨(r : X), hrN⟩ : ↥N) ∈ (R ⊔ U : Subgroup X).subgroupOf N := by
      rw [Subgroup.mem_subgroupOf]
      exact Subgroup.mem_sup_left hr
    rw [hSeq] at hmem
    have hmem' : N.subtype ⟨(r : X), hrN⟩ ∈ (S : Subgroup ↥N).map N.subtype :=
      Subgroup.mem_map_of_mem N.subtype hmem
    rw [← hUeq] at hmem'
    simpa using hmem'
  have hRU : R = U := by
    refine le_antisymm hRleU ?_
    intro u hu
    obtain ⟨y, hy⟩ := Fintype.exists_ne_of_one_lt_card hcardΩ ω
    have huy_ne : (u : X) • y ≠ ω := by
      intro h1
      have huω : (u : X) • ω = ω := hUle hu
      have hyω : y = ω := by
        calc y = (u : X)⁻¹ • ((u : X) • y) := (inv_smul_smul (u : X) y).symm
          _ = (u : X)⁻¹ • ω := by rw [h1]
          _ = ω := by
              conv_lhs => rw [← huω]
              exact inv_smul_smul (u : X) ω
      exact hy hyω
    obtain ⟨r, hr, -⟩ := hreg y ((u : X) • y) hy huy_ne
    have hfix : ((u : X)⁻¹ * (r : X)) • y = y := by
      rw [mul_smul, hr, inv_smul_smul]
    have huN : (u : X) ∈ N := hUleN hu
    have hrN : (r : X) ∈ N := hRleN r.2
    have hmemN : (u : X)⁻¹ * (r : X) ∈ N := N.mul_mem (N.inv_mem huN) hrN
    have huω : (u : X) • ω = ω := hUle hu
    have hrω : (r : X) • ω = ω := hR r.2
    have hmemG : (u : X)⁻¹ * (r : X) ∈ MulAction.stabilizer X ω := by
      rw [MulAction.mem_stabilizer_iff, mul_smul, hrω]
      conv_lhs => rw [← huω]
      exact inv_smul_smul (u : X) ω
    have hmemT : (u : X)⁻¹ * (r : X) ∈
        N ⊓ MulAction.stabilizer X ω ⊓ MulAction.stabilizer X y :=
      ⟨⟨hmemN, hmemG⟩, hfix⟩
    have hmemU : (u : X)⁻¹ * (r : X) ∈ U :=
      U.mul_mem (U.inv_mem hu) (hRleU r.2)
    have hbot : (u : X)⁻¹ * (r : X) ∈ (⊥ : Subgroup X) := by
      rw [← hdisj y hy]
      exact ⟨hmemU, hmemT⟩
    rw [Subgroup.mem_bot] at hbot
    have hEq : (r : X) = (u : X) := by
      calc (r : X) = ((u : X) * (u : X)⁻¹) * (r : X) := by group
        _ = (u : X) * ((u : X)⁻¹ * (r : X)) := by group
        _ = (u : X) * 1 := by rw [hbot]
        _ = (u : X) := mul_one _
    exact hEq ▸ r.2
  refine ⟨?_, ?_⟩
  · rw [hRU]
    simpa [q] using hUcard
  · rw [hRU]
    simpa [q] using hUcenter


theorem rankOneCenter_sz {X Ω : Type} [Group X] [Finite X]
    [Fintype Ω] [MulAction X Ω] [FaithfulSMul X Ω]
    (h2 : MulAction.IsMultiplyPretransitive X Ω 2) (a : ℕ) (ha : 1 ≤ a)
    (N : Subgroup X) (hN : N.Normal) (e : ↥N ≃* Sz a)
    (hΩ : Fintype.card Ω = 2 ^ (2 * (2 * a + 1)) + 1) :
    RankOneCenter X Ω N 1 := by
  classical
  have h : RankOneLocal X Ω N := rankOneLocal_sz h2 a ha N hN e hΩ
  have hZ : RankOneZassenhaus X Ω N := rankOneZassenhaus_sz h2 a ha N hN e hΩ
  refine RankOneLocal.rankOneCenter_of_zassenhaus hN h hZ ?_
  intro ω ω' hne R hR hRn hR2 hreg
  have hres := root_card_sz h2 ha N hN e hΩ hR hRn hR2 hreg
  obtain ⟨ω₀, β₀, Q, T, ψ, P, hψT, hψQ, hψB⟩ :=
    exists_szPointAction (X := X) (Ω := Ω) h2 ha N hN e hΩ
  obtain ⟨n, -, -, hTxy⟩ := exists_conj_torus P hne
  have hfield : N ⊓ MulAction.stabilizer X ω ⊓ MulAction.stabilizer X ω' =
      (T.map (MulAut.conj n).toMonoidHom).map N.subtype :=
    inf_stabilizer_eq_map_subtype hTxy
  have hTcard : Nat.card ↥(N ⊓ MulAction.stabilizer X ω ⊓ MulAction.stabilizer X ω') =
      2 ^ (2 * a + 1) - 1 := by
    rw [hfield, Subgroup.card_map_of_injective (K := T.map (MulAut.conj n).toMonoidHom)
      N.subtype_injective, Subgroup.card_map_of_injective (K := T) (MulAut.conj n).injective]
    exact P.card_T
  rw [hres.2, hTcard]
  have hpos : 0 < 2 ^ (2 * a + 1) := pow_pos (by norm_num : (0 : ℕ) < 2) (2 * a + 1)
  omega

theorem rankOneNonabelian_sz {X Ω : Type} [Group X] [Finite X]
    [Fintype Ω] [MulAction X Ω] [FaithfulSMul X Ω]
    (h2 : MulAction.IsMultiplyPretransitive X Ω 2) (a : ℕ) (ha : 1 ≤ a)
    (N : Subgroup X) (hN : N.Normal) (e : ↥N ≃* Sz a)
    (hΩ : Fintype.card Ω = 2 ^ (2 * (2 * a + 1)) + 1) :
    RankOneNonabelian X Ω := by
  classical
  refine ⟨?not_comm⟩
  intro ω R hR hRn hR2 hreg
  have hres := root_card_sz h2 ha N hN e hΩ hR hRn hR2 hreg
  by_contra hcomm
  push Not at hcomm
  have hle : R ≤ Subgroup.centralizer (R : Set X) := by
    intro r hr
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    exact (hcomm r hr s hs).symm
  have hcard : Nat.card R =
      Nat.card (R ⊓ Subgroup.centralizer (R : Set X) : Subgroup X) := by
    rw [inf_eq_left.mpr hle]
  rw [hres.1, hres.2] at hcard
  have hq1 : 1 < 2 ^ (2 * a + 1) := one_lt_pow' (by norm_num) (by omega)
  have hlt : 2 ^ (2 * a + 1) < (2 ^ (2 * a + 1)) ^ 2 := by
    have := Nat.mul_lt_mul_of_pos_left hq1 (pow_pos (by norm_num : (0 : ℕ) < 2) (2 * a + 1))
    simpa [pow_two, mul_comm, mul_left_comm, mul_assoc] using this
  exact (ne_of_gt hlt) hcard

end CFSG.Quasithin.Stroth.WeissDelta

end
