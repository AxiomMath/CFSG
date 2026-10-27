module

public import CFSG.Sporadic.Co1.Cover.Iota
public import CFSG.Sporadic.Co1.Cover.Rels
public import CFSG.Sporadic.Co1.Module.TwoB
public import CFSG.Monster.Schur.Restriction

public section

namespace CFSG.Sporadic.Co1.Cover

open scoped commutatorElement

open CFSG.Sporadic.SmallF2 CFSG.Sporadic.Co1.CoverNative CFSG.Sporadic.Co1.Module
  CFSG.Monster.Schur CFSG.Monster.Schur.M24 CFSG.Blueprint Matrix SemidirectProduct

attribute [local irreducible] eps0 ga gb regCov rrCov epsRows

@[expose] def x0vec : Fin 11 → ZMod 2 := toVecD 11 x0mask

@[expose] noncomputable def t0 :
    NativeSporadic.Co1 :=
  epsHom (Multiplicative.ofAdd x0vec) * ga

theorem matHom_t0 :
    matHom t0 = rowsMatrix 24 t0Rows := by
  show matHom (epsHom (Multiplicative.ofAdd (toVecD 11 x0mask)) * ga) = _
  rw [map_mul, matHom_epsHom_toVecD, matHom_ga, ← rowsMatrix_mulRows]
  rfl

theorem orderOf_t0 :
    orderOf t0 = 2 :=
  orderOf_eq_of_orderIs matHom_t0 (by norm_num) cov_t0_order

theorem t0_mul_self :
    t0 * t0 = 1 := by
  have h := pow_orderOf_eq_one t0
  rw [orderOf_t0, pow_two] at h
  exact h

theorem isCo1TwoB_t0 :
    CFSG.Monster.GMS.IsCo1TwoB t0 := by
  obtain ⟨c1, c2⟩ := countsOK_facts cov_t0_counts
  have hfix : {v : Vec24 | co1Act t0 v = v} = {v | rowsMatrix 24 t0Rows *ᵥ v = v} := by
    ext v
    simp only [Set.mem_ofPred_eq, co1Act_eq_mulVec, matHom_t0]
  have hfixq : {v : Vec24 | co1Act t0 v = v ∧ q₀ v = 1} =
      {v | rowsMatrix 24 t0Rows *ᵥ v = v ∧ q₀ v = 1} := by
    ext v
    simp only [Set.mem_ofPred_eq, co1Act_eq_mulVec, matHom_t0]
  have h12 : {v : Vec24 | co1Act t0 v = v}.ncard = 2 ^ 12 := by
    rw [hfix, c1]
    norm_num
  have h0 : {v : Vec24 | co1Act t0 v = v ∧ q₀ v = 1}.ncard = 0 := by
    rw [hfixq, c2]
  refine ⟨orderOf_t0, h12, fun v hv => ?_⟩
  by_contra h
  have h1 : q₀ v = 1 := by
    rcases zmod2_cases (q₀ v) with h0' | h1'
    · exact absurd h0' h
    · exact h1'
  have hmem : v ∈ {v : Vec24 | co1Act t0 v = v ∧ q₀ v = 1} := ⟨hv, h1⟩
  rw [Set.ncard_eq_zero (Set.toFinite _)] at h0
  rw [h0] at hmem
  exact hmem

theorem closure_gen_pair :
    Subgroup.closure ({gen 0, gen 1} : Set PM24) = ⊤ := by
  have h : Set.range gen = ({gen 0, gen 1} : Set PM24) := by
    ext x
    simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff, Fin.exists_fin_two]
    tauto
  rw [← h]
  exact closure_gen

theorem gen_not_comm :
    gen 0 * gen 1 ≠ gen 1 * gen 0 := by
  intro h
  apply ga_gb_not_comm
  have := congrArg iota h
  rwa [map_mul, map_mul, iota_gen0, iota_gen1] at this

theorem perfect_PM24 :
    Group.IsPerfect PM24 := by
  have := isSimpleGroup_PM24
  rw [Group.isPerfect_def]
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator PM24) with h | h
  · exfalso
    have hmem : ⁅gen 0, gen 1⁆ ∈ commutator PM24 :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
    rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
    exact gen_not_comm hmem
  · exact h

theorem co1DoubleCoverTwoB :
    CFSG.Monster.GMS.Co1DoubleCoverTwoB := by
  intro C _ π ζ hπ hker hζc hζo ⟨c, hc2, hc⟩
  have hζ2 : ζ * ζ = 1 := by
    rw [← pow_two, ← hζo]
    exact pow_orderOf_eq_one ζ
  have hζne : ζ ≠ 1 := fun h => by
    rw [h, orderOf_one] at hζo
    omega
  have hζcomm : ∀ x : C, ζ * x = x * ζ := fun x => (Subgroup.mem_center_iff.1 hζc x).symm
  have hζker : ζ ∈ π.ker := by
    rw [hker]
    exact Subgroup.mem_zpowers ζ
  have hker2 : Nat.card π.ker = 2 := by
    rw [hker, Nat.card_zpowers, hζo]
  have : Finite NativeSporadic.Co1 := finite_co1
  have : Finite C := finite_of_card_ker_ne_zero π (by rw [hker2]; norm_num)
  obtain ⟨g, hg⟩ := isConj_iff.1 (CFSG.Monster.GMS.isCo1TwoB_isConj hc isCo1TwoB_t0)
  obtain ⟨ĝ, hĝ⟩ := hπ g
  set c₁ : C := ĝ * c * ĝ⁻¹ with hc₁
  have hc₁2 : c₁ * c₁ = 1 := by
    rw [hc₁]
    calc ĝ * c * ĝ⁻¹ * (ĝ * c * ĝ⁻¹) = ĝ * (c * c) * ĝ⁻¹ := by group
      _ = 1 := by rw [hc2]; group
  have hπc₁ : π c₁ = t0 := by
    rw [hc₁, map_mul, map_mul, map_inv, hĝ]
    exact hg
  let X : Subgroup (SM24 × C) :=
    (theta.comp (MonoidHom.fst SM24 C)).eqLocus (π.comp (MonoidHom.snd SM24 C))
  let ψ : X →* SM24 := (MonoidHom.fst SM24 C).comp X.subtype
  have hψ : Function.Surjective ψ := by
    intro s
    obtain ⟨y, hy⟩ := hπ (theta s)
    exact ⟨⟨(s, y), hy.symm⟩, rfl⟩
  let z : X := ⟨(1, ζ), by
    show theta 1 = π ζ
    rw [map_one, MonoidHom.mem_ker.1 hζker]⟩
  have hzc : ∀ x : X, z * x = x * z := fun x =>
    Subtype.ext (Prod.ext (by simp [z]) (hζcomm x.1.2))
  have hz2 : z * z = 1 := Subtype.ext (Prod.ext (one_mul 1) hζ2)
  have hzne : z ≠ 1 := fun h => hζne (congrArg (fun x : X => x.1.2) h)
  have hkerψ : ψ.ker = Subgroup.zpowers z := by
    ext x
    constructor
    · intro hx
      have hx1 : x.1.1 = 1 := hx
      have hmem : x.1.2 ∈ π.ker := by
        rw [MonoidHom.mem_ker, ← (show theta x.1.1 = π x.1.2 from x.2), hx1, map_one]
      rw [hker] at hmem
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmem
      refine Subgroup.mem_zpowers_iff.2 ⟨k, ?_⟩
      apply Subtype.ext
      apply Prod.ext
      · simp [z, hx1]
      · simp [z, hk]
    · intro hx
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
      show ((z ^ k : X) : SM24 × C).1 = 1
      simp [z]
  let t0S : SM24 := inl (Multiplicative.ofAdd x0vec) * inr (gen 0)
  have htheta_t0S : theta t0S = t0 := by
    rw [map_mul, theta_inl, theta_inr, iota_gen0]
    rfl
  let x₁ : X := ⟨(t0S, c₁), by
    show theta t0S = π c₁
    rw [htheta_t0S, hπc₁]⟩
  have ht0S2 : t0S * t0S = 1 :=
    theta_injective (by rw [map_mul, htheta_t0S, t0_mul_self, map_one])
  have hx₁ : x₁ * x₁ = 1 := Subtype.ext (Prod.ext ht0S2 hc₁2)
  have := perfect_PM24
  obtain ⟨τ, hτ⟩ := exists_hom_section rho ψ noPerfectDoubleCover_M24 (gen 0) (gen 1)
    closure_gen_pair Amat Bmat rho_gen0 rho_gen1 hC_proof hl_proof x0vec
    (by rw [rho_gen0]; exact Amat_x0) gen_sq
    (fun l hl h0 => hfox_proof (gen 0) (gen 1) rho Amat Bmat rho_gen0 rho_gen1 hrel_M24 rfl rfl l
      hl h0)
    hψ hzc hz2 hzne hkerψ x₁ hx₁ rfl
  let τ' : SM24 →* C := (MonoidHom.snd SM24 C).comp (X.subtype.comp τ)
  have hτ' : ∀ s, π (τ' s) = theta s := by
    intro s
    have h1 : theta (τ s).1.1 = π (τ s).1.2 := (τ s).2
    have h2 : (τ s).1.1 = s := hτ s
    show π (τ s).1.2 = theta s
    rw [← h1, h2]
  obtain ⟨N, hNdef⟩ : ∃ N : Subgroup C, N = Subgroup.zpowers ζ := ⟨_, rfl⟩
  have hNker : N = π.ker := hNdef.trans hker.symm
  have hmemN : ∀ y : C, y ∈ N ↔ π y = 1 := fun y => by rw [hNker, MonoidHom.mem_ker]
  have hNnormal : N.Normal := hNker ▸ π.normal_ker
  have hNcomm : IsMulCommutative N := by
    rw [hNdef]
    infer_instance
  let H : Subgroup C := theta.range.comap π
  let K : Subgroup C := τ'.range
  have hNK : N ⊓ K = ⊥ := by
    rw [eq_bot_iff]
    rintro y ⟨hyN, s, rfl⟩
    have h1 : π (τ' s) = 1 := (hmemN _).1 hyN
    rw [hτ'] at h1
    have hs : s = 1 := theta_injective (h1.trans (map_one theta).symm)
    rw [hs, map_one]
    exact Subgroup.one_mem _
  have hsup : N ⊔ K = H := by
    apply le_antisymm
    · apply sup_le
      · intro y hy
        show π y ∈ theta.range
        rw [(hmemN y).1 hy]
        exact Subgroup.one_mem _
      · rintro _ ⟨s, rfl⟩
        show π (τ' s) ∈ theta.range
        rw [hτ']
        exact ⟨s, rfl⟩
    · intro y hy
      obtain ⟨s, hs⟩ := (show π y ∈ theta.range from hy)
      have hyk : y * (τ' s)⁻¹ ∈ N := by
        rw [hmemN, map_mul, map_inv, hτ', hs, mul_inv_cancel]
      have e : y = y * (τ' s)⁻¹ * τ' s := by group
      rw [e]
      exact Subgroup.mul_mem_sup hyk (show τ' s ∈ K from ⟨s, rfl⟩)
  have hcop : Nat.Coprime H.index (Nat.card N) := by
    have h1 : H.index = theta.range.index := Subgroup.index_comap_of_surjective theta.range hπ
    rw [h1, theta_index, hNdef, Nat.card_zpowers, hζo]
    norm_num
  obtain ⟨D, -, hND, hDsup⟩ :=
    CFSG.GroupTheory.abelian_normal_coprime_index_complement_lifting N H K hcop hNK hsup
  refine ⟨D, ?_, ?_⟩
  · intro k k' hkk'
    have h1 : (k : C)⁻¹ * k' ∈ N ⊓ D := by
      refine ⟨(hmemN _).2 ?_, D.mul_mem (D.inv_mem k.2) k'.2⟩
      rw [map_mul, map_inv]
      exact inv_mul_eq_one.2 hkk'
    rw [hND, Subgroup.mem_bot] at h1
    exact Subtype.ext (inv_mul_eq_one.1 h1)
  · intro y
    obtain ⟨y, rfl⟩ := hπ y
    have hy : y ∈ N ⊔ D := by rw [hDsup]; exact Subgroup.mem_top y
    have hy' : y ∈ (↑(N ⊔ D) : Set C) := hy
    rw [Subgroup.normal_mul] at hy'
    obtain ⟨n, hn, d, hd, rfl⟩ := Set.mem_mul.1 hy'
    refine ⟨⟨d, hd⟩, ?_⟩
    show π d = π (n * d)
    rw [map_mul, (hmemN n).1 hn, one_mul]

end CFSG.Sporadic.Co1.Cover
