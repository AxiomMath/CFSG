module

public import CFSG.RankThree.GF2n.Stroth80.Sec7TailFlagType

public section

namespace CFSG.RankThree.GF2n.Stroth80

open Subgroup CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank

theorem exists_noncomm_of_perfect {A : Type*} [Group A] [Nontrivial A] (h : Group.IsPerfect A) :
    ∃ a b : A, a * b ≠ b * a := by
  by_contra hcon
  push Not at hcon
  obtain ⟨x, hx⟩ := exists_ne (1 : A)
  have h1 : commutator A = ⊥ := by
    change (⁅(⊤ : Subgroup A), (⊤ : Subgroup A)⁆ : Subgroup A) = ⊥
    rw [eq_bot_iff, Subgroup.commutator_le]
    intro a _ b _
    exact (commutatorElement_eq_one_iff_mul_comm.2 (hcon a b)) ▸ Subgroup.one_mem _
  rw [h.commutator_eq_top] at h1
  exact hx (Subgroup.mem_bot.1 (h1 ▸ Subgroup.mem_top x))

theorem statedProj_statedSL_four_simple_nonabelian (K : Type) [Field K] [Finite K] :
    IsSimpleGroup (StatedProj (StatedSL 4 K)) ∧
      ∃ a b : StatedProj (StatedSL 4 K), a * b ≠ b * a := by
  refine ⟨CFSG.Open.StatedAPI.isSimpleGroup_statedProj_statedSL K (d := 4) (by norm_num)
    (Or.inl (by norm_num)) (Or.inl (by norm_num)), ?_⟩
  haveI := CFSG.LinearGroups.linear_projective_nontrivial (K := K) (n := 4) (by norm_num)
  have hperf := CFSG.LinearGroups.linear_projective_perfect (K := K) (n := 4) (by norm_num)
    (Or.inl (by norm_num))
  obtain ⟨a, b, hab⟩ := exists_noncomm_of_perfect hperf
  let e := projectiveSpecialLinearGroupEquivStatedProj 4 K
  exact ⟨e a, e b, fun h => hab (e.injective (by simpa using h))⟩

theorem map_inSubgroup_pCore_two_equiv {X X' : Type*} [Group X] [Group X'] (e : X ≃* X')
    (H : Subgroup X) :
    (inSubgroup (pCore 2) H).map e.toMonoidHom = inSubgroup (pCore 2) (H.map e.toMonoidHom) := by
  have hH : (pCore 2 ↥H).map (Subgroup.equivMapOfInjective H e.toMonoidHom e.injective).toMonoidHom
      = pCore 2 ↥(H.map e.toMonoidHom) :=
    pCore_map_iso 2 (Subgroup.equivMapOfInjective H e.toMonoidHom e.injective)
  unfold inSubgroup
  rw [Subgroup.map_map, ← hH, Subgroup.map_map]
  rfl

theorem flag_type_of_radical_equiv
    (hRad : RadicalTwoSubgroupLinearStatement) (hArtin : ArtinLinearOrdersStatement)
    {X : Type} [Group X] [Finite X]
    (r : ℕ) (K : Type) [Field K] [Finite K] (hr : 3 ≤ r)
    (hK : ∃ f : ℕ, 1 ≤ f ∧ Nat.card K = 2 ^ f) (e : X ≃* StatedProj (StatedSL r K))
    (q : ℕ) (hq4 : 4 ≤ q) (K' : Type) [Field K'] [Finite K'] (hK' : Nat.card K' = q)
    (hq2 : ∃ g : ℕ, q = 2 ^ g)
    (U P : Subgroup X) (hU1 : U ≠ ⊥) (hU2 : IsPGroup 2 U)
    (hrad : inSubgroup (pCore 2) (Subgroup.normalizer (U : Set X)) = U)
    (hZ : Nat.card ↥(Subgroup.center ↥U) = q) (hcard : Nat.card U = q ^ 9)
    (hUP : U ≤ P) (hPn : P ≤ Subgroup.normalizer (U : Set X))
    (hPN : ∀ k ∈ Subgroup.normalizer (U : Set X), k ∈ Subgroup.normalizer (P : Set X))
    (hPU : ∃ _ : (U.subgroupOf P).Normal,
      Nonempty ((↥P ⧸ U.subgroupOf P) ≃* StatedProj (StatedSL 4 K'))) :
    r = 6 ∧ Nat.card K = q := by
  classical
  obtain ⟨hnUP, ⟨ePU⟩⟩ := hPU
  let U' : Subgroup (StatedProj (StatedSL r K)) := U.map e.toMonoidHom
  let P' : Subgroup (StatedProj (StatedSL r K)) := P.map e.toMonoidHom
  have hN' : Subgroup.normalizer (U' : Set (StatedProj (StatedSL r K))) =
      (Subgroup.normalizer (U : Set X)).map e.toMonoidHom :=
    (Subgroup.map_equiv_normalizer_eq U e).symm
  have hrad' : inSubgroup (pCore 2) (Subgroup.normalizer (U' : Set (StatedProj (StatedSL r K))))
      = U' := by
    rw [hN', ← map_inSubgroup_pCore_two_equiv, hrad]
  have hU1' : U' ≠ ⊥ := fun h => hU1 ((Subgroup.map_eq_bot_iff_of_injective U e.injective).mp h)
  have hU2' : IsPGroup 2 U' := hU2.map e.toMonoidHom
  have eU : ↥U ≃* ↥U' := Subgroup.equivMapOfInjective U e.toMonoidHom e.injective
  have hZ' : Nat.card ↥(Subgroup.center ↥U') = q := by
    rw [← hZ]
    exact (Nat.card_congr (Subgroup.centerCongr eU).toEquiv).symm
  have hcard' : Nat.card U' = q ^ 9 := by
    rw [← hcard]
    exact (Nat.card_congr eU.toEquiv).symm
  have hP'N : P' ≤ Subgroup.normalizer (U' : Set (StatedProj (StatedSL r K))) := by
    rw [hN']
    exact Subgroup.map_mono hPn
  have hPN' : ∀ k ∈ Subgroup.normalizer (U' : Set (StatedProj (StatedSL r K))),
      k ∈ Subgroup.normalizer (P' : Set (StatedProj (StatedSL r K))) := by
    intro k hk
    rw [hN'] at hk
    obtain ⟨k0, hk0, rfl⟩ := hk
    rw [← Subgroup.map_equiv_normalizer_eq P e]
    exact ⟨k0, hPN k0 hk0, rfl⟩
  let N1 : Subgroup (StatedProj (StatedSL r K)) :=
    Subgroup.normalizer (U' : Set (StatedProj (StatedSL r K)))
  let eP : ↥P ≃* ↥P' := Subgroup.equivMapOfInjective P e.toMonoidHom e.injective
  let ψ : ↥P →* (↥N1 ⧸ U'.subgroupOf N1) :=
    (QuotientGroup.mk' (U'.subgroupOf N1)).comp ((Subgroup.inclusion hP'N).comp eP.toMonoidHom)
  have hψmk : ∀ p : ↥P, ψ p = QuotientGroup.mk (⟨e p, hP'N ⟨p, p.2, rfl⟩⟩ : ↥N1) := fun p => rfl
  have hker : ψ.ker = U.subgroupOf P := by
    ext p
    rw [MonoidHom.mem_ker, hψmk, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf,
      Subgroup.mem_subgroupOf]
    constructor
    · rintro ⟨u, hu, hue⟩
      have : u = (p : X) := e.injective hue
      rw [← this]
      exact hu
    · intro hp
      exact ⟨p, hp, rfl⟩
  haveI hnUP' : (U.subgroupOf P).Normal := hnUP
  let S : Subgroup (↥N1 ⧸ U'.subgroupOf N1) := ψ.range
  have hSnormal : S.Normal := by
    refine ⟨fun s hs g => ?_⟩
    obtain ⟨p, rfl⟩ := hs
    obtain ⟨g0, rfl⟩ := QuotientGroup.mk_surjective g
    have hmem : (g0 : StatedProj (StatedSL r K)) * e p * (g0 : StatedProj (StatedSL r K))⁻¹
        ∈ P' := by
      have := (Subgroup.mem_normalizer_iff.mp (hPN' _ g0.2) (e p)).mp ⟨p, p.2, rfl⟩
      exact this
    obtain ⟨p2, hp2, hp2e⟩ := hmem
    refine ⟨⟨p2, hp2⟩, ?_⟩
    simp only [hψmk]
    rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    apply congrArg QuotientGroup.mk
    apply Subtype.ext
    simpa using hp2e
  let eS : ↥P ⧸ U.subgroupOf P ≃* ↥S :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans (QuotientGroup.quotientKerEquivRange ψ)
  obtain ⟨hsimp4, hnab4⟩ := statedProj_statedSL_four_simple_nonabelian K'
  let eS' : ↥S ≃* StatedProj (StatedSL 4 K') := eS.symm.trans ePU
  haveI : IsSimpleGroup (StatedProj (StatedSL 4 K')) := hsimp4
  haveI : IsSimpleGroup ↥S := eS'.isSimpleGroup
  have hnabS : ∃ a b : ↥S, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnab4
    exact ⟨eS'.symm a, eS'.symm b, fun h => hab (eS'.symm.injective (by simpa using h))⟩
  obtain ⟨hq, -⟩ := CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnabS
  exact flag_type_of_radical hRad hArtin r K hr hK q hq4 K' hK' hq2 U' hU1' hU2' hrad' hZ' hcard'
    S hSnormal hq ⟨⊥, bot_le, inferInstance, ⟨(QuotientGroup.quotientBot).trans eS'⟩⟩

end CFSG.RankThree.GF2n.Stroth80

