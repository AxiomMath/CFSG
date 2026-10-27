module

public import CFSG.Milestones.ASVolI.F45.Lie
public import CFSG.Quasithin.Vol2.GoldschmidtF431UnPre
public import CFSG.Quasithin.Vol2.GoldschmidtF431Un5Pre
public import CFSG.LieType.Universal.Unitary.Comparison
public import CFSG.ClassicalGroups.Unitary.Simple
public import CFSG.LieType.TitsSimplicity.Core
public import CFSG.LieType.Steinberg.CentralExt.BorelIndex
public import CFSG.LieType.Steinberg.CentralExt.UnitaryRootGroups
public import CFSG.GH74.GLS.SP.Transfer
public import CFSG.LieType.Universal.Unitary.Extras.Torus
import all CFSG.Milestones.ASVolI.F4

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion
  CFSG.ASVolI.ChF

section Generic

variable {X Y : Type} [Group X] [Group Y]

theorem burnsideF45_isSylowOf_map_surj {p : ℕ} (π : X →* Y) (hπ : Function.Surjective π)
    {U : Subgroup X} (hU : ChF.IsSylowOf p U ⊤) : ChF.IsSylowOf p (U.map π) ⊤ := by
  obtain ⟨-, hpU, hi⟩ := hU
  refine ⟨le_top, hpU.map π, ?_⟩
  rw [Subgroup.relIndex_top_right] at hi ⊢
  rw [Subgroup.index_map, MonoidHom.range_eq_top.2 hπ, Subgroup.index_top, mul_one]
  exact fun h => hi (h.trans (Subgroup.index_dvd_of_le le_sup_left))

end Generic

section Projection

open CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.Quasithin.H13.F431.Un

variable {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p]
  (hF : Nat.card F = (p ^ f) ^ 2)

@[expose] noncomputable def burnsideF45U_proj (n : ℕ) :
    SU (unitaryInvolution F p f) n →* StatedProj (StatedSU n (p ^ f) F) :=
  (QuotientGroup.mk' _).comp (equivStatedSU hF n).toMonoidHom

theorem burnsideF45U_proj_surjective (n : ℕ) : Function.Surjective (burnsideF45U_proj hF n) :=
  (QuotientGroup.mk'_surjective _).comp (equivStatedSU hF n).surjective

theorem burnsideF45U_ker_proj_le_center (n : ℕ) :
    (burnsideF45U_proj hF n).ker ≤ Subgroup.center (SU (unitaryInvolution F p f) n) := by
  intro x hx
  have hx' : equivStatedSU hF n x ∈
      (StatedScalars (Fin n) F).subgroupOf (StatedSU n (p ^ f) F) :=
    (QuotientGroup.eq_one_iff _).mp (MonoidHom.mem_ker.mp hx)
  have hc : ((equivStatedSU hF n x : StatedSU n (p ^ f) F) : GL (Fin n) F) ∈
      Subgroup.center (GL (Fin n) F) := by
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
    exact Subgroup.mem_subgroupOf.mp hx'
  rw [Subgroup.mem_center_iff]
  intro g
  apply (equivStatedSU hF n).injective
  apply Subtype.ext
  rw [map_mul, map_mul, Subgroup.coe_mul, Subgroup.coe_mul]
  exact Subgroup.mem_center_iff.mp hc _

include hF in
theorem burnsideF45U_center_le_unT {n : ℕ} (hn : 2 ≤ n) :
    Subgroup.center (SU (unitaryInvolution F p f) n) ≤ unT (F := F) (p := p) (f := f) n := by
  obtain ⟨ζ, hζ⟩ := exists_traceZero_ne_zero hF
  rw [CFSG.LieType.TitsSimplicity.center_eq_normalCore_borel (D := rootDatum hF n)
    (isCTGroupDatum hF n hn ζ hζ) (steinbergExtras hF n hn ζ hζ)
    (CFSG.LieType.Steinberg.CentralExt.SUBruhat.bruhatExtras hF hn ζ hζ)]
  exact CFSG.LieType.TitsSimplicity.normalCore_borel_le_iSup (D := rootDatum hF n)
    (isCTGroupDatum hF n hn ζ hζ)
    (CFSG.LieType.Steinberg.CentralExt.SUBruhat.bruhatExtras hF hn ζ hζ)

theorem burnsideF45U_ker_le {n : ℕ} (hn : 2 ≤ n) (ζ : traceZero (unitaryInvolution F p f))
    (hζ : (ζ : F) ≠ 0) : (burnsideF45U_proj hF n).ker ≤ unB hF n ⊓ unN hF n ζ := by
  have h : unB hF n ⊓ unN hF n ζ = unT (F := F) (p := p) (f := f) n :=
    CFSG.LieType.Steinberg.borel_inf_weylN (D := rootDatum hF n) (isCTGroupDatum hF n hn ζ hζ)
      (steinbergExtras hF n hn ζ hζ)
  rw [h]
  exact (burnsideF45U_ker_proj_le_center hF n).trans (burnsideF45U_center_le_unT hF hn)

theorem burnsideF45U_unU_inf_ker {n : ℕ} (hn : 2 ≤ n) :
    unU hF n ⊓ (burnsideF45U_proj hF n).ker = ⊥ := by
  obtain ⟨ζ, hζ⟩ := exists_traceZero_ne_zero hF
  rw [eq_bot_iff]
  intro x hx
  have hT : x ∈ unT (F := F) (p := p) (f := f) n :=
    burnsideF45U_center_le_unT hF hn (burnsideF45U_ker_proj_le_center hF n hx.2)
  have h0 := (steinbergExtras hF n hn ζ hζ).torus_inf_posPart
  have h : x ∈ (⨆ i, levelTorus (unitaryInvolution F p f) i) ⊓
      ⨆ γ ∈ {γ | γ ∈ (rootDatum hF n).roots ∧ 0 < CFSG.LieType.Steinberg.ht γ},
        (rootDatum hF n).rootGroup γ :=
    ⟨hT, hx.1⟩
  exact Subgroup.mem_bot.1 (h0.le h)

end Projection

section Sylow

open CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.Quasithin.H13.F431.Un Matrix

variable {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p]

theorem burnsideF45U_exists_diagonal_of_mem_unT {n : ℕ} {t : SU (unitaryInvolution F p f) n}
    (ht : t ∈ unT (F := F) (p := p) (f := f) n) :
    ∃ d : Fin n → F, SUExtras.mat (unitaryInvolution F p f) n t = diagonal d :=
  Subgroup.iSup_induction (C := fun y : SU (unitaryInvolution F p f) n =>
    ∃ d : Fin n → F, SUExtras.mat (unitaryInvolution F p f) n y = diagonal d)
    (fun i => levelTorus (unitaryInvolution F p f) i) ht
    (fun _ _ hy => SUExtras.exists_diagonal_of_mem_levelTorus hy)
    ⟨1, by rw [map_one]; exact diagonal_one.symm⟩ fun y z ⟨d, hd⟩ ⟨d', hd'⟩ =>
      ⟨d * d', by rw [map_mul, hd, hd', diagonal_mul_diagonal]; rfl⟩

theorem burnsideF45U_pow_card_sub_one_unT {n : ℕ} {t : SU (unitaryInvolution F p f) n}
    (ht : t ∈ unT (F := F) (p := p) (f := f) n) : t ^ (Nat.card F - 1) = 1 := by
  obtain ⟨d, hd⟩ := burnsideF45U_exists_diagonal_of_mem_unT ht
  have hdet : ∏ i, d i = 1 := by
    have h := t.2.1
    have h2 : ((t : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = diagonal d := hd
    rw [h2, det_diagonal] at h
    exact h
  have hne : ∀ i, d i ≠ 0 := fun i h0 => by
    have : ∏ i, d i = 0 := Finset.prod_eq_zero (Finset.mem_univ i) h0
    rw [hdet] at this
    exact one_ne_zero this
  have : Fintype F := Fintype.ofFinite F
  apply SUExtras.mat_injective
  rw [map_pow, hd, diagonal_pow, map_one]
  have hc : Nat.card F - 1 = Fintype.card F - 1 := by rw [Nat.card_eq_fintype_card]
  rw [hc]
  ext i j
  by_cases hij : i = j
  · subst hij
    simp [diagonal_apply_eq, FiniteField.pow_card_sub_one_eq_one _ (hne i)]
  · simp [diagonal_apply_ne _ hij, one_apply_ne hij]

theorem burnsideF45U_coprime_card_unT (hF : Nat.card F = (p ^ f) ^ 2) (n : ℕ) :
    p.Coprime (Nat.card (unT (F := F) (p := p) (f := f) n)) := by
  have hp : p.Prime := Fact.out
  rw [Nat.Prime.coprime_iff_not_dvd hp]
  intro h
  have : Fintype (unT (F := F) (p := p) (f := f) n) := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card] at h
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card (G := unT (F := F) (p := p) (f := f) n) p h
  have hpow : (x : SU (unitaryInvolution F p f) n) ^ (Nat.card F - 1) = 1 :=
    burnsideF45U_pow_card_sub_one_unT x.2
  have h3 : orderOf (x : SU (unitaryInvolution F p f) n) ∣ Nat.card F - 1 :=
    orderOf_dvd_of_pow_eq_one hpow
  rw [Subgroup.orderOf_coe, hx] at h3
  have h1 : 1 < Nat.card F := Finite.one_lt_card
  have hf : f ≠ 0 := by
    rintro rfl
    rw [hF] at h1
    simp at h1
  have h4 : p ∣ Nat.card F := by
    rw [hF]
    exact Dvd.dvd.pow (dvd_pow_self p hf) (by norm_num)
  have h5 : p ∣ Nat.card F - (Nat.card F - 1) := Nat.dvd_sub h4 h3
  rw [show Nat.card F - (Nat.card F - 1) = 1 by omega] at h5
  exact hp.one_lt.ne' (Nat.dvd_one.mp h5)

theorem burnsideF45U_isSylowOf_unU (hF : Nat.card F = (p ^ f) ^ 2) {n : ℕ} (hn : 2 ≤ n)
    (hpU : IsPGroup p (unU hF n)) : ChF.IsSylowOf p (unU hF n) ⊤ := by
  obtain ⟨ζ, hζ⟩ := exists_traceZero_ne_zero hF
  haveI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  have hcop : p.Coprime (unU hF n).index :=
    CFSG.LieType.Steinberg.CentralExt.BorelIndex.coprime_index_posUnipotent (D := rootDatum hF n)
      (isCTGroupDatum hF n hn ζ hζ) (steinbergExtras hF n hn ζ hζ)
      (CFSG.LieType.Steinberg.CentralExt.SUBruhat.bruhatExtras hF hn ζ hζ)
      (fun γ hγ => CFSG.LieType.Steinberg.isPGroup_rootGroup (unitaryInvolution_involutive hF)
        (SUExtras.toStd_ne_zero_of_mem_roots hγ)) (burnsideF45U_coprime_card_unT hF n)
  refine ⟨le_top, hpU, ?_⟩
  rw [Subgroup.relIndex_top_right]
  exact (Nat.Prime.coprime_iff_not_dvd Fact.out).1 hcop

end Sylow

section Systems

open CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.Quasithin.H13.F431.Un

variable {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p]
  (hF : Nat.card F = (p ^ f) ^ 2) (ζ : traceZero (unitaryInvolution F p f))
  [hζ : Fact ((ζ : F) ≠ 0)]

@[expose] noncomputable def burnsideF45U4_system :
    CFSG.GH74.BNPair.RankTwoSystem (StatedProj (StatedSU 4 (p ^ f) F)) 4 :=
  haveI := CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU F p f hF 4 (by norm_num)
    (by simp)
  ((unPre hF ζ).map (burnsideF45U_proj hF 4) (burnsideF45U_proj_surjective hF 4)
    (burnsideF45U_ker_le hF (by norm_num) ζ hζ.out)
    (burnsideF45U_unU_inf_ker hF (by norm_num))).toSystemOfSimple

theorem burnsideF45U4_system_isSylow : ChF.IsSylowOf p (burnsideF45U4_system hF ζ).U ⊤ :=
  burnsideF45_isSylowOf_map_surj (burnsideF45U_proj hF 4) (burnsideF45U_proj_surjective hF 4)
    (burnsideF45U_isSylowOf_unU hF (by norm_num) (isPGroup_unU hF))

@[expose] noncomputable def burnsideF45U5_system :
    CFSG.GH74.BNPair.RankTwoSystem (StatedProj (StatedSU 5 (p ^ f) F)) 4 :=
  haveI := CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU F p f hF 5 (by norm_num)
    (by simp)
  ((un5Pre hF ζ).map (burnsideF45U_proj hF 5) (burnsideF45U_proj_surjective hF 5)
    (burnsideF45U_ker_le hF (by norm_num) ζ hζ.out)
    (burnsideF45U_unU_inf_ker hF (by norm_num))).toSystemOfSimple

theorem burnsideF45U5_system_isSylow : ChF.IsSylowOf p (burnsideF45U5_system hF ζ).U ⊤ :=
  burnsideF45_isSylowOf_map_surj (burnsideF45U_proj hF 5) (burnsideF45U_proj_surjective hF 5)
    (burnsideF45U_isSylowOf_unU hF (by norm_num) (isPGroup_unU5 hF))

end Systems

section Marking

open CFSG.ASVolI.ChF.ClassicalRoots

theorem burnsideF45U_nonempty_marking {c : ClassicalRoots.Kind} {p f : ℕ} {E : Type} [Group E]
    {Gp M₁ M₂ : Subgroup E} (h : HypF_4_4g (classicalKind c) p f Gp M₁ M₂) :
    Nonempty (ClassicalRoots.Marking c p f Gp) := by
  obtain ⟨chart, -⟩ := h.lie_amalgam
  rcases chart.coordinates with
    ⟨c', hk, marking, -⟩ | ⟨hk, -⟩ | ⟨hk, -⟩ | ⟨hk, -⟩ |
    ⟨-, exponent, K, fK, finK, charK, scope, ⟨hk, -⟩ | ⟨hk, -⟩⟩
  · have hc : c' = c := by
      cases c <;> cases c' <;> first | rfl | exact absurd hk (by decide)
    subst hc
    exact ⟨marking⟩
  all_goals exact absurd hk (by cases c <;> decide)

end Marking

section Facts

open CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.Quasithin.H13.F431.Un
  CFSG.ASVolI.ChF.ClassicalRoots


theorem burnsideF45_facts45L_U4 {p f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : HypF_4_4 .U4 p f Gp M₁ M₂) (hp : p.Prime) (hm : 3 ≤ GLKind.U4.m) :
    (burnsideF45_setting hyp hp hm).Facts45L := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨marking⟩ := burnsideF45U_nonempty_marking (c := .U4) hyp.toHypF_4_4g
  have hF : Nat.card marking.field = (p ^ f) ^ 2 := marking.field_card.trans (if_pos (Or.inl rfl))
  haveI : CharP marking.field p := CFSG.ClassicalGroups.Unitary.charP_of_card_sq hF
  obtain ⟨ζ, hζ⟩ := exists_traceZero_ne_zero hF
  haveI : Fact ((ζ : marking.field) ≠ 0) := ⟨hζ⟩
  have hU := burnsideF45U4_system_isSylow hF ζ
  let θ₀ : StatedProj (StatedSU 4 (p ^ f) marking.field) ≃* ↥Gp :=
    (MulEquiv.refl _ : StatedProj (StatedSU 4 (p ^ f) marking.field) ≃*
      StatedProj (nativeGroup .U4 (p ^ f) marking.field)).trans marking.identification
  exact burnsideF45_facts45L_of_system hyp hp hm (burnsideF45_parabolics hyp.toHypF_4_4g) θ₀
    (burnsideF45U4_system hF ζ) rfl hU
    (fun i => burnsideF45_bn_modelBase (burnsideF45U4_system hF ζ) hp hU i)

theorem burnsideF45_facts45L_U5 {p f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : HypF_4_4 .U5 p f Gp M₁ M₂) (hp : p.Prime) (hm : 3 ≤ GLKind.U5.m) :
    (burnsideF45_setting hyp hp hm).Facts45L := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨marking⟩ := burnsideF45U_nonempty_marking (c := .U5) hyp.toHypF_4_4g
  have hF : Nat.card marking.field = (p ^ f) ^ 2 := marking.field_card.trans (if_pos (Or.inr rfl))
  haveI : CharP marking.field p := CFSG.ClassicalGroups.Unitary.charP_of_card_sq hF
  obtain ⟨ζ, hζ⟩ := exists_traceZero_ne_zero hF
  haveI : Fact ((ζ : marking.field) ≠ 0) := ⟨hζ⟩
  have hU := burnsideF45U5_system_isSylow hF ζ
  let θ₀ : StatedProj (StatedSU 5 (p ^ f) marking.field) ≃* ↥Gp :=
    (MulEquiv.refl _ : StatedProj (StatedSU 5 (p ^ f) marking.field) ≃*
      StatedProj (nativeGroup .U5 (p ^ f) marking.field)).trans marking.identification
  exact burnsideF45_facts45L_of_system hyp hp hm (burnsideF45_parabolics hyp.toHypF_4_4g) θ₀
    (burnsideF45U5_system hF ζ) rfl hU
    (fun i => burnsideF45_bn_modelBase (burnsideF45U5_system hF ζ) hp hU i)

end Facts

end CFSG.ASVolI
