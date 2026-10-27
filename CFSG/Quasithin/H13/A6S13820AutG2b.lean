module

public import CFSG.Quasithin.H13.A6S13820AutG2a
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenAutomorphisms
public import CFSG.Quasithin.H13.A6S13820AutL3b
public import CFSG.Quasithin.H13.A6S13820AutT

public section

namespace CFSG.Quasithin.H13.A6

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.QuasithinUnique.Vol2Native.L239.Lie.G2 CFSG.Quasithin.H13.RootData.G2
  CFSG.ComponentClassification.UnbalancedCatalog CFSG.LocalAnalysis.ComponentInitial
open CFSG.QuasithinUnique (IsSylowTwoOf)
open scoped Pointwise

namespace Aut20

theorem three_le_card_fix20 {K : Type} [Field K] [Finite K] (σ : K ≃+* K) {s : K}
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) (hs : σ s = s) : 3 ≤ Nat.card {t : K // σ t = t} := by
  let f : Fin 3 → {t : K // σ t = t} := ![⟨0, map_zero σ⟩, ⟨1, map_one σ⟩, ⟨s, hs⟩]
  have hs0' : (0 : K) ≠ s := hs0.symm
  have hs1' : (1 : K) ≠ s := hs1.symm
  have hf : Function.Injective f := by
    intro i j hij
    have hij' : (f i : K) = f j := congrArg Subtype.val hij
    fin_cases i <;> fin_cases j <;> simp_all [f]
  simpa using Nat.card_le_card_of_injective f hf

theorem inf_ne_bot20 {G : Type*} [Group G] {C N H : Subgroup G} (hHN : H ≤ N)
    (hidx : C.relIndex N ∣ 3) (hH : Nat.card H = 9) : C ⊓ H ≠ ⊥ := by
  have hidx0 : C.relIndex N ≠ 0 := by
    intro h0
    rw [h0] at hidx
    norm_num at hidx
  have hle := Subgroup.relIndex_le_of_le_right hHN hidx0
  have h3 := Nat.le_of_dvd (by norm_num) hidx
  intro hbot
  have h9 : C.relIndex H = 9 := by
    rw [Subgroup.relIndex, Subgroup.subgroupOf_eq_bot.mpr (disjoint_iff.mpr hbot),
      Subgroup.index_bot, hH]
  omega

theorem sigma_eq_one_two20 {K : Type} [Field K] [Finite K] (hK : Nat.card K = 4) (σ : K ≃+* K)
    {p : Kˣ × Kˣ} (hp1 : p ≠ 1)
    (hp : Units.map σ.toRingHom.toMonoidHom p.1 = p.1 ∧
      Units.map σ.toRingHom.toMonoidHom p.2 = p.2) : σ = 1 := by
  by_contra hσ
  obtain ⟨s, hs1, hs⟩ : ∃ s : Kˣ, s ≠ 1 ∧ σ (s : K) = s := by
    by_cases h1 : p.1 = 1
    · have h2 : p.2 ≠ 1 := fun h2 => hp1 (Prod.ext h1 h2)
      exact ⟨p.2, h2, by simpa using congrArg Units.val hp.2⟩
    · exact ⟨p.1, h1, by simpa using congrArg Units.val hp.1⟩
  have hfixc := CFSG.LocalAnalysis.EvenBN.LinearThree.card_fix_mul_card_fix_le (f := 2)
    (by norm_num) hK hσ
  have h3 := three_le_card_fix20 σ (Units.ne_zero s) (fun h => hs1 (Units.ext h)) hs
  rw [hK] at hfixc
  nlinarith

section Torus


theorem mem_normalizer_U20 {K : Type} [Field K] {c : ↥(adjointGroup Tag.G2 K)}
    (hc : (c : ModGL Tag.G2 K) ∈ torusGroup Tag.G2 K) :
    c ∈ Subgroup.normalizer (((posUnipotent Tag.G2 K).subgroupOf (adjointGroup Tag.G2 K) :
      Subgroup ↥(adjointGroup Tag.G2 K)) : Set ↥(adjointGroup Tag.G2 K)) := by
  have hN := torusGroup_le_normalizer_posUnipotent (τ := Tag.G2) (R := K) hc
  rw [Subgroup.mem_normalizer_iff] at hN ⊢
  intro y
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_mul,
    Subgroup.coe_inv]
  exact hN y

theorem torus_fix20 {K : Type} [Field K] {g : ModGL Tag.G2 K} (hgB : g ∈ borelGroup Tag.G2 K)
    {σ : K ≃+* K} {s₁ s₂ : Kˣ}
    (h : (tor20 s₁ s₂)⁻¹ * (g * Units.map (entrywiseHom σ.toRingHom) (tor20 s₁ s₂) * g⁻¹) ∈
      posUnipotent Tag.G2 K) :
    Units.map σ.toRingHom.toMonoidHom s₁ = s₁ ∧ Units.map σ.toRingHom.toMonoidHom s₂ = s₂ := by
  have hgB' : g ∈ (SetLike.coe (torusGroup Tag.G2 K) *
      SetLike.coe (posUnipotent Tag.G2 K) : Set (ModGL Tag.G2 K)) := by
    rw [← (triangular_borel_structure.{0, 0} Tag.G2 K).2.2.2.2.1]
    exact hgB
  obtain ⟨t, ht, u, hu, htu⟩ := Set.mem_mul.mp hgB'
  have hHab := (triangular_borel_structure.{0, 0} Tag.G2 K).1
  have hHN := torusGroup_le_normalizer_posUnipotent (τ := Tag.G2) (R := K)
  have hHU := torusGroup_inf_posUnipotent (τ := Tag.G2) (R := K)
  rw [entrywise_tor20 σ] at h
  set d := tor20 (Units.map σ.toRingHom.toMonoidHom s₁) (Units.map σ.toRingHom.toMonoidHom s₂)
    with hd
  have hdH : d ∈ torusGroup Tag.G2 K := tor20_mem_torusGroup _ _
  have hcH := tor20_mem_torusGroup (K := K) s₁ s₂
  have hcomm' : g * d * g⁻¹ * d⁻¹ ∈ posUnipotent Tag.G2 K := by
    rw [← htu]
    exact comm_mem_of_mul20 hHN hHab ht hu hdH
  have h2 := mem_of_conj_mem20 (hHN hcH) hcomm' h
  have h3 : (tor20 s₁ s₂)⁻¹ * d ∈ torusGroup Tag.G2 K ⊓ posUnipotent Tag.G2 K :=
    Subgroup.mem_inf.mpr ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ hcH) hdH, h2⟩
  rw [hHU, Subgroup.mem_bot, inv_mul_eq_one, hd] at h3
  have h4 := tor20_injective h3
  exact ⟨h4.1.symm, h4.2.symm⟩

theorem card_range_torHom20 {K : Type} [Field K] [Finite K] (hK : Nat.card K = 4) :
    Nat.card (torHom20 (K := K)).range = 9 := by
  rw [← Nat.card_congr (MonoidHom.ofInjective torHom20_injective).toEquiv, Nat.card_prod,
    Nat.card_units, hK]

theorem range_torHom20_le {K : Type} [Field K] :
    (torHom20 (K := K)).range ≤ Subgroup.normalizer
      (((posUnipotent Tag.G2 K).subgroupOf (adjointGroup Tag.G2 K) :
        Subgroup ↥(adjointGroup Tag.G2 K)) : Set ↥(adjointGroup Tag.G2 K)) := by
  rintro _ ⟨p, rfl⟩
  exact mem_normalizer_U20 (tor20_mem_torusGroup p.1 p.2)

theorem exists_tor_mem20 {K : Type} [Field K] [Finite K] (hK : Nat.card K = 4)
    {C : Subgroup ↥(adjointGroup Tag.G2 K)}
    (hidx : C.relIndex (Subgroup.normalizer
      (((posUnipotent Tag.G2 K).subgroupOf (adjointGroup Tag.G2 K) :
        Subgroup ↥(adjointGroup Tag.G2 K)) : Set ↥(adjointGroup Tag.G2 K))) ∣ 3) :
    ∃ p : Kˣ × Kˣ, p ≠ 1 ∧ torHom20 p ∈ C := by
  have hne := inf_ne_bot20 range_torHom20_le hidx (card_range_torHom20 hK)
  obtain ⟨⟨c, hcC, p, hp⟩, hc1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  refine ⟨p, fun hp1 => hc1 (Subtype.ext ?_), hp ▸ hcC⟩
  show c = 1
  rw [← hp, hp1, map_one]

theorem cube_fix20 {K : Type} [Field K] {C : Subgroup ↥(adjointGroup Tag.G2 K)}
    (hCn : (C.subgroupOf (Subgroup.normalizer
      (((posUnipotent Tag.G2 K).subgroupOf (adjointGroup Tag.G2 K) :
        Subgroup ↥(adjointGroup Tag.G2 K)) : Set ↥(adjointGroup Tag.G2 K)))).Normal)
    (hidx : C.relIndex (Subgroup.normalizer
      (((posUnipotent Tag.G2 K).subgroupOf (adjointGroup Tag.G2 K) :
        Subgroup ↥(adjointGroup Tag.G2 K)) : Set ↥(adjointGroup Tag.G2 K))) ∣ 3)
    (σ : K ≃+* K)
    (hfix : ∀ c ∈ C, ∀ s₁ s₂ : Kˣ, (c : ModGL Tag.G2 K) = tor20 s₁ s₂ →
      Units.map σ.toRingHom.toMonoidHom s₁ = s₁ ∧ Units.map σ.toRingHom.toMonoidHom s₂ = s₂)
    (a : Kˣ) : σ ((a : K) ^ 3) = (a : K) ^ 3 := by
  have hmem := mem_normalizer_U20 (c := torHom20 (a, 1)) (tor20_mem_torusGroup a 1)
  have h3 := pow_three_mem20 hCn hidx hmem
  rw [← map_pow, Prod.pow_mk, one_pow] at h3
  have h4 := (hfix _ h3 (a ^ 3) 1 rfl).1
  have h5 := congrArg Units.val h4
  simpa using h5

end Torus

section NormalForm


theorem isSylowTwoOf_U20 {K : Type} [Field K] [Finite K] [CharP K 2] :
    IsSylowTwoOf ((posUnipotent Tag.G2 K).subgroupOf (adjointGroup Tag.G2 K)) ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hp, hi⟩ := isPGroup_and_not_dvd_index 2
    (posUnipotent_le_adjointGroup (τ := Tag.G2) (K := K)) card_posUnipotent
  refine ⟨le_top, hp, ?_⟩
  rwa [show (((posUnipotent Tag.G2 K).subgroupOf (adjointGroup Tag.G2 K)).subgroupOf ⊤).index =
    ((posUnipotent Tag.G2 K).subgroupOf (adjointGroup Tag.G2 K)).relIndex ⊤ from rfl,
    Subgroup.relIndex_top_right]

theorem mem_borel_of20 {K : Type} [Field K] {α : MulAut ↥(adjointGroup Tag.G2 K)}
    {g : ↥(adjointGroup Tag.G2 K)} {σ : K ≃+* K}
    (hgσ : ∀ h : ↥(adjointGroup Tag.G2 K), (α h : ModGL Tag.G2 K) =
      (g : ModGL Tag.G2 K) * Units.map (entrywiseHom σ.toRingHom) (h : ModGL Tag.G2 K) *
        (g : ModGL Tag.G2 K)⁻¹)
    (hαS : ((posUnipotent Tag.G2 K).subgroupOf (adjointGroup Tag.G2 K)).map α.toMonoidHom =
      (posUnipotent Tag.G2 K).subgroupOf (adjointGroup Tag.G2 K)) :
    (g : ModGL Tag.G2 K) ∈ borelGroup Tag.G2 K := by
  have hUC : posUnipotent Tag.G2 K ≤ adjointGroup Tag.G2 K := posUnipotent_le_adjointGroup
  have hψU := map_entrywise_posUnipotent (K := K) σ
  have hαU : ∀ u (hu : u ∈ posUnipotent Tag.G2 K),
      ((α ⟨u, hUC hu⟩ : ↥(adjointGroup Tag.G2 K)) : ModGL Tag.G2 K) ∈
        posUnipotent Tag.G2 K := by
    intro u hu
    have h1 : α ⟨u, hUC hu⟩ ∈ (posUnipotent Tag.G2 K).subgroupOf (adjointGroup Tag.G2 K) := by
      rw [← hαS]
      exact ⟨_, Subgroup.mem_subgroupOf.mpr hu, rfl⟩
    exact Subgroup.mem_subgroupOf.mp h1
  have hαU' : ∀ y : ↥(adjointGroup Tag.G2 K), (y : ModGL Tag.G2 K) ∈ posUnipotent Tag.G2 K →
      ((α.symm y : ↥(adjointGroup Tag.G2 K)) : ModGL Tag.G2 K) ∈ posUnipotent Tag.G2 K := by
    intro y hy
    have h1 : y ∈ (posUnipotent Tag.G2 K).subgroupOf (adjointGroup Tag.G2 K) :=
      Subgroup.mem_subgroupOf.mpr hy
    rw [← hαS] at h1
    obtain ⟨x, hx, rfl⟩ := h1
    have e : α.symm (α.toMonoidHom x) = x := α.symm_apply_apply x
    rw [e]
    exact Subgroup.mem_subgroupOf.mp hx
  have hgN : (g : ModGL Tag.G2 K) ∈
      Subgroup.normalizer (posUnipotent Tag.G2 K : Set (ModGL Tag.G2 K)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      have hx' : x ∈ (posUnipotent Tag.G2 K).map (Units.map (entrywiseHom σ.toRingHom)) := by
        rw [hψU]
        exact hx
      obtain ⟨u, hu, rfl⟩ := hx'
      rw [← hgσ ⟨u, hUC hu⟩]
      exact hαU u hu
    · intro hx
      have hu' := hαU' ⟨_, hUC hx⟩ hx
      have h1 := hgσ (α.symm ⟨_, hUC hx⟩)
      rw [MulEquiv.apply_symm_apply] at h1
      have h2 : x = Units.map (entrywiseHom σ.toRingHom)
          ((α.symm ⟨_, hUC hx⟩ : ↥(adjointGroup Tag.G2 K)) : ModGL Tag.G2 K) :=
        mul_left_cancel (mul_right_cancel h1)
      rw [h2, ← hψU]
      exact ⟨_, hu', rfl⟩
  rw [← (borel_self_normalizers Tag.G2 K).1]
  exact ⟨g.2, hgN⟩

theorem autBorelG2U20 {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ} (hn : 2 ≤ n)
    (hK : Nat.card K = 2 ^ n) {C : Subgroup ↥(adjointGroup Tag.G2 K)}
    {α : MulAut ↥(adjointGroup Tag.G2 K)}
    (h : BorelAut13820 ((posUnipotent Tag.G2 K).subgroupOf (adjointGroup Tag.G2 K)) C α) :
    ∃ g, α = MulAut.conj g := by
  obtain ⟨-, -, -, hCn, hidx, -, hαS, hcomm⟩ := h
  obtain ⟨⟨g, σ⟩, hgσ, -⟩ := (even_G2_exact_automorphism_normal_form hn K hK).1 α
  simp only at hgσ
  have hgB := mem_borel_of20 hgσ hαS
  have hfix : ∀ c ∈ C, ∀ s₁ s₂ : Kˣ, (c : ModGL Tag.G2 K) = tor20 s₁ s₂ →
      Units.map σ.toRingHom.toMonoidHom s₁ = s₁ ∧ Units.map σ.toRingHom.toMonoidHom s₂ = s₂ := by
    intro c hc s₁ s₂ hcs
    have h1 := Subgroup.mem_subgroupOf.mp (hcomm c hc)
    rw [Subgroup.coe_mul, Subgroup.coe_inv, hgσ c, hcs] at h1
    exact torus_fix20 hgB h1
  have hσ1 : σ = 1 := by
    rcases Nat.lt_or_ge n 3 with hn3 | hn3
    · have hK4 : Nat.card K = 4 := by rw [hK, show n = 2 by omega]; norm_num
      obtain ⟨p, hp1, hpC⟩ := exists_tor_mem20 hK4 hidx
      exact sigma_eq_one_two20 hK4 σ hp1 (hfix _ hpC p.1 p.2 rfl)
    · rcases sigma_eq_one_of_fix_cubes20 hn hK σ (cube_fix20 hCn hidx σ hfix) with h1 | h2
      · exact h1
      · omega
  subst hσ1
  refine ⟨g, MulEquiv.ext fun x => Subtype.ext ?_⟩
  rw [hgσ x, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
  congr 2
  exact Units.ext (entrywise_id _)

theorem autBorelG2_20 {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 2 ≤ n)
    (hK : Nat.card K = 2 ^ n) {S C : Subgroup ↥(adjointGroup Tag.G2 K)}
    {α : MulAut ↥(adjointGroup Tag.G2 K)} (h : BorelAut13820 S C α) :
    ∃ g, α = MulAut.conj g := by
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two (by omega) hK
  have : Finite (ModGL Tag.G2 K) := finite_modGL
  obtain ⟨x, hx⟩ := exists_map_conj_eq20 h.1 (isSylowTwoOf_U20 (K := K))
  have h' := borelAut_mulEquiv20 (MulAut.conj x) h
  rw [hx] at h'
  exact (inner_congr_iff20 (MulAut.conj x) α).1 (autBorelG2U20 hn hK h')

end NormalForm

end Aut20

theorem autBorel13820G2_holds :
    AutBorel13820G2 := by
  intro Q _ _ n hq hZ hn hG S C α h
  have hquot := Aut20.borelAut_quot20 hZ h
  have hm : UntwistedChevalleyModel (Q ⧸ Subgroup.center Q) .G2 (2 ^ n) := hG.2
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup .G2 hm
  have : Finite (ModGL Tag.G2 K) := finite_modGL
  obtain ⟨g, hg⟩ := (Aut20.inner_congr_iff20 e _).1
    (Aut20.autBorelG2_20 hn hK (Aut20.borelAut_mulEquiv20 e hquot))
  have : Group.IsPerfect Q := hq.1
  exact Aut20.inner_of_quot20 hg

end CFSG.Quasithin.H13.A6
