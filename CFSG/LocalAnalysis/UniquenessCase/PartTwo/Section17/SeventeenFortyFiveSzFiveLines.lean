module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFortyFiveSzFiveFactors
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFortyFiveSzFiveNormC31
public import CFSG.GroupTheory.SylowIntersectionControl.Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.SzFive

open Subgroup CFSG.Open CFSG.Quasithin
  CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.GroupTheory
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]




private theorem action_on_line_of_mem_sup_centOverO2
    (D : Data G) {X L K A₂ : Subgroup G} {φ : ↥D.M →* DihedralGroup 5}
    (hXM : X ≤ D.M) (hMX : D.M ≤ Subgroup.normalizer (X : Set G))
    (hXeq : X = L ⊔ K) (hLKne : L ≠ K)
    (hLcalM : L ∈ calC D.M) (hKcalM : K ∈ calC D.M)
    (hLcalX : L ∈ calC X) (hKcalX : K ∈ calC X)
    (hNleK : X ⊔ F08.CentOverO2 D.M X ≤ Subgroup.normalizer (K : Set G))
    (hker : φ.ker = (X ⊔ F08.CentOverO2 D.M X).subgroupOf D.M)
    (hSzK : IsSz (Bar2 K) 5)
    (hA₂K : A₂ ≤ K) (hA₂card : Nat.card A₂ = 31)
    (hA₂disj : A₂ ⊓ CFSG.Open.pCoreOf 2 K = ⊥)
    {n : G} (hnN : n ∈ X ⊔ F08.CentOverO2 D.M X)
    (hnA₂ : n ∈ Subgroup.normalizer (A₂ : Set G)) :
    (∀ a ∈ A₂, n * a * n⁻¹ = a) ∨ (∀ a ∈ A₂, n * a * n⁻¹ = a⁻¹) := by
  classical
  haveI : Fact (Nat.Prime 31) := ⟨by norm_num⟩
  have hNleM : X ⊔ F08.CentOverO2 D.M X ≤ D.M := by
    refine sup_le hXM ?_
    intro c hc
    exact (mem_centOverO2_iff.mp hc).1
  have hnM : n ∈ D.M := hNleM hnN
  have hnK : n ∈ Subgroup.normalizer (K : Set G) := hNleK hnN
  obtain ⟨u, hu⟩ :=
    rhoL_mem_inner_of_mem_sup_centOverO2 hXM hMX hXeq hLKne hLcalM hKcalM
      hLcalX hKcalX hNleK hnN
  let f : ↥A₂ →* Bar2 K :=
    (QuotientGroup.mk' (CFSG.pCore 2 ↥K)).comp (Subgroup.inclusion hA₂K)
  have hf_inj : Function.Injective f := by
    refine (injective_iff_map_eq_one f).mpr ?_
    intro a ha
    apply Subtype.ext
    have haK : (QuotientGroup.mk (⟨(a : G), hA₂K a.2⟩ : ↥K) : Bar2 K) = 1 := ha
    have hmemK : (⟨(a : G), hA₂K a.2⟩ : ↥K) ∈ CFSG.pCore 2 ↥K :=
      (QuotientGroup.eq_one_iff _).mp haK
    have hmemG : (a : G) ∈ CFSG.Open.pCoreOf 2 K :=
      (CFSG.Quasithin.C1Pack.coe_mem_pCoreOf_iff K ⟨(a : G), hA₂K a.2⟩).mpr hmemK
    have hmem : (a : G) ∈ A₂ ⊓ CFSG.Open.pCoreOf 2 K := ⟨a.2, hmemG⟩
    rw [hA₂disj] at hmem
    exact Subgroup.mem_bot.mp hmem
  have hCeq : (barImage K A₂) = f.range := by
    simp [barImage, f, MonoidHom.range_comp, Subgroup.inclusion_range]
  have hCcard : Nat.card (barImage K A₂) = 31 := by
    rw [hCeq, ← hA₂card]
    change Nat.card (Set.range f) = Nat.card ↥A₂
    exact Nat.card_congr (Equiv.ofInjective f hf_inj).symm
  have hfin : ∀ a : ↥A₂, f a =
      (QuotientGroup.mk (⟨(a : G), hA₂K a.2⟩ : ↥K) : Bar2 K) := fun a => rfl
  have hact : ∀ a : ↥A₂,
      (QuotientGroup.mk
        (⟨n * (a : G) * n⁻¹,
          hA₂K ((Subgroup.mem_normalizer_iff.mp hnA₂ (a : G)).mp a.2)⟩ : ↥K) :
        Bar2 K) = u * f a * u⁻¹ := by
    intro a
    have hna : n * (a : G) * n⁻¹ ∈ A₂ :=
      (Subgroup.mem_normalizer_iff.mp hnA₂ (a : G)).mp a.2
    have harg : (⟨n * (a : G) * n⁻¹, hA₂K hna⟩ : ↥K) =
        Subgroup.normalizerMonoidHom K ⟨n, hnK⟩ ⟨(a : G), hA₂K a.2⟩ := by
      apply Subtype.ext
      rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
    have h1 : (UC6S846.rhoL K ⟨n, hnK⟩) (f a) =
        QuotientGroup.mk (⟨n * (a : G) * n⁻¹, hA₂K hna⟩ : ↥K) := by
      rw [hfin a, UC6S846.rhoL_mk, ← harg]
    have h2 : (MulAut.conj u) (f a) = u * f a * u⁻¹ := rfl
    rw [hu] at h2
    exact h1.symm.trans h2
  have hinj : ∀ a b : ↥A₂, f a = f b → (a : G) = (b : G) := by
    intro a b hab
    exact congrArg Subtype.val (hf_inj hab)
  have hcentral : ∀ a : ↥A₂, u * f a * u⁻¹ = f a → n * (a : G) * n⁻¹ = (a : G) := by
    intro a heq
    have hna : n * (a : G) * n⁻¹ ∈ A₂ :=
      (Subgroup.mem_normalizer_iff.mp hnA₂ (a : G)).mp a.2
    have hq : f ⟨n * (a : G) * n⁻¹, hna⟩ = f a := by
      rw [hfin, hfin]
      exact (hact a).trans heq
    exact hinj _ _ hq
  have hinvert : ∀ a : ↥A₂, u * f a * u⁻¹ = (f a)⁻¹ → n * (a : G) * n⁻¹ = (a : G)⁻¹ := by
    intro a heq
    have hna : n * (a : G) * n⁻¹ ∈ A₂ :=
      (Subgroup.mem_normalizer_iff.mp hnA₂ (a : G)).mp a.2
    have hainv : (a : G)⁻¹ ∈ A₂ := A₂.inv_mem a.2
    have hq : f ⟨n * (a : G) * n⁻¹, hna⟩ = f ⟨(a : G)⁻¹, hainv⟩ := by
      rw [hfin, hfin]
      refine (hact a).trans ?_
      rw [heq]
      congr 1
    exact hinj _ _ hq
  by_cases huC : u ∈ barImage K A₂
  · left
    intro a ha
    refine hcentral ⟨a, ha⟩ ?_
    haveI : IsMulCommutative ↥(barImage K A₂) :=
      (isCyclic_of_prime_card hCcard).isMulCommutative
    have hmemC : f ⟨a, ha⟩ ∈ barImage K A₂ := by
      rw [hCeq]
      exact Set.mem_range_self (⟨a, ha⟩ : ↥A₂)
    have hcomm_sub : (⟨u, huC⟩ : ↥(barImage K A₂)) * ⟨f ⟨a, ha⟩, hmemC⟩ =
        ⟨f ⟨a, ha⟩, hmemC⟩ * ⟨u, huC⟩ :=
      (isCyclic_of_prime_card hCcard).isMulCommutative.is_comm.comm _ _
    have hcomm : u * f ⟨a, ha⟩ = f ⟨a, ha⟩ * u := congrArg Subtype.val hcomm_sub
    rw [hcomm]
    group
  · right
    intro a ha
    refine hinvert ⟨a, ha⟩ ?_
    have hmemC : f ⟨a, ha⟩ ∈ barImage K A₂ := by
      rw [hCeq]
      exact Set.mem_range_self (⟨a, ha⟩ : ↥A₂)
    exact (sz32_normalizer_c31
      hSzK (barImage K A₂) hCcard).2 u
      (Subgroup.mem_normalizer_iff_map_conj_eq.mpr (by
        rw [hu]
        exact rhoL_maps_barImage hA₂K hnA₂ hnK)) huC (f ⟨a, ha⟩) hmemC


private theorem phi_not_rotations_of_map_conj_eq
    (D : Data G) {X L K N : Subgroup G} {φ : ↥D.M →* DihedralGroup 5}
    (hNM : N ≤ D.M) (hNleL : N ≤ Subgroup.normalizer (L : Set G))
    (hker : φ.ker = N.subgroupOf D.M) (hφ : Function.Surjective φ)
    (hMLrel : (D.M ⊓ Subgroup.normalizer (L : Set G)).relIndex D.M = 2)
    {g : G} (hgM : g ∈ D.M) (hLg : L.map (MulAut.conj g).toMonoidHom = K) (hLKne : L ≠ K) :
    φ ⟨g, hgM⟩ ∉ TauCeti.dihedralRotations 5 := by
  classical
  let H : Subgroup G := D.M ⊓ Subgroup.normalizer (L : Set G)
  have hHM : H ≤ D.M := inf_le_left
  have hNleH : N ≤ H := fun x hx => ⟨hNM hx, hNleL hx⟩
  have hNindex : N.index = (N.subgroupOf D.M).index * D.M.index := by
    have hmap := Subgroup.index_map_subtype (H := D.M) (K := N.subgroupOf D.M)
    rwa [Subgroup.map_subgroupOf_eq_of_le hNM] at hmap
  have hkeridx : (N.subgroupOf D.M).index = 2 * 5 := by
    rw [← hker, Subgroup.index_ker φ, MonoidHom.range_eq_top.mpr hφ]
    rw [Subgroup.card_top, DihedralGroup.nat_card]
  have hNrelM : N.relIndex D.M = 2 * 5 := by
    have hrel := Subgroup.relIndex_mul_index hNM
    rw [hNindex, hkeridx] at hrel
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos hrel
  have hNrelH : N.relIndex H = 5 := by
    have hrel := Subgroup.relIndex_mul_relIndex N H D.M hNleH hHM
    rw [hMLrel, hNrelM] at hrel
    have h2 : N.relIndex H * 2 = 5 * 2 := by rw [hrel, mul_comm]
    exact Nat.eq_of_mul_eq_mul_right (by norm_num) h2
  have hkercomp : (φ.comp (Subgroup.inclusion hHM)).ker = N.subgroupOf H := by
    ext x
    change (φ.comp (Subgroup.inclusion hHM)) x = 1 ↔ x ∈ N.subgroupOf H
    rw [MonoidHom.comp_apply]
    constructor
    · intro h
      have h1 : (Subgroup.inclusion hHM x : ↥D.M) ∈ φ.ker := MonoidHom.mem_ker.mpr h
      rw [hker, Subgroup.mem_subgroupOf] at h1
      exact Subgroup.mem_subgroupOf.mpr h1
    · intro h
      have h1 : (x : G) ∈ N := Subgroup.mem_subgroupOf.mp h
      have h2 : (Subgroup.inclusion hHM x : ↥D.M) ∈ N.subgroupOf D.M :=
        Subgroup.mem_subgroupOf.mpr h1
      rw [← hker] at h2
      exact MonoidHom.mem_ker.mp h2
  have hindexH : (N.subgroupOf H).index = N.relIndex H := by
    rw [← Subgroup.relIndex_top_right (N.subgroupOf H), ← Subgroup.subgroupOf_self H,
      Subgroup.relIndex_subgroupOf (H := N) (K := H) (L := H) le_rfl]
  have himgcard : Nat.card ↥(φ.comp (Subgroup.inclusion hHM)).range = 5 := by
    have h := Subgroup.index_ker (φ.comp (Subgroup.inclusion hHM))
    rw [hkercomp, hindexH, hNrelH] at h
    exact h.symm
  have hrangeRot : (φ.comp (Subgroup.inclusion hHM)).range ≤ TauCeti.dihedralRotations 5 := by
    intro z hz
    have hz5 : z ^ 5 = 1 := by
      have hdvd : orderOf z ∣ 5 := by
        have h1 := Subgroup.orderOf_dvd_natCard (φ.comp (Subgroup.inclusion hHM)).range hz
        rw [himgcard] at h1
        exact h1
      exact orderOf_dvd_iff_pow_eq_one.mp hdvd
    rw [TauCeti.mem_dihedralRotations_iff]
    by_contra h
    push Not at h
    rcases hd : z with i | i
    · exact h i hd
    · rw [hd] at hz5
      have hdvd2 : (2 : ℕ) ∣ 5 := by
        have := orderOf_dvd_of_pow_eq_one hz5
        rwa [DihedralGroup.orderOf_sr] at this
      omega
  have hrange : (φ.comp (Subgroup.inclusion hHM)).range = TauCeti.dihedralRotations 5 := by
    refine Subgroup.eq_of_le_of_card_ge hrangeRot ?_
    rw [TauCeti.card_dihedralRotations, himgcard]
  intro hgRot
  have hmemRange : φ ⟨g, hgM⟩ ∈ (φ.comp (Subgroup.inclusion hHM)).range := by
    rw [hrange]
    exact hgRot
  rcases hmemRange with ⟨h, hh⟩
  have hkerMem : (⟨g, hgM⟩ * (Subgroup.inclusion hHM h)⁻¹) ∈ φ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv]
    have hh' : φ ((Subgroup.inclusion hHM) h) = φ ⟨g, hgM⟩ := hh
    rw [hh']
    exact mul_inv_cancel _
  have hmemN : g * (h : G)⁻¹ ∈ N := by
    rw [hker] at hkerMem
    exact Subgroup.mem_subgroupOf.mp hkerMem
  have hmemH : g * (h : G)⁻¹ ∈ H := hNleH hmemN
  have hgH : g ∈ H := by
    have h1 : (g * (h : G)⁻¹) * (h : G) ∈ H := H.mul_mem hmemH h.2
    have h2 : (g * (h : G)⁻¹) * (h : G) = g := by group
    rwa [h2] at h1
  have hgNL : g ∈ Subgroup.normalizer (L : Set G) := hgH.2
  have hLmap : L.map (MulAut.conj g).toMonoidHom = L :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hgNL
  rw [hLg] at hLmap
  exact hLKne hLmap.symm

theorem lines_of_case8100Four (D : Data G)
    {V₀ V L X : Subgroup G} {p n l r : ℕ} {C Dc : Subgroup G} {Gamma : Set G} {x : G}
    {A₀ A B : Subgroup G}
    (hV₀ : V₀ ≠ ⊥) (ctx : Ctx17_42 D V₀ V L X p n l C Dc Gamma)
    (h8100 : F08.Hyp8100 D ![L, conjSubgroup L x] ![n, n] r p A₀ X)
    (hc4 : F08.Case8100FourR D ![L, conjSubgroup L x] p X)
    (hAsyl : CFSG.ABGLocalTools.IsSylowOf r A X) (hAT : Permutes A D.T) (hBM : B ≤ D.M)
    (hBcard : Nat.card B = p) (hAB : ⁅A, B⁆ = A) (hBT : Permutes B D.T) :
    ∀ D' : Subgroup G, D' ≤ A → Nat.card D' = 31 → B ≤ normalizer (D' : Set G) →
      D' = A ⊓ L ∨ D' = A ⊓ conjSubgroup L x := by
  classical
  have hL11 := factors_of_case8100Four D hV₀ ctx h8100 hc4 hAsyl hAT hBM hBcard hAB hBT
  obtain ⟨hA₁card, hA₂card, hcent, hinf, hBcard5, hBn₁, hBn₂, hAeq, hfixfree⟩ := hL11
  have h8100' := h8100
  have hc4' := hc4
  obtain ⟨hLcal, hLKne0, hshape, hr, hrdvd, hpSig, -, -, hXprod, hMNX⟩ := h8100
  have hshape0 : IsL2 (Bar2 L) n ∨ IsSz (Bar2 L) n := hshape 0
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Nat.gcd_self] at hrdvd
  obtain ⟨hset0, hSzL, hp5, -, φ, hφ, hker⟩ := hc4
  subst p
  set K : Subgroup G := conjSubgroup L x with hKdef
  have hLKne : L ≠ K := by
    simpa [hKdef, Matrix.cons_val_zero, Matrix.cons_val_one] using hLKne0
  have hSzL' : IsSz (Bar2 L) 5 := hSzL
  have hset : ({L, K} : Set (Subgroup G)) = conjSetOf D.M L := by
    simpa [conjSetOf, hKdef, Matrix.cons_val_zero, Matrix.cons_val_one] using hset0
  have hXprod' : (X : Set G) = (L : Set G) * (K : Set G) := by
    simpa [hKdef, Matrix.cons_val_zero, Matrix.cons_val_one] using hXprod
  have hXeq : X = L ⊔ K := by
    refine le_antisymm ?_ ?_
    · intro z hz
      have hz' : z ∈ (L : Set G) * (K : Set G) := by rwa [← hXprod']
      obtain ⟨a, ha, b, hb, rfl⟩ := hz'
      exact Subgroup.mul_mem_sup ha hb
    · refine sup_le ?_ ?_
      · intro a ha
        have h : a ∈ (L : Set G) * (K : Set G) := ⟨a, ha, 1, K.one_mem, by simp⟩
        change a ∈ (X : Set G)
        rw [hXprod']
        exact h
      · intro b hb
        have h : b ∈ (L : Set G) * (K : Set G) := ⟨1, L.one_mem, b, hb, by simp⟩
        change b ∈ (X : Set G)
        rw [hXprod']
        exact h
  have hLcalM : L ∈ calC D.M := by simpa using hLcal 0
  have hKconj : K ∈ conjSetOf D.M L := by
    rw [← hset]; exact Set.mem_insert_iff.mpr (Or.inr rfl)
  have hKcalM : K ∈ calC D.M := uc22p2214_calC_of_mem_conjSetOf hLcalM hKconj
  have hLM : L ≤ D.M := s13_le_of_mem_calC hLcalM
  have hKM : K ≤ D.M := s13_le_of_mem_calC hKcalM
  have hXM : X ≤ D.M := by rw [hXeq]; exact sup_le hLM hKM
  have hMX : D.M ≤ Subgroup.normalizer (X : Set G) := hMNX
  obtain ⟨-, -, hsubset⟩ := conjSetOf_subset_calC_conjClosure (M := D.M) hLcalM
  have hLmemSelf : L ∈ conjSetOf D.M L := by
    refine ⟨1, D.M.one_mem, ?_⟩
    ext z
    simp [MulAut.conj_apply]
  have hLcalX : L ∈ calC X := by
    rw [ctx.X_eq]; exact hsubset L hLmemSelf
  have hKcalX : K ∈ calC X := by
    rw [ctx.X_eq]; exact hsubset K hKconj
  have hn5 : n = 5 := by
    rcases hshape0 with hN | hN
    · exact (CFSG.LocalAnalysis.UniquenessCase.UC22.P2214S.false_of_isSz_of_isL2 hSzL hN).elim
    · exact eq_five_of_isSz_five hN hSzL
  have hr31 : r = 31 := by
    have hdvd31 : r ∣ 31 := by simpa [hn5] using hrdvd
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 31)).mp hdvd31 with h | h
    · exact absurd h hr.ne_one
    · exact h
  haveI : Fact (Nat.Prime 31) := ⟨by norm_num⟩
  have hAsyl31 : CFSG.ABGLocalTools.IsSylowOf 31 A X := by
    rw [← hr31]; exact hAsyl
  have hXfact : (Nat.card X).factorization 31 = 2 := by
    have h := (borel_order_data_of_case34 ctx h8100' (Or.inr hc4')).2.2.2
    rwa [hr31] at h
  have hAcard : Nat.card A = 31 ^ 2 := by
    rw [hAsyl31.card_eq, hXfact]
  have hLX : L ≤ X := by rw [hXeq]; exact le_sup_left
  have hKX : K ≤ X := by rw [hXeq]; exact le_sup_right
  have hLnormX : (L.subgroupOf X).Normal := by
    rw [ctx.X_eq]
    exact component_normal_in_conjClosure hLcalM
  have hXLnorm : X ≤ Subgroup.normalizer (L : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLX).mp hLnormX
  have hKnormX : (K.subgroupOf X).Normal := by
    have hKcCompX : K ∈ CFSG.Quasithin.cComp X := uc22p20e_cComp_of_calC hKcalX
    have hspanX : CFSG.Quasithin.cCompSpan X = X := by
      rw [ctx.X_eq]; exact cCompSpan_conjClosure ctx.mem_calC
    have hKspan : (K.subgroupOf (CFSG.Quasithin.cCompSpan X)).Normal :=
      (CFSG.Quasithin.cComp_normal_span_of_le hKcCompX).2
    rwa [hspanX] at hKspan
  have hXKnorm : X ≤ Subgroup.normalizer (K : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKX).mp hKnormX
  have hKconj' := hKconj
  obtain ⟨m, hmM, hmK⟩ := hKconj'
  have hSzK : IsSz (Bar2 K) 5 := by
    obtain ⟨eKL⟩ := uc22p20d_bar2_conj m L
    have hKuc : K = uc22p20bCj m L := by rw [hmK, uc22p20bCj]
    rw [← hKuc] at eKL
    exact CFSG.Blueprint.LieModel.of_mulEquiv eKL hSzL
  have hZbarL : Subgroup.center (Bar2 L) = ⊥ := center_eq_bot_of_isSz_five hSzL'
  obtain ⟨eL, -⟩ := uc22p22l_barImage_equiv (L := X) (K := L) hLcalX
  have hZimgL : Subgroup.center ↥(barImage X L) = ⊥ := by
    have hc : Nat.card ↥(Subgroup.center ↥(barImage X L)) = 1 := by
      rw [← Nat.card_congr (Subgroup.centerCongr eL).toEquiv, hZbarL, Subgroup.card_bot]
    exact (Subgroup.card_eq_one).mp hc
  obtain ⟨eK, -⟩ := uc22p22l_barImage_equiv (L := X) (K := K) hKcalX
  have hZimgK : Subgroup.center ↥(barImage X K) = ⊥ := by
    have hc : Nat.card ↥(Subgroup.center ↥(barImage X K)) = 1 := by
      rw [← Nat.card_congr (Subgroup.centerCongr eK).toEquiv]
      have hZbarK : Subgroup.center (Bar2 K) = ⊥ := center_eq_bot_of_isSz_five hSzK
      rw [hZbarK, Subgroup.card_bot]
    exact (Subgroup.card_eq_one).mp hc
  have hsetK : ({K, L} : Set (Subgroup G)) = conjSetOf D.M K := by
    have hEqK := uc22p2214_conjSetOf_eq hKconj
    rw [hEqK]
    rw [show ({K, L} : Set (Subgroup G)) = ({L, K} : Set (Subgroup G)) from by
      ext z; simp [or_comm]]
    exact hset
  have hNleL : X ⊔ F08.CentOverO2 D.M X ≤ Subgroup.normalizer (L : Set G) :=
    sup_centOverO2_le_normalizer_of_component hXM hMX hXeq hLKne hset hLcalX hKcalX hZimgL
  have hNleK : X ⊔ F08.CentOverO2 D.M X ≤ Subgroup.normalizer (K : Set G) :=
    sup_centOverO2_le_normalizer_of_component hXM hMX (by rw [hXeq, sup_comm])
      hLKne.symm hsetK hKcalX hLcalX hZimgK
  have hA31 : IsPGroup 31 ↥A := hAsyl31.isPGroup
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hO2L : IsPGroup 2 ↥(CFSG.Open.pCoreOf 2 L) :=
    CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L
  have hO2K : IsPGroup 2 ↥(CFSG.Open.pCoreOf 2 K) :=
    CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K
  have hAdisjL : A ⊓ CFSG.Open.pCoreOf 2 L = ⊥ :=
    (IsPGroup.disjoint_of_ne 31 2 (by norm_num) A (CFSG.Open.pCoreOf 2 L) hA31 hO2L).eq_bot
  have hAdisjK : A ⊓ CFSG.Open.pCoreOf 2 K = ⊥ :=
    (IsPGroup.disjoint_of_ne 31 2 (by norm_num) A (CFSG.Open.pCoreOf 2 K) hA31 hO2K).eq_bot
  have hA₁leA : A ⊓ L ≤ A := inf_le_left
  have hA₂leA : A ⊓ K ≤ A := inf_le_left
  have hA₁disj : (A ⊓ L) ⊓ CFSG.Open.pCoreOf 2 L = ⊥ := by
    have hle : (A ⊓ L) ⊓ CFSG.Open.pCoreOf 2 L ≤ A ⊓ CFSG.Open.pCoreOf 2 L := by
      intro x hx
      exact ⟨hx.1.1, hx.2⟩
    rw [hAdisjL] at hle
    exact le_bot_iff.mp hle
  have hA₂disj : (A ⊓ K) ⊓ CFSG.Open.pCoreOf 2 K = ⊥ := by
    have hle : (A ⊓ K) ⊓ CFSG.Open.pCoreOf 2 K ≤ A ⊓ CFSG.Open.pCoreOf 2 K := by
      intro x hx
      exact ⟨hx.1.1, hx.2⟩
    rw [hAdisjK] at hle
    exact le_bot_iff.mp hle
  obtain ⟨yb, hybord⟩ := exists_prime_orderOf_dvd_card' (G := ↥B) 5 (by rw [hBcard5])
  let y : G := yb
  have hyB : y ∈ B := yb.2
  have hyord : orderOf y = 5 := by
    rw [Subgroup.orderOf_coe]
    exact hybord
  have hBzp : Subgroup.zpowers y = B := by
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hyB) ?_
    rw [Nat.card_zpowers, hyord, hBcard5]
  have hBA : B ≤ Subgroup.normalizer (A : Set G) := by
    rw [Subgroup.le_normalizer_iff_commutator_le_left, hAB]
  have hyA : y ∈ Subgroup.normalizer (A : Set G) := hBA hyB
  have hact₂ : ∀ n : G, n ∈ X ⊔ F08.CentOverO2 D.M X →
      n ∈ Subgroup.normalizer ((A ⊓ K : Subgroup G) : Set G) →
      (∀ a ∈ A ⊓ K, n * a * n⁻¹ = a) ∨
        (∀ a ∈ A ⊓ K, n * a * n⁻¹ = a⁻¹) := by
    intro n hnN hnA₂
    exact action_on_line_of_mem_sup_centOverO2 (D := D) (X := X) (L := L) (K := K)
      (A₂ := A ⊓ K) (φ := φ) hXM hMX hXeq hLKne hLcalM hKcalM hLcalX hKcalX
      hNleK hker hSzK inf_le_right hA₂card hA₂disj hnN hnA₂
  have hact₁ : ∀ n : G, n ∈ X ⊔ F08.CentOverO2 D.M X →
      n ∈ Subgroup.normalizer ((A ⊓ L : Subgroup G) : Set G) →
      (∀ a ∈ A ⊓ L, n * a * n⁻¹ = a) ∨
        (∀ a ∈ A ⊓ L, n * a * n⁻¹ = a⁻¹) := by
    intro n hnN hnA₂
    exact action_on_line_of_mem_sup_centOverO2 (D := D) (X := X) (L := K) (K := L)
      (A₂ := A ⊓ L) (φ := φ) hXM hMX (by rw [hXeq, sup_comm]) hLKne.symm
      hKcalM hLcalM hKcalX hLcalX hNleL hker hSzL' inf_le_right hA₁card hA₁disj
      hnN hnA₂
  have hyN : y ∉ X ⊔ F08.CentOverO2 D.M X := by
    intro hyN
    have hycent₁ : y ∈ Subgroup.centralizer ((A ⊓ L : Subgroup G) : Set G) := by
      rcases hact₁ y hyN (hBn₁ hyB) with h | h
      · rw [Subgroup.mem_centralizer_iff]
        intro a ha
        have hcomm : y * a = a * y := by
          have := congrArg (fun z => z * y) (h a ha)
          simpa [mul_assoc] using this
        exact hcomm.symm
      · have h2g : ∀ a ∈ (A ⊓ L : Subgroup G), y ^ 2 * a * (y ^ 2)⁻¹ = a := by
          intro a ha
          calc y ^ 2 * a * (y ^ 2)⁻¹ = y * (y * a * y⁻¹) * y⁻¹ := by
                rw [pow_two]
                group
            _ = y * a⁻¹ * y⁻¹ := by rw [h a ha]
            _ = (y * a * y⁻¹)⁻¹ := by group
            _ = (a⁻¹)⁻¹ := by rw [h a ha]
            _ = a := inv_inv a
        have hy2 : y ^ 2 ∈ Subgroup.centralizer ((A ⊓ L : Subgroup G) : Set G) := by
          rw [Subgroup.mem_centralizer_iff]
          intro b hb
          have hcomm : y ^ 2 * b = b * y ^ 2 := by
            have := congrArg (fun z => z * y ^ 2) (h2g b hb)
            simpa [mul_assoc] using this
          exact hcomm.symm
        have hy_eq : y = (y ^ 2) ^ 3 := by
          have h5 : y ^ 5 = 1 := by
            rw [← hyord]
            exact pow_orderOf_eq_one y
          calc y = y ^ 6 := by
                rw [show y ^ 6 = y ^ 5 * y by group, h5, one_mul]
            _ = (y ^ 2) ^ 3 := by group
        rw [Subgroup.mem_centralizer_iff]
        intro a ha
        rw [hy_eq]
        exact (Subgroup.mem_centralizer_iff.mp (Subgroup.pow_mem _ hy2 3)) a ha
    have hycent₂ : y ∈ Subgroup.centralizer ((A ⊓ K : Subgroup G) : Set G) := by
      rcases hact₂ y hyN (hBn₂ hyB) with h | h
      · rw [Subgroup.mem_centralizer_iff]
        intro a ha
        have hcomm : y * a = a * y := by
          have := congrArg (fun z => z * y) (h a ha)
          simpa [mul_assoc] using this
        exact hcomm.symm
      · have h2g : ∀ a ∈ (A ⊓ K : Subgroup G), y ^ 2 * a * (y ^ 2)⁻¹ = a := by
          intro a ha
          calc y ^ 2 * a * (y ^ 2)⁻¹ = y * (y * a * y⁻¹) * y⁻¹ := by
                rw [pow_two]
                group
            _ = y * a⁻¹ * y⁻¹ := by rw [h a ha]
            _ = (y * a * y⁻¹)⁻¹ := by group
            _ = (a⁻¹)⁻¹ := by rw [h a ha]
            _ = a := inv_inv a
        have hy2 : y ^ 2 ∈ Subgroup.centralizer ((A ⊓ K : Subgroup G) : Set G) := by
          rw [Subgroup.mem_centralizer_iff]
          intro b hb
          have hcomm : y ^ 2 * b = b * y ^ 2 := by
            have := congrArg (fun z => z * y ^ 2) (h2g b hb)
            simpa [mul_assoc] using this
          exact hcomm.symm
        have hy_eq : y = (y ^ 2) ^ 3 := by
          have h5 : y ^ 5 = 1 := by
            rw [← hyord]
            exact pow_orderOf_eq_one y
          calc y = y ^ 6 := by
                rw [show y ^ 6 = y ^ 5 * y by group, h5, one_mul]
            _ = (y ^ 2) ^ 3 := by group
        rw [Subgroup.mem_centralizer_iff]
        intro a ha
        rw [hy_eq]
        exact (Subgroup.mem_centralizer_iff.mp (Subgroup.pow_mem _ hy2 3)) a ha
    have hBcent : B ≤ Subgroup.centralizer (A : Set G) := by
      rw [← hBzp]
      have hsup : Subgroup.zpowers y ≤
          Subgroup.centralizer (((A ⊓ L) ⊔ (A ⊓ K) : Subgroup G) : Set G) :=
        le_centralizer_sup_of_le_centralizers (Subgroup.zpowers_le.mpr hycent₁)
          (Subgroup.zpowers_le.mpr hycent₂)
      rwa [hAeq] at hsup
    have hABbot : ⁅A, B⁆ = ⊥ := by
      rw [Subgroup.commutator_comm]
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hBcent
    have hAbot : A = ⊥ := by
      rw [hAB] at hABbot
      exact hABbot
    have hcard1 : Nat.card A = 1 := by rw [hAbot, Subgroup.card_bot]
    rw [hAcard] at hcard1
    norm_num at hcard1
  have hAmSyl : CFSG.ABGLocalTools.IsSylowOf 31 (A.map (MulAut.conj m).toMonoidHom) X := by
    have hXm : Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj m)) X = X := by
      simpa using (Subgroup.mem_normalizer_iff_map_conj_eq.mp (hMX hmM))
    have h := CFSG.GroupTheory.isSylowOf_map_conj hAsyl31 m
    rw [hXm] at h
    exact h
  obtain ⟨k, hkX, hk⟩ := hAsyl31.exists_mem_conj hAmSyl
  have hAmEq : A.map (MulAut.conj m).toMonoidHom =
      A.map (MulAut.conj k).toMonoidHom := by
    ext x
    constructor
    · intro hx
      have hx' : k⁻¹ * x * k ∈ A := (hk x).mp hx
      refine Subgroup.mem_map.mpr ⟨k⁻¹ * x * k, hx', ?_⟩
      simp [MulAut.conj_apply]
      group
    · intro hx
      rcases Subgroup.mem_map.mp hx with ⟨a, ha, rfl⟩
      refine (hk (k * a * k⁻¹)).mpr ?_
      have hka : k⁻¹ * (k * a * k⁻¹) * k = a := by group
      simpa [hka] using ha
  have hXNL : X ≤ Subgroup.normalizer (L : Set G) := by
    rw [hXeq]
    exact sup_le (Subgroup.le_normalizer)
      (uc22p22u_calC_normalizes hLcalX hKcalX hLKne)
  have hXNK : X ≤ Subgroup.normalizer (K : Set G) := by
    rw [hXeq]
    exact sup_le (uc22p22u_calC_normalizes hKcalX hLcalX hLKne.symm)
      (Subgroup.le_normalizer)
  have hkL : k ∈ Subgroup.normalizer (L : Set G) := hXNL hkX
  have hkK : k ∈ Subgroup.normalizer (K : Set G) := hXNK hkX
  have hkKinv : K.map (MulAut.conj k⁻¹).toMonoidHom = K :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.inv_mem _ hkK)
  let g : G := k⁻¹ * m
  have hgM : g ∈ D.M := D.M.mul_mem (D.M.inv_mem (hXM hkX)) hmM
  have hcompg : (MulAut.conj g).toMonoidHom =
      ((MulAut.conj k⁻¹).toMonoidHom).comp ((MulAut.conj m).toMonoidHom) := by
    ext x
    simp [g, MulAut.conj_apply]
  have hAg : A.map (MulAut.conj g).toMonoidHom = A := by
    calc A.map (MulAut.conj g).toMonoidHom
        = A.map (((MulAut.conj k⁻¹).toMonoidHom).comp
            ((MulAut.conj m).toMonoidHom)) := by rw [hcompg]
      _ = (A.map (MulAut.conj m).toMonoidHom).map (MulAut.conj k⁻¹).toMonoidHom := by
            rw [← Subgroup.map_map]
      _ = (A.map (MulAut.conj k).toMonoidHom).map (MulAut.conj k⁻¹).toMonoidHom := by
            rw [hAmEq]
      _ = A.map (((MulAut.conj k⁻¹).toMonoidHom).comp
            ((MulAut.conj k).toMonoidHom)) := by
            rw [← Subgroup.map_map]
      _ = A := by
            have hid : ((MulAut.conj k⁻¹).toMonoidHom).comp
                ((MulAut.conj k).toMonoidHom) = MonoidHom.id G := by
              ext x
              simp [MulAut.conj_apply]
              group
            rw [hid, Subgroup.map_id]
  have hLg : L.map (MulAut.conj g).toMonoidHom = K := by
    calc L.map (MulAut.conj g).toMonoidHom
        = L.map (((MulAut.conj k⁻¹).toMonoidHom).comp
            ((MulAut.conj m).toMonoidHom)) := by rw [hcompg]
      _ = (L.map (MulAut.conj m).toMonoidHom).map (MulAut.conj k⁻¹).toMonoidHom := by
            rw [← Subgroup.map_map]
      _ = K.map (MulAut.conj k⁻¹).toMonoidHom := by rw [← hmK]
      _ = K := hkKinv
  have hKg : K.map (MulAut.conj g).toMonoidHom = L := by
    have hmemK : K.map (MulAut.conj g).toMonoidHom ∈ conjSetOf D.M K :=
      ⟨g, hgM, rfl⟩
    have hmem : K.map (MulAut.conj g).toMonoidHom ∈ ({L, K} : Set (Subgroup G)) := by
      rw [← hsetK] at hmemK
      simpa [or_comm] using hmemK
    have hcases : K.map (MulAut.conj g).toMonoidHom = L ∨
        K.map (MulAut.conj g).toMonoidHom = K := by simpa using hmem
    rcases hcases with h | h
    · exact h
    · exfalso
      exact hLKne (Subgroup.map_injective (f := (MulAut.conj g).toMonoidHom)
        (MulAut.conj g).injective (by rw [hLg, h]))
  have hA₁map : (A ⊓ L).map (MulAut.conj g).toMonoidHom = A ⊓ K := by
    rw [Subgroup.map_inf _ _ _ (MulAut.conj g).injective, hAg, hLg]
  have hA₂map : (A ⊓ K).map (MulAut.conj g).toMonoidHom = A ⊓ L := by
    rw [Subgroup.map_inf _ _ _ (MulAut.conj g).injective, hAg, hKg]
  have hyM : y ∈ D.M := hBM hyB
  have hφy_ne : φ ⟨y, hyM⟩ ≠ 1 := by
    intro h1
    apply hyN
    have hmem : ⟨y, hyM⟩ ∈ φ.ker := MonoidHom.mem_ker.mpr h1
    rw [hker] at hmem
    exact Subgroup.mem_subgroupOf.mp hmem
  have hφy_dvd : orderOf (φ ⟨y, hyM⟩) ∣ 5 := by
    have h := orderOf_map_dvd φ ⟨y, hyM⟩
    rwa [Subgroup.orderOf_mk, hyord] at h
  have hφy_ord : orderOf (φ ⟨y, hyM⟩) = 5 := by
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 5)).mp hφy_dvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hφy_ne
    · exact h
  have hφy_rot : φ ⟨y, hyM⟩ ∈ TauCeti.dihedralRotations 5 := by
    rw [TauCeti.mem_dihedralRotations_iff]
    by_contra h
    push Not at h
    rcases hd : φ ⟨y, hyM⟩ with i | i
    · exact h i hd
    · rw [hd] at hφy_ord
      rw [DihedralGroup.orderOf_sr] at hφy_ord
      omega
  have hNleM : X ⊔ F08.CentOverO2 D.M X ≤ D.M := by
    refine sup_le hXM ?_
    intro c hc
    exact (mem_centOverO2_iff.mp hc).1
  have hMLrel : (D.M ⊓ Subgroup.normalizer (L : Set G)).relIndex D.M = 2 :=
    s17_45_relIndex_inf_normalizer_eq_two (by rw [← hset]; simp [hLKne])
  have hφg_not_rot : φ ⟨g, hgM⟩ ∉ TauCeti.dihedralRotations 5 :=
    phi_not_rotations_of_map_conj_eq (D := D) (X := X) hNleM hNleL hker hφ hMLrel hgM hLg hLKne
  let h : G := g * y * g⁻¹ * y
  have hhM : h ∈ D.M := by
    exact D.M.mul_mem (D.M.mul_mem (D.M.mul_mem hgM hyM) (D.M.inv_mem hgM)) hyM
  have hgA : g ∈ Subgroup.normalizer (A : Set G) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr hAg
  have hhA : h ∈ Subgroup.normalizer (A : Set G) := by
    have hstruct : h = (g * y * g⁻¹) * y := rfl
    rw [hstruct]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _
      (Subgroup.mul_mem _ hgA hyA) (Subgroup.inv_mem _ hgA)) hyA
  have hφg_conj : φ ⟨g, hgM⟩ * φ ⟨y, hyM⟩ * (φ ⟨g, hgM⟩)⁻¹ =
      (φ ⟨y, hyM⟩)⁻¹ :=
    TauCeti.conj_eq_inv_of_notMem_dihedralRotations hφg_not_rot hφy_rot
  have hφh : φ ⟨h, hhM⟩ = 1 := by
    have harg : (⟨h, hhM⟩ : ↥D.M) =
        ⟨g, hgM⟩ * ⟨y, hyM⟩ * ⟨g, hgM⟩⁻¹ * ⟨y, hyM⟩ := Subtype.ext rfl
    rw [harg, map_mul, map_mul, map_mul, map_inv, hφg_conj]
    group
  have hhN : h ∈ X ⊔ F08.CentOverO2 D.M X := by
    have hmem : ⟨h, hhM⟩ ∈ φ.ker := MonoidHom.mem_ker.mpr hφh
    rw [hker] at hmem
    exact Subgroup.mem_subgroupOf.mp hmem
  have hhK : h ∈ Subgroup.normalizer (K : Set G) := hNleK hhN
  have hA₂norm : h ∈ Subgroup.normalizer ((A ⊓ K : Subgroup G) : Set G) :=
    CFSG.ABGLocalTools.mem_normalizer_inf hhA hhK
  have hhact₂ := hact₂ h hhN hA₂norm
  obtain ⟨a₁, ha₁⟩ := exists_prime_orderOf_dvd_card' (G := ↥(A ⊓ L)) 31 (by rw [hA₁card])
  obtain ⟨a₂, ha₂⟩ := exists_prime_orderOf_dvd_card' (G := ↥(A ⊓ K)) 31 (by rw [hA₂card])
  have ha1ord : orderOf (a₁ : G) = 31 := by
    rw [Subgroup.orderOf_coe]
    exact ha₁
  have ha2ord : orderOf (a₂ : G) = 31 := by
    rw [Subgroup.orderOf_coe]
    exact ha₂
  have hA₁zp : A ⊓ L = Subgroup.zpowers (a₁ : G) := by
    symm
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr a₁.2) ?_
    rw [Nat.card_zpowers, ha1ord, hA₁card]
  have hA₂zp : A ⊓ K = Subgroup.zpowers (a₂ : G) := by
    symm
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr a₂.2) ?_
    rw [Nat.card_zpowers, ha2ord, hA₂card]
  have hya₁ : y * (a₁ : G) * y⁻¹ ∈ A ⊓ L :=
    (Subgroup.mem_normalizer_iff.mp (hBn₁ hyB) (a₁ : G)).mp a₁.2
  have hya₁' : y * (a₁ : G) * y⁻¹ ∈ Subgroup.zpowers (a₁ : G) := by
    rw [← hA₁zp]
    exact hya₁
  obtain ⟨c₁, hc₁⟩ := Subgroup.mem_zpowers_iff.mp hya₁'
  have hc₁y : y * (a₁ : G) * y⁻¹ = (a₁ : G) ^ c₁ := hc₁.symm
  have hya₂ : y * (a₂ : G) * y⁻¹ ∈ A ⊓ K :=
    (Subgroup.mem_normalizer_iff.mp (hBn₂ hyB) (a₂ : G)).mp a₂.2
  have hya₂' : y * (a₂ : G) * y⁻¹ ∈ Subgroup.zpowers (a₂ : G) := by
    rw [← hA₂zp]
    exact hya₂
  obtain ⟨c₂, hc₂⟩ := Subgroup.mem_zpowers_iff.mp hya₂'
  have hc₂y : y * (a₂ : G) * y⁻¹ = (a₂ : G) ^ c₂ := hc₂.symm
  have hc1pow : c₁ ^ 5 ≡ 1 [ZMOD 31] := by
    have h := CFSG.RankThree.PartOne.pow_conj_eq_zpow hc₁y 5
    have hy5 : y ^ 5 = 1 := by
      rw [← hyord]
      exact pow_orderOf_eq_one y
    rw [hy5] at h
    simp at h
    have h2 : (a₁ : G) ^ (c₁ ^ 5) = (a₁ : G) ^ (1 : ℤ) := by
      rw [← h]
      simp
    have hmod := (zpow_eq_zpow_iff_modEq).mp h2
    rwa [ha1ord] at hmod
  have hc2pow : c₂ ^ 5 ≡ 1 [ZMOD 31] := by
    have h := CFSG.RankThree.PartOne.pow_conj_eq_zpow hc₂y 5
    have hy5 : y ^ 5 = 1 := by
      rw [← hyord]
      exact pow_orderOf_eq_one y
    rw [hy5] at h
    simp at h
    have h2 : (a₂ : G) ^ (c₂ ^ 5) = (a₂ : G) ^ (1 : ℤ) := by
      rw [← h]
      simp
    have hmod := (zpow_eq_zpow_iff_modEq).mp h2
    rwa [ha2ord] at hmod
  have hc₁_ne : ¬ c₁ ≡ 1 [ZMOD 31] := by
    intro hc
    have hc' : c₁ ≡ 1 [ZMOD orderOf (a₁ : G)] := by simpa [ha1ord] using hc
    have hpow : (a₁ : G) ^ c₁ = (a₁ : G) ^ (1 : ℤ) :=
      (zpow_eq_zpow_iff_modEq).mpr hc'
    have hfix : y * (a₁ : G) * y⁻¹ = (a₁ : G) := by
      rw [hc₁y, hpow]
      simp
    have hcomm : (a₁ : G) * y = y * (a₁ : G) := by
      have := congrArg (fun z => z * y) hfix
      simpa [mul_assoc] using this.symm
    have hyne : y ≠ 1 := by
      intro h1
      rw [h1, orderOf_one] at hyord
      omega
    have hmem : (a₁ : G) ∈ (A ⊓ L) ⊔ (A ⊓ K) := Subgroup.mem_sup_left a₁.2
    have hone := hfixfree y hyB hyne (a₁ : G) hmem hcomm
    rw [hone, orderOf_one] at ha1ord
    omega
  have hc₂_ne : ¬ c₂ ≡ 1 [ZMOD 31] := by
    intro hc
    have hc' : c₂ ≡ 1 [ZMOD orderOf (a₂ : G)] := by simpa [ha2ord] using hc
    have hpow : (a₂ : G) ^ c₂ = (a₂ : G) ^ (1 : ℤ) :=
      (zpow_eq_zpow_iff_modEq).mpr hc'
    have hfix : y * (a₂ : G) * y⁻¹ = (a₂ : G) := by
      rw [hc₂y, hpow]
      simp
    have hcomm : (a₂ : G) * y = y * (a₂ : G) := by
      have := congrArg (fun z => z * y) hfix
      simpa [mul_assoc] using this.symm
    have hyne : y ≠ 1 := by
      intro h1
      rw [h1, orderOf_one] at hyord
      omega
    have hmem : (a₂ : G) ∈ (A ⊓ L) ⊔ (A ⊓ K) := Subgroup.mem_sup_right a₂.2
    have hone := hfixfree y hyB hyne (a₂ : G) hmem hcomm
    rw [hone, orderOf_one] at ha2ord
    omega
  let b : G := g * (a₁ : G) * g⁻¹
  have hb₂ : b ∈ A ⊓ K := by
    rw [← hA₁map]
    exact Subgroup.mem_map.mpr ⟨(a₁ : G), a₁.2, rfl⟩
  have hbord : orderOf b = 31 := by
    have := orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective (a₁ : G)
    simpa [b, MulAut.conj_apply, ha1ord] using this
  have hbzp : A ⊓ K = Subgroup.zpowers b := by
    symm
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hb₂) ?_
    rw [Nat.card_zpowers, hbord, hA₂card]
  obtain ⟨u, hu⟩ := Subgroup.mem_zpowers_iff.mp (by rw [← hbzp]; exact a₂.2)
  have hgy_b : (g * y * g⁻¹) * b * (g * y * g⁻¹)⁻¹ = b ^ c₁ := by
    calc (g * y * g⁻¹) * b * (g * y * g⁻¹)⁻¹
        = g * (y * (a₁ : G) * y⁻¹) * g⁻¹ := by
            simp [b]
            group
      _ = g * (a₁ : G) ^ c₁ * g⁻¹ := by rw [hc₁y]
      _ = (g * (a₁ : G) * g⁻¹) ^ c₁ := by
            simpa [MulAut.conj_apply] using (map_zpow (MulAut.conj g) (a₁ : G) c₁)
      _ = b ^ c₁ := by simp [b]
  have hgy_a₂ : (g * y * g⁻¹) * (a₂ : G) * (g * y * g⁻¹)⁻¹ = (a₂ : G) ^ c₁ := by
    have h1 : (MulAut.conj (g * y * g⁻¹)) (a₂ : G) = (a₂ : G) ^ c₁ := by
      rw [← hu, map_zpow,
        show (MulAut.conj (g * y * g⁻¹)) b = b ^ c₁ by
          change (g * y * g⁻¹) * b * (g * y * g⁻¹)⁻¹ = b ^ c₁
          exact hgy_b,
        ← zpow_mul, ← zpow_mul, mul_comm]
    change (MulAut.conj (g * y * g⁻¹)) (a₂ : G) = (a₂ : G) ^ c₁
    exact h1
  have hh_a₂ : h * (a₂ : G) * h⁻¹ = (a₂ : G) ^ (c₁ * c₂) := by
    have hexp : h = (g * y * g⁻¹) * y := rfl
    rw [hexp]
    calc ((g * y * g⁻¹) * y) * (a₂ : G) * ((g * y * g⁻¹) * y)⁻¹
        = (g * y * g⁻¹) * (y * (a₂ : G) * y⁻¹) * (g * y * g⁻¹)⁻¹ := by group
      _ = (g * y * g⁻¹) * (a₂ : G) ^ c₂ * (g * y * g⁻¹)⁻¹ := by rw [hc₂y]
      _ = ((g * y * g⁻¹) * (a₂ : G) * (g * y * g⁻¹)⁻¹) ^ c₂ := by
            change (MulAut.conj (g * y * g⁻¹)) ((a₂ : G) ^ c₂) =
              ((MulAut.conj (g * y * g⁻¹)) (a₂ : G)) ^ c₂
            exact map_zpow (MulAut.conj (g * y * g⁻¹)) (a₂ : G) c₂
      _ = ((a₂ : G) ^ c₁) ^ c₂ := by rw [hgy_a₂]
      _ = (a₂ : G) ^ (c₁ * c₂) := by rw [← zpow_mul]
  have hprod : c₁ * c₂ ≡ 1 [ZMOD 31] ∨ c₁ * c₂ ≡ -1 [ZMOD 31] := by
    rcases hhact₂ with hsign | hsign
    · left
      have h1 : (a₂ : G) ^ (c₁ * c₂) = (a₂ : G) ^ (1 : ℤ) := by
        rw [zpow_one, ← hh_a₂]
        exact hsign (a₂ : G) a₂.2
      have hmod := (zpow_eq_zpow_iff_modEq).mp h1
      rwa [ha2ord] at hmod
    · right
      have h1 : (a₂ : G) ^ (c₁ * c₂) = (a₂ : G) ^ (-1 : ℤ) := by
        rw [← hh_a₂, hsign (a₂ : G) a₂.2]
        simp
      have hmod := (zpow_eq_zpow_iff_modEq).mp h1
      rwa [ha2ord] at hmod
  have hc1z5 : ((c₁ : ZMod 31) ^ 5) = 1 := by
    have hcast : ((c₁ ^ 5 : ℤ) : ZMod 31) = ((1 : ℤ) : ZMod 31) :=
      (ZMod.intCast_eq_intCast_iff (c₁ ^ 5) 1 31).mpr hc1pow
    simpa [Int.cast_pow] using hcast
  have hc2z5 : ((c₂ : ZMod 31) ^ 5) = 1 := by
    have hcast : ((c₂ ^ 5 : ℤ) : ZMod 31) = ((1 : ℤ) : ZMod 31) :=
      (ZMod.intCast_eq_intCast_iff (c₂ ^ 5) 1 31).mpr hc2pow
    simpa [Int.cast_pow] using hcast
  have hc1z_ne : (c₁ : ZMod 31) ≠ 1 := by
    intro h
    apply hc₁_ne
    exact (ZMod.intCast_eq_intCast_iff c₁ 1 31).mp (by simpa using h)
  have hc2z_ne : (c₂ : ZMod 31) ≠ 1 := by
    intro h
    apply hc₂_ne
    exact (ZMod.intCast_eq_intCast_iff c₂ 1 31).mp (by simpa using h)
  have huv : ((c₁ : ZMod 31) * (c₂ : ZMod 31) = 1) ∨
      ((c₁ : ZMod 31) * (c₂ : ZMod 31) = -1) := by
    rcases hprod with h | h
    · left
      have := (ZMod.intCast_eq_intCast_iff (c₁ * c₂) 1 31).mpr h
      simpa [Int.cast_mul] using this
    · right
      have := (ZMod.intCast_eq_intCast_iff (c₁ * c₂) (-1) 31).mpr h
      simpa [Int.cast_mul] using this
  have hc_diff : (c₁ : ZMod 31) ≠ (c₂ : ZMod 31) := by
    intro heq
    have hsq : ((c₁ : ZMod 31) ^ 2 = 1) ∨ ((c₁ : ZMod 31) ^ 2 = -1) := by
      rcases huv with h | h
      · left
        rw [← heq] at h
        simpa [pow_two] using h
      · right
        rw [← heq] at h
        simpa [pow_two] using h
    have h4 : ((c₁ : ZMod 31) ^ 4) = 1 := by
      rcases hsq with h | h
      · calc ((c₁ : ZMod 31) ^ 4) = (((c₁ : ZMod 31) ^ 2) ^ 2) := by ring
          _ = 1 := by rw [h, one_pow]
      · calc ((c₁ : ZMod 31) ^ 4) = (((c₁ : ZMod 31) ^ 2) ^ 2) := by ring
          _ = (-1 : ZMod 31) ^ 2 := by rw [h]
          _ = 1 := by norm_num
    have h := hc1z5
    rw [show ((c₁ : ZMod 31) ^ 5) =
        ((c₁ : ZMod 31) ^ 4) * (c₁ : ZMod 31) by ring, h4, one_mul] at h
    exact hc1z_ne h
  intro D' hD'A hD'card hBD'
  classical
  obtain ⟨d₀, hd₀ord⟩ := exists_prime_orderOf_dvd_card' (G := ↥D') 31 (by rw [hD'card])
  have hd0ord : orderOf (d₀ : G) = 31 := by
    rw [Subgroup.orderOf_coe]
    exact hd₀ord
  have hD'zp : D' = Subgroup.zpowers (d₀ : G) := by
    symm
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr d₀.2) ?_
    rw [Nat.card_zpowers, hd0ord, hD'card]
  have hd0A : (d₀ : G) ∈ A := hD'A d₀.2
  have hAab : IsMulCommutative ↥A := IsPGroup.isMulCommutative_of_card_eq_prime_sq hAcard
  letI : CommGroup ↥A := IsMulCommutative.instCommGroup
  have hsupA : (A ⊓ L).subgroupOf A ⊔ (A ⊓ K).subgroupOf A = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hA₁leA hA₂leA, hAeq, Subgroup.subgroupOf_self]
  let d0A : ↥A := ⟨(d₀ : G), hd0A⟩
  have hd0A_mem : d0A ∈ (A ⊓ L).subgroupOf A ⊔ (A ⊓ K).subgroupOf A := by
    rw [hsupA]
    exact Subgroup.mem_top _
  obtain ⟨d₁A, hd₁A, d₂A, hd₂A, hd₁₂A⟩ := Subgroup.mem_sup.mp hd0A_mem
  let d₁ : G := d₁A
  let d₂ : G := d₂A
  have hd₁ : d₁ ∈ A ⊓ L := Subgroup.mem_subgroupOf.mp hd₁A
  have hd₂ : d₂ ∈ A ⊓ K := Subgroup.mem_subgroupOf.mp hd₂A
  have hd₁₂ : d₁ * d₂ = (d₀ : G) := by
    have h := congrArg Subtype.val hd₁₂A
    simpa [d₁, d₂, d0A] using h
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (by rwa [hA₁zp] at hd₁)
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (by rwa [hA₂zp] at hd₂)
  have hd0decomp : (d₀ : G) = (a₁ : G) ^ m * (a₂ : G) ^ n := by
    rw [← hd₁₂, hm, hn]
  have hyd₀_mem : y * (d₀ : G) * y⁻¹ ∈ D' :=
    (Subgroup.mem_normalizer_iff.mp (hBD' hyB) (d₀ : G)).mp d₀.2
  let d0G : G := (d₀ : G)
  have hyd₀_memD : y * d0G * y⁻¹ ∈ D' := by simpa [d0G] using hyd₀_mem
  have hD'zpG : (D' : Set G) = (Subgroup.zpowers d0G : Set G) := by
    rw [hD'zp]
  have hyd₀_memZ : y * d0G * y⁻¹ ∈ Subgroup.zpowers d0G := by
    have h : y * d0G * y⁻¹ ∈ (D' : Set G) := hyd₀_memD
    rw [hD'zpG] at h
    exact h
  obtain ⟨γ, hγ⟩ := Subgroup.mem_zpowers_iff.mp hyd₀_memZ
  have hγ' : (d₀ : G) ^ γ = y * (d₀ : G) * y⁻¹ := by simpa [d0G] using hγ
  have hcomm12 : Commute (a₁ : G) (a₂ : G) :=
    (Subgroup.mem_centralizer_iff.mp (hcent a₁.2) (a₂ : G) a₂.2).symm
  have hc₁' : (MulAut.conj y) (a₁ : G) = (a₁ : G) ^ c₁ := by
    simpa [MulAut.conj_apply] using hc₁y
  have hc₂' : (MulAut.conj y) (a₂ : G) = (a₂ : G) ^ c₂ := by
    simpa [MulAut.conj_apply] using hc₂y
  have hy_d0 : y * (d₀ : G) * y⁻¹ =
      (a₁ : G) ^ (c₁ * m) * (a₂ : G) ^ (c₂ * n) := by
    rw [hd0decomp]
    calc y * ((a₁ : G) ^ m * (a₂ : G) ^ n) * y⁻¹
        = (y * (a₁ : G) ^ m * y⁻¹) * (y * (a₂ : G) ^ n * y⁻¹) := by group
      _ = (((MulAut.conj y) (a₁ : G)) ^ m) *
            (((MulAut.conj y) (a₂ : G)) ^ n) := by
            rw [show y * (a₁ : G) ^ m * y⁻¹ = ((MulAut.conj y) (a₁ : G)) ^ m by
                  simpa [MulAut.conj_apply] using map_zpow (MulAut.conj y) (a₁ : G) m,
                show y * (a₂ : G) ^ n * y⁻¹ = ((MulAut.conj y) (a₂ : G)) ^ n by
                  simpa [MulAut.conj_apply] using map_zpow (MulAut.conj y) (a₂ : G) n]
      _ = ((a₁ : G) ^ c₁) ^ m * ((a₂ : G) ^ c₂) ^ n := by rw [hc₁', hc₂']
      _ = (a₁ : G) ^ (c₁ * m) * (a₂ : G) ^ (c₂ * n) := by
            rw [← zpow_mul, ← zpow_mul]
  have hd0pow : (d₀ : G) ^ γ = (a₁ : G) ^ (m * γ) * (a₂ : G) ^ (n * γ) := by
    rw [hd0decomp]
    rw [(hcomm12.zpow_zpow m n).mul_zpow γ]
    rw [← zpow_mul, ← zpow_mul]
  have hmain : (a₁ : G) ^ (c₁ * m) * (a₂ : G) ^ (c₂ * n) =
      (a₁ : G) ^ (m * γ) * (a₂ : G) ^ (n * γ) := by
    rw [← hy_d0, ← hγ', hd0pow]
  have heq : (a₁ : G) ^ (c₁ * m - m * γ) = (a₂ : G) ^ (n * γ - c₂ * n) :=
    CFSG.RankThree.PartTwo.Sec11.ActOnA.zpow_sub_eq_zpow_sub hmain
  have hleftA₁ : (a₁ : G) ^ (c₁ * m - m * γ) ∈ A ⊓ L :=
    (A ⊓ L).zpow_mem a₁.2 _
  have hrightA₂ : (a₂ : G) ^ (n * γ - c₂ * n) ∈ A ⊓ K :=
    (A ⊓ K).zpow_mem a₂.2 _
  have hleft_one : (a₁ : G) ^ (c₁ * m - m * γ) = 1 := by
    have hmem : (a₁ : G) ^ (c₁ * m - m * γ) ∈ (A ⊓ L) ⊓ (A ⊓ K) :=
      ⟨hleftA₁, by rw [heq]; exact hrightA₂⟩
    rw [hinf, Subgroup.mem_bot] at hmem
    exact hmem
  have hright_one : (a₂ : G) ^ (n * γ - c₂ * n) = 1 := by
    rw [← heq, hleft_one]
  have hmod1 : c₁ * m - m * γ ≡ 0 [ZMOD 31] := by
    have h1 : (a₁ : G) ^ (c₁ * m - m * γ) = (a₁ : G) ^ (0 : ℤ) := by
      rw [hleft_one]
      simp
    have hmod := (zpow_eq_zpow_iff_modEq).mp h1
    rwa [ha1ord] at hmod
  have hmod2 : n * γ - c₂ * n ≡ 0 [ZMOD 31] := by
    have h1 : (a₂ : G) ^ (n * γ - c₂ * n) = (a₂ : G) ^ (0 : ℤ) := by
      rw [hright_one]
      simp
    have hmod := (zpow_eq_zpow_iff_modEq).mp h1
    rwa [ha2ord] at hmod
  have hz1 : (c₁ : ZMod 31) * (m : ZMod 31) - (m : ZMod 31) * (γ : ZMod 31) = 0 := by
    have := (ZMod.intCast_eq_intCast_iff (c₁ * m - m * γ) 0 31).mpr hmod1
    simpa [Int.cast_sub, Int.cast_mul] using this
  have hz2 : (n : ZMod 31) * (γ : ZMod 31) - (c₂ : ZMod 31) * (n : ZMod 31) = 0 := by
    have := (ZMod.intCast_eq_intCast_iff (n * γ - c₂ * n) 0 31).mpr hmod2
    simpa [Int.cast_sub, Int.cast_mul] using this
  have hm_or_hn : (m : ZMod 31) = 0 ∨ (n : ZMod 31) = 0 := by
    by_contra h
    push Not at h
    obtain ⟨hm0, hn0⟩ := h
    have hcγ : (c₁ : ZMod 31) = (γ : ZMod 31) := by
      have h1 : (c₁ : ZMod 31) * (m : ZMod 31) = (γ : ZMod 31) * (m : ZMod 31) := by
        rw [mul_comm (γ : ZMod 31) (m : ZMod 31)]
        exact sub_eq_zero.mp hz1
      exact mul_right_cancel₀ hm0 h1
    have hγc : (γ : ZMod 31) = (c₂ : ZMod 31) := by
      have h1 : (γ : ZMod 31) * (n : ZMod 31) = (c₂ : ZMod 31) * (n : ZMod 31) := by
        rw [mul_comm (n : ZMod 31) (γ : ZMod 31)] at hz2
        exact sub_eq_zero.mp hz2
      exact mul_right_cancel₀ hn0 h1
    exact hc_diff (hcγ.trans hγc)
  rcases hm_or_hn with hm0 | hn0
  · right
    have hmz : m ≡ 0 [ZMOD 31] :=
      (ZMod.intCast_eq_intCast_iff m 0 31).mp (by simpa using hm0)
    have hmz1 : (a₁ : G) ^ m = 1 := by
      have h1 : (a₁ : G) ^ m = (a₁ : G) ^ (0 : ℤ) :=
        (zpow_eq_zpow_iff_modEq).mpr (by simpa [ha1ord] using hmz)
      simpa using h1
    have hd0eq : (d₀ : G) = (a₂ : G) ^ n := by
      rw [hd0decomp, hmz1, one_mul]
    have hd0A₂ : (d₀ : G) ∈ A ⊓ K := by
      rw [hd0eq]
      exact (A ⊓ K).zpow_mem a₂.2 n
    have hD'le : D' ≤ A ⊓ K := by
      rw [hD'zp]
      exact Subgroup.zpowers_le.mpr hd0A₂
    refine Subgroup.eq_of_le_of_card_ge hD'le ?_
    rw [hA₂card, hD'card]
  · left
    have hnz : n ≡ 0 [ZMOD 31] :=
      (ZMod.intCast_eq_intCast_iff n 0 31).mp (by simpa using hn0)
    have hnz1 : (a₂ : G) ^ n = 1 := by
      have h1 : (a₂ : G) ^ n = (a₂ : G) ^ (0 : ℤ) :=
        (zpow_eq_zpow_iff_modEq).mpr (by simpa [ha2ord] using hnz)
      simpa using h1
    have hd0eq : (d₀ : G) = (a₁ : G) ^ m := by
      rw [hd0decomp, hnz1, mul_one]
    have hd0A₁ : (d₀ : G) ∈ A ⊓ L := by
      rw [hd0eq]
      exact (A ⊓ L).zpow_mem a₁.2 m
    have hD'le : D' ≤ A ⊓ L := by
      rw [hD'zp]
      exact Subgroup.zpowers_le.mpr hd0A₁
    refine Subgroup.eq_of_le_of_card_ge hD'le ?_
    rw [hA₁card, hD'card]


end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.SzFive
