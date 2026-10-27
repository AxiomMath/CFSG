module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1Kernel

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

private theorem s16c1_commutator_eq_top_of_simple {S : Type} [Group S] [IsSimpleGroup S]
    (hnab : ∃ a b : S, a * b ≠ b * a) : commutator S = ⊤ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator S) with h | h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnab
    have hc : ⁅a, b⁆ ∈ commutator S := by
      rw [_root_.commutator_def]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
    rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hc
    exact hab hc
  · exact h

private theorem s16c1_commutator_quotient_eq_top {X : Type} [Group X] (N : Subgroup X)
    [N.Normal] (hA : UC22.IsAlt (X ⧸ N) 5) : commutator (X ⧸ N) = ⊤ := by
  obtain ⟨e⟩ := hA
  haveI : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup_five
  haveI : IsSimpleGroup (X ⧸ N) := e.isSimpleGroup
  refine s16c1_commutator_eq_top_of_simple ?_
  obtain ⟨a, b, hab⟩ :=
    (by decide : ∃ a b : alternatingGroup (Fin 5), a * b ≠ b * a)
  exact ⟨e.symm a, e.symm b, fun h => hab (by simpa using congrArg e h)⟩

private theorem s16c1_card_of_isElemAbelianOfRank {M : Type} [Group M]
    (h : IsElemAbelianOfRank 2 4 M) : Nat.card M = 16 := by
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv,
    Nat.card_congr (Multiplicative.toAdd : Multiplicative (Fin 4 → ZMod 2) ≃ (Fin 4 → ZMod 2)),
    Nat.card_fun, Nat.card_fin, Nat.card_zmod]
  norm_num

private theorem s16c1_card_fixedPoints_eq {X : Type} [Group X] (Y : Subgroup X) [Y.Normal]
    (x : X) :
    (letI : MulAction ↥(Subgroup.zpowers x) ↥Y :=
        MulAction.compHom ↥Y ((MulAut.conjNormal : X →* MulAut ↥Y).comp
          (Subgroup.zpowers x).subtype);
      Nat.card (MulAction.fixedPoints ↥(Subgroup.zpowers x) ↥Y)) =
      Nat.card ↥(Y ⊓ Subgroup.centralizer ({x} : Set X)) := by
  letI : MulAction ↥(Subgroup.zpowers x) ↥Y :=
    MulAction.compHom ↥Y ((MulAut.conjNormal : X →* MulAut ↥Y).comp
      (Subgroup.zpowers x).subtype)
  have hset : MulAction.fixedPoints ↥(Subgroup.zpowers x) (↥Y) =
      ((Y ⊓ Subgroup.centralizer ({x} : Set X)).subgroupOf Y : Set ↥Y) := by
    ext y
    rw [MulAction.mem_fixedPoints]
    change (∀ m : ↥(Subgroup.zpowers x), m • y = y) ↔
      y ∈ (Y ⊓ Subgroup.centralizer ({x} : Set X)).subgroupOf Y
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
    constructor
    · intro h
      have hxfix : MulAut.conjNormal x y = y := h ⟨x, Subgroup.mem_zpowers x⟩
      have hv : x * (y : X) * x⁻¹ = (y : X) := by
        simpa [MulAut.conjNormal_apply] using congrArg Subtype.val hxfix
      refine ⟨y.2, fun z hz => ?_⟩
      rw [Set.mem_singleton_iff] at hz
      rw [hz]
      calc x * (y : X) = (x * (y : X) * x⁻¹) * x := by group
        _ = (y : X) * x := by rw [hv]
    · rintro ⟨-, hcomm⟩ p
      have hle : Subgroup.zpowers x ≤
          Subgroup.comap MulAut.conjNormal (MulAction.stabilizer (MulAut ↥Y) y) := by
        rw [Subgroup.zpowers_le, Subgroup.mem_comap, MulAction.mem_stabilizer_iff]
        apply Subtype.ext
        rw [MulAut.smul_def, MulAut.conjNormal_apply]
        have hx := hcomm x (Set.mem_singleton x)
        rw [hx]
        group
      have hp := hle p.2
      rw [Subgroup.mem_comap, MulAction.mem_stabilizer_iff] at hp
      change (MulAut.conjNormal (p : X)) y = y
      exact hp
  rw [hset]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv

theorem s16c1_hyperplane {X : Type} [Group X] [Finite X] (N : Subgroup X) [N.Normal]
    (hN : IsElemAbelianOfRank 2 4 ↥N) (hA : UC22.IsAlt (X ⧸ N) 5) (hnp : commutator X ≠ ⊤) :
    ∃ N₁ : Subgroup X, N₁ ≤ N ∧ N₁.Normal ∧ Nat.card ↥N = 2 * Nat.card ↥N₁ := by
  classical
  have hcard : Nat.card ↥N = 16 := s16c1_card_of_isElemAbelianOfRank hN
  have hNn : N.Normal := inferInstance
  have hperf : commutator (X ⧸ N) = ⊤ := s16c1_commutator_quotient_eq_top N hA
  have hmap : (commutator X).map (QuotientGroup.mk' N) = commutator (X ⧸ N) := by
    simp only [_root_.commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)]
  have hcover : ∀ x : X, ∃ c ∈ commutator X, c⁻¹ * x ∈ N := by
    intro x
    have hx : QuotientGroup.mk' N x ∈ (commutator X).map (QuotientGroup.mk' N) := by
      rw [hmap, hperf]
      exact Subgroup.mem_top _
    rw [Subgroup.mem_map] at hx
    obtain ⟨c, hc, hcx⟩ := hx
    exact ⟨c, hc, QuotientGroup.eq.mp hcx⟩
  have hnotle : ¬ N ≤ commutator X := by
    intro hle
    apply hnp
    rw [eq_top_iff]
    intro x _
    obtain ⟨c, hc, hcx⟩ := hcover x
    have hx : x = c * (c⁻¹ * x) := by group
    rw [hx]
    exact (commutator X).mul_mem hc (hle hcx)
  set M₀ : Subgroup X := N ⊓ commutator X with hM₀
  have hM₀N : M₀ ≤ N := inf_le_left
  have hM₀X : M₀ ≤ commutator X := inf_le_right
  have hproper : M₀.subgroupOf N ≠ ⊤ := by
    intro htop
    rw [Subgroup.subgroupOf_eq_top] at htop
    exact hnotle (htop.trans hM₀X)
  haveI : Fintype ↥N := Fintype.ofFinite ↥N
  haveI : Fintype (Set ↥N) := Set.fintype
  haveI : Fintype (Subgroup ↥N) :=
    Fintype.ofInjective (fun H : Subgroup ↥N => (H : Set ↥N))
      (fun _ _ h => SetLike.coe_injective h)
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hNpg : IsPGroup 2 ↥N := IsPGroup.of_card (n := 4) (by rw [hcard]; norm_num)
  haveI : Group.IsNilpotent ↥N := hNpg.isNilpotent
  rcases IsCoatomic.eq_top_or_exists_le_coatom (M₀.subgroupOf N) with htop | ⟨C, hC, hle⟩
  · exact absurd htop hproper
  · have hCindex : C.index = 2 := (IsPGroup.isCoatom_iff_index_eq_prime hNpg).mp hC
    have hcardC : Nat.card ↥N = 2 * Nat.card ↥C := by
      rw [← Subgroup.index_mul_card C, hCindex]
    have hcardmap : Nat.card ↥(C.map N.subtype) = Nat.card ↥C :=
      Subgroup.card_map_of_injective (K := C) (f := N.subtype) N.subtype_injective
    have hnormal : (C.map N.subtype).Normal := by
      refine Subgroup.Normal.mk ?_
      intro n hn g
      rw [Subgroup.mem_map] at hn ⊢
      obtain ⟨c, hcC, rfl⟩ := hn
      refine ⟨MulAut.conjNormal g c, ?_, rfl⟩
      have hcommN : ⁅g, (c : X)⁆ ∈ N := by
        have hconj : g * (c : X) * g⁻¹ ∈ N := hNn.conj_mem (c : X) c.2 g
        rw [commutatorElement_def]
        exact N.mul_mem hconj (N.inv_mem c.2)
      have hcommM₀ : ⁅g, (c : X)⁆ ∈ M₀ := by
        refine ⟨hcommN, ?_⟩
        rw [_root_.commutator_def]
        exact Subgroup.commutator_mem_commutator (Subgroup.mem_top g) (Subgroup.mem_top (c : X))
      have hcommC : (⟨⁅g, (c : X)⁆, hcommN⟩ : ↥N) ∈ C :=
        hle (by rw [Subgroup.mem_subgroupOf]; exact hcommM₀)
      have hprod : (⟨⁅g, (c : X)⁆, hcommN⟩ : ↥N) * c ∈ C := C.mul_mem hcommC hcC
      convert hprod using 1
      apply Subtype.ext
      rw [MulAut.conjNormal_apply, Subgroup.coe_mul, ← MulAut.conj_apply,
        conj_eq_commutatorElement_mul]
    exact ⟨C.map N.subtype, Subgroup.map_subtype_le C, hnormal, by rw [hcardC, hcardmap]⟩

theorem s16c1_order_five_centralizes {X : Type} [Group X] [Finite X] (N N₁ : Subgroup X)
    [N.Normal] [N₁.Normal] (hN : IsElemAbelianOfRank 2 4 ↥N) (hN₁ : N₁ ≤ N)
    (hidx : Nat.card ↥N = 2 * Nat.card ↥N₁) {x : X} (hx : orderOf x = 5) :
    ∀ n ∈ N, x * n = n * x := by
  classical
  have hNcard : Nat.card ↥N = 16 := s16c1_card_of_isElemAbelianOfRank hN
  have hN₁card : Nat.card ↥N₁ = 8 := by omega
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hPcard : Nat.card ↥(Subgroup.zpowers x) = 5 := by
    rw [Nat.card_zpowers]
    exact hx
  have hPpg : IsPGroup 5 ↥(Subgroup.zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [hPcard]; norm_num)
  letI actN : MulAction ↥(Subgroup.zpowers x) ↥N :=
    MulAction.compHom ↥N ((MulAut.conjNormal : X →* MulAut ↥N).comp
      (Subgroup.zpowers x).subtype)
  letI actN₁ : MulAction ↥(Subgroup.zpowers x) ↥N₁ :=
    MulAction.compHom ↥N₁ ((MulAut.conjNormal : X →* MulAut ↥N₁).comp
      (Subgroup.zpowers x).subtype)
  have hD₁dvd : Nat.card ↥(N₁ ⊓ Subgroup.centralizer ({x} : Set X)) ∣ 8 := by
    have h := Subgroup.card_subgroup_dvd_card
      ((N₁ ⊓ Subgroup.centralizer ({x} : Set X)).subgroupOf N₁)
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv, hN₁card] at h
  have hmodN₁ : Nat.card ↥(N₁ ⊓ Subgroup.centralizer ({x} : Set X)) % 5 = 3 := by
    have h := hPpg.card_modEq_card_fixedPoints (↥N₁)
    rw [s16c1_card_fixedPoints_eq N₁ x, hN₁card] at h
    norm_num at h
    exact h.symm
  have hD₁eq : Nat.card ↥(N₁ ⊓ Subgroup.centralizer ({x} : Set X)) = 8 := by
    have hle : Nat.card ↥(N₁ ⊓ Subgroup.centralizer ({x} : Set X)) ≤ 8 :=
      Nat.le_of_dvd (by norm_num) hD₁dvd
    interval_cases Nat.card ↥(N₁ ⊓ Subgroup.centralizer ({x} : Set X)) <;> omega
  have hN₁cent : N₁ ≤ Subgroup.centralizer ({x} : Set X) := by
    have hcard_sub : Nat.card ↥((N₁ ⊓ Subgroup.centralizer ({x} : Set X)).subgroupOf N₁) = 8 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv, hD₁eq]
    have htop : (N₁ ⊓ Subgroup.centralizer ({x} : Set X)).subgroupOf N₁ = ⊤ := by
      apply Subgroup.eq_top_of_le_card
      rw [hcard_sub, hN₁card]
    exact (Subgroup.subgroupOf_eq_top.mp htop).trans inf_le_right
  have hDdvd : Nat.card ↥(N ⊓ Subgroup.centralizer ({x} : Set X)) ∣ 16 := by
    have h := Subgroup.card_subgroup_dvd_card
      ((N ⊓ Subgroup.centralizer ({x} : Set X)).subgroupOf N)
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv, hNcard] at h
  have hN₁D : N₁ ≤ N ⊓ Subgroup.centralizer ({x} : Set X) := le_inf hN₁ hN₁cent
  have h8dvd : 8 ∣ Nat.card ↥(N ⊓ Subgroup.centralizer ({x} : Set X)) := by
    have h := Subgroup.card_subgroup_dvd_card
      (N₁.subgroupOf (N ⊓ Subgroup.centralizer ({x} : Set X)))
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hN₁D).toEquiv, hN₁card] at h
  have hmodN : Nat.card ↥(N ⊓ Subgroup.centralizer ({x} : Set X)) % 5 = 1 := by
    have h := hPpg.card_modEq_card_fixedPoints (↥N)
    rw [s16c1_card_fixedPoints_eq N x, hNcard] at h
    norm_num at h
    exact h.symm
  have hDeq : Nat.card ↥(N ⊓ Subgroup.centralizer ({x} : Set X)) = 16 := by
    have hle : Nat.card ↥(N ⊓ Subgroup.centralizer ({x} : Set X)) ≤ 16 :=
      Nat.le_of_dvd (by norm_num) hDdvd
    interval_cases Nat.card ↥(N ⊓ Subgroup.centralizer ({x} : Set X)) <;> omega
  have hNcent : N ≤ Subgroup.centralizer ({x} : Set X) := by
    have htop : (N ⊓ Subgroup.centralizer ({x} : Set X)).subgroupOf N = ⊤ := by
      apply Subgroup.eq_top_of_le_card
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv, hDeq, hNcard]
    exact Subgroup.subgroupOf_eq_top.mp htop |>.trans inf_le_right
  intro n hn
  exact Subgroup.mem_centralizer_iff.mp (hNcent hn) x (Set.mem_singleton x)

theorem s16c1_central_of_not_perfect {X : Type} [Group X] [Finite X] (N : Subgroup X) [N.Normal]
    (hN : IsElemAbelianOfRank 2 4 ↥N) (hA : UC22.IsAlt (X ⧸ N) 5) (hnp : commutator X ≠ ⊤) :
    N ≤ Subgroup.center X := by
  classical
  obtain ⟨N₁, hN₁N, hN₁normal, hidx⟩ := s16c1_hyperplane N hN hA hnp
  haveI : N₁.Normal := hN₁normal
  have hperf : commutator (X ⧸ N) = ⊤ := s16c1_commutator_quotient_eq_top N hA
  have hNcard : Nat.card ↥N = 16 := s16c1_card_of_isElemAbelianOfRank hN
  let K : Subgroup X := Subgroup.closure {y : X | orderOf y = 5}
  have hKcent : K ≤ Subgroup.centralizer (N : Set X) := by
    rw [Subgroup.closure_le]
    intro y hy
    change y ∈ Subgroup.centralizer (N : Set X)
    rw [Subgroup.mem_centralizer_iff]
    intro n hn
    exact (s16c1_order_five_centralizes N N₁ hN hN₁N hidx hy n hn).symm
  have hKnormal : K.Normal := by
    refine Subgroup.Normal.mk ?_
    intro k hk g
    refine Subgroup.closure_induction (p := fun z _ => g * z * g⁻¹ ∈ K) ?_ ?_ ?_ ?_ hk
    · intro y hy
      have hy5 : orderOf (MulAut.conj g y) = 5 := by rw [MulEquiv.orderOf_eq, hy]
      have hmem : MulAut.conj g y ∈ K := Subgroup.subset_closure hy5
      rwa [MulAut.conj_apply] at hmem
    · simpa using K.one_mem
    · intro a b _ _ ha hb
      have hmul : g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by group
      rw [hmul]
      exact K.mul_mem ha hb
    · intro a _ ha
      have hinv : g * a⁻¹ * g⁻¹ = (g * a * g⁻¹)⁻¹ := by group
      rw [hinv]
      exact K.inv_mem ha
  let Kbar : Subgroup (X ⧸ N) := K.map (QuotientGroup.mk' N)
  haveI : Kbar.Normal :=
    Subgroup.Normal.map hKnormal (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)
  obtain ⟨e⟩ := hA
  haveI : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup_five
  haveI : IsSimpleGroup (X ⧸ N) := e.isSimpleGroup
  have hKbar_ne_bot : Kbar ≠ ⊥ := by
    intro hbot
    have hXcard : Nat.card X = 960 := s16c1_card_of_isE16A5 ⟨N, inferInstance, hN, ⟨e⟩⟩
    haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    have h5dvd : 5 ∣ Nat.card X := by rw [hXcard]; norm_num
    obtain ⟨g, hg5⟩ := exists_prime_orderOf_dvd_card' (G := X) 5 h5dvd
    have hgK : g ∈ K := Subgroup.subset_closure hg5
    have hgN : g ∉ N := by
      intro hgN
      have hdvd : orderOf g ∣ Nat.card ↥N := Subgroup.orderOf_dvd_natCard N hgN
      rw [hg5, hNcard] at hdvd
      norm_num at hdvd
    have hmk : QuotientGroup.mk' N g ∈ Kbar := Subgroup.mem_map.mpr ⟨g, hgK, rfl⟩
    rw [hbot, Subgroup.mem_bot] at hmk
    exact hgN ((QuotientGroup.eq_one_iff g).mp hmk)
  have hKbar_top : Kbar = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal Kbar with h | h
    · exact absurd h hKbar_ne_bot
    · exact h
  have hcommN : ∀ a b : ↥N, a * b = b * a := by
    obtain ⟨eN⟩ := hN
    intro a b
    apply eN.injective
    rw [map_mul, map_mul]
    exact mul_comm _ _
  intro n hn
  rw [Subgroup.mem_center_iff]
  intro g
  have hgKbar : QuotientGroup.mk' N g ∈ Kbar := by rw [hKbar_top]; exact Subgroup.mem_top _
  rw [Subgroup.mem_map] at hgKbar
  obtain ⟨k, hkK, hk⟩ := hgKbar
  have hm : k⁻¹ * g ∈ N := QuotientGroup.eq.mp hk
  have hx : g = k * (k⁻¹ * g) := by group
  have hkcent : k * n = n * k :=
    (Subgroup.mem_centralizer_iff.mp (hKcent hkK) n hn).symm
  have hmcomm : (k⁻¹ * g) * n = n * (k⁻¹ * g) :=
    congrArg Subtype.val (hcommN ⟨k⁻¹ * g, hm⟩ ⟨n, hn⟩)
  calc g * n = (k * (k⁻¹ * g)) * n := by rw [← hx]
    _ = k * ((k⁻¹ * g) * n) := by group
    _ = k * (n * (k⁻¹ * g)) := by rw [hmcomm]
    _ = (k * n) * (k⁻¹ * g) := by group
    _ = (n * k) * (k⁻¹ * g) := by rw [hkcent]
    _ = n * (k * (k⁻¹ * g)) := by group
    _ = n * g := by rw [← hx]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
