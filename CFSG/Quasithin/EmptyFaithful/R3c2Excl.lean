module

public import CFSG.Quasithin.EmptyFaithful.R3c2Kernel
public import CFSG.Quasithin.EmptyFaithful.R3c2Gen
public import CFSG.Quasithin.EmptyFaithful.T1515eA

public section

namespace CFSG.Quasithin.R3c2

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

theorem exclusion_of_mulEquiv {X Y : Type} [Group X] [Finite X] [Group Y] [Finite Y] (e : X ≃* Y)
    (h : A318Exclusion X) : A318Exclusion Y := by
  have := h.simple
  refine ⟨e.symm.isSimpleGroup, ?_, ?_⟩
  · rw [← CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num) e]
    exact h.rank
  · intro Z _ s p k hp hk hZ hmod f hf
    exact h.noImage Z s p k hp hk hZ hmod (e.symm.toMonoidHom.comp f)
      (e.symm.surjective.comp hf)

theorem not_case2_case3_of_equiv_exclusion {G' : Type} [Group G'] (S₀ : Subgroup G') {T : Type}
    [Group T] [Finite T] (e : ↥S₀ ≃* T) (hT : A318Exclusion T) :
    ¬ A318Case2 S₀ ∧ ¬ A318Case3Group ↥S₀ := by
  have hZ := hT.center_eq_bot
  have : Finite ↥S₀ := Finite.of_equiv T e.symm.toEquiv
  refine ⟨fun h2 => ?_, fun h3 => ?_⟩
  · obtain ⟨s, q, hmod, ⟨r, k, hrp, hk1, hq, hPSL⟩, -⟩ := h2
    subst hq
    exact hT.noImage _ s r k hrp hk1 hPSL hmod e.toMonoidHom e.surjective
  · obtain ⟨z, hzcen, hz⟩ := exists_central_order_three_of_a318Case3Group1515e h3
    have hzc : e z ∈ Subgroup.center T := Subgroup.map_center_le_center e.surjective ⟨_, hzcen, rfl⟩
    rw [hZ, Subgroup.mem_bot] at hzc
    have : z = 1 := e.injective (by rw [hzc, map_one])
    rw [this, orderOf_one] at hz
    omega

theorem card_alternatingGroup_six : Nat.card (alternatingGroup (Fin 6)) = 360 := by
  have : Nontrivial (Fin 6) := Fin.nontrivial_iff_two_le.mpr (by norm_num)
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
  decide

theorem three_dvd_card_of_one_le_pRank {Y : Type} [Group Y] [Finite Y] (K : Subgroup Y)
    (h : 1 ≤ CFSG.Open.pRank 3 K) : 3 ∣ Nat.card K := by
  obtain ⟨E, hEK, -, hE⟩ := CFSG.SectionRank.exists_pRank (p := 3) (by norm_num) K
  refine dvd_trans ?_ (Subgroup.card_dvd_of_le hEK)
  rw [hE]
  exact dvd_pow_self 3 (by omega)

theorem pRank_three_subgroupOf {Y : Type} [Group Y] [Finite Y] {L H : Subgroup Y} (hLH : L ≤ H) :
    CFSG.Open.pRank 3 (L.subgroupOf H) = CFSG.Open.pRank 3 L :=
  (CFSG.Quasithin.Vol2.Ch11.SecA.pRank_subgroupOf_eq hLH Nat.prime_three (by norm_num)).trans
    (R3c.pRank_three_eq_pCore_quotient L).symm

theorem normal_closure_orderOf_eq {X : Type*} [Group X] (n : ℕ) :
    (Subgroup.closure {y : X | orderOf y = n}).Normal := by
  refine ⟨fun a ha g => ?_⟩
  refine Subgroup.closure_induction
    (p := fun a _ => g * a * g⁻¹ ∈ Subgroup.closure {y : X | orderOf y = n}) ?_ ?_ ?_ ?_ ha
  · intro y hy
    apply Subgroup.subset_closure
    show orderOf (g * y * g⁻¹) = n
    have := orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective y
    simpa using this.trans hy
  · simp
  · intro x y _ _ hx hy
    have : g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
    rw [this]
    exact Subgroup.mul_mem _ hx hy
  · intro x _ hx
    have : g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := by group
    rw [this]
    exact Subgroup.inv_mem _ hx

theorem closure_orderOf_three_eq_top_of_simple {X : Type*} [Group X] [Finite X] [IsSimpleGroup X]
    (h3 : 3 ∣ Nat.card X) : Subgroup.closure {y : X | orderOf y = 3} = ⊤ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have := normal_closure_orderOf_eq (X := X) 3
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.closure {y : X | orderOf y = 3}) with hb | ht
  · exfalso
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := X) 3 h3
    have hy1 : y ∈ Subgroup.closure {y : X | orderOf y = 3} := Subgroup.subset_closure hy
    rw [hb, Subgroup.mem_bot] at hy1
    rw [hy1, orderOf_one] at hy
    omega
  · exact ht

theorem not_subsingleton_starImage {Y : Type} [Group Y] [Finite Y] {L H : Subgroup Y} (hLH : L ≤ H)
    (hr : 1 ≤ CFSG.Open.pRank 3 L) : ¬ Subsingleton ↥(starImage 3 (L.subgroupOf H)) := by
  intro hsub
  have hle : L.subgroupOf H ≤ CFSG.pPrimeCore 3 ↥H := by
    intro k hk
    have hmem : QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥H) k ∈ starImage 3 (L.subgroupOf H) :=
      ⟨k, hk, rfl⟩
    have h1 := congrArg Subtype.val (hsub.elim ⟨_, hmem⟩ 1)
    exact (QuotientGroup.eq_one_iff (N := CFSG.pPrimeCore 3 ↥H) k).1 h1
  have hdvd := Subgroup.card_dvd_of_le hle
  have hcop : Nat.Coprime 3 (Nat.card (L.subgroupOf H)) :=
    Nat.Coprime.coprime_dvd_right hdvd CFSG.pPrimeCore_coprime_card
  have h3 : 3 ∣ Nat.card (L.subgroupOf H) := by
    apply three_dvd_card_of_one_le_pRank
    rwa [pRank_three_subgroupOf hLH]
  have := Nat.Coprime.eq_one_of_dvd hcop h3
  omega

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ Yp I L : Subgroup G}

theorem not_case2_case3_of_star_exclusion (hI : IsHPlus Yp (Sgp153 T V₁) M I)
    (hF : Facts15325 T Mc M V₁ V₂ Yp I) (hLI : L ≤ I)
    (hnorm : I ≤ Subgroup.normalizer (L : Set G)) (hr : 1 ≤ CFSG.Open.pRank 3 L)
    {S : Type} [Group S] [Finite S] (e : ↥(Star153 T I L) ≃* S) (hS : A318Exclusion S) :
    ¬ A318Case2 (starImage 3 (L.subgroupOf I)) ∧ ¬ A318Case3Group ↥(starImage 3 (L.subgroupOf I)) := by
  have := hS.simple
  have hX : IsSimpleGroup ↥(Star153 T I L) := e.isSimpleGroup
  obtain ⟨π, hπ⟩ := exists_surjection_star_starImage hI hF hLI hnorm
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal π.ker with hb | ht
  · have hinj : Function.Injective π := (MonoidHom.ker_eq_bot_iff π).1 hb
    exact not_case2_case3_of_equiv_exclusion _
      ((MulEquiv.ofBijective π ⟨hinj, hπ⟩).symm.trans e) hS
  · exfalso
    refine not_subsingleton_starImage hLI hr ⟨fun a b => ?_⟩
    obtain ⟨a', rfl⟩ := hπ a
    obtain ⟨b', rfl⟩ := hπ b
    rw [MonoidHom.mem_ker.1 (ht ▸ Subgroup.mem_top a'), MonoidHom.mem_ker.1 (ht ▸ Subgroup.mem_top b')]

theorem eq_thetaOf_of_star_exclusion (hF318 : A318Facts) (h36 : A36ForSQTK) (h38 : A38ForSQTK)
    (hSQ : SQTKGroup ↥I) (hI : IsHPlus Yp (Sgp153 T V₁) M I) (hF : Facts15325 T Mc M V₁ V₂ Yp I)
    (hLc : L ∈ cComp I) (hnorm : I ≤ Subgroup.normalizer (L : Set G))
    (hQ : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L))
    {S : Type} [Group S] [Finite S] (e : ↥(Star153 T I L) ≃* S) (hS : A318Exclusion S) :
    L = thetaOf I := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hLI : L ≤ I := le_of_mem_cComp hLc
  have hperf : ⁅L, L⁆ = L := perfect_of_mem_cComp hLc
  have : Finite ↥(Star153 T I L) := Finite.of_equiv S e.symm.toEquiv
  have hr : 2 ≤ CFSG.Open.pRank 3 L := by
    rw [pRank_three_eq_star hI hF hLI,
      CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num) e]
    exact hS.rank
  obtain ⟨ψ, hψ, hψ1⟩ := exists_starSurj T I L hLI
  have hker3 : ∀ x ∈ ψ.ker, orderOf x ≠ 3 := fun x hx h3 =>
    orderOf_ne_three_of_mem_centralizer_UI hI hF (hLI x.2) ((hψ1 x).1 hx)
      (by rw [Subgroup.orderOf_coe]; exact h3)
  have hX3 : 3 ∣ Nat.card ↥(Star153 T I L) := by
    rw [Nat.card_congr e.toEquiv]
    exact hS.three_dvd_card
  have := hS.simple
  have hXs : IsSimpleGroup ↥(Star153 T I L) := e.isSimpleGroup
  have hθ : L ≤ thetaOf I :=
    le_thetaOf_of_surjection hLI hperf hQ ψ hψ hker3
      (closure_orderOf_three_eq_top_of_simple hX3) hX3
  obtain ⟨hn2, hn3⟩ := not_case2_case3_of_star_exclusion hI hF hLI hnorm (by omega) e hS
  exact eq_thetaOf_of_a318_of_group hF318 h36 h38 hSQ hLc hQ hr hn2 (fun h => absurd h hn3) hθ

end CFSG.Quasithin.R3c2
