module

public import CFSG.Quasithin.Vol2.Ch12Sec6L32Pe
public import CFSG.Quasithin.Vol2.Ch12Sec6L32NoFF
public import CFSG.Quasithin.Vol2.Ch12Sec6L32Pc
public import CFSG.Quasithin.Vol2.Ch12Sec6L32Pd

public section

namespace CFSG.Quasithin.H13.L1232

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique S126 F126 L1233
open CFSG.Assembly.LowTwoRank Matrix

theorem noFF12632_of (h56 : AsB56) : NoFF12632 := by
  intro G _ _ T L V _ F hH hZ H K hIs h1 h918 W _ _ hW ρ hρQ hρK hff
  have h := h918.toHypF98.toHypF91
  have hKH : K ≤ H := le_of_mem_cComp h918.K_cComp
  have hXH : K ⊔ T ≤ H := sup_le hKH h918.T_le_H
  have hTK : T ≤ Subgroup.normalizer (K : Set G) := by
    refine le_normalizer_of_conj fun x hx k hk => ?_
    rw [← h1.1]
    exact mem_conjClosure hx hk
  have hXK : ∀ x ∈ K ⊔ T, ∀ k ∈ K, x * k * x⁻¹ ∈ K := fun x hx k hk =>
    (Subgroup.mem_normalizer_iff.1 ((sup_le Subgroup.le_normalizer hTK) hx) k).1 hk
  have hT2 : IsPGroup 2 ↥T := h.sylow.2.1
  have hO2 : pCoreOf 2 H ≠ ⊥ := fun h0 => h.V₁_ne_bot (le_bot_iff.1 (h0 ▸
    h.V₁_le_Vp.trans ((le_conjClosure _ _).trans h.conjClosure_Vp_le_pCoreOf)))
  have hSQX : SQTKGroup ↥(K ⊔ T) := Vol2.Ch10.SecB.C11AmS.K8.sqtkGroup_of_le
    (sqtkGroup_of_pCoreOf_ne_bot hH.hyp.qtke hH.hyp.simple hH.hyp.nonabelian hO2) hXH
  have hQ : G64.IsQuotientOfSQTKCat ↥ρ.range :=
    ⟨↥(K ⊔ T), inferInstance, inferInstance, ρ.ker, inferInstance, SQTKGroup.isSQTKCat hSQX,
      ⟨(QuotientGroup.quotientKerEquivRange ρ).symm⟩⟩
  set Lg := (K.subgroupOf (K ⊔ T)).map ρ with hLg
  have hLΓ : Lg ≤ ρ.range := Subgroup.map_le_range ρ _
  have hΓL : ρ.range ≤ Subgroup.normalizer (Lg : Set (MulAut W)) := by
    rintro _ ⟨x, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · rintro ⟨k, hk, rfl⟩
      refine ⟨x * k * x⁻¹, Subgroup.mem_subgroupOf.2
        (hXK x x.2 k (Subgroup.mem_subgroupOf.1 hk)), ?_⟩
      rw [map_mul, map_mul, map_inv]
    · rintro ⟨k, hk, hke⟩
      refine ⟨x⁻¹ * k * x, Subgroup.mem_subgroupOf.2 ?_, ?_⟩
      · have := hXK _ (Subgroup.inv_mem _ x.2) k (Subgroup.mem_subgroupOf.1 hk)
        simpa using this
      · rw [map_mul, map_mul, map_inv, hke]
        group
  have hKn := star_normal_of_case1 h918 h1
  have hperf : ⁅S126.star H K, S126.star H K⁆ = S126.star H K :=
    perfect_of_mem_cComp (star_mem_cComp h918.K_cComp)
  obtain ⟨hCK, hK3⟩ := centralizer_star_le_of_case1 h918 h1
  have hcent : ∀ x : ↥(K ⊔ T), ρ x ∈ Subgroup.centralizer (Lg : Set (MulAut W)) →
      starOf hXH x ∈ Subgroup.centralizer (S126.star H K : Set (S126.HStar H)) := by
    intro x hx
    refine starOf_mem_centralizer hKn hperf hXK hρK fun k hk => ?_
    exact (Subgroup.mem_centralizer_iff.1 hx (ρ k) ⟨k, Subgroup.mem_subgroupOf.2 hk, rfl⟩).symm
  have hCL : ρ.range ⊓ Subgroup.centralizer (Lg : Set (MulAut W)) ≤ Lg := by
    rintro _ ⟨⟨x, rfl⟩, hx⟩
    exact rho_mem_of_starOf_mem hρQ (hCK (hcent x hx))
  have hC : ∀ γ ∈ ρ.range, γ ∈ Subgroup.centralizer (Lg : Set (MulAut W)) → γ ^ 2 = 1 →
      γ = 1 := by
    rintro _ ⟨x, rfl⟩ hx hx2
    have hx3 := hK3 _ (hCK (hcent x hx)) (hcent x hx)
    have h3 : ρ x ^ 3 = 1 := by
      rw [← starOf_pow] at hx3
      rw [← map_pow]
      exact hρQ _ (mkH_eq_one_iff.1 hx3)
    calc ρ x = ρ x ^ 3 * (ρ x ^ 2)⁻¹ := by group
      _ = 1 := by rw [h3, hx2, inv_one, mul_one]
  have h2 : ∀ γ ∈ ρ.range, ∃ m : ℕ, γ ^ 2 ^ m ∈ Lg := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨m, hm⟩ := S126L24.exists_pow_mem_of_mem_sup (T := T) hTK hT2 x.2
    exact ⟨m, ⟨x ^ 2 ^ m, Subgroup.mem_subgroupOf.2 (by simpa using hm), map_pow ρ x _⟩⟩
  have hoff := B6.exists_isFFStarOffender hff
  obtain ⟨θ, hθs, hθk⟩ := exists_star_hom (T := T) hKH hρQ hρK
  have hLq : CFSG.IsQuasisimple ↥(S126.star H K) → CFSG.IsQuasisimple ↥Lg := by
    intro hq
    refine CFSG.LieType.CurtisTits.isQuasisimple_of_surjective hq hθs ?_
    by_contra hno
    push Not at hno
    obtain ⟨a, b, hab⟩ := G64.IsQuasisimple.exists_ne hq
    have ha : a ∈ Subgroup.center ↥(S126.star H K) := hθk (hno a)
    exact hab (Subgroup.mem_center_iff.1 ha b).symm
  rcases h1.2.1 with ⟨F', _, _, hF', ⟨e₁⟩, -⟩ | ⟨F', _, _, hF', ⟨e₁⟩, hidx, hsq⟩
  ·
    have : IsSimpleGroup (PSL3Model F') := E54.isSimpleGroup_of_lieModel (lieModel_psl3Model hF')
    have hKs : IsSimpleGroup ↥(S126.star H K) := e₁.isSimpleGroup
    have hnc : ∃ a b : ↥(S126.star H K), a * b ≠ b * a := by
      by_contra hc
      push Not at hc
      let _ : CommGroup ↥(S126.star H K) :=
        { (inferInstance : Group ↥(S126.star H K)) with mul_comm := hc }
      have hp : (Nat.card ↥(S126.star H K)).Prime := IsSimpleGroup.prime_card
      rw [Nat.card_congr e₁.toEquiv, E54.card_of_lieModel (lieModel_psl3Model hF')] at hp
      norm_num at hp
    have hKq : CFSG.IsQuasisimple ↥(S126.star H K) :=
      (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnc).1
    have hZK : Subgroup.center ↥(S126.star H K) = ⊥ := by
      apply Subgroup.eq_bot_of_card_eq
      rw [Nat.card_congr (Subgroup.centerCongr e₁).toEquiv, center_psl3Model_eq_bot hF',
        Subgroup.card_bot]
    have hθi : Function.Injective θ := by
      rw [← MonoidHom.ker_eq_bot_iff]
      exact le_bot_iff.1 (hZK ▸ hθk)
    exact false_of_ff_psl34 h56 hW hQ (hLq hKq) hLΓ hΓL hC hoff hF'
      ((MulEquiv.ofBijective θ ⟨hθi, hθs⟩).symm.trans e₁)
  ·
    set eS : ↥(S126.star H K) ≃* SpecialLinearGroup (Fin 3) F' :=
      e₁.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 F').symm with heS
    have hKq : CFSG.IsQuasisimple ↥(S126.star H K) :=
      EmptyFaithfulMultiple.FFL.isQuasisimple_of_mulEquiv e₁.symm
        (EmptyFaithfulMultiple.FFL.isQuasisimple_statedSL (m := 2) le_rfl F')
    have hZ3 : Nat.card ↥(Subgroup.center ↥(S126.star H K)) = 3 := by
      rw [Nat.card_congr (Subgroup.centerCongr eS).toEquiv]
      exact Ch9.KGFF.card_center_sl3_four hF'
    have hk3 : Nat.card θ.ker ∣ 3 := by
      have := Subgroup.card_dvd_of_le hθk
      rwa [hZ3] at this
    rcases (Nat.dvd_prime Nat.prime_three).mp hk3 with hk1 | hk3'
    ·
      have hθi : Function.Injective θ :=
        (MonoidHom.ker_eq_bot_iff θ).1 (Subgroup.eq_bot_of_card_eq _ hk1)
      obtain ⟨t₁, t₂, ht₁, ht₂, hn₁, hn₂, hn₁₂⟩ := exists_outer_pair h918 h1 hidx hsq
      have hnot : ∀ x : ↥(K ⊔ T), starOf hXH x ∉ S126.star H K → ρ x ∉ Lg := by
        intro x hx hρx
        obtain ⟨⟨k, hkX⟩, hk, hke⟩ := hρx
        have hkK : k ∈ K := Subgroup.mem_subgroupOf.1 hk
        have h1' : ρ (x * (⟨k, hkX⟩ : ↥(K ⊔ T))⁻¹) = 1 := by
          rw [map_mul, map_inv, hke, mul_inv_cancel]
        have hc := hCK (hcent _ (by rw [h1']; exact Subgroup.one_mem _))
        rw [starOf_mul, starOf_inv] at hc
        apply hx
        have hkS : starOf hXH ⟨k, hkX⟩ ∈ S126.star H K :=
          ⟨⟨k, hKH hkK⟩, Subgroup.mem_subgroupOf.2 hkK, rfl⟩
        have := (S126.star H K).mul_mem hc hkS
        rwa [inv_mul_cancel_right] at this
      set x₁ : ↥(K ⊔ T) := ⟨t₁, Subgroup.mem_sup_right ht₁⟩
      set x₂ : ↥(K ⊔ T) := ⟨t₂, Subgroup.mem_sup_right ht₂⟩
      have hx₁ : ρ x₁ ∉ Lg := hnot x₁ hn₁
      have hx₂ : ρ x₂ ∉ Lg := hnot x₂ hn₂
      have hx₁₂ : ρ x₁ * (ρ x₂)⁻¹ ∉ Lg := by
        rw [← map_inv, ← map_mul]
        exact hnot (x₁ * x₂⁻¹) hn₁₂
      exact false_of_ff_sl34 h56 hW hQ (hLq hKq) hLΓ hΓL hC hCL hoff hF'
        ((MulEquiv.ofBijective θ ⟨hθi, hθs⟩).symm.trans eS) h2 ⟨x₁, rfl⟩ ⟨x₂, rfl⟩
        hx₁ hx₂ hx₁₂
    ·
      have hkZ : θ.ker = Subgroup.center ↥(S126.star H K) :=
        Subgroup.eq_of_le_of_card_ge hθk (by rw [hk3', hZ3])
      have eP : ↥Lg ≃* CFSG.Assembly.LowTwoRank.StatedProj
          (CFSG.Assembly.LowTwoRank.StatedSL 3 F') :=
        (QuotientGroup.quotientKerEquivOfSurjective θ hθs).symm.trans
          ((QuotientGroup.quotientMulEquivOfEq hkZ).trans
            ((QuotientGroup.congr _ _ eS (Subgroup.map_center_eq eS)).trans
              (projectiveSpecialLinearGroupEquivStatedProj 3 F')))
      exact false_of_ff_psl34 h56 hW hQ (hLq hKq) hLΓ hΓL hC hoff hF' eP

end CFSG.Quasithin.H13.L1232
