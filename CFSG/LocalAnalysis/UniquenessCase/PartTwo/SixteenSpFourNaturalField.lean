module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSpFourNaturalNormalizer
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenFieldExtensionRows
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenNaturalThreeK7Residual
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKLift

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.Vol2 CFSG.Open Subgroup
  CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.RankThree.GF2n.Stroth80
open Matrix

variable {G : Type} [Group G] [Finite G]
variable {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}

private theorem s168e3_sp4_quotient_transitive
    (c : S168e3Ctx D V₀ V L hV)
    (hs : s15 D.M V₀ V hV L = 1)
    {K : Type} [Field K] [Finite K]
    (hreal : (FFModel.nat (StatedSp 2 K)).Realizes (lBar V₀ V hV L)
      (commSub ⊤ (lBar V₀ V hV L))
      (commSub ⊤ (lBar V₀ V hV L) ⊓ fixV (lBar V₀ V hV L))) :
    ∀ x y : Vtil V₀ V hV, x ∉ fixV (lBar V₀ V hV L) →
      y ∉ fixV (lBar V₀ V hV L) →
      ∃ m : ↥D.M,
        barHom V₀ V hV c.m_le_stabTil m x * y⁻¹ ∈ fixV (lBar V₀ V hV L) := by
  classical
  let W := Vtil V₀ V hV
  let H : Subgroup (MulAut W) := lBar V₀ V hV L
  let Γ : Subgroup (GL (Fin 2 ⊕ Fin 2) K) := StatedSp 2 K
  have hrealTop : (FFModel.nat Γ).Realizes H ⊤ (fixV H) :=
    s16g_realizes_top c.conc hs Γ hreal
  obtain ⟨π, hπ⟩ := hrealTop
  obtain ⟨f, hf⟩ := KGNat.exists_isCoord (KGNat.linModelNat Γ) hπ
  intro x y hx hy
  have hfx : f x ≠ 0 := by
    intro h
    exact hx ((hf.ker x).mp h)
  have hfy : f y ≠ 0 := by
    intro h
    exact hy ((hf.ker y).mp h)
  obtain ⟨A, hA, hAx⟩ :=
    CFSG.ClassicalGroups.Symplectic.exists_statedSp_mulVec_eq
      (m := 2) (K := K) hfx hfy
  let γ : ↥Γ := ⟨A, hA⟩
  have hact : f (((π γ : ↥H) : MulAut W) x) =
      (KGNat.linModelNat Γ).lin γ (f x) := hf.act γ x
  have hlin : (KGNat.linModelNat Γ).lin γ (f x) =
      ((A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ f x) := by
    rw [KGNat.linModelNat_lin]
  have hfxy : f (((π γ : ↥H) : MulAut W) x) = f y := by
    rw [hact, hlin, hAx]
  have hHA : H ≤ Mbar D.M V₀ V hV := by
    simpa only [H, lBar, Mbar] using barSub_mono V₀ V hV c.setting.hyp151.le
  have hπγA : ((π γ : ↥H) : MulAut W) ∈ Mbar D.M V₀ V hV := hHA (π γ).2
  have hπγrange : ((π γ : ↥H) : MulAut W) ∈
      (barHom V₀ V hV c.m_le_stabTil).range := by
    rw [range_barHom]
    exact hπγA
  obtain ⟨m, hm⟩ := MonoidHom.mem_range.mp hπγrange
  refine ⟨m, ?_⟩
  rw [← hf.ker]
  rw [hf.map_mul_inv]
  have hfm : f (barHom V₀ V hV c.m_le_stabTil m x) = f y := by
    rw [show barHom V₀ V hV c.m_le_stabTil m = ((π γ : ↥H) : MulAut W) from hm]
    exact hfxy
  rw [hfm, sub_self]


private theorem s168e3_sp4_sigma_mem_of_realization
    (c : S168e3Ctx D V₀ V L hV)
    (hs : s15 D.M V₀ V hV L = 1)
    {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 4 ∨ Nat.card K = 8)
    (hreal : (FFModel.nat (StatedSp 2 K)).Realizes (lBar V₀ V hV L)
      (commSub ⊤ (lBar V₀ V hV L))
      (commSub ⊤ (lBar V₀ V hV L) ⊓ fixV (lBar V₀ V hV L))) :
    Nat.card K - 1 ∈ D.sig := by
  classical
  let W := Vtil V₀ V hV
  let A : Subgroup (MulAut W) := Mbar D.M V₀ V hV
  let H : Subgroup (MulAut W) := lBar V₀ V hV L
  let Γ : Subgroup (GL (Fin 2 ⊕ Fin 2) K) := StatedSp 2 K
  let φ : ↥D.M →* MulAut W := barHom V₀ V hV c.m_le_stabTil
  have hHA : H ≤ A := by
    simpa only [H, A, lBar, Mbar] using barSub_mono V₀ V hV c.setting.hyp151.le
  have hAn : A ≤ Subgroup.normalizer (H : Set (MulAut W)) := by
    intro g hg
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr
      (lBar_conj_eq_of_s15_eq_one hs hg)
  have hcomm : commSub ⊤ H = ⊤ := by
    simpa only [H, wTil, lBar] using wTil_eq_top_of_case163_2 c.conc hs
  have hrealTop : (FFModel.nat Γ).Realizes H ⊤ (fixV H) :=
    s16g_realizes_top c.conc hs Γ hreal
  obtain ⟨π, hπ⟩ := hrealTop
  obtain ⟨f, hf⟩ := KGNat.exists_isCoord (KGNat.linModelNat Γ) hπ
  obtain ⟨ρ, hρinj, hρcoord, hρcomp, hρmap, hρnorm⟩ :=
    exists_faithful_nat_hom_of_isCoord (W := W) (Γ := Γ) (A := A) (H := H)
      (π := π) (f := f) hHA hAn hf hcomm
  have hΓadd : AddCommutantScalar Γ := addCommutantScalar_statedSp (m := 2) (K := K)
  obtain ⟨θ, hθsem, hθker⟩ := s16g_exists_theta (Γ := Γ) hΓadd
  let ρN : A →* ↥(s16gNorm Γ) := ρ.codRestrict (s16gNorm Γ) hρnorm
  let ψ : A →* RingAut K := θ.comp ρN
  obtain ⟨p, hpσ⟩ := c.std.hx.sig_nonempty
  have hp : p.Prime := (D.sig_prime p hpσ).1
  have hp2 : p ≠ 2 := (D.sig_prime p hpσ).2
  have hp_eq : p = Nat.card K - 1 := by
    by_contra hpne
    obtain ⟨E, hEel, hEcard⟩ :=
      exists_isElemAbelian_subgroupOf_of_le_pRank (M := D.M) hp (by
        rw [c.std.pRank_eq_three hpσ])
    let E_A : Subgroup A := (E.map φ).subgroupOf A
    have hE_A_el : IsElemAbelian p E_A := (hEel.map φ).subgroupOf A
    let E_N : Subgroup (MulAut (Multiplicative (Fin 2 ⊕ Fin 2 → K))) := E_A.map ρ
    have hEN : E_N ≤ s16gNorm Γ := by
      intro x hx
      obtain ⟨a, ha, rfl⟩ := hx
      exact hρnorm a
    have hE_N_el : IsElemAbelian p E_N := hE_A_el.map ρ
    have hcop_or_three : (¬ p ∣ Nat.card (RingAut K)) ∨ (p = 3 ∧ Nat.card K = 8) := by
      rcases hK with hK4 | hK8
      · left
        rw [s16k_card_ringAut_of_card (a := 2) (by rw [hK4]; norm_num)]
        intro h2
        exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2)
      · by_cases hp3 : p = 3
        · exact Or.inr ⟨hp3, hK8⟩
        · left
          rw [s16g_card_ringAut_eight hK8]
          intro h3
          exact hp3 ((Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 3)).mp h3)
    have hElin : E_N ≤ s16gLin (Fin 2 ⊕ Fin 2) K := by
      rcases hcop_or_three with hcop | ⟨hp3, hK8⟩
      · exact s16g_le_lin_of_coprime hΓadd hp hcop hEN hE_N_el.isPGroup
      · intro g hg
        obtain ⟨a, ha, rfl⟩ := hg
        have hAut3 : Nat.card (RingAut K) = 3 := s16g_card_ringAut_eight hK8
        have hQp : IsPGroup p (RingAut K) :=
          IsPGroup.of_card (n := 1) (by rw [hp3, hAut3]; norm_num)
        have hψ : ψ = 1 :=
          s168e3_hom_eq_one_of_isPGroup c hp hp2 (Or.inl hpσ) hQp ψ
        have hψa : ψ a = 1 := by rw [hψ]; rfl
        have hθ : θ ⟨ρ a, hρnorm a⟩ = 1 := hψa
        exact (hθker ⟨ρ a, hρnorm a⟩).1 hθ
    obtain ⟨F, hFN, hFmap⟩ := s16g_exists_matrix_subgroup hEN hElin
    have hF_el : IsElemAbelian p F := by
      have h := IsElemAbelian.comap (E := E_N) hE_N_el
        (s16gNatHom_injective (ι := Fin 2 ⊕ Fin 2) (K := K))
      convert h using 2
      ext x
      constructor
      · intro hx
        exact Subgroup.mem_comap.mpr (by
          rw [← hFmap]
          exact Subgroup.mem_map_of_mem _ hx)
      · intro hx
        have hx' : s16gNatHom (Fin 2 ⊕ Fin 2) K x ∈ E_N := Subgroup.mem_comap.mp hx
        rw [← hFmap] at hx'
        obtain ⟨y, hy, hxy⟩ := hx'
        have hyx : y = x := s16gNatHom_injective (ι := Fin 2 ⊕ Fin 2) (K := K) hxy
        simpa [hyx] using hy
    have hUnits : ¬ p ∣ Nat.card Kˣ := by
      rcases hK with hK4 | hK8
      · rw [s16k_card_units_of_card (a := 2) (by rw [hK4]; norm_num)]
        intro h3
        have hp3 : p = 3 := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h3
        exact hpne (by rw [hK4]; norm_num; exact hp3)
      · rw [s16k_card_units_of_card (a := 3) (by rw [hK8]; norm_num)]
        intro h7
        have hp7 : p = 7 := (Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 7)).mp h7
        exact hpne (by rw [hK8]; norm_num; exact hp7)
    obtain ⟨μ, -, hμ⟩ := s16g_exists_mult_statedSp (m := 2) (K := K) (by norm_num)
    have hμF : ∀ x : ↥(Subgroup.normalizer (Γ : Set (GL (Fin 2 ⊕ Fin 2) K))),
        (x : GL (Fin 2 ⊕ Fin 2) K) ∈ F → μ x = 1 :=
      s16g_mu_eq_one_of_coprime μ hFN hp hF_el.isPGroup hUnits
    have hFΓ : F ≤ Γ := by
      intro x hx
      have hxN : x ∈ Subgroup.normalizer (Γ : Set (GL (Fin 2 ⊕ Fin 2) K)) := hFN hx
      exact (hμ ⟨x, hxN⟩).1 (hμF ⟨x, hxN⟩ hx)
    have hENΓ : E_N ≤ Γ.map (s16gNatHom (Fin 2 ⊕ Fin 2) K) := by
      intro x hx
      rw [← hFmap] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      exact Subgroup.mem_map_of_mem _ (hFΓ hy)
    have hEAH : E_A ≤ H.subgroupOf A := by
      intro a ha
      have hρa : ρ a ∈ E_N := Subgroup.mem_map_of_mem _ ha
      have hρaΓ : ρ a ∈ (H.subgroupOf A).map ρ := by
        rw [hρmap]
        exact hENΓ hρa
      exact (Subgroup.mem_map_iff_mem hρinj).mp hρaΓ
    have hbarH : ∀ e ∈ E, φ e ∈ H := by
      intro e he
      have hφeA : φ e ∈ A := by
        change φ e ∈ Mbar D.M V₀ V hV
        rw [show Mbar D.M V₀ V hV = barSub V₀ V hV D.M from rfl]
        rw [← range_barHom V₀ V hV c.m_le_stabTil]
        exact ⟨e, rfl⟩
      have hφe : (⟨φ e, hφeA⟩ : A) ∈ E_A :=
        Subgroup.mem_subgroupOf.mpr (Subgroup.mem_map_of_mem _ he)
      exact Subgroup.mem_subgroupOf.mp (hEAH hφe)
    have hEfix : ∀ e ∈ E, ∀ z ∈ fixV H, φ e z = z := by
      intro e he z hz
      exact (mem_fixV.1 hz) (φ e) (hbarH e he)
    have hstab : A ≤ CFSG.Quasithin.stabSub (fixV H) :=
      CFSG.Quasithin.FixVLat.le_stabSub_fixV_of_le_normalizer hAn
    have hZ : ∀ (m : ↥D.M) (z : W), z ∈ fixV H → φ m z ∈ fixV H := by
      intro m z hz
      have hmA : φ m ∈ A := by
        change φ m ∈ Mbar D.M V₀ V hV
        rw [show Mbar D.M V₀ V hV = barSub V₀ V hV D.M from rfl]
        rw [← range_barHom V₀ V hV c.m_le_stabTil]
        exact ⟨m, rfl⟩
      exact (hstab hmA z).mpr hz
    have htr : ∀ x y : W, x ∉ fixV H → y ∉ fixV H →
        ∃ m : ↥D.M, φ m x * y⁻¹ ∈ fixV H := by
      simpa only [W, H, φ] using s168e3_sp4_quotient_transitive c hs hreal
    have hpW : ¬ p ∣ Nat.card W := by
      have : Fact p.Prime := ⟨hp⟩
      intro hdvd
      obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hdvd
      have hx2 : x ^ 2 = 1 := s15_Infra_vtil_sq_eq_one V₀ V hV x
      have hp2dvd : p ∣ 2 := hx ▸ orderOf_dvd_iff_pow_eq_one.mpr hx2
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hp2dvd)
    have hfixM : ∀ x : W, x ≠ 1 → ∃ B : Subgroup ↥D.M, IsPGroup p B ∧ ¬ IsCyclic ↥B ∧
        ∀ b ∈ B, φ b x = x := by
      intro x hx
      exact exists_noncyclic_pSubgroup_fixing_of_quotient_transitive
        (M := ↥D.M) (W := W) hp hpW φ (fixV H) hZ E hEel hEcard hEfix htr x
    exact s168e3_false_of_fix_M c hp hpσ hfixM
  exact hp_eq ▸ hpσ

theorem s168e3_false_of_natSp4_four_of_s_eq_one
    {G : Type} [Group G] [Finite G]
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (hs : s15 D.M V₀ V hV L = 1)
    (hrow : NatSpn (lBar V₀ V hV L)
      (commSub ⊤ (lBar V₀ V hV L))
      (commSub ⊤ (lBar V₀ V hV L) ⊓ fixV (lBar V₀ V hV L)) 4 2) : False := by
  classical
  have hrow' := hrow
  obtain ⟨-, K, hKf, hKfin, hKcard, hreal⟩ := hrow'
  let : Field K := hKf
  let : Finite K := hKfin
  have hK4 : Nat.card K = 4 := by rw [hKcard]; norm_num
  have hqmem : Nat.card K - 1 ∈ D.sig :=
    s168e3_sp4_sigma_mem_of_realization c hs (Or.inl hK4) hreal
  have h3sig : 3 ∈ D.sig := by simpa [hK4] using hqmem
  have hm : MBarGT D.M V₀ V 1 :=
    s168e3_sp4_four_mbarGT_one_of_s_eq_one c hs hrow
  have hZ : fixV (lBar V₀ V hV L) = ⊥ :=
    fixV_lBar_eq_bot_of_field_four_at_three c hs hK4 (Or.inr hreal) h3sig hm
  have htr : ∀ x y : Vtil V₀ V hV, x ≠ 1 → y ≠ 1 →
      ∃ a ∈ Mbar D.M V₀ V hV, a x = y := by
    intro x y hx hy
    have hx' : x ∉ fixV (lBar V₀ V hV L) := by simpa [hZ] using hx
    have hy' : y ∉ fixV (lBar V₀ V hV L) := by simpa [hZ] using hy
    obtain ⟨m, hm⟩ := s168e3_sp4_quotient_transitive c hs hreal x y hx' hy'
    have hm1 : barHom V₀ V hV c.m_le_stabTil m x * y⁻¹ = 1 := by
      simpa [hZ] using hm
    refine ⟨barHom V₀ V hV c.m_le_stabTil m, ?_, ?_⟩
    · rw [show Mbar D.M V₀ V hV = barSub V₀ V hV D.M from rfl,
        ← range_barHom V₀ V hV c.m_le_stabTil]
      exact ⟨m, rfl⟩
    · exact mul_inv_eq_one.mp hm1
  exact s168e3_false_of_transitive c htr

theorem s168e3_false_of_natSp4_eight_of_s_eq_one
    {G : Type} [Group G] [Finite G]
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (hs : s15 D.M V₀ V hV L = 1)
    (hrow : NatSpn (lBar V₀ V hV L)
      (commSub ⊤ (lBar V₀ V hV L))
      (commSub ⊤ (lBar V₀ V hV L) ⊓ fixV (lBar V₀ V hV L)) 4 3) : False := by
  classical
  have hrow' := hrow
  obtain ⟨-, K, hKf, hKfin, hKcard, hreal⟩ := hrow'
  let : Field K := hKf
  let : Finite K := hKfin
  have hK8 : Nat.card K = 8 := by rw [hKcard]; norm_num
  have hqmem : Nat.card K - 1 ∈ D.sig :=
    s168e3_sp4_sigma_mem_of_realization c hs (Or.inr hK8) hreal
  have h7sig : 7 ∈ D.sig := by simpa [hK8] using hqmem
  have hm : MBarGT D.M V₀ V 2 :=
    s168e3_sp4_eight_mbarGT_two_of_s_eq_one c hs hrow
  have hZ : fixV (lBar V₀ V hV L) = ⊥ :=
    fixV_lBar_eq_bot_of_field_eight_at_three c hs hK8 (Or.inr hreal) h7sig hm
  have htr : ∀ x y : Vtil V₀ V hV, x ≠ 1 → y ≠ 1 →
      ∃ a ∈ Mbar D.M V₀ V hV, a x = y := by
    intro x y hx hy
    have hx' : x ∉ fixV (lBar V₀ V hV L) := by simpa [hZ] using hx
    have hy' : y ∉ fixV (lBar V₀ V hV L) := by simpa [hZ] using hy
    obtain ⟨m, hm⟩ := s168e3_sp4_quotient_transitive c hs hreal x y hx' hy'
    have hm1 : barHom V₀ V hV c.m_le_stabTil m x * y⁻¹ = 1 := by
      simpa [hZ] using hm
    refine ⟨barHom V₀ V hV c.m_le_stabTil m, ?_, ?_⟩
    · rw [show Mbar D.M V₀ V hV = barSub V₀ V hV D.M from rfl,
        ← range_barHom V₀ V hV c.m_le_stabTil]
      exact ⟨m, rfl⟩
    · exact mul_inv_eq_one.mp hm1
  exact s168e3_false_of_transitive c htr

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
