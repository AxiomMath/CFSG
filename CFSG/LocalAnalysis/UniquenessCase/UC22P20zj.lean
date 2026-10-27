module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P20zi
public import CFSG.LocalAnalysis.UniquenessCase.UC22P20zda
public import CFSG.LocalAnalysis.UniquenessCase.UC22P20zg
public import CFSG.LocalAnalysis.UniquenessCase.Lie.Suzuki
public import CFSG.LocalAnalysis.UniquenessCase.Lie.SL2
public import CFSG.LocalAnalysis.UniquenessCase.Lie.SU3Cover

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup

section Abstract

variable {X Γ : Type} [Group X] [Group Γ]

theorem uc22pwt_elem_of_inputG
    [Finite X] (hΓ : IsPGroup 2 Γ) {ρ : Γ →* MulAut X} {τ : Γ}
    {U A₁ A₂ : Subgroup X} (C : UC22pwtCtx ρ τ U A₁ A₂)
    (hUsyl : CFSG.ABGLocalTools.IsSylowOf 2 (U ⊓ A₁) A₁) (hq : CFSG.Open.IsQuasisimple ↥A₁) {n : ℕ}
    (hn : 2 < n) (hsh : IsSz ↥A₁ n ∨ IsL2 ↥A₁ n ∨ IsSU3 ↥A₁ n)
    (hZ : ∀ p : ℕ, p.Prime → p ∣ 2 ^ n - 1 → ¬ p ∣ Nat.card (Subgroup.center ↥A₁))
    {e m' : ℕ} (hm' : Odd m') (hnem : n = 2 ^ e * m') :
    ∃ (h w₁ : X) (m a b : ℕ), UC22pwtElem C h w₁ m a b {p : ℕ | p.Prime ∧ p ∣ 2 ^ m' - 1} ∧
      (∀ p : ℕ, p.Prime → (p ∣ m ↔ p ∣ 2 ^ n - 1)) ∧
      ∀ g ∈ uc22pwtStab2 ρ A₁ A₂, ∃ i : ℕ, ρ g h * (h ^ 2 ^ i)⁻¹ ∈ U := by
  obtain ⟨U', hU'⟩ := uc22pwtb_exists_sylow hUsyl
  have hUinv : ∀ (g : ↥(uc22pwtStab2 ρ A₁ A₂)) (x : ↥A₁),
      x ∈ (U' : Subgroup ↥A₁) ↔ uc22pwtRes2 ρ A₁ A₂ g x ∈ (U' : Subgroup ↥A₁) := by
    intro g x
    rw [hU', Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    exact ⟨fun hx => ⟨(C.Uinv g x).1 hx.1, (uc22pwtRes2 ρ A₁ A₂ g x).2⟩,
      fun hx => ⟨(C.Uinv g x).2 hx.1, x.2⟩⟩
  obtain ⟨E, hE, hG⟩ : ∃ E : Subgroup ↥A₁, uc22pwlie_ConclAt uc22pwr1_shape ↥A₁ (U' : Subgroup ↥A₁)
      ↥(uc22pwtStab2 ρ A₁ A₂) (uc22pwtRes2 ρ A₁ A₂) n m' E ∧
      uc22pwlie_Gal (U' : Subgroup ↥A₁) E (uc22pwtRes2 ρ A₁ A₂) := by
    rcases hsh with hs | hs | hs
    · exact uc22pwr1_concl_of_isSzG hs U' (hΓ.to_subgroup _) _ hUinv hm' hnem
    · exact uc22pwr1_concl_of_isL2G hs U' (hΓ.to_subgroup _) _ hUinv hm' hnem
    · exact uc22pwr1_concl_of_isSU3G hq hn hs U' (hΓ.to_subgroup _) _ hUinv hm' hnem
  obtain ⟨hEU, ⟨hEcyc, hEsq, hEodd⟩, hEpi, hEinv, hEα, w, hw2, hwinv, hwgen⟩ := hE
  rw [hU'] at hEU hEinv hEα hwgen hG
  obtain ⟨h, w₁, m, a, b, El, hpr, h₀, hh₀E, rfl⟩ :=
    uc22pwt_elem_of_E C hq hn hZ hEU hEcyc hEsq hEodd hEpi hEinv hEα hw2 hwinv hwgen
  refine ⟨_, w₁, m, a, b, El, hpr, fun g hg => ?_⟩
  obtain ⟨i, hi⟩ := hG ⟨g, hg⟩
  exact ⟨i, (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 (hi h₀ hh₀E))).1⟩

theorem uc22pwt_coreG
    [Finite X] (hΓ : IsPGroup 2 Γ) (ρ : Γ →* MulAut X) (τ : Γ)
    {U A₁ A₂ : Subgroup X} (C : UC22pwtCtx ρ τ U A₁ A₂) (hU : IsPGroup 2 U)
    (hUsyl : CFSG.ABGLocalTools.IsSylowOf 2 (U ⊓ A₁) A₁) (hq : CFSG.Open.IsQuasisimple ↥A₁) {n : ℕ}
    (hn : 2 < n) (hsh : IsSz ↥A₁ n ∨ IsL2 ↥A₁ n ∨ IsSU3 ↥A₁ n)
    (hZ : ∀ p : ℕ, p.Prime → p ∣ 2 ^ n - 1 → ¬ p ∣ Nat.card (Subgroup.center ↥A₁))
    {e m' : ℕ} (hm' : Odd m') (hnem : n = 2 ^ e * m') :
    ∃ E : Subgroup X, E ≤ normalizer (U : Set X) ∧ IsMulCommutative E ∧ Odd (Nat.card E) ∧
      (∀ p : ℕ, p.Prime → ∃ Q : Sylow p E, IsElemAbelian p (Q : Subgroup E) ∧ Nat.card Q ≤ p ^ 2) ∧
      piSet E = etaSet n ∧ (∀ g : Γ, ∀ x ∈ E, ρ g x ∈ E ⊔ U) ∧
      (∀ g : Γ, ∀ x ∈ oPi {p | p.Prime ∧ p ∣ 2 ^ m' - 1} E, ρ g x * x⁻¹ ∈ U) ∧
      (∃ w : X, w ^ 2 = 1 ∧ (∀ x ∈ E, w * x * w⁻¹ = x⁻¹) ∧
        normalizer (U : Set X) ⊔ Subgroup.zpowers w = ⊤) ∧
      ∃ F : ℕ → Subgroup X,
        (∀ p : ℕ, p.Prime → F p ≤ pCoreOf p E ∧ uc22pwsInv U (Set.range ρ) (F p) ∧
          (p ∣ Nat.card E → F p ≠ ⊥) ∧
          ∀ W : Subgroup X, W ≤ F p → uc22pwsInv U (Set.range ρ) W → W = ⊥ ∨ W = F p) ∧
        ∀ J : Subgroup X, J = ⨆ q ∈ (Nat.card E).primeFactors, F q →
          (IsCyclic J → uc22pwlAlike ρ J) ∧ (IsPowTwo n → ∀ g : Γ, ¬ ∀ x ∈ J, ρ g x = x⁻¹) := by
  obtain ⟨h, w₁, m, a, b, El, hpr, hGal⟩ := uc22pwt_elem_of_inputG hΓ C hUsyl hq hn hsh hZ hm' hnem
  have P := El.pair
  obtain ⟨F, hF, hJ⟩ := uc22pwt_sel_two El hU hGal
  refine ⟨uc22pwtE h (ρ τ h) a b, El.E_le_normalizer, P.isMulCommutative_E, P.odd_card_E, P.rank_E, ?_,
    El.invariant, El.alpha_clause, El.involution, F, hF, fun J hJdef => ⟨(hJ J hJdef).1, fun hp2 => ?_⟩⟩
  · rw [P.piSet_E]
    ext p
    simp only [etaSet, Set.mem_setOf_eq]
    exact ⟨fun hp => ⟨hp.1, (hpr p hp.1).1 hp.2⟩, fun hp => ⟨hp.1, (hpr p hp.1).2 hp.2⟩⟩
  · have hm1 : m' = 1 := by
      obtain ⟨k, hk⟩ := hp2
      exact Nat.Coprime.eq_one_of_dvd ((Nat.coprime_two_right.2 hm').pow_right k)
        (Dvd.intro_left (2 ^ e) (hnem.symm.trans hk))
    have h21 : (2 : ℕ) ^ m' - 1 = 1 := by
      rw [hm1]
      norm_num
    have hdb : ∀ p : ℕ, p.Prime → p ∣ 15 → p ∣ b := by
      intro p hp hp15
      have hpm : p ∣ m := (hpr p hp).2 (hp15.trans (uc22pwc_fifteen_dvd hp2 hn))
      have hpab : p ∣ a * b := by
        rw [El.ab]
        exact hpm
      rcases (Nat.Prime.dvd_mul hp).1 hpab with hpa | hpb
      · obtain ⟨-, hpd⟩ := (El.pr p hp hpm).2 hpa
        rw [h21] at hpd
        exact absurd (Nat.dvd_one.1 hpd) hp.one_lt.ne'
      · exact hpb
    exact (hJ J hJdef).2 (hdb 3 Nat.prime_three (by norm_num)) (hdb 5 Nat.prime_five (by norm_num))

end Abstract

section Concrete

variable {G : Type} [Group G] [Finite G]

theorem uc22pw_uA_eq_range (D : Data G) {L : Subgroup G} (hL : L ∈ calL D.T D.M) :
    uc22p20uA D L = Set.range (uc22pwIndHom L D.T hL.1) := by
  ext φ
  constructor
  · rintro ⟨t, ht, htT, rfl⟩
    exact ⟨⟨t, htT⟩, rfl⟩
  · rintro ⟨⟨t, htT⟩, rfl⟩
    exact ⟨t, hL.1 htT, htT, rfl⟩

theorem uc22pw_ch214U_two
    (hu38 : uc22p20oU38Witness) (D : Data G) (hB : ListBNonabelian)
    (h1930 : H1930 D) {L K K₂ : Subgroup G} (hL : L ∈ calL D.T D.M) (hK : K ∈ calC L)
    (hK₂ : K₂ ∈ calC L) (hne : K₂ ≠ K) (hLK : L = K ⊔ K₂) {t : G} (htT : t ∈ D.T)
    (ht : K₂ = uc22p20bCj t K) {n : ℕ} (hn : 2 < n)
    (hsh : IsSz (Bar2 K) n ∨ IsL2 (Bar2 K) n ∨ (n = 3 ∧ IsSU3 (Bar2 K) 3)) :
    ∃ B0 : Subgroup G, Choice214U D L B0 ∧ B0 ∈ calB1 D.T D.M L ∧ piSet B0 = etaSet n ∧
      AlphaCond D.T B0 n ∧ B0 ≤ D.M := by
  obtain ⟨C, hUsyl, hq, hsh', hZ⟩ := uc22pw_two_ctx hu38 D hL hK hK₂ hne hLK htT ht hn hsh
  obtain ⟨e, m', hm', hnem⟩ := Nat.exists_eq_two_pow_mul_odd (by omega : n ≠ 0)
  obtain ⟨E, hEU, hab, hodd, hrank, hpi, hinv, hα, hw, F, hF, hJ⟩ :=
    uc22pwt_coreG D.sylowM.isPGroup (uc22pwIndHom L D.T hL.1) ⟨t, htT⟩ C (uc22p20i_sylowBar_isPGroup D)
      hUsyl hq hn hsh' hZ hm' hnem
  have hE := uc22pw_good_of_induced D hL hm' hnem hEU hab hodd hrank hpi hinv hα hw
  have hA := uc22pw_uA_eq_range D hL
  obtain ⟨Bb, Cb, hBE, hCE, -, hcyc, hsqf, hBinv, hCinv, hpiBC, hCsyl, hCirr, hBC⟩ :=
    uc22pw_select_mod_of hab hrank hF
  rw [← hA] at hBinv hCinv hCirr
  obtain ⟨hC1, hC2⟩ := hJ _ hBC
  refine uc22pw_lift214_sel D hB h1930 hL hE hBE hCE hcyc hsqf hBinv hCinv hpiBC hCsyl hCirr ?_ ?_
  · intro hcycBC φ hφ φ' hφ'
    rw [hA] at hφ hφ'
    obtain ⟨g₁, rfl⟩ := hφ
    obtain ⟨g₂, rfl⟩ := hφ'
    exact hC1 hcycBC g₁ g₂
  · intro hp2 φ hφ
    rw [hA] at hφ
    obtain ⟨g, rfl⟩ := hφ
    exact hC2 hp2 g

end Concrete

end CFSG.LocalAnalysis.UniquenessCase.UC22
