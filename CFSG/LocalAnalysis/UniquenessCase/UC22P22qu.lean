module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P22qq
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22ql
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22qo
public import CFSG.GroupTheory.ABGLocalTools.ZJFactorization
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22qp

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup CFSG.ABGLocalTools
open CFSG.Blueprint (LieModel)
open CFSG.ASVolI.ChIJK (IsWeaklyClosedIn)

variable {G : Type} [Group G] [Finite G]

theorem uc22p22qu_M_le_normalizer_R (M : Subgroup G) : M ≤ normalizer (pCoreOf 2 M : Set G) :=
  CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 M

theorem uc22p22qu_Q_le (D : Data G) {p : ℕ} {L : Subgroup G}
    (hfrob : CFSG.Open.uniqueFourIsFrobenius
      (CFSG.Open.uniqueFourPrimeCore p D.M ⊔ centralizer (L : Set G)) (CFSG.Open.pCoreOf 2 D.M)
      (centralizer (L : Set G))) :
    ∀ q ∈ CFSG.Open.uniqueFourPrimeCore p D.M, ∃ r ∈ CFSG.Open.pCoreOf 2 D.M, ∃ d ∈ centralizer (L : Set G),
      q = r * d := by
  intro q hq
  obtain ⟨hDM, -⟩ := uc22p22qk_frob_unpack D hfrob
  have hXKV : CFSG.Open.uniqueFourPrimeCore p D.M ⊔ centralizer (L : Set G) =
      CFSG.Open.pCoreOf 2 D.M ⊔ centralizer (L : Set G) := hfrob.2.2.2.2.2.1
  have hDN : centralizer (L : Set G) ≤ normalizer (pCoreOf 2 D.M : Set G) := fun d hd =>
    uc22p22qu_M_le_normalizer_R D.M (hDM hd)
  have hq' : q ∈ pCoreOf 2 D.M ⊔ centralizer (L : Set G) := by
    rw [← hXKV]
    exact Subgroup.mem_sup_left hq
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left (pCoreOf 2 D.M) _ hDN] at hq'
  obtain ⟨r, hr, d, hd, hrd⟩ := hq'
  have hrd' : r * d = q := hrd
  exact ⟨r, hr, d, hd, hrd'.symm⟩

theorem uc22p22qu_L_inf_R (D : Data G) {p : ℕ} {P₀ L : Subgroup G} (hP₀ : P₀ ≠ ⊥)
    (hLX : L ≤ centralizer (P₀ : Set G))
    (hfrob : CFSG.Open.uniqueFourIsFrobenius
      (CFSG.Open.uniqueFourPrimeCore p D.M ⊔ centralizer (L : Set G)) (CFSG.Open.pCoreOf 2 D.M)
      (centralizer (L : Set G))) :
    ∀ y ∈ L, y ∈ pCoreOf 2 D.M → y = 1 := by
  intro y hy hyR
  obtain ⟨-, hfpf⟩ := uc22p22qk_frob_unpack D hfrob
  obtain ⟨⟨z, hz⟩, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hP₀
  have hz1' : z ≠ 1 := fun h => hz1 (Subtype.ext h)
  have hzD : z ∈ centralizer (L : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    exact (Subgroup.mem_centralizer_iff.1 (hLX hl) z hz).symm
  have hyz : z * y = y * z := (Subgroup.mem_centralizer_iff.1 (hLX hy) z hz)
  exact hfpf z hzD hz1' y hyR (by rw [hyz]; group)

theorem uc22p22qu_Dd_odd (D : Data G) {p : ℕ} {L : Subgroup G}
    (hfrob : CFSG.Open.uniqueFourIsFrobenius
      (CFSG.Open.uniqueFourPrimeCore p D.M ⊔ centralizer (L : Set G)) (CFSG.Open.pCoreOf 2 D.M)
      (centralizer (L : Set G))) :
    ∀ d ∈ centralizer (L : Set G), Odd (orderOf d) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro d hd
  obtain ⟨hDM, hfpf⟩ := uc22p22qk_frob_unpack D hfrob
  by_contra hev
  rw [Nat.not_odd_iff_even] at hev
  obtain ⟨k, hk⟩ := hev
  have hpos : 0 < orderOf d := orderOf_pos d
  have hkpos : 0 < k := by omega
  have ht2 : (d ^ k) ^ 2 = 1 := by
    rw [← pow_mul, show k * 2 = orderOf d by omega]
    exact pow_orderOf_eq_one d
  have ht1 : d ^ k ≠ 1 := by
    intro h
    have := Nat.le_of_dvd hkpos (orderOf_dvd_of_pow_eq_one h)
    omega
  have htD : d ^ k ∈ centralizer (L : Set G) := Subgroup.pow_mem _ hd k
  have hR2 : IsPGroup 2 (pCoreOf 2 D.M) := uc22p22qh_isPGroup_pCoreOf D.M
  have htR : ∀ w ∈ pCoreOf 2 D.M, d ^ k * w * (d ^ k)⁻¹ ∈ pCoreOf 2 D.M := fun w hw =>
    uc22p22qh_conj_mem_pCoreOf (hDM htD) hw
  obtain ⟨w, hwR, hw1, htw⟩ := uc22p22q_exists_fixed_involution ht2 hR2 hfrob.1 htR
  exact hw1 (hfpf _ htD ht1 w hwR htw)

theorem uc22p22qu_strong_of_weak {p : ℕ} (hp : p.Prime) {P P₀ : Subgroup G} (hcard : Nat.card P₀ = p)
    (hwe : ∀ g : G, (∀ x ∈ P₀, g⁻¹ * x * g ∈ P) → ∀ x ∈ P₀, g⁻¹ * x * g ∈ P₀) :
    ∀ a ∈ P₀, ∀ m : G, m⁻¹ * a * m ∈ P → m⁻¹ * a * m ∈ P₀ := by
  intro a ha m hm
  by_cases ha1 : a = 1
  · subst ha1
    simpa using P₀.one_mem
  · have hdvd : orderOf a ∣ p := by
      rw [← hcard]
      exact Subgroup.orderOf_dvd_natCard P₀ ha
    have hord : orderOf a = p :=
      ((Nat.dvd_prime hp).1 hdvd).resolve_left (fun h => ha1 (orderOf_eq_one_iff.1 h))
    have hzle : Subgroup.zpowers a ≤ P₀ := Subgroup.zpowers_le.2 ha
    have hzeq : Subgroup.zpowers a = P₀ := by
      apply Subgroup.eq_of_le_of_card_ge hzle
      rw [Nat.card_zpowers, hord, hcard]
    refine hwe m (fun x hx => ?_) a ha
    rw [← hzeq] at hx
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    have e : m⁻¹ * a ^ i * m = (m⁻¹ * a * m) ^ i := by
      have := conj_zpow (a := m⁻¹) (b := a) (i := i)
      simpa using this.symm
    rw [e]
    exact P.zpow_mem hm i

theorem uc22p22qu_P0Q_normal (D : Data G) {p : ℕ} {P P₀ : Subgroup G} (hH : UC6.Hyp612 D p P P₀)
    (hsolv : Group.IsSolvable ↥D.M) (hwc : IsWeaklyClosedIn P₀ P) :
    D.M ≤ normalizer ((P₀ ⊔ uniqueFourPrimeCore p D.M : Subgroup G) : Set G) := by
  have hpσ : p ∈ D.sig := by
    rw [D.sig_sub]
    exact Or.inl (Or.inr hH.mem_sig2)
  have hpP : p.Prime := (D.sig_prime p hpσ).1
  haveI : Fact p.Prime := ⟨hpP⟩
  have hP₀1 : P₀ ≠ ⊥ := by
    intro h
    have := hH.card
    rw [h, Subgroup.card_bot] at this
    exact hpP.one_lt.ne this
  refine uc22p22qp_normal_of_strongly_closed hsolv hH.sylow hH.le hP₀1
    (fun a ha m _ hm => uc22p22qu_strong_of_weak hpP hH.card (uc22p22q_weak_elem hwc) a ha m hm) ?_
  intro N hNM hNn
  have hdvd : Nat.card ↥(P₀ ⊓ N) ∣ p := by
    rw [← hH.card]
    exact Subgroup.card_dvd_of_le inf_le_left
  rcases (Nat.dvd_prime hpP).1 hdvd with h1 | h1
  · left
    exact Subgroup.card_eq_one.1 h1
  · right
    have : P₀ ⊓ N = P₀ :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hH.card, h1])
    rw [← this]
    exact inf_le_right

theorem uc22p22qu_isSylowOf_sup {p : ℕ} [Fact p.Prime] {M S : Subgroup G} (hSM : S ≤ M) (hS : IsPGroup p S) :
    IsSylowOf p S (S ⊔ uniqueFourPrimeCore p M) := by
  have hQ' : uniqueFourPrimeCore p M = (CFSG.pPrimeCore p ↥M).map M.subtype :=
    CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple.relPPrimeCore_eq_map Fact.out M
  have h1 : IsSylowOf p (S.subgroupOf M) (CFSG.pPrimeCore p ↥M ⊔ S.subgroupOf M) :=
    isSylowOf_sup_of_coprime (N := CFSG.pPrimeCore p ↥M) pPrimeCore_coprime_card hS.comap_subtype
  have h2 := (isSylowOf_map_subtype_iff (p := p) M).2 h1
  rwa [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hSM, ← hQ', sup_comm] at h2

theorem uc22p22qu_P1Q_normal (D : Data G) (hstd : Sigma23Std D) {p : ℕ} {P P₀ : Subgroup G}
    (hH : UC6.Hyp612 D p P P₀) (hd : UC6.R613DefAt D p P P₀) :
    D.M ≤ normalizer (((P ⊓ UC6.inftyOf (centralizer (P₀ : Set G))) ⊔ uniqueFourPrimeCore p D.M : Subgroup G) :
      Set G) := by
  obtain ⟨⟨hp3, hsolv, hwc, hΓ, hL, hfrob⟩, hcent⟩ := hd
  have hpσ : p ∈ D.sig := by
    rw [D.sig_sub]
    exact Or.inl (Or.inr hH.mem_sig2)
  have hpP : p.Prime := (D.sig_prime p hpσ).1
  haveI : Fact p.Prime := ⟨hpP⟩
  have hp2 : p ≠ 2 := (D.sig_prime p hpσ).2
  have hirrP := uc22p22q_irr_P1 D hstd hH hwc hL hp2 hΓ
  have hne := uc22p22q_P1_ne_bot D hstd hH hwc hL hp2
  have hsc := (uc22p22q_stronglyClosed_P1 D hstd hH hwc hcent).2
  refine uc22p22qp_normal_of_strongly_closed hsolv hH.sylow inf_le_left hne
    (fun a ha m _ hm => hsc a ha m hm) ?_
  intro N hNM hNn
  have hnorm : D.M ⊓ normalizer ((P ⊓ UC6.inftyOf (centralizer (P₀ : Set G)) : Subgroup G) : Set G) ≤
      normalizer (((P ⊓ UC6.inftyOf (centralizer (P₀ : Set G))) ⊓ N : Subgroup G) : Set G) := by
    rintro n ⟨hnM, hnP⟩
    exact inf_normalizer_le_normalizer_inf ⟨hnP, uc22p22qk_mem_normalizer fun k hk => hNn n hnM k hk⟩
  rcases hirrP _ inf_le_left hnorm with h | h
  · exact Or.inl h
  · exact Or.inr (inf_eq_left.1 h)

end CFSG.LocalAnalysis.UniquenessCase.UC22
