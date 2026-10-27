module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S21rU4XF
import CFSG.LocalAnalysis.UniquenessCase.UC22S21r8100Res2
import CFSG.LocalAnalysis.UniquenessCase.UC6R869Pair
import CFSG.LocalAnalysis.UniquenessCase.UC22P22ry
import CFSG.LocalAnalysis.UniquenessCase.UC22P2214Rk
import CFSG.LocalAnalysis.UniquenessCase.UC22InE229Cong
import CFSG.LocalAnalysis.UniquenessCase.UC22InE229Nb
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Fourteen1c
import CFSG.LocalAnalysis.EvenBN.GMSK.SzFacts
import CFSG.SignalizerFunctorTheorem.McBride.Models.Suzuki.Local

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup

variable {G : Type} [Group G] [Finite G]

theorem uc22r3p_card_sq_dvd {M L K : Subgroup G} (hL : L ∈ calC M) (hK : K ∈ calC M)
    (hne : K ≠ L) (hset : conjSetOf M L = {L, K}) {n : ℕ}
    (hS : IsL2 (Bar2 L) n ∨ IsSz (Bar2 L) n) :
    Nat.card (Bar2 L) ^ 2 ∣ Nat.card (Bar2 (conjClosure M L)) := by
  obtain ⟨hcomm, hinf, -, -, hX, -, -⟩ := u4x_bar_structure hL hK hne hset hS
  obtain ⟨e₀, -⟩ := uc22p22l_barImage_equiv hL
  obtain ⟨e₁, -⟩ := uc22p22l_barImage_equiv hK
  obtain ⟨eK⟩ := u4x_bar2_equiv (M := M) (L := L) (K := K) (by rw [hset]; simp)
  have hc₀ : Nat.card ↥(barImage M L) = Nat.card (Bar2 L) := (Nat.card_congr e₀.toEquiv).symm
  have hc₁ : Nat.card ↥(barImage M K) = Nat.card (Bar2 L) :=
    (Nat.card_congr (eK.trans e₁).toEquiv).symm
  have hN : barImage M L ≤ normalizer (barImage M K : Set (Bar2 M)) :=
    le_trans (fun a ha => Subgroup.mem_centralizer_iff.2 fun b hb => (hcomm a ha b hb).symm)
      (centralizer_le_normalizer _)
  have hsup := PartTwo.card_sup_mul_card_inf_of_le_normalizer hN
  rw [inf_comm, hinf, Subgroup.card_bot, mul_one, hc₀, hc₁] at hsup
  obtain ⟨hXM, hMX, -⟩ := uc22p22u_conjClosure_isProd le_rfl Subgroup.le_normalizer hL
  have hdvd := u4x_card_barImage_dvd hXM hMX
  rw [hX, hsup] at hdvd
  rwa [sq]

theorem uc22r3p_pX {D : Data G} {L K : Subgroup G} (hL : L ∈ calC D.M) (hK : K ∈ calC D.M)
    (hne : K ≠ L) (hset : conjSetOf D.M L = {L, K}) (hc2 : (conjSetOf D.M L).ncard = 2)
    {n p : ℕ} (hn : 2 < n) (hp : p ∈ D.sig)
    (hcong : (IsL2 (Bar2 L) n ∧ (2 : ℤ) ^ n ≡ -1 [ZMOD (p : ℤ)]) ∨
      (IsSz (Bar2 L) n ∧ (2 : ℤ) ^ (2 * n) ≡ -1 [ZMOD (p : ℤ)])) :
    ∃ p ∈ D.sig, 2 ≤ CFSG.Open.pRank p (conjClosure D.M L) ∧
      (p = 5 → 2 ^ 12 ∣ Nat.card (Bar2 (conjClosure D.M L))) := by
  obtain ⟨hpp, hp2⟩ := D.sig_prime p hp
  have hsq := uc22r3p_card_sq_dvd hL hK hne hset (hcong.imp And.left And.left)
  have h12 : 2 ^ 6 ∣ Nat.card (Bar2 L) → 2 ^ 12 ∣ Nat.card (Bar2 (conjClosure D.M L)) :=
    fun h6 => calc 2 ^ 12 = (2 ^ 6) ^ 2 := by norm_num
      _ ∣ Nat.card (Bar2 L) ^ 2 := pow_dvd_pow_of_dvd h6 2
      _ ∣ Nat.card (Bar2 (conjClosure D.M L)) := hsq
  rcases hcong with ⟨hL2, hc⟩ | ⟨hSz, hc⟩
  · have hcard := uc22p22r_L2_card hL2
    have hpL : p ∣ Nat.card (Bar2 L) := by
      have e : (2 ^ n) ^ 2 - 1 = (2 ^ n + 1) * (2 ^ n - 1) := by rw [← Nat.sq_sub_sq, one_pow]
      rw [hcard, e]
      exact ((uc22r8100b_dvd_of_modEq hc).mul_right _).mul_left _
    refine ⟨p, hp, UC6.R869S.two_le_pRank_pair_of_isL2 hL hc2 hL2 hpp hp2 hpL,
      fun h5 => h12 ?_⟩
    subst h5
    have hn6 : 6 ≤ n := by
      by_contra h
      interval_cases n <;> norm_num [Int.ModEq] at hc
    rw [hcard]
    exact (Nat.pow_dvd_pow 2 hn6).mul_right _
  · haveI := CFSG.LocalAnalysis.EvenBN.GMSK.isSimpleGroup_of_lieModel_twistedB2 hSz
    have hcard : Nat.card (Bar2 L) = ((2 ^ n) ^ 2 + 1) * (2 ^ n) ^ 2 * (2 ^ n - 1) := by
      obtain ⟨a, ha, rfl, ⟨e⟩⟩ :=
        CFSG.LocalAnalysis.EvenBN.GMSK.exists_mulEquiv_sz_of_lieModel_twistedB2 hSz
      rw [Nat.card_congr
          (e.trans (CFSG.SignalizerFunctorTheorem.McBride.SzModel.szEquiv a)).toEquiv,
        CFSG.SectionRank.card_suzukiMatrixGroup a ha]
    have hpL : p ∣ Nat.card (Bar2 L) := by
      have e : (2 ^ n) ^ 2 + 1 = 2 ^ (2 * n) + 1 := by rw [← pow_mul, mul_comm]
      rw [hcard, e]
      exact ((uc22r8100b_dvd_of_modEq hc).mul_right _).mul_right _
    refine ⟨p, hp, P2214R.two_le_pRank_pair hL hc2 hpp hp2 ?_, fun _ => h12 ?_⟩
    · rw [uc22p21k_center_eq_bot hL.2.2, Subgroup.index_bot]
      exact hpL
    · have h6 : 2 ^ 6 ∣ (2 ^ n) ^ 2 := by
        rw [← pow_mul]
        exact Nat.pow_dvd_pow 2 (by omega)
      rw [hcard]
      exact (h6.trans (dvd_mul_left _ _)).mul_right _

structure R3Pair (D : Data G) (L K : Subgroup G) (n p : ℕ) : Prop where
  hL : L ∈ calC D.M
  hK : K ∈ calC D.M
  hne : K ≠ L
  hset : conjSetOf D.M L = {L, K}
  hc2 : (conjSetOf D.M L).ncard = 2
  hn : 2 < n
  hσ : p ∈ D.sig
  hcong : (IsL2 (Bar2 L) n ∧ (2 : ℤ) ^ n ≡ -1 [ZMOD (p : ℤ)]) ∨
    (IsSz (Bar2 L) n ∧ (2 : ℤ) ^ (2 * n) ≡ -1 [ZMOD (p : ℤ)])

namespace R3Pair

variable {D : Data G} {L K : Subgroup G} {n p : ℕ}

theorem of_two_pow_mul (hL : L ∈ calC D.M) (hK : K ∈ calC D.M) (hne : K ≠ L)
    (hset : conjSetOf D.M L = {L, K}) (hc2 : (conjSetOf D.M L).ncard = 2) {k : ℕ}
    (hL2 : IsL2 (Bar2 L) n) (hp : p ∈ D.sig) (hk : 0 < k) (hn : n = 2 ^ k * p)
    (hcong : (2 : ℤ) ^ n ≡ -1 [ZMOD (p : ℤ)]) : R3Pair D L K n p where
  hL := hL
  hK := hK
  hne := hne
  hset := hset
  hc2 := hc2
  hn := by
    obtain ⟨hpp, hp2⟩ := D.sig_prime p hp
    have h3 : 3 ≤ p := by have := hpp.two_le; omega
    rw [hn]
    exact (by norm_num : 2 < 2 * 3).trans_le (Nat.mul_le_mul (Nat.le_self_pow hk.ne' 2) h3)
  hσ := hp
  hcong := Or.inl ⟨hL2, hcong⟩

theorem mem_K (u : R3Pair D L K n p) : K ∈ conjSetOf D.M L := by rw [u.hset]; simp

theorem shape (u : R3Pair D L K n p) : IsL2 (Bar2 L) n ∨ IsSz (Bar2 L) n :=
  u.hcong.imp And.left And.left

theorem pX (u : R3Pair D L K n p) : ∃ q ∈ D.sig, 2 ≤ CFSG.Open.pRank q (conjClosure D.M L) ∧
    (q = 5 → 2 ^ 12 ∣ Nat.card (Bar2 (conjClosure D.M L))) :=
  uc22r3p_pX u.hL u.hK u.hne u.hset u.hc2 u.hn u.hσ u.hcong

theorem dvd_card_bar2 (u : R3Pair D L K n p) : 2 ^ n - 1 ∣ Nat.card (Bar2 L) := by
  rcases u.shape with hL2 | hSz
  · have e : (2 ^ n) ^ 2 - 1 = (2 ^ n + 1) * (2 ^ n - 1) := by rw [← Nat.sq_sub_sq, one_pow]
    rw [uc22p22r_L2_card hL2, e]
    exact (dvd_mul_left _ _).mul_left _
  · exact uc22ine229_dvd_card_of_isSz hSz

theorem dvd_card_of_dvd (u : R3Pair D L K n p) {q : ℕ} (hq : q ∣ 2 ^ n - 1) :
    q ∣ Nat.card L :=
  hq.trans (u.dvd_card_bar2.trans (Subgroup.card_quotient_dvd_card _))

theorem symm (u : R3Pair D L K n p) : R3Pair D K L n p where
  hL := u.hK
  hK := u.hL
  hne := u.hne.symm
  hset := by rw [uc22p2214_conjSetOf_eq u.mem_K, u.hset, Set.pair_comm]
  hc2 := by rw [uc22p2214_conjSetOf_eq u.mem_K]; exact u.hc2
  hn := u.hn
  hσ := u.hσ
  hcong := by
    obtain ⟨e⟩ := u4x_bar2_equiv u.mem_K
    exact u.hcong.imp (fun h => ⟨CFSG.Blueprint.LieModel.of_mulEquiv e h.1, h.2⟩)
      (fun h => ⟨CFSG.Blueprint.LieModel.of_mulEquiv e h.1, h.2⟩)

theorem conj_cases (u : R3Pair D L K n p) {t : G} (ht : t ∈ D.M) :
    (t ∈ normalizer (L : Set G) ∧ t ∈ normalizer (K : Set G)) ∨
      (L.map (MulAut.conj t).toMonoidHom = K ∧ K.map (MulAut.conj t).toMonoidHom = L) := by
  have hL' : L.map (MulAut.conj t).toMonoidHom ∈ conjSetOf D.M L := ⟨t, ht, rfl⟩
  have hK' : K.map (MulAut.conj t).toMonoidHom ∈ conjSetOf D.M K := ⟨t, ht, rfl⟩
  rw [u.hset] at hL'
  rw [uc22p2214_conjSetOf_eq u.mem_K, u.hset] at hK'
  have hinj := Subgroup.map_injective (f := (MulAut.conj t).toMonoidHom) (MulAut.conj t).injective
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hL' hK'
  rcases hL' with hL' | hL' <;> rcases hK' with hK' | hK'
  · exact absurd (hinj (hL'.trans hK'.symm)).symm u.hne
  · exact Or.inl ⟨mem_normalizer_iff_map_conj_eq.2 hL', mem_normalizer_iff_map_conj_eq.2 hK'⟩
  · exact Or.inr ⟨hL', hK'⟩
  · exact absurd (hinj (hL'.trans hK'.symm)).symm u.hne

theorem conj_mem_V (u : R3Pair D L K n p) {x₀ x₁ : Bar2 D.M} (hx₀ : x₀ ∈ barImage D.M L)
    (hx₁ : x₁ ∈ barImage D.M K)
    (hN : x₀ * x₁ ∈ normalizer (barImage D.M D.T : Set (Bar2 D.M))) {t : ↥D.M}
    (ht : (t : G) ∈ D.T) :
    uc22p21cPi D.M t * (x₀ * x₁⁻¹) * (uc22p21cPi D.M t)⁻¹ ∈
      zpowers (x₀ * x₁⁻¹) ⊔ (barImage D.M D.T ⊓ (barImage D.M L ⊔ barImage D.M K)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hcomm, hinf, -, -, -, hXn, -⟩ := u4x_bar_structure u.hL u.hK u.hne u.hset u.shape
  have hT := u4x_isSylowOf_barImage (p := 2) D.sylowM
  have hτ : uc22p21cPi D.M t ∈ barImage D.M D.T := uc22p21c_mem_barImage.2 ⟨t, ht, rfl⟩
  set τ := uc22p21cPi D.M t with hτdef
  have hβ : τ * (x₀ * x₁) * τ⁻¹ * (x₀ * x₁)⁻¹ ∈ barImage D.M D.T := by
    rw [show τ * (x₀ * x₁) * τ⁻¹ * (x₀ * x₁)⁻¹ = τ * (x₀ * x₁ * τ⁻¹ * (x₀ * x₁)⁻¹) by group]
    exact mul_mem hτ ((mem_normalizer_iff.1 hN τ⁻¹).1 (inv_mem hτ))
  have hS : ∀ {s}, s ∈ barImage D.M D.T → s ∈ barImage D.M L ⊔ barImage D.M K →
      s ∈ zpowers (x₀ * x₁⁻¹) ⊔ (barImage D.M D.T ⊓ (barImage D.M L ⊔ barImage D.M K)) :=
    fun h₁ h₂ => mem_sup_right ⟨h₁, h₂⟩
  have hy : x₀ * x₁⁻¹ ∈
      zpowers (x₀ * x₁⁻¹) ⊔ (barImage D.M D.T ⊓ (barImage D.M L ⊔ barImage D.M K)) :=
    mem_sup_left (mem_zpowers _)
  rcases u.conj_cases t.2 with ⟨h0, h1⟩ | ⟨h0, h1⟩
  · have ha : τ * x₀ * τ⁻¹ * x₀⁻¹ ∈ barImage D.M L :=
      mul_mem ((mem_normalizer_iff.1 (uc22ine229_mk_mem_normalizer h0) x₀).1 hx₀) (inv_mem hx₀)
    have hb : τ * x₁ * τ⁻¹ * x₁⁻¹ ∈ barImage D.M K :=
      mul_mem ((mem_normalizer_iff.1 (uc22ine229_mk_mem_normalizer h1) x₁).1 hx₁) (inv_mem hx₁)
    have e1 := hcomm x₀ hx₀ _ hb
    have e : τ * (x₀ * x₁) * τ⁻¹ * (x₀ * x₁)⁻¹ =
        τ * x₀ * τ⁻¹ * x₀⁻¹ * (τ * x₁ * τ⁻¹ * x₁⁻¹) := by
      calc τ * (x₀ * x₁) * τ⁻¹ * (x₀ * x₁)⁻¹ =
          τ * x₀ * τ⁻¹ * x₀⁻¹ * (x₀ * (τ * x₁ * τ⁻¹ * x₁⁻¹)) * x₀⁻¹ := by group
        _ = τ * x₀ * τ⁻¹ * x₀⁻¹ * (τ * x₁ * τ⁻¹ * x₁⁻¹ * x₀) * x₀⁻¹ := by rw [e1]
        _ = τ * x₀ * τ⁻¹ * x₀⁻¹ * (τ * x₁ * τ⁻¹ * x₁⁻¹) := by group
    obtain ⟨haT, hbT⟩ := u4x_mem_of_mul_mem hcomm hinf hT hXn ha hb (by rw [← e]; exact hβ)
    rw [show τ * (x₀ * x₁⁻¹) * τ⁻¹ =
      τ * x₀ * τ⁻¹ * x₀⁻¹ * (x₀ * x₁⁻¹) * (τ * x₁ * τ⁻¹ * x₁⁻¹)⁻¹ by group]
    exact mul_mem (mul_mem (hS haT (mem_sup_left ha)) hy) (inv_mem (hS hbT (mem_sup_right hb)))
  · have h0' : τ * x₀ * τ⁻¹ ∈ barImage D.M K := u4x_conj_mem_barImage h0 hx₀
    have h1' : τ * x₁ * τ⁻¹ ∈ barImage D.M L := u4x_conj_mem_barImage h1 hx₁
    have ha : τ * x₁ * τ⁻¹ * x₀⁻¹ ∈ barImage D.M L := mul_mem h1' (inv_mem hx₀)
    have hb : τ * x₀ * τ⁻¹ * x₁⁻¹ ∈ barImage D.M K := mul_mem h0' (inv_mem hx₁)
    have e1 := hcomm _ h1' _ h0'
    have e2 := hcomm _ (inv_mem hx₀) _ hb
    have e : τ * (x₀ * x₁) * τ⁻¹ * (x₀ * x₁)⁻¹ =
        τ * x₁ * τ⁻¹ * x₀⁻¹ * (τ * x₀ * τ⁻¹ * x₁⁻¹) := by
      calc τ * (x₀ * x₁) * τ⁻¹ * (x₀ * x₁)⁻¹ =
          τ * x₀ * τ⁻¹ * (τ * x₁ * τ⁻¹) * x₁⁻¹ * x₀⁻¹ := by group
        _ = τ * x₁ * τ⁻¹ * (τ * x₀ * τ⁻¹) * x₁⁻¹ * x₀⁻¹ := by rw [← e1]
        _ = τ * x₁ * τ⁻¹ * (τ * x₀ * τ⁻¹ * x₁⁻¹ * x₀⁻¹) := by group
        _ = τ * x₁ * τ⁻¹ * (x₀⁻¹ * (τ * x₀ * τ⁻¹ * x₁⁻¹)) := by rw [← e2]
        _ = τ * x₁ * τ⁻¹ * x₀⁻¹ * (τ * x₀ * τ⁻¹ * x₁⁻¹) := by group
    obtain ⟨haT, hbT⟩ := u4x_mem_of_mul_mem hcomm hinf hT hXn ha hb (by rw [← e]; exact hβ)
    rw [show τ * (x₀ * x₁⁻¹) * τ⁻¹ =
      τ * x₀ * τ⁻¹ * x₁⁻¹ * (x₀ * x₁⁻¹)⁻¹ * (τ * x₁ * τ⁻¹ * x₀⁻¹)⁻¹ by group]
    exact mul_mem (mul_mem (hS hbT (mem_sup_right hb)) (inv_mem hy))
      (inv_mem (hS haT (mem_sup_left ha)))

end R3Pair

end CFSG.LocalAnalysis.UniquenessCase.UC22
