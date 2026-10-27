module
public import CFSG.Quasithin.Vol2.Ch12Sec6P31WXV
public import CFSG.Quasithin.Vol2.Ch12Sec6P31WXU3P
public import CFSG.Quasithin.EmptyFaithful.R3c3Rank
public import CFSG.LocalAnalysis.EvenBN.GMSK.CatSporadicBenderLarge
public import CFSG.GroupTheory.SteinbergCBFTSCN
public import CFSG.Quasithin.Vol2.Ch12Sec6P31PropACore

public section
namespace CFSG.Quasithin.H13.P31A
open scoped Pointwise
open CFSG.Open
variable {X : Type} [Group X]

theorem no_three_of_centralizer {K : Subgroup X} [K.Normal] [Finite X]
    (hZ : Subgroup.center ↥K = ⊥)
    (hK3 : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup ↥K))
    (hX3 : CFSG.Open.pRank 3 (⊤ : Subgroup X) ≤ 2) :
    ∀ c ∈ Subgroup.centralizer (K : Set X), c ^ 3 = 1 → c = 1 := by
  classical
  set C : Subgroup X := Subgroup.centralizer (K : Set X) with hCdef
  have hKC : K ⊓ C = ⊥ := inf_centralizer_eq_bot_of_center_eq_bot hZ
  have hcomm : ∀ k ∈ K, ∀ c ∈ C, k * c = c * k := fun k hk c hc =>
    Subgroup.mem_centralizer_iff.mp hc k hk
  have hK3' : 2 ≤ CFSG.Open.pRank 3 K := by
    rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup (p := 3) (G := X) (H := K)]
    exact hK3
  have hrank : CFSG.Open.pRank 3 K + CFSG.Open.pRank 3 C ≤
      CFSG.Open.pRank 3 (⊤ : Subgroup X) :=
    (pRank_add_pRank_le_of_commute Nat.prime_three hKC hcomm).trans
      (CFSG.SectionRank.pRank_mono (p := 3) (by norm_num) le_top)
  have hC0 : CFSG.Open.pRank 3 C = 0 := by omega
  intro c hc hc3
  by_contra hne
  have hord : orderOf c = 3 := orderOf_eq_prime hc3 hne
  have hcard : Nat.card (Subgroup.zpowers c) = 3 ^ 1 := by
    rw [Nat.card_zpowers, hord]; rfl
  have hle : Subgroup.zpowers c ≤ C := (Subgroup.zpowers_le).mpr hc
  have h1 := CFSG.SectionRank.le_pRank (by norm_num : 1 < 3) hle
    (CFSG.Open.isElemAbelian_zpowers hc3) hcard
  omega

theorem exists_mem_inf_mod_of_mem_inf_sup {K L₁ : Subgroup X} [K.Normal] [Finite X]
    (hC3 : ∀ c ∈ Subgroup.centralizer (K : Set X), c ^ 3 = 1 → c = 1)
    (hL₁3 : ∀ g ∈ L₁, ∃ k : ℕ, g ^ (3 ^ k) ∈ pCoreOf 2 L₁) :
    ∀ g ∈ L₁ ⊓ (K ⊔ Subgroup.centralizer (K : Set X)),
      ∃ k ∈ L₁ ⊓ K, g * k⁻¹ ∈ pCoreOf 2 L₁ := by
  classical
  set C : Subgroup X := Subgroup.centralizer (K : Set X) with hCdef
  have hC3' : ∀ a : ℕ, ∀ c ∈ C, c ^ (3 ^ a) = 1 → c = 1 := by
    intro a
    induction a with
    | zero => intro c _ h; simpa using h
    | succ a ih =>
      intro c hc h
      apply ih c hc
      apply hC3 _ (C.pow_mem hc _)
      rw [← pow_mul, ← pow_succ]
      exact h
  set e := Nat.card X with he
  have he0 : e ≠ 0 := Nat.card_pos.ne'
  set a := e.factorization 3
  set b := e / 3 ^ a
  have hab : 3 ^ a * b = e := Nat.ordProj_mul_ordCompl_eq_self e 3
  have hcop : Nat.Coprime (3 ^ a) b :=
    Nat.Coprime.pow_left a (Nat.coprime_ordCompl Nat.prime_three he0)
  obtain ⟨n, hn1, hn0⟩ := Nat.chineseRemainder hcop 1 0
  obtain ⟨m, hm0, hm1⟩ := Nat.chineseRemainder hcop 0 1
  have hnm : n + m ≡ 1 [MOD e] := by
    rw [← hab, ← Nat.modEq_and_modEq_iff_modEq_mul hcop]
    exact ⟨by simpa using hn1.add hm0, by simpa using hn0.add hm1⟩
  have hdvd_n : e ∣ n * 3 ^ a := by
    rw [← hab, mul_comm (3 ^ a) b]
    exact Nat.mul_dvd_mul_right ((Nat.modEq_zero_iff_dvd).mp hn0) _
  have hdvd_m : e ∣ m * b := by
    rw [← hab]
    exact Nat.mul_dvd_mul_right ((Nat.modEq_zero_iff_dvd).mp hm0) _
  have hpowe : ∀ x : X, ∀ k : ℕ, e ∣ k → x ^ k = 1 := by
    intro x k hk
    obtain ⟨j, rfl⟩ := hk
    rw [pow_mul, he, pow_card_eq_one', one_pow]
  intro g ⟨hgL, hgW⟩
  have hgW' : g ∈ ((K ⊔ C : Subgroup X) : Set X) := hgW
  rw [Subgroup.normal_mul] at hgW'
  obtain ⟨k, hk, c, hc, rfl⟩ := Set.mem_mul.mp hgW'
  have hkc : Commute k c := Subgroup.mem_centralizer_iff.mp hc k hk
  have hcn : c ^ n = 1 := by
    apply hC3' a _ (C.pow_mem hc n)
    rw [← pow_mul]
    exact hpowe c _ hdvd_n
  refine ⟨(k * c) ^ n, ⟨L₁.pow_mem hgL n, ?_⟩, ?_⟩
  · rw [hkc.mul_pow, hcn, mul_one]
    exact K.pow_mem hk n
  ·
    set g := k * c
    have hg1 : g ^ (n + m) = g := by
      have := (pow_eq_pow_iff_modEq (x := g)).mpr
        (hnm.of_dvd (orderOf_dvd_of_pow_eq_one (hpowe g e dvd_rfl)))
      simpa using this
    have hgm : g * (g ^ n)⁻¹ = g ^ m := by
      rw [pow_add] at hg1
      calc g * (g ^ n)⁻¹ = (g ^ n)⁻¹ * g := by
              rw [(Commute.self_pow g n).inv_right.eq]
        _ = g ^ m := by
              rw [inv_mul_eq_iff_eq_mul, hg1]
    rw [hgm]
    set h := g ^ m
    have hhL : h ∈ L₁ := L₁.pow_mem hgL m
    have hhb : h ^ b = 1 := by rw [← pow_mul]; exact hpowe g _ hdvd_m
    obtain ⟨j, hj⟩ := hL₁3 h hhL
    have hcop3 : Nat.Coprime 3 b := Nat.coprime_ordCompl Nat.prime_three he0
    have hcopj : Nat.Coprime (3 ^ j) (orderOf h) :=
      Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one hhb) (hcop3.pow_left j)
    obtain ⟨u, hu⟩ := exists_pow_eq_self_of_coprime hcopj
    rw [← hu]
    exact (pCoreOf 2 L₁).pow_mem hj u

theorem commutator_mem_pCore_of_le_normalizer {K L₁ T : Subgroup X} [K.Normal] [Finite X]
    (hT2 : IsPGroup 2 T)
    (hTL : T ≤ Subgroup.normalizer (L₁ : Set X))
    (hLB : L₁ ⊓ K ≤ Subgroup.normalizer ((T ⊓ K : Subgroup X) : Set X)) :
    ∀ u ∈ T ⊓ K, ∀ k ∈ L₁ ⊓ K, u * k * u⁻¹ * k⁻¹ ∈ pCoreOf 2 L₁ := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hN : (T ⊓ K) ⊓ (L₁ ⊓ K) ≤ pCoreOf 2 (L₁ ⊓ K) := by
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right ?_ ?_
    · intro k hk
      have h1 := Subgroup.mem_normalizer_iff.mp (hLB hk)
      have h2 := Subgroup.mem_normalizer_iff.mp ((L₁ ⊓ K).le_normalizer hk)
      rw [Subgroup.mem_normalizer_iff]
      intro g
      simp only [SetLike.mem_coe, Subgroup.mem_inf] at h1 h2 ⊢
      constructor
      · rintro ⟨⟨a, b⟩, c, d⟩
        exact ⟨(h1 g).mp ⟨a, b⟩, (h2 g).mp ⟨c, d⟩⟩
      · rintro ⟨⟨a, b⟩, c, d⟩
        exact ⟨(h1 g).mpr ⟨a, b⟩, (h2 g).mpr ⟨c, d⟩⟩
    · exact hT2.to_le (inf_le_left.trans inf_le_left)
  have hcore : pCoreOf 2 (L₁ ⊓ K) ≤ pCoreOf 2 L₁ := by
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans inf_le_left) ?_
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)
    intro l hl
    have hlLK : l ∈ Subgroup.normalizer ((L₁ ⊓ K : Subgroup X) : Set X) := by
      rw [Subgroup.mem_normalizer_iff]
      intro g
      constructor
      · rintro ⟨hgL, hgK⟩
        exact ⟨L₁.mul_mem (L₁.mul_mem hl hgL) (L₁.inv_mem hl),
          (inferInstance : K.Normal).conj_mem g hgK l⟩
      · rintro ⟨hgL, hgK⟩
        refine ⟨?_, ?_⟩
        · have := L₁.mul_mem (L₁.mul_mem (L₁.inv_mem hl) hgL) hl
          simpa [mul_assoc] using this
        · have := (inferInstance : K.Normal).conj_mem _ hgK l⁻¹
          simpa [mul_assoc] using this
    exact CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _ hlLK
  intro u hu k hk
  refine hcore (hN ⟨?_, ?_⟩)
  ·
    have hk' : k * u⁻¹ * k⁻¹ ∈ T ⊓ K :=
      (Subgroup.mem_normalizer_iff.mp (hLB hk) u⁻¹).mp ((T ⊓ K).inv_mem hu)
    have := (T ⊓ K).mul_mem hu hk'
    simpa [mul_assoc] using this
  ·
    have hL : u * k * u⁻¹ ∈ L₁ :=
      (Subgroup.mem_normalizer_iff.mp (hTL hu.1) k).mp hk.1
    have hK : u * k * u⁻¹ ∈ K := (inferInstance : K.Normal).conj_mem k hk.2 u
    exact ⟨L₁.mul_mem hL (L₁.inv_mem hk.1), K.mul_mem hK (K.inv_mem hk.2)⟩

theorem false_of_borel_out2 {K L₁ T : Subgroup X} [K.Normal] [Finite X]
    (hZ : Subgroup.center ↥K = ⊥)
    (hK3 : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup ↥K))
    (hX3 : CFSG.Open.pRank 3 (⊤ : Subgroup X) ≤ 2)
    (hOut : ∀ P : Subgroup (CFSG.ComponentClassification.OuterAutomorphisms.Outer ↥K),
      IsPGroup 2 ↥P → Nat.card ↥P ≤ 2)
    (hT2 : IsPGroup 2 T) (hTmax : ∀ S : Subgroup X, IsPGroup 2 S → T ≤ S → S = T)
    (hTL : T ≤ Subgroup.normalizer (L₁ : Set X))
    (hL₁3 : ∀ g ∈ L₁, ∃ k : ℕ, g ^ (3 ^ k) ∈ pCoreOf 2 L₁)
    (hLB : L₁ ⊓ K ≤ Subgroup.normalizer ((T ⊓ K : Subgroup X) : Set X))
    {x y t₁ t₂ : X} (hx : x ∈ L₁) (hy : y ∈ L₁) (ht₁ : t₁ ∈ T) (ht₂ : t₂ ∈ T)
    (h₁ : t₁ * x * t₁⁻¹ * x ∈ pCoreOf 2 L₁) (h₂ : t₂ * x * t₂⁻¹ * y⁻¹ ∈ pCoreOf 2 L₁)
    (h₃ : t₂ * y * t₂⁻¹ * x⁻¹ ∈ pCoreOf 2 L₁)
    (hx₂ : x ^ 2 ∉ pCoreOf 2 L₁) (hyx : y * x ∉ pCoreOf 2 L₁)
    (hyx' : y * x⁻¹ ∉ pCoreOf 2 L₁) : False := by
  classical
  let C : Subgroup X := Subgroup.centralizer (K : Set X)
  let W : Subgroup X := K ⊔ C
  let O : Subgroup X := pCoreOf 2 L₁
  haveI : C.Normal := Subgroup.normal_centralizer
  haveI : W.Normal := Subgroup.sup_normal K C
  have hKC : K ⊓ C = ⊥ := inf_centralizer_eq_bot_of_center_eq_bot hZ
  have hcomm : ∀ k ∈ K, ∀ c ∈ C, k * c = c * k := fun k hk c hc =>
    Subgroup.mem_centralizer_iff.mp hc k hk
  have hC3 := no_three_of_centralizer hZ hK3 hX3
  have hstep2 := exists_mem_inf_mod_of_mem_inf_sup (L₁ := L₁) hC3 hL₁3
  have hstep3 := commutator_mem_pCore_of_le_normalizer hT2 hTL hLB
  have hOn : ∀ r ∈ L₁, ∀ o ∈ O, r * o * r⁻¹ ∈ O := by
    intro r hr o ho
    have hN : r ∈ Subgroup.normalizer (O : Set X) :=
      CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L₁ hr
    exact (Subgroup.mem_normalizer_iff.mp hN o).mp ho
  have hTO : T ≤ Subgroup.normalizer (O : Set X) :=
    hTL.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L₁)
  have hOL : O ≤ L₁ := CFSG.openPCoreOf_le 2 L₁
  have hpowc : ∀ a ∈ L₁, ∀ b : X, a * b⁻¹ ∈ O → ∀ i : ℕ, a ^ i * (b ^ i)⁻¹ ∈ O := by
    intro a ha b hab i
    induction i with
    | zero => simp
    | succ i ih =>
      have h1 := hOn a ha _ ih
      have : a ^ (i + 1) * (b ^ (i + 1))⁻¹ = a * (a ^ i * (b ^ i)⁻¹) * a⁻¹ * (a * b⁻¹) := by
        group
      rw [this]
      exact O.mul_mem h1 hab
  have hstep4 : T ⊓ W = (T ⊓ K) ⊔ (T ⊓ C) := sylow_inf_sup_centralizer_eq hKC hT2 hTmax
  have htriv : ∀ s ∈ T ⊓ W, ∀ r ∈ L₁, s * r * s⁻¹ * r⁻¹ ∈ O := by
    intro s hs r hr
    have hsT : s ∈ T := hs.1
    have hsW : s ∈ W := hs.2
    have hsL : ∀ z ∈ L₁, s * z * s⁻¹ ∈ L₁ := fun z hz =>
      (Subgroup.mem_normalizer_iff.mp (hTL hsT) z).mp hz
    have hsO : ∀ z ∈ O, s * z * s⁻¹ ∈ O := fun z hz =>
      (Subgroup.mem_normalizer_iff.mp (hTO hsT) z).mp hz
    have hfix : ∀ k ∈ L₁ ⊓ K, s * k * s⁻¹ * k⁻¹ ∈ O := by
      intro k hk
      have hDnorm : T ⊓ C ≤ Subgroup.normalizer (T ⊓ K : Set X) :=
        (inf_le_right : T ⊓ C ≤ C).trans
          (le_normalizer_of_comm (K := K) (C := C) (H := T ⊓ K) inf_le_right hcomm)
      have hset : (((T ⊓ K) ⊔ (T ⊓ C) : Subgroup X) : Set X) =
          ((T ⊓ K : Subgroup X) : Set X) * ((T ⊓ C : Subgroup X) : Set X) :=
        Subgroup.coe_mul_of_right_le_normalizer_left (T ⊓ K) (T ⊓ C) hDnorm
      have hs' : s ∈ ((T ⊓ K : Subgroup X) : Set X) * ((T ⊓ C : Subgroup X) : Set X) := by
        rw [← hset, ← hstep4]
        exact hs
      obtain ⟨u, hu, c, hc, huc⟩ := Set.mem_mul.mp hs'
      have hck : c * k = k * c := (Subgroup.mem_centralizer_iff.mp hc.2 k hk.2).symm
      have key : (u * c) * k * (u * c)⁻¹ * k⁻¹ = u * k * u⁻¹ * k⁻¹ := by
        calc (u * c) * k * (u * c)⁻¹ * k⁻¹
            = u * (c * k) * c⁻¹ * u⁻¹ * k⁻¹ := by group
          _ = u * (k * c) * c⁻¹ * u⁻¹ * k⁻¹ := by rw [hck]
          _ = u * k * u⁻¹ * k⁻¹ := by group
      rw [← huc, key]
      exact hstep3 u hu k hk
    obtain ⟨e, hedef⟩ : ∃ e, e = s * r * s⁻¹ * r⁻¹ := ⟨_, rfl⟩
    rw [← hedef]
    have heL : e ∈ L₁ := hedef ▸ L₁.mul_mem (hsL r hr) (L₁.inv_mem hr)
    have heW : e ∈ W := by
      have : e = s * (r * s⁻¹ * r⁻¹) := by rw [hedef]; group
      rw [this]
      refine W.mul_mem hsW ?_
      have h := (inferInstance : W.Normal).conj_mem s⁻¹ (W.inv_mem hsW) r
      simpa [mul_assoc] using h
    obtain ⟨k, hk, hek⟩ := hstep2 e ⟨heL, heW⟩
    have hse : s * e * s⁻¹ * e⁻¹ ∈ O := by
      have : s * e * s⁻¹ * e⁻¹ =
          (s * (e * k⁻¹) * s⁻¹) * (s * k * s⁻¹ * k⁻¹) * (e * k⁻¹)⁻¹ := by group
      rw [this]
      exact O.mul_mem (O.mul_mem (hsO _ hek) (hfix k hk)) (O.inv_mem hek)
    have hiter : ∀ i : ℕ, s ^ i * r * (s ^ i)⁻¹ * (e ^ i * r)⁻¹ ∈ O := by
      intro i
      induction i with
      | zero => simp
      | succ i ih =>
        have h1 := hsO _ ih
        have h2 := hpowc _ (hsL e heL) e hse i
        have : s ^ (i + 1) * r * (s ^ (i + 1))⁻¹ * (e ^ (i + 1) * r)⁻¹ =
            (s * (s ^ i * r * (s ^ i)⁻¹ * (e ^ i * r)⁻¹) * s⁻¹) *
              (s * (e ^ i * r) * s⁻¹ * (e ^ (i + 1) * r)⁻¹) := by group
        rw [this]
        refine O.mul_mem h1 ?_
        have h3 : s * (e ^ i * r) * s⁻¹ * (e ^ (i + 1) * r)⁻¹ =
            (s * e * s⁻¹) ^ i * (e ^ i)⁻¹ := by
          have hconj : s * e ^ i * s⁻¹ = (s * e * s⁻¹) ^ i := by
            rw [← MulAut.conj_apply, map_pow, MulAut.conj_apply]
          calc s * (e ^ i * r) * s⁻¹ * (e ^ (i + 1) * r)⁻¹
              = (s * e ^ i * s⁻¹) * (s * r * s⁻¹ * r⁻¹) * (e ^ (i + 1))⁻¹ := by group
            _ = (s * e * s⁻¹) ^ i * (e ^ i)⁻¹ := by
              rw [hconj, ← hedef, pow_succ]; group
        rw [h3]
        exact h2
    obtain ⟨N, hN⟩ := hT2 ⟨s, hsT⟩
    have hsN : s ^ 2 ^ N = 1 := by simpa using congrArg Subtype.val hN
    have h2N : e ^ 2 ^ N ∈ O := by
      have h := hiter (2 ^ N)
      rw [hsN] at h
      have : (1 : X) * r * (1 : X)⁻¹ * (e ^ 2 ^ N * r)⁻¹ = (e ^ 2 ^ N)⁻¹ := by group
      rw [this] at h
      simpa using O.inv_mem h
    obtain ⟨j, hj⟩ := hL₁3 e heL
    have hcop : Nat.gcd (2 ^ N) (3 ^ j) = 1 :=
      Nat.Coprime.pow N j (by norm_num : Nat.Coprime 2 3)
    have hg := Nat.gcd_eq_gcd_ab (2 ^ N) (3 ^ j)
    rw [hcop, Nat.cast_one] at hg
    have he1 : e = (e ^ 2 ^ N) ^ (Nat.gcdA (2 ^ N) (3 ^ j)) *
        (e ^ 3 ^ j) ^ (Nat.gcdB (2 ^ N) (3 ^ j)) := by
      rw [← zpow_natCast e (2 ^ N), ← zpow_natCast e (3 ^ j), ← zpow_mul, ← zpow_mul,
        ← zpow_add, ← hg, zpow_one]
    rw [he1]
    exact O.mul_mem (O.zpow_mem h2N _) (O.zpow_mem hj _)
  let φ : X →* CFSG.ComponentClassification.OuterAutomorphisms.Outer ↥K :=
    (QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner ↥K)).comp
      (MulAut.conjNormal (H := K))
  have hφW : ∀ z : X, φ z = 1 → z ∈ W := fun z hz =>
    mem_sup_centralizer_of_outer_eq_one hz
  have hP : Nat.card ↥(T.map φ) ≤ 2 := hOut _ (hT2.map φ)
  have hchain : (∃ k : ℕ, t₁ ^ k * t₂⁻¹ ∈ W) ∨ (∃ k : ℕ, t₂ ^ k * t₁⁻¹ ∈ W) := by
    by_cases h2 : φ t₂ = 1
    · exact Or.inl ⟨0, by simpa using W.inv_mem (hφW t₂ h2)⟩
    by_cases h1 : φ t₁ = 1
    · exact Or.inr ⟨0, by simpa using W.inv_mem (hφW t₁ h1)⟩
    refine Or.inl ⟨1, hφW _ ?_⟩
    rw [pow_one, map_mul, map_inv, mul_inv_eq_one]
    by_contra h12
    let P := T.map φ
    let a : ↥P := ⟨φ t₁, Subgroup.mem_map_of_mem φ ht₁⟩
    let b : ↥P := ⟨φ t₂, Subgroup.mem_map_of_mem φ ht₂⟩
    have ha1 : a ≠ 1 := fun h => h1 (congrArg Subtype.val h)
    have hb1 : b ≠ 1 := fun h => h2 (congrArg Subtype.val h)
    have hab : a ≠ b := fun h => h12 (congrArg Subtype.val h)
    rcases Nat.lt_or_ge (Nat.card ↥P) 2 with hlt | hge
    · haveI : Subsingleton ↥P := (Finite.card_le_one_iff_subsingleton).mp (by omega)
      exact ha1 (Subsingleton.elim _ _)
    · obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' (1 : ↥P)).mp (le_antisymm hP hge)
      exact hab ((hy a ha1).trans (hy b hb1).symm)
  exact false_of_action_mod (R := L₁) (O := O) (T := T) (W := W)
    hOL hOn hTL hTO htriv ht₁ ht₂ hchain hx hy h₁ h₂ h₃ hx₂ hyx hyx'

end CFSG.Quasithin.H13.P31A



namespace CFSG.Quasithin.H13.P31U38

open CFSG.Quasithin.H13 S126E Equiv

@[expose] def c4 (j : Fin 4) : Fin 4 :=
  if j = 0 then 1 else if j = 1 then 2 else if j = 2 then 0 else 3

theorem fin4_cube : ∀ a : Fin 4 → Fin 4, (∀ j, a (a (a j)) = j) →
    ∃ u : Fin 4, ∃ i : Fin 3, ∀ j, a j = xr u (c4^[i.val] j) := by
  decide +kernel

theorem c1_conj_mem : ∀ u v : Fin 4, ∃ u' v' : Fin 4, c1 * tau u v * c1⁻¹ = tau u' v' := by
  decide +kernel

theorem c1_inv_conj_mem : ∀ u v : Fin 4, ∃ u' v' : Fin 4, c1⁻¹ * tau u v * c1 = tau u' v' := by
  decide +kernel

theorem c2_conj_mem : ∀ u v : Fin 4, ∃ u' v' : Fin 4, c2 * tau u v * c2⁻¹ = tau u' v' := by
  decide +kernel

theorem c2_inv_conj_mem : ∀ u v : Fin 4, ∃ u' v' : Fin 4, c2⁻¹ * tau u v * c2 = tau u' v' := by
  decide +kernel

theorem glue_lo : ∀ u v : Fin 4, ∀ a b : Fin 3, ∀ j : Fin 4,
    ((tau u v * (c1 ^ a.val * c2 ^ b.val)) (⟨j.val, by omega⟩ : Fin 8)).val =
      (xr u (c4^[a.val] j)).val := by
  decide +kernel

theorem glue_hi : ∀ u v : Fin 4, ∀ a b : Fin 3, ∀ j : Fin 4,
    ((tau u v * (c1 ^ a.val * c2 ^ b.val)) (⟨j.val + 4, by omega⟩ : Fin 8)).val =
      (xr v (c4^[b.val] j)).val + 4 := by
  decide +kernel

@[expose] def IsA (σ : Perm (Fin 8)) : Prop :=
  ∃ q ∈ E16, ∃ a b : ℕ, σ = q * (c1 ^ a * c2 ^ b)

theorem c1_mem_normalizer : c1 ∈ Subgroup.normalizer (E16 : Set (Perm (Fin 8))) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · rintro ⟨u, v, rfl⟩
    obtain ⟨u', v', e⟩ := c1_conj_mem u v
    exact ⟨u', v', e⟩
  · rintro ⟨u, v, e⟩
    obtain ⟨u', v', e'⟩ := c1_inv_conj_mem u v
    refine ⟨u', v', ?_⟩
    rw [← e', ← e]
    group

theorem c2_mem_normalizer : c2 ∈ Subgroup.normalizer (E16 : Set (Perm (Fin 8))) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · rintro ⟨u, v, rfl⟩
    obtain ⟨u', v', e⟩ := c2_conj_mem u v
    exact ⟨u', v', e⟩
  · rintro ⟨u, v, e⟩
    obtain ⟨u', v', e'⟩ := c2_inv_conj_mem u v
    refine ⟨u', v', ?_⟩
    rw [← e', ← e]
    group

theorem d_mem_normalizer (a b : ℕ) :
    c1 ^ a * c2 ^ b ∈ Subgroup.normalizer (E16 : Set (Perm (Fin 8))) :=
  Subgroup.mul_mem _ (Subgroup.pow_mem _ c1_mem_normalizer a)
    (Subgroup.pow_mem _ c2_mem_normalizer b)

theorem conj_mem_E16 {d q : Perm (Fin 8)}
    (hd : d ∈ Subgroup.normalizer (E16 : Set (Perm (Fin 8)))) (hq : q ∈ E16) :
    d * q * d⁻¹ ∈ E16 :=
  (Subgroup.mem_normalizer_iff.mp hd q).mp hq

theorem c12_comm : Commute c1 c2 := by
  change c1 * c2 = c2 * c1
  decide

theorem d_mul (a b a' b' : ℕ) :
    c1 ^ a * c2 ^ b * (c1 ^ a' * c2 ^ b') = c1 ^ (a + a') * c2 ^ (b + b') := by
  have h : Commute (c2 ^ b) (c1 ^ a') := (c12_comm.symm.pow_pow b a')
  rw [pow_add, pow_add, mul_assoc, ← mul_assoc (c2 ^ b), h.eq]
  group

theorem d_cube (a b : ℕ) : (c1 ^ a * c2 ^ b) ^ 3 = 1 := by
  rw [(c12_comm.pow_pow a b).mul_pow, ← pow_mul, ← pow_mul, mul_comm a, mul_comm b, pow_mul,
    pow_mul, c1_pow_three, c2_pow_three, one_pow, one_pow, one_mul]

theorem d_inv (a b : ℕ) : (c1 ^ a * c2 ^ b)⁻¹ = c1 ^ (2 * a) * c2 ^ (2 * b) := by
  rw [inv_eq_iff_mul_eq_one, d_mul]
  have h1 : c1 ^ (a + 2 * a) = 1 := by rw [show a + 2 * a = 3 * a by ring, pow_mul, c1_pow_three, one_pow]
  have h2 : c2 ^ (b + 2 * b) = 1 := by rw [show b + 2 * b = 3 * b by ring, pow_mul, c2_pow_three, one_pow]
  rw [h1, h2, one_mul]

theorem IsA.mul {σ τ : Perm (Fin 8)} (hσ : IsA σ) (hτ : IsA τ) : IsA (σ * τ) := by
  obtain ⟨q, hq, a, b, rfl⟩ := hσ
  obtain ⟨q', hq', a', b', rfl⟩ := hτ
  refine ⟨q * ((c1 ^ a * c2 ^ b) * q' * (c1 ^ a * c2 ^ b)⁻¹),
    E16.mul_mem hq (conj_mem_E16 (d_mem_normalizer a b) hq'), a + a', b + b', ?_⟩
  rw [← d_mul]
  group

theorem IsA.inv {σ : Perm (Fin 8)} (hσ : IsA σ) : IsA σ⁻¹ := by
  obtain ⟨q, hq, a, b, rfl⟩ := hσ
  have hdn : (c1 ^ a * c2 ^ b)⁻¹ ∈ Subgroup.normalizer (E16 : Set (Perm (Fin 8))) :=
    Subgroup.inv_mem _ (d_mem_normalizer a b)
  refine ⟨(c1 ^ a * c2 ^ b)⁻¹ * q⁻¹ * (c1 ^ a * c2 ^ b)⁻¹⁻¹,
    conj_mem_E16 hdn (E16.inv_mem hq), 2 * a, 2 * b, ?_⟩
  rw [← d_inv]
  group

theorem IsA.one : IsA 1 := ⟨1, E16.one_mem, 0, 0, by simp⟩

theorem IsA.cube_mem {σ : Perm (Fin 8)} (hσ : IsA σ) : σ ^ 3 ∈ E16 := by
  obtain ⟨q, hq, a, b, rfl⟩ := hσ
  set d := c1 ^ a * c2 ^ b
  have hd := d_mem_normalizer a b
  have e : (q * d) ^ 3 = q * (d * q * d⁻¹) * (d ^ 2 * q * (d ^ 2)⁻¹) * d ^ 3 := by
    clear_value d
    rw [pow_succ, pow_succ, pow_one]
    group
  rw [e, d_cube, mul_one]
  exact E16.mul_mem (E16.mul_mem hq (conj_mem_E16 hd hq))
    (conj_mem_E16 (Subgroup.pow_mem _ hd 2) hq)

theorem IsA.normalizes {σ : Perm (Fin 8)} (hσ : IsA σ) :
    σ ∈ Subgroup.normalizer (E16 : Set (Perm (Fin 8))) := by
  obtain ⟨q, hq, a, b, rfl⟩ := hσ
  exact Subgroup.mul_mem _ (Subgroup.le_normalizer hq) (d_mem_normalizer a b)

theorem pow_two_eq_one_of_mem_E16 {σ : Perm (Fin 8)} (hσ : σ ∈ E16) : σ ^ 2 = 1 := by
  obtain ⟨u, v, rfl⟩ := hσ
  rw [sq, tau_mul, xr_self, xr_self, tau_zero]

theorem isA_of_cube {σ : Perm (Fin 8)} (hb : ∀ i : Fin 8, (i.val < 4 ↔ (σ i).val < 4))
    (h3 : σ ^ 3 = 1) : IsA σ := by
  let Lo : Fin 4 → Fin 8 := fun j => ⟨j.val, by omega⟩
  let Hi : Fin 4 → Fin 8 := fun j => ⟨j.val + 4, by omega⟩
  let a : Fin 4 → Fin 4 := fun j => ⟨(σ (Lo j)).val, by
    have h := (hb (Lo j)).1 j.isLt
    simpa [Lo] using h⟩
  let b : Fin 4 → Fin 4 := fun j => ⟨(σ (Hi j)).val - 4, by
    have h1 : ¬ (Hi j).val < 4 := by simp [Hi]
    have h2 : ¬ (σ (Hi j)).val < 4 := fun hc => h1 ((hb (Hi j)).2 hc)
    have h3 : (σ (Hi j)).val < 8 := (σ (Hi j)).isLt
    omega⟩
  have hσL : ∀ j, σ (Lo j) = Lo (a j) := fun j => Fin.ext rfl
  have hσH : ∀ j, σ (Hi j) = Hi (b j) := by
    intro j
    have h1 : ¬ (Hi j).val < 4 := by simp [Hi]
    have h2 : ¬ (σ (Hi j)).val < 4 := fun hc => h1 ((hb (Hi j)).2 hc)
    apply Fin.ext
    change (σ (Hi j)).val = ((σ (Hi j)).val - 4) + 4
    omega
  have h3' : ∀ i, σ (σ (σ i)) = i := by
    intro i
    have := congrArg (fun τ : Perm (Fin 8) => τ i) h3
    simpa [pow_succ, Perm.mul_apply] using this
  have ha3 : ∀ j, a (a (a j)) = j := by
    intro j
    have h := h3' (Lo j)
    rw [hσL, hσL, hσL] at h
    exact Fin.ext (by simpa [Lo] using congrArg Fin.val h)
  have hb3 : ∀ j, b (b (b j)) = j := by
    intro j
    have h := h3' (Hi j)
    rw [hσH, hσH, hσH] at h
    exact Fin.ext (by simpa [Hi] using congrArg Fin.val h)
  obtain ⟨u, i, hu⟩ := fin4_cube a ha3
  obtain ⟨v, k, hv⟩ := fin4_cube b hb3
  refine ⟨tau u v, tau_mem u v, i.val, k.val, ?_⟩
  ext x
  by_cases hx : x.val < 4
  · have hxe : x = Lo ⟨x.val, hx⟩ := Fin.ext rfl
    rw [hxe, hσL, glue_lo u v i k ⟨x.val, hx⟩, ← hu]
  · have hx' : x.val - 4 < 4 := by omega
    have hxe : x = Hi ⟨x.val - 4, hx'⟩ := Fin.ext (by simp [Hi]; omega)
    rw [hxe, hσH, glue_hi u v i k ⟨x.val - 4, hx'⟩, ← hv]

end CFSG.Quasithin.H13.P31U38


namespace CFSG.Quasithin.H13.P31X

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits S126 S126P31
open scoped IsMulCommutative Pointwise

@[expose] def U38OutFacts : Prop := ∀ (X : Type) [Group X] [Finite X], IsPSU 3 2 3 X →
  ∀ P : Subgroup (CFSG.ComponentClassification.OuterAutomorphisms.Outer X),
    IsPGroup 2 ↥P → Nat.card ↥P ≤ 2

@[expose] def U38ThreeRank : Prop := ∀ (X : Type) [Group X] [Finite X], IsPSU 3 2 3 X →
  2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X)

variable {G : Type} [Group G] [Finite G] {T L V H K : Subgroup G} [IsMulCommutative ↥V]

theorem cube_mem_pCoreOf_star_L1 (h1222 : Stmt12_2_2) {F : Frame126 T L V}
    (hH : Hyp126 G T L V) (hIs : IsHK T L F.V1 H K) :
    ∀ g ∈ star H (Li L F.V1), g ^ 3 ∈ pCoreOf 2 (star H (Li L F.V1)) := by
  classical
  have hL1L : Li L F.V1 ≤ L := S126L19b.L1_le_L F
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := hH.hyp.irrPlus.2.2.1
  let ψ : ↥L →* Equiv.Perm (Fin 8) :=
    (alternatingGroup (Fin 8)).subtype.comp (S126L19a.psi F hH)
  have hA : ∀ x ∈ Li L F.V1, ∃ hxL : x ∈ L, P31U38.IsA (ψ ⟨x, hxL⟩) := by
    intro x hx
    rw [S126L19b.L1_eq F] at hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨⟨hxL, hx1⟩, m, hm, hxm⟩ := hx
      refine ⟨hxL, ?_⟩
      have h3 := S126L19b.pow_three_of_mem h1222 F hH hxL hx1 hm hxm
      have hσ := S126L19a.actsAs_psi F hH ⟨x, hxL⟩
      have hσ3 := S126P.pow_eq_one_of_actsAs hσ (hLV hxL) h3
      exact P31U38.isA_of_cube
        (P31A.blocks_of_cube_one (S126L19a.blocks_of_mem_V1 F hx1 hσ) hσ3) hσ3
    | one => exact ⟨L.one_mem, by
        rw [show (⟨1, L.one_mem⟩ : ↥L) = 1 from rfl, map_one]; exact P31U38.IsA.one⟩
    | mul x y _ _ hx hy =>
      obtain ⟨hxL, hx⟩ := hx
      obtain ⟨hyL, hy⟩ := hy
      exact ⟨L.mul_mem hxL hyL, by
        rw [show (⟨x * y, L.mul_mem hxL hyL⟩ : ↥L) = ⟨x, hxL⟩ * ⟨y, hyL⟩ from rfl, map_mul]
        exact hx.mul hy⟩
    | inv x _ hx =>
      obtain ⟨hxL, hx⟩ := hx
      exact ⟨L.inv_mem hxL, by
        rw [show (⟨x⁻¹, L.inv_mem hxL⟩ : ↥L) = (⟨x, hxL⟩ : ↥L)⁻¹ from rfl, map_inv]
        exact hx.inv⟩
  let R : Subgroup G := ((Li L F.V1).subgroupOf L ⊓ (S126E.E16.comap ψ)).map L.subtype
  have hmemR : ∀ x (hxL : x ∈ L), x ∈ Li L F.V1 → ψ ⟨x, hxL⟩ ∈ S126E.E16 → x ∈ R :=
    fun x hxL hx1 hxE => ⟨⟨x, hxL⟩, ⟨Subgroup.mem_subgroupOf.mpr hx1, hxE⟩, rfl⟩
  have hRL : R ≤ Li L F.V1 := by
    rintro _ ⟨l, ⟨hl1, -⟩, rfl⟩
    exact Subgroup.mem_subgroupOf.mp hl1
  have hR2 : IsPGroup 2 ↥R := by
    rintro ⟨_, l, ⟨hl1, hlE⟩, rfl⟩
    have hsq : ψ (l ^ 2) = 1 := by
      rw [map_pow]; exact P31U38.pow_two_eq_one_of_mem_E16 hlE
    have hC : ((l ^ 2 : ↥L) : G) ∈ Subgroup.centralizer (V : Set G) := by
      rw [← S126L19a.psi_eq_one_iff F hH]
      exact Subtype.ext (by simpa [ψ] using hsq)
    have hL1 : ((l ^ 2 : ↥L) : G) ∈ Li L F.V1 :=
      (Li L F.V1).pow_mem (Subgroup.mem_subgroupOf.mp hl1) 2
    obtain ⟨k, hk⟩ := P31A.isPGroup_L1_inf_centralizer h1222 F hH ⟨_, hL1, hC⟩
    refine ⟨k + 1, Subtype.ext ?_⟩
    have hk' := congrArg Subtype.val hk
    simp only [Subgroup.coe_pow, Subgroup.coe_one] at hk' ⊢
    rw [pow_succ', pow_mul]
    simpa [Subgroup.coe_pow] using hk'
  have hconjR : ∀ x ∈ Li L F.V1, ∀ r ∈ R, x * r * x⁻¹ ∈ R := by
    rintro x hx _ ⟨l, ⟨hl1, hlE⟩, rfl⟩
    obtain ⟨hxL, hxA⟩ := hA x hx
    refine hmemR _ (L.mul_mem (L.mul_mem hxL l.2) (L.inv_mem hxL))
      ((Li L F.V1).mul_mem ((Li L F.V1).mul_mem hx (Subgroup.mem_subgroupOf.mp hl1))
        ((Li L F.V1).inv_mem hx)) ?_
    convert P31U38.conj_mem_E16 hxA.normalizes hlE using 1
    rw [← map_inv, ← map_mul, ← map_mul]
    rfl
  have hXN : Li L F.V1 ≤ Subgroup.normalizer (R : Set G) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro r
    refine ⟨hconjR x hx r, fun h => ?_⟩
    have := hconjR x⁻¹ ((Li L F.V1).inv_mem hx) _ h
    simpa [mul_assoc] using this
  have hcube : ∀ x ∈ Li L F.V1, x ^ 3 ∈ R := by
    intro x hx
    obtain ⟨hxL, hxA⟩ := hA x hx
    refine hmemR _ (L.pow_mem hxL 3) ((Li L F.V1).pow_mem hx 3) ?_
    rw [show (⟨x ^ 3, L.pow_mem hxL 3⟩ : ↥L) = (⟨x, hxL⟩ : ↥L) ^ 3 from rfl, map_pow]
    exact hxA.cube_mem
  have hN : star H R ≤ pCoreOf 2 (star H (Li L F.V1)) :=
    P31A.star_le_pCoreOf hRL (P31A.L1_le_H F hIs) hR2 hXN
  rintro _ ⟨h, hh, rfl⟩
  have hh1 : (h : G) ∈ Li L F.V1 := Subgroup.mem_subgroupOf.mp hh
  rw [← map_pow]
  exact hN (S126P31.mk_mem_star (h := h ^ 3) (by simpa using hcube _ hh1))

theorem noU38_of (hU : U3BorelFacts) (hO : U38OutFacts) (hR : U38ThreeRank)
    (h1222 : Stmt12_2_2) : NoU38 := by
  intro h1229 G _ _ T L V _ F hH hZV H K hIs h918 hK₀ hZ hX
  haveI : (star H K).Normal := P31A.normal_star_K F h918 hK₀
  have eK : (↥(star H K) ⧸ Subgroup.center ↥(star H K)) ≃* ↥(star H K) :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  have hXq : IsPSU 3 2 3 (↥(star H K) ⧸ Subgroup.center ↥(star H K)) :=
    IsPSU.of_mulEquiv eK.symm hX
  have hSD := singleData_of_setting h1229 h1222 F hH hZV hIs h918 hK₀
    (star_three_dvd_of_isPSU3 hXq)
  have hSylX : IsSylowTwoOf (star H T ⊓ star H K) (star H K) :=
    A4.isSylowTwoOf_inf_normal hSD.sylow le_top Subgroup.le_normalizer_of_normal
  obtain ⟨-, -, hcoat, -, -⟩ := hU 3 (by norm_num) _ _ _ (perfect_star_K h918) hXq hSylX
  have hMB : star H (Subgroup.normalizer (L : Set G) ⊓ H) ⊓ star H K =
      CFSG.Quasithin.H13.S126.borel (star H K) (star H T) := by
    rcases P31Grp.eq_or_eq_of_isCoatom_subgroupOf hcoat (le_inf hSD.borel_le inf_le_left)
      inf_le_right with h1 | h1
    · exact h1
    · exact absurd (inf_eq_right.1 h1) hSD.not_le
  have hLB : star H (Li L F.V1) ⊓ star H K ≤
      Subgroup.normalizer ((star H T ⊓ star H K : Subgroup (HStar H)) : Set (HStar H)) := by
    have h1 : star H (Li L F.V1) ⊓ star H K ≤
        CFSG.Quasithin.H13.S126.borel (star H K) (star H T) :=
      hMB ▸ inf_le_inf_right _ hSD.Ls_le
    exact h1.trans inf_le_right
  have hX3 : CFSG.Open.pRank 3 (⊤ : Subgroup (HStar H)) ≤ 2 :=
    S126P31.pRank_hStar_le hH (S126P31.pCoreOf_ne_bot h918.toHypF98.toHypF91)
  have hT2 : IsPGroup 2 ↥(star H T) := P31A.isPGroup_star_T F hH hIs
  have hTmax : ∀ S : Subgroup (HStar H), IsPGroup 2 ↥S → star H T ≤ S → S = star H T :=
    P31A.star_T_max F hH hIs
  have hTL : star H T ≤ Subgroup.normalizer (star H (S126.Li L F.V1) : Set (HStar H)) :=
    S126P31.star_le_normalizer_star (P31A.L1_le_H F hIs) (P31A.T_le_H F hIs)
      (S126L19b.T_le_normalizer_L1 h1222 hH)
  have hL₁3 : ∀ g ∈ star H (S126.Li L F.V1), ∃ k : ℕ,
      g ^ (3 ^ k) ∈ pCoreOf 2 (star H (S126.Li L F.V1)) := fun g hg =>
    ⟨1, by simpa using cube_mem_pCoreOf_star_L1 h1222 hH hIs g hg⟩
  let N : Subgroup G := S126.Li L F.V1 ⊓ Subgroup.centralizer (V : Set G)
  have hN2 : IsPGroup 2 ↥N := P31A.isPGroup_L1_inf_centralizer h1222 F hH
  have hXN : S126.Li L F.V1 ≤ Subgroup.normalizer (N : Set G) := by
    refine Subgroup.le_normalizer_inf ?_ ?_
    · exact Subgroup.le_normalizer
    · exact CFSG.GroupTheory.FT63ChII.le_normalizer_centralizer
        ((S126L19b.L1_le_L F).trans hH.hyp.irrPlus.2.2.1)
  have hNle : star H N ≤ pCoreOf 2 (star H (S126.Li L F.V1)) :=
    P31A.star_le_pCoreOf (N := N) (X := S126.Li L F.V1) inf_le_left
      (P31A.L1_le_H F hIs) hN2 hXN
  have hTL1 : T ≤ Subgroup.normalizer (S126.Li L F.V1 : Set G) :=
    S126L19b.T_le_normalizer_L1 h1222 hH
  have hconj : ∀ t ∈ T, ∀ z ∈ S126.Li L F.V1, t * z * t⁻¹ ∈ S126.Li L F.V1 :=
    fun t ht z hz => (Subgroup.mem_normalizer_iff.1 (hTL1 ht) z).1 hz
  have hmem1 : ∀ t ∈ T, ∀ z ∈ S126.Li L F.V1, ∀ w ∈ S126.Li L F.V1,
      t * z * t⁻¹ * w ∈ S126.Li L F.V1 :=
    fun t ht z hz w hw => (S126.Li L F.V1).mul_mem (hconj t ht z hz) hw
  have hmem2 : ∀ t ∈ T, ∀ z ∈ S126.Li L F.V1, ∀ w ∈ S126.Li L F.V1,
      t * z * t⁻¹ * w⁻¹ ∈ S126.Li L F.V1 :=
    fun t ht z hz w hw =>
      (S126.Li L F.V1).mul_mem (hconj t ht z hz) ((S126.Li L F.V1).inv_mem hw)
  obtain ⟨x, hxL1, y, hyL1, t₁, ht₁T, t₂, ht₂T, h1c, h2c, h3c, hx2ne, hyxne, hyx'ne⟩ :=
    P31A.exists_e9_frame h1222 F hH
  have hxH : x ∈ H := P31A.L1_le_H F hIs hxL1
  have hyH : y ∈ H := P31A.L1_le_H F hIs hyL1
  have ht₁H : t₁ ∈ H := P31A.T_le_H F hIs ht₁T
  have ht₂H : t₂ ∈ H := P31A.T_le_H F hIs ht₂T
  let q : ↥H →* HStar H := QuotientGroup.mk' (CFSG.pCore 2 ↥H)
  let x' : HStar H := q ⟨x, hxH⟩
  let y' : HStar H := q ⟨y, hyH⟩
  let t₁' : HStar H := q ⟨t₁, ht₁H⟩
  let t₂' : HStar H := q ⟨t₂, ht₂H⟩
  have key : ∀ g : ↥H, (g : G) ∈ S126.Li L F.V1 →
      (g : G) ∈ Subgroup.centralizer (V : Set G) →
      q g ∈ pCoreOf 2 (star H (S126.Li L F.V1)) :=
    fun g h₁ h₂ => by
      show q g ∈ pCoreOf 2 (star H (S126.Li L F.V1))
      simpa [q] using hNle (S126P31.mk_mem_star (h := g) ⟨h₁, h₂⟩)
  have key' : ∀ g : ↥H, (∀ k : ℕ, (g : G) ^ (2 ^ k) ≠ 1) →
      q g ∉ pCoreOf 2 (star H (S126.Li L F.V1)) :=
    fun g hg => by
      show q g ∉ pCoreOf 2 (star H (S126.Li L F.V1))
      simpa [q] using P31A.mk_not_mem_pCoreOf (H := H) (g := g) hg
        (star H (S126.Li L F.V1))
  have h1 : t₁' * x' * t₁'⁻¹ * x' ∈ pCoreOf 2 (star H (S126.Li L F.V1)) := by
    rw [show t₁' * x' * t₁'⁻¹ * x' =
        q ((⟨t₁, ht₁H⟩ : ↥H) * ⟨x, hxH⟩ * (⟨t₁, ht₁H⟩ : ↥H)⁻¹ * ⟨x, hxH⟩) by
      simp only [x', t₁', map_mul, map_inv]]
    exact key _ (hmem1 t₁ ht₁T x hxL1 x hxL1) h1c
  have h2 : t₂' * x' * t₂'⁻¹ * y'⁻¹ ∈ pCoreOf 2 (star H (S126.Li L F.V1)) := by
    rw [show t₂' * x' * t₂'⁻¹ * y'⁻¹ =
        q ((⟨t₂, ht₂H⟩ : ↥H) * ⟨x, hxH⟩ * (⟨t₂, ht₂H⟩ : ↥H)⁻¹ * (⟨y, hyH⟩ : ↥H)⁻¹) by
      simp only [x', y', t₂', map_mul, map_inv]]
    exact key _ (hmem2 t₂ ht₂T x hxL1 y hyL1) h2c
  have h3 : t₂' * y' * t₂'⁻¹ * x'⁻¹ ∈ pCoreOf 2 (star H (S126.Li L F.V1)) := by
    rw [show t₂' * y' * t₂'⁻¹ * x'⁻¹ =
        q ((⟨t₂, ht₂H⟩ : ↥H) * ⟨y, hyH⟩ * (⟨t₂, ht₂H⟩ : ↥H)⁻¹ * (⟨x, hxH⟩ : ↥H)⁻¹) by
      simp only [x', y', t₂', map_mul, map_inv]]
    exact key _ (hmem2 t₂ ht₂T y hyL1 x hxL1) h3c
  have hx2 : x' ^ 2 ∉ pCoreOf 2 (star H (S126.Li L F.V1)) := by
    have hg : ∀ k : ℕ, (((⟨x, hxH⟩ : ↥H) ^ 2 : ↥H) : G) ^ (2 ^ k) ≠ 1 := by
      intro k
      simpa [Subgroup.coe_pow] using hx2ne k
    rw [show x' ^ 2 = q ((⟨x, hxH⟩ : ↥H) ^ 2) by simp only [x', map_pow]]
    exact key' _ hg
  have hyx : y' * x' ∉ pCoreOf 2 (star H (S126.Li L F.V1)) := by
    have hg : ∀ k : ℕ, (((⟨y, hyH⟩ : ↥H) * ⟨x, hxH⟩ : ↥H) : G) ^ (2 ^ k) ≠ 1 := by
      intro k
      simpa [Subgroup.coe_mul] using hyxne k
    rw [show y' * x' = q ((⟨y, hyH⟩ : ↥H) * ⟨x, hxH⟩) by simp only [x', y', map_mul]]
    exact key' _ hg
  have hyx' : y' * x'⁻¹ ∉ pCoreOf 2 (star H (S126.Li L F.V1)) := by
    have hg : ∀ k : ℕ,
        (((⟨y, hyH⟩ : ↥H) * (⟨x, hxH⟩ : ↥H)⁻¹ : ↥H) : G) ^ (2 ^ k) ≠ 1 := by
      intro k
      simpa [Subgroup.coe_mul, Subgroup.coe_inv] using hyx'ne k
    rw [show y' * x'⁻¹ = q ((⟨y, hyH⟩ : ↥H) * (⟨x, hxH⟩ : ↥H)⁻¹) by
      simp only [x', y', map_mul, map_inv]]
    exact key' _ hg
  exact P31A.false_of_borel_out2 (X := HStar H) (K := star H K)
    (L₁ := star H (S126.Li L F.V1)) (T := star H T)
    hZ (hR _ hX) hX3 (hO _ hX) hT2 hTmax hTL hL₁3 hLB
    (S126P31.mk_mem_star (h := ⟨x, hxH⟩) hxL1)
    (S126P31.mk_mem_star (h := ⟨y, hyH⟩) hyL1)
    (S126P31.mk_mem_star (h := ⟨t₁, ht₁H⟩) ht₁T)
    (S126P31.mk_mem_star (h := ⟨t₂, ht₂H⟩) ht₂T)
    h1 h2 h3 hx2 hyx hyx'

end CFSG.Quasithin.H13.P31X

namespace CFSG.Quasithin.H13.P31X

open CFSG.Open CFSG.Blueprint CFSG.Quasithin

theorem u38OutFacts_proof (X : Type) [Group X] [Finite X] (hX : IsPSU 3 2 3 X)
    (P : Subgroup (CFSG.ComponentClassification.OuterAutomorphisms.Outer X))
    (hP : IsPGroup 2 ↥P) : Nat.card ↥P ≤ 2 := by
  have hL : LieModel X .PSU 3 2 3 := Or.inl ⟨by decide, hX⟩
  have h18 : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer X) = 18 := by
    rw [CFSG.LocalAnalysis.EvenBN.GMSK.SporadicBender.card_outer_of_lieModel_PSU3 hL]
    norm_num
  haveI : Finite (CFSG.ComponentClassification.OuterAutomorphisms.Outer X) :=
    Nat.finite_of_card_ne_zero (by rw [h18]; norm_num)
  have hdvd : Nat.card ↥P ∣ 18 := h18 ▸ Subgroup.card_subgroup_dvd_card P
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := hP.exists_card_eq
  rw [hk] at hdvd ⊢
  have : k ≤ 1 := by
    by_contra h
    have h4 : 2 ^ 2 ∣ 2 ^ k := pow_dvd_pow 2 (by omega)
    have := h4.trans hdvd
    norm_num at this
  calc 2 ^ k ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) this
    _ = 2 := by norm_num

end CFSG.Quasithin.H13.P31X

namespace CFSG.Quasithin.H13.P31X

open CFSG.Open CFSG.Blueprint CFSG.Quasithin

theorem u38OutFacts_holds : U38OutFacts := fun X _ _ hX P hP => u38OutFacts_proof X hX P hP

theorem u38ThreeRank_holds : U38ThreeRank := fun _ _ _ hX =>
  CFSG.Quasithin.R3c3.two_le_pRank_three_isPSU_two_odd (by decide) hX

theorem noU38_holds
    (h1222 : Stmt12_2_2) : NoU38 :=
  noU38_of u3BorelFacts_holds u38OutFacts_holds u38ThreeRank_holds h1222

end CFSG.Quasithin.H13.P31X
