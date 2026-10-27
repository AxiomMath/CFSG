module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.lemma_4_5_a
public import CFSG.Quasithin.EmptyFaithful.QTKELocal

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

theorem mem_of_isCyclic_sylow_ch615 {Γ : Type*} [Group Γ] [Finite Γ] {p : ℕ} [Fact p.Prime]
    (hcyc : ∀ P : Sylow p Γ, IsCyclic P) {K : Subgroup Γ} (hK : K.Normal) {x₁ : Γ}
    (hx₁ : x₁ ∈ K) (hx₁p : orderOf x₁ = p) {x : Γ} (hx : x ^ p = 1) : x ∈ K := by
  have hpg : ∀ y : Γ, y ^ p = 1 → IsPGroup p (Subgroup.zpowers y) := by
    intro y hy g
    obtain ⟨g, m, rfl⟩ := g
    refine ⟨1, Subtype.ext ?_⟩
    show (y ^ m) ^ p ^ 1 = 1
    rw [pow_one, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hy, one_zpow]
  have hx₁' : x₁ ^ p = 1 := by rw [← hx₁p]; exact pow_orderOf_eq_one x₁
  obtain ⟨P, hP⟩ := (hpg x hx).exists_le_sylow
  obtain ⟨P₁, hP₁⟩ := (hpg x₁ hx₁').exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Γ P₁ P
  have hyP : g * x₁ * g⁻¹ ∈ (P : Subgroup Γ) := by
    rw [← hg, Sylow.coe_subgroup_smul]
    exact ⟨x₁, hP₁ (Subgroup.mem_zpowers x₁), rfl⟩
  have hxP : x ∈ (P : Subgroup Γ) := hP (Subgroup.mem_zpowers x)
  have := hcyc P
  have hconj : orderOf (g * x₁ * g⁻¹) = orderOf x₁ := by
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
  have hle : Subgroup.zpowers (⟨x, hxP⟩ : ↥(P : Subgroup Γ)) ≤
      Subgroup.zpowers (⟨g * x₁ * g⁻¹, hyP⟩ : ↥(P : Subgroup Γ)) := by
    rw [IsCyclic.subgroup_le_iff_card_dvd, Nat.card_zpowers, Nat.card_zpowers,
      Subgroup.orderOf_mk, Subgroup.orderOf_mk, hconj, hx₁p]
    exact orderOf_dvd_of_pow_eq_one hx
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hle (Subgroup.mem_zpowers _))
  have hk' : (g * x₁ * g⁻¹) ^ k = x := by
    have := congrArg Subtype.val hk
    simpa using this
  rw [← hk']
  exact K.zpow_mem (hK.conj_mem x₁ hx₁ g) k

variable {G : Type} [Group G] [Finite G]

theorem exists_elemAbelian_sq_ch615 {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {C : Subgroup G}
    (P : Sylow p ↥C) (hP : ¬ IsCyclic P) :
    ∃ E : Subgroup G, E ≤ C ∧ IsElemAbelian p E ∧ Nat.card E = p ^ 2 := by
  have : Fact (IsPGroup p ↥(P : Subgroup ↥C)) := ⟨P.isPGroup'⟩
  obtain ⟨S, -, hcard, hel⟩ := lemma_4_5_a hp2 hP
  set f : ↥(P : Subgroup ↥C) →* G := C.subtype.comp (P : Subgroup ↥C).subtype with hf
  have hfinj : Function.Injective f :=
    C.subtype_injective.comp (P : Subgroup ↥C).subtype_injective
  refine ⟨S.map f, ?_, ?_, ?_⟩
  · rintro _ ⟨s, -, rfl⟩
    exact ((s : ↥C)).2
  · exact CFSG.SectionRank.isElemAbelian_map
      ⟨hel.toIsMulCommutative, fun x hx => elemPow_eq_one_of_isElementaryAbelian x hx⟩ f
  · rw [Subgroup.card_map_of_injective hfinj, hcard]

theorem three_le_pRank_ch615 {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) {A N E : Subgroup G}
    {d : G} (hNA : N ≤ A) (hEA : E ≤ A) (hdA : d ∈ A)
    (hAN : A ≤ Subgroup.normalizer (N : Set G)) (hN2 : IsPGroup 2 N) (hE : IsElemAbelian p E)
    (hEcard : Nat.card E = p ^ 2) (hd : orderOf d = p)
    (hcomm : ∀ e ∈ E, ∀ δ ∈ Subgroup.zpowers d, e * δ * e⁻¹ * δ⁻¹ ∈ N)
    (hinj : ∀ e ∈ E, ∀ δ ∈ Subgroup.zpowers d, e * δ ∈ N → e = 1 ∧ δ = 1) :
    3 ≤ CFSG.Open.pRank p A := by
  have hNn : (N.subgroupOf A).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNA).mpr hAN
  have hdA' : Subgroup.zpowers d ≤ A := (Subgroup.zpowers_le (G := G) (H := A)).mpr hdA
  set π := QuotientGroup.mk' (N.subgroupOf A) with hπ
  set f₁ : ↥E →* ↥A ⧸ N.subgroupOf A := π.comp (Subgroup.inclusion hEA) with hf₁
  set f₂ : ↥(Subgroup.zpowers d) →* ↥A ⧸ N.subgroupOf A :=
    π.comp (Subgroup.inclusion hdA') with hf₂
  have hcomm' : ∀ (e : ↥E) (δ : ↥(Subgroup.zpowers d)), Commute (f₁ e) (f₂ δ) := by
    intro e δ
    show π _ * π _ = π _ * π _
    rw [← map_mul, ← map_mul, hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have h1 := hcomm e e.2 δ δ.2
    have h2 : ((e : G) * δ)⁻¹ ∈ Subgroup.normalizer (N : Set G) :=
      hAN (A.inv_mem (A.mul_mem (hEA e.2) (hdA' δ.2)))
    have h3 := (Subgroup.mem_normalizer_iff.mp h2 _).mp (N.inv_mem h1)
    have e1 : (((Subgroup.inclusion hEA e * Subgroup.inclusion hdA' δ)⁻¹ *
        (Subgroup.inclusion hdA' δ * Subgroup.inclusion hEA e) : ↥A) : G) =
        ((e : G) * δ)⁻¹ * ((e : G) * δ * (e : G)⁻¹ * (δ : G)⁻¹)⁻¹ * ((e : G) * δ)⁻¹⁻¹ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inclusion]
      group
    rw [e1]
    exact h3
  set f := MonoidHom.noncommCoprod f₁ f₂ hcomm' with hf
  have hf_inj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    rintro ⟨e, δ⟩ h
    rw [hf, MonoidHom.noncommCoprod_apply, hf₁, hf₂, MonoidHom.comp_apply, MonoidHom.comp_apply,
      ← map_mul, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
      Subgroup.mem_subgroupOf] at h
    have h' : (e : G) * δ ∈ N := by simpa using h
    obtain ⟨he, hδ⟩ := hinj e e.2 δ δ.2 h'
    exact Prod.ext (Subtype.ext he) (Subtype.ext hδ)
  have hAcomm : ∀ a b : ↥E × ↥(Subgroup.zpowers d), a * b = b * a := by
    rintro ⟨e, δ⟩ ⟨e', δ'⟩
    have := hE.1
    refine Prod.ext (mul_comm' e e') ?_
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp δ.2
    obtain ⟨i', hi'⟩ := Subgroup.mem_zpowers_iff.mp δ'.2
    apply Subtype.ext
    show (δ : G) * δ' = δ' * δ
    rw [← hi, ← hi', ← zpow_add, ← zpow_add, add_comm]
  have hpd : d ^ p = 1 := by rw [← hd]; exact pow_orderOf_eq_one d
  have hApow : ∀ a : ↥E × ↥(Subgroup.zpowers d), a ^ p = 1 := by
    rintro ⟨e, δ⟩
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
    · simpa using hE.2 (e : G) e.2
    · obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp δ.2
      show (δ : G) ^ p = 1
      rw [← hi, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hpd, one_zpow]
  have hAcard : Nat.card (↥E × ↥(Subgroup.zpowers d)) = p ^ 3 := by
    rw [Nat.card_prod, Nat.card_zpowers, hd, hEcard]
    ring
  have h3 : 3 ≤ CFSG.Open.pRank p (⊤ : Subgroup (↥A ⧸ N.subgroupOf A)) :=
    CFSG.SectionRank.le_pRank_of_injective hp.out.one_lt hAcomm hApow hAcard f hf_inj le_top
  have hNp : ¬ p ∣ Nat.card (N.subgroupOf A) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNA).toEquiv]
    obtain ⟨m, hm⟩ := hN2.exists_card_eq
    rw [hm]
    intro h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp (hp.out.dvd_of_dvd_pow h))
  rw [CFSG.SectionRank.pRank_quotient_eq _ hNp, CFSG.Quasithin.pRank_top_subtype] at h3
  exact h3

theorem not_elemAbelian_sq_ch615 (hK : quasithinIsQTKECat G) {M : Subgroup G}
    (hM : IsTwoLocal M) {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) {C B : Subgroup G} {d : G}
    (hCM : C ≤ M) (hBM : B ≤ M) (hdB : d ∈ B) (hd : orderOf d = p)
    (hCB : C ≤ Subgroup.normalizer (B : Set G)) (hBC : B ≤ Subgroup.normalizer (C : Set G))
    (hN2 : IsPGroup 2 ↥(C ⊓ B)) {E : Subgroup G} (hEC : E ≤ C) (hE : IsElemAbelian p E)
    (hEcard : Nat.card E = p ^ 2) : False := by
  set N := C ⊓ B with hN
  set A := (N ⊔ E) ⊔ Subgroup.zpowers d with hA
  have hNA : N ≤ A := le_sup_left.trans le_sup_left
  have hEA : E ≤ A := le_sup_right.trans le_sup_left
  have hdA : d ∈ A := Subgroup.mem_sup_right (Subgroup.mem_zpowers d)
  have hdpow : ∀ δ ∈ Subgroup.zpowers d, δ ∈ B := fun δ hδ =>
    (Subgroup.zpowers_le (G := G) (H := B)).mpr hdB hδ
  have hNnorm : ∀ g ∈ C, g ∈ Subgroup.normalizer (B : Set G) →
      g ∈ Subgroup.normalizer (N : Set G) := fun g hg hgB =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hg, hgB⟩
  have hNnorm' : ∀ g ∈ B, g ∈ Subgroup.normalizer (C : Set G) →
      g ∈ Subgroup.normalizer (N : Set G) := fun g hg hgC =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hgC, Subgroup.le_normalizer hg⟩
  have hAN : A ≤ Subgroup.normalizer (N : Set G) := by
    refine sup_le (sup_le Subgroup.le_normalizer fun e he => hNnorm e (hEC he) (hCB (hEC he))) ?_
    exact (Subgroup.zpowers_le (G := G) (H := Subgroup.normalizer (N : Set G))).mpr
      (hNnorm' d hdB (hBC hdB))
  have hpow1 : ∀ g : G, g ^ p = 1 → g ∈ N → g = 1 := by
    intro g hg hgN
    obtain ⟨k, hk⟩ := hN2 ⟨g, hgN⟩
    have hk' : g ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have h1 := orderOf_dvd_of_pow_eq_one hg
    have h2 := orderOf_dvd_of_pow_eq_one hk'
    have hcop : Nat.Coprime p (2 ^ k) :=
      Nat.Coprime.pow_right k ((Nat.coprime_primes hp.out Nat.prime_two).mpr hp2)
    exact orderOf_eq_one_iff.mp
      (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h1 hcop) h2)
  have hδp : ∀ δ ∈ Subgroup.zpowers d, δ ^ p = 1 := by
    intro δ hδ
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hδ
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hd, pow_orderOf_eq_one,
      one_zpow]
  have h3 := three_le_pRank_ch615 hp2 hNA hEA hdA hAN hN2 hE hEcard hd
    (fun e he δ hδ => ⟨by
      have h1 : δ * e⁻¹ * δ⁻¹ ∈ C :=
        (Subgroup.mem_normalizer_iff.mp (hBC (hdpow δ hδ)) _).mp (C.inv_mem (hEC he))
      have e1 : e * δ * e⁻¹ * δ⁻¹ = e * (δ * e⁻¹ * δ⁻¹) := by group
      rw [e1]
      exact C.mul_mem (hEC he) h1, by
      have h1 : e * δ * e⁻¹ ∈ B := (Subgroup.mem_normalizer_iff.mp (hCB (hEC he)) _).mp (hdpow δ hδ)
      exact B.mul_mem h1 (B.inv_mem (hdpow δ hδ))⟩)
    (fun e he δ hδ heδ => by
      have heB : e ∈ B := by
        have e1 : e = e * δ * δ⁻¹ := by group
        rw [e1]
        exact B.mul_mem heδ.2 (B.inv_mem (hdpow δ hδ))
      have he1 : e = 1 := hpow1 e (hE.2 e he) ⟨hEC he, heB⟩
      refine ⟨he1, hpow1 δ (hδp δ hδ) ?_⟩
      rw [he1, one_mul] at heδ
      exact heδ)
  have hAM : A ≤ M := sup_le (sup_le (inf_le_left.trans hCM) (hEC.trans hCM))
    ((Subgroup.zpowers_le (G := G) (H := M)).mpr (hBM hdB))
  have h2 := CFSG.Quasithin.pRank_le_two_of_isTwoLocal hK hM hp.out hp2
  have h4 := CFSG.SectionRank.pRank_mono hp.out.one_lt hAM
  omega

end CFSG.Quasithin.H13
