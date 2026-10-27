module

public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL45KGForms
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL45FinalTorus
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL45RankXCyclic

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

section Basic

variable {G : Type} [Group G] (K : Subgroup G)

theorem ggL45_rhoK_coe (g : Subgroup.normalizer (K : Set G)) (k : K) :
    ((K.normalizerMonoidHom g k : K) : G) = (g : G) * k * (g : G)⁻¹ :=
  rfl

variable {R : Type} [Group R] (θ : K ⧸ Subgroup.center K ≃* R)

theorem induces_rhoK (g : Subgroup.normalizer (K : Set G)) :
    LargeEvenInduces θ (fun k k' => k' = K.normalizerMonoidHom g k) (ggLAut K θ g) := by
  intro l l' h
  subst h
  rw [ggLAut_apply]

theorem eq_ggLAut_of_induces_rhoK (g : Subgroup.normalizer (K : Set G)) {φ : MulAut R}
    (h : LargeEvenInduces θ (fun k k' => k' = K.normalizerMonoidHom g k) φ) :
    φ = ggLAut K θ g := by
  ext r
  obtain ⟨q, rfl⟩ := θ.surjective r
  induction q using QuotientGroup.induction_on with
  | H l =>
    rw [ggLAut_apply]
    exact h l _ rfl

theorem ggL45_inducesIn_rhoK_iff (I : Set (MulAut R)) (g : Subgroup.normalizer (K : Set G)) :
    GGL45InducesIn θ I (K.normalizerMonoidHom g) ↔ ggLAut K θ g ∈ I := by
  constructor
  · rintro ⟨φ, hφ, hind⟩
    rwa [eq_ggLAut_of_induces_rhoK K θ g hind] at hφ
  · intro h
    exact ⟨_, h, induces_rhoK K θ g⟩

theorem induces_inv_iff {g : G} (hg : g ∈ Subgroup.normalizer (K : Set G)) (φ : MulAut R) :
    LargeEvenInduces θ (fun k k' => (k' : G) = g⁻¹ * k * g) φ ↔
      LargeEvenInduces θ (fun k k' => k' = K.normalizerMonoidHom ⟨g⁻¹, inv_mem hg⟩ k) φ := by
  constructor
  · intro h l l' hl
    refine h l l' ?_
    show (l' : G) = _
    rw [hl, ggL45_rhoK_coe]
    simp
  · intro h l l' hl
    refine h l l' (Subtype.ext ?_)
    rw [hl, ggL45_rhoK_coe]
    simp

theorem conj_eq_rhoK (k : K) :
    MulAut.conj k = K.normalizerMonoidHom ⟨k, Subgroup.le_normalizer k.2⟩ := by
  ext k'
  rfl

theorem ggL45_rhoK_eq_one_iff (g : Subgroup.normalizer (K : Set G)) :
    K.normalizerMonoidHom g = 1 ↔ (g : G) ∈ Subgroup.centralizer (K : Set G) := by
  constructor
  · intro h
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    have := congrArg (fun α : MulAut K => ((α ⟨k, hk⟩ : K) : G)) h
    simp only [ggL45_rhoK_coe, MulAut.one_apply] at this
    calc k * (g : G) = ((g : G) * k * (g : G)⁻¹) * g := by rw [this]
      _ = g * k := by group
  · intro h
    ext k
    simp only [ggL45_rhoK_coe, MulAut.one_apply]
    rw [(Subgroup.mem_centralizer_iff.mp h k k.2).symm]
    group

end Basic

section PPart

variable {G : Type} [Group G] [Finite G]

theorem exists_pElt_pow (p : ℕ) [Fact p.Prime] {C : Subgroup G} {g : G} {k : ℕ}
    (hk : g ^ p ^ k ∈ C) : ∃ N : ℕ, GGL45IsPElt p (g ^ N) ∧ g * (g ^ N)⁻¹ ∈ C := by
  have hp := (Fact.out : p.Prime)
  set n := orderOf g with hn
  have hn0 : 0 < n := orderOf_pos g
  obtain ⟨a, m, hm, hnm⟩ : ∃ a m : ℕ, Nat.Coprime p m ∧ n = p ^ a * m :=
    ⟨n.factorization p, n / p ^ n.factorization p,
      Nat.coprime_ordCompl hp hn0.ne', (Nat.ordProj_mul_ordCompl_eq_self n p).symm⟩
  have hcop : Nat.Coprime m (p ^ k) := Nat.Coprime.pow_right k hm.symm
  obtain ⟨N, hN1, hN2⟩ := Nat.chineseRemainder hcop 0 1
  refine ⟨N, ⟨a, ?_⟩, ?_⟩
  · rw [← pow_mul, orderOf_dvd_iff_pow_eq_one.symm, ← hn, hnm]
    have : m ∣ N := (Nat.modEq_zero_iff_dvd).mp hN1
    rw [mul_comm N]
    exact Nat.mul_dvd_mul_left _ this
  ·
    have hle : 1 ≤ N ∨ N = 0 := by omega
    rcases hle with hle | h0
    · obtain ⟨t, ht⟩ : p ^ k ∣ N - 1 := (Nat.modEq_iff_dvd' hle).mp hN2.symm
      have e : g * (g ^ N)⁻¹ = ((g ^ p ^ k) ^ t)⁻¹ := by
        rw [← pow_mul, ← ht]
        have : N = (N - 1) + 1 := by omega
        conv_lhs => rw [this, pow_succ]
        group
      rw [e]
      exact C.inv_mem (C.pow_mem hk t)
    ·
      have h1 : 0 ≡ 1 [MOD p ^ k] := h0 ▸ hN2
      have hk0 : p ^ k ∣ 1 := (Nat.modEq_iff_dvd' (by omega)).mp h1
      have : p ^ k = 1 := Nat.eq_one_of_dvd_one hk0
      rw [this, pow_one] at hk
      rw [h0, pow_zero, inv_one, mul_one]
      exact hk

end PPart

theorem ggL45_isElemAbelian_zpowers' {G : Type*} [Group G] {p : ℕ} {z : G} (hz : z ^ p = 1) :
    IsElemAbelian p (Subgroup.zpowers z) := by
  refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun e he => ?_⟩
  · obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp a.2
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp b.2
    show (a : G) * b = b * a
    rw [← hm, ← hn]
    exact (Commute.zpow_zpow_self z m n).eq
  · obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp he
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hz, one_zpow]

section Config

variable {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
  {L D J X B₂ : Subgroup G} {d y : G} {K U U₁ : Subgroup G}

@[expose] def ggL45KgE (K B₁ : Subgroup G) (h : B₁ ≤ Subgroup.normalizer (K : Set G)) :
    Subgroup (MulAut K) :=
  (K.normalizerMonoidHom.comp (Subgroup.inclusion h)).range

theorem mem_ggL45KgE {K B₁ : Subgroup G} {h : B₁ ≤ Subgroup.normalizer (K : Set G)}
    {e : MulAut K} : e ∈ ggL45KgE K B₁ h ↔ ∃ b ∈ B₁, ∃ hb : b ∈ Subgroup.normalizer (K : Set G),
      K.normalizerMonoidHom ⟨b, hb⟩ = e := by
  constructor
  · rintro ⟨b, rfl⟩
    exact ⟨b, b.2, h b.2, rfl⟩
  · rintro ⟨b, hb, hbN, rfl⟩
    exact ⟨⟨b, hb⟩, rfl⟩

theorem card_ggL45KgE_mul (K B₁ : Subgroup G) (h : B₁ ≤ Subgroup.normalizer (K : Set G)) :
    Nat.card (ggL45KgE K B₁ h) * Nat.card (B₁ ⊓ Subgroup.centralizer (K : Set G) : Subgroup G) =
      Nat.card B₁ := by
  set β := K.normalizerMonoidHom.comp (Subgroup.inclusion h)
  have hker : β.ker.map B₁.subtype = B₁ ⊓ Subgroup.centralizer (K : Set G) := by
    ext g
    constructor
    · rintro ⟨b, hb, rfl⟩
      exact ⟨b.2, (ggL45_rhoK_eq_one_iff K _).mp hb⟩
    · rintro ⟨hg, hgC⟩
      exact ⟨⟨g, hg⟩, (ggL45_rhoK_eq_one_iff K ⟨g, h hg⟩).mpr hgC, rfl⟩
  rw [← hker, Subgroup.card_map_of_injective B₁.subtype_injective, mul_comm]
  exact Subgroup.card_ker_mul_card_range β

theorem GGL45Config.kg_xN (hcfg : GGL45Config p B Bs x L D J X B₂ d y K U U₁) :
    x ∈ Subgroup.normalizer (K : Set G) :=
  hcfg.le_normalizer (hcfg.bs_le hcfg.x_mem)

theorem GGL45Config.kg_B1N (hcfg : GGL45Config p B Bs x L D J X B₂ d y K U U₁) :
    Bs ⊓ Subgroup.centralizer (X : Set G) ≤ Subgroup.normalizer (K : Set G) :=
  fun _ hb => hcfg.le_normalizer (hcfg.bs_le hb.1)

theorem GGL45Config.kg_psi_pow (hcfg : GGL45Config p B Bs x L D J X B₂ d y K U U₁) :
    K.normalizerMonoidHom ⟨x⁻¹, inv_mem hcfg.kg_xN⟩ ^ p = 1 := by
  rw [← map_pow]
  have : (⟨x⁻¹, inv_mem hcfg.kg_xN⟩ : Subgroup.normalizer (K : Set G)) ^ p = 1 :=
    Subtype.ext (by simp [inv_pow, hcfg.x_pow])
  rw [this, map_one]

theorem GGL45Config.kg_E_elemAbelian (hcfg : GGL45Config p B Bs x L D J X B₂ d y K U U₁) :
    IsElemAbelian p (ggL45KgE K _ hcfg.kg_B1N) := by
  refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun e he => ?_⟩
  · obtain ⟨b₁, hb₁, hb₁N, hab⟩ := mem_ggL45KgE.mp a.2
    obtain ⟨b₂, hb₂, hb₂N, hbb⟩ := mem_ggL45KgE.mp b.2
    show (a : MulAut K) * b = b * a
    rw [← hab, ← hbb, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (mul_comm_of_isElemAbelian hcfg.isElemAbelian hb₁.1 hb₂.1)
  · obtain ⟨b, hb, hbN, rfl⟩ := mem_ggL45KgE.mp he
    have h1 : (⟨b, hbN⟩ : Subgroup.normalizer (K : Set G)) ^ p = 1 :=
      Subtype.ext (by simpa using hcfg.isElemAbelian.2 b hb.1)
    rw [← map_pow, h1, map_one]

theorem GGL45Config.kg_E_comm (hcfg : GGL45Config p B Bs x L D J X B₂ d y K U U₁) :
    ∀ e ∈ ggL45KgE K _ hcfg.kg_B1N,
      e * K.normalizerMonoidHom ⟨x⁻¹, inv_mem hcfg.kg_xN⟩ =
        K.normalizerMonoidHom ⟨x⁻¹, inv_mem hcfg.kg_xN⟩ * e := by
  intro e he
  obtain ⟨b, hb, hbN, rfl⟩ := mem_ggL45KgE.mp he
  rw [← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext (mul_comm_of_isElemAbelian hcfg.isElemAbelian hb.1 (inv_mem hcfg.x_mem))

theorem GGL45Config.kg_sq_le_card_E (hcfg : GGL45Config p B Bs x L D J X B₂ d y K U U₁)
    (hcent : Bs ⊓ Subgroup.centralizer (X : Set G) ⊓ Subgroup.centralizer (K : Set G) ≤
      Subgroup.zpowers d) :
    p ^ 2 ≤ Nat.card (ggL45KgE K _ hcfg.kg_B1N) := by
  have hp : p.Prime := hcfg.prime
  have : Fact p.Prime := ⟨hp⟩
  have hI := hcfg.1.1.1
  have hB : Nat.card B = p ^ LargeEvenTwoLocalRank p G := hI.2.2.2.2.2.2.1.1.2.1
  have hm4 : 4 ≤ LargeEvenTwoLocalRank p G := hI.2.2.2.2.2.1.2.2.2
  have hB4 : p ^ 4 ≤ Nat.card Bs := by
    calc p ^ 4 ≤ p ^ LargeEvenTwoLocalRank p G := Nat.pow_le_pow_right hp.pos hm4
      _ = Nat.card B := hB.symm
      _ ≤ Nat.card Bs := Subgroup.card_le_of_le hcfg.1.1.2.1.1
  have h43 : GGL43 Bs x X := hcfg.2.2.1
  have hx1 : x ≠ 1 := fun h => h43.1 (h ▸ one_mem _)
  have hle := card_bstar_le_of_ggL43 hcfg.isElemAbelian hcfg.x_mem hx1 h43
  have hker : Nat.card (Bs ⊓ Subgroup.centralizer (X : Set G) ⊓
      Subgroup.centralizer (K : Set G) : Subgroup G) ≤ p := by
    calc _ ≤ Nat.card (Subgroup.zpowers d) := Subgroup.card_le_of_le hcent
      _ = p := by rw [Nat.card_zpowers, orderOf_eq_prime hcfg.d_pow hcfg.d_ne]
  have hcard := card_ggL45KgE_mul K _ hcfg.kg_B1N
  have hp1 := hp.one_lt
  have h3 : p ^ 3 ≤ Nat.card (Bs ⊓ Subgroup.centralizer (X : Set G) : Subgroup G) := by
    have : p ^ 4 ≤ _ * p := hB4.trans hle
    have e : p ^ 4 = p ^ 3 * p := by ring
    rw [e] at this
    exact Nat.le_of_mul_le_mul_right this (by omega)
  by_contra hlt
  push Not at hlt
  have h4 : Nat.card (Bs ⊓ Subgroup.centralizer (X : Set G) : Subgroup G) ≤
      Nat.card (ggL45KgE K _ hcfg.kg_B1N) * p := by
    rw [← hcard]
    exact Nat.mul_le_mul_left _ hker
  have h5 : Nat.card (ggL45KgE K _ hcfg.kg_B1N) * p < p ^ 2 * p :=
    Nat.mul_lt_mul_of_pos_right hlt hp.pos
  have e : p ^ 2 * p = p ^ 3 := by ring
  omega

theorem psi_fix_iff {x : G} (hxN : x ∈ Subgroup.normalizer (K : Set G)) (k : K) :
    K.normalizerMonoidHom ⟨x⁻¹, inv_mem hxN⟩ k = k ↔ (k : G) * x = x * k := by
  constructor
  · intro h
    have h' := congrArg Subtype.val h
    rw [ggL45_rhoK_coe] at h'
    simp only [inv_inv] at h'
    calc (k : G) * x = x * (x⁻¹ * k * x) := by group
      _ = x * k := by rw [h']
  · intro h
    refine Subtype.ext ?_
    rw [ggL45_rhoK_coe]
    simp only [inv_inv]
    rw [mul_assoc, h]
    group

theorem ggL45_rhoK_fix_iff {b : G} (hbN : b ∈ Subgroup.normalizer (K : Set G)) (k : K) :
    K.normalizerMonoidHom ⟨b, hbN⟩ k = k ↔ b * k = (k : G) * b := by
  constructor
  · intro h
    have h' := congrArg Subtype.val h
    rw [ggL45_rhoK_coe] at h'
    calc b * k = (b * k * b⁻¹) * b := by group
      _ = k * b := by rw [h']
  · intro h
    refine Subtype.ext ?_
    rw [ggL45_rhoK_coe, h]
    group

theorem GGL45Config.kg_sat
    (hcfg : GGL45Config p B Bs x L D J X B₂ d y K U U₁) {R : Type} [Group R]
    {I : Set (MulAut R)} (θ : K ⧸ Subgroup.center K ≃* R) (hinn : ∀ r : R, MulAut.conj r ∈ I)
    (hB₁U₁ : Bs ⊓ Subgroup.centralizer (X : Set G) ≤ U₁) (hxU₁ : x ∉ U₁)
    (hiff : ∀ u ∈ U, ∀ hu : u ∈ Subgroup.normalizer (K : Set G),
      (u ∈ U₁ ↔ ggLAut K θ ⟨u, hu⟩ ∈ I)) :
    ∀ k : K, k ^ p = 1 → (∀ e ∈ ggL45KgE K _ hcfg.kg_B1N, e k = k) →
      K.normalizerMonoidHom ⟨x⁻¹, inv_mem hcfg.kg_xN⟩ k = k →
      MulAut.conj k ∈ ggL45KgE K _ hcfg.kg_B1N := by
  intro k hkp hkE hkψ
  have hB₁k : ∀ b ∈ Bs ⊓ Subgroup.centralizer (X : Set G), b * k = (k : G) * b := fun b hb =>
    (ggL45_rhoK_fix_iff (hcfg.kg_B1N hb) k).mp (hkE _ (mem_ggL45KgE.mpr ⟨b, hb, _, rfl⟩))
  have hxk : (k : G) * x = x * k := (psi_fix_iff hcfg.kg_xN k).mp hkψ
  have hle : Bs ≤ Subgroup.centralizer ({(k : G)} : Set G) := by
    rw [hcfg.2.2.1.2]
    refine sup_le (fun b hb => ?_) ((Subgroup.zpowers_le).mpr ?_)
    · rw [Subgroup.mem_centralizer_iff]
      rintro _ rfl
      exact (hB₁k b hb).symm
    · rw [Subgroup.mem_centralizer_iff]
      rintro _ rfl
      exact hxk
  have hkC : (k : G) ∈ Subgroup.centralizer (Bs : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact ((Subgroup.mem_centralizer_iff.mp (hle hb)) k rfl).symm
  have hkp' : (k : G) ^ p = 1 := by simpa using congrArg Subtype.val hkp
  have hkBs : (k : G) ∈ Bs := hcfg.bstar_max k hkC hkp'
  have hkN : (k : G) ∈ Subgroup.normalizer (K : Set G) := Subgroup.le_normalizer k.2
  have hkU₁ : (k : G) ∈ U₁ :=
    (hiff k (hcfg.bs_le hkBs) hkN).mpr (by rw [ggLAut_mk_self K θ k]; exact hinn _)
  have hkB₁ := hcfg.inf_part_le hB₁U₁ hxU₁ ⟨hkBs, hkU₁⟩
  rw [conj_eq_rhoK]
  exact mem_ggL45KgE.mpr ⟨k, hkB₁, _, rfl⟩

theorem GGL45Config.kg_E_inducesIn
    (hcfg : GGL45Config p B Bs x L D J X B₂ d y K U U₁) {R : Type} [Group R]
    {I : Set (MulAut R)} (θ : K ⧸ Subgroup.center K ≃* R)
    (hB₁I : ∀ b ∈ Bs ⊓ Subgroup.centralizer (X : Set G), ∃ φ ∈ I,
      LargeEvenInduces θ (fun k k' => (k' : G) = b⁻¹ * k * b) φ) :
    ∀ e ∈ ggL45KgE K _ hcfg.kg_B1N, GGL45InducesIn θ I e := by
  intro e he
  obtain ⟨b, hb, hbN, rfl⟩ := mem_ggL45KgE.mp he
  exact (ggL45_inducesIn_rhoK_iff K θ I _).mpr (ggLAut_mem_of_induces K θ hcfg.kg_B1N hB₁I hb)

theorem GGL45Config.kg_card_E_d4
    (hcfg : GGL45Config 3 B Bs x L D J X B₂ d y K U U₁)
    (hcent : Bs ⊓ Subgroup.centralizer (X : Set G) ⊓ Subgroup.centralizer (K : Set G) ≤
      Subgroup.zpowers d) (h5 : 3 ^ 5 ≤ Nat.card Bs) :
    3 ^ 3 ≤ Nat.card (ggL45KgE K _ hcfg.kg_B1N) := by
  have h27 := hcfg.card_bone_ge hcent h5
  have hcard := card_ggL45KgE_mul K _ hcfg.kg_B1N
  have hpos : 0 < Nat.card (Bs ⊓ Subgroup.centralizer (X : Set G) ⊓
      Subgroup.centralizer (K : Set G) : Subgroup G) := Nat.card_pos
  have : 27 * Nat.card (Bs ⊓ Subgroup.centralizer (X : Set G) ⊓
      Subgroup.centralizer (K : Set G) : Subgroup G) ≤
      Nat.card (ggL45KgE K _ hcfg.kg_B1N) * Nat.card (Bs ⊓ Subgroup.centralizer (X : Set G) ⊓
        Subgroup.centralizer (K : Set G) : Subgroup G) := by
    rw [hcard]; exact h27
  have := Nat.le_of_mul_le_mul_right this hpos
  norm_num
  exact this

theorem GGL45Config.kg_exists_pi
    (hcfg : GGL45Config p B Bs x L D J X B₂ d y K U U₁) :
    ∃ P : Subgroup G, P ≤ Bs ⊓ Subgroup.centralizer (X : Set G) ∧
      Nat.card (Bs ⊓ Subgroup.centralizer (X : Set G) : Subgroup G) ≤ p * Nat.card P ∧
      ∀ b ∈ P, ∃ g ∈ X, g * x * g⁻¹ * x⁻¹ = b := by
  rcases hcfg.2.2.2.2.1 with h | ⟨hlt, h⟩
  · exact ⟨_, le_rfl, Nat.le_mul_of_pos_left _ hcfg.prime.pos, fun b hb => (h b).mp hb⟩
  · refine ⟨_, inf_le_left, ?_, fun b hb => (h b).mp hb⟩
    set B₁ := Bs ⊓ Subgroup.centralizer (X : Set G)
    have hB₂Bs : B₂ ≤ Bs := hcfg.2.1.2.1
    have hidx : B₂.relIndex Bs ≤ p := by
      have h1 := Subgroup.relIndex_mul_card B₂ Bs
      rw [inf_eq_left.mpr hB₂Bs] at h1
      have h2 : Nat.card Bs ≤ p * Nat.card B₂ := hcfg.2.1.2.2.1
      have hpos : 0 < Nat.card B₂ := Nat.card_pos
      rw [← h1] at h2
      exact Nat.le_of_mul_le_mul_right h2 hpos
    have h0 : B₂.relIndex Bs ≠ 0 := by
      intro h0
      have := Subgroup.relIndex_mul_card B₂ Bs
      rw [h0, zero_mul] at this
      exact (Nat.card_pos (α := Bs)).ne this
    have hle := Subgroup.relIndex_le_of_le_right (H := B₂) (inf_le_left : B₁ ≤ Bs) h0
    have h1 := Subgroup.relIndex_mul_card B₂ B₁
    rw [inf_comm] at h1
    calc Nat.card B₁ = B₂.relIndex B₁ * Nat.card (B₁ ⊓ B₂ : Subgroup G) := h1.symm
      _ ≤ p * Nat.card (B₁ ⊓ B₂ : Subgroup G) := Nat.mul_le_mul_right _ (hle.trans hidx)

theorem GGL45Config.kg_pi
    (hcfg : GGL45Config p B Bs x L D J X B₂ d y K U U₁) :
    ∃ P : Subgroup (MulAut K), P ≤ ggL45KgE K _ hcfg.kg_B1N ∧
      Nat.card (ggL45KgE K _ hcfg.kg_B1N) ≤ p * Nat.card P ∧ ∀ e ∈ P,
        ∃ γ : MulAut K, GGL45IsPElt p γ ∧ (∀ e' ∈ ggL45KgE K _ hcfg.kg_B1N, γ * e' = e' * γ) ∧
          IsPGroup p (Subgroup.closure (insert γ
            (insert (K.normalizerMonoidHom ⟨x⁻¹, inv_mem hcfg.kg_xN⟩)
              (ggL45KgE K _ hcfg.kg_B1N : Set (MulAut K))))) ∧
          e = γ * (K.normalizerMonoidHom ⟨x⁻¹, inv_mem hcfg.kg_xN⟩)⁻¹ * γ⁻¹ *
            K.normalizerMonoidHom ⟨x⁻¹, inv_mem hcfg.kg_xN⟩ := by
  have hp : p.Prime := hcfg.prime
  have : Fact p.Prime := ⟨hp⟩
  set B₁ := Bs ⊓ Subgroup.centralizer (X : Set G) with hB₁def
  obtain ⟨Pi, hPiB₁, hPicard, hPi⟩ := hcfg.kg_exists_pi
  have hPiN : Pi ≤ Subgroup.normalizer (K : Set G) := hPiB₁.trans hcfg.kg_B1N
  refine ⟨ggL45KgE K Pi hPiN, fun e he => ?_, ?_, fun e he => ?_⟩
  · obtain ⟨b, hb, hbN, rfl⟩ := mem_ggL45KgE.mp he
    exact mem_ggL45KgE.mpr ⟨b, hPiB₁ hb, hbN, rfl⟩
  ·
    have h1 := card_ggL45KgE_mul K B₁ hcfg.kg_B1N
    have h2 := card_ggL45KgE_mul K Pi hPiN
    have h3 : Nat.card (Pi ⊓ Subgroup.centralizer (K : Set G) : Subgroup G) ≤
        Nat.card (B₁ ⊓ Subgroup.centralizer (K : Set G) : Subgroup G) :=
      Subgroup.card_le_of_le (inf_le_inf_right _ hPiB₁)
    have hpos : 0 < Nat.card (B₁ ⊓ Subgroup.centralizer (K : Set G) : Subgroup G) := Nat.card_pos
    have : Nat.card (ggL45KgE K B₁ hcfg.kg_B1N) *
        Nat.card (B₁ ⊓ Subgroup.centralizer (K : Set G) : Subgroup G) ≤
        p * Nat.card (ggL45KgE K Pi hPiN) *
          Nat.card (B₁ ⊓ Subgroup.centralizer (K : Set G) : Subgroup G) := by
      rw [h1]
      calc Nat.card B₁ ≤ p * Nat.card Pi := hPicard
        _ = p * (Nat.card (ggL45KgE K Pi hPiN) *
              Nat.card (Pi ⊓ Subgroup.centralizer (K : Set G) : Subgroup G)) := by rw [h2]
        _ ≤ p * (Nat.card (ggL45KgE K Pi hPiN) *
              Nat.card (B₁ ⊓ Subgroup.centralizer (K : Set G) : Subgroup G)) :=
            Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ h3)
        _ = _ := by ring
    exact Nat.le_of_mul_le_mul_right this hpos
  · obtain ⟨b, hb, hbN, rfl⟩ := mem_ggL45KgE.mp he
    obtain ⟨g₀, hg₀X, hg₀⟩ := hPi b hb
    have hFC := hcfg.1
    have hXN : X ≤ Subgroup.normalizer (Bs : Set G) := hFC.2.2.1
    obtain ⟨k, hk⟩ := hFC.2.2.2.2.2.1 g₀ hg₀X
    obtain ⟨N, ⟨a, ha⟩, hc⟩ := exists_pElt_pow p (C := Subgroup.centralizer (Bs : Set G)) hk
    set g := g₀ ^ N with hgdef
    have hgX : g ∈ X := X.pow_mem hg₀X N
    have hgB₁ : ∀ b' ∈ B₁, g * b' = b' * g := fun b' hb' =>
      (Subgroup.mem_centralizer_iff.mp hb'.2 g hgX)
    have h44 := hcfg.2.2.2.2.2.1
    have hdD : d ∈ D ⊓ B₁ := by rw [h44.1]; exact Subgroup.mem_zpowers d
    have hgnB₁ : g ∈ Subgroup.normalizer (B₁ : Set G) :=
      Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun b' hb' =>
        (hgB₁ b' hb').symm)
    have hgnd : g ∈ Subgroup.normalizer (Subgroup.zpowers d : Set G) :=
      Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun z hz => by
        obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
        exact (Commute.zpow_right (hgB₁ d hdD.2) n).eq.symm)
    have hgN : g ∈ Subgroup.normalizer (K : Set G) :=
      hFC.2.1 X hXN hFC.2.2.2.1 hFC.2.2.2.2.1 hFC.2.2.2.2.2.1 hFC.2.2.2.2.2.2 d hdD h44.2.1 y K
        h44.2.2.1 h44.2.2.2.1 ⟨hgnB₁, hgnd⟩
    have hcomm : g * x * g⁻¹ * x⁻¹ = b := by
      rw [← hg₀]
      set c := g₀ * g⁻¹
      have hcg : g₀ = c * g := by simp [c]
      have hgxg : g * x * g⁻¹ ∈ Bs := by
        have := (Subgroup.mem_normalizer_iff.mp (hXN hgX) x).mp hcfg.x_mem
        simpa [mul_assoc] using this
      have hcx : c * (g * x * g⁻¹) = (g * x * g⁻¹) * c :=
        (Subgroup.mem_centralizer_iff.mp hc _ hgxg).symm
      rw [hcg]
      calc g * x * g⁻¹ * x⁻¹ = (c * (g * x * g⁻¹) * c⁻¹) * x⁻¹ := by
            rw [hcx]; group
        _ = c * g * x * (c * g)⁻¹ * x⁻¹ := by group
    refine ⟨K.normalizerMonoidHom ⟨g, hgN⟩, ⟨a, ?_⟩, ?_, ?_, ?_⟩
    · rw [← map_pow]
      have : (⟨g, hgN⟩ : Subgroup.normalizer (K : Set G)) ^ p ^ a = 1 :=
        Subtype.ext (by simpa [hgdef] using ha)
      rw [this, map_one]
    · intro e' he'
      obtain ⟨b', hb', hb'N, rfl⟩ := mem_ggL45KgE.mp he'
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hgB₁ b' hb')
    ·
      have hga : g ^ p ^ a = 1 := ha
      have hzp : IsPGroup p (Subgroup.zpowers g) := by
        rintro ⟨z, hz⟩
        obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
        refine ⟨a, Subtype.ext ?_⟩
        show (g ^ n) ^ p ^ a = 1
        rw [← zpow_natCast (g ^ n), ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hga, one_zpow]
      have hMp : IsPGroup p (Subgroup.zpowers g ⊔ Bs : Subgroup G) :=
        hzp.to_sup_of_normal_right' (isPGroup_of_isElemAbelian hcfg.isElemAbelian)
          ((Subgroup.zpowers_le).mpr (hXN hgX))
      have hM'p : IsPGroup p ((Subgroup.zpowers g ⊔ Bs).subgroupOf
          (Subgroup.normalizer (K : Set G))) :=
        hMp.comap_of_injective _ (Subgroup.subtype_injective _)
      refine (hM'p.map K.normalizerMonoidHom).to_le ((Subgroup.closure_le _).mpr ?_)
      intro α hα
      rcases hα with rfl | rfl | hαE
      · exact ⟨⟨g, hgN⟩, Subgroup.mem_subgroupOf.mpr
          (Subgroup.mem_sup_left (Subgroup.mem_zpowers g)), rfl⟩
      · exact ⟨⟨x⁻¹, inv_mem hcfg.kg_xN⟩, Subgroup.mem_subgroupOf.mpr
          (Subgroup.mem_sup_right (inv_mem hcfg.x_mem)), rfl⟩
      · obtain ⟨b', hb', hb'N, rfl⟩ := mem_ggL45KgE.mp hαE
        exact ⟨⟨b', hb'N⟩, Subgroup.mem_subgroupOf.mpr (Subgroup.mem_sup_right hb'.1), rfl⟩
    · have hb : (⟨b, hbN⟩ : Subgroup.normalizer (K : Set G)) =
          ⟨g, hgN⟩ * (⟨x⁻¹, inv_mem hcfg.kg_xN⟩)⁻¹ * (⟨g, hgN⟩)⁻¹ * ⟨x⁻¹, inv_mem hcfg.kg_xN⟩ :=
        Subtype.ext (by simp [← hcomm])
      rw [hb]
      simp only [map_mul, map_inv]

omit [Finite G] in
theorem ggL45_card_mul_le_card_sup [Finite G] {A C : Subgroup G} (hinf : A ⊓ C = ⊥) :
    Nat.card A * Nat.card C ≤ Nat.card (A ⊔ C : Subgroup G) := by
  rw [← Nat.card_prod]
  refine Nat.card_le_card_of_injective
    (fun ac => ⟨(ac.1 : G) * ac.2, (A ⊔ C).mul_mem (Subgroup.mem_sup_left ac.1.2)
      (Subgroup.mem_sup_right ac.2.2)⟩) ?_
  rintro ⟨a, c⟩ ⟨a', c'⟩ h
  have h' : (a : G) * c = a' * c' := congrArg Subtype.val h
  have hm : (a' : G)⁻¹ * a ∈ A ⊓ C := by
    refine ⟨A.mul_mem (A.inv_mem a'.2) a.2, ?_⟩
    have : (a' : G)⁻¹ * a = c' * (c : G)⁻¹ := by
      rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, eq_mul_inv_iff_mul_eq]
      exact h'
    rw [this]
    exact C.mul_mem c'.2 (C.inv_mem c.2)
  rw [hinf, Subgroup.mem_bot] at hm
  have ha : a = a' := Subtype.ext (inv_mul_eq_one.mp hm).symm
  subst ha
  have hc : c = c' := Subtype.ext (mul_left_cancel h')
  rw [hc]

theorem ggLAut_eq_one_of_cent {R : Type} [Group R] (θ : K ⧸ Subgroup.center K ≃* R) {v : G}
    (hv : v ∈ Subgroup.centralizer (K : Set G)) :
    ggLAut K θ ⟨v, Subgroup.centralizer_le_normalizer _ hv⟩ = 1 := by
  ext r
  obtain ⟨q, rfl⟩ := θ.surjective r
  induction q using QuotientGroup.induction_on with
  | H l =>
    rw [ggLAut_apply, MulAut.one_apply]
    congr 2
    refine Subtype.ext ?_
    rw [normalizerMonoidHom_coe]
    rw [(Subgroup.mem_centralizer_iff.mp hv l l.2).symm]
    group

theorem GGL45Config.kg_xout
    (hcfg : GGL45Config p B Bs x L D J X B₂ d y K U U₁) {R : Type} [Group R]
    {I : Set (MulAut R)} (θ : K ⧸ Subgroup.center K ≃* R) (hinn : ∀ r : R, MulAut.conj r ∈ I)
    (hxI : ggLAut K θ ⟨x, hcfg.kg_xN⟩ ∉ I) :
    ∀ z ∈ Subgroup.zpowers x, ∀ a ∈ K, ∀ v ∈ Subgroup.centralizer (K : Set G), z = a * v →
      z = 1 := by
  have : Fact p.Prime := ⟨hcfg.prime⟩
  intro z hz a ha v hv hzav
  by_contra hz1
  have heq := zpowers_eq_of_mem_of_ne_one hcfg.x_pow hz hz1
  have hxz : x ∈ Subgroup.zpowers z := heq ▸ Subgroup.mem_zpowers x
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hxz
  have hav : Commute a v := Subgroup.mem_centralizer_iff.mp hv a ha
  have hx : x = a ^ m * v ^ m := by rw [← hm, hzav, hav.mul_zpow]
  have hamN : a ^ m ∈ Subgroup.normalizer (K : Set G) :=
    Subgroup.le_normalizer (K.zpow_mem ha m)
  have hvmC : v ^ m ∈ Subgroup.centralizer (K : Set G) :=
    (Subgroup.centralizer (K : Set G)).zpow_mem hv m
  have hsplit : (⟨x, hcfg.kg_xN⟩ : Subgroup.normalizer (K : Set G)) =
      ⟨a ^ m, hamN⟩ * ⟨v ^ m, Subgroup.centralizer_le_normalizer _ hvmC⟩ :=
    Subtype.ext hx
  apply hxI
  rw [hsplit, map_mul, ggLAut_eq_one_of_cent θ hvmC, mul_one]
  have := ggLAut_mk_self K θ ⟨a ^ m, K.zpow_mem ha m⟩
  rw [this]
  exact hinn _

theorem GGL45Config.kg_rk
    (hcfg : GGL45Config p B Bs x L D J X B₂ d y K U U₁) {R : Type} [Group R]
    {I : Set (MulAut R)} (θ : K ⧸ Subgroup.center K ≃* R) (hinn : ∀ r : R, MulAut.conj r ∈ I)
    (hxI : ggLAut K θ ⟨x, hcfg.kg_xN⟩ ∉ I)
    (hcent : Bs ⊓ Subgroup.centralizer (X : Set G) ⊓ Subgroup.centralizer (K : Set G) ≤
      Subgroup.zpowers d) :
    ∀ R₀ Q : Subgroup K, IsElemAbelian p R₀ →
      (∀ r ∈ R₀, K.normalizerMonoidHom ⟨x⁻¹, inv_mem hcfg.kg_xN⟩ r = r) → IsPGroup 2 Q →
      Q ≠ ⊥ → (∀ g ∈ Q, K.normalizerMonoidHom ⟨x⁻¹, inv_mem hcfg.kg_xN⟩ g ∈ Q) →
      R₀ ≤ Subgroup.normalizer (Q : Set K) →
      Nat.card R₀ * p ≤ Nat.card (ggL45KgE K _ hcfg.kg_B1N) * p ^ 2 ∧
        (Nat.Coprime p (Nat.card (Subgroup.center K)) →
          Nat.card R₀ ≤ Nat.card (ggL45KgE K _ hcfg.kg_B1N)) := by
  have hp : p.Prime := hcfg.prime
  have : Fact p.Prime := ⟨hp⟩
  intro R₀ Q hR₀ hR₀x hQ2 hQ1 hQψ hR₀Q
  set R₀' : Subgroup G := R₀.map K.subtype
  set Q' : Subgroup G := Q.map K.subtype
  have hxout := hcfg.kg_xout θ hinn hxI
  have hR₀x' : ∀ r ∈ R₀', r * x = x * r := by
    rintro _ ⟨r, hr, rfl⟩
    exact (psi_fix_iff hcfg.kg_xN r).mp (hR₀x r hr)
  have hQx : ∀ q ∈ Q', x⁻¹ * q * x ∈ Q' := by
    rintro _ ⟨q, hq, rfl⟩
    refine ⟨_, hQψ q hq, ?_⟩
    simp [ggL45_rhoK_coe]
  have hQxn : ∀ n : ℕ, ∀ q ∈ Q', x⁻¹ ^ n * q * x ^ n ∈ Q' := by
    intro n
    induction n with
    | zero => intro q hq; simpa using hq
    | succ n ih =>
      intro q hq
      have := hQx _ (ih q hq)
      have e : x⁻¹ ^ (n + 1) * q * x ^ (n + 1) = x⁻¹ * (x⁻¹ ^ n * q * x ^ n) * x := by
        rw [pow_succ' x⁻¹, pow_succ x]; group
      rw [e]; exact this
  have hxNQ : x ∈ Subgroup.normalizer (Q' : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro q
    constructor
    · intro hq
      have hxp : x ^ p = 1 := hcfg.x_pow
      have h1 := hQxn (p - 1) q hq
      have e1 : x⁻¹ ^ (p - 1) = x := by
        have : x⁻¹ ^ (p - 1) * x⁻¹ = 1 := by
          rw [← pow_succ, Nat.sub_add_cancel hp.one_lt.le, inv_pow, hxp, inv_one]
        calc x⁻¹ ^ (p - 1) = x⁻¹ ^ (p - 1) * x⁻¹ * x := by group
          _ = x := by rw [this, one_mul]
      have e2 : x ^ (p - 1) = x⁻¹ := by
        rw [← inv_inv (x ^ (p - 1)), ← inv_pow, e1]
      rwa [e1, e2] at h1
    · intro hq
      have := hQx _ hq
      simpa [mul_assoc] using this
  have hR₀NQ : R₀' ≤ Subgroup.normalizer (Q' : Set G) :=
    (Subgroup.map_mono hR₀Q).trans (Subgroup.le_normalizer_map K.subtype)
  have hQ'2 : IsPGroup 2 Q' := hQ2.map K.subtype
  have hQ'1 : Q' ≠ ⊥ := by
    intro h
    apply hQ1
    rw [eq_bot_iff]
    intro q hq
    have : (q : G) ∈ Q' := ⟨q, hq, rfl⟩
    rw [h, Subgroup.mem_bot] at this
    exact (Subgroup.mem_bot).mpr (Subtype.ext this)
  have hTL : IsTwoLocal (Subgroup.normalizer (Q' : Set G)) := ⟨Q', hQ'1, hQ'2, rfl⟩
  have hI := hcfg.1.1.1
  have hB : Nat.card B = p ^ LargeEvenTwoLocalRank p G := hI.2.2.2.2.2.2.1.1.2.1
  have h43 : GGL43 Bs x X := hcfg.2.2.1
  have hx1 : x ≠ 1 := fun h => h43.1 (h ▸ one_mem _)
  have hle := card_bstar_le_of_ggL43 hcfg.isElemAbelian hcfg.x_mem hx1 h43
  have hker : Nat.card (Bs ⊓ Subgroup.centralizer (X : Set G) ⊓
      Subgroup.centralizer (K : Set G) : Subgroup G) ≤ p := by
    calc _ ≤ Nat.card (Subgroup.zpowers d) := Subgroup.card_le_of_le hcent
      _ = p := by rw [Nat.card_zpowers, orderOf_eq_prime hcfg.d_pow hcfg.d_ne]
  have hcard := card_ggL45KgE_mul K _ hcfg.kg_B1N
  have hm : p ^ LargeEvenTwoLocalRank p G ≤ Nat.card (ggL45KgE K _ hcfg.kg_B1N) * p ^ 2 := by
    calc p ^ LargeEvenTwoLocalRank p G = Nat.card B := hB.symm
      _ ≤ Nat.card Bs := Subgroup.card_le_of_le hcfg.1.1.2.1.1
      _ ≤ Nat.card (Bs ⊓ Subgroup.centralizer (X : Set G) : Subgroup G) * p := hle
      _ = Nat.card (ggL45KgE K _ hcfg.kg_B1N) * Nat.card (Bs ⊓ Subgroup.centralizer (X : Set G) ⊓
            Subgroup.centralizer (K : Set G) : Subgroup G) * p := by rw [hcard]
      _ ≤ Nat.card (ggL45KgE K _ hcfg.kg_B1N) * p * p :=
            Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hker)
      _ = _ := by ring
  have hzx : IsElemAbelian p (Subgroup.zpowers x) := ggL45_isElemAbelian_zpowers' hcfg.x_pow
  have hzd : IsElemAbelian p (Subgroup.zpowers d) := ggL45_isElemAbelian_zpowers' hcfg.d_pow
  have hinf1 : R₀' ⊓ Subgroup.zpowers x = ⊥ := by
    rw [eq_bot_iff]
    rintro z ⟨⟨r, hr, rfl⟩, hz⟩
    exact (Subgroup.mem_bot).mpr
      (hxout _ hz r r.2 1 (Subgroup.one_mem _) (mul_one _).symm)
  have hcR₀x : ∀ a ∈ R₀', ∀ c ∈ Subgroup.zpowers x, a * c = c * a := by
    intro a ha c hc
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
    exact (Commute.zpow_right (hR₀x' a ha : Commute a x) n).eq
  have hE₁ab : IsElemAbelian p (R₀' ⊔ Subgroup.zpowers x) :=
    TableB.isElemAbelian_sup (TableB.isElemAbelian_map hR₀ K.subtype) hzx hcR₀x
  have hE₁N : R₀' ⊔ Subgroup.zpowers x ≤ Subgroup.normalizer (Q' : Set G) :=
    sup_le hR₀NQ ((Subgroup.zpowers_le).mpr hxNQ)
  have hcR₀ : Nat.card R₀' = Nat.card R₀ :=
    Subgroup.card_map_of_injective K.subtype_injective
  have hcx : Nat.card (Subgroup.zpowers x) = p := by
    rw [Nat.card_zpowers, orderOf_eq_prime hcfg.x_pow hx1]
  have hcd : Nat.card (Subgroup.zpowers d) = p := by
    rw [Nat.card_zpowers, orderOf_eq_prime hcfg.d_pow hcfg.d_ne]
  have h1 := TableB.card_le_of_twoLocal hp hTL hE₁N hE₁ab
  have h2 := ggL45_card_mul_le_card_sup hinf1
  rw [hcR₀, hcx] at h2
  refine ⟨?_, fun hcop => ?_⟩
  · calc Nat.card R₀ * p ≤ _ := h2
      _ ≤ _ := h1
      _ ≤ _ := hm
  ·
    have hdV := hcfg.d_mem_V
    have hdC : d ∈ Subgroup.centralizer (K : Set G) := hdV.2
    have hE₁d : R₀' ⊔ Subgroup.zpowers x ≤ Subgroup.centralizer ({d} : Set G) := by
      refine sup_le ?_ ((Subgroup.zpowers_le).mpr ?_)
      · rintro _ ⟨r, -, rfl⟩
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact (Subgroup.mem_centralizer_iff.mp hdC r r.2)
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact mul_comm_of_isElemAbelian hcfg.isElemAbelian hcfg.x_mem hcfg.d_mem.1
    have hcE₁d : ∀ a ∈ R₀' ⊔ Subgroup.zpowers x, ∀ c ∈ Subgroup.zpowers d, a * c = c * a := by
      intro a ha c hc
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
      have had : Commute a d := Subgroup.mem_centralizer_singleton_iff.mp (hE₁d ha)
      exact (Commute.zpow_right had n).eq
    have hE₂ab := TableB.isElemAbelian_sup hE₁ab hzd hcE₁d
    have hdNQ : Subgroup.zpowers d ≤ Subgroup.normalizer (Q' : Set G) := by
      refine (Subgroup.zpowers_le).mpr (Subgroup.centralizer_le_normalizer _ ?_)
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨q, -, rfl⟩
      exact (Subgroup.mem_centralizer_iff.mp hdC q q.2)
    have h3 := TableB.card_le_of_twoLocal hp hTL (sup_le hE₁N hdNQ) hE₂ab
    have hR₀Nx : R₀' ≤ Subgroup.normalizer (Subgroup.zpowers x : Set G) := fun a ha =>
      Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun c hc =>
        (hcR₀x a ha c hc).symm)
    have hinf2 : (R₀' ⊔ Subgroup.zpowers x) ⊓ Subgroup.zpowers d = ⊥ := by
      rw [eq_bot_iff]
      rintro z ⟨hz1, hz2⟩
      have hz1' : z ∈ ((R₀' ⊔ Subgroup.zpowers x : Subgroup G) : Set G) := hz1
      rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hR₀Nx] at hz1'
      obtain ⟨a, ha, w, hw, hzaw⟩ := hz1'
      obtain ⟨r, -, hra⟩ := ha
      have hra' : (r : G) = a := hra
      subst hzaw
      beta_reduce at hz2 ⊢
      have hzC : a * w ∈ Subgroup.centralizer (K : Set G) := by
        obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hz2
        rw [← hn]
        exact (Subgroup.centralizer (K : Set G)).zpow_mem hdC n
      have haK : a⁻¹ ∈ K := by rw [← hra']; exact K.inv_mem r.2
      have hw1 : w = 1 := hxout w hw a⁻¹ haK _ hzC (by group)
      subst hw1
      rw [mul_one] at hzC hz2 ⊢
      rw [← hra'] at hzC hz2 ⊢
      rw [Subgroup.mem_bot]
      by_contra hr1
      have hrp : (r : G) ^ p = 1 := by
        obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hz2
        rw [← hn, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hcfg.d_pow,
          one_zpow]
      have hrZ : r ∈ Subgroup.center K := by
        rw [Subgroup.mem_center_iff]
        intro g
        exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hzC g g.2)
      have hord : orderOf (⟨r, hrZ⟩ : Subgroup.center K) = p := by
        refine orderOf_eq_prime (Subtype.ext (Subtype.ext ?_)) ?_
        · simpa using hrp
        · intro h
          apply hr1
          have := congrArg (fun t : Subgroup.center K => ((t : K) : G)) h
          simpa using this
      have hdvd : p ∣ Nat.card (Subgroup.center K) := hord ▸ orderOf_dvd_natCard _
      exact hp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hcop hdvd)
    have h4 := ggL45_card_mul_le_card_sup hinf2
    rw [hcd] at h4
    have hp0 := hp.pos
    have : Nat.card R₀ * p * p ≤ Nat.card (ggL45KgE K _ hcfg.kg_B1N) * p ^ 2 :=
      calc Nat.card R₀ * p * p ≤ Nat.card (R₀' ⊔ Subgroup.zpowers x : Subgroup G) * p :=
            Nat.mul_le_mul_right _ h2
        _ ≤ _ := h4
        _ ≤ _ := h3
        _ ≤ _ := hm
    have e : Nat.card R₀ * p * p = Nat.card R₀ * p ^ 2 := by ring
    rw [e] at this
    exact Nat.le_of_mul_le_mul_right this (pow_pos hp0 2)

end Config

end CFSG.StandardType
