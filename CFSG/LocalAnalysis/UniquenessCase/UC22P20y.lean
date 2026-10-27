module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P20i
public import CFSG.GH74.BNPair.Lemma3013

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem uc22pw_disjoint_of_odd {N A : Subgroup G} (hN : IsPGroup 2 N) (hA : Odd (Nat.card A)) :
    Disjoint N A := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hN
  refine Subgroup.disjoint_of_coprime_natCard ?_
  rw [hk]
  exact Nat.Coprime.pow_left k (Nat.coprime_two_left.2 hA)

theorem uc22pw_permutes_of_split {T S Ê A : Subgroup G} (hST : S ≤ T)
    (hTÊ : T ≤ normalizer (Ê : Set G)) (hsplit : (S : Set G) * (A : Set G) = (Ê : Set G)) :
    Permutes A T := by
  have hAÊ : A ≤ Ê := fun a ha => by
    have : a ∈ (Ê : Set G) := by
      rw [← hsplit]
      exact Set.mem_mul.2 ⟨1, S.one_mem, a, ha, one_mul a⟩
    exact this
  have hconj : ∀ t ∈ T, ∀ x ∈ Ê, t * x * t⁻¹ ∈ Ê := fun t ht x hx =>
    (Subgroup.mem_normalizer_iff.1 (hTÊ ht) x).1 hx
  have hAS : ∀ x ∈ Ê, ∃ a ∈ A, ∃ s ∈ S, x = a * s := by
    intro x hx
    have hx' : x⁻¹ ∈ (S : Set G) * (A : Set G) := hsplit ▸ Ê.inv_mem hx
    obtain ⟨s, hs, a, ha, hsa⟩ := Set.mem_mul.1 hx'
    exact ⟨a⁻¹, A.inv_mem ha, s⁻¹, S.inv_mem hs, by
      have : x = (s * a)⁻¹ := by rw [hsa, inv_inv]
      rw [this, mul_inv_rev]⟩
  have hSA : ∀ x ∈ Ê, ∃ s ∈ S, ∃ a ∈ A, x = s * a := by
    intro x hx
    obtain ⟨s, hs, a, ha, h⟩ := Set.mem_mul.1 (hsplit ▸ hx : x ∈ (S : Set G) * (A : Set G))
    exact ⟨s, hs, a, ha, h.symm⟩
  unfold Permutes
  ext x
  constructor
  · rintro ⟨a, ha, t, ht, rfl⟩
    obtain ⟨s, hs, a', ha', h⟩ := hSA (t⁻¹ * a * t) (by
      simpa using hconj t⁻¹ (T.inv_mem ht) a (hAÊ ha))
    refine ⟨t * s, T.mul_mem ht (hST hs), a', ha', ?_⟩
    calc t * s * a' = t * (s * a') := by rw [mul_assoc]
      _ = t * (t⁻¹ * a * t) := by rw [← h]
      _ = a * t := by group
  · rintro ⟨t, ht, a, ha, rfl⟩
    obtain ⟨a', ha', s, hs, h⟩ := hAS (t * a * t⁻¹) (hconj t ht a (hAÊ ha))
    refine ⟨a', ha', s * t, T.mul_mem (hST hs) ht, ?_⟩
    calc a' * (s * t) = (a' * s) * t := by rw [mul_assoc]
      _ = (t * a * t⁻¹) * t := by rw [← h]
      _ = t * a := by group

theorem uc22pw_mem_normalizer_of_fixed {T S : Subgroup G} (hST : S ≤ T) {b : G}
    (hbS : b ∈ normalizer (S : Set G)) (hfix : ∀ t ∈ T, ∃ s ∈ S, t * b * t⁻¹ = b * s) :
    b ∈ normalizer (T : Set G) := by
  have key : ∀ c : G, c ∈ normalizer (S : Set G) → (∀ t ∈ T, ∃ s ∈ S, t * c * t⁻¹ = c * s) →
      ∀ x ∈ T, c * x * c⁻¹ ∈ T := by
    intro c hcS hc x hx
    obtain ⟨s, hs, hxs⟩ := hc x hx
    have h1 : c * x * c⁻¹ = (c * s⁻¹ * c⁻¹) * x := by
      have : x * c⁻¹ * x⁻¹ = s⁻¹ * c⁻¹ := by
        have h := congrArg (fun y => y⁻¹) hxs
        simp only [mul_inv_rev, inv_inv] at h
        calc x * c⁻¹ * x⁻¹ = (x * c * x⁻¹)⁻¹ := by group
          _ = (c * s)⁻¹ := by rw [hxs]
          _ = s⁻¹ * c⁻¹ := by rw [mul_inv_rev]
      calc c * x * c⁻¹ = c * (x * c⁻¹ * x⁻¹) * x := by group
        _ = c * (s⁻¹ * c⁻¹) * x := by rw [this]
        _ = (c * s⁻¹ * c⁻¹) * x := by group
    rw [h1]
    refine T.mul_mem (hST ?_) hx
    exact (Subgroup.mem_normalizer_iff.1 hcS s⁻¹).1 (S.inv_mem hs) |> fun h => by
      simpa [mul_assoc] using h
  have hbinv : b⁻¹ ∈ normalizer (S : Set G) := inv_mem hbS
  have hfix' : ∀ t ∈ T, ∃ s ∈ S, t * b⁻¹ * t⁻¹ = b⁻¹ * s := by
    intro t ht
    obtain ⟨s, hs, hts⟩ := hfix t ht
    refine ⟨b * s⁻¹ * b⁻¹, ?_, ?_⟩
    · have := (Subgroup.mem_normalizer_iff.1 hbS s⁻¹).1 (S.inv_mem hs)
      simpa [mul_assoc] using this
    · calc t * b⁻¹ * t⁻¹ = (t * b * t⁻¹)⁻¹ := by group
        _ = (b * s)⁻¹ := by rw [hts]
        _ = b⁻¹ * (b * s⁻¹ * b⁻¹) := by group
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    exact key b hbS hfix x hx
  · intro hx
    have := key b⁻¹ hbinv hfix' _ hx
    simpa [mul_assoc] using this

theorem uc22pw_exists_complement {S Ê : Subgroup G} (hSÊ : S ≤ Ê) (hSn : (S.subgroupOf Ê).Normal)
    (h2 : IsPGroup 2 S) (hi : Odd (S.subgroupOf Ê).index) :
    ∃ A : Subgroup G, A ≤ Ê ∧ Odd (Nat.card A) ∧ Disjoint S A ∧
      (S : Set G) * (A : Set G) = (Ê : Set G) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI := hSn
  have hSp : IsPGroup 2 (S.subgroupOf Ê) := h2.of_equiv (Subgroup.subgroupOfEquivOfLe hSÊ).symm
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hSp
  have hcop : Nat.Coprime (Nat.card (S.subgroupOf Ê)) (S.subgroupOf Ê).index := by
    rw [hk]
    exact Nat.Coprime.pow_left k (Nat.coprime_two_left.2 hi)
  obtain ⟨H, hH⟩ := Subgroup.exists_right_complement'_of_coprime hcop
  refine ⟨H.map Ê.subtype, Subgroup.map_subtype_le H, ?_, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective Ê.subtype_injective, ← hH.symm.index_eq_card]
    exact hi
  · refine Subgroup.disjoint_def.2 fun {x} hxS hxA => ?_
    obtain ⟨h, hh, rfl⟩ := hxA
    have h1 : h ∈ S.subgroupOf Ê := hxS
    have := Subgroup.disjoint_def.1 hH.disjoint h1 hh
    rw [this]
    simp
  · have hmul : ((S.subgroupOf Ê : Subgroup ↥Ê) : Set ↥Ê) * (H : Set ↥Ê) = Set.univ := by
      rw [← Subgroup.normal_mul, hH.sup_eq_top]
      simp
    ext x
    constructor
    · rintro ⟨s, hs, a, ⟨h, hh, rfl⟩, rfl⟩
      exact Ê.mul_mem (hSÊ hs) h.2
    · intro hx
      have hx' : (⟨x, hx⟩ : ↥Ê) ∈ ((S.subgroupOf Ê : Subgroup ↥Ê) : Set ↥Ê) * (H : Set ↥Ê) := by
        rw [hmul]
        trivial
      obtain ⟨n, hn, h, hh, hnh⟩ := Set.mem_mul.1 hx'
      refine ⟨(n : G), hn, (h : G), ⟨h, hh, rfl⟩, ?_⟩
      exact congrArg Subtype.val hnh


theorem uc22pw_conj_complements {N K A₁ A₂ : Subgroup G} (hNK : N ≤ K) (hNn : (N.subgroupOf K).Normal)
    (hN2 : IsPGroup 2 N) (h₁K : A₁ ≤ K) (h₂K : A₂ ≤ K) (hodd₁ : Odd (Nat.card A₁))
    (hodd₂ : Odd (Nat.card A₂)) (hsup : N ⊔ A₂ = N ⊔ A₁) :
    ∃ e ∈ N, A₂.map (MulAut.conj e).toMonoidHom = A₁ := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI := hNn
  have hN'2 : IsPGroup 2 (N.subgroupOf K) := hN2.of_equiv (Subgroup.subgroupOfEquivOfLe hNK).symm
  have hZ : ¬ 2 ∣ Nat.card (A₁.subgroupOf K) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe h₁K).toEquiv]
    exact fun h => (Nat.not_even_iff_odd.2 hodd₁) (even_iff_two_dvd.2 h)
  have hd₁ : Disjoint (N.subgroupOf K) (A₁.subgroupOf K) := by
    refine Subgroup.disjoint_def.2 fun {x} hx1 hx2 => ?_
    have := Subgroup.disjoint_def.1 (uc22pw_disjoint_of_odd hN2 hodd₁) hx1 hx2
    exact Subtype.ext this
  have hd₂ : Disjoint (N.subgroupOf K) (A₂.subgroupOf K) := by
    refine Subgroup.disjoint_def.2 fun {x} hx1 hx2 => ?_
    have := Subgroup.disjoint_def.1 (uc22pw_disjoint_of_odd hN2 hodd₂) hx1 hx2
    exact Subtype.ext this
  have hsup' : N.subgroupOf K ⊔ A₂.subgroupOf K = N.subgroupOf K ⊔ A₁.subgroupOf K := by
    rw [← Subgroup.subgroupOf_sup hNK h₂K, ← Subgroup.subgroupOf_sup hNK h₁K, hsup]
  obtain ⟨e', he', hconj⟩ := CFSG.GH74.BNPair.exists_conj_of_complements (p := 2) hN'2 hZ hd₁ hd₂ hsup'
  refine ⟨(e' : G), he', ?_⟩
  ext y
  constructor
  · rintro ⟨a, ha, rfl⟩
    have h1 : (⟨a, h₂K ha⟩ : ↥K) ∈ A₂.subgroupOf K := ha
    have h2 : (MulAut.conj e' : MulAut ↥K) ⟨a, h₂K ha⟩ ∈ A₁.subgroupOf K := by
      rw [← hconj]
      exact Subgroup.mem_map_of_mem _ h1
    have h3 := Subgroup.mem_subgroupOf.1 h2
    simpa [MulAut.conj_apply] using h3
  · intro hy
    have h1 : (⟨y, h₁K hy⟩ : ↥K) ∈ A₁.subgroupOf K := hy
    rw [← hconj] at h1
    obtain ⟨a', ha', ha'y⟩ := Subgroup.mem_map.1 h1
    refine ⟨(a' : G), ha', ?_⟩
    have := congrArg Subtype.val ha'y
    simpa [MulAut.conj_apply] using this


theorem uc22pw_exists_mul_mem_normalizer {T S Ê A : Subgroup G}
    (hTS : T ≤ normalizer (S : Set G)) (hTÊ : T ≤ normalizer (Ê : Set G))
    (hS2 : IsPGroup 2 S) (hAodd : Odd (Nat.card A)) (hAS : A ≤ normalizer (S : Set G))
    (hsplit : (S : Set G) * (A : Set G) = (Ê : Set G)) {t : G} (ht : t ∈ T) :
    ∃ s ∈ S, s * t ∈ normalizer (A : Set G) := by
  classical
  have hSÊ : S ≤ Ê := fun s hs => by
    have : s ∈ (Ê : Set G) := by
      rw [← hsplit]
      exact Set.mem_mul.2 ⟨s, hs, 1, A.one_mem, mul_one s⟩
    exact this
  have hAÊ : A ≤ Ê := fun a ha => by
    have : a ∈ (Ê : Set G) := by
      rw [← hsplit]
      exact Set.mem_mul.2 ⟨1, S.one_mem, a, ha, one_mul a⟩
    exact this
  have hÊS : ∀ x ∈ Ê, ∀ y ∈ S, x * y * x⁻¹ ∈ S := by
    intro x hx y hy
    have hx' : x ∈ (S : Set G) * (A : Set G) := hsplit ▸ hx
    obtain ⟨s, hs, a, ha, rfl⟩ := Set.mem_mul.1 hx'
    have h1 : a * y * a⁻¹ ∈ S := (Subgroup.mem_normalizer_iff.1 (hAS ha) y).1 hy
    have h2 : s * (a * y * a⁻¹) * s⁻¹ ∈ S := S.mul_mem (S.mul_mem hs h1) (S.inv_mem hs)
    simpa [mul_assoc] using h2
  have hSn : (S.subgroupOf Ê).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simpa using hÊS g g.2 n hn
  set A₂ : Subgroup G := A.map (MulAut.conj t).toMonoidHom with hA₂
  have hA₂Ê : A₂ ≤ Ê := by
    rintro _ ⟨a, ha, rfl⟩
    exact (Subgroup.mem_normalizer_iff.1 (hTÊ ht) a).1 (hAÊ ha)
  have hA₂odd : Odd (Nat.card A₂) := by
    rw [hA₂, Subgroup.card_map_of_injective (MulAut.conj t).injective]
    exact hAodd
  have hsupA : S ⊔ A = Ê := by
    refine le_antisymm (sup_le hSÊ hAÊ) fun x hx => ?_
    have hx' : x ∈ (S : Set G) * (A : Set G) := hsplit ▸ hx
    obtain ⟨s, hs, a, ha, rfl⟩ := Set.mem_mul.1 hx'
    exact Subgroup.mul_mem_sup hs ha
  have hsupA₂ : S ⊔ A₂ = S ⊔ A := by
    rw [hsupA]
    refine le_antisymm (sup_le hSÊ hA₂Ê) fun x hx => ?_
    have hx1 : t⁻¹ * x * t ∈ Ê := (Subgroup.mem_normalizer_iff''.1 (hTÊ ht) x).1 hx
    have hx' : t⁻¹ * x * t ∈ (S : Set G) * (A : Set G) := hsplit ▸ hx1
    obtain ⟨s, hs, a, ha, hsa⟩ := Set.mem_mul.1 hx'
    have hxeq : x = (t * s * t⁻¹) * (t * a * t⁻¹) := by
      calc x = t * (t⁻¹ * x * t) * t⁻¹ := by group
        _ = t * (s * a) * t⁻¹ := by rw [hsa]
        _ = (t * s * t⁻¹) * (t * a * t⁻¹) := by group
    rw [hxeq]
    refine Subgroup.mul_mem_sup ?_ ⟨a, ha, by simp [MulAut.conj_apply]⟩
    exact (Subgroup.mem_normalizer_iff.1 (hTS ht) s).1 hs
  obtain ⟨e, he, hconj⟩ := uc22pw_conj_complements hSÊ hSn hS2 hAÊ hA₂Ê hAodd hA₂odd hsupA₂
  refine ⟨e, he, ?_⟩
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    have h1 : e * (t * h * t⁻¹) * e⁻¹ ∈ A₂.map (MulAut.conj e).toMonoidHom :=
      ⟨t * h * t⁻¹, ⟨h, hh, by simp [MulAut.conj_apply]⟩, by simp [MulAut.conj_apply]⟩
    rw [hconj] at h1
    simpa [mul_assoc] using h1
  · intro hh
    have h1 : e * (t * h * t⁻¹) * e⁻¹ ∈ A := by simpa [mul_assoc] using hh
    rw [← hconj] at h1
    obtain ⟨x, hx, hxe⟩ := Subgroup.mem_map.1 h1
    obtain ⟨a, ha, rfl⟩ := hx
    have hxe' : e * (t * a * t⁻¹) * e⁻¹ = e * (t * h * t⁻¹) * e⁻¹ := by
      simpa [MulAut.conj_apply] using hxe
    have : a = h := by
      calc a = (e * t)⁻¹ * (e * (t * a * t⁻¹) * e⁻¹) * (e * t) := by group
        _ = (e * t)⁻¹ * (e * (t * h * t⁻¹) * e⁻¹) * (e * t) := by rw [hxe']
        _ = h := by group
    rwa [← this]


theorem uc22pw_exists_inverting {L A : Subgroup G} (hAL : A ≤ L) (hAodd : Odd (Nat.card A))
    (w : Bar2 L) (hw : w ^ 2 = 1)
    (hinv : ∀ a : ↥L, (a : G) ∈ A → w * QuotientGroup.mk a * w⁻¹ = (QuotientGroup.mk a)⁻¹) :
    ∃ r : ↥L, (∃ k : ℕ, orderOf (r : G) = 2 ^ k) ∧ QuotientGroup.mk r = w ∧
      ∀ a ∈ A, (r : G) * a * (r : G)⁻¹ = a⁻¹ := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI hNn : (CFSG.pCore 2 ↥L).Normal := CFSG.pCore_normal
  have hN2 : IsPGroup 2 (CFSG.pCore 2 ↥L) := CFSG.pCore_isPGroup
  obtain ⟨w₀, hw₀⟩ : ∃ w₀ : ↥L, (QuotientGroup.mk w₀ : Bar2 L) = w := QuotientGroup.mk_surjective w
  set N : Subgroup ↥L := CFSG.pCore 2 ↥L with hN
  set A' : Subgroup ↥L := A.subgroupOf L with hA'
  set A'' : Subgroup ↥L := A'.map (MulAut.conj w₀).toMonoidHom with hA''
  have hA'odd : Odd (Nat.card A') := by
    rw [hA', Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAL).toEquiv]
    exact hAodd
  have hA''odd : Odd (Nat.card A'') := by
    rw [hA'', Subgroup.card_map_of_injective (MulAut.conj w₀).injective]
    exact hA'odd
  have hd' : Disjoint N A' := uc22pw_disjoint_of_odd hN2 hA'odd
  have hd'' : Disjoint N A'' := uc22pw_disjoint_of_odd hN2 hA''odd
  have hkey : ∀ x ∈ A', w₀ * x * w₀⁻¹ * x ∈ N := by
    intro x hx
    have h1 := hinv x hx
    rw [← hw₀] at h1
    rw [hN, ← QuotientGroup.eq_one_iff]
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    rw [h1]
    exact inv_mul_cancel _
  have hsup : N ⊔ A'' = N ⊔ A' := by
    refine le_antisymm (sup_le le_sup_left ?_) (sup_le le_sup_left ?_)
    · rintro _ ⟨x, hx, rfl⟩
      have hy : w₀ * x * w₀⁻¹ * x ∈ N := hkey x hx
      have : w₀ * x * w₀⁻¹ = (w₀ * x * w₀⁻¹ * x) * x⁻¹ := by group
      show (MulAut.conj w₀) x ∈ N ⊔ A'
      rw [MulAut.conj_apply, this]
      exact Subgroup.mul_mem_sup hy (A'.inv_mem hx)
    · intro x hx
      have hy : w₀ * x⁻¹ * w₀⁻¹ * x⁻¹ ∈ N := hkey x⁻¹ (A'.inv_mem hx)
      have hyA : w₀ * x⁻¹ * w₀⁻¹ ∈ A'' := ⟨x⁻¹, A'.inv_mem hx, by simp [MulAut.conj_apply]⟩
      have : x = (w₀ * x⁻¹ * w₀⁻¹ * x⁻¹)⁻¹ * (w₀ * x⁻¹ * w₀⁻¹) := by group
      rw [this]
      exact Subgroup.mul_mem_sup (N.inv_mem hy) hyA
  obtain ⟨e, heN, hconj⟩ :=
    CFSG.GH74.BNPair.exists_conj_of_complements (p := 2) hN2
      (fun h => (Nat.not_even_iff_odd.2 hA'odd) (even_iff_two_dvd.2 h)) hd' hd'' hsup
  have heπ : (QuotientGroup.mk e : Bar2 L) = 1 := (QuotientGroup.eq_one_iff e).2 heN
  have hrw : (QuotientGroup.mk (e * w₀) : Bar2 L) = w := by
    rw [QuotientGroup.mk_mul, heπ, one_mul, hw₀]
  refine ⟨e * w₀, ?_, hrw, ?_⟩
  · have hsq : (e * w₀) ^ 2 ∈ N := by
      rw [hN, ← QuotientGroup.eq_one_iff]
      have : (QuotientGroup.mk ((e * w₀) ^ 2) : Bar2 L) = w ^ 2 := by
        rw [QuotientGroup.mk_pow, hrw]
      rw [this, hw]
    obtain ⟨k, hk⟩ := hN2 ⟨(e * w₀) ^ 2, hsq⟩
    have hk' : (e * w₀) ^ (2 * 2 ^ k) = 1 := by
      have := congrArg Subtype.val hk
      simpa [pow_mul] using this
    have hdvd : orderOf (e * w₀) ∣ 2 ^ (k + 1) := by
      rw [pow_succ']
      exact orderOf_dvd_of_pow_eq_one hk'
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
    exact ⟨j, by rw [Subgroup.orderOf_coe]; exact hj⟩
  · intro a ha
    set x : ↥L := ⟨a, hAL ha⟩ with hx
    have hxA : x ∈ A' := ha
    have hmem : (e * w₀) * x * (e * w₀)⁻¹ ∈ A' := by
      have h1 : w₀ * x * w₀⁻¹ ∈ A'' := ⟨x, hxA, by simp [MulAut.conj_apply]⟩
      have h2 : e * (w₀ * x * w₀⁻¹) * e⁻¹ ∈ A''.map (MulAut.conj e).toMonoidHom :=
        ⟨_, h1, by simp [MulAut.conj_apply]⟩
      rw [hconj] at h2
      simpa [mul_assoc] using h2
    have himg : (QuotientGroup.mk ((e * w₀) * x * (e * w₀)⁻¹) : Bar2 L) = (QuotientGroup.mk x)⁻¹ := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, hrw]
      exact hinv x ha
    have hprod_N : ((e * w₀) * x * (e * w₀)⁻¹) * x ∈ N := by
      rw [hN, ← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, himg]
      exact inv_mul_cancel _
    have hprod_A : ((e * w₀) * x * (e * w₀)⁻¹) * x ∈ A' := A'.mul_mem hmem hxA
    have h1 := Subgroup.disjoint_def.1 hd' hprod_N hprod_A
    have h2 : (e * w₀) * x * (e * w₀)⁻¹ = x⁻¹ := eq_inv_of_mul_eq_one_left h1
    have h3 := congrArg Subtype.val h2
    simpa using h3

theorem uc22pw_not_mem_M (D : Data G) (hB : ListBNonabelian) (h1930 : H1930 D) {L : Subgroup G}
    (hL : L ∈ calL D.T D.M) {r : ↥L}
    (hgen : normalizer ((uc22p20iSylowBar D L : Subgroup (Bar2 L)) : Set (Bar2 L)) ⊔
      Subgroup.zpowers (QuotientGroup.mk r : Bar2 L) = ⊤) : (r : G) ∉ D.M := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hrM
  set π : ↥L →* Bar2 L := QuotientGroup.mk' (CFSG.pCore 2 ↥L) with hπ
  set Mb : Subgroup (Bar2 L) := ((D.M ⊓ L).subgroupOf L).map π with hMb
  have hN : normalizer ((uc22p20iSylowBar D L : Subgroup (Bar2 L)) : Set (Bar2 L)) ≤ Mb := by
    intro y hy
    obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥L) y
    exact ⟨l, Subgroup.mem_subgroupOf.2 ⟨uc22p20i_borel_le_M D hB h1930 hL l hy, l.2⟩, rfl⟩
  have hz : Subgroup.zpowers (QuotientGroup.mk r : Bar2 L) ≤ Mb := by
    rw [Subgroup.zpowers_le]
    exact ⟨r, Subgroup.mem_subgroupOf.2 ⟨hrM, r.2⟩, rfl⟩
  have htop : Mb = ⊤ := top_le_iff.1 (hgen ▸ sup_le hN hz)
  apply uc22p20i_not_le_M D hL
  intro l hl
  have hmem : π ⟨l, hl⟩ ∈ Mb := by rw [htop]; trivial
  obtain ⟨m, hm, hml⟩ := hmem
  have hk : m⁻¹ * ⟨l, hl⟩ ∈ CFSG.pCore 2 ↥L := (QuotientGroup.eq (s := CFSG.pCore 2 ↥L)).1 hml
  have hkT : (((m⁻¹ * ⟨l, hl⟩ : ↥L)) : G) ∈ D.T :=
    (uc22p20i_pCoreOf_le D hL ⟨_, hk, rfl⟩).1
  have hmM : (m : G) ∈ D.M := (Subgroup.mem_subgroupOf.1 hm).1
  have : l = (m : G) * (((m⁻¹ * ⟨l, hl⟩ : ↥L)) : G) := by simp
  rw [this]
  exact D.M.mul_mem hmM (D.sylowM.le hkT)

end CFSG.LocalAnalysis.UniquenessCase.UC22
