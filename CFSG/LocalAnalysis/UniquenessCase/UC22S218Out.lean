module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S218CenL
import CFSG.LocalAnalysis.UniquenessCase.UC22S218GAbs
import CFSG.LocalAnalysis.UniquenessCase.UC6S846c

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem uc22s218_exists_lift_of_power_maps {L M : Subgroup G} (hLM : L ≤ M)
    [(L.subgroupOf M).Normal] (K : Subgroup ↥L) [K.Characteristic] {p r : ℕ} (hp : p.Prime)
    (hr : r.Prime) (hpr : p ≠ r) (hpK : ¬ p ∣ Nat.card K) (hrK : ¬ r ∣ Nat.card K)
    {Q : Subgroup G} (hQM : Q ≤ M) (hQ : IsElemAbelian p Q) {E₁ : Subgroup (↥L ⧸ K)}
    (hE₁ : IsElemAbelian r E₁) (hE₁c : Nat.card E₁ = r ^ 2)
    (hpow : ∀ (x : G) (hx : x ∈ Q), ∃ k : ℕ, ∀ e ∈ E₁,
      uc22s218_rhoK L K ⟨x, le_normalizer_of_normal_subgroupOf hLM (hQM hx)⟩ e = e ^ k) :
    ∃ E : Subgroup G, E ≤ L ∧ IsElemAbelian r E ∧ Nat.card E = r ^ 2 ∧
      ∀ x ∈ Q, ∃ k : ℕ, ∀ e ∈ E, x * e * x⁻¹ = e ^ k := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Fact r.Prime := ⟨hr⟩
  have : IsMulCommutative ↥E₁ := hE₁.1
  have hML : M ≤ normalizer (L : Set G) := le_normalizer_of_normal_subgroupOf hLM
  have hcop : Nat.Coprime (Nat.card E₁) (Nat.card K) := by
    rw [hE₁c]
    exact Nat.Coprime.pow_left 2 ((Nat.Prime.coprime_iff_not_dvd hr).2 hrK)
  obtain ⟨β, -, hβ⟩ := uc22s218_exists_lift_hom_of_coprime K ⊤
    (fun l => ⟨l, mem_top l, by simp⟩) E₁ hcop
  have hβinj : Function.Injective β := fun a b hab =>
    Subtype.ext ((hβ a).symm.trans ((congrArg (QuotientGroup.mk' K) hab).trans (hβ b)))
  let χ : ↥E₁ →* G := L.subtype.comp β
  have hχinj : Function.Injective χ := L.subtype_injective.comp hβinj
  have hE₀el : IsElemAbelian r χ.range := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun z hz => ?_⟩
    · obtain ⟨u, hu⟩ := MonoidHom.mem_range.1 a.2
      obtain ⟨v, hv⟩ := MonoidHom.mem_range.1 b.2
      apply Subtype.ext
      change (a : G) * b = b * a
      rw [← hu, ← hv, ← map_mul, ← map_mul, mul_comm' u v]
    · obtain ⟨u, rfl⟩ := MonoidHom.mem_range.1 hz
      rw [← map_pow]
      have : u ^ r = 1 := Subtype.ext (hE₁.2 _ u.2)
      rw [this, map_one]
  have hE₀c : Nat.card χ.range = r ^ 2 := by
    rw [← hE₁c]
    exact (Nat.card_congr (MonoidHom.ofInjective hχinj).toEquiv).symm
  have hE₀L : χ.range ≤ L := by
    rintro _ ⟨u, rfl⟩
    exact (β u).2
  let Ê : Subgroup G := (E₁.comap (QuotientGroup.mk' K)).map L.subtype
  have hÊL : Ê ≤ L := Subgroup.map_subtype_le _
  have hKÊ : K.map L.subtype ≤ Ê := by
    rintro _ ⟨k, hk, rfl⟩
    refine Subgroup.mem_map.2 ⟨k, ?_, rfl⟩
    have hk1 : QuotientGroup.mk' K k = 1 := (QuotientGroup.eq_one_iff k).2 hk
    rw [Subgroup.mem_comap, hk1]
    exact E₁.one_mem
  have hE₀Ê : χ.range ≤ Ê := by
    rintro _ ⟨u, rfl⟩
    refine Subgroup.mem_map.2 ⟨β u, ?_, rfl⟩
    rw [Subgroup.mem_comap, hβ u]
    exact u.2
  have hSr : ¬ r ∣ Nat.card (K.map L.subtype) := by
    rwa [Subgroup.card_map_of_injective L.subtype_injective]
  have hSp : ¬ p ∣ Nat.card (K.map L.subtype) := by
    rwa [Subgroup.card_map_of_injective L.subtype_injective]
  have hQS : Q ≤ normalizer ((K.map L.subtype : Subgroup G) : Set G) :=
    hQM.trans (hML.trans (uc22s218_normalizer_le_normalizer_map_subtype L K))
  have hE₀S : χ.range ≤ normalizer ((K.map L.subtype : Subgroup G) : Set G) :=
    hE₀L.trans (uc22s218_le_normalizer_map_subtype L K)
  obtain ⟨E, hEÊ, hEel, hEc, hEpow⟩ := exists_pow_conj_of_coprime (L := Ê)
    (S := K.map L.subtype) (E₀ := χ.range) (Q := Q) hp hr hpr hKÊ hSr hSp hE₀Ê hE₀S hE₀el hE₀c hQ
    hQS (fun x hx => by
      obtain ⟨k, hk⟩ := hpow x hx
      refine ⟨k, fun h hh _ => ?_⟩
      obtain ⟨l, hl, rfl⟩ := hh
      have hmk : QuotientGroup.mk' K
          (Subgroup.normalizerMonoidHom L ⟨x, hML (hQM hx)⟩ l * (l ^ k)⁻¹) = 1 := by
        have h1 : uc22s218_rhoK L K ⟨x, hML (hQM hx)⟩ (QuotientGroup.mk l) =
            (QuotientGroup.mk l) ^ k := hk _ hl
        rw [uc22s218_rhoK_mk] at h1
        rw [map_mul, map_inv, map_pow]
        exact mul_inv_eq_one.2 h1
      refine ⟨_, (QuotientGroup.eq_one_iff _).1 hmk, ?_⟩
      simp)
  exact ⟨E, hEÊ.trans hÊL, hEel, hEc, hEpow⟩

theorem uc22s218_exists_pair_of_outer {L M : Subgroup G} (hLM : L ≤ M) [(L.subgroupOf M).Normal]
    (K : Subgroup ↥L) [K.Characteristic] {p r : ℕ} (hp : p.Prime) (hr : r.Prime) (hpr : p ≠ r)
    (hpK : ¬ p ∣ Nat.card K) (hrK : ¬ r ∣ Nat.card K) (hrank : 4 ≤ CFSG.Open.pRank p M)
    {E₀ : Subgroup (↥L ⧸ K)} (hE₀ : IsElemAbelian r E₀) (hE₀c : Nat.card E₀ = r ^ 2)
    {y : ↥L ⧸ K} (hy : orderOf y = p) (hyE : ∀ e ∈ E₀, y * e = e * y)
    (hyZ : ∃ w : ↥L ⧸ K, w * y ≠ y * w)
    (hOuter : ∀ V : Subgroup (MulAut (↥L ⧸ K)), IsElemAbelian p V → Nat.card V = p ^ 4 →
      ∃ (E₁ : Subgroup (↥L ⧸ K)) (Q₁ : Subgroup (MulAut (↥L ⧸ K))), IsElemAbelian r E₁ ∧
        Nat.card E₁ = r ^ 2 ∧ Q₁ ≤ V ∧ IsElemAbelian p Q₁ ∧ Nat.card Q₁ = p ^ 2 ∧
        ∀ α ∈ Q₁, ∃ k : ℕ, ∀ e ∈ E₁, α e = e ^ k) :
    ∃ E Q : Subgroup G, E ≤ L ∧ IsElemAbelian r E ∧ Nat.card E = r ^ 2 ∧ Q ≤ M ∧
      IsElemAbelian p Q ∧ Nat.card Q = p ^ 2 ∧
      ∀ x ∈ Q, ∃ k : ℕ, ∀ e ∈ E, x * e * x⁻¹ = e ^ k := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hML : M ≤ normalizer (L : Set G) := le_normalizer_of_normal_subgroupOf hLM
  obtain ⟨A, hAM, hAel, hAc⟩ := UC6S846.exists_elemAbelian_card_of_le_pRank hp hrank
  let ρA : ↥A →* MulAut (↥L ⧸ K) := (uc22s218_rhoK L K).comp (Subgroup.inclusion (hAM.trans hML))
  have : IsMulCommutative ↥A := hAel.1
  by_cases hker : ∃ a : ↥A, a ≠ 1 ∧ ρA a = 1
  · obtain ⟨a, ha1, hρa⟩ := hker
    exact uc22s218_exists_pair_of_kernel_elem hLM K hp hr hpr hpK hrK (hAM a.2)
      (fun h => ha1 (Subtype.ext h)) (hAel.2 _ a.2) hρa hE₀ hE₀c hy hyE hyZ
  · have hinj : Function.Injective ρA := (injective_iff_map_eq_one ρA).2 fun a ha =>
      by_contra fun h => hker ⟨a, h, ha⟩
    have hVel : IsElemAbelian p ρA.range := by
      refine ⟨⟨⟨fun a b => ?_⟩⟩, fun z hz => ?_⟩
      · obtain ⟨u, hu⟩ := MonoidHom.mem_range.1 a.2
        obtain ⟨v, hv⟩ := MonoidHom.mem_range.1 b.2
        apply Subtype.ext
        change (a : MulAut (↥L ⧸ K)) * b = b * a
        rw [← hu, ← hv, ← map_mul, ← map_mul, mul_comm' u v]
      · obtain ⟨u, rfl⟩ := MonoidHom.mem_range.1 hz
        rw [← map_pow]
        have : u ^ p = 1 := Subtype.ext (hAel.2 _ u.2)
        rw [this, map_one]
    have hVc : Nat.card ρA.range = p ^ 4 := by
      rw [← hAc]
      exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
    obtain ⟨E₁, Q₁, hE₁, hE₁c, hQ₁V, hQ₁, hQ₁c, hpow⟩ := hOuter _ hVel hVc
    let Q : Subgroup G := (Q₁.comap ρA).map A.subtype
    have hQA : Q ≤ A := Subgroup.map_subtype_le _
    have hQc : Nat.card Q = p ^ 2 := by
      rw [Subgroup.card_map_of_injective A.subtype_injective, ← hQ₁c,
        ← Subgroup.card_map_of_injective hinj, Subgroup.map_comap_eq_self hQ₁V]
    obtain ⟨E, hEL, hEel, hEc, hEpow⟩ := uc22s218_exists_lift_of_power_maps hLM K hp hr hpr hpK hrK
      (hQA.trans hAM) (CFSG.Open.IsElemAbelian.mono hAel hQA) hE₁ hE₁c (fun x hx => by
        obtain ⟨a, ha, rfl⟩ := hx
        exact hpow (ρA a) ha)
    exact ⟨E, Q, hEL, hEel, hEc, hQA.trans hAM, CFSG.Open.IsElemAbelian.mono hAel hQA, hQc, hEpow⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22
