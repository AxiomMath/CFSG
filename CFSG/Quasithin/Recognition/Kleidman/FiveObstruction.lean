module

public import CFSG.Quasithin.Recognition.J2RecLocal
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23P4BlkB

public section

namespace CFSG.Quasithin.Kleidman

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin

open Equiv in
theorem perm_five_eq_one_of_commute : ∀ τ : Perm (Fin 5), τ ≠ 1 → (τ ^ 3 = 1 ∨ τ ^ 5 = 1) →
    ∀ σ : Perm (Fin 5), σ * σ = 1 → Perm.sign σ = 1 → σ * τ = τ * σ → σ = 1 := by
  decide +kernel

theorem isConj_of_involutionClassCount_eq_one {G : Type} [Group G] {z t : G} (hz2 : z * z = 1)
    (hz1 : z ≠ 1) (hone : involutionClassCount G = 1) (ht2 : t * t = 1) (ht1 : t ≠ 1) :
    IsConj z t := by
  obtain ⟨a, ha⟩ := Set.ncard_eq_one.mp hone
  have hzmem : ConjClasses.mk z ∈ {c : ConjClasses G | ∃ x : G, x ^ 2 = 1 ∧ x ≠ 1 ∧
      ConjClasses.mk x = c} := ⟨z, by rw [pow_two]; exact hz2, hz1, rfl⟩
  have htmem : ConjClasses.mk t ∈ {c : ConjClasses G | ∃ x : G, x ^ 2 = 1 ∧ x ≠ 1 ∧
      ConjClasses.mk x = c} := ⟨t, by rw [pow_two]; exact ht2, ht1, rfl⟩
  rw [ha] at hzmem htmem
  exact ConjClasses.mk_eq_mk_iff_isConj.mp ((Set.mem_singleton_iff.mp hzmem).trans
    (Set.mem_singleton_iff.mp htmem).symm)

namespace IsTypeH2

variable {G : Type} [Group G] [Finite G] {z : G}

omit [Finite G] in
theorem mem_pCoreOf_iff (x : ↥(Subgroup.centralizer ({z} : Set G))) :
    (x : G) ∈ pCoreOf 2 (Subgroup.centralizer ({z} : Set G)) ↔
      x ∈ CFSG.Open.pCore 2 ↥(Subgroup.centralizer ({z} : Set G)) := by
  constructor
  · rintro ⟨y, hy, hyx⟩
    have : y = x := Subtype.ext hyx
    rwa [← this]
  · intro hx
    exact ⟨x, hx, rfl⟩

omit [Finite G] in
theorem conj_mem_pCoreOf {x q : G} (hx : x ∈ Subgroup.centralizer ({z} : Set G))
    (hq : q ∈ pCoreOf 2 (Subgroup.centralizer ({z} : Set G))) :
    x * q * x⁻¹ ∈ pCoreOf 2 (Subgroup.centralizer ({z} : Set G)) := by
  set H := Subgroup.centralizer ({z} : Set G) with hH
  have hqH : q ∈ H := pCoreOf_le 2 H hq
  have hq' := (mem_pCoreOf_iff (z := z) ⟨q, hqH⟩).mp hq
  have h := (CFSG.LieType.BorelTits.pCore_normal (G := ↥H) 2).conj_mem _ hq' ⟨x, hx⟩
  exact (mem_pCoreOf_iff (z := z) (⟨x, hx⟩ * ⟨q, hqH⟩ * ⟨x, hx⟩⁻¹)).mpr h

omit [Finite G] in
theorem mem_pCoreOf_of_commute (h : IsTypeH2 G z) {v f : G}
    (hv : v ∈ Subgroup.centralizer ({z} : Set G)) (hf : f ∈ Subgroup.centralizer ({z} : Set G))
    (hv2 : v * v = 1) (hfQ : f ∉ pCoreOf 2 (Subgroup.centralizer ({z} : Set G)))
    (hfo : f ^ 3 = 1 ∨ f ^ 5 = 1) (hvf : v * f = f * v) :
    v ∈ pCoreOf 2 (Subgroup.centralizer ({z} : Set G)) := by
  set H := Subgroup.centralizer ({z} : Set G) with hH
  obtain ⟨φ⟩ := h.quot
  have := CFSG.LieType.BorelTits.pCore_normal (G := ↥H) 2
  set π : ↥H →* OTwoQuot H := QuotientGroup.mk' _ with hπ
  set ψ : ↥H →* Equiv.Perm (Fin 5) := (alternatingGroup (Fin 5)).subtype.comp
    (φ.toMonoidHom.comp π) with hψ
  have hker : ∀ x : ↥H, ψ x = 1 → (x : G) ∈ pCoreOf 2 H := by
    intro x hx
    have h1 : φ (π x) = 1 := Subtype.ext hx
    have h2 : π x = 1 := φ.injective (h1.trans (map_one φ).symm)
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h2
    exact (mem_pCoreOf_iff x).mpr h2
  have hsign : ∀ x : ↥H, Equiv.Perm.sign (ψ x) = 1 := fun x => (φ (π x)).2
  set V : ↥H := ⟨v, hv⟩
  set F : ↥H := ⟨f, hf⟩
  have hV2 : ψ V * ψ V = 1 := by
    rw [← map_mul, show V * V = 1 from Subtype.ext hv2, map_one]
  have hF1 : ψ F ≠ 1 := fun h1 => hfQ (hker F h1)
  have hFo : ψ F ^ 3 = 1 ∨ ψ F ^ 5 = 1 := by
    rcases hfo with h3 | h5
    · left
      rw [← map_pow, show F ^ 3 = 1 from Subtype.ext (by simpa using h3), map_one]
    · right
      rw [← map_pow, show F ^ 5 = 1 from Subtype.ext (by simpa using h5), map_one]
  have hVF : ψ V * ψ F = ψ F * ψ V := by
    rw [← map_mul, ← map_mul, show V * F = F * V from Subtype.ext hvf]
  exact hker V (perm_five_eq_one_of_commute _ hF1 hFo _ hV2 (hsign V) hVF)

theorem eq_one_or_eq_of_orderOf_five (h : IsTypeH2 G z) {f : G}
    (hf : f ∈ Subgroup.centralizer ({z} : Set G)) (hf5 : orderOf f = 5) {q : G}
    (hq : q ∈ pCoreOf 2 (Subgroup.centralizer ({z} : Set G))) (hqf : q * f = f * q) :
    q = 1 ∨ q = z := by
  classical
  set H := Subgroup.centralizer ({z} : Set G) with hH
  set Q := pCoreOf 2 H with hQ
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQc : Nat.card Q = 32 := h.card_pCoreOf
  have hmod := CFSG.Quasithin.H23P4.card_modEq_card_fixed (X := Q) (y := f)
    (fun x hx => conj_mem_pCoreOf hf hx) (k := 1) (by rw [pow_one, ← hf5]; exact pow_orderOf_eq_one f)
  set F := Q ⊓ Subgroup.centralizer ({f} : Set G) with hF
  have hdvd : Nat.card F ∣ 32 := hQc ▸ Subgroup.card_dvd_of_le inf_le_left
  rw [hQc] at hmod
  have hF2 : Nat.card F = 2 := by
    have hcases : Nat.card F = 1 ∨ Nat.card F = 2 ∨ Nat.card F = 4 ∨ Nat.card F = 8 ∨
        Nat.card F = 16 ∨ Nat.card F = 32 := by
      have h32 : (32 : ℕ) = 2 ^ 5 := by norm_num
      rw [h32] at hdvd
      obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
      interval_cases k <;> simp_all
    rcases hcases with h1 | h1 | h1 | h1 | h1 | h1
    · rw [h1] at hmod; exact absurd hmod (by decide)
    · exact h1
    · rw [h1] at hmod; exact absurd hmod (by decide)
    · rw [h1] at hmod; exact absurd hmod (by decide)
    · rw [h1] at hmod; exact absurd hmod (by decide)
    · exfalso
      have hFQ : F = Q := by
        apply Subgroup.eq_of_le_of_card_ge inf_le_left
        rw [h1, hQc]
      have hfQ : f ∈ Q := by
        apply h.charTwo
        refine ⟨hf, Subgroup.mem_centralizer_iff.mpr fun x hx => ?_⟩
        have hxF : x ∈ F := hFQ ▸ hx
        exact (Subgroup.mem_centralizer_singleton_iff.mp hxF.2)
      obtain ⟨n, hn⟩ := (IsPGroup.iff_orderOf.mp (pCoreOf_isPGroup 2 H)) ⟨f, hfQ⟩
      rw [Subgroup.orderOf_mk, hf5] at hn
      have : (2 : ℕ) ∣ 5 := by
        rcases n with _ | n
        · simp at hn
        · exact hn ▸ dvd_pow_self 2 (Nat.succ_ne_zero n)
      omega
  have hzQ : z ∈ Q := h.z_mem_pCoreOf
  have hzF : z ∈ F := ⟨hzQ, Subgroup.mem_centralizer_singleton_iff.mpr
    (Subgroup.mem_centralizer_singleton_iff.mp hf).symm⟩
  have hqF : q ∈ F := ⟨hq, Subgroup.mem_centralizer_singleton_iff.mpr hqf⟩
  by_contra hne
  push Not at hne
  have hsub : (({1, z, q} : Finset G) : Set G) ⊆ (F : Set G) := by
    intro x hx
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact one_mem F
    · exact hzF
    · exact hqF
  have h3 : ({1, z, q} : Finset G).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_pair (Ne.symm hne.2)]
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨Ne.symm h.ne_one, Ne.symm hne.1⟩
  have : Finite (F : Set G) := inferInstanceAs (Finite F)
  have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [Set.ncard_coe_finset, h3, ← Nat.card_coe_set_eq, SetLike.coe_sort_coe, hF2] at hle
  omega

theorem eq_of_commute_orderOf_five (h : IsTypeH2 G z) {f v : G}
    (hf : f ∈ Subgroup.centralizer ({z} : Set G)) (hf5 : orderOf f = 5)
    (hv : v ∈ Subgroup.centralizer ({z} : Set G)) (hv2 : v * v = 1) (hv1 : v ≠ 1)
    (hvf : v * f = f * v) : v = z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hfQ : f ∉ pCoreOf 2 (Subgroup.centralizer ({z} : Set G)) := by
    intro hfQ
    obtain ⟨n, hn⟩ := (IsPGroup.iff_orderOf.mp
      (pCoreOf_isPGroup 2 (Subgroup.centralizer ({z} : Set G)))) ⟨f, hfQ⟩
    rw [Subgroup.orderOf_mk, hf5] at hn
    have : (2 : ℕ) ∣ 5 := by
      rcases n with _ | n
      · simp at hn
      · exact hn ▸ dvd_pow_self 2 (Nat.succ_ne_zero n)
    omega
  have hvQ := mem_pCoreOf_of_commute h hv hf hv2 hfQ
    (Or.inr (by rw [← hf5]; exact pow_orderOf_eq_one f)) hvf
  rcases eq_one_or_eq_of_orderOf_five h hf hf5 hvQ hvf with h1 | h1
  · exact absurd h1 hv1
  · exact h1

theorem false_of_klein_five (h : IsTypeH2 G z) (hone : involutionClassCount G = 1)
    {τ τ' f : G} (hτ2 : τ * τ = 1) (hτ1 : τ ≠ 1) (hτ'2 : τ' * τ' = 1) (hτ'1 : τ' ≠ 1)
    (hne : τ ≠ τ') (hcomm : τ * τ' = τ' * τ) (hf5 : orderOf f = 5) (hfτ : f * τ = τ * f)
    (hfτ' : f * τ' = τ' * f) : False := by
  have hz2 : z * z = 1 := by rw [← pow_two]; exact h.sq
  obtain ⟨g, hg⟩ := isConj_iff.mp (isConj_of_involutionClassCount_eq_one hz2 h.ne_one hone hτ2 hτ1)
  have hmem : ∀ {x : G}, x * τ = τ * x →
      g⁻¹ * x * g ∈ Subgroup.centralizer ({z} : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hz : z = g⁻¹ * τ * g := by rw [← hg]; group
    rw [hz]
    calc g⁻¹ * x * g * (g⁻¹ * τ * g) = g⁻¹ * (x * τ) * g := by group
      _ = g⁻¹ * (τ * x) * g := by rw [hx]
      _ = g⁻¹ * τ * g * (g⁻¹ * x * g) := by group
  have hf' := hmem hfτ
  have hv' := hmem hcomm.symm
  have hf'5 : orderOf (g⁻¹ * f * g) = 5 := by
    have h1 := MulEquiv.orderOf_eq (MulAut.conj g⁻¹) f
    rw [MulAut.conj_apply, inv_inv] at h1
    rw [h1, hf5]
  have hv'2 : g⁻¹ * τ' * g * (g⁻¹ * τ' * g) = 1 := by
    calc g⁻¹ * τ' * g * (g⁻¹ * τ' * g) = g⁻¹ * (τ' * τ') * g := by group
      _ = 1 := by rw [hτ'2]; group
  have hv'1 : g⁻¹ * τ' * g ≠ 1 := by
    intro h1
    apply hτ'1
    calc τ' = g * (g⁻¹ * τ' * g) * g⁻¹ := by group
      _ = 1 := by rw [h1]; group
  have hvf : g⁻¹ * τ' * g * (g⁻¹ * f * g) = g⁻¹ * f * g * (g⁻¹ * τ' * g) := by
    calc g⁻¹ * τ' * g * (g⁻¹ * f * g) = g⁻¹ * (τ' * f) * g := by group
      _ = g⁻¹ * (f * τ') * g := by rw [hfτ']
      _ = g⁻¹ * f * g * (g⁻¹ * τ' * g) := by group
  have := eq_of_commute_orderOf_five h hf' hf'5 hv' hv'2 hv'1 hvf
  apply hne
  calc τ = g * z * g⁻¹ := hg.symm
    _ = g * (g⁻¹ * τ' * g) * g⁻¹ := by rw [this]
    _ = τ' := by group

end IsTypeH2

end CFSG.Quasithin.Kleidman
