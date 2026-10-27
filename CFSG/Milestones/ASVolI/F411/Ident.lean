module

public import CFSG.Milestones.ASVolI.F411.Red

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.ASVolI.ChF

section Generic

variable {E : Type} [Group E]

@[expose] def burnsideF411_BorelTitsIn (p : ℕ) (Gp : Subgroup E) : Prop :=
  ∀ R : Subgroup E, R ≤ Gp → R ≠ ⊥ → IsPGroup p R →
    ∃ S' : Subgroup E, IsSylowOf p S' Gp ∧ ∃ P : Subgroup E, P ≤ Gp ∧ P ≠ Gp ∧
      Gp ⊓ Subgroup.normalizer (R : Set E) ≤ P ∧ Gp ⊓ Subgroup.normalizer (S' : Set E) ≤ P

@[expose] def burnsideF411_RankOne (p : ℕ) (Gp B P : Subgroup E) : Prop :=
  ∀ S : Subgroup E, IsSylowOf p S Gp → S ≤ B → ∀ Y : Subgroup E, S ≤ Y → Y ≤ P → ¬ Y ≤ B →
    oPPrime p P ≤ Y

@[expose] def burnsideF411_CentSylow (p : ℕ) (Gp : Subgroup E) : Prop :=
  ∀ S : Subgroup E, IsSylowOf p S Gp → ∀ W : Subgroup E, IsPGroup p W →
    W ≤ Subgroup.centralizer (S : Set E) → W ≤ Gp

theorem burnsideF411_eq_of_isSylowOf [Finite E] {p : ℕ} [Fact p.Prime] {S Q H : Subgroup E}
    (hS : IsSylowOf p S H) (hSQ : S ≤ Q) (hQH : Q ≤ H) (hQ : IsPGroup p Q) : Q = S := by
  obtain ⟨-, -, hSi⟩ := hS
  have hmul := Subgroup.relIndex_mul_relIndex S Q H hSQ hQH
  have hQ' : IsPGroup p ↥Q := hQ
  obtain ⟨n, hn⟩ := hQ'.index (S.subgroupOf Q)
  have hrel : S.relIndex Q = p ^ n := hn
  have hn0 : n = 0 := by
    by_contra h
    apply hSi
    rw [← hmul, hrel]
    exact Dvd.dvd.mul_right (dvd_pow_self p h) _
  rw [hn0, pow_zero] at hrel
  exact le_antisymm (Subgroup.relIndex_eq_one.mp hrel) hSQ

theorem burnsideF411_isSylowOf_of_le {p : ℕ} {S P H : Subgroup E} (hS : IsSylowOf p S H)
    (hSP : S ≤ P) (hPH : P ≤ H) : IsSylowOf p S P := by
  obtain ⟨-, hSp, hSi⟩ := hS
  refine ⟨hSP, hSp, fun h => hSi ?_⟩
  rw [← Subgroup.relIndex_mul_relIndex S P H hSP hPH]
  exact Dvd.dvd.mul_right h _

theorem burnsideF411_sylow_conj [Finite E] {p : ℕ} [Fact p.Prime] {S S' P : Subgroup E}
    (hS : IsSylowOf p S P) (hS' : IsSylowOf p S' P) :
    ∃ k ∈ P, ∀ x, x ∈ S ↔ ∃ s ∈ S', k * s * k⁻¹ = x := by
  classical
  obtain ⟨hSP, hSp, hSi⟩ := hS
  obtain ⟨hS'P, hS'p, hS'i⟩ := hS'
  let A : Subgroup ↥P := S.subgroupOf P
  let A' : Subgroup ↥P := S'.subgroupOf P
  have hAp : IsPGroup p A := hSp.of_equiv (Subgroup.subgroupOfEquivOfLe hSP).symm
  have hA'p : IsPGroup p A' := hS'p.of_equiv (Subgroup.subgroupOfEquivOfLe hS'P).symm
  have hAi : ¬ p ∣ A.index := hSi
  have hA'i : ¬ p ∣ A'.index := hS'i
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq ↥P (hA'p.toSylow hA'i) (hAp.toSylow hAi)
  refine ⟨k, k.2, fun x => ?_⟩
  have hAeq : A = ((k • hA'p.toSylow hA'i : Sylow p ↥P) : Subgroup ↥P) := by
    rw [hk, IsPGroup.toSylow_coe]
  constructor
  · intro hx
    have hxA : (⟨x, hSP hx⟩ : ↥P) ∈ A := hx
    rw [hAeq, Sylow.coe_subgroup_smul, IsPGroup.toSylow_coe,
      Subgroup.mem_smul_pointwise_iff_exists] at hxA
    obtain ⟨s, hs, hseq⟩ := hxA
    refine ⟨s, hs, ?_⟩
    have := congrArg Subtype.val hseq
    simpa [MulAut.smul_def, MulAut.conj_apply] using this
  · rintro ⟨s, hs, rfl⟩
    have hsA' : (⟨s, hS'P hs⟩ : ↥P) ∈ A' := hs
    have hmem : k * ⟨s, hS'P hs⟩ * k⁻¹ ∈ A := by
      rw [hAeq, Sylow.coe_subgroup_smul, IsPGroup.toSylow_coe,
        Subgroup.mem_smul_pointwise_iff_exists]
      exact ⟨_, hsA', by simp [MulAut.smul_def, MulAut.conj_apply]⟩
    exact hmem

theorem burnsideF411_isSylowOf_conj [Finite E] {p : ℕ} {S H : Subgroup E} (hS : IsSylowOf p S H)
    {x : E} (hx : x ∈ H) : IsSylowOf p (S.map (MulAut.conj x).toMonoidHom) H := by
  obtain ⟨hSH, hSp, hSi⟩ := hS
  have hle : S.map (MulAut.conj x).toMonoidHom ≤ H := by
    rintro _ ⟨s, hs, rfl⟩
    exact H.mul_mem (H.mul_mem hx (hSH hs)) (H.inv_mem hx)
  refine ⟨hle, hSp.map _, fun h => hSi ?_⟩
  have hcard : Nat.card (S.map (MulAut.conj x).toMonoidHom) = Nat.card S :=
    Subgroup.card_map_of_injective (MulAut.conj x).injective
  have h1 := Subgroup.relIndex_mul_card S H
  have h2 := Subgroup.relIndex_mul_card (S.map (MulAut.conj x).toMonoidHom) H
  rw [inf_of_le_left hSH] at h1
  rw [inf_of_le_left hle, hcard] at h2
  have : (S.map (MulAut.conj x).toMonoidHom).relIndex H = S.relIndex H :=
    Nat.eq_of_mul_eq_mul_right Nat.card_pos (h2.trans h1.symm)
  rwa [← this]

theorem burnsideF411_le_of_normal [Finite E] {p : ℕ} [Fact p.Prime] {S Q P H : Subgroup E}
    (hS : IsSylowOf p S H) (hSQ : S ≤ Q) (hQP : Q ≤ P) (hPH : P ≤ H)
    (hQn : H ≤ Subgroup.normalizer (Q : Set E))
    (hNP : H ⊓ Subgroup.normalizer (S : Set E) ≤ P) : H ≤ P := by
  intro x hx
  have hSx := burnsideF411_isSylowOf_conj hS hx
  have hSxQ : S.map (MulAut.conj x).toMonoidHom ≤ Q := by
    rintro _ ⟨s, hs, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp (hQn hx) s).mp (hSQ hs)
  have hQH : Q ≤ H := hQP.trans hPH
  obtain ⟨q, hq, hqS⟩ := burnsideF411_sylow_conj (burnsideF411_isSylowOf_of_le hSx hSxQ hQH)
    (burnsideF411_isSylowOf_of_le hS hSQ hQH)
  have hn : q⁻¹ * x ∈ H ⊓ Subgroup.normalizer (S : Set E) := by
    refine ⟨H.mul_mem (H.inv_mem (hQH hq)) hx, ?_⟩
    show q⁻¹ * x ∈ Subgroup.normalizer (S : Set E)
    rw [Subgroup.mem_normalizer_iff]
    intro s
    constructor
    · intro hs
      have h1 : x * s * x⁻¹ ∈ S.map (MulAut.conj x).toMonoidHom := ⟨s, hs, rfl⟩
      obtain ⟨t, ht, hteq⟩ := (hqS _).mp h1
      have : q⁻¹ * x * s * (q⁻¹ * x)⁻¹ = t := by
        calc q⁻¹ * x * s * (q⁻¹ * x)⁻¹ = q⁻¹ * (x * s * x⁻¹) * q := by group
          _ = q⁻¹ * (q * t * q⁻¹) * q := by rw [hteq]
          _ = t := by group
      rw [this]
      exact ht
    · intro hs
      have h1 : q * (q⁻¹ * x * s * (q⁻¹ * x)⁻¹) * q⁻¹ ∈ S.map (MulAut.conj x).toMonoidHom :=
        (hqS _).mpr ⟨_, hs, rfl⟩
      obtain ⟨t, ht, hteq⟩ := h1
      have : s = t := by
        have h2 : x * t * x⁻¹ = x * s * x⁻¹ := by
          rw [show (MulAut.conj x).toMonoidHom t = x * t * x⁻¹ from rfl] at hteq
          rw [hteq]
          group
        simpa using h2.symm
      rw [this]
      exact ht
  have := P.mul_mem (hQP hq) (hNP hn)
  simpa using this

theorem burnsideF411_oPPrime_le (p : ℕ) (P : Subgroup E) : oPPrime p P ≤ P := by
  rw [oPPrime, Subgroup.closure_le]
  exact fun x hx => hx.1

theorem burnsideF411_oPPrime_mono (p : ℕ) {P Q : Subgroup E} (h : P ≤ Q) :
    oPPrime p P ≤ oPPrime p Q :=
  Subgroup.closure_mono fun x hx => ⟨h hx.1, hx.2⟩

theorem burnsideF411_le_oPPrime {p : ℕ} [Fact p.Prime] {S P : Subgroup E} (hSP : S ≤ P)
    (hS : IsPGroup p S) : S ≤ oPPrime p P := by
  intro s hs
  apply Subgroup.subset_closure
  refine ⟨hSP hs, ?_⟩
  obtain ⟨k, hk⟩ := hS ⟨s, hs⟩
  have hk' : s ^ (p ^ k) = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow (Fact.out : p.Prime)).mp (orderOf_dvd_of_pow_eq_one hk')
  exact ⟨j, hj⟩

theorem burnsideF411_normalizer_le_normalizer_oPPrime (p : ℕ) (P : Subgroup E) :
    Subgroup.normalizer (P : Set E) ≤ Subgroup.normalizer (oPPrime p P : Set E) := by
  have key : ∀ g ∈ Subgroup.normalizer (P : Set E), ∀ x ∈ oPPrime p P, g * x * g⁻¹ ∈ oPPrime p P := by
    intro g hg x hx
    have hle : oPPrime p P ≤ (oPPrime p P).comap (MulAut.conj g).toMonoidHom := by
      rw [oPPrime, Subgroup.closure_le]
      rintro y ⟨hyP, k, hk⟩
      apply Subgroup.subset_closure
      refine ⟨(Subgroup.mem_normalizer_iff.mp hg y).mp hyP, k, ?_⟩
      show orderOf ((MulAut.conj g) y) = p ^ k
      rw [MulEquiv.orderOf_eq]
      exact hk
    exact hle hx
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨key g hg x, fun hx => ?_⟩
  have := key g⁻¹ (inv_mem hg) _ hx
  simpa [mul_assoc] using this

theorem burnsideF411_oPPrime_eq (p : ℕ) {P Y : Subgroup E} (h1 : oPPrime p P ≤ Y) (h2 : Y ≤ P) :
    oPPrime p Y = oPPrime p P := by
  refine le_antisymm (burnsideF411_oPPrime_mono p h2) ?_
  rw [oPPrime, Subgroup.closure_le]
  rintro x ⟨hxP, k, hk⟩
  apply Subgroup.subset_closure
  exact ⟨h1 (Subgroup.subset_closure ⟨hxP, k, hk⟩), k, hk⟩

theorem burnsideF411_le_normalizer {K S : Subgroup E}
    (h : ∀ y ∈ K, ∀ s ∈ S, y * s * y⁻¹ ∈ S) : K ≤ Subgroup.normalizer (S : Set E) := by
  intro y hy
  rw [Subgroup.mem_normalizer_iff]
  intro s
  refine ⟨h y hy s, fun hs => ?_⟩
  have := h y⁻¹ (K.inv_mem hy) _ hs
  simpa [mul_assoc] using this

theorem burnsideF411_le_normalizer_inf {Gp : Subgroup E} (hN : Gp.Normal) (X : Subgroup E) :
    X ≤ Subgroup.normalizer ((X ⊓ Gp : Subgroup E) : Set E) :=
  burnsideF411_le_normalizer fun y hy s hs =>
    ⟨X.mul_mem (X.mul_mem hy hs.1) (X.inv_mem hy), hN.conj_mem s hs.2 y⟩

theorem burnsideF411_le_normalizer_pCoreOf_inf (p : ℕ) {Gp : Subgroup E} (hN : Gp.Normal)
    (M : Subgroup E) : M ≤ Subgroup.normalizer (pCoreOf p (Gp ⊓ M) : Set E) := by
  have h1 : M ≤ Subgroup.normalizer ((Gp ⊓ M : Subgroup E) : Set E) := by
    rw [inf_comm]
    exact burnsideF411_le_normalizer_inf hN M
  exact h1.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf p (Gp ⊓ M))

theorem burnsideF411_normalizer_le {Gp M₁₂ M Q : Subgroup E} (hle : M₁₂ ≤ M)
    (hsplit : ∀ e : E, ∃ n ∈ Gp, ∃ h ∈ M₁₂, e = n * h)
    (hMQ : M ≤ Subgroup.normalizer (Q : Set E))
    (hGQ : Gp ⊓ Subgroup.normalizer (Q : Set E) ≤ M) :
    Subgroup.normalizer (Q : Set E) ≤ M := by
  intro x hx
  obtain ⟨n, hn, h, hh, rfl⟩ := hsplit x
  have hhN : h ∈ Subgroup.normalizer (Q : Set E) := hMQ (hle hh)
  have hnN : n ∈ Subgroup.normalizer (Q : Set E) := by
    have := (Subgroup.normalizer (Q : Set E)).mul_mem hx (inv_mem hhN)
    simpa using this
  exact M.mul_mem (hGQ ⟨hn, hnN⟩) (hle hh)

theorem burnsideF411_sup_eq_top {Gp M₁₂ M : Subgroup E} (hle : M₁₂ ≤ M)
    (hsplit : ∀ e : E, ∃ n ∈ Gp, ∃ h ∈ M₁₂, e = n * h) : Gp ⊔ M = ⊤ := by
  rw [eq_top_iff]
  intro e _
  obtain ⟨n, hn, h, hh, rfl⟩ := hsplit e
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hn) (Subgroup.mem_sup_right (hle hh))

theorem burnsideF411_pCoreOf_ne_bot_of_equiv (p : ℕ) {X M : Subgroup E} (χ : ↥X ≃* ↥M)
    (hM : pCoreOf p M ≠ ⊥) : pCoreOf p X ≠ ⊥ := by
  intro hX
  apply hM
  have h1 : CFSG.pCore p ↥X = ⊥ := by
    apply Subgroup.map_injective X.subtype_injective
    rw [Subgroup.map_bot]
    exact hX
  have h2 := CFSG.LieType.BorelTits.map_pCore_mulEquiv p χ
  rw [h1, Subgroup.map_bot] at h2
  show (CFSG.pCore p ↥M).map M.subtype = ⊥
  rw [← h2, Subgroup.map_bot]

theorem burnsideF411_card_inf_ge [Finite E] {Gp X M : Subgroup E} (hN : Gp.Normal)
    (hGM : Gp ⊔ M = ⊤) (hcard : Nat.card X = Nat.card M) :
    Nat.card (Gp ⊓ M : Subgroup E) ≤ Nat.card (Gp ⊓ X : Subgroup E) := by
  have h1 := Subgroup.relIndex_mul_card Gp X
  have h2 := Subgroup.relIndex_mul_card Gp M
  have hrelM : Gp.relIndex M = Gp.index := by
    rw [← Subgroup.relIndex_sup_left, hGM, Subgroup.relIndex_top_right]
  have hrelX : Gp.relIndex X ≤ Gp.index :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
      (Subgroup.relIndex_dvd_index_of_normal Gp X)
  rw [hrelM] at h2
  have hpos : 0 < Gp.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have : Gp.index * Nat.card (Gp ⊓ M : Subgroup E) ≤ Gp.index * Nat.card (Gp ⊓ X : Subgroup E) := by
    rw [h2, ← hcard, ← h1]
    exact Nat.mul_le_mul_right _ hrelX
  exact Nat.le_of_mul_le_mul_left this hpos

theorem burnsideF411_conj_mem_normalizer {S S' : Subgroup E} {k n : E}
    (hk : ∀ x, x ∈ S ↔ ∃ s ∈ S', k * s * k⁻¹ = x) (hn : n ∈ Subgroup.normalizer (S : Set E)) :
    k⁻¹ * n * k ∈ Subgroup.normalizer (S' : Set E) := by
  rw [Subgroup.mem_normalizer_iff]
  intro s
  constructor
  · intro hs
    have h1 : k * s * k⁻¹ ∈ S := (hk _).mpr ⟨s, hs, rfl⟩
    have h2 : n * (k * s * k⁻¹) * n⁻¹ ∈ S := (Subgroup.mem_normalizer_iff.mp hn _).mp h1
    obtain ⟨t, ht, hteq⟩ := (hk _).mp h2
    have : k⁻¹ * n * k * s * (k⁻¹ * n * k)⁻¹ = t := by
      calc k⁻¹ * n * k * s * (k⁻¹ * n * k)⁻¹ = k⁻¹ * (n * (k * s * k⁻¹) * n⁻¹) * k := by group
        _ = k⁻¹ * (k * t * k⁻¹) * k := by rw [hteq]
        _ = t := by group
    rw [this]
    exact ht
  · intro hs
    have h1 : k * (k⁻¹ * n * k * s * (k⁻¹ * n * k)⁻¹) * k⁻¹ ∈ S := (hk _).mpr ⟨_, hs, rfl⟩
    have h1' : n * (k * s * k⁻¹) * n⁻¹ ∈ S := by
      have e : k * (k⁻¹ * n * k * s * (k⁻¹ * n * k)⁻¹) * k⁻¹ = n * (k * s * k⁻¹) * n⁻¹ := by group
      rw [← e]
      exact h1
    have h2 : k * s * k⁻¹ ∈ S := (Subgroup.mem_normalizer_iff.mp hn _).mpr h1'
    obtain ⟨t, ht, hteq⟩ := (hk _).mp h2
    have : t = s := by
      have := congrArg (fun z => k⁻¹ * z * k) hteq
      simpa [mul_assoc] using this
    rw [← this]
    exact ht

end Generic

section Main

variable {E : Type} [Group E]

theorem burnsideF411_inf_normalizer_oPPrime_le [Finite E] {p : ℕ} [Fact p.Prime]
    {Gp S B P : Subgroup E} (hS : IsSylowOf p S Gp) (hB : B = Gp ⊓ Subgroup.normalizer (S : Set E))
    (hBP : B ≤ P) (hPGp : P ≤ Gp) (hPne : P ≠ Gp)
    (hPmax : ∀ R : Subgroup E, P < R → R ≤ Gp → R = Gp) :
    Gp ⊓ Subgroup.normalizer (oPPrime p P : Set E) ≤ P := by
  have hSB : S ≤ B := hB ▸ le_inf hS.1 Subgroup.le_normalizer
  have hSO : S ≤ oPPrime p P := burnsideF411_le_oPPrime (hSB.trans hBP) hS.2.1
  have hPle : P ≤ Gp ⊓ Subgroup.normalizer (oPPrime p P : Set E) :=
    le_inf hPGp (Subgroup.le_normalizer.trans
      (burnsideF411_normalizer_le_normalizer_oPPrime p P))
  by_cases hW : Gp ⊓ Subgroup.normalizer (oPPrime p P : Set E) = Gp
  · exfalso
    apply hPne
    refine le_antisymm hPGp (burnsideF411_le_of_normal hS hSO
      (burnsideF411_oPPrime_le p P) hPGp ?_ (hB ▸ hBP))
    rw [← hW]
    exact inf_le_right
  · rcases lt_or_eq_of_le hPle with hlt | heq
    · exact absurd (hPmax _ hlt inf_le_left) hW
    · exact heq.symm.le

theorem burnsideF411_ident_of [Finite E] {p : ℕ} [Fact p.Prime] {Gp M₁ M₂ : Subgroup E}
    (hN : Gp.Normal) (hsplit : ∀ e : E, ∃ n ∈ Gp, ∃ h ∈ M₁ ⊓ M₂, e = n * h)
    (hP : IsLieParabolics p Gp (Gp ⊓ (M₁ ⊓ M₂)) (Gp ⊓ M₁) (Gp ⊓ M₂))
    (hBT : burnsideF411_BorelTitsIn p Gp)
    (hFC : burnsideF411_CentSylow p Gp)
    (hRK1 : burnsideF411_RankOne p Gp (Gp ⊓ (M₁ ⊓ M₂)) (Gp ⊓ M₁))
    (hRK2 : burnsideF411_RankOne p Gp (Gp ⊓ (M₁ ⊓ M₂)) (Gp ⊓ M₂))
    (hQ1 : pCoreOf p (Gp ⊓ M₁) ≠ ⊥) (hQ2 : pCoreOf p (Gp ⊓ M₂) ≠ ⊥) :
    burnsideF411_Ident p M₁ M₂ := by
  classical
  intro T hTp hTi hT X₁ X₂ hX₁ hX₂ hTX₁ hTX₂ hX
  obtain ⟨⟨S, hS, hB⟩, hne, hinter, hmax⟩ := hP
  obtain ⟨hBP₁, hP₁Gp, hP₁ne, hP₁max⟩ := (hmax (Gp ⊓ M₁)).mpr (Or.inl rfl)
  obtain ⟨hBP₂, hP₂Gp, hP₂ne, hP₂max⟩ := (hmax (Gp ⊓ M₂)).mpr (Or.inr rfl)
  have hSB : S ≤ Gp ⊓ (M₁ ⊓ M₂) := hB ▸ le_inf hS.1 Subgroup.le_normalizer
  have hM12S : M₁ ⊓ M₂ ≤ Subgroup.normalizer (S : Set E) := by
    refine burnsideF411_le_normalizer fun x hx s hs => ?_
    let Q : Subgroup E := S.map (MulAut.conj x).toMonoidHom
    have hQB : Q ≤ Gp ⊓ (M₁ ⊓ M₂) := by
      rintro _ ⟨t, ht, rfl⟩
      have htB := hSB ht
      exact ⟨hN.conj_mem t htB.1 x, (M₁ ⊓ M₂).mul_mem ((M₁ ⊓ M₂).mul_mem hx htB.2)
        ((M₁ ⊓ M₂).inv_mem hx)⟩
    have hQN : Q ≤ Subgroup.normalizer (S : Set E) := fun q hq => (hB ▸ hQB hq).2
    have hpQ : IsPGroup p (S ⊔ Q : Subgroup E) :=
      IsPGroup.to_sup_of_normal_left' hS.2.1 (hS.2.1.map _) hQN
    have hQS : S ⊔ Q = S := burnsideF411_eq_of_isSylowOf hS le_sup_left
      (sup_le hS.1 (hQB.trans inf_le_left)) hpQ
    have : x * s * x⁻¹ ∈ Q := ⟨s, hs, rfl⟩
    exact hQS ▸ (le_sup_right : Q ≤ S ⊔ Q) this
  have hTS : T ≤ Subgroup.normalizer (S : Set E) := hT.trans hM12S
  have hST : S ≤ T := by
    have hp : IsPGroup p (S ⊔ T : Subgroup E) := IsPGroup.to_sup_of_normal_left' hS.2.1 hTp hTS
    have := (hTp.toSylow hTi).is_maximal' hp le_sup_right
    rw [IsPGroup.toSylow_coe] at this
    exact this ▸ le_sup_left
  have hNO1 : Subgroup.normalizer (oPPrime p (Gp ⊓ M₁) : Set E) ≤ M₁ :=
    burnsideF411_normalizer_le inf_le_left hsplit
      ((burnsideF411_le_normalizer_inf hN M₁).trans (by
        rw [inf_comm]; exact burnsideF411_normalizer_le_normalizer_oPPrime p _))
      ((burnsideF411_inf_normalizer_oPPrime_le hS hB hBP₁ hP₁Gp hP₁ne hP₁max).trans inf_le_right)
  have hNO2 : Subgroup.normalizer (oPPrime p (Gp ⊓ M₂) : Set E) ≤ M₂ :=
    burnsideF411_normalizer_le inf_le_right hsplit
      ((burnsideF411_le_normalizer_inf hN M₂).trans (by
        rw [inf_comm]; exact burnsideF411_normalizer_le_normalizer_oPPrime p _))
      ((burnsideF411_inf_normalizer_oPPrime_le hS hB hBP₂ hP₂Gp hP₂ne hP₂max).trans inf_le_right)
  have hBlt : ∀ P : Subgroup E, (P = Gp ⊓ M₁ ∨ P = Gp ⊓ M₂) →
      Nat.card (Gp ⊓ (M₁ ⊓ M₂) : Subgroup E) < Nat.card P := by
    intro P hP'
    have hBle : Gp ⊓ (M₁ ⊓ M₂) ≤ P := by
      rcases hP' with rfl | rfl
      · exact hBP₁
      · exact hBP₂
    have hBne : Gp ⊓ (M₁ ⊓ M₂) ≠ P := by
      intro hBeq
      apply hne
      rcases hP' with rfl | rfl
      ·
        have h1 : Gp ⊓ M₁ ≤ Gp ⊓ M₂ := hBeq ▸ hBP₂
        rcases lt_or_eq_of_le h1 with hlt | heq
        · exact absurd (hP₁max _ hlt hP₂Gp) hP₂ne
        · exact heq
      · have h1 : Gp ⊓ M₂ ≤ Gp ⊓ M₁ := hBeq ▸ hBP₁
        rcases lt_or_eq_of_le h1 with hlt | heq
        · exact absurd (hP₂max _ hlt hP₁Gp) hP₁ne
        · exact heq.symm
    exact Subgroup.card_lt_of_lt (lt_of_le_of_ne hBle hBne)
  have single : ∀ (X M : Subgroup E), Nonempty (↥X ≃* ↥M) → M₁ ⊓ M₂ ≤ M →
      pCoreOf p (Gp ⊓ M) ≠ ⊥ → Nat.card (Gp ⊓ (M₁ ⊓ M₂) : Subgroup E) < Nat.card (Gp ⊓ M : Subgroup E) →
      T ≤ X → X ≤ M₁ ∨ X ≤ M₂ := by
    intro X M ⟨χ⟩ hM12M hQM hBltM hTX
    have hOpM : pCoreOf p M ≠ ⊥ := by
      intro h
      apply hQM
      have hle : pCoreOf p (Gp ⊓ M) ≤ pCoreOf p M :=
        CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer p
          ((CFSG.LieType.BorelTits.pCoreOf_le p (Gp ⊓ M)).trans inf_le_right)
          (burnsideF411_le_normalizer_pCoreOf_inf p hN M)
          (CFSG.LieType.BorelTits.pCoreOf_isPGroup p (Gp ⊓ M))
      rw [h] at hle
      exact le_bot_iff.mp hle
    have hOpX : pCoreOf p X ≠ ⊥ := burnsideF411_pCoreOf_ne_bot_of_equiv p χ hOpM
    have hXOp : X ≤ Subgroup.normalizer (pCoreOf p X : Set E) :=
      CFSG.LieType.BorelTits.le_normalizer_pCoreOf p X
    have hOpp : IsPGroup p (pCoreOf p X) := CFSG.LieType.BorelTits.pCoreOf_isPGroup p X
    have hOpXT : pCoreOf p X ≤ T := by
      have hp : IsPGroup p (pCoreOf p X ⊔ T : Subgroup E) :=
        IsPGroup.to_sup_of_normal_left' hOpp hTp (hTX.trans hXOp)
      have := (hTp.toSylow hTi).is_maximal' hp le_sup_right
      rw [IsPGroup.toSylow_coe] at this
      exact this ▸ le_sup_left
    have hR : pCoreOf p X ⊓ Gp ≠ ⊥ := by
      intro hR
      apply hOpX
      have hcent : pCoreOf p X ≤ Subgroup.centralizer (S : Set E) := by
        intro a ha
        rw [Subgroup.mem_centralizer_iff]
        intro s hs
        have hsX : s ∈ X := hTX (hST hs)
        have hc1 : a * s * a⁻¹ * s⁻¹ ∈ pCoreOf p X := by
          have h1 : s * a⁻¹ * s⁻¹ ∈ pCoreOf p X :=
            (Subgroup.mem_normalizer_iff.mp (hXOp hsX) a⁻¹).mp ((pCoreOf p X).inv_mem ha)
          have := (pCoreOf p X).mul_mem ha h1
          simpa [mul_assoc] using this
        have hc2 : a * s * a⁻¹ * s⁻¹ ∈ Gp := by
          have h1 : a * s * a⁻¹ ∈ S :=
            (Subgroup.mem_normalizer_iff.mp (hTS (hOpXT ha)) s).mp hs
          exact Gp.mul_mem (hS.1 h1) (Gp.inv_mem (hS.1 hs))
        have hc : a * s * a⁻¹ * s⁻¹ ∈ pCoreOf p X ⊓ Gp := ⟨hc1, hc2⟩
        rw [hR, Subgroup.mem_bot] at hc
        have : a * s = s * a := by
          calc a * s = (a * s * a⁻¹ * s⁻¹) * (s * a) := by group
            _ = s * a := by rw [hc, one_mul]
        exact this.symm
      have h1 : pCoreOf p X ≤ pCoreOf p X ⊓ Gp := le_inf le_rfl (hFC S hS _ hOpp hcent)
      rw [hR] at h1
      exact le_bot_iff.mp h1
    obtain ⟨S', hS', Pb, hPbGp, hPbne, hNR, hNS'⟩ :=
      hBT (pCoreOf p X ⊓ Gp) inf_le_right hR (hOpp.to_le inf_le_left)
    have hXR : X ≤ Subgroup.normalizer ((pCoreOf p X ⊓ Gp : Subgroup E) : Set E) :=
      burnsideF411_le_normalizer fun y hy s hs =>
        ⟨(Subgroup.mem_normalizer_iff.mp (hXOp hy) s).mp hs.1, hN.conj_mem s hs.2 y⟩
    have hYPb : X ⊓ Gp ≤ Pb := fun y hy => hNR ⟨hy.2, hXR hy.1⟩
    have hSY : S ≤ X ⊓ Gp := le_inf (hST.trans hTX) hS.1
    have hS'Pb : S' ≤ Pb := fun x hx => hNS' ⟨hS'.1 hx, Subgroup.le_normalizer hx⟩
    obtain ⟨k, hkPb, hk⟩ := burnsideF411_sylow_conj
      (burnsideF411_isSylowOf_of_le hS (hSY.trans hYPb) hPbGp)
      (burnsideF411_isSylowOf_of_le hS' hS'Pb hPbGp)
    have hBPb : Gp ⊓ (M₁ ⊓ M₂) ≤ Pb := by
      rw [hB]
      rintro n ⟨hnGp, hnS⟩
      have hkGp : k ∈ Gp := hPbGp hkPb
      have h1 : k⁻¹ * n * k ∈ Gp ⊓ Subgroup.normalizer (S' : Set E) :=
        ⟨Gp.mul_mem (Gp.mul_mem (Gp.inv_mem hkGp) hnGp) hkGp,
          burnsideF411_conj_mem_normalizer hk hnS⟩
      have h2 := hNS' h1
      have := Pb.mul_mem (Pb.mul_mem hkPb h2) (Pb.inv_mem hkPb)
      simpa [mul_assoc] using this
    obtain ⟨Q, hPbQ, hQmax⟩ := Set.Finite.exists_le_maximal
      (Set.toFinite {Q : Subgroup E | Q ≤ Gp ∧ Q ≠ Gp})
      (show Pb ∈ {Q : Subgroup E | Q ≤ Gp ∧ Q ≠ Gp} from ⟨hPbGp, hPbne⟩)
    have hQ12 : Q = Gp ⊓ M₁ ∨ Q = Gp ⊓ M₂ := by
      refine (hmax Q).mp ⟨hBPb.trans hPbQ, hQmax.1.1, hQmax.1.2, fun R hQR hRGp => ?_⟩
      by_contra hRne
      exact absurd (hQmax.2 ⟨hRGp, hRne⟩ hQR.le) (not_le_of_gt hQR)
    have hYQ : X ⊓ Gp ≤ Q := hYPb.trans hPbQ
    have hcardX : Nat.card X = Nat.card M := Nat.card_congr χ.toEquiv
    have hge : Nat.card (Gp ⊓ M : Subgroup E) ≤ Nat.card (X ⊓ Gp : Subgroup E) := by
      rw [inf_comm X]
      exact burnsideF411_card_inf_ge hN (burnsideF411_sup_eq_top hM12M hsplit) hcardX
    have hnotB : ¬ X ⊓ Gp ≤ Gp ⊓ (M₁ ⊓ M₂) := by
      intro hle
      have := Subgroup.card_le_of_le hle
      omega
    rcases hQ12 with hQ | hQ
    · left
      have hO := hRK1 S hS hSB (X ⊓ Gp) hSY (hQ ▸ hYQ) hnotB
      have hOeq := burnsideF411_oPPrime_eq p hO (hQ ▸ hYQ)
      refine le_trans ?_ hNO1
      rw [← hOeq]
      exact (burnsideF411_le_normalizer_inf hN X).trans
        (burnsideF411_normalizer_le_normalizer_oPPrime p _)
    · right
      have hO := hRK2 S hS hSB (X ⊓ Gp) hSY (hQ ▸ hYQ) hnotB
      have hOeq := burnsideF411_oPPrime_eq p hO (hQ ▸ hYQ)
      refine le_trans ?_ hNO2
      rw [← hOeq]
      exact (burnsideF411_le_normalizer_inf hN X).trans
        (burnsideF411_normalizer_le_normalizer_oPPrime p _)
  have h1 := single X₁ M₁ hX₁ inf_le_left hQ1 (hBlt _ (Or.inl rfl)) hTX₁
  have h2 := single X₂ M₂ hX₂ inf_le_right hQ2 (hBlt _ (Or.inr rfl)) hTX₂
  have hc1 : Nat.card X₁ = Nat.card M₁ := Nat.card_congr hX₁.some.toEquiv
  have hc2 : Nat.card X₂ = Nat.card M₂ := Nat.card_congr hX₂.some.toEquiv
  have hM1ne : M₁ ≠ ⊤ := fun h => hP₁ne (by rw [h, inf_top_eq])
  have hM2ne : M₂ ≠ ⊤ := fun h => hP₂ne (by rw [h, inf_top_eq])
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · exact absurd (eq_top_iff.mpr (hX ▸ sup_le h1 h2)) hM1ne
  · exact Or.inl ⟨Subgroup.eq_of_le_of_card_ge h1 hc1.ge, Subgroup.eq_of_le_of_card_ge h2 hc2.ge⟩
  · have hle1 := Subgroup.card_le_of_le h1
    have hle2 := Subgroup.card_le_of_le h2
    exact Or.inr ⟨Subgroup.eq_of_le_of_card_ge h1 (by omega),
      Subgroup.eq_of_le_of_card_ge h2 (by omega)⟩
  · exact absurd (eq_top_iff.mpr (hX ▸ sup_le h1 h2)) hM2ne

end Main

end CFSG.ASVolI
