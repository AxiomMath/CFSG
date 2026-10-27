module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamSTypeA
public import CFSG.Quasithin.Background.GoldschmidtAmalgamSEightB

public section

namespace CFSG.Quasithin.F6.GoldAmS

open Equiv CFSG.Open CFSG.QuasithinUnique

def signZ2 : Perm (Fin 3) →* Multiplicative (ZMod 2) :=
  MonoidHom.mk' (fun σ => if Equiv.Perm.sign σ = 1 then 1 else Multiplicative.ofAdd 1)
    (by decide +kernel)

theorem signZ2_involution : ∀ s : Perm (Fin 3), s * s = 1 → s ≠ 1 →
    signZ2 s = Multiplicative.ofAdd 1 := by
  decide +kernel

theorem zmod_two_sq : ∀ y : Multiplicative (ZMod 2), y * y = 1 := by decide

section VertexData

variable {E : Type*} [Group E] [Finite E] {A₁ A₂ : Subgroup E}

theorem vertex_data (h : IsGoldschmidtTriple A₁ A₂) (c : CharTwo A₁)
    (hT : Nat.card ↥(A₁ ⊓ A₂) = 16) :
    ∃ (x : ↥A₁) (π : ↥A₁ →* Perm (Fin 3)), Nat.card (CFSG.Open.pCore 2 ↥A₁) = 8 ∧ x ^ 3 = 1 ∧
      (∃ q ∈ CFSG.Open.pCore 2 ↥A₁, x * q * x⁻¹ ≠ q) ∧
      ∀ g : ↥A₁, π g = 1 ↔ g ∈ CFSG.Open.pCore 2 ↥A₁ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h3 := card_vertex_left h
  have h6 := card_pCore_mul_six h
  have hA : Nat.card ↥A₁ = 48 := by rw [h3, hT]
  have hQ : Nat.card (CFSG.Open.pCore 2 ↥A₁) = 8 := by omega
  have h33 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let _ : Fintype ↥A₁ := Fintype.ofFinite _
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card (G := ↥A₁) 3
    (by rw [← Nat.card_eq_fintype_card, hA]; norm_num)
  have hx3 : x ^ 3 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  have hx1 : x ≠ 1 := fun h => by rw [h, orderOf_one] at hx; omega
  obtain ⟨e⟩ := h.quotient₁
  refine ⟨x, e.toMonoidHom.comp (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥A₁)), hQ, hx3, ?_, ?_⟩
  · by_contra hcon
    push Not at hcon
    have hxQ : x ∈ CFSG.Open.pCore 2 ↥A₁ := charTwo_cent c x fun q hq => by
      have := hcon q hq
      calc x * q = x * q * x⁻¹ * x := by group
        _ = q * x := by rw [this]
    have h8 : x ^ 8 = 1 := by
      have h := pow_card_eq_one' (G := CFSG.Open.pCore 2 ↥A₁) (x := ⟨x, hxQ⟩)
      rw [hQ] at h
      simpa using congrArg Subtype.val h
    apply hx1
    calc x = (x ^ 3) ^ 3 * (x ^ 8)⁻¹ := by group
      _ = 1 := by rw [hx3, h8]; simp
  · intro g
    show e (QuotientGroup.mk g) = 1 ↔ g ∈ CFSG.Open.pCore 2 ↥A₁
    rw [← map_one e, e.injective.eq_iff]
    exact QuotientGroup.eq_one_iff g

@[expose] def Dich (A Q : Subgroup E) : Prop :=
  (∀ q ∈ Q, q * q = 1) ∨ ∃ z ∈ Q, z ≠ 1 ∧ z * z = 1 ∧ (∀ g ∈ A, g * z = z * g) ∧
    ∀ q ∈ Q, q * q = 1 → q = 1 ∨ q = z

theorem dich_of_vertex (h : IsGoldschmidtTriple A₁ A₂) (c : CharTwo A₁)
    (hT : Nat.card ↥(A₁ ⊓ A₂) = 16) : Dich A₁ (pCoreOf 2 A₁) := by
  obtain ⟨x, π, hcard, hx, hnc, -⟩ := vertex_data h c hT
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn : (CFSG.Open.pCore 2 ↥A₁).Normal := CFSG.LieType.BorelTits.pCore_normal 2
  have : Finite (CFSG.Open.pCore 2 ↥A₁) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  rcases eight_dichotomy (CFSG.Open.pCore 2 ↥A₁) hcard x hx hnc with
    h1 | ⟨z, hzQ, hz1, hzz, hzu⟩
  · left
    rintro _ ⟨q, hq, rfl⟩
    have := congrArg Subtype.val (h1 q hq)
    simpa using this
  · right
    refine ⟨(z : E), ⟨z, hzQ, rfl⟩, fun h => hz1 (Subtype.ext h), ?_, ?_, ?_⟩
    · have := congrArg Subtype.val hzz
      simpa using this
    · intro g hg
      have hconj : (⟨g, hg⟩ : ↥A₁) * z * (⟨g, hg⟩ : ↥A₁)⁻¹ ∈ CFSG.Open.pCore 2 ↥A₁ :=
        hn.conj_mem z hzQ ⟨g, hg⟩
      have hsq : ((⟨g, hg⟩ : ↥A₁) * z * (⟨g, hg⟩ : ↥A₁)⁻¹) *
          ((⟨g, hg⟩ : ↥A₁) * z * (⟨g, hg⟩ : ↥A₁)⁻¹) = 1 := by
        calc _ = (⟨g, hg⟩ : ↥A₁) * (z * z) * (⟨g, hg⟩ : ↥A₁)⁻¹ := by group
          _ = 1 := by rw [hzz]; group
      rcases hzu _ hconj hsq with h2 | h2
      · exfalso
        apply hz1
        calc z = (⟨g, hg⟩ : ↥A₁)⁻¹ * ((⟨g, hg⟩ : ↥A₁) * z * (⟨g, hg⟩ : ↥A₁)⁻¹) * ⟨g, hg⟩ := by
              group
          _ = 1 := by rw [h2]; group
      · have := congrArg Subtype.val h2
        simp only [Subgroup.coe_mul, Subgroup.coe_inv] at this
        calc g * (z : E) = g * z * g⁻¹ * g := by group
          _ = (z : E) * g := by rw [this]
    · rintro _ ⟨q, hq, rfl⟩ hqq
      have hq2 : q * q = 1 := Subtype.ext (by simpa using hqq)
      rcases hzu q hq hq2 with h2 | h2
      · exact Or.inl (by rw [h2]; rfl)
      · exact Or.inr (by rw [h2]; rfl)

structure VtxB (A Q N : Subgroup E) (ε : E) : Prop where
  Q_le : Q ≤ A
  Q_norm : ∀ g ∈ A, ∀ q ∈ Q, g * q * g⁻¹ ∈ Q
  Q_card : Nat.card Q = 8
  Q_exp : ∀ q ∈ Q, q * q = 1
  cent : ∀ g ∈ A, (∀ q ∈ Q, g * q = q * g) → g ∈ Q
  ε_mem : ε ∈ Q
  ε_ne : ε ≠ 1
  ε_central : ∀ g ∈ A, g * ε = ε * g
  N_le : N ≤ Q
  N_norm : ∀ g ∈ A, ∀ n ∈ N, g * n * g⁻¹ ∈ N
  N_card : Nat.card N = 4
  ε_not_N : ε ∉ N
  Q_split : ∀ q ∈ Q, q ∈ N ∨ ε * q ∈ N
  N_kill : ∀ V : ↥A →* Multiplicative (ZMod 2), ∀ n (hn : n ∈ N), V ⟨n, Q_le (N_le hn)⟩ = 1
  comm_N : ∀ q ∈ Q, ∀ g ∈ A, q * (g * q * g⁻¹)⁻¹ ∈ N
  sign : ∃ s : ↥A →* Multiplicative (ZMod 2), (∀ q (hq : q ∈ Q), s ⟨q, Q_le hq⟩ = 1) ∧
    ∀ g (hg : g ∈ A), g * g = 1 → g ∉ Q → s ⟨g, hg⟩ = Multiplicative.ofAdd 1

theorem vtxB_of_vertex (h : IsGoldschmidtTriple A₁ A₂) (c : CharTwo A₁)
    (hT : Nat.card ↥(A₁ ⊓ A₂) = 16) (hexp : ∀ q ∈ pCoreOf 2 A₁, q * q = 1) :
    ∃ (N : Subgroup E) (ε : E), VtxB A₁ (pCoreOf 2 A₁) N ε := by
  obtain ⟨x, π, hcard, hx, hnc, hker⟩ := vertex_data h c hT
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn : (CFSG.Open.pCore 2 ↥A₁).Normal := CFSG.LieType.BorelTits.pCore_normal 2
  have hexp' : ∀ q ∈ CFSG.Open.pCore 2 ↥A₁, q * q = 1 := fun q hq => by
    have := hexp (q : E) ⟨q, hq, rfl⟩
    exact Subtype.ext (by simpa using this)
  have hE : Eight (CFSG.Open.pCore 2 ↥A₁) x π := ⟨hcard, hexp', hx, hnc, hker⟩
  obtain ⟨cc, hcc⟩ := hE.exists_c
  have hcent := charTwo_cent c
  refine ⟨(hE.normKer).map A₁.subtype, (cc : E), ?_⟩
  have hQle : pCoreOf 2 A₁ ≤ A₁ := Subgroup.map_subtype_le _
  have hNle : (hE.normKer).map A₁.subtype ≤ pCoreOf 2 A₁ :=
    Subgroup.map_mono hE.normKer_le
  refine ⟨hQle, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hNle, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro g hg _ ⟨q, hq, rfl⟩
    exact ⟨⟨g, hg⟩ * q * ⟨g, hg⟩⁻¹, hn.conj_mem q hq ⟨g, hg⟩, rfl⟩
  · show Nat.card ↥((CFSG.Open.pCore 2 ↥A₁).map A₁.subtype) = 8
    rw [Subgroup.card_map_of_injective A₁.subtype_injective]
    exact hcard
  · rintro _ ⟨q, hq, rfl⟩
    exact hexp q ⟨q, hq, rfl⟩
  · intro g hg hgc
    have := hcent ⟨g, hg⟩ fun q hq => Subtype.ext (hgc q ⟨q, hq, rfl⟩)
    exact ⟨⟨g, hg⟩, this, rfl⟩
  · exact ⟨cc, hcc.mem, rfl⟩
  · exact fun h1 => hcc.ne (Subtype.ext h1)
  · intro g hg
    have := hE.c_central hcc ⟨g, hg⟩
    have h2 : (⟨g, hg⟩ : ↥A₁) * cc = cc * ⟨g, hg⟩ := by
      calc (⟨g, hg⟩ : ↥A₁) * cc = ⟨g, hg⟩ * cc * ⟨g, hg⟩⁻¹ * ⟨g, hg⟩ := by group
        _ = cc * ⟨g, hg⟩ := by rw [this]
    exact congrArg Subtype.val h2
  · rintro g hg _ ⟨n, hn', rfl⟩
    exact ⟨⟨g, hg⟩ * n * ⟨g, hg⟩⁻¹, hE.normKer_conj hcc ⟨g, hg⟩ hn', rfl⟩
  · show Nat.card ↥((hE.normKer).map A₁.subtype) = 4
    rw [Subgroup.card_map_of_injective A₁.subtype_injective]
    exact hE.card_normKer hcc
  · rintro ⟨n, hn', hnc'⟩
    exact hE.c_not_mem_normKer hcc (by
      have : n = cc := Subtype.ext hnc'
      rwa [this] at hn')
  · rintro _ ⟨q, hq, rfl⟩
    rcases hE.mem_normKer_or hcc hq with h1 | h1
    · exact Or.inl ⟨q, h1, rfl⟩
    · exact Or.inr ⟨cc * q, h1, rfl⟩
  · intro V n hn'
    obtain ⟨n', hn'', rfl⟩ := hn'
    exact hE.normKer_kill zmod_two_sq V hn''
  · rintro _ ⟨q, hq, rfl⟩ g hg
    exact ⟨q * (⟨g, hg⟩ * q * ⟨g, hg⟩⁻¹)⁻¹, hE.comm_mem_normKer hcc hq ⟨g, hg⟩, rfl⟩
  · refine ⟨signZ2.comp π, ?_, ?_⟩
    · rintro _ ⟨q, hq, rfl⟩
      show signZ2 (π q) = 1
      rw [(hker q).2 hq, map_one]
    · intro g hg hgg hgQ
      show signZ2 (π ⟨g, hg⟩) = _
      apply signZ2_involution
      · rw [← map_mul]
        have : (⟨g, hg⟩ : ↥A₁) * ⟨g, hg⟩ = 1 := Subtype.ext hgg
        rw [this, map_one]
      · intro h1
        exact hgQ ⟨⟨g, hg⟩, (hker _).1 h1, rfl⟩

end VertexData

end CFSG.Quasithin.F6.GoldAmS
