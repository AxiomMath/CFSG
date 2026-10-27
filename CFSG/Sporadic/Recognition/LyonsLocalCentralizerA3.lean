module

public import CFSG.Sporadic.Recognition.LyonsLocalNormalizerA3

public section

namespace CFSG.Sporadic.Recognition.LyonsSims

open Equiv Equiv.Perm Subgroup

@[expose] def PairCentralizer162 (K : Type*) [Group K] : Prop :=
  ∀ a b : K, orderOf a = 3 → orderOf b = 3 → Nat.card ↥(centralizer ({a} : Set K)) = 29160 →
    Nat.card ↥(centralizer ({b} : Set K)) = 29160 → a * b = b * a → b ∉ zpowers a →
      Nat.card ↥(centralizer ({a, b} : Set K)) = 162

section Std

variable {G : Type} [Group G] [Finite G] {t : G}
  {ρ : ↥(centralizer ({t} : Set G)) →* Perm (Fin 11)}
  {x₁ x₂ x₃ : ↥(centralizer ({t} : Set G))}

namespace LyData

@[expose] def x₃M (D : LyData G t ρ) (S : LyStd ρ x₁ x₂ x₃) :
    ↥(centralizer ({(x₁ : G)} : Set G)) :=
  ⟨(x₃ : G), mem_centralizer_singleton_iff.2 (D.comm₃₁ S)⟩

@[expose] def x₃Q (D : LyData G t ρ) (S : LyStd ρ x₁ x₂ x₃) : CentQuot (x₁ : G) :=
  QuotientGroup.mk (D.x₃M S)

theorem commute_of_comm_mem_zpowers₃ (D : LyData G t ρ) (S : LyStd ρ x₁ x₂ x₃) {m : G}
    (hcomm : m * (x₃ : G) * m⁻¹ * (x₃ : G)⁻¹ ∈ zpowers (x₁ : G)) :
    m * (x₃ : G) = (x₃ : G) * m := by
  obtain ⟨u, hu₂, -, hu₁, -⟩ := D.exists_swap23 S
  have hu₁G : (u : G) * (x₁ : G) * (u : G)⁻¹ = (x₁ : G) := by
    have := congrArg Subtype.val hu₁; simpa using this
  have hu₂G : (u : G) * (x₂ : G) * (u : G)⁻¹ = (x₃ : G) := by
    have := congrArg Subtype.val hu₂; simpa using this
  have hu₁G' : (u : G)⁻¹ * (x₁ : G) * (u : G) = (x₁ : G) := by
    have hc : (u : G) * (x₁ : G) = (x₁ : G) * (u : G) := mul_inv_eq_iff_eq_mul.1 hu₁G
    calc (u : G)⁻¹ * (x₁ : G) * (u : G) = (u : G)⁻¹ * ((x₁ : G) * (u : G)) := by group
      _ = (u : G)⁻¹ * ((u : G) * (x₁ : G)) := by rw [hc]
      _ = (x₁ : G) := by group
  obtain ⟨k, hk⟩ := mem_zpowers_iff.1 hcomm
  have hm' : ((u : G)⁻¹ * m * (u : G)) * (x₂ : G) * ((u : G)⁻¹ * m * (u : G))⁻¹ * (x₂ : G)⁻¹ ∈
      zpowers (x₁ : G) := by
    refine mem_zpowers_iff.2 ⟨k, ?_⟩
    have h1 : (u : G)⁻¹ * (m * (x₃ : G) * m⁻¹ * (x₃ : G)⁻¹) * (u : G) =
        ((u : G)⁻¹ * m * (u : G)) * (x₂ : G) * ((u : G)⁻¹ * m * (u : G))⁻¹ * (x₂ : G)⁻¹ := by
      rw [← hu₂G]; group
    rw [← h1, ← hk]
    have hcz := conj_zpow (a := (u : G)⁻¹) (b := (x₁ : G)) (i := k)
    rw [inv_inv, hu₁G'] at hcz
    exact hcz
  have h2 := D.commute_of_comm_mem_zpowers S hm'
  calc m * (x₃ : G) = m * ((u : G) * (x₂ : G) * (u : G)⁻¹) := by rw [hu₂G]
    _ = (u : G) * (((u : G)⁻¹ * m * (u : G)) * (x₂ : G)) * (u : G)⁻¹ := by group
    _ = (u : G) * ((x₂ : G) * ((u : G)⁻¹ * m * (u : G))) * (u : G)⁻¹ := by rw [h2]
    _ = ((u : G) * (x₂ : G) * (u : G)⁻¹) * m := by group
    _ = (x₃ : G) * m := by rw [hu₂G]

theorem commute_of_mk_commute₃ (D : LyData G t ρ) (S : LyStd ρ x₁ x₂ x₃)
    {m : ↥(centralizer ({(x₁ : G)} : Set G))}
    (h : (QuotientGroup.mk m : CentQuot (x₁ : G)) * D.x₃Q S =
      D.x₃Q S * QuotientGroup.mk m) :
    (m : G) * (x₃ : G) = (x₃ : G) * (m : G) := by
  apply D.commute_of_comm_mem_zpowers₃ S
  have h1 := mem_zpowers_of_mk_eq_one (x₁ : G)
    (m := m * D.x₃M S * m⁻¹ * (D.x₃M S)⁻¹) (by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
        QuotientGroup.mk_inv, QuotientGroup.mk_inv]
      change (QuotientGroup.mk m : CentQuot (x₁ : G)) * D.x₃Q S * (QuotientGroup.mk m)⁻¹ *
        (D.x₃Q S)⁻¹ = 1
      rw [h]
      group)
  exact h1

theorem Q3_eq_preimQ (D : LyData G t ρ) (S : LyStd ρ x₁ x₂ x₃) :
    Q3 (x₁ : G) (x₂ : G) (x₃ : G) =
      preimQ (x₁ : G) (centralizer ({D.x₂Q S, D.x₃Q S} : Set (CentQuot (x₁ : G)))) := by
  ext g
  rw [mem_Q3, mem_preimQ]
  constructor
  · rintro ⟨h1, h2, h3⟩
    have hc : g ∈ centralizer ({(x₁ : G)} : Set G) := mem_centralizer_singleton_iff.2 h1.symm
    refine ⟨hc, ?_⟩
    rw [mem_centralizer_iff]
    intro y hy
    rcases hy with rfl | rfl
    · change D.x₂Q S * QuotientGroup.mk (⟨g, hc⟩ : ↥(centralizer ({(x₁ : G)} : Set G))) =
        QuotientGroup.mk (⟨g, hc⟩ : ↥(centralizer ({(x₁ : G)} : Set G))) * D.x₂Q S
      rw [LyData.x₂Q, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      congr 1
      exact Subtype.ext h2
    · change D.x₃Q S * QuotientGroup.mk (⟨g, hc⟩ : ↥(centralizer ({(x₁ : G)} : Set G))) =
        QuotientGroup.mk (⟨g, hc⟩ : ↥(centralizer ({(x₁ : G)} : Set G))) * D.x₃Q S
      rw [LyData.x₃Q, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      congr 1
      exact Subtype.ext h3
  · rintro ⟨hc, hK⟩
    rw [mem_centralizer_iff] at hK
    have h2 := hK (D.x₂Q S) (by simp)
    have h3 := hK (D.x₃Q S) (by simp)
    have e2 := D.commute_of_mk_commute S (m := ⟨g, hc⟩) h2.symm
    have e3 := D.commute_of_mk_commute₃ S (m := ⟨g, hc⟩) h3.symm
    exact ⟨(mem_centralizer_singleton_iff.1 hc).symm, e2.symm, e3.symm⟩

omit [Finite G] in
theorem orderOf_x₃Q (D : LyData G t ρ) (S : LyStd ρ x₁ x₂ x₃) : orderOf (D.x₃Q S) = 3 := by
  have h3 : D.x₃Q S ^ 3 = 1 := by
    rw [x₃Q, ← QuotientGroup.mk_pow]
    have : D.x₃M S ^ 3 = 1 := by
      apply Subtype.ext
      have := congrArg Subtype.val S.pow₃
      simpa [x₃M] using this
    rw [this]; rfl
  have hne : D.x₃Q S ≠ 1 := by
    intro h1
    have h2 := mem_zpowers_of_mk_eq_one (x₁ : G) h1
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 h2
    have hx1 : (x₁ : G) ^ k = ((x₁ ^ k : ↥(centralizer ({t} : Set G))) : G) := by
      rw [Subgroup.coe_zpow]
    have hH : x₁ ^ k = x₃ := Subtype.ext (hx1.symm.trans hk)
    have hρ : ρ (x₁ ^ k) = x3p := by rw [hH, S.rho₃]
    rw [map_zpow, S.rho₁] at hρ
    rcases zpow_cases x1p_pow_three k with h | h | h <;> rw [h] at hρ <;>
      exact absurd hρ.symm (by decide)
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  exact orderOf_eq_prime h3 hne

omit [Finite G] in
theorem x₂Q_mul_x₃Q (D : LyData G t ρ) (S : LyStd ρ x₁ x₂ x₃) :
    D.x₂Q S * D.x₃Q S = D.x₃Q S * D.x₂Q S := by
  rw [x₂Q, x₃Q, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  congr 1
  apply Subtype.ext
  exact (D.comm₃₂ S).symm

omit [Finite G] in
theorem x₃Q_notMem_zpowers (D : LyData G t ρ) (S : LyStd ρ x₁ x₂ x₃) :
    D.x₃Q S ∉ zpowers (D.x₂Q S) := by
  intro hmem
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmem
  have h1 : (QuotientGroup.mk ((D.x₂M S) ^ k * (D.x₃M S)⁻¹) : CentQuot (x₁ : G)) = 1 := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_zpow]
    change (D.x₂Q S) ^ k * (D.x₃Q S)⁻¹ = 1
    rw [hk]; group
  have h2 := mem_zpowers_of_mk_eq_one (x₁ : G) h1
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 h2
  have hj' : (x₁ : G) ^ j = (x₂ : G) ^ k * (x₃ : G)⁻¹ := by
    simpa [x₂M, x₃M] using hj
  have hH : x₂ ^ k * x₃⁻¹ = x₁ ^ j := by
    apply Subtype.ext
    simpa using hj'.symm
  have hρ := congrArg ρ hH
  rw [map_mul, map_inv, map_zpow, map_zpow, S.rho₁, S.rho₂, S.rho₃] at hρ
  rcases zpow_cases x2p_pow_three k with h | h | h <;>
    rcases zpow_cases x1p_pow_three j with h' | h' | h' <;>
    rw [h, h'] at hρ <;> exact absurd hρ (by decide)

end LyData

end Std

theorem conj_mem_Q3 {G : Type*} [Group G] {a b c n q : G}
    (hn : n ∈ normalizer (A3 a b c : Set G)) (hq : q ∈ Q3 a b c) : n * q * n⁻¹ ∈ Q3 a b c := by
  have hQ : Q3 a b c = centralizer ((A3 a b c : Subgroup G) : Set G) := by
    rw [A3, Subgroup.centralizer_closure]; rfl
  rw [hQ] at hq ⊢
  rw [mem_centralizer_iff] at hq ⊢
  intro e he
  have he' : n⁻¹ * e * n ∈ (A3 a b c : Subgroup G) := (mem_normalizer_iff''.1 hn e).1 he
  have h1 := hq _ he'
  calc e * (n * q * n⁻¹) = n * ((n⁻¹ * e * n) * q) * n⁻¹ := by group
    _ = n * (q * (n⁻¹ * e * n)) * n⁻¹ := by rw [h1]
    _ = n * q * n⁻¹ * e := by group

structure SylowQ3 {G : Type*} [Group G] (a b c t : G) (A : Subgroup G) : Prop where
  le : A ≤ Q3 a b c
  card : Nat.card ↥A = 243
  isPGroup : IsPGroup 3 ↥A
  normal : ∀ g ∈ Q3 a b c, ∀ x ∈ A, g * x * g⁻¹ ∈ A
  max : ∀ J : Subgroup G, J ≤ Q3 a b c → IsPGroup 3 ↥J → J ≤ A
  t_mem : t ∈ Q3 a b c
  t_notMem : t ∉ A
  cosets : ∀ g ∈ Q3 a b c, g ∈ A ∨ ∃ x ∈ A, g = x * t
  normalizer : ∀ n ∈ normalizer (A3 a b c : Set G), ∀ x ∈ A, n * x * n⁻¹ ∈ A

section Cert

variable {G : Type} [Group G] [Finite G] {t : G}
  {ρ : ↥(centralizer ({t} : Set G)) →* Perm (Fin 11)}
  {x₁ x₂ x₃ : ↥(centralizer ({t} : Set G))}

namespace LyData

theorem card_Q3 (D : LyData G t ρ) (S : LyStd ρ x₁ x₂ x₃)
    (hpair : PairCentralizer162 (CentQuot (x₁ : G))) :
    Nat.card ↥(Q3 (x₁ : G) (x₂ : G) (x₃ : G)) = 486 := by
  obtain ⟨e⟩ := D.centQuot_mcl S.pow₁ S.rho₁
  have hy2 := D.orderOf_x₂Q S
  have hy3 := D.orderOf_x₃Q S
  have hc2 := card_centralizer_eq_of_five_dvd e hy2 (D.five_dvd_card_centralizer_x₂Q S)
  obtain ⟨u, hu₂, -, hu₁, -⟩ := D.exists_swap23 S
  have hu₁G : (u : G) * (x₁ : G) = (x₁ : G) * (u : G) := by
    have := congrArg Subtype.val hu₁
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at this
    exact mul_inv_eq_iff_eq_mul.1 this
  let uM : ↥(centralizer ({(x₁ : G)} : Set G)) :=
    ⟨(u : G), mem_centralizer_singleton_iff.2 hu₁G⟩
  have hconj : IsConj (D.x₂Q S) (D.x₃Q S) := by
    refine isConj_iff.2 ⟨QuotientGroup.mk uM, ?_⟩
    rw [LyData.x₂Q, LyData.x₃Q, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
      ← QuotientGroup.mk_mul]
    congr 1
    apply Subtype.ext
    have := congrArg Subtype.val hu₂
    simpa [uM, LyData.x₂M, LyData.x₃M] using this
  have hc3 : Nat.card ↥(centralizer ({D.x₃Q S} : Set (CentQuot (x₁ : G)))) = 29160 := by
    rw [← card_centralizer_eq_of_isConj hconj]; exact hc2
  have h := hpair _ _ hy2 hy3 hc2 hc3 (D.x₂Q_mul_x₃Q S) (D.x₃Q_notMem_zpowers S)
  rw [D.Q3_eq_preimQ S, card_preimQ, orderOf_x₁ S, h]

theorem exists_sylowQ3 (D : LyData G t ρ) (S : LyStd ρ x₁ x₂ x₃)
    (hpair : PairCentralizer162 (CentQuot (x₁ : G))) :
    ∃ A : Subgroup G, SylowQ3 (x₁ : G) (x₂ : G) (x₃ : G) t A := by
  set W : Subgroup G := Q3 (x₁ : G) (x₂ : G) (x₃ : G) with hW
  have hcard : Nat.card ↥W = 486 := D.card_Q3 S hpair
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hfin : Finite ↥W := inferInstance
  obtain ⟨P⟩ : Nonempty (Sylow 3 ↥W) := inferInstance
  have hfac : (Nat.card ↥W).factorization 3 = 5 := by
    rw [hcard, show (486 : ℕ) = 3 ^ 5 * 2 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.Prime.factorization_pow (by norm_num : Nat.Prime 3), Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
  have hPcard : Nat.card ↥(P : Subgroup ↥W) = 243 := by
    rw [Sylow.card_eq_multiplicity, hfac]; norm_num
  have hidx : (P : Subgroup ↥W).index = 2 := by
    have h1 := Subgroup.card_mul_index (P : Subgroup ↥W)
    rw [hPcard, hcard] at h1
    omega
  have hPn : (P : Subgroup ↥W).Normal := Subgroup.normal_of_index_eq_two hidx
  have hunique : Unique (Sylow 3 ↥W) := Sylow.unique_of_normal P hPn
  set A : Subgroup G := (P : Subgroup ↥W).map W.subtype with hA
  have hAle : A ≤ W := map_subtype_le _
  have hAcard : Nat.card ↥A = 243 := by
    rw [hA, Subgroup.card_map_of_injective W.subtype_injective, hPcard]
  have hmax : ∀ J : Subgroup G, J ≤ W → IsPGroup 3 ↥J → J ≤ A := by
    intro J hJW hJ
    have hJ' : IsPGroup 3 ↥(J.subgroupOf W) := hJ.of_equiv (subgroupOfEquivOfLe hJW).symm
    obtain ⟨Q, hQ⟩ := hJ'.exists_le_sylow
    have hQP : Q = P := Subsingleton.elim Q P
    rw [hQP] at hQ
    intro g hg
    exact ⟨⟨g, hJW hg⟩, hQ hg, rfl⟩
  have hnorm : ∀ g ∈ W, ∀ x ∈ A, g * x * g⁻¹ ∈ A := by
    rintro g hg _ ⟨x, hx, rfl⟩
    exact ⟨⟨g, hg⟩ * x * ⟨g, hg⟩⁻¹, hPn.conj_mem x hx ⟨g, hg⟩, by simp⟩
  have htW : t ∈ W := by
    rw [hW, mem_Q3]
    refine ⟨?_, ?_, ?_⟩
    · exact (mem_centralizer_singleton_iff.1 x₁.2)
    · exact (mem_centralizer_singleton_iff.1 x₂.2)
    · exact (mem_centralizer_singleton_iff.1 x₃.2)
  have ht2 : orderOf t = 2 := D.order_t
  have hAp : IsPGroup 3 ↥A := IsPGroup.of_card (n := 5) (by rw [hAcard]; norm_num)
  have htA : t ∉ A := by
    intro htA
    obtain ⟨k, hk⟩ := hAp ⟨t, htA⟩
    have h1 : orderOf (⟨t, htA⟩ : ↥A) ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one hk
    rw [Subgroup.orderOf_mk, ht2] at h1
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two Nat.prime_three).1
      (Nat.Prime.dvd_of_dvd_pow Nat.prime_two h1)
    omega
  refine ⟨A, ⟨hAle, hAcard, hAp, hnorm, hmax, htW, htA, ?_, ?_⟩⟩
  ·
    intro g hg
    obtain ⟨c, hc⟩ := Subgroup.index_eq_two_iff.1 hidx
    by_cases hgA : g ∈ A
    · exact Or.inl hgA
    · right
      have hgP : (⟨g, hg⟩ : ↥W) ∉ (P : Subgroup ↥W) := fun h => hgA ⟨_, h, rfl⟩
      have htP : (⟨t, htW⟩ : ↥W) ∉ (P : Subgroup ↥W) := fun h => htA ⟨_, h, rfl⟩
      have h1 := ((hc ⟨g, hg⟩).resolve_right (fun h => hgP h.1)).1
      have h2 := ((hc ⟨t, htW⟩).resolve_right (fun h => htP h.1)).1
      have h3 : (⟨g, hg⟩ : ↥W) * (⟨t, htW⟩ : ↥W)⁻¹ ∈ (P : Subgroup ↥W) := by
        have := (P : Subgroup ↥W).mul_mem h1 ((P : Subgroup ↥W).inv_mem h2)
        simpa [mul_assoc] using this
      refine ⟨g * t⁻¹, ⟨_, h3, rfl⟩, ?_⟩
      group
  · intro n hn x hx
    have hJ : A.map (MulAut.conj n).toMonoidHom ≤ A := by
      refine hmax _ ?_ (hAp.map _)
      rintro _ ⟨a, ha, rfl⟩
      exact conj_mem_Q3 hn (hAle ha)
    exact hJ ⟨x, hx, rfl⟩

theorem card_normalizer_A3' (D : LyData G t ρ) (S : LyStd ρ x₁ x₂ x₃)
    (hpair : PairCentralizer162 (CentQuot (x₁ : G))) :
    Nat.card ↥(normalizer (A3 (x₁ : G) (x₂ : G) (x₃ : G) : Set G)) = 23328 := by
  rw [D.card_normalizer_A3 S, D.card_Q3 S hpair]

end LyData

end Cert

end CFSG.Sporadic.Recognition.LyonsSims
