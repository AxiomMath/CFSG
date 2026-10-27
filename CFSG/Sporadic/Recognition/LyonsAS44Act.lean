module

public import CFSG.Sporadic.Recognition.LyonsAS44Sylow
public import CFSG.Sporadic.Recognition.LyonsAS44ConjPerm

public section

namespace CFSG.Sporadic.Recognition.LyonsSims

open Equiv Equiv.Perm Subgroup CFSG.Sporadic.Recognition.McLAS

section Gen

variable {G : Type*} [Group G]

abbrev normAG (x : G) (A : Subgroup (CentQuot x)) : Subgroup G :=
  normalizer (preimQ x A : Set G)

abbrev ptsAG (x : G) (A : Subgroup (CentQuot x)) : Set (Subgroup G) := deltaIn x (preimQ x A)

theorem conjSub_mem_deltaIn {x : G} {K : Subgroup G} {g : G} (hg : g ∈ normalizer (K : Set G))
    {B : Subgroup G} (hB : B ∈ deltaIn x K) : conjSub g B ∈ deltaIn x K := by
  obtain ⟨w, hwc, hwK, rfl⟩ := mem_deltaIn_iff.1 hB
  refine mem_deltaIn_iff.2 ⟨g * w * g⁻¹, hwc.trans (isConj_iff.2 ⟨g, rfl⟩), ?_,
    conjSub_zpowers _ _⟩
  exact (mem_normalizer_iff.1 hg w).1 hwK

@[expose] def actPerm (x : G) (A : Subgroup (CentQuot x)) :
    ↥(normAG x A) →* Perm ↥(ptsAG x A) :=
  conjPerm (normAG x A) (ptsAG x A) fun _ hg _ hB => conjSub_mem_deltaIn hg hB

@[expose] def pt0 (x : G) (A : Subgroup (CentQuot x)) : ↥(ptsAG x A) :=
  ⟨zpowers x, mem_deltaIn_iff.2 ⟨x, IsConj.refl _, x_mem_preimQ A, rfl⟩⟩

theorem mem_preimQ_coe {x : G} {K : Subgroup (CentQuot x)} (u : ↥(centralizer ({x} : Set G))) :
    (u : G) ∈ preimQ x K ↔ projQ x u ∈ K :=
  ⟨fun h => (mem_preimQ.1 h).2, fun h => mem_preimQ.2 ⟨u.2, h⟩⟩

theorem mem_normalizer_preimQ_iff {x : G} {A : Subgroup (CentQuot x)}
    (m : ↥(centralizer ({x} : Set G))) :
    (m : G) ∈ normalizer (preimQ x A : Set G) ↔ projQ x m ∈ normalizer (A : Set (CentQuot x)) := by
  rw [mem_normalizer_iff, mem_normalizer_iff]
  constructor
  · intro h q
    obtain ⟨u, rfl⟩ := projQ_surjective x q
    have h1 := h (u : G)
    rw [mem_preimQ_coe, show (m : G) * (u : G) * (m : G)⁻¹ =
      ((m * u * m⁻¹ : ↥(centralizer ({x} : Set G))) : G) from rfl, mem_preimQ_coe] at h1
    rw [← map_inv, ← map_mul, ← map_mul]
    exact h1
  · intro h g
    by_cases hg : g ∈ centralizer ({x} : Set G)
    · have h1 := h (projQ x ⟨g, hg⟩)
      rw [← map_inv, ← map_mul, ← map_mul] at h1
      have e1 := mem_preimQ_coe (K := A) ⟨g, hg⟩
      have e2 := mem_preimQ_coe (K := A) (m * ⟨g, hg⟩ * m⁻¹)
      simp only [Subgroup.coe_mul, Subgroup.coe_inv] at e1 e2
      rw [e1, e2]
      exact h1
    · have hg' : (m : G) * g * (m : G)⁻¹ ∉ centralizer ({x} : Set G) := by
        intro hc
        apply hg
        have := Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ m.2) hc) m.2
        simpa [mul_assoc] using this
      exact ⟨fun hh => absurd (preimQ_le_centralizer _ hh) hg,
        fun hh => absurd (preimQ_le_centralizer _ hh) hg'⟩

end Gen

section Act

variable {G : Type} [Group G] [Finite G] {t : G}
  {ρ : ↥(centralizer ({t} : Set G)) →* Perm (Fin 11)}
  {x₁ x₂ x₃ : ↥(centralizer ({t} : Set G))}
  {R T A : Subgroup (CentQuot (x₁ : G))} {Y : Fin 10 → CentQuot (x₁ : G)}

namespace LyData

variable (D : LyData G t ρ) (S : LyStd ρ x₁ x₂ x₃) (F : LyAFacts D S R T A Y)

include D S F

theorem exists_actPerm_eq (ω ω' : ↥(ptsAG (x₁ : G) A)) :
    ∃ k : ↥(normAG (x₁ : G) A), actPerm (x₁ : G) A k ω = ω' := by
  obtain ⟨B, hB⟩ := ω
  obtain ⟨B', hB'⟩ := ω'
  obtain ⟨w, hwc, hwA, rfl⟩ := mem_deltaIn_iff.1 hB
  obtain ⟨w', hwc', hwA', rfl⟩ := mem_deltaIn_iff.1 hB'
  obtain ⟨k, hk, hkw⟩ := D.exists_mem_normalizer_of_isConj S F hwA hwA' (hwc.symm.trans hwc')
  refine ⟨⟨k, hk⟩, Subtype.ext ?_⟩
  show conjSub k (zpowers w) = zpowers w'
  rw [conjSub_zpowers, hkw]

theorem exists_idx {ω : ↥(ptsAG (x₁ : G) A)} (hω : ω ≠ pt0 (x₁ : G) A) :
    ∃ j : Fin 10, (ω : Subgroup G) = zpowers (D.zlift S F j : G) := by
  obtain ⟨i | j, hij⟩ := (D.deltaIn_AG_eq S F).le ω.2
  · exact absurd (Subtype.ext hij.symm) hω
  · exact ⟨j, hij.symm⟩

theorem zpowers_conj_zlift (m : ↥(centralizer ({(x₁ : G)} : Set G))) (i j : Fin 10)
    (h : projQ (x₁ : G) m * Y i * (projQ (x₁ : G) m)⁻¹ = Y j ∨
      projQ (x₁ : G) m * Y i * (projQ (x₁ : G) m)⁻¹ = (Y j)⁻¹) :
    zpowers ((m : G) * (D.zlift S F i : G) * (m : G)⁻¹) = zpowers (D.zlift S F j : G) := by
  set u : ↥(centralizer ({(x₁ : G)} : Set G)) := m * D.zlift S F i * m⁻¹ with hu
  have huG : (u : G) = (m : G) * (D.zlift S F i : G) * (m : G)⁻¹ := rfl
  have huc : IsConj (x₁ : G) (u : G) :=
    (D.zlift_isConj S F i).trans (isConj_iff.2 ⟨m, huG.symm⟩)
  have hpu : projQ (x₁ : G) u = projQ (x₁ : G) m * Y i * (projQ (x₁ : G) m)⁻¹ := by
    rw [hu, map_mul, map_mul, map_inv, D.zlift_proj S F]
  rw [← huG]
  rcases h with h | h
  · have := D.eq_of_isConj_of_proj_eq S F huc (D.zlift_isConj S F j)
      (by rw [hpu, h, D.zlift_proj S F]) (by rw [hpu, h]; exact D.Y_ne_one S F j)
    rw [this]
  · have hinv : IsConj (x₁ : G) ((u⁻¹ : ↥(centralizer ({(x₁ : G)} : Set G))) : G) :=
      isConj_inv_of_isConj huc (D.isConj_x₁_inv S F)
    have := D.eq_of_isConj_of_proj_eq S F hinv (D.zlift_isConj S F j)
      (by rw [map_inv, hpu, h, inv_inv, D.zlift_proj S F])
      (by rw [map_inv, hpu, h, inv_inv]; exact D.Y_ne_one S F j)
    have h2 : (u : G)⁻¹ = (D.zlift S F j : G) := congrArg Subtype.val this
    rw [← h2]
    exact zpowers_inv.symm

theorem exists_actPerm_stab_three (a b : Fin 3 → ↥(ptsAG (x₁ : G) A))
    (ha : ∀ i, a i ≠ pt0 (x₁ : G) A) (hb : ∀ i, b i ≠ pt0 (x₁ : G) A)
    (hai : Function.Injective a) (hbi : Function.Injective b) :
    ∃ k : ↥(normAG (x₁ : G) A), actPerm (x₁ : G) A k (pt0 (x₁ : G) A) = pt0 (x₁ : G) A ∧
      ∀ i, actPerm (x₁ : G) A k (a i) = b i := by
  choose ia hia using fun i => D.exists_idx S F (ha i)
  choose ib hib using fun i => D.exists_idx S F (hb i)
  have hiai : Function.Injective ia := by
    intro i j h
    apply hai
    apply Subtype.ext
    rw [hia i, hia j, h]
  have hibi : Function.Injective ib := by
    intro i j h
    apply hbi
    apply Subtype.ext
    rw [hib i, hib j, h]
  obtain ⟨g, hgN, hg⟩ := F.mcl.norm.trans3 ia ib hiai hibi
  obtain ⟨m, rfl⟩ := projQ_surjective (x₁ : G) g
  have hmN : (m : G) ∈ normAG (x₁ : G) A := (mem_normalizer_preimQ_iff m).2 hgN
  refine ⟨⟨m, hmN⟩, Subtype.ext ?_, fun i => Subtype.ext ?_⟩
  · show conjSub (m : G) (zpowers (x₁ : G)) = zpowers (x₁ : G)
    rw [conjSub_zpowers]
    have : (m : G) * (x₁ : G) * (m : G)⁻¹ = (x₁ : G) :=
      mul_inv_eq_iff_eq_mul.2 (mem_centralizer_singleton_iff.1 m.2)
    rw [this]
  · show conjSub (m : G) (a i).1 = (b i).1
    rw [hia i, hib i, conjSub_zpowers]
    exact D.zpowers_conj_zlift S F m (ia i) (ib i) (hg i)

omit [Finite G] D S F in
theorem mem_normAG_of_inverts {s : G} (hs2 : s * s = 1)
    (hsA : ∀ g ∈ preimQ (x₁ : G) A, s * g * s⁻¹ = g⁻¹) : s ∈ normAG (x₁ : G) A := by
  have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs2
  rw [mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    rw [hsA h hh]
    exact Subgroup.inv_mem _ hh
  · intro hh
    have h2 := hsA _ hh
    have h3 : s * (s * h * s⁻¹) * s⁻¹ = h := by
      rw [hsinv]
      calc s * (s * h * s) * s = (s * s) * h * (s * s) := by group
        _ = h := by rw [hs2]; group
    rw [h3] at h2
    rw [h2]
    exact Subgroup.inv_mem _ hh

omit [Finite G] in
theorem actPerm_of_mem_AG {g : G} (hg : g ∈ preimQ (x₁ : G) A)
    (hgK : g ∈ normAG (x₁ : G) A) : actPerm (x₁ : G) A ⟨g, hgK⟩ = 1 := by
  refine Equiv.ext fun ω => Subtype.ext ?_
  obtain ⟨B, hB⟩ := ω
  obtain ⟨w, hwc, hwA, rfl⟩ := mem_deltaIn_iff.1 hB
  show conjSub g (zpowers w) = zpowers w
  rw [conjSub_zpowers]
  have : g * w * g⁻¹ = w := mul_inv_eq_iff_eq_mul.2 (D.AG_comm S F g hg w hwA)
  rw [this]

omit [Finite G] D S F in
theorem actPerm_of_inverts {s : G} (hsK : s ∈ normAG (x₁ : G) A)
    (hsA : ∀ g ∈ preimQ (x₁ : G) A, s * g * s⁻¹ = g⁻¹) :
    actPerm (x₁ : G) A ⟨s, hsK⟩ = 1 := by
  refine Equiv.ext fun ω => Subtype.ext ?_
  obtain ⟨B, hB⟩ := ω
  obtain ⟨w, hwc, hwA, rfl⟩ := mem_deltaIn_iff.1 hB
  show conjSub s (zpowers w) = zpowers w
  rw [conjSub_zpowers, hsA w hwA]
  exact zpowers_inv

theorem mem_AG_or_of_fix {s : G} (hs2 : s * s = 1) (hsx : s * (x₁ : G) * s⁻¹ = (x₁ : G)⁻¹)
    (hsA : ∀ g ∈ preimQ (x₁ : G) A, s * g * s⁻¹ = g⁻¹) (k : ↥(normAG (x₁ : G) A))
    (hk0 : actPerm (x₁ : G) A k (pt0 (x₁ : G) A) = pt0 (x₁ : G) A)
    (a : Fin 3 → ↥(ptsAG (x₁ : G) A)) (ha : ∀ i, a i ≠ pt0 (x₁ : G) A)
    (hai : Function.Injective a) (hfix : ∀ i, actPerm (x₁ : G) A k (a i) = a i) :
    (k : G) ∈ preimQ (x₁ : G) A ∨ (k : G) * s ∈ preimQ (x₁ : G) A := by
  have hx3 := x₁_pow_three S
  have hx1 : (x₁ : G) ≠ 1 := by
    intro h
    have h3 := orderOf_x₁ S
    rw [h, orderOf_one] at h3
    exact absurd h3 (by norm_num)
  have hkx : (k : G) ∈ NormX (x₁ : G) := by
    have h2 : conjSub (k : G) (zpowers (x₁ : G)) = zpowers (x₁ : G) := congrArg Subtype.val hk0
    rw [conjSub_zpowers] at h2
    exact mem_normalizer_zpowers_iff'.2 h2
  have hsK : s ∈ normAG (x₁ : G) A := mem_normAG_of_inverts hs2 hsA
  have hsact := actPerm_of_inverts hsK hsA
  obtain ⟨k', hk'M, hact, hk'⟩ : ∃ k' : ↥(normAG (x₁ : G) A),
      (k' : G) ∈ centralizer ({(x₁ : G)} : Set G) ∧
        actPerm (x₁ : G) A k' = actPerm (x₁ : G) A k ∧ ((k' : G) = k ∨ (k' : G) = k * s) := by
    rcases conj_eq_or_inv hx3 hx1 hkx with h | h
    · exact ⟨k, mem_centralizer_singleton_iff.2 (mul_inv_eq_iff_eq_mul.1 h), rfl, Or.inl rfl⟩
    · refine ⟨k * ⟨s, hsK⟩, ?_, by rw [map_mul, hsact, mul_one], Or.inr rfl⟩
      have e : (k : G) * s * (x₁ : G) * ((k : G) * s)⁻¹ =
          (k : G) * (s * (x₁ : G) * s⁻¹) * (k : G)⁻¹ := by group
      have e2 : (k : G) * s * (x₁ : G) * ((k : G) * s)⁻¹ = (x₁ : G) := by
        rw [e, hsx]
        calc (k : G) * (x₁ : G)⁻¹ * (k : G)⁻¹ = ((k : G) * (x₁ : G) * (k : G)⁻¹)⁻¹ := by group
          _ = (x₁ : G) := by rw [h, inv_inv]
      exact mem_centralizer_singleton_iff.2 (mul_inv_eq_iff_eq_mul.1 e2)
  set m : ↥(centralizer ({(x₁ : G)} : Set G)) := ⟨k', hk'M⟩ with hm
  have hq : projQ (x₁ : G) m ∈ normalizer (A : Set (CentQuot (x₁ : G))) :=
    (mem_normalizer_preimQ_iff m).1 k'.2
  choose ia hia using fun i => D.exists_idx S F (ha i)
  have hiai : Function.Injective ia := by
    intro i j h
    apply hai
    apply Subtype.ext
    rw [hia i, hia j, h]
  have hqfix : ∀ i, projQ (x₁ : G) m * Y (ia i) * (projQ (x₁ : G) m)⁻¹ = Y (ia i) ∨
      projQ (x₁ : G) m * Y (ia i) * (projQ (x₁ : G) m)⁻¹ = (Y (ia i))⁻¹ := by
    intro i
    have h1 : conjSub (k' : G) (a i).1 = (a i).1 := by
      have := congrArg Subtype.val (show actPerm (x₁ : G) A k' (a i) = a i by
        rw [hact]; exact hfix i)
      exact this
    rw [hia i, conjSub_zpowers] at h1
    have hz := D.zlift_proj S F (ia i)
    rcases (zpowers_eq_iff (D.zlift_pow_three S F (ia i)) (D.zlift_ne_one S F (ia i))).1 h1
      with h3 | h3
    · left
      have : m * D.zlift S F (ia i) * m⁻¹ = D.zlift S F (ia i) := Subtype.ext h3
      calc projQ (x₁ : G) m * Y (ia i) * (projQ (x₁ : G) m)⁻¹
          = projQ (x₁ : G) (m * D.zlift S F (ia i) * m⁻¹) := by
            rw [map_mul, map_mul, map_inv, hz]
        _ = Y (ia i) := by rw [this, hz]
    · right
      have : m * D.zlift S F (ia i) * m⁻¹ = (D.zlift S F (ia i))⁻¹ := Subtype.ext h3
      calc projQ (x₁ : G) m * Y (ia i) * (projQ (x₁ : G) m)⁻¹
          = projQ (x₁ : G) (m * D.zlift S F (ia i) * m⁻¹) := by
            rw [map_mul, map_mul, map_inv, hz]
        _ = (Y (ia i))⁻¹ := by rw [this, map_inv, hz]
  have hqA : projQ (x₁ : G) m ∈ A := F.mcl.norm.sharp3 _ hq ia hiai hqfix
  have hk'A : (k' : G) ∈ preimQ (x₁ : G) A := mem_preimQ.2 ⟨hk'M, hqA⟩
  rcases hk' with h | h
  · left; rw [← h]; exact hk'A
  · right; rw [← h]; exact hk'A

theorem actPerm_eq_one_of_fix (k : ↥(normAG (x₁ : G) A))
    (hk0 : actPerm (x₁ : G) A k (pt0 (x₁ : G) A) = pt0 (x₁ : G) A)
    (a : Fin 3 → ↥(ptsAG (x₁ : G) A)) (ha : ∀ i, a i ≠ pt0 (x₁ : G) A)
    (hai : Function.Injective a) (hfix : ∀ i, actPerm (x₁ : G) A k (a i) = a i) :
    actPerm (x₁ : G) A k = 1 := by
  obtain ⟨s, hs2, -, hsx, hsA⟩ := F.inv
  have hsK : s ∈ normAG (x₁ : G) A := mem_normAG_of_inverts hs2 hsA
  have hsact := actPerm_of_inverts hsK hsA
  have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs2
  rcases D.mem_AG_or_of_fix S F hs2 hsx hsA k hk0 a ha hai hfix with h | h
  · have := D.actPerm_of_mem_AG S F h k.2
    exact this
  · have hKA : (k : G) * s ∈ normAG (x₁ : G) A := Subgroup.mul_mem _ k.2 hsK
    have h1 := D.actPerm_of_mem_AG S F h hKA
    have hk : k = ⟨(k : G) * s, hKA⟩ * ⟨s, hsK⟩ := by
      apply Subtype.ext
      show (k : G) = (k : G) * s * s
      rw [mul_assoc, hs2, mul_one]
    rw [hk, map_mul, h1, hsact, mul_one]

end LyData

end Act

end CFSG.Sporadic.Recognition.LyonsSims
