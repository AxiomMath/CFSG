module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineBRedPair
public import CFSG.LocalAnalysis.WeakClosure81.NineCalP
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineBDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.NG915

open Subgroup CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.WeakClosure81

variable {G : Type} [Group G]

section Bar

variable {N : Subgroup G} {Z : Type*} [Group Z]

theorem map_subgroupOf_map_conj (ψ : ↥N →* Z) (A : Subgroup G) (g : ↥N) :
    ((A.map (MulAut.conj (g : G)).toMonoidHom).subgroupOf N).map ψ =
      ((A.subgroupOf N).map ψ).map (MulAut.conj (ψ g)).toMonoidHom := by
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [SetLike.mem_coe, mem_subgroupOf] at hy
    obtain ⟨a, ha, hay⟩ := mem_map.mp hy
    have hay' : (g : G) * a * (g : G)⁻¹ = y := hay
    have haN : a ∈ N := by
      have e : a = (g : G)⁻¹ * (y : G) * g := by rw [← hay']; group
      rw [e]
      exact N.mul_mem (N.mul_mem (N.inv_mem g.2) y.2) g.2
    refine ⟨ψ ⟨a, haN⟩, mem_map_of_mem ψ (by rw [mem_subgroupOf]; exact ha), ?_⟩
    have e : y = g * ⟨a, haN⟩ * g⁻¹ := Subtype.ext (by rw [← hay']; simp)
    rw [e, map_mul, map_mul, map_inv]
    simp
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨g * x * g⁻¹, ?_, by simp⟩
    rw [SetLike.mem_coe, mem_subgroupOf]
    exact ⟨x, hx, by simp⟩

theorem mem_sup_pCoreOf_iff (ψ : ↥N →* Z) (hψk : ∀ x : ↥N, ψ x = 1 ↔ (x : G) ∈ pCoreOf 2 N)
    {A : Subgroup G} (hA : A ≤ N) (x : ↥N) :
    (x : G) ∈ A ⊔ pCoreOf 2 N ↔ ψ x ∈ (A.subgroupOf N).map ψ := by
  constructor
  · intro hx
    have h1 : x ∈ (A ⊔ pCoreOf 2 N).subgroupOf N := hx
    rw [subgroupOf_sup hA (CFSG.LieType.BorelTits.pCoreOf_le 2 N)] at h1
    have h2 : A.subgroupOf N ⊔ (pCoreOf 2 N).subgroupOf N ≤ ((A.subgroupOf N).map ψ).comap ψ :=
      sup_le (le_comap_map _ _) fun q hq => by
        rw [mem_comap, (hψk q).mpr hq]
        exact one_mem _
    exact h2 h1
  · rintro ⟨a, ha, hax⟩
    have h1 : ψ (a⁻¹ * x) = 1 := by rw [map_mul, map_inv, hax, inv_mul_cancel]
    have h2 := (hψk _).mp h1
    have e : (x : G) = a * ((a⁻¹ * x : ↥N) : G) := by simp
    rw [e]
    exact mul_mem (mem_sup_left ha) (mem_sup_right h2)

theorem map_subgroupOf_conjSubgroup (ψ : ↥N →* Z) (A : Subgroup G) {t : G} (ht : t ∈ N) :
    ((conjSubgroup A t).subgroupOf N).map ψ =
      ((A.subgroupOf N).map ψ).map (MulAut.conj (ψ ⟨t⁻¹, N.inv_mem ht⟩)).toMonoidHom := by
  rw [← map_subgroupOf_map_conj]
  rfl

theorem map_sup_eq_top {T L : Subgroup G} (hN : N = T ⊔ L) (ψ : ↥N →* Z)
    (hψs : Function.Surjective ψ) : (L.subgroupOf N).map ψ ⊔ (T.subgroupOf N).map ψ = ⊤ := by
  have hLN : L ≤ N := by rw [hN]; exact le_sup_right
  have hTN : T ≤ N := by rw [hN]; exact le_sup_left
  have htop : L.subgroupOf N ⊔ T.subgroupOf N = ⊤ := by
    apply Subgroup.map_injective N.subtype_injective
    rw [Subgroup.map_sup, Subgroup.map_top, Subgroup.range_subtype,
      Subgroup.map_subgroupOf_eq_of_le hLN, Subgroup.map_subgroupOf_eq_of_le hTN, sup_comm, ← hN]
  rw [← Subgroup.map_sup, htop, Subgroup.map_top, MonoidHom.range_eq_top_of_surjective ψ hψs]

theorem map_conj_eq_or_eq_of_perm {T L L₂ : Subgroup G} (ψ : ↥N →* Z)
    (hperm : ∀ t ∈ T, conjSubgroup L t = L ∨ conjSubgroup L t = L₂) :
    ∀ s ∈ (T.subgroupOf N).map ψ,
      ((L.subgroupOf N).map ψ).map (MulAut.conj s).toMonoidHom = (L.subgroupOf N).map ψ ∨
        ((L.subgroupOf N).map ψ).map (MulAut.conj s).toMonoidHom = (L₂.subgroupOf N).map ψ := by
  rintro _ ⟨s, hs, rfl⟩
  have hs' : (s : G) ∈ T := hs
  have e : L.map (MulAut.conj (s : G)).toMonoidHom = conjSubgroup L (s : G)⁻¹ := by
    rw [CFSG.Quasithin.conjSubgroup, inv_inv]
  rw [← map_subgroupOf_map_conj, e]
  rcases hperm _ (T.inv_mem hs') with h | h
  · exact Or.inl (by rw [h])
  · exact Or.inr (by rw [h])

theorem map_ne_map_conjSubgroup [Finite G] {L : Subgroup G}
    (hL : L = perfectCore (L ⊔ pCoreOf 2 N)) (hLN : L ≤ N) {t : G} (ht : t ∈ N)
    (hne : L ≠ conjSubgroup L t) (ψ : ↥N →* Z)
    (hψk : ∀ x : ↥N, ψ x = 1 ↔ (x : G) ∈ pCoreOf 2 N) :
    (L.subgroupOf N).map ψ ≠ ((conjSubgroup L t).subgroupOf N).map ψ := by
  intro heq
  apply hne
  have hLperf : ⁅L, L⁆ = L := by
    have h := perfectCore_perfect (L ⊔ pCoreOf 2 N)
    rw [← hL] at h
    exact h
  have hL2perf : ⁅conjSubgroup L t, conjSubgroup L t⁆ = conjSubgroup L t := by
    rw [CFSG.Quasithin.conjSubgroup, ← Subgroup.map_commutator, hLperf]
  have hL2N : conjSubgroup L t ≤ N := (E3.conjSubgroup_mono_left t hLN).trans_eq
    (conjSubgroup_eq_iff_mem_normalizer.2 (le_normalizer ht))
  have hle : conjSubgroup L t ≤ L ⊔ pCoreOf 2 N := fun y hy => by
    have h1 : ψ ⟨y, hL2N hy⟩ ∈ ((conjSubgroup L t).subgroupOf N).map ψ :=
      mem_map_of_mem ψ (by rw [mem_subgroupOf]; exact hy)
    rw [← heq] at h1
    exact (mem_sup_pCoreOf_iff ψ hψk hLN ⟨y, hL2N hy⟩).mpr h1
  have hle' : conjSubgroup L t ≤ L := by
    have h := le_perfectCore_of_perfect hle hL2perf
    rwa [← hL] at h
  have hcard : Nat.card L = Nat.card (conjSubgroup L t) := by
    rw [CFSG.Quasithin.conjSubgroup, Subgroup.card_map_of_injective (MulAut.conj t⁻¹).injective]
  exact (Subgroup.eq_of_le_of_card_ge hle' hcard.le).symm

end Bar

theorem pCoreOf_le_normalizer_of_eq_perfectCore {N L : Subgroup G}
    (hL : L = perfectCore (L ⊔ pCoreOf 2 N)) : pCoreOf 2 N ≤ normalizer (L : Set G) := by
  have h := normalizer_le_normalizer_perfectCore (L ⊔ pCoreOf 2 N)
  rw [← hL] at h
  exact le_sup_right.trans (le_normalizer.trans h)

theorem pCoreOf_le_normalizer_conjSubgroup {N A : Subgroup G}
    (hA : pCoreOf 2 N ≤ normalizer (A : Set G)) {t : G} (ht : t ∈ N) :
    pCoreOf 2 N ≤ normalizer (conjSubgroup A t : Set G) := by
  intro q hq
  rw [← WeakClosure81.conjSubgroup_normalizer, mem_conjSubgroup_iff]
  exact hA ((mem_normalizer_iff.mp (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 N ht) q).mp hq)

theorem mem_of_mem_sup_pCoreOf [Finite G] {N A : Subgroup G}
    (hnorm : pCoreOf 2 N ≤ normalizer (A : Set G)) {y : G} (hy : y ∈ A ⊔ pCoreOf 2 N)
    (hord : orderOf y = 3) : y ∈ A := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hAH : A ≤ A ⊔ pCoreOf 2 N := le_sup_left
  have hQH : pCoreOf 2 N ≤ A ⊔ pCoreOf 2 N := le_sup_right
  have hAn : (A.subgroupOf (A ⊔ pCoreOf 2 N)).Normal :=
    (normal_subgroupOf_iff_le_normalizer hAH).mpr (sup_le le_normalizer hnorm)
  have hQ2 : IsPGroup 2 ((pCoreOf 2 N).subgroupOf (A ⊔ pCoreOf 2 N)) :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 N).of_equiv (subgroupOfEquivOfLe hQH).symm
  have hsup : A.subgroupOf (A ⊔ pCoreOf 2 N) ⊔ (pCoreOf 2 N).subgroupOf (A ⊔ pCoreOf 2 N) = ⊤ := by
    rw [← subgroupOf_sup hAH hQH, subgroupOf_self]
  have hq := NF914.isPGroup_quotient_of_sup_eq_top hQ2 hsup
  set w := QuotientGroup.mk' (A.subgroupOf (A ⊔ pCoreOf 2 N)) ⟨y, hy⟩ with hw
  obtain ⟨k, hk⟩ := hq w
  have h3 : w ^ 3 = 1 := by
    have e : (⟨y, hy⟩ : ↥(A ⊔ pCoreOf 2 N)) ^ 3 = 1 :=
      Subtype.ext (by rw [Subgroup.coe_pow, ← hord, pow_orderOf_eq_one, Subgroup.coe_one])
    rw [hw, ← map_pow, e, map_one]
  have h1 : w = 1 := (pow_eq_one_iff_of_coprime (Nat.Coprime.pow_left k (by norm_num))).mp ⟨hk, h3⟩
  have h2 : (⟨y, hy⟩ : ↥(A ⊔ pCoreOf 2 N)) ∈ A.subgroupOf (A ⊔ pCoreOf 2 N) :=
    (QuotientGroup.eq_one_iff (⟨y, hy⟩ : ↥(A ⊔ pCoreOf 2 N))).mp h1
  exact h2

theorem exists_conj_mem_of_isSylowIn [Finite G] {X N : Subgroup G} (hX : IsSylowIn 3 X N)
    {x : G} (hxN : x ∈ N) (hord : orderOf x = 3) : ∃ n ∈ N, n * x * n⁻¹ ∈ X := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hE : IsPGroup 3 (zpowers (⟨x, hxN⟩ : ↥N)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, Subgroup.orderOf_mk, hord, pow_one])
  obtain ⟨Q, hQ⟩ := hE.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (↥N) hX.toSylow Q
  have hxQ : (⟨x, hxN⟩ : ↥N) ∈ (Q : Set ↥N) := hQ (mem_zpowers _)
  rw [← hg, Sylow.coe_smul] at hxQ
  obtain ⟨y, hy, hyx⟩ := Set.mem_smul_set.1 hxQ
  have hyX : ((y : ↥N) : G) ∈ X := by
    have h : y ∈ (hX.toSylow : Subgroup ↥N) := hy
    rw [IsSylowIn.coe_toSylow, mem_subgroupOf] at h
    exact h
  refine ⟨((g⁻¹ : ↥N) : G), (g⁻¹ : ↥N).2, ?_⟩
  have e : (⟨x, hxN⟩ : ↥N) = g * y * g⁻¹ := by
    rw [← hyx]
    simp [MulAut.smul_def, MulAut.conj_apply]
  have e' : x = (g : G) * y * (g : G)⁻¹ := by
    have := congrArg Subtype.val e
    simpa using this
  rw [e']
  simpa [mul_assoc] using hyX

theorem star915_of_fixSwap [Finite G] {V N L₁ L₂ X : Subgroup G}
    (hNM : N ≤ normalizer (V : Set G)) {Z : Type*} [Group Z] (ψ : ↥N →* Z)
    (hψk : ∀ x : ↥N, ψ x = 1 ↔ (x : G) ∈ pCoreOf 2 N) (hL1N : L₁ ≤ N) (hL2N : L₂ ≤ N)
    (hn1 : pCoreOf 2 N ≤ normalizer (L₁ : Set G)) (hn2 : pCoreOf 2 N ≤ normalizer (L₂ : Set G))
    (hX : IsSylowIn 3 X N) (hX1 : X ⊓ L₁ ∈ calP V) (hX2 : X ⊓ L₂ ∈ calP V)
    (hfs : ∀ z : Z,
      (((L₁.subgroupOf N).map ψ).map (MulAut.conj z).toMonoidHom = (L₁.subgroupOf N).map ψ ∧
          ((L₂.subgroupOf N).map ψ).map (MulAut.conj z).toMonoidHom = (L₂.subgroupOf N).map ψ) ∨
        (((L₁.subgroupOf N).map ψ).map (MulAut.conj z).toMonoidHom = (L₂.subgroupOf N).map ψ ∧
          ((L₂.subgroupOf N).map ψ).map (MulAut.conj z).toMonoidHom =
            (L₁.subgroupOf N).map ψ)) :
    Star915 V N L₁ L₂ := by
  intro g hg hVg x hx hxL hord
  obtain ⟨hxN, hxg⟩ := mem_inf.mp hx
  obtain ⟨n, hnN, hy⟩ := exists_conj_mem_of_isSylowIn hX hxN hord
  obtain ⟨B, hBL, hxB⟩ : ∃ B : Subgroup G, (B = L₁ ∨ B = L₂) ∧
      ψ ⟨x, hxN⟩ ∈ (B.subgroupOf N).map ψ := by
    rcases hxL with h | h
    · exact ⟨L₁, Or.inl rfl, (mem_sup_pCoreOf_iff ψ hψk hL1N ⟨x, hxN⟩).mp h⟩
    · exact ⟨L₂, Or.inr rfl, (mem_sup_pCoreOf_iff ψ hψk hL2N ⟨x, hxN⟩).mp h⟩
  have hyB : ψ (⟨n, hnN⟩ * ⟨x, hxN⟩ * ⟨n, hnN⟩⁻¹) ∈
      ((B.subgroupOf N).map ψ).map (MulAut.conj (ψ ⟨n, hnN⟩)).toMonoidHom :=
    ⟨ψ ⟨x, hxN⟩, hxB, by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_inv]⟩
  obtain ⟨A, hAL, hAeq⟩ : ∃ A : Subgroup G, (A = L₁ ∨ A = L₂) ∧
      ((B.subgroupOf N).map ψ).map (MulAut.conj (ψ ⟨n, hnN⟩)).toMonoidHom =
        (A.subgroupOf N).map ψ := by
    have hB' : (B.subgroupOf N).map ψ = (L₁.subgroupOf N).map ψ ∨
        (B.subgroupOf N).map ψ = (L₂.subgroupOf N).map ψ := by
      rcases hBL with h | h <;> rw [h] <;> simp
    rcases map_conj_eq_or_eq hfs (ψ ⟨n, hnN⟩) hB' with h | h
    · exact ⟨L₁, Or.inl rfl, h⟩
    · exact ⟨L₂, Or.inr rfl, h⟩
  rw [hAeq] at hyB
  have hAN : A ≤ N := by rcases hAL with h | h <;> rw [h] <;> assumption
  have hnA : pCoreOf 2 N ≤ normalizer (A : Set G) := by
    rcases hAL with h | h <;> rw [h] <;> assumption
  have hXA : X ⊓ A ∈ calP V := by rcases hAL with h | h <;> rw [h] <;> assumption
  have hyA' := (mem_sup_pCoreOf_iff ψ hψk hAN _).mpr hyB
  have hyA : n * x * n⁻¹ ∈ A := by
    refine mem_of_mem_sup_pCoreOf hnA (by simpa using hyA') ?_
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, hord]
  obtain ⟨-, -, -, -, -, -, hcap⟩ := calP_conj hXA (hNM hnN)
  have hmem : x ∈ conjSubgroup (X ⊓ A) n ⊓ conjSubgroup (normalizer (V : Set G)) g := by
    refine mem_inf.mpr ⟨mem_conjSubgroup_iff.mpr (mem_inf.mpr ⟨hy, hyA⟩), ?_⟩
    rw [WeakClosure81.conjSubgroup_normalizer]
    exact hxg
  rw [hcap g hg hVg, mem_bot] at hmem
  rw [hmem, orderOf_one] at hord
  exact absurd hord (by norm_num)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.NG915
