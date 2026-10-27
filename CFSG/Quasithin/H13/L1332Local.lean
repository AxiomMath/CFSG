module

public import CFSG.Quasithin.H13.L1332Inputs
public import CFSG.Quasithin.Vol2.Ch12Sec2Action
public import CFSG.Quasithin.H13.AssemblyLocal

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem eq_bot_of_perfect_of_solvable {X : Type*} [Group X] {B : Subgroup X}
    (hB : ⁅B, B⁆ = B) (hs : Group.IsSolvable B) : B = ⊥ := by
  have htop : commutator B = ⊤ := by
    apply Subgroup.map_injective B.subtype_injective
    rw [Subgroup.map_subtype_commutator, hB, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hder : ∀ n, derivedSeries B n = ⊤ := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => rw [derivedSeries_succ, ih, ← commutator_def, htop]
  obtain ⟨n, hn⟩ := hs.solvable
  rw [hder] at hn
  rw [eq_bot_iff]
  intro x hx
  have hx' : (⟨x, hx⟩ : B) ∈ (⊥ : Subgroup B) := hn ▸ Subgroup.mem_top _
  rw [Subgroup.mem_bot] at hx' ⊢
  exact congrArg Subtype.val hx'

theorem le_normalizer_of_le_of_isLocal
    (hD : LocalDoubleEmbeddingExclusion) (hs : IsSimpleGroup G)
    (hnab : ∃ a b : G, a * b ≠ b * a) (hQ : quasithinIsQTKECat G) {T K I : Subgroup G}
    (hK : quasithinIsLocal T K) (hI : quasithinIsLocal T I) (hKI : K ≤ I)
    (hTI : T ≤ Subgroup.normalizer (I : Set G)) : T ≤ Subgroup.normalizer (K : Set G) := by
  intro t ht
  have heq := local_normalizer_chain_equality hD hs hnab hQ hK hI hKI
  have hmem : t ∈ T ⊓ Subgroup.normalizer (I : Set G) := ⟨ht, hTI ht⟩
  rw [← heq] at hmem
  exact hmem.2

theorem eq_of_faithfulLocal_le
    (hD : LocalDoubleEmbeddingExclusion)
    (hodd : FiveQuotientOddIndexSolvable) (hs : IsSimpleGroup G)
    (hnab : ∃ a b : G, a * b ≠ b * a) (hQ : quasithinIsQTKECat G) {T K I : Subgroup G}
    (hT : quasithinIsSylowTwo T) (hK : quasithinIsFaithfulLocal T K)
    (hI : quasithinIsMaximalLocal T I) (hIf : quasithinIsFaithfulLocal T I) (hKI : K ≤ I)
    (hTI : T ≤ Subgroup.normalizer (I : Set G))
    (hIq : CFSG.IsQuasisimple (↥I ⧸ CFSG.pCore 2 ↥I))
    (hI5 : QT13Five (↥I ⧸ CFSG.pCore 2 ↥I)) : K = I := by
  have hTK : T ≤ Subgroup.normalizer (K : Set G) :=
    le_normalizer_of_le_of_isLocal hD hs hnab hQ hK.1 hI.1 hKI hTI
  have hK1 : K ≠ ⊥ := hK.1.2.1.1
  have hKp : ⁅K, K⁆ = K := hK.1.2.1.2.1
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥I) with hπ
  set ρ : ↥K →* ↥I ⧸ CFSG.pCore 2 ↥I := π.comp (Subgroup.inclusion hKI) with hρ
  set Kb : Subgroup (↥I ⧸ CFSG.pCore 2 ↥I) := ρ.range with hKb
  set S' : Subgroup ↥I := (T ⊓ I).subgroupOf I with hS'
  set Sb : Subgroup (↥I ⧸ CFSG.pCore 2 ↥I) := S'.map π with hSb
  have hKtop : commutator ↥K = ⊤ := by
    apply Subgroup.map_injective K.subtype_injective
    rw [Subgroup.map_subtype_commutator, hKp, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hKbp : ⁅Kb, Kb⁆ = Kb := by
    rw [hKb, MonoidHom.range_eq_map, ← Subgroup.map_commutator, ← commutator_def, hKtop]
  have hSbN : Sb ≤ Subgroup.normalizer (Kb : Set (↥I ⧸ CFSG.pCore 2 ↥I)) := by
    rintro _ ⟨s, hs', rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    have hsT : (s : G) ∈ T := (Subgroup.mem_subgroupOf.mp hs').1
    have key : ∀ (u : G), u ∈ T → ∀ (y : ↥I ⧸ CFSG.pCore 2 ↥I), y ∈ Kb →
        ∀ (w : ↥I), (w : G) = u → π w * y * (π w)⁻¹ ∈ Kb := by
      rintro u hu _ ⟨k, rfl⟩ w rfl
      have hkk : (w : G) * (k : G) * (w : G)⁻¹ ∈ K :=
        (Subgroup.mem_normalizer_iff.mp (hTK hu) k).mp k.2
      refine ⟨⟨_, hkk⟩, ?_⟩
      simp only [hρ, MonoidHom.comp_apply, ← map_mul, ← map_inv]
      congr 1
    intro y
    constructor
    · intro hy
      exact key _ hsT y hy s rfl
    · intro hy
      have h2 := key _ (T.inv_mem hsT) _ hy s⁻¹ (by simp)
      simpa [mul_assoc] using h2
  set X : Subgroup (↥I ⧸ CFSG.pCore 2 ↥I) := Kb ⊔ Sb with hX
  have hsyl : IsSylowTwoOf (T ⊓ I) I :=
    A4.isSylowTwoOf_inf_normal (isSylowTwoOf_of_quasithinIsSylowTwo hT le_sup_right)
      (le_sup_left : I ≤ I ⊔ T) (sup_le Subgroup.le_normalizer hTI)
  have hXodd : ¬ 2 ∣ X.index := by
    intro h2
    apply hsyl.2.2
    have h1 : X.index ∣ Sb.index := Subgroup.index_dvd_of_le le_sup_right
    have h3 : Sb.index ∣ S'.index := Subgroup.index_map_dvd _ (QuotientGroup.mk'_surjective _)
    exact h2.trans (h1.trans h3)
  have hKbtop : Kb = ⊤ := by
    have hsolv : Kb ≠ ⊤ → Group.IsSolvable Kb := by
      intro hne
      by_cases hXt : X = ⊤
      · have hN : Kb.Normal := by
          rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, ← hXt]
          exact sup_le Subgroup.le_normalizer hSbN
        rcases CFSG.LocalCores.quasisimple_normal_subgroups hIq hN with h | h
        · exact absurd h hne
        · have : IsMulCommutative Kb := ⟨⟨fun a b => Subtype.ext
            ((Subgroup.mem_center_iff.mp (h a.2) b).symm)⟩⟩
          infer_instance
      · have := hodd _ hI5 X hXodd hXt
        exact Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective
          (le_sup_left : Kb ≤ X))
    by_contra hne
    have hbot := eq_bot_of_perfect_of_solvable hKbp (hsolv hne)
    have hKO : ∀ k : ↥K, (Subgroup.inclusion hKI k) ∈ CFSG.pCore 2 ↥I := by
      intro k
      have : ρ k ∈ Kb := ⟨k, rfl⟩
      rw [hbot, Subgroup.mem_bot] at this
      have h' : π (Subgroup.inclusion hKI k) = 1 := this
      rwa [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h'
    have h2 : IsPGroup 2 ↥K := by
      intro k
      obtain ⟨n, hn⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥I)) ⟨_, hKO k⟩
      refine ⟨n, Subtype.ext ?_⟩
      have := congrArg (fun x : ↥(CFSG.pCore 2 ↥I) => ((x : ↥I) : G)) hn
      simpa using this
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have : Group.IsNilpotent ↥K := h2.isNilpotent
    exact hK1 (eq_bot_of_perfect_of_solvable hKp inferInstance)
  have hdecomp : ∀ x : ↥I, ∃ k : ↥K, ∃ p ∈ CFSG.pCore 2 ↥I, x = Subgroup.inclusion hKI k * p := by
    intro x
    have hx : π x ∈ Kb := hKbtop ▸ Subgroup.mem_top _
    obtain ⟨k, hk⟩ := hx
    refine ⟨k, (Subgroup.inclusion hKI k)⁻¹ * x, ?_, by group⟩
    have hk' : π (Subgroup.inclusion hKI k) = π x := hk
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hk'
    exact hk'
  have hO2T : pCoreOf 2 I ≤ T := pCoreOf_le_of_le_normalizer hT hTI
  have hIK : I ≤ Subgroup.normalizer (K : Set G) := by
    intro x hx
    obtain ⟨k, p, hp, hkp⟩ := hdecomp ⟨x, hx⟩
    have hx' : x = (k : G) * ((p : ↥I) : G) := by
      have := congrArg Subtype.val hkp
      simpa using this
    have hpT : ((p : ↥I) : G) ∈ T := by
      apply hO2T
      exact ⟨p, hp, rfl⟩
    rw [hx']
    exact Subgroup.mul_mem _ (Subgroup.le_normalizer k.2) (hTK hpT)
  have hKn : (K.subgroupOf I).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hKI).mpr hIK
  refine hIf.2.1 K hKI hKn fun x hx => ?_
  obtain ⟨k, p, hp, hkp⟩ := hdecomp ⟨x, hx⟩
  obtain ⟨n, hn⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥I)) ⟨p, hp⟩
  have hpn : p ^ 2 ^ n = 1 := by
    have := congrArg Subtype.val hn
    simpa using this
  refine ⟨n, ?_⟩
  set q := QuotientGroup.mk' (K.subgroupOf I) with hq
  have hqk : q (Subgroup.inclusion hKI k) = 1 := by
    rw [hq, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact k.2
  have hqx : q ⟨x, hx⟩ ^ 2 ^ n = 1 := by
    rw [hkp, map_mul, hqk, one_mul, ← map_pow, hpn, map_one]
  rw [← map_pow, hq, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
    Subgroup.mem_subgroupOf] at hqx
  simpa using hqx

end CFSG.Quasithin.H13
