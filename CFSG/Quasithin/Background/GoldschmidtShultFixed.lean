module

public import CFSG.Quasithin.Background.GoldschmidtShultStatements

public section

namespace CFSG.Quasithin.Shult

open CFSG.Open CFSG.QuasithinUnique

variable {G : Type*} [Group G]

theorem smul_mk_eq_iff {M : Subgroup G} (v g : G) :
    v • (QuotientGroup.mk g : G ⧸ M) = QuotientGroup.mk g ↔ g⁻¹ * v * g ∈ M := by
  rw [MulAction.Quotient.smul_mk, eq_comm, QuotientGroup.eq, smul_eq_mul, ← mul_assoc]

theorem existsUnique_fixed_iff {M : Subgroup G} {v : G} (hv : v ∈ M) :
    (∃! c : G ⧸ M, v • c = c) ↔ ∀ g : G, g⁻¹ * v * g ∈ M → g ∈ M := by
  have h1 : v • (QuotientGroup.mk 1 : G ⧸ M) = QuotientGroup.mk 1 := by
    rw [smul_mk_eq_iff]
    simpa using hv
  constructor
  · rintro ⟨c, -, huniq⟩ g hg
    have hg' : v • (QuotientGroup.mk g : G ⧸ M) = QuotientGroup.mk g :=
      (smul_mk_eq_iff v g).2 hg
    have h := (huniq _ hg').trans (huniq _ h1).symm
    have h' := QuotientGroup.eq.1 h
    simpa using M.inv_mem h'
  · intro h
    refine ⟨QuotientGroup.mk 1, h1, fun c hc => ?_⟩
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective c
    have hgM : g ∈ M := h g ((smul_mk_eq_iff v g).1 hc)
    exact QuotientGroup.eq.2 (by simpa using M.inv_mem hgM)

variable {M V : Subgroup G}

theorem ShultI85Hyp.key (h : ShultI85Hyp M V) :
    ∀ v ∈ V, v ≠ 1 → ∀ g : G, g⁻¹ * v * g ∈ M → g ∈ M := by
  obtain ⟨-, -, hVM, -, -, hfix⟩ := h
  intro v hv hv1
  exact (existsUnique_fixed_iff (hVM hv)).1 (hfix v hv hv1)

theorem ShultI85Hyp.normalizer_eq (h : ShultI85Hyp M V) :
    Subgroup.normalizer (V : Set G) = M := by
  apply le_antisymm
  · intro g hg
    obtain ⟨⟨v, hv⟩, hv1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp h.2.1
    refine h.key v hv (fun e => hv1 (Subtype.ext e)) g ?_
    have := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (V : Set G)).inv_mem hg) v).mp
      hv
    rw [inv_inv] at this
    exact h.2.2.1 this
  · exact (Subgroup.normal_subgroupOf_iff_le_normalizer h.2.2.1).1 h.2.2.2.1

theorem inv_mul_mul_mem_of_mem_normalizer {g a : G} (hg : g ∈ Subgroup.normalizer (V : Set G))
    (ha : a ∈ V) : g⁻¹ * a * g ∈ V := by
  have := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (V : Set G)).inv_mem hg) a).mp ha
  rwa [inv_inv] at this

theorem ShultI85Hyp.not_normal (h : ShultI85Hyp M V) : ¬ V.Normal := by
  intro hN
  obtain ⟨⟨v, hv⟩, hv1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp h.2.1
  refine h.1 (Subgroup.eq_top_iff' M |>.2 fun g => ?_)
  refine h.key v hv (fun e => hv1 (Subtype.ext e)) g ?_
  exact h.2.2.1 (hN.conj_mem' v hv g)

theorem ShultI85Hyp.isTI (h : ShultI85Hyp M V) : fusionIsTI V := by
  intro g hg
  by_contra hne
  apply hg
  obtain ⟨⟨x, hxmem⟩, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  obtain ⟨y, hyV, hyx⟩ := Subgroup.mem_map.mp hxmem.2
  have hxy : g⁻¹ * x * g = y := by
    rw [← hyx]
    simp [MulAut.conj_apply, mul_assoc]
  have hgM : g ∈ M := by
    refine h.key x hxmem.1 (fun e => hx1 (Subtype.ext e)) g ?_
    rw [hxy]
    exact h.2.2.1 hyV
  rw [← h.normalizer_eq] at hgM
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hgM w).mp hw
  · intro hz
    exact ⟨g⁻¹ * z * g, inv_mul_mul_mem_of_mem_normalizer hgM hz, by simp [MulAut.conj_apply,
      mul_assoc]⟩

theorem ShultI85Hyp.stronglyClosed (h : ShultI85Hyp M V) {T : Subgroup G} (hTM : T ≤ M) :
    fusionStronglyClosed (V : Set G) T := by
  intro a ha g hg
  by_cases ha1 : a = 1
  · subst ha1
    simp
  · have hgM : g ∈ M := h.key a ha ha1 g (hTM hg)
    rw [← h.normalizer_eq] at hgM
    exact inv_mul_mul_mem_of_mem_normalizer hgM ha

variable [Finite G]

theorem ShultI85Hyp.index_odd (h : ShultI85Hyp M V) : Odd M.index := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨⟨v, hv⟩, hv1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp h.2.1
  have hv1' : v ≠ 1 := fun e => hv1 (Subtype.ext e)
  have hord : orderOf v = 2 := orderOf_eq_prime (h.2.2.2.2.1.2 v hv) hv1'
  have hp : IsPGroup 2 (Subgroup.zpowers v) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hord]; norm_num)
  obtain ⟨c₀, hc₀, huniq⟩ := h.2.2.2.2.2 v hv hv1'
  have hfp : MulAction.fixedPoints (Subgroup.zpowers v) (G ⧸ M) = {c₀} := by
    ext c
    simp only [MulAction.mem_fixedPoints, Set.mem_singleton_iff]
    constructor
    · intro hc
      exact huniq c (hc ⟨v, Subgroup.mem_zpowers v⟩)
    · intro hc m
      rw [hc]
      have hle : Subgroup.zpowers v ≤ MulAction.stabilizer G c₀ :=
        Subgroup.zpowers_le.mpr (MulAction.mem_stabilizer_iff.mpr hc₀)
      exact MulAction.mem_stabilizer_iff.mp (hle m.2)
  have hmod := hp.card_modEq_card_fixedPoints (G ⧸ M)
  have h1 : Nat.card ↥({c₀} : Set (G ⧸ M)) = 1 := Nat.card_unique
  rw [hfp, h1] at hmod
  rw [Subgroup.index_eq_card]
  exact Nat.odd_iff.mpr hmod

theorem ShultI85Hyp.exists_sylow (h : ShultI85Hyp M V) :
    ∃ T : Sylow 2 G, V ≤ (T : Subgroup G) ∧ (T : Subgroup G) ≤ M := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow 2 ↥M))
  let P' : Subgroup G := (P : Subgroup ↥M).map M.subtype
  have hP'le : P' ≤ M := Subgroup.map_subtype_le _
  have hP'p : IsPGroup 2 P' := by
    intro x
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp x.2
    obtain ⟨k, hk⟩ := P.isPGroup' ⟨y, hy⟩
    have h2 : y ^ 2 ^ k = 1 := by
      have := congrArg (fun z : ↥(P : Subgroup ↥M) => (z : ↥M)) hk
      simpa using this
    refine ⟨k, Subtype.ext ?_⟩
    rw [Subgroup.coe_pow, Subgroup.coe_one, ← hyx, ← map_pow, h2, map_one]
  have hrel : P'.relIndex M * M.index = P'.index := Subgroup.relIndex_mul_index hP'le
  have hrel' : P'.relIndex M = (P : Subgroup ↥M).index := by
    unfold Subgroup.relIndex Subgroup.subgroupOf
    rw [Subgroup.comap_map_eq_self_of_injective M.subtype_injective]
  have hindex : ¬ 2 ∣ P'.index := by
    rw [← hrel, hrel']
    have h1 : ¬ 2 ∣ (P : Subgroup ↥M).index := P.not_dvd_index
    have h2 : ¬ 2 ∣ M.index := by
      have := h.index_odd
      rwa [← even_iff_two_dvd, ← Nat.not_odd_iff_even, not_not]
    exact fun hd => (Nat.Prime.dvd_mul Nat.prime_two).1 hd |>.elim h1 h2
  refine ⟨hP'p.toSylow hindex, ?_, hP'le⟩
  have hVp : IsPGroup 2 (V.subgroupOf M) := by
    intro g
    refine ⟨1, ?_⟩
    have hg : ((g : M) : G) ^ 2 = 1 := h.2.2.2.2.1.2 _ g.2
    apply Subtype.ext
    apply Subtype.ext
    simpa using hg
  have hVn : (V.subgroupOf M).Normal := h.2.2.2.1
  have hle : V.subgroupOf M ≤ (P : Subgroup ↥M) := hVp.le_sylow_of_normal P
  intro x hx
  have hxM : x ∈ M := h.2.2.1 hx
  exact ⟨⟨x, hxM⟩, hle (Subgroup.mem_subgroupOf.mpr hx), rfl⟩

theorem ShultI85Hyp.shult_hypotheses (h : ShultI85Hyp M V) :
    ∃ T : Sylow 2 G, V ≤ (T : Subgroup G) ∧ (T : Subgroup G) ≤ M ∧
      fusionStronglyClosed (V : Set G) (T : Subgroup G) ∧ fusionIsTI V ∧ ¬ V.Normal := by
  obtain ⟨T, hVT, hTM⟩ := h.exists_sylow
  exact ⟨T, hVT, hTM, h.stronglyClosed hTM, h.isTI, h.not_normal⟩

end CFSG.Quasithin.Shult
