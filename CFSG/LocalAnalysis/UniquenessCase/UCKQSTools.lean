module

public import CFSG.LocalAnalysis.UniquenessCase.UC6N588A1

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK

open Subgroup CFSG.ABGLocalTools

@[expose] def PCentralAbelianAt (K : Type) [Group K] [Finite K] (p : ℕ) : Prop :=
  ∀ T : Subgroup K, IsSylowOf p T ⊤ → (∀ x ∈ T, x ^ p = 1 → ∀ y ∈ T, x * y = y * x) →
    CFSG.Open.pRank p T ≤ 3 → IsMulCommutative T

section Transfer

theorem pca_pcentral_of_map {G K : Type} [Group G] [Group K] {p : ℕ} (f : G →* K) {T : Subgroup G}
    (hinj : ∀ x ∈ T, f x = 1 → x = 1)
    (hcen : ∀ x ∈ T.map f, x ^ p = 1 → ∀ y ∈ T.map f, x * y = y * x) :
    ∀ x ∈ T, x ^ p = 1 → ∀ y ∈ T, x * y = y * x := by
  intro x hx hxp y hy
  have h := hcen (f x) (mem_map_of_mem f hx) (by rw [← map_pow, hxp, map_one]) (f y) (mem_map_of_mem f hy)
  have h1 : f (x * y * (y * x)⁻¹) = 1 := by rw [map_mul, map_mul, map_inv, map_mul, h, mul_inv_cancel]
  have h2 := hinj _ (T.mul_mem (T.mul_mem hx hy) (T.inv_mem (T.mul_mem hy hx))) h1
  exact mul_inv_eq_one.mp h2

theorem pca_pcentral_map {G K : Type} [Group G] [Group K] {p : ℕ} (f : G →* K) {T : Subgroup G}
    (hinj : ∀ x ∈ T, f x = 1 → x = 1) (hcen : ∀ x ∈ T, x ^ p = 1 → ∀ y ∈ T, x * y = y * x) :
    ∀ x ∈ T.map f, x ^ p = 1 → ∀ y ∈ T.map f, x * y = y * x := by
  rintro _ ⟨x, hx, rfl⟩ hxp _ ⟨y, hy, rfl⟩
  have hxp' : x ^ p = 1 := hinj _ (T.pow_mem hx p) (by rw [map_pow, hxp])
  rw [← map_mul, ← map_mul, hcen x hx hxp' y hy]

theorem pca_comm_map {G K : Type} [Group G] [Group K] (f : G →* K) {T : Subgroup G}
    (h : IsMulCommutative T) : IsMulCommutative (T.map f) := by
  rw [isMulCommutative_iff] at h ⊢
  rintro ⟨_, x, hx, rfl⟩ ⟨_, y, hy, rfl⟩
  apply Subtype.ext
  have := congrArg Subtype.val (h ⟨x, hx⟩ ⟨y, hy⟩)
  simp only [Subgroup.coe_mul] at this ⊢
  rw [← map_mul, ← map_mul, this]

theorem pca_comm_of_map {G K : Type} [Group G] [Group K] (f : G →* K) (hf : Function.Injective f)
    {T : Subgroup G} (h : IsMulCommutative (T.map f)) : IsMulCommutative T := by
  rw [isMulCommutative_iff] at h ⊢
  intro a b
  have := congrArg Subtype.val (h ⟨f a, mem_map_of_mem f a.2⟩ ⟨f b, mem_map_of_mem f b.2⟩)
  simp only [Subgroup.coe_mul] at this
  rw [← map_mul, ← map_mul] at this
  exact Subtype.ext (hf this)

theorem pca_pRank_le_map {G K : Type} [Group G] [Finite G] [Group K] [Finite K] {p : ℕ} (hp : 1 < p)
    (f : G →* K) {T : Subgroup G} (hinj : ∀ x ∈ T, f x = 1 → x = 1) :
    CFSG.Open.pRank p T ≤ CFSG.Open.pRank p (T.map f) := by
  obtain ⟨E, hET, hE, hcard⟩ := CFSG.SectionRank.exists_pRank hp T
  have hE' := hE
  obtain ⟨hcomm, hpow⟩ := hE'
  rw [isMulCommutative_iff] at hcomm
  have hginj : Function.Injective (f.comp E.subtype) := by
    rw [injective_iff_map_eq_one]
    intro a ha
    exact Subtype.ext (hinj _ (hET a.2) ha)
  refine CFSG.SectionRank.le_pRank_of_injective hp hcomm (fun a => Subtype.ext (hpow _ a.2)) hcard
    (f.comp E.subtype) hginj ?_
  rintro _ ⟨a, rfl⟩
  exact mem_map_of_mem f (hET a.2)

theorem pca_pRank_map_le {G K : Type} [Group G] [Finite G] [Group K] [Finite K] {p : ℕ} (hp : 1 < p)
    (f : G →* K) (hf : Function.Injective f) (H : Subgroup G) :
    CFSG.Open.pRank p (H.map f) ≤ CFSG.Open.pRank p H := by
  obtain ⟨E, hEH, hE, hcard⟩ := CFSG.SectionRank.exists_pRank hp (H.map f)
  have hEle : E ≤ f.range := hEH.trans (map_le_range f H)
  have hEc : (E.comap f).map f = E := Subgroup.map_comap_eq_self hEle
  refine CFSG.SectionRank.le_pRank hp (H := H) (E := E.comap f) ?_ ?_ ?_
  · intro x hx
    obtain ⟨h, hh, hhx⟩ := hEH hx
    rwa [← hf hhx]
  · obtain ⟨hcomm, hpow⟩ := hE
    rw [isMulCommutative_iff] at hcomm
    refine ⟨⟨⟨fun a b => Subtype.ext (hf ?_)⟩⟩, fun x hx => hf (by rw [map_pow, hpow _ hx, map_one])⟩
    have := congrArg Subtype.val (hcomm ⟨f a, a.2⟩ ⟨f b, b.2⟩)
    simpa only [Subgroup.coe_mul, map_mul] using this
  · rw [← hcard, ← hEc, Subgroup.card_map_of_injective hf, hEc]

end Transfer

section Sylow

theorem pca_exists_conj_mem {K : Type} [Group K] [Finite K] {p : ℕ} [Fact p.Prime] {T U : Subgroup K}
    (hT : IsSylowOf p T ⊤) (hU : IsPGroup p U) : ∃ g : K, ∀ u ∈ U, g * u * g⁻¹ ∈ T := by
  obtain ⟨g, hg⟩ := N588A.exists_le_conjugate hT hU
  exact ⟨g, fun u hu => N588A.mem_conjugate_iff.mp (hg hu)⟩

theorem pca_comm_of_pow_eq_one {K : Type} [Group K] [Finite K] {p : ℕ} [Fact p.Prime] {T U : Subgroup K}
    (hT : IsSylowOf p T ⊤) (hcen : ∀ x ∈ T, x ^ p = 1 → ∀ y ∈ T, x * y = y * x) (hU : IsPGroup p U)
    {x y : K} (hx : x ∈ U) (hy : y ∈ U) (hxp : x ^ p = 1) : x * y = y * x := by
  obtain ⟨g, hg⟩ := pca_exists_conj_mem hT hU
  have h := hcen _ (hg x hx) (by rw [conj_pow, hxp, mul_one, mul_inv_cancel]) _ (hg y hy)
  apply (MulAut.conj g).injective
  simp only [map_mul, MulAut.conj_apply]
  exact h

namespace PCentralAbelianAt

theorem of_sylow {K : Type} [Group K] [Finite K] {p : ℕ} [Fact p.Prime] (P : Sylow p K)
    (h : (∀ x ∈ (P : Subgroup K), x ^ p = 1 → ∀ y ∈ (P : Subgroup K), x * y = y * x) →
      CFSG.Open.pRank p (P : Subgroup K) ≤ 3 → IsMulCommutative (P : Subgroup K)) :
    PCentralAbelianAt K p := by
  intro T hT hcen hrk
  obtain ⟨Q, rfl⟩ := N588A.exists_sylow_of_isSylowOf_top hT
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq K P Q
  have hQ : (Q : Subgroup K) = (P : Subgroup K).map (MulAut.conj g).toMonoidHom := by
    rw [← hg, Sylow.coe_subgroup_smul]
    rfl
  have hinj : ∀ x ∈ (P : Subgroup K), (MulAut.conj g).toMonoidHom x = 1 → x = 1 :=
    fun x _ hx => (MulAut.conj g).injective (by rw [map_one]; exact hx)
  rw [hQ] at hcen hrk ⊢
  have hrk' := (pca_pRank_le_map (Fact.out : p.Prime).one_lt _ hinj).trans hrk
  exact pca_comm_map _ (h (pca_pcentral_of_map _ hinj hcen) hrk')

theorem of_mulEquiv {K L : Type} [Group K] [Finite K] [Group L] [Finite L] {p : ℕ} [Fact p.Prime] (e : K ≃* L)
    (h : PCentralAbelianAt L p) : PCentralAbelianAt K p := by
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow p K))
  refine of_sylow P fun hcen hrk => ?_
  have hinj : ∀ x ∈ (P : Subgroup K), e.toMonoidHom x = 1 → x = 1 :=
    fun x _ hx => e.injective (by rw [map_one]; exact hx)
  have hS : IsSylowOf p ((P : Subgroup K).map e.toMonoidHom) ⊤ :=
    N588A.isSylowOf_top_of_sylow (P.mapSurjective (f := e.toMonoidHom) e.surjective)
  have hc := h _ hS (pca_pcentral_map _ hinj hcen)
    ((pca_pRank_map_le (Fact.out : p.Prime).one_lt _ e.injective _).trans hrk)
  exact pca_comm_of_map _ e.injective hc

theorem of_surjective_coprime_ker {G K : Type} [Group G] [Finite G] [Group K] [Finite K] {p : ℕ} [Fact p.Prime]
    (f : G →* K) (hf : Function.Surjective f) (hker : ¬ p ∣ Nat.card f.ker) (h : PCentralAbelianAt G p) :
    PCentralAbelianAt K p := by
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow p G))
  have hinj : ∀ x ∈ (P : Subgroup G), f x = 1 → x = 1 := by
    intro x hx hfx
    obtain ⟨k, hk⟩ := P.isPGroup' ⟨x, hx⟩
    have hxk : x ^ p ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hord : orderOf (⟨x, hfx⟩ : f.ker) ∣ p ^ k :=
      orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using hxk))
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow (Fact.out : p.Prime)).mp hord
    have hdvd : orderOf (⟨x, hfx⟩ : f.ker) ∣ Nat.card f.ker := orderOf_dvd_natCard _
    rcases j with _ | j
    · have h1 : (⟨x, hfx⟩ : f.ker) = 1 := orderOf_eq_one_iff.mp (by simpa using hj)
      exact congrArg Subtype.val h1
    · exact absurd ((dvd_pow_self p (Nat.succ_ne_zero j)).trans (hj ▸ hdvd)) hker
  refine of_sylow (P.mapSurjective hf) fun hcen hrk => ?_
  have hcen' : ∀ x ∈ (P : Subgroup G).map f, x ^ p = 1 → ∀ y ∈ (P : Subgroup G).map f, x * y = y * x := hcen
  have hrk' : CFSG.Open.pRank p ((P : Subgroup G).map f) ≤ 3 := hrk
  have hc := h _ (N588A.isSylowOf_top_of_sylow P) (pca_pcentral_of_map f hinj hcen')
    ((pca_pRank_le_map (Fact.out : p.Prime).one_lt f hinj).trans hrk')
  exact pca_comm_map f hc

theorem of_normal_coprime_index {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] (N : Subgroup G)
    (hidx : ¬ p ∣ N.index) (h : PCentralAbelianAt G p) : PCentralAbelianAt ↥N p := by
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow p ↥N))
  refine of_sylow P fun hcen hrk => ?_
  have hinj : ∀ x ∈ (P : Subgroup ↥N), N.subtype x = 1 → x = 1 :=
    fun x _ hx => N.subtype_injective (by rw [map_one]; exact hx)
  have hPG : IsPGroup p ((P : Subgroup ↥N).map N.subtype) := P.isPGroup'.map N.subtype
  have hidx' : ¬ p ∣ ((P : Subgroup ↥N).map N.subtype).index := by
    rw [Subgroup.index_map_subtype]
    intro hd
    rcases (Nat.Prime.dvd_mul (Fact.out : p.Prime)).mp hd with h1 | h1
    · exact P.not_dvd_index h1
    · exact hidx h1
  have hS := N588A.isSylowOf_top_of_sylow (hPG.toSylow hidx')
  rw [IsPGroup.toSylow_coe] at hS
  have hc := h _ hS (pca_pcentral_map N.subtype hinj hcen)
    ((pca_pRank_map_le (Fact.out : p.Prime).one_lt _ N.subtype_injective _).trans hrk)
  exact pca_comm_of_map _ N.subtype_injective hc

theorem of_sylow_comm {K : Type} [Group K] [Finite K] {p : ℕ} [Fact p.Prime]
    (h : ∀ S : Sylow p K, IsMulCommutative (S : Subgroup K)) : PCentralAbelianAt K p := by
  intro T hT _ _
  obtain ⟨P, rfl⟩ := N588A.exists_sylow_of_isSylowOf_top hT
  exact h P

theorem of_sylow_cyclic {K : Type} [Group K] [Finite K] {p : ℕ} [Fact p.Prime]
    (h : ∀ S : Sylow p K, IsCyclic (S : Subgroup K)) : PCentralAbelianAt K p := by
  refine of_sylow_comm fun S => ?_
  haveI := h S
  letI : CommGroup ↥(S : Subgroup K) := IsCyclic.commGroup
  rw [isMulCommutative_iff]
  exact fun a b => mul_comm a b

theorem pca_isCyclic_of_pRank_le_one {K : Type} [Group K] [Finite K] {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {P : Subgroup K} (hP : IsPGroup p P) (hrk : CFSG.Open.pRank p P ≤ 1) : IsCyclic P := by
  by_contra hnc
  haveI : Fact (IsPGroup p P) := ⟨hP⟩
  obtain ⟨S, -, hScard, hSel⟩ := CFSG.lemma_4_5_a hp2 hnc
  haveI := hSel
  have hE : CFSG.Open.IsElemAbelian p (S.map P.subtype) := by
    refine ⟨pca_comm_map _ inferInstance, ?_⟩
    rintro _ ⟨s, hs, rfl⟩
    have := elemPow_eq_one_of_isElementaryAbelian (p := p) s hs
    rw [← map_pow, this, map_one]
  have h2 := CFSG.SectionRank.le_pRank (Fact.out : p.Prime).one_lt (H := P) (map_subtype_le S) hE
    (by rw [Subgroup.card_map_of_injective P.subtype_injective, hScard])
  omega

theorem of_pRank_le_one {K : Type} [Group K] [Finite K] {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (h : CFSG.Open.pRank p (⊤ : Subgroup K) ≤ 1) : PCentralAbelianAt K p :=
  of_sylow_cyclic fun S => pca_isCyclic_of_pRank_le_one hp2 S.isPGroup'
    ((CFSG.SectionRank.pRank_mono (Fact.out : p.Prime).one_lt le_top).trans h)

theorem of_four_le_pRank {K : Type} [Group K] [Finite K] {p : ℕ} (hp : p.Prime) {H : Subgroup K}
    (h : 4 ≤ CFSG.Open.pRank p H) : PCentralAbelianAt K p := by
  intro T hT _ hrk
  have := N588A.pRank_le_of_isSylowOf hp hT H
  omega

theorem of_elemAbelian {K : Type} [Group K] [Finite K] {p : ℕ} (hp : p.Prime) {E : Subgroup K}
    (hE : CFSG.Open.IsElemAbelian p E) {k : ℕ} (hcard : Nat.card E = p ^ k) (hk : 4 ≤ k) : PCentralAbelianAt K p :=
  of_four_le_pRank hp (hk.trans (CFSG.SectionRank.le_pRank hp.one_lt le_rfl hE hcard))

theorem of_noncomm {K : Type} [Group K] [Finite K] {p : ℕ} [Fact p.Prime] {U : Subgroup K} (hU : IsPGroup p U)
    {x y : K} (hx : x ∈ U) (hy : y ∈ U) (hxp : x ^ p = 1) (hxy : x * y ≠ y * x) : PCentralAbelianAt K p := by
  intro T hT hcen _
  exact absurd (pca_comm_of_pow_eq_one hT hcen hU hx hy hxp) hxy

theorem of_hasNoncommPair {K : Type} [Group K] [Finite K] {p : ℕ} [Fact p.Prime]
    (h : CFSG.RankThree.PartOne.StrongP.HasNoncommPair p K) : PCentralAbelianAt K p := by
  obtain ⟨x, y, hxp, -, hxy, hP⟩ := h
  exact of_noncomm hP (Subgroup.subset_closure (Set.mem_insert x {y}))
    (Subgroup.subset_closure (Set.mem_insert_of_mem x rfl)) hxp hxy

theorem of_exponent {K : Type} [Group K] [Finite K] {p : ℕ} [Fact p.Prime] {U : Subgroup K} (hU : IsPGroup p U)
    (hexp : ∀ u ∈ U, u ^ p = 1) (hcard : p ^ 5 ≤ Nat.card U) : PCentralAbelianAt K p := by
  intro T hT hcen hrk
  exfalso
  have hE : CFSG.Open.IsElemAbelian p U := by
    refine ⟨?_, hexp⟩
    rw [isMulCommutative_iff]
    intro a b
    exact Subtype.ext (pca_comm_of_pow_eq_one hT hcen hU a.2 b.2 (hexp _ a.2))
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hU
  have hk5 : 5 ≤ k := by
    rw [hk] at hcard
    exact (Nat.pow_le_pow_iff_right (Fact.out : p.Prime).one_lt).mp hcard
  have h1 := CFSG.SectionRank.le_pRank (Fact.out : p.Prime).one_lt le_rfl hE hk
  have h2 := N588A.pRank_le_of_isSylowOf (Fact.out : p.Prime) hT U
  omega

theorem of_factorization_le {K : Type} [Group K] [Finite K] {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (h : (Nat.card K).factorization p ≤ 3) : PCentralAbelianAt K p := by
  intro T hT hcen _
  obtain ⟨P, rfl⟩ := N588A.exists_sylow_of_isSylowOf_top hT
  by_contra hnab
  haveI : Fact (IsPGroup p ↥(P : Subgroup K)) := ⟨P.isPGroup'⟩
  have hnc : ¬ IsCyclic ↥(P : Subgroup K) := by
    intro hc
    letI : CommGroup ↥(P : Subgroup K) := IsCyclic.commGroup
    exact hnab (isMulCommutative_iff.mpr fun a b => mul_comm a b)
  obtain ⟨S, -, hScard, hSel⟩ := CFSG.lemma_4_5_a hp2 hnc
  haveI := hSel
  have hSZ : S ≤ Subgroup.center ↥(P : Subgroup K) := by
    intro s hs
    rw [Subgroup.mem_center_iff]
    intro y
    have hsp : (s : K) ^ p = 1 := by
      rw [← Subgroup.coe_pow, elemPow_eq_one_of_isElementaryAbelian (p := p) s hs, Subgroup.coe_one]
    exact Subtype.ext (hcen (s : K) s.2 hsp (y : K) y.2).symm
  have hZdvd : p ^ 2 ∣ Nat.card (Subgroup.center ↥(P : Subgroup K)) :=
    hScard ▸ Subgroup.card_dvd_of_le hSZ
  have hPcard := Sylow.card_eq_multiplicity P
  set v := (Nat.card K).factorization p
  have hQ := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥(P : Subgroup K))
  obtain ⟨m, hm⟩ := hZdvd
  rw [hPcard, hm] at hQ
  have hv : 2 ≤ v := by
    have h1 : p ^ 2 ∣ p ^ v :=
      ⟨Nat.card (↥(P : Subgroup K) ⧸ Subgroup.center ↥(P : Subgroup K)) * m, by rw [hQ]; ring⟩
    exact (Nat.pow_dvd_pow_iff_le_right (Fact.out : p.Prime).one_lt).mp h1
  have hQdvd : Nat.card (↥(P : Subgroup K) ⧸ Subgroup.center ↥(P : Subgroup K)) ∣ p := by
    have h1 : p ^ v = p ^ (v - 2) * p ^ 2 := by rw [← pow_add, Nat.sub_add_cancel hv]
    have h2 : Nat.card (↥(P : Subgroup K) ⧸ Subgroup.center ↥(P : Subgroup K)) * m = p ^ (v - 2) := by
      have hp0 : 0 < p ^ 2 := pow_pos (Fact.out : p.Prime).pos 2
      apply Nat.eq_of_mul_eq_mul_right hp0
      rw [← h1, hQ]
      ring
    have h3 : p ^ (v - 2) ∣ p ^ 1 := pow_dvd_pow p (by omega)
    rw [pow_one] at h3
    exact (Dvd.intro _ h2).trans h3
  have hcyc : IsCyclic (↥(P : Subgroup K) ⧸ Subgroup.center ↥(P : Subgroup K)) := by
    rcases (Nat.dvd_prime (Fact.out : p.Prime)).mp hQdvd with h1 | h1
    · haveI := (Nat.card_eq_one_iff_unique.mp h1).1
      infer_instance
    · exact isCyclic_of_prime_card h1
  apply hnab
  rw [isMulCommutative_iff]
  exact commutative_of_cyclic_center_quotient (QuotientGroup.mk' (Subgroup.center ↥(P : Subgroup K)))
    (by rw [QuotientGroup.ker_mk'])

end PCentralAbelianAt

end Sylow

end CFSG.LocalAnalysis.UniquenessCase.UCK
