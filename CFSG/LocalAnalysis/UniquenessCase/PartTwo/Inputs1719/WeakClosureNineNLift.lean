module

public import CFSG.Quasithin.Background.E1Sec3
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.B2FactorizationResidual
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.WeakClosure81.NFW

open CFSG.Quasithin CFSG.Open Subgroup

section Generic

variable {G : Type*} [Group G]

theorem exists_isSylowIn [Finite G] (p : ℕ) [Fact p.Prime] (H : Subgroup G) :
    ∃ P : Subgroup G, IsSylowIn p P H := by
  obtain ⟨R⟩ := (inferInstance : Nonempty (Sylow p H))
  refine ⟨(R : Subgroup H).map H.subtype, Subgroup.map_subtype_le _, R.isPGroup'.map _, ?_⟩
  rw [Subgroup.relIndex, ← Subgroup.comap_subtype,
    Subgroup.comap_map_eq_self_of_injective H.subtype_injective]
  exact R.not_dvd_index

theorem le_normalizer_of_conj_mem {T D : Subgroup G}
    (h : ∀ t ∈ T, ∀ x ∈ D, t * x * t⁻¹ ∈ D) : T ≤ normalizer (D : Set G) := by
  intro t ht
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨h t ht x, fun hx => ?_⟩
  have := h t⁻¹ (T.inv_mem ht) _ hx
  simpa [mul_assoc] using this

theorem mem_normalizer_centralizer {H : Subgroup G} {g : G}
    (hg : g ∈ normalizer (H : Set G)) : g ∈ normalizer (centralizer (H : Set G) : Set G) := by
  have key : ∀ g ∈ normalizer (H : Set G), ∀ x ∈ centralizer (H : Set G),
      g * x * g⁻¹ ∈ centralizer (H : Set G) := by
    intro g hg x hx
    rw [Subgroup.mem_centralizer_iff] at hx ⊢
    intro y hy
    have hy' : g⁻¹ * y * g ∈ H := by
      have := (Subgroup.mem_normalizer_iff''.1 hg y).1 hy
      exact this
    have h1 := hx _ hy'
    calc y * (g * x * g⁻¹) = g * ((g⁻¹ * y * g) * x) * g⁻¹ := by group
      _ = g * (x * (g⁻¹ * y * g)) * g⁻¹ := by rw [h1]
      _ = g * x * g⁻¹ * y := by group
  exact le_normalizer_of_conj_mem (T := normalizer (H : Set G)) key hg

theorem map_frattini_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    (frattini A).map e.toMonoidHom = frattini B := by
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap]
    exact frattini_le_comap_frattini_of_surjective e.surjective
  · intro x hx
    have h := frattini_le_comap_frattini_of_surjective (φ := e.symm.toMonoidHom) e.symm.surjective
      hx
    exact ⟨e.symm x, h, by simp⟩

theorem exists_orderOf_eq_of_isPGroup [Finite G] {p : ℕ} [Fact p.Prime] {H : Subgroup G}
    (hH : IsPGroup p H) (hne : H ≠ ⊥) : ∃ x ∈ H, orderOf x = p := by
  have : Nontrivial H := (Subgroup.nontrivial_iff_ne_bot H).2 hne
  obtain ⟨n, hn, hcard⟩ := (hH.nontrivial_iff_card).1 inferInstance
  have hdvd : p ∣ Nat.card H := by
    rw [hcard]
    exact dvd_pow_self p hn.ne'
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hdvd
  exact ⟨x, x.2, by rw [Subgroup.orderOf_coe]; exact hx⟩

theorem oTwoPTwo_eq_top_of_surjective {A B : Type*} [Group A] [Group B] [Finite A] [Finite B]
    {p : ℕ} [Fact p.Prime] (f : A →* B) (hker : IsPGroup 2 f.ker)
    (h : E1.oTwoPTwo B p = ⊤) : E1.oTwoPTwo A p = ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hN2 : ((CFSG.Open.pCore 2 B).comap f).Normal :=
    (CFSG.LieType.BorelTits.pCore_normal 2).comap f
  have hN2p : ((E1.oTwoP B p).comap f).Normal := (E1.instNormalOTwoP B p).comap f
  refine E1.oTwoPTwo_eq_top_of_series (N₂ := (CFSG.Open.pCore 2 B).comap f)
    (N₂p := (E1.oTwoP B p).comap f) ?_ ?_ ?_
  · exact IsPGroup.comap_of_ker_isPGroup (CFSG.LieType.BorelTits.pCore_isPGroup 2) f hker
  · intro x hx
    have hx' : QuotientGroup.mk' (CFSG.Open.pCore 2 B) (f x) ∈
        CFSG.Open.pCore p (B ⧸ CFSG.Open.pCore 2 B) := hx
    obtain ⟨k, hk⟩ := (CFSG.LieType.BorelTits.pCore_isPGroup p (G := B ⧸ CFSG.Open.pCore 2 B))
      ⟨_, hx'⟩
    refine ⟨k, ?_⟩
    show f (x ^ p ^ k) ∈ CFSG.Open.pCore 2 B
    rw [map_pow, ← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
    simpa using congrArg Subtype.val hk
  · intro q
    have hq : f q ∈ E1.oTwoPTwo B p := by rw [h]; exact Subgroup.mem_top _
    have hq' : QuotientGroup.mk' (E1.oTwoP B p) (f q) ∈
        CFSG.Open.pCore 2 (B ⧸ E1.oTwoP B p) := hq
    obtain ⟨k, hk⟩ := (CFSG.LieType.BorelTits.pCore_isPGroup 2 (G := B ⧸ E1.oTwoP B p))
      ⟨_, hq'⟩
    refine ⟨k, ?_⟩
    show f (q ^ 2 ^ k) ∈ E1.oTwoP B p
    rw [map_pow, ← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
    simpa using congrArg Subtype.val hk

end Generic

variable {G : Type} [Group G] {N : Subgroup G} {X : Type} [Group X]

@[expose] def liftSub (π : ↥N →* X) (K : Subgroup X) : Subgroup G := (K.comap π).map N.subtype

@[expose] def barSub (π : ↥N →* X) (H : Subgroup G) : Subgroup X := (H.subgroupOf N).map π

variable {π : ↥N →* X}

theorem mem_liftSub {K : Subgroup X} {x : G} :
    x ∈ liftSub π K ↔ ∃ h : x ∈ N, π ⟨x, h⟩ ∈ K := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨h, hx⟩
    exact ⟨⟨x, h⟩, hx, rfl⟩

theorem liftSub_le (K : Subgroup X) : liftSub π K ≤ N := by
  rintro _ ⟨y, -, rfl⟩
  exact y.2

theorem mem_barSub_of_mem {H : Subgroup G} {x : G} (hxN : x ∈ N) (hxH : x ∈ H) :
    π ⟨x, hxN⟩ ∈ barSub π H :=
  ⟨⟨x, hxN⟩, hxH, rfl⟩

theorem mem_barSub_of_mem' {H : Subgroup G} {x : ↥N} (hxH : (x : G) ∈ H) :
    π x ∈ barSub π H :=
  ⟨x, hxH, rfl⟩

theorem barSub_mono {H H' : Subgroup G} (h : H ≤ H') : barSub π H ≤ barSub π H' := by
  rintro _ ⟨x, hx, rfl⟩
  exact ⟨x, h hx, rfl⟩

theorem liftSub_mono {K K' : Subgroup X} (h : K ≤ K') : liftSub π K ≤ liftSub π K' :=
  Subgroup.map_mono (Subgroup.comap_mono h)

theorem barSub_liftSub (hπ : Function.Surjective π) (K : Subgroup X) :
    barSub π (liftSub π K) = K := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨_, hK⟩ := mem_liftSub.1 hx
    exact hK
  · intro hy
    obtain ⟨x, rfl⟩ := hπ y
    exact ⟨x, mem_liftSub.2 ⟨x.2, hy⟩, rfl⟩

theorem barSub_le_iff {H : Subgroup G} (hHN : H ≤ N) {K : Subgroup X} :
    barSub π H ≤ K ↔ H ≤ liftSub π K := by
  constructor
  · intro h x hx
    exact mem_liftSub.2 ⟨hHN hx, h (mem_barSub_of_mem _ hx)⟩
  · rintro h _ ⟨x, hx, rfl⟩
    obtain ⟨hxN, hK⟩ := mem_liftSub.1 (h hx)
    exact hK

theorem liftSub_inf (K K' : Subgroup X) :
    liftSub π (K ⊓ K') = liftSub π K ⊓ liftSub π K' := by
  ext x
  simp only [Subgroup.mem_inf, mem_liftSub]
  constructor
  · rintro ⟨h, hK, hK'⟩
    exact ⟨⟨h, hK⟩, ⟨h, hK'⟩⟩
  · rintro ⟨⟨h, hK⟩, ⟨_, hK'⟩⟩
    exact ⟨h, hK, hK'⟩

theorem liftSub_top : liftSub π (⊤ : Subgroup X) = N :=
  le_antisymm (liftSub_le _) fun _ hx => mem_liftSub.2 ⟨hx, Subgroup.mem_top _⟩

theorem barSub_top_eq (hπ : Function.Surjective π) : barSub π N = ⊤ := by
  refine eq_top_iff.2 fun y _ => ?_
  obtain ⟨x, rfl⟩ := hπ y
  exact mem_barSub_of_mem' x.2

theorem mem_normalizer_barSub {H : Subgroup G} {n : ↥N}
    (hn : (n : G) ∈ normalizer (H : Set G)) : π n ∈ normalizer (barSub π H : Set X) := by
  have key : ∀ m : ↥N, (m : G) ∈ normalizer (H : Set G) →
      ∀ y ∈ barSub π H, π m * y * (π m)⁻¹ ∈ barSub π H := by
    rintro m hm _ ⟨x, hx, rfl⟩
    refine ⟨m * x * m⁻¹, ?_, by simp [map_mul, map_inv]⟩
    exact (Subgroup.mem_normalizer_iff.1 hm x).1 hx
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨key n hn y, fun hy => ?_⟩
  have := key n⁻¹ (by simpa using inv_mem hn) _ hy
  simpa [map_inv, mul_assoc] using this

theorem barSub_le_normalizer {A H : Subgroup G} (hA : A ≤ normalizer (H : Set G)) :
    barSub π A ≤ normalizer (barSub π H : Set X) := by
  rintro _ ⟨x, hx, rfl⟩
  exact mem_normalizer_barSub (hA hx)

theorem barSub_normal (hπ : Function.Surjective π) {H : Subgroup G}
    (hH : N ≤ normalizer (H : Set G)) : (barSub π H).Normal := by
  have h := barSub_le_normalizer (π := π) hH
  rw [barSub_top_eq hπ, top_le_iff] at h
  exact Subgroup.normalizer_eq_top_iff.1 h

theorem barSub_le_centralizer {A H : Subgroup G} (hA : A ≤ centralizer (H : Set G)) :
    barSub π A ≤ centralizer (barSub π H : Set X) := by
  rintro _ ⟨x, hx, rfl⟩
  rw [Subgroup.mem_centralizer_iff]
  rintro _ ⟨y, hy, rfl⟩
  have h : (y : G) * x = x * y := (Subgroup.mem_centralizer_iff.1 (hA hx)) y hy
  have h' : y * x = x * y := Subtype.ext h
  rw [← map_mul, ← map_mul, h']

theorem mem_normalizer_liftSub {x : G} (hx : x ∈ N) {K : Subgroup X}
    (h : π ⟨x, hx⟩ ∈ normalizer (K : Set X)) : x ∈ normalizer (liftSub π K : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro z
  constructor
  · intro hz
    obtain ⟨hzN, hzK⟩ := mem_liftSub.1 hz
    have hmem : x * z * x⁻¹ ∈ N := N.mul_mem (N.mul_mem hx hzN) (N.inv_mem hx)
    refine mem_liftSub.2 ⟨hmem, ?_⟩
    have e : (⟨x * z * x⁻¹, hmem⟩ : ↥N) = ⟨x, hx⟩ * ⟨z, hzN⟩ * (⟨x, hx⟩)⁻¹ := rfl
    rw [e, map_mul, map_mul, map_inv]
    exact (Subgroup.mem_normalizer_iff.1 h _).1 hzK
  · intro hz
    obtain ⟨hzN', hzK⟩ := mem_liftSub.1 hz
    have hzN : z ∈ N := by
      have := N.mul_mem (N.mul_mem (N.inv_mem hx) hzN') hx
      simpa [mul_assoc] using this
    refine mem_liftSub.2 ⟨hzN, ?_⟩
    have e : (⟨x * z * x⁻¹, hzN'⟩ : ↥N) = ⟨x, hx⟩ * ⟨z, hzN⟩ * (⟨x, hx⟩)⁻¹ := rfl
    rw [e, map_mul, map_mul, map_inv] at hzK
    exact (Subgroup.mem_normalizer_iff.1 h _).2 hzK

theorem relIndex_liftSub (hπ : Function.Surjective π) (A B : Subgroup X) :
    (liftSub π A).relIndex (liftSub π B) = A.relIndex B := by
  unfold liftSub
  rw [Subgroup.relIndex_map_map, Subgroup.ker_subtype, sup_bot_eq, sup_bot_eq,
    Subgroup.relIndex_comap, Subgroup.map_comap_eq_self_of_surjective hπ]

theorem isPGroup_barSub {p : ℕ} {H : Subgroup G} (hH : IsPGroup p H) :
    IsPGroup p (barSub π H) :=
  (hH.comap_of_injective N.subtype N.subtype_injective).map π

theorem exists_orderOf_eq_of_barSub [Finite G] {D : Subgroup G} {y : X} (hy : y ∈ barSub π D)
    {k : ℕ} (hk : orderOf y = k) : ∃ x ∈ D, orderOf x = k := by
  obtain ⟨n, hnD, rfl⟩ := hy
  have hdvd : orderOf (π n) ∣ orderOf (n : G) := by
    rw [Subgroup.orderOf_coe]
    exact orderOf_map_dvd π n
  have hpos : orderOf (n : G) ≠ 0 := (orderOf_pos (n : G)).ne'
  refine ⟨(n : G) ^ (orderOf (n : G) / k), D.pow_mem hnD _, ?_⟩
  rw [orderOf_pow_orderOf_div hpos (hk ▸ hdvd)]

variable (hker : ∀ x : ↥N, π x = 1 ↔ (x : G) ∈ pCoreOf 2 N)
include hker

theorem ker_eq_comap : π.ker = (pCoreOf 2 N).comap N.subtype := by
  ext x
  rw [MonoidHom.mem_ker, Subgroup.mem_comap]
  exact hker x

theorem isPGroup_ker [Finite G] : IsPGroup 2 π.ker := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [ker_eq_comap hker]
  exact IsPGroup.comap_of_injective (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 N) N.subtype
    N.subtype_injective

theorem pCoreOf_le_liftSub (K : Subgroup X) : pCoreOf 2 N ≤ liftSub π K := by
  intro x hx
  have hxN : x ∈ N := CFSG.LieType.BorelTits.pCoreOf_le 2 N hx
  refine mem_liftSub.2 ⟨hxN, ?_⟩
  rw [(hker ⟨x, hxN⟩).2 hx]
  exact K.one_mem

theorem liftSub_barSub {H : Subgroup G} (hQH : pCoreOf 2 N ≤ H) (hHN : H ≤ N) :
    liftSub π (barSub π H) = H := by
  ext x
  constructor
  · intro hx
    obtain ⟨hxN, y, hyH, hy⟩ := mem_liftSub.1 hx
    have hk : π (y⁻¹ * ⟨x, hxN⟩) = 1 := by rw [map_mul, map_inv, hy, inv_mul_cancel]
    have hq : (y : G)⁻¹ * x ∈ H := hQH ((hker _).1 hk)
    have := H.mul_mem hyH hq
    simpa using this
  · intro hx
    exact mem_liftSub.2 ⟨hHN hx, mem_barSub_of_mem _ hx⟩

theorem barSub_eq_bot_iff {H : Subgroup G} (hHN : H ≤ N) :
    barSub π H = ⊥ ↔ H ≤ pCoreOf 2 N := by
  constructor
  · intro h x hx
    have hmem := mem_barSub_of_mem (π := π) (hHN hx) hx
    rw [h, Subgroup.mem_bot] at hmem
    exact (hker _).1 hmem
  · intro h
    rw [eq_bot_iff]
    rintro _ ⟨x, hx, rfl⟩
    exact (Subgroup.mem_bot).2 ((hker x).2 (h hx))

theorem isPGroup_liftSub [Finite G] {K : Subgroup X} (hK : IsPGroup 2 K) :
    IsPGroup 2 (liftSub π K) :=
  (IsPGroup.comap_of_ker_isPGroup hK π (isPGroup_ker hker)).map N.subtype

theorem isPGroup_of_barSub [Finite G] {H : Subgroup G} (hHN : H ≤ N)
    (h : IsPGroup 2 (barSub π H)) : IsPGroup 2 H :=
  (isPGroup_liftSub hker h).to_le ((barSub_le_iff hHN).1 le_rfl)

theorem card_barSub {H : Subgroup G} (hHN : H ≤ N) :
    Nat.card (barSub π H) = (pCoreOf 2 N).relIndex H := by
  have h1 : (⊥ : Subgroup X).relIndex (barSub π H) = Nat.card (barSub π H) :=
    Subgroup.relIndex_bot_left _
  rw [← h1, barSub, ← Subgroup.relIndex_comap, MonoidHom.comap_bot, ker_eq_comap hker,
    Subgroup.relIndex_comap, Subgroup.map_subgroupOf_eq_of_le hHN]

theorem liftSub_pCoreOf_le [Finite G] [Finite X] (K : Subgroup X) :
    liftSub π (pCoreOf 2 K) ≤ pCoreOf 2 (liftSub π K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
    (liftSub_mono (CFSG.LieType.BorelTits.pCoreOf_le 2 K)) ?_
    (isPGroup_liftSub hker (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K))
  intro x hx
  obtain ⟨hxN, hxK⟩ := mem_liftSub.1 hx
  exact mem_normalizer_liftSub hxN (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K hxK)

@[expose] def liftRestrict (π : ↥N →* X) (K : Subgroup X) : ↥(liftSub π K) →* ↥K :=
  (π.comp (Subgroup.inclusion (liftSub_le K))).codRestrict K fun x => by
    obtain ⟨h, hx⟩ := mem_liftSub.1 x.2
    exact hx

theorem isPGroup_ker_liftRestrict [Finite G] (K : Subgroup X) :
    IsPGroup 2 (liftRestrict π K).ker := by
  unfold liftRestrict
  rw [MonoidHom.ker_codRestrict, ← MonoidHom.comap_ker]
  exact IsPGroup.comap_of_injective (isPGroup_ker hker) _ (Subgroup.inclusion_injective _)

theorem oTwoPTwo_liftSub [Finite G] [Finite X] (K : Subgroup X) {p : ℕ} [Fact p.Prime]
    (h : E1.oTwoPTwo ↥K p = ⊤) : E1.oTwoPTwo ↥(liftSub π K) p = ⊤ :=
  oTwoPTwo_eq_top_of_surjective (liftRestrict π K) (isPGroup_ker_liftRestrict hker K) h

theorem isSylowIn_two_liftSub [Finite G] (hπ : Function.Surjective π) {S K : Subgroup X}
    (h : IsSylowIn 2 S K) : IsSylowIn 2 (liftSub π S) (liftSub π K) :=
  ⟨liftSub_mono h.1, isPGroup_liftSub hker h.2.1, by rw [relIndex_liftSub hπ]; exact h.2.2⟩

end CFSG.LocalAnalysis.WeakClosure81.NFW
