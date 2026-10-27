module

public import CFSG.LocalAnalysis.SolvableSignalizer.Basic
public import CFSG.LocalAnalysis.SignalizerFunctor.MinimalIncompleteSolvable

public section

namespace CFSG.SolvableSignalizer.Internal

section Ambient

variable {G A : Type*} [Group G] [Group A]

abbrev Ambient (α : A →* MulAut G) := G ⋊[α] A

abbrev embed (α : A →* MulAut G) : G →* Ambient α := SemidirectProduct.inl

abbrev actorEmbed (α : A →* MulAut G) : A →* Ambient α := SemidirectProduct.inr

def actor (α : A →* MulAut G) : Subgroup (Ambient α) := (actorEmbed α).range

@[expose]
def lift (α : A →* MulAut G) (H : Subgroup G) : Subgroup (Ambient α) :=
  H.map (embed α)

def actorLift (α : A →* MulAut G) (B : Subgroup A) : Subgroup (Ambient α) :=
  B.map (actorEmbed α)

def lower (α : A →* MulAut G) (H : Subgroup (Ambient α)) : Subgroup G :=
  H.comap (embed α)

private def actorLower (α : A →* MulAut G) (S : Subgroup (Ambient α)) : Subgroup A :=
  S.comap (actorEmbed α)

theorem embed_injective (α : A →* MulAut G) : Function.Injective (embed α) :=
  SemidirectProduct.inl_injective

theorem actorEmbed_injective (α : A →* MulAut G) : Function.Injective (actorEmbed α) :=
  SemidirectProduct.inr_injective

@[expose]
noncomputable def liftEquiv (α : A →* MulAut G) (H : Subgroup G) : H ≃* lift α H :=
  H.equivMapOfInjective (embed α) (embed_injective α)

instance instFiniteAmbient [Finite G] [Finite A] (α : A →* MulAut G) : Finite (Ambient α) :=
  Finite.of_equiv (G × A) SemidirectProduct.equivProd.symm

theorem lift_injective (α : A →* MulAut G) : Function.Injective (lift α) :=
  Subgroup.map_injective (embed_injective α)

@[simp] theorem lift_inf (α : A →* MulAut G) (H K : Subgroup G) :
    lift α (H ⊓ K) = lift α H ⊓ lift α K :=
  Subgroup.map_inf H K (embed α) (embed_injective α)

@[simp] theorem lift_le_lift (α : A →* MulAut G) {H K : Subgroup G} :
    lift α H ≤ lift α K ↔ H ≤ K :=
  Subgroup.map_le_map_iff_of_injective (embed_injective α)

@[simp] theorem mem_lift (α : A →* MulAut G) (H : Subgroup G) (g : G) :
    embed α g ∈ lift α H ↔ g ∈ H :=
  Subgroup.mem_map_iff_mem (embed_injective α)

@[simp] theorem card_lift (α : A →* MulAut G) (H : Subgroup G) :
    Nat.card (lift α H) = Nat.card H :=
  Subgroup.card_map_of_injective (embed_injective α)

@[simp] theorem card_actor (α : A →* MulAut G) : Nat.card (actor α) = Nat.card A :=
  (Nat.card_congr (MonoidHom.ofInjective (actorEmbed_injective α)).toEquiv).symm

private theorem card_actorLift (α : A →* MulAut G) (B : Subgroup A) :
    Nat.card (actorLift α B) = Nat.card B :=
  Subgroup.card_map_of_injective (actorEmbed_injective α)

private theorem isSolvable_lift_iff (α : A →* MulAut G) (H : Subgroup G) :
    Group.IsSolvable (lift α H) ↔ Group.IsSolvable H :=
  ⟨fun _ => Group.isSolvable_of_isSolvable_injective
      (f := (liftEquiv α H).toMonoidHom) (liftEquiv α H).injective,
    fun _ => Group.isSolvable_of_isSolvable_injective
      (f := (liftEquiv α H).symm.toMonoidHom) (liftEquiv α H).symm.injective⟩

private theorem lift_lower (α : A →* MulAut G) (H : Subgroup (Ambient α))
    (hH : H ≤ lift α ⊤) : lift α (lower α H) = H := by
  refine le_antisymm (Subgroup.map_comap_le _ _) fun x hx => ?_
  obtain ⟨g, -, rfl⟩ := hH hx
  exact Subgroup.mem_map_of_mem _ hx

private theorem actorLift_actorLower (α : A →* MulAut G) (S : Subgroup (Ambient α))
    (hS : S ≤ actor α) : actorLift α (actorLower α S) = S := by
  refine le_antisymm (Subgroup.map_comap_le _ _) fun x hx => ?_
  obtain ⟨a, rfl⟩ := hS hx
  exact Subgroup.mem_map_of_mem _ hx

private theorem card_actorLower (α : A →* MulAut G) (S : Subgroup (Ambient α))
    (hS : S ≤ actor α) : Nat.card (actorLower α S) = Nat.card S := by
  rw [← card_actorLift α (actorLower α S), actorLift_actorLower α S hS]

private theorem le_lift_top_of_coprime [Finite G] [Finite A] (α : A →* MulAut G)
    (p : ℕ) (hexp : ∀ a : A, a ^ p = 1) (H : Subgroup (Ambient α))
    (hcop : Nat.Coprime p (Nat.card H)) : H ≤ lift α ⊤ := by
  intro x hx
  have hxpow : x ^ Nat.card H = 1 := by
    have h := congrArg Subtype.val (pow_card_eq_one' (G := H) (x := ⟨x, hx⟩))
    simpa only [SubmonoidClass.coe_pow, OneMemClass.coe_one] using h
  have hrpow : x.right ^ Nat.card H = 1 := by
    have h := congrArg SemidirectProduct.rightHom hxpow
    rwa [map_pow, map_one] at h
  have hr : x.right = 1 := (pow_eq_one_iff_of_coprime hcop).mp ⟨hexp _, hrpow⟩
  exact ⟨x.left, Subgroup.mem_top _, SemidirectProduct.ext rfl hr.symm⟩

private theorem lift_lower_of_coprime [Finite G] [Finite A] (α : A →* MulAut G)
    (p : ℕ) (hexp : ∀ a : A, a ^ p = 1) (H : Subgroup (Ambient α))
    (hcop : Nat.Coprime p (Nat.card H)) : lift α (lower α H) = H :=
  lift_lower α H (le_lift_top_of_coprime α p hexp H hcop)

private theorem actorEmbed_conj_embed (α : A →* MulAut G) (a : A) (g : G) :
    actorEmbed α a * embed α g * (actorEmbed α a)⁻¹ = embed α (α a g) := by
  simpa using (SemidirectProduct.inl_aut (φ := α) a g).symm

private theorem apply_eq_self_iff (α : A →* MulAut G) (a : A) (g : G) :
    α a g = g ↔ actorEmbed α a * embed α g = embed α g * actorEmbed α a := by
  rw [← mul_inv_eq_iff_eq_mul, actorEmbed_conj_embed]
  exact (embed_injective α).eq_iff.symm

private theorem lift_fixedIn (α : A →* MulAut G) (H : Subgroup G) (a : A) :
    lift α (fixedIn α H a) =
      lift α H ⊓ Subgroup.centralizer ({actorEmbed α a} : Set (Ambient α)) := by
  ext x
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨(mem_lift α H g).2 hg.1, Subgroup.mem_centralizer_singleton_iff.mpr
      ((apply_eq_self_iff α a g).mp hg.2).symm⟩
  · rintro ⟨⟨g, hg, rfl⟩, hxcent⟩
    exact (mem_lift α _ g).2 ⟨hg, (apply_eq_self_iff α a g).mpr
      (Subgroup.mem_centralizer_singleton_iff.mp hxcent).symm⟩

private theorem lift_map_apply (α : A →* MulAut G) (H : Subgroup G) (a : A) :
    lift α (H.map (α a).toMonoidHom) =
      (lift α H).map (MulAut.conj (actorEmbed α a)).toMonoidHom := by
  simp only [lift, Subgroup.map_map]
  congr 1
  exact MonoidHom.ext fun g => (actorEmbed_conj_embed α a g).symm

theorem isInvariant_iff_actor_le_normalizer (α : A →* MulAut G) (H : Subgroup G) :
    IsInvariant α H ↔ actor α ≤ Subgroup.normalizer (lift α H : Set (Ambient α)) := by
  constructor
  · rintro h _ ⟨a, rfl⟩
    apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
    change (lift α H).map (MulAut.conj (actorEmbed α a)).toMonoidHom = lift α H
    rw [← lift_map_apply, h a]
  · intro h a
    apply lift_injective α
    rw [lift_map_apply]
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mp (h ⟨a, rfl⟩)

private theorem comap_normalizer_lift (α : A →* MulAut G) (H : Subgroup G) :
    (Subgroup.normalizer (lift α H : Set (Ambient α))).comap (embed α) =
      Subgroup.normalizer (H : Set G) := by
  rw [lift, Subgroup.comap_normalizer_eq_of_le_range (Subgroup.map_le_range (embed α) H),
    Subgroup.comap_map_eq_self_of_injective (embed_injective α)]

private theorem lift_inf_normalizer (α : A →* MulAut G) (H U : Subgroup G) :
    lift α (H ⊓ Subgroup.normalizer (U : Set G)) =
      lift α H ⊓ Subgroup.normalizer (lift α U : Set (Ambient α)) := by
  ext x
  constructor
  · rintro ⟨g, hg, rfl⟩
    have hgn : g ∈ (Subgroup.normalizer (lift α U : Set (Ambient α))).comap (embed α) := by
      rw [comap_normalizer_lift]
      exact hg.2
    exact ⟨(mem_lift α H g).2 hg.1, hgn⟩
  · rintro ⟨⟨g, hg, rfl⟩, hgn⟩
    have hgn : g ∈ (Subgroup.normalizer (lift α U : Set (Ambient α))).comap (embed α) := hgn
    rw [comap_normalizer_lift] at hgn
    exact (mem_lift α _ g).2 ⟨hg, hgn⟩

private theorem lift_completion (α : A →* MulAut G) (θ : A → Subgroup G) :
    lift α (completion θ) = ⨆ (a : A) (_ : a ≠ 1), lift α (θ a) := by
  simp only [completion, lift, Subgroup.map_iSup]

private theorem lift_completionIn_normalizer (α : A →* MulAut G) (θ : A → Subgroup G)
    (U : Subgroup G) :
    lift α (completionIn θ (Subgroup.normalizer (U : Set G))) =
      ⨆ (a : A) (_ : a ≠ 1),
        lift α (θ a) ⊓ Subgroup.normalizer (lift α U : Set (Ambient α)) := by
  simp only [completionIn, ← lift_inf_normalizer]
  simp only [lift, Subgroup.map_iSup]

def cyclicActor (α : A →* MulAut G) (a : A) : Subgroup (Ambient α) :=
  Subgroup.closure ({actorEmbed α a} : Set (Ambient α))

theorem cyclicActor_le (α : A →* MulAut G) (a : A) : cyclicActor α a ≤ actor α :=
  (Subgroup.closure_le (actor α)).mpr (Set.singleton_subset_iff.mpr ⟨a, rfl⟩)

private theorem exists_index (α : A →* MulAut G) {p : ℕ} (hp : p.Prime)
    (S : Subgroup (Ambient α)) (hS : S ≤ actor α) (hcard : Nat.card S = p) :
    ∃ a : A, a ≠ 1 ∧ actorEmbed α a ∈ S := by
  obtain ⟨x, hxS, hx⟩ := S.bot_or_exists_ne_one.resolve_left fun h =>
    hp.one_lt.ne' (by rw [← hcard, h, Subgroup.card_bot])
  obtain ⟨a, rfl⟩ := hS hxS
  exact ⟨a, fun h => hx (by rw [h, map_one]), hxS⟩

noncomputable def index (α : A →* MulAut G) (S : Subgroup (Ambient α)) : A := by
  classical
  exact if h : ∃ a : A, a ≠ 1 ∧ actorEmbed α a ∈ S then Classical.choose h else 1

theorem index_spec (α : A →* MulAut G) {p : ℕ} (hp : p.Prime)
    (S : Subgroup (Ambient α)) (hS : S ≤ actor α) (hcard : Nat.card S = p) :
    index α S ≠ 1 ∧ actorEmbed α (index α S) ∈ S := by
  classical
  have h := exists_index α hp S hS hcard
  simp only [index, h, ↓reduceDIte]
  exact Classical.choose_spec h

@[expose]
noncomputable def values (α : A →* MulAut G) (θ : A → Subgroup G)
    (S : Subgroup (Ambient α)) : Subgroup (Ambient α) := lift α (θ (index α S))

private theorem apply_eq_self_of_mem_closure {α : A →* MulAut G} {a b : A}
    (hb : b ∈ Subgroup.closure ({a} : Set A)) {g : G} (hg : α a g = g) : α b g = g := by
  have hle : Subgroup.closure ({a} : Set A) ≤ (MulAction.stabilizer (MulAut G) g).comap α :=
    (Subgroup.closure_le _).mpr (Set.singleton_subset_iff.mpr hg)
  exact hle hb

end Ambient

private theorem closure_singleton_eq_of_card_eq_prime {H : Type*} [Group H] {p : ℕ}
    [Fact p.Prime] (B : Subgroup H) (hB : Nat.card B = p) {a : H} (haB : a ∈ B) (ha : a ≠ 1) :
    Subgroup.closure ({a} : Set H) = B := by
  have hgen := congrArg (Subgroup.map B.subtype) (zpowers_eq_top_of_prime_card hB
    (g := ⟨a, haB⟩) fun h => ha (congrArg Subtype.val h))
  rw [Subgroup.zpowers_eq_closure, MonoidHom.map_closure] at hgen
  simpa only [Set.image_singleton, Subgroup.map_top, Subgroup.range_subtype,
    Subgroup.coe_subtype] using hgen

theorem lift_le_normalizer_lift {A G : Type*} [CommGroup A] [Finite A] [Group G] [Finite G]
    {α : A →* MulAut G} (H K : Subgroup G) :
    lift α H ≤ Subgroup.normalizer (lift α K : Set (Ambient α)) ↔
      H ≤ Subgroup.normalizer (K : Set G) := by
  rw [lift, Subgroup.map_le_iff_le_comap, comap_normalizer_lift]

section RankOne

open CFSG.Open CFSG.SignalizerFunctor.Helpers

variable {p : ℕ} {A G : Type*} [CommGroup A] [Finite A] [Group G] [Finite G]
variable {α : A →* MulAut G} {θ : A → Subgroup G}

private theorem theta_eq_of_closure_eq (d : Datum p α θ)
    {a b : A} (ha : a ≠ 1) (hb : b ≠ 1)
    (hab : Subgroup.closure ({a} : Set A) = Subgroup.closure ({b} : Set A)) :
    θ a = θ b := by
  have hf : fixedSubgroup α a = fixedSubgroup α b := by
    ext g
    exact ⟨apply_eq_self_of_mem_closure (hab ▸ Subgroup.mem_closure_singleton_self b),
      apply_eq_self_of_mem_closure (hab ▸ Subgroup.mem_closure_singleton_self a)⟩
  exact le_antisymm (fun g hg => d.balance a b ha hb ⟨hg, hf ▸ d.central a ha hg⟩)
    (fun g hg => d.balance b a hb ha ⟨hg, hf.symm ▸ d.central b hb hg⟩)

private theorem theta_eq_of_mem (d : Datum p α θ) (B : Subgroup A)
    (hB : Nat.card B = p) {a b : A} (haB : a ∈ B) (hbB : b ∈ B) (ha : a ≠ 1) (hb : b ≠ 1) :
    θ a = θ b := by
  have : Fact p.Prime := ⟨d.prime⟩
  apply theta_eq_of_closure_eq d ha hb
  rw [closure_singleton_eq_of_card_eq_prime B hB haB ha,
    closure_singleton_eq_of_card_eq_prime B hB hbB hb]

theorem card_cyclicActor (d : Datum p α θ) {a : A} (ha : a ≠ 1) :
    Nat.card (cyclicActor α a) = p := by
  rw [cyclicActor, ← Subgroup.zpowers_eq_closure, Nat.card_zpowers]
  have hpow : actorEmbed α a ^ p = 1 := by rw [← map_pow, d.exponent, map_one]
  have hne : actorEmbed α a ≠ 1 := fun h => ha (actorEmbed_injective α (h.trans (map_one _).symm))
  exact (d.prime.eq_one_or_self_of_dvd _ (orderOf_dvd_of_pow_eq_one hpow)).resolve_left
    fun h => hne (orderOf_eq_one_iff.mp h)

theorem values_cyclicActor (d : Datum p α θ) {a : A} (ha : a ≠ 1) :
    values α θ (cyclicActor α a) = lift α (θ a) := by
  have hS := cyclicActor_le α a
  have hc := card_cyclicActor d ha
  have hspec := index_spec α d.prime _ hS hc
  exact congrArg (lift α) (theta_eq_of_mem d (actorLower α _)
    ((card_actorLower α _ hS).trans hc) hspec.2 (Subgroup.mem_closure_singleton_self _)
    hspec.1 ha)

theorem _root_.CFSG.SolvableSignalizer.Datum.exists_ne_one (d : Datum p α θ) : ∃ a : A, a ≠ 1 := by
  have : Nontrivial A := Finite.one_lt_card_iff_nontrivial.mp
    ((one_lt_pow₀ d.prime.one_lt two_ne_zero).trans_le d.rank_two)
  exact exists_ne 1

omit [Finite A] [Finite G] in
private theorem mem_Ek {S : Subgroup (Ambient α)} :
    S ∈ signalizerFunctorEk p 1 (actor α) ↔ S ≤ actor α ∧ Nat.card S = p := by
  simp [signalizerFunctorEk]

private theorem index_ne_one (d : Datum p α θ) {S : Subgroup (Ambient α)}
    (hS : S ∈ signalizerFunctorEk p 1 (actor α)) : index α S ≠ 1 :=
  (index_spec α d.prime S hS.1 (mem_Ek.mp hS).2).1

private theorem cyclicActor_mem (d : Datum p α θ) {a : A} (ha : a ≠ 1) :
    cyclicActor α a ∈ signalizerFunctorEk p 1 (actor α) :=
  mem_Ek.mpr ⟨cyclicActor_le α a, card_cyclicActor d ha⟩

private theorem theta_index_cyclicActor (d : Datum p α θ) {a : A} (ha : a ≠ 1) :
    θ (index α (cyclicActor α a)) = θ a :=
  lift_injective α (values_cyclicActor d ha)

private theorem primeSubfunctor_index_cyclicActor (d : Datum p α θ) (π : Set ℕ)
    {a : A} (ha : a ≠ 1) :
    primeSubfunctor α θ π (index α (cyclicActor α a)) = primeSubfunctor α θ π a := by
  unfold primeSubfunctor
  rw [theta_index_cyclicActor d ha]

private theorem centralizer_eq_index (d : Datum p α θ) {S : Subgroup (Ambient α)}
    (hS : S ∈ signalizerFunctorEk p 1 (actor α)) :
    Subgroup.centralizer (S : Set (Ambient α)) =
      Subgroup.centralizer ({actorEmbed α (index α S)} : Set (Ambient α)) := by
  have : Fact p.Prime := ⟨d.prime⟩
  have hs := index_spec α d.prime S hS.1 (mem_Ek.mp hS).2
  have hne : actorEmbed α (index α S) ≠ 1 :=
    fun h => hs.1 (actorEmbed_injective α (h.trans (map_one _).symm))
  calc Subgroup.centralizer (S : Set (Ambient α))
      _ = Subgroup.centralizer
          (Subgroup.closure {actorEmbed α (index α S)} : Set (Ambient α)) := by
        rw [closure_singleton_eq_of_card_eq_prime S (mem_Ek.mp hS).2 hs.2 hne]
      _ = _ := Subgroup.centralizer_closure _

private theorem iSup_Ek_index (d : Datum p α θ) {X : Type*} [CompleteLattice X]
    (f : A → X) (hf : ∀ a : A, a ≠ 1 → f (index α (cyclicActor α a)) = f a) :
    ⨆ S ∈ signalizerFunctorEk p 1 (actor α), f (index α S) = ⨆ (a : A) (_ : a ≠ 1), f a :=
  le_antisymm (iSup₂_le fun S hS => le_iSup₂_of_le (index α S) (index_ne_one d hS) le_rfl)
    (iSup₂_le fun a ha => hf a ha ▸ le_iSup₂_of_le (cyclicActor α a) (cyclicActor_mem d ha) le_rfl)

private theorem pow_le_card_actor (d : Datum p α θ) :
    p ^ 1 ≤ Nat.card (actor α) := by
  rw [card_actor, pow_one]
  exact (le_self_pow₀ d.prime.one_lt.le two_ne_zero).trans d.rank_two

theorem isElemAbelian_actor (d : Datum p α θ) : IsElemAbelian p (actor α) := by
  refine ⟨⟨⟨fun x y => ?_⟩⟩, ?_⟩
  · obtain ⟨_, a, rfl⟩ := x
    obtain ⟨_, b, rfl⟩ := y
    ext1
    simp only [Subgroup.coe_mul, ← map_mul, mul_comm a b]
  · rintro _ ⟨a, rfl⟩
    rw [← map_pow, d.exponent, map_one]

theorem solvableSignalizerConditions_values (d : Datum p α θ) :
    SolvableSignalizerConditions p 1 (actor α) (values α θ) := by
  refine ⟨fun S hS => ?_, fun S hS => ?_, fun S hS => ?_, fun S hS T hT => ?_, fun S hS => ?_⟩
  · rw [centralizer_eq_index d hS]
    rintro _ ⟨g, hg, rfl⟩
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      ((apply_eq_self_iff α _ g).mp (d.central _ (index_ne_one d hS) hg)).symm
  · rw [values, card_lift]
    exact d.coprime _ (index_ne_one d hS)
  · exact (isInvariant_iff_actor_le_normalizer α _).mp (d.invariant _ (index_ne_one d hS))
  · rw [centralizer_eq_index d hT, values, values, ← lift_fixedIn]
    exact Subgroup.map_mono (d.balance _ _ (index_ne_one d hS) (index_ne_one d hT))
  · exact (isSolvable_lift_iff α _).mpr (d.solvable _ (index_ne_one d hS))

theorem iSup_values_eq_lift_completion (d : Datum p α θ) :
    (⨆ S ∈ signalizerFunctorEk p 1 (actor α), values α θ S) = lift α (completion θ) := by
  rw [lift_completion]
  exact iSup_Ek_index d (fun a => lift α (θ a))
    fun a ha => congrArg (lift α) (theta_index_cyclicActor d ha)

theorem signalizerSpectrum_values (d : Datum p α θ) :
    signalizerSpectrum p 1 (actor α) (values α θ) = spectrum θ := by
  ext q
  simp only [signalizerSpectrum, spectrum, Set.mem_ofPred_eq]
  refine and_congr_right fun _ => ⟨?_, ?_⟩
  · rintro ⟨S, hS, hq⟩
    exact ⟨index α S, index_ne_one d hS, by rwa [values, card_lift] at hq⟩
  · rintro ⟨a, ha, hq⟩
    exact ⟨cyclicActor α a, cyclicActor_mem d ha, by rwa [values_cyclicActor d ha, card_lift]⟩

theorem signalizerCommonFixed_values (d : Datum p α θ) :
    signalizerCommonFixed p 1 (actor α) (values α θ) = lift α (commonSignalizerWhole θ) := by
  have hvalues (x : Ambient α) : x ∈ ⨅ S ∈ signalizerFunctorEk p 1 (actor α), values α θ S ↔
      ∀ S ∈ signalizerFunctorEk p 1 (actor α), x ∈ values α θ S := by
    simp only [Subgroup.mem_iInf]
  rw [signalizerCommonFixed]
  apply le_antisymm
  · intro x hx
    rw [Subgroup.mem_inf, hvalues] at hx
    obtain ⟨-, hx⟩ := hx
    obtain ⟨a, ha⟩ := CFSG.SolvableSignalizer.Datum.exists_ne_one d
    have hxa := hx _ (cyclicActor_mem d ha)
    rw [values_cyclicActor d ha] at hxa
    obtain ⟨g, -, rfl⟩ := hxa
    refine (mem_lift α _ g).mpr (mem_commonSignalizerWhole.mpr fun b hb => ?_)
    rw [← mem_lift α, ← values_cyclicActor d hb]
    exact hx _ (cyclicActor_mem d hb)
  · rintro _ ⟨g, hg, rfl⟩
    replace hg := mem_commonSignalizerWhole.mp hg
    refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_centralizer_iff.mpr ?_,
      (hvalues _).mpr fun S hS => (mem_lift α _ g).mpr (hg _ (index_ne_one d hS))⟩
    rintro _ ⟨a, rfl⟩
    by_cases ha : a = 1
    · simp [ha]
    · exact (apply_eq_self_iff α a g).mp (d.central a ha (hg a ha))

theorem signalizerPrimeValue_values (d : Datum p α θ) (π : Set ℕ)
    {S : Subgroup (Ambient α)} (_hS : S ∈ signalizerFunctorEk p 1 (actor α)) :
    signalizerPrimeValue p 1 (actor α) (values α θ) π S =
      lift α (primeSubfunctor α θ π (index α S)) := by
  rw [signalizerPrimeValue, signalizerCommonFixed_values d]
  apply le_antisymm
  · refine iSup₂_le fun V ⟨hU, hp, hi, hn⟩ => ?_
    have hVL : lift α (lower α V) = V :=
      lift_lower α V (hU.trans (Subgroup.map_mono le_top))
    rw [← hVL] at hU hp hi hn ⊢
    refine (lift_le_lift α).mpr (le_primeSubfunctor ((lift_le_lift α).mp hU)
      ((isInvariant_iff_actor_le_normalizer α _).mpr hi) ?_ ((lift_le_normalizer_lift _ _).mp hn))
    simpa [CFSG.SignalizerFunctor.Helpers.primeSupported,
      CFSG.primeSupported] using hp
  · refine Subgroup.map_le_iff_le_comap.mpr (iSup_le fun U => iSup_le fun hU =>
      iSup_le fun hi => iSup_le fun hp => iSup_le fun hn => Subgroup.map_le_iff_le_comap.mp ?_)
    refine le_iSup₂_of_le (lift α U) ⟨Subgroup.map_mono hU, ?_,
      (isInvariant_iff_actor_le_normalizer α U).mp hi, (lift_le_normalizer_lift _ _).mpr hn⟩ le_rfl
    simpa [CFSG.SignalizerFunctor.Helpers.primeSupported,
      CFSG.primeSupported] using hp

theorem compatible_iff_lift (d : Datum p α θ) (H : Subgroup G) :
    Compatible p α θ H ↔ solvableSignalizerCompatible p 1 (actor α) (values α θ) (lift α H) := by
  constructor
  · rintro ⟨hinv, hsolv, -, hcent⟩
    refine ⟨⟨(isInvariant_iff_actor_le_normalizer α H).mp hinv, fun S hS => ?_⟩,
      (isSolvable_lift_iff α H).mpr hsolv⟩
    rw [centralizer_eq_index d hS, ← lift_fixedIn]
    exact Subgroup.map_mono (hcent _ (index_ne_one d hS))
  · rintro ⟨⟨hinv, hcent⟩, hsolv⟩
    refine ⟨(isInvariant_iff_actor_le_normalizer α H).mpr hinv,
      (isSolvable_lift_iff α H).mp hsolv, ?_, fun a ha => ?_⟩
    · simpa using signalizer_subgroup_coprime p 1 d.prime (actor α) (isElemAbelian_actor d)
        (pow_le_card_actor d) (values α θ) (solvableSignalizerConditions_values d).coprime
        (lift α H) hinv hcent
    · have h := hcent (cyclicActor α a) (cyclicActor_mem d ha)
      rw [values_cyclicActor d ha, cyclicActor, Subgroup.centralizer_closure,
        ← lift_fixedIn] at h
      exact (lift_le_lift α).mp h

theorem compatible_lower (d : Datum p α θ) (H : Subgroup (Ambient α))
    (hH : solvableSignalizerCompatible p 1 (actor α) (values α θ) H) :
    Compatible p α θ (lower α H) ∧ lift α (lower α H) = H := by
  have heq := lift_lower_of_coprime α p d.exponent H
    (signalizer_subgroup_coprime p 1 d.prime (actor α) (isElemAbelian_actor d) (pow_le_card_actor d)
      (values α θ) (solvableSignalizerConditions_values d).coprime H hH.1.1 hH.1.2)
  exact ⟨(compatible_iff_lift d _).mpr (heq.symm ▸ hH), heq⟩

theorem iSup_signalizerRestriction_values (d : Datum p α θ) (U : Subgroup G) :
    (⨆ S ∈ signalizerFunctorEk p 1 (actor α), signalizerRestriction (values α θ)
      (Subgroup.normalizer (lift α U : Set (Ambient α))) S) =
        lift α (completionIn θ (Subgroup.normalizer (U : Set G))) := by
  rw [lift_completionIn_normalizer]
  exact iSup_Ek_index d
    (fun a => lift α (θ a) ⊓ Subgroup.normalizer (lift α U : Set (Ambient α)))
    fun a ha => by simp only [theta_index_cyclicActor d ha]

theorem iSup_signalizerPrimeValue_values (d : Datum p α θ) (π : Set ℕ) :
    (⨆ S ∈ signalizerFunctorEk p 1 (actor α),
      signalizerPrimeValue p 1 (actor α) (values α θ) π S) =
        lift α (completion (primeSubfunctor α θ π)) := by
  have h : (⨆ S ∈ signalizerFunctorEk p 1 (actor α),
      signalizerPrimeValue p 1 (actor α) (values α θ) π S) =
      ⨆ S ∈ signalizerFunctorEk p 1 (actor α), lift α (primeSubfunctor α θ π (index α S)) :=
    iSup_congr fun S => iSup_congr fun hS => signalizerPrimeValue_values d π hS
  rw [h, lift_completion]
  exact iSup_Ek_index d (fun a => lift α (primeSubfunctor α θ π a))
    fun a ha => congrArg (lift α) (primeSubfunctor_index_cyclicActor d π ha)

theorem maxCompatible_iff (d : Datum p α θ) (π : Set ℕ) (H : Subgroup G) :
    MaxCompatible p α θ π H ↔
      (solvableSignalizerCompatible p 1 (actor α) (values α θ) (lift α H) ∧
        CFSG.SignalizerFunctor.Helpers.primeSupported π (Nat.card (lift α H))) ∧
      ∀ K : Subgroup (Ambient α),
        (solvableSignalizerCompatible p 1 (actor α) (values α θ) K ∧
          CFSG.SignalizerFunctor.Helpers.primeSupported π (Nat.card K)) →
        lift α H ≤ K → K ≤ lift α H := by
  have hat (U : Subgroup G) : CompatibleAt p α θ π U ↔
      solvableSignalizerCompatible p 1 (actor α) (values α θ) (lift α U) ∧
        CFSG.SignalizerFunctor.Helpers.primeSupported π (Nat.card (lift α U)) := by
    simp only [CompatibleAt, compatible_iff_lift d, card_lift,
      CFSG.primeSupported,
      CFSG.SignalizerFunctor.Helpers.primeSupported]
  constructor
  · rintro ⟨hH, hmax⟩
    refine ⟨(hat H).mp hH, fun K hK hHK => ?_⟩
    obtain ⟨-, heq⟩ := compatible_lower d K hK.1
    rw [← heq] at hK hHK ⊢
    exact Subgroup.map_mono (hmax _ ((hat _).mpr hK) ((lift_le_lift α).mp hHK))
  · rintro ⟨hH, hmax⟩
    exact ⟨(hat H).mpr hH, fun K hK hHK =>
      (lift_le_lift α).mp (hmax (lift α K) ((hat K).mp hK) (Subgroup.map_mono hHK))⟩

private theorem compatible_primeSubfunctor_iff (d : Datum p α θ) (π : Set ℕ)
    (H : Subgroup G) :
    Compatible p α (primeSubfunctor α θ π) H ↔
      solvableSignalizerCompatible p 1 (actor α)
        (signalizerPrimeValue p 1 (actor α) (values α θ) π) (lift α H) := by
  constructor
  · rintro ⟨hinv, hsolv, -, hcent⟩
    refine ⟨⟨(isInvariant_iff_actor_le_normalizer α H).mp hinv, fun S hS => ?_⟩,
      (isSolvable_lift_iff α H).mpr hsolv⟩
    rw [signalizerPrimeValue_values d π hS, centralizer_eq_index d hS, ← lift_fixedIn]
    exact Subgroup.map_mono (hcent _ (index_ne_one d hS))
  · rintro ⟨⟨hinv, hcent⟩, hsolv⟩
    have hcop := signalizer_subgroup_coprime p 1 d.prime (actor α) (isElemAbelian_actor d)
      (pow_le_card_actor d) _ (solvable_signalizer_prime_subfunctor_conditions p 1 d.prime
        (actor α) (isElemAbelian_actor d) (values α θ)
        (solvableSignalizerConditions_values d) π).coprime
      (lift α H) hinv hcent
    refine ⟨(isInvariant_iff_actor_le_normalizer α H).mpr hinv, (isSolvable_lift_iff α H).mp hsolv,
      by simpa using hcop, fun a ha => ?_⟩
    have h := hcent (cyclicActor α a) (cyclicActor_mem d ha)
    rw [signalizerPrimeValue_values d π (cyclicActor_mem d ha),
      primeSubfunctor_index_cyclicActor d π ha, cyclicActor, Subgroup.centralizer_closure,
      ← lift_fixedIn] at h
    exact (lift_le_lift α).mp h

theorem locallyComplete_iff (d : Datum p α θ) :
    LocallyComplete p α θ ↔ solvableSignalizerLocallyComplete p 1 (actor α) (values α θ) := by
  constructor
  · rintro ⟨hnorm, hprime⟩
    refine ⟨fun K hne hK => ?_, fun q hq => ?_⟩
    · obtain ⟨hU, heq⟩ := compatible_lower d K hK
      have hUne : lower α K ≠ ⊥ := fun hbot =>
        hne (heq.symm.trans ((congrArg (lift α) hbot).trans (Subgroup.map_bot _)))
      rw [← heq, iSup_signalizerRestriction_values d]
      exact (compatible_iff_lift d _).mp (hnorm _ hU hUne)
    · rw [signalizerSpectrum_values d] at hq ⊢
      rw [iSup_signalizerPrimeValue_values d]
      exact (compatible_primeSubfunctor_iff d _ _).mp (hprime q hq)
  · rintro ⟨hnorm, hprime⟩
    refine ⟨fun U hU hne => ?_, fun q hq => ?_⟩
    · have hUne : lift α U ≠ ⊥ := fun hbot =>
        hne (lift_injective α (hbot.trans (Subgroup.map_bot _).symm))
      have h := hnorm (lift α U) hUne ((compatible_iff_lift d U).mp hU)
      rw [iSup_signalizerRestriction_values d U] at h
      exact (compatible_iff_lift d _).mpr h
    · have h := hprime q (by rwa [signalizerSpectrum_values d])
      rw [signalizerSpectrum_values d, iSup_signalizerPrimeValue_values d] at h
      exact (compatible_primeSubfunctor_iff d _ _).mpr h

end RankOne

end CFSG.SolvableSignalizer.Internal
