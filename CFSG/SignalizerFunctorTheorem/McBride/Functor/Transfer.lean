module

public import CFSG.LocalAnalysis.SignalizerFunctor.SignalizerImageLifting
public import CFSG.SignalizerFunctorTheorem.McBride.Defs

public section

open CFSG.Open

namespace CFSG.SignalizerFunctorTheorem.McBride

variable {G : Type*} [Group G] {p : ℕ} {A : Subgroup G} {θ : G → Subgroup G}

@[expose] def pullFunctor {H : Type*} [Group H] (ι : H →* G) (θ : G → Subgroup G) :
    H → Subgroup H :=
  fun a => (θ (ι a)).comap ι

theorem IsFunctor.pullFunctor {H : Type*} [Group H] (ι : H →* G) (hι : Function.Injective ι)
    {A : Subgroup H} (hθ : IsFunctor p (A.map ι) θ) : IsFunctor p A (pullFunctor ι θ) := by
  have hmem : ∀ a ∈ A, a ≠ 1 → ι a ∈ A.map ι ∧ ι a ≠ 1 := fun a ha ha1 =>
    ⟨Subgroup.mem_map_of_mem ι ha, fun h => ha1 (hι (h.trans (map_one ι).symm))⟩
  refine ⟨fun a ha ha1 x hx => ?_, fun a ha ha1 => ?_, fun a ha ha1 => ?_,
    fun a ha ha1 b hb hb1 x hx => ?_⟩
  · obtain ⟨h1, h2⟩ := hmem a ha ha1
    have h := hθ.le_centralizer (ι a) h1 h2 hx
    rw [Subgroup.mem_centralizer_singleton_iff] at h ⊢
    apply hι
    simpa only [map_mul] using h
  · obtain ⟨h1, h2⟩ := hmem a ha ha1
    exact (hθ.coprime (ι a) h1 h2).coprime_dvd_right
      (Subgroup.card_comap_dvd_of_injective _ ι hι)
  · obtain ⟨h1, h2⟩ := hmem a ha ha1
    have hn := hθ.normalized (ι a) h1 h2
    intro a' ha' x
    have h := Subgroup.mem_normalizer_iff.mp (hn (Subgroup.mem_map_of_mem ι ha')) (ι x)
    change ι x ∈ θ (ι a) ↔ ι (a' * x * a'⁻¹) ∈ θ (ι a)
    simpa only [map_mul, map_inv] using h
  · obtain ⟨h1, h2⟩ := hmem a ha ha1
    obtain ⟨h3, h4⟩ := hmem b hb hb1
    have hx1 : ι x ∈ θ (ι a) := hx.1
    have hx2 : x ∈ Subgroup.centralizer {b} := hx.2
    have hxb : ι x ∈ Subgroup.centralizer {ι b} := by
      rw [Subgroup.mem_centralizer_singleton_iff] at hx2 ⊢
      simpa only [map_mul] using congrArg ι hx2
    exact hθ.balance (ι a) h1 h2 (ι b) h3 h4 ⟨hx1, hxb⟩

theorem mem_signalizers_pullFunctor_iff {H : Type*} [Group H] (ι : H →* G)
    (hι : Function.Injective ι) {A X : Subgroup H} {P : Subgroup H → Prop}
    {P' : Subgroup G → Prop} (hPP' : ∀ Y : Subgroup H, P Y ↔ P' (Y.map ι)) :
    X ∈ signalizers p A (pullFunctor ι θ) P ↔ X.map ι ∈ signalizers p (A.map ι) θ P' := by
  have hnorm : A ≤ Subgroup.normalizer (X : Set H) ↔
      A.map ι ≤ Subgroup.normalizer ((X.map ι : Subgroup G) : Set G) := by
    refine ⟨CFSG.SignalizerFunctor.Helpers.normalizer_image_le ι A X, fun h a ha => ?_⟩
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have h1 := Subgroup.mem_normalizer_iff.mp (h (Subgroup.mem_map_of_mem ι ha)) (ι x)
    have h2 : ι x ∈ X.map ι ↔ ι (a * x * a⁻¹) ∈ X.map ι := by
      simpa only [map_mul, map_inv] using h1
    rwa [Subgroup.mem_map_iff_mem hι, Subgroup.mem_map_iff_mem hι] at h2
  have hcard : Nat.card (X.map ι) = Nat.card X := Subgroup.card_map_of_injective hι
  unfold signalizers
  simp only [Set.mem_ofPred_eq]
  rw [hnorm, hcard, hPP' X]
  refine and_congr Iff.rfl (and_congr Iff.rfl (and_congr ?_ Iff.rfl))
  constructor
  · intro h b hb hb1
    obtain ⟨a, ha, rfl⟩ := hb
    have ha1 : a ≠ 1 := fun h' => hb1 (by rw [h', map_one])
    rintro y ⟨⟨x, hx, rfl⟩, hy⟩
    have hy' : ι x ∈ Subgroup.centralizer {ι a} := hy
    have hxa : x ∈ Subgroup.centralizer {a} := by
      rw [Subgroup.mem_centralizer_singleton_iff] at hy' ⊢
      apply hι
      simpa only [map_mul] using hy'
    exact h a ha ha1 ⟨hx, hxa⟩
  · intro h a ha ha1 x hx
    have ha1' : ι a ≠ 1 := fun h' => ha1 (hι (h'.trans (map_one ι).symm))
    have hx1 : x ∈ X := hx.1
    have hx2 : x ∈ Subgroup.centralizer {a} := hx.2
    have hxa : ι x ∈ Subgroup.centralizer {ι a} := by
      rw [Subgroup.mem_centralizer_singleton_iff] at hx2 ⊢
      simpa only [map_mul] using congrArg ι hx2
    exact h (ι a) (Subgroup.mem_map_of_mem ι ha) ha1' ⟨Subgroup.mem_map_of_mem ι hx1, hxa⟩

theorem isCompleteIn_signalizers_pullFunctor_iff {H : Type*} [Group H] (ι : H →* G)
    (hι : Function.Injective ι) {A : Subgroup H} {P : Subgroup H → Prop}
    {P' : Subgroup G → Prop} (hPP' : ∀ Y : Subgroup H, P Y ↔ P' (Y.map ι)) :
    IsCompleteIn (signalizers p A (pullFunctor ι θ) P) ↔
      ∃ W ∈ signalizers p (A.map ι) θ P', W ≤ ι.range ∧
        ∀ Y ∈ signalizers p (A.map ι) θ P', Y ≤ ι.range → Y ≤ W := by
  constructor
  · rintro ⟨W₀, hW₀, hmax⟩
    refine ⟨W₀.map ι, (mem_signalizers_pullFunctor_iff ι hι hPP').mp hW₀,
      Subgroup.map_le_range ι W₀, fun Y hY hYr => ?_⟩
    have hmem : Y.comap ι ∈ signalizers p A (pullFunctor ι θ) P := by
      rw [mem_signalizers_pullFunctor_iff ι hι hPP', Subgroup.map_comap_eq_self hYr]
      exact hY
    calc Y = (Y.comap ι).map ι := (Subgroup.map_comap_eq_self hYr).symm
      _ ≤ W₀.map ι := Subgroup.map_mono (hmax _ hmem)
  · rintro ⟨W, hW, hWr, hmax⟩
    have hWc : (W.comap ι).map ι = W := Subgroup.map_comap_eq_self hWr
    refine ⟨W.comap ι, ?_, fun X hX => ?_⟩
    · rw [mem_signalizers_pullFunctor_iff ι hι hPP', hWc]
      exact hW
    · have hXm := (mem_signalizers_pullFunctor_iff ι hι hPP').mp hX
      exact Subgroup.map_le_iff_le_comap.mp (hmax _ hXm (Subgroup.map_le_range ι X))

theorem pullFunctor_subtype_apply {K : Subgroup G} (a : K) :
    pullFunctor K.subtype θ a = (θ a).subgroupOf K := rfl

@[expose] def imageFunctor {H : Type*} [Group H] (f : G →* H) (A : Subgroup G)
    (θ : G → Subgroup G) : H → Subgroup H :=
  fun y => ⨆ (a : G) (_ : a ∈ A) (_ : f a = y), (θ a).map f

theorem imageFunctor_apply {H : Type*} [Group H] {f : G →* H} (hf : Set.InjOn f A) {a : G}
    (ha : a ∈ A) : imageFunctor f A θ (f a) = (θ a).map f := by
  unfold imageFunctor
  apply le_antisymm
  · refine iSup_le fun b => iSup_le fun hb => iSup_le fun hfb => ?_
    obtain rfl : b = a := hf hb ha hfb
    exact le_rfl
  · exact le_iSup_of_le a (le_iSup_of_le ha (le_iSup_of_le rfl le_rfl))

theorem injOn_of_coprime_ker [Finite G] (hp : p.Prime) (hA : IsElemAbelian p A)
    {H : Type*} [Group H] {f : G →* H} (hker : Nat.Coprime p (Nat.card f.ker)) :
    Set.InjOn f A := by
  have hinj := CFSG.SignalizerFunctor.Helpers.actor_image_injective_of_coprime_kernel p hp f A
    (CFSG.SignalizerFunctor.Helpers.elementary_abelian_isPGroup p A hA) hker
  intro a ha b hb hab
  exact congrArg Subtype.val (@hinj ⟨a, ha⟩ ⟨b, hb⟩ hab)

theorem map_inf_centralizer_singleton {H : Type*} [Group H] (hp : p.Prime)
    (hA : IsElemAbelian p A) (f : G →* H) {X : Subgroup G}
    (hAX : A ≤ Subgroup.normalizer (X : Set G)) (hX : Nat.Coprime p (Nat.card X)) {b : G}
    (hb : b ∈ A) :
    (X ⊓ Subgroup.centralizer {b}).map f = X.map f ⊓ Subgroup.centralizer {f b} := by
  have hz : Subgroup.zpowers b ≤ A := Subgroup.zpowers_le.mpr hb
  have h := CFSG.SignalizerFunctor.Helpers.coprime_centralizer_image p hp f (Subgroup.zpowers b) X
    ((CFSG.SignalizerFunctor.Helpers.elementary_abelian_isPGroup p A hA).to_le hz)
    (hz.trans hAX) hX
  rw [MonoidHom.map_zpowers] at h
  simpa only [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure] using h

theorem IsFunctor.imageFunctor [Finite G] (hp : p.Prime) (hA : IsElemAbelian p A)
    (hθ : IsFunctor p A θ) {H : Type*} [Group H] {f : G →* H} (hf : Set.InjOn f A) :
    IsFunctor p (A.map f) (imageFunctor f A θ) := by
  have key : ∀ x ∈ A.map f, x ≠ 1 → ∃ a ∈ A, a ≠ 1 ∧ f a = x := by
    rintro _ ⟨a, ha, rfl⟩ hx1
    exact ⟨a, ha, fun h => hx1 (by rw [h, map_one]), rfl⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx hx1
    obtain ⟨a, ha, ha1, rfl⟩ := key x hx hx1
    rw [imageFunctor_apply hf ha]
    rintro _ ⟨t, ht, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have := Subgroup.mem_centralizer_singleton_iff.mp (hθ.le_centralizer a ha ha1 ht)
    simpa only [← map_mul] using congrArg f this
  · intro x hx hx1
    obtain ⟨a, ha, ha1, rfl⟩ := key x hx hx1
    rw [imageFunctor_apply hf ha]
    exact (hθ.coprime a ha ha1).coprime_dvd_right (Subgroup.card_map_dvd _ f)
  · intro x hx hx1
    obtain ⟨a, ha, ha1, rfl⟩ := key x hx hx1
    rw [imageFunctor_apply hf ha]
    exact CFSG.SignalizerFunctor.Helpers.normalizer_image_le f A (θ a) (hθ.normalized a ha ha1)
  · intro x hx hx1 y hy hy1
    obtain ⟨a, ha, ha1, rfl⟩ := key x hx hx1
    obtain ⟨b, hb, hb1, rfl⟩ := key y hy hy1
    rw [imageFunctor_apply hf ha, imageFunctor_apply hf hb,
      ← map_inf_centralizer_singleton hp hA f (hθ.normalized a ha ha1) (hθ.coprime a ha ha1) hb]
    exact Subgroup.map_mono (hθ.balance a ha ha1 b hb hb1)

theorem map_mem_signalizers_imageFunctor [Finite G] (hp : p.Prime) (hA : IsElemAbelian p A)
    {H : Type*} [Group H] {f : G →* H} (hf : Set.InjOn f A)
    {P : Subgroup G → Prop} {P' : Subgroup H → Prop} {X : Subgroup G}
    (hX : X ∈ signalizers p A θ P) (hP : P' (X.map f)) :
    X.map f ∈ signalizers p (A.map f) (imageFunctor f A θ) P' := by
  obtain ⟨hAX, hXp, hXθ, -⟩ := hX
  refine ⟨CFSG.SignalizerFunctor.Helpers.normalizer_image_le f A X hAX,
    hXp.coprime_dvd_right (Subgroup.card_map_dvd _ f), ?_, hP⟩
  rintro _ ⟨a, ha, rfl⟩ hy1
  have ha1 : a ≠ 1 := fun h => hy1 (by rw [h, map_one])
  rw [imageFunctor_apply hf ha, ← map_inf_centralizer_singleton hp hA f hAX hXp ha]
  exact Subgroup.map_mono (hXθ a ha ha1)

end CFSG.SignalizerFunctorTheorem.McBride
