module

public import CFSG.SignalizerFunctorTheorem.Glauberman.Basic
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

open CFSG.Open CFSG.SignalizerFunctorTheorem.Glauberman

namespace CFSG.SignalizerFunctorTheorem.Quadratic

variable {G : Type*} [Group G] [Finite G] (q : ℕ)

omit [Finite G] in
theorem thompsonJ_le (T : Subgroup G) : thompsonJ q T ≤ T :=
  sSup_le fun _ hE => hE.1

namespace ThompsonJAux

omit [Finite G] in
theorem mem_omegaCenter_iff {T : Subgroup G} {z : G} :
    z ∈ omegaCenter q T ↔ z ∈ T ∧ (∀ t ∈ T, z * t = t * z) ∧ z ^ q = 1 :=
  Iff.rfl

section Map

variable {G' : Type*} [Group G'] (f : G →* G') {T : Subgroup G}

omit [Finite G] in
theorem card_map_of_le_of_injOn (hf : ∀ x ∈ T, ∀ y ∈ T, f x = f y → x = y) {E : Subgroup G}
    (hE : E ≤ T) : Nat.card (E.map f) = Nat.card E := by
  symm
  refine Nat.card_congr (Equiv.ofBijective
    (fun x : E => (⟨f x, Subgroup.mem_map_of_mem f x.2⟩ : E.map f)) ⟨?_, ?_⟩)
  · intro x y h
    exact Subtype.ext (hf x (hE x.2) y (hE y.2) (congrArg Subtype.val h))
  · rintro ⟨_, x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩

omit [Finite G] in
theorem isElemAbelian_map {E : Subgroup G} (hE : IsElemAbelian q E) :
    IsElemAbelian q (E.map f) := CFSG.Open.IsElemAbelian.map hE _

omit [Finite G] in
theorem isElemAbelian_of_map (hf : ∀ x ∈ T, ∀ y ∈ T, f x = f y → x = y) {E : Subgroup G}
    (hE : E ≤ T) (h : IsElemAbelian q (E.map f)) : IsElemAbelian q E := by
  obtain ⟨hc, hx⟩ := h
  refine ⟨⟨⟨fun x y => ?_⟩⟩, fun x hxE => ?_⟩
  · apply Subtype.ext
    have h1 : f (x * y) = f (y * x) := by
      rw [map_mul, map_mul]
      exact congrArg Subtype.val (mul_comm' (⟨f x, Subgroup.mem_map_of_mem f x.2⟩ : E.map f)
        ⟨f y, Subgroup.mem_map_of_mem f y.2⟩)
    exact hf _ (T.mul_mem (hE x.2) (hE y.2)) _ (T.mul_mem (hE y.2) (hE x.2)) h1
  · apply hf _ (T.pow_mem (hE hxE) q) 1 T.one_mem
    rw [map_pow, map_one]
    exact hx _ (Subgroup.mem_map_of_mem f hxE)

omit [Finite G] in
theorem map_inf_comap_of_le {E : Subgroup G'} (h : E ≤ T.map f) :
    (T ⊓ E.comap f).map f = E := by
  apply le_antisymm
  · rintro _ ⟨x, ⟨_, hx⟩, rfl⟩
    exact hx
  · intro y hy
    obtain ⟨x, hxT, rfl⟩ := h hy
    exact ⟨x, ⟨hxT, hy⟩, rfl⟩

end Map

omit [Finite G] in
theorem map_conj_eq_self_of_mem_normalizer {H : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (H : Set G)) : H.map (MulAut.conj g).toMonoidHom = H := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hg y).mp hy
  · intro hx
    refine ⟨g⁻¹ * x * g, ?_, by simp [MulAut.conj_apply, mul_assoc]⟩
    refine (Subgroup.mem_normalizer_iff.mp hg _).mpr ?_
    simpa [mul_assoc] using hx

omit [Finite G] in
theorem mem_normalizer_of_map_conj_eq {H : Subgroup G} {g : G}
    (h : H.map (MulAut.conj g).toMonoidHom = H) : g ∈ Subgroup.normalizer (H : Set G) := by
  refine Subgroup.mem_normalizer_iff.mpr fun x => ⟨fun hx => ?_, fun hx => ?_⟩
  · rw [← h]
    exact Subgroup.mem_map_of_mem _ hx
  · rw [← h] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    have : y = x := (MulAut.conj g).injective hyx
    rwa [← this]

end ThompsonJAux

open ThompsonJAux

omit [Finite G] in
theorem omegaCenter_le (T : Subgroup G) : omegaCenter q T ≤ T := fun _ hz =>
  ((mem_omegaCenter_iff q).mp hz).1

omit [Finite G] in
theorem map_thompsonJ {G' : Type*} [Group G'] (f : G →* G') {T : Subgroup G}
    (hf : ∀ x ∈ T, ∀ y ∈ T, f x = f y → x = y) :
    (thompsonJ q T).map f = thompsonJ q (T.map f) := by
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap]
    refine sSup_le fun E hE => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    refine le_sSup ⟨Subgroup.map_mono hE.1, isElemAbelian_map q f hE.2.1,
      fun E'' hE''T hE''a => ?_⟩
    have h1 := map_inf_comap_of_le f hE''T
    have hFT : T ⊓ E''.comap f ≤ T := inf_le_left
    have hFa : IsElemAbelian q (T ⊓ E''.comap f) :=
      isElemAbelian_of_map q f hf hFT (by rw [h1]; exact hE''a)
    calc Nat.card E'' = Nat.card ((T ⊓ E''.comap f).map f) := by rw [h1]
      _ = Nat.card (T ⊓ E''.comap f : Subgroup G) := card_map_of_le_of_injOn f hf hFT
      _ ≤ Nat.card E := hE.2.2 _ hFT hFa
      _ = Nat.card (E.map f) := (card_map_of_le_of_injOn f hf hE.1).symm
  · refine sSup_le fun E' hE' => ?_
    have h1 := map_inf_comap_of_le f hE'.1
    have hFT : T ⊓ E'.comap f ≤ T := inf_le_left
    have hFa : IsElemAbelian q (T ⊓ E'.comap f) :=
      isElemAbelian_of_map q f hf hFT (by rw [h1]; exact hE'.2.1)
    rw [← h1]
    refine Subgroup.map_mono (le_sSup ⟨hFT, hFa, fun E'' hE''T hE''a => ?_⟩)
    calc Nat.card E'' = Nat.card (E''.map f) := (card_map_of_le_of_injOn f hf hE''T).symm
      _ ≤ Nat.card E' := hE'.2.2 _ (Subgroup.map_mono hE''T) (isElemAbelian_map q f hE''a)
      _ = Nat.card ((T ⊓ E'.comap f).map f) := by rw [h1]
      _ = Nat.card (T ⊓ E'.comap f : Subgroup G) := card_map_of_le_of_injOn f hf hFT

omit [Finite G] in
theorem map_omegaCenter {G' : Type*} [Group G'] (f : G →* G') {T : Subgroup G}
    (hf : ∀ x ∈ T, ∀ y ∈ T, f x = f y → x = y) :
    (omegaCenter q T).map f = omegaCenter q (T.map f) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨hxT, hxc, hxq⟩ := (mem_omegaCenter_iff q).mp hx
    refine (mem_omegaCenter_iff q).mpr ⟨Subgroup.mem_map_of_mem f hxT, ?_, ?_⟩
    · rintro _ ⟨t, htT, rfl⟩
      rw [← map_mul, ← map_mul, hxc t htT]
    · rw [← map_pow, hxq, map_one]
  · intro hy
    obtain ⟨⟨x, hxT, rfl⟩, hyc, hyq⟩ := (mem_omegaCenter_iff q).mp hy
    refine ⟨x, (mem_omegaCenter_iff q).mpr ⟨hxT, fun t htT => ?_, ?_⟩, rfl⟩
    · apply hf _ (T.mul_mem hxT htT) _ (T.mul_mem htT hxT)
      rw [map_mul, map_mul]
      exact hyc (f t) (Subgroup.mem_map_of_mem f htT)
    · apply hf _ (T.pow_mem hxT q) 1 T.one_mem
      rw [map_pow, map_one]
      exact hyq

omit [Finite G] in
theorem cj_thompsonJ (g : G) (T : Subgroup G) :
    (thompsonJ q T).map (MulAut.conj g).toMonoidHom =
      thompsonJ q (T.map (MulAut.conj g).toMonoidHom) :=
  map_thompsonJ q _ fun _ _ _ _ h => (MulAut.conj g).injective h

omit [Finite G] in
theorem cj_omegaCenter (g : G) (T : Subgroup G) :
    (omegaCenter q T).map (MulAut.conj g).toMonoidHom =
      omegaCenter q (T.map (MulAut.conj g).toMonoidHom) :=
  map_omegaCenter q _ fun _ _ _ _ h => (MulAut.conj g).injective h

theorem thompsonJ_eq_of_le {T T' : Subgroup G} (h1 : thompsonJ q T ≤ T') (h2 : T' ≤ T) :
    thompsonJ q T' = thompsonJ q T := by
  obtain ⟨E₀, ⟨hE₀T, hE₀a⟩, hE₀max⟩ := Set.exists_max_image
    {E : Subgroup G | E ≤ T ∧ IsElemAbelian q E} (fun E => Nat.card E) (Set.toFinite _)
    ⟨⊥, bot_le, ⟨inferInstance, fun x hx => by
      rw [Subgroup.mem_bot.mp hx, one_pow]⟩⟩
  have hE₀ : E₀ ≤ thompsonJ q T := le_sSup ⟨hE₀T, hE₀a, fun E' hE'T hE'a => hE₀max E' ⟨hE'T, hE'a⟩⟩
  unfold thompsonJ
  congr 1
  ext E
  constructor
  · rintro ⟨hET', hEa, hEmax⟩
    refine ⟨hET'.trans h2, hEa, fun E' hE'T hE'a => ?_⟩
    exact (hE₀max E' ⟨hE'T, hE'a⟩).trans (hEmax E₀ (hE₀.trans h1) hE₀a)
  · intro hE
    have hET' : E ≤ T' := (le_sSup hE).trans h1
    exact ⟨hET', hE.2.1, fun E' hE'T hE'a => hE.2.2 E' (hE'T.trans h2) hE'a⟩

omit [Finite G] in
theorem mem_normalizer_thompsonJ {T : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (T : Set G)) :
    g ∈ Subgroup.normalizer (thompsonJ q T : Set G) := by
  have h := cj_thompsonJ q g T
  rw [map_conj_eq_self_of_mem_normalizer hg] at h
  exact mem_normalizer_of_map_conj_eq h

omit [Finite G] in
theorem mem_normalizer_omegaCenter {T : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (T : Set G)) :
    g ∈ Subgroup.normalizer (omegaCenter q T : Set G) := by
  have h := cj_omegaCenter q g T
  rw [map_conj_eq_self_of_mem_normalizer hg] at h
  exact mem_normalizer_of_map_conj_eq h

theorem thompsonJ_le_of_isSylowOf (hq : q.Prime) {U S : Subgroup G} (hS : IsSylowOf q S U) :
    thompsonJ q S ≤ thompsonJ q U := by
  have := Fact.mk hq
  obtain ⟨P, hPS⟩ := hS
  refine sSup_le fun E hE => le_sSup ⟨hE.1.trans (hPS ▸ Subgroup.map_subtype_le _), hE.2.1,
    fun E' hE'U hE'a => ?_⟩
  have hpg : IsPGroup q (E'.subgroupOf U) := fun x => ⟨1, by
    rw [pow_one]
    apply Subtype.ext
    apply Subtype.ext
    simpa using hE'a.2 (x : U) x.2⟩
  obtain ⟨P', hP'⟩ := hpg.exists_le_sylow
  obtain ⟨u, hu⟩ := MulAction.exists_smul_eq U P' P
  have hconj : E'.map (MulAut.conj (u : G)).toMonoidHom ≤ S := by
    rintro _ ⟨x, hx, rfl⟩
    have hxU : x ∈ U := hE'U hx
    have h1 : (⟨x, hxU⟩ : U) ∈ (P' : Subgroup U) := hP' hx
    have h2 : MulAut.conj u ⟨x, hxU⟩ ∈ (P : Subgroup U) := by
      rw [← hu, Sylow.smul_def, Sylow.pointwise_smul_def]
      exact Subgroup.smul_mem_pointwise_smul _ _ _ h1
    rw [← hPS]
    exact ⟨_, h2, rfl⟩
  calc Nat.card E' = Nat.card (E'.map (MulAut.conj (u : G)).toMonoidHom) :=
      (Subgroup.card_map_of_injective (MulAut.conj (u : G)).injective).symm
    _ ≤ Nat.card E := hE.2.2 _ hconj (isElemAbelian_map q _ hE'a)

omit [Finite G] in
theorem le_thompsonJ {U E : Subgroup G} (hE : E ≤ U) (hEa : IsElemAbelian q E)
    (hmax : ∀ E' : Subgroup G, E' ≤ U → IsElemAbelian q E' → Nat.card E' ≤ Nat.card E) :
    E ≤ thompsonJ q U :=
  le_sSup ⟨hE, hEa, hmax⟩

end CFSG.SignalizerFunctorTheorem.Quadratic
