module

public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Semisimple
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec2.Thm210SetupGlobal

public section

open CFSG.Open

namespace CFSG.SignalizerFunctorTheorem.McBride.Near

open Thm210

variable {Γ : Type*} [Group Γ]

theorem Thm210.conj_eq_coord_conj [Finite Γ] {S : Set (Subgroup Γ)} {L : Subgroup Γ}
    (hL : IsDirectProduct S L) {J : Subgroup Γ} (hJ : J ∈ S) {y : Γ} (hy : y ∈ L) {n : Γ}
    (hn : n ∈ J) :
    y * n * y⁻¹ = ((hL.coord hJ ⟨y, hy⟩ : J) : Γ) * n * ((hL.coord hJ ⟨y, hy⟩ : J) : Γ)⁻¹ := by
  set c : Γ := ((hL.coord hJ ⟨y, hy⟩ : J) : Γ) with hc
  have hcL : c ∈ L := hL.le hJ (hL.coord hJ ⟨y, hy⟩).2
  have hl : c⁻¹ * y ∈ sSup (S \ {J}) := by
    rw [← hL.coord_eq_one_iff hJ ⟨c⁻¹ * y, mul_mem (inv_mem hcL) hy⟩]
    have : (⟨c⁻¹ * y, mul_mem (inv_mem hcL) hy⟩ : L) = ⟨c⁻¹, inv_mem hcL⟩ * ⟨y, hy⟩ := rfl
    rw [this, map_mul]
    have h1 : hL.coord hJ ⟨c⁻¹, inv_mem hcL⟩ = (hL.coord hJ ⟨y, hy⟩)⁻¹ :=
      Subtype.ext (hL.coord_of_mem hJ (inv_mem (hL.coord hJ ⟨y, hy⟩).2))
    rw [h1, inv_mul_cancel]
  have hcomm : n * (c⁻¹ * y) = (c⁻¹ * y) * n := (hL.commute_sSup_diff hJ n hn _ hl).eq
  calc y * n * y⁻¹ = c * ((c⁻¹ * y) * n) * (c⁻¹ * y)⁻¹ * c⁻¹ := by group
    _ = c * (n * (c⁻¹ * y)) * (c⁻¹ * y)⁻¹ * c⁻¹ := by rw [hcomm]
    _ = c * n * c⁻¹ := by group

section Abstract

variable {H : Type*} [Group H] [Finite H]

theorem Thm210.exists_conj_map_sSup_eq {𝓛 : Set (Subgroup H)} (hL : IsDirectProduct 𝓛 ⊤)
    (K : Subgroup H → Subgroup H) (hK : ∀ J ∈ 𝓛, K J ≤ J) (φ : MulAut H)
    (hφ : ∀ J ∈ 𝓛, J.map φ.toMonoidHom ∈ 𝓛) (hφ' : ∀ J ∈ 𝓛, J.map φ.symm.toMonoidHom ∈ 𝓛)
    (hconj : ∀ J ∈ 𝓛, ∃ i ∈ J.map φ.toMonoidHom,
      (K J).map φ.toMonoidHom = (K (J.map φ.toMonoidHom)).map (MulAut.conj i).toMonoidHom) :
    ∃ g : H, ((sSup {X | ∃ J ∈ 𝓛, X = K J}).map φ.toMonoidHom).map (MulAut.conj g).toMonoidHom =
      sSup {X | ∃ J ∈ 𝓛, X = K J} := by
  classical
  have hmm : ∀ J : Subgroup H, (J.map φ.symm.toMonoidHom).map φ.toMonoidHom = J := by
    intro J
    rw [Subgroup.map_map]
    have : φ.toMonoidHom.comp φ.symm.toMonoidHom = MonoidHom.id H := by
      ext x
      simp
    rw [this, Subgroup.map_id]
  have hmm' : ∀ J : Subgroup H, (J.map φ.toMonoidHom).map φ.symm.toMonoidHom = J := by
    intro J
    rw [Subgroup.map_map]
    have : φ.symm.toMonoidHom.comp φ.toMonoidHom = MonoidHom.id H := by
      ext x
      simp
    rw [this, Subgroup.map_id]
  have hex : ∀ J' ∈ 𝓛, ∃ i ∈ J', (K (J'.map φ.symm.toMonoidHom)).map φ.toMonoidHom =
      (K J').map (MulAut.conj i).toMonoidHom := by
    intro J' hJ'
    obtain ⟨i, hi, hconj'⟩ := hconj _ (hφ' J' hJ')
    rw [hmm] at hi hconj'
    exact ⟨i, hi, hconj'⟩
  choose! i hiJ hi using hex
  let z : (J' : 𝓛) → (J' : Subgroup H) := fun J' => ⟨(i J'.1)⁻¹, inv_mem (hiJ J'.1 J'.2)⟩
  let g : H := ((hL.equiv z : ↥(⊤ : Subgroup H)) : H)
  have hg : ∀ J' ∈ 𝓛, ∀ n ∈ J', g * n * g⁻¹ = (i J')⁻¹ * n * i J' := by
    intro J' hJ' n hn
    have h1 := conj_eq_coord_conj hL hJ' (Subgroup.mem_top g) hn
    have h2 : hL.coord hJ' ⟨g, Subgroup.mem_top g⟩ = z ⟨J', hJ'⟩ := hL.coord_equiv hJ' z
    rw [h2] at h1
    simpa [z] using h1
  have hKJ : ∀ J ∈ 𝓛, ((K J).map φ.toMonoidHom).map (MulAut.conj g).toMonoidHom =
      K (J.map φ.toMonoidHom) := by
    intro J hJ
    have hJ' := hφ J hJ
    have e1 := hi (J.map φ.toMonoidHom) hJ'
    rw [hmm'] at e1
    rw [e1]
    have key : ∀ k ∈ J.map φ.toMonoidHom,
        g * (i (J.map φ.toMonoidHom) * k * (i (J.map φ.toMonoidHom))⁻¹) * g⁻¹ = k := by
      intro k hk
      have hiJ' := hiJ _ hJ'
      have hik : i (J.map φ.toMonoidHom) * k * (i (J.map φ.toMonoidHom))⁻¹ ∈ J.map φ.toMonoidHom :=
        mul_mem (mul_mem hiJ' hk) (inv_mem hiJ')
      rw [hg _ hJ' _ hik]
      group
    ext x
    constructor
    · rintro ⟨_, ⟨k, hk, rfl⟩, rfl⟩
      have h2 := key k (hK _ hJ' hk)
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [h2]
      exact hk
    · intro hx
      refine ⟨_, ⟨x, hx, rfl⟩, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      exact key x (hK _ hJ' hx)
  refine ⟨g, ?_⟩
  set ψ : H →* H := (MulAut.conj g).toMonoidHom.comp φ.toMonoidHom with hψ
  rw [Subgroup.map_map, (Subgroup.gc_map_comap ψ).l_sSup]
  refine le_antisymm (iSup₂_le fun X hX => ?_) (sSup_le fun X hX => ?_)
  · obtain ⟨J, hJ, rfl⟩ := hX
    have : (K J).map ψ = K (J.map φ.toMonoidHom) := by
      rw [hψ, ← Subgroup.map_map]
      exact hKJ J hJ
    rw [this]
    exact le_sSup ⟨J.map φ.toMonoidHom, hφ J hJ, rfl⟩
  · obtain ⟨J', hJ', rfl⟩ := hX
    have hJ := hφ' J' hJ'
    have : K J' = (K (J'.map φ.symm.toMonoidHom)).map ψ := by
      have h1 := hKJ _ hJ
      rw [hmm] at h1
      rw [hψ, ← Subgroup.map_map, h1]
    rw [this]
    exact le_iSup₂_of_le (K (J'.map φ.symm.toMonoidHom)) ⟨_, hJ, rfl⟩ le_rfl

theorem Thm210.nearSimple_of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) {p : ℕ}
    (h : NearSimple p X) : NearSimple p Y where
  prime := h.prime
  simple := by
    have := h.simple
    exact e.symm.isSimpleGroup
  nonabelian := by
    obtain ⟨a, b, hab⟩ := h.nonabelian
    exact ⟨e a, e b, fun hc => hab (e.injective (by simpa using hc))⟩
  nearPSolvable := TransportA.nearPSolvable_of_mulEquiv e h.nearPSolvable

theorem Thm210.exists_conj_map_fixedNormalizer
    {p : ℕ} (φ : MulAut H) {J₀ J₁ : Subgroup H}
    (hJ : J₀.map φ.toMonoidHom = J₁) (hJ₁ : NearSimple p ↥J₁) {f : MulAut ↥J₀}
    (hf : orderOf f = p) {f' : MulAut ↥J₁} (hf' : orderOf f' = p) :
    ∃ i ∈ J₁, ((fixedNormalizer f).map J₀.subtype).map φ.toMonoidHom =
      ((fixedNormalizer f').map J₁.subtype).map (MulAut.conj i).toMonoidHom := by
  subst hJ
  let e : ↥J₀ ≃* ↥(J₀.map φ.toMonoidHom) :=
    Subgroup.equivMapOfInjective J₀ φ.toMonoidHom φ.injective
  have hbound : ∀ P : Subgroup (MulAut ↥(J₀.map φ.toMonoidHom)), IsPGroup p P → Nat.card P ∣ p :=
    fun P hP => near_aut_pSubgroup_card_dvd hJ₁ P hP
  have hfe : orderOf (MulAut.congr e f) = p := by rw [orderOf_congr, hf]
  obtain ⟨g, hg⟩ := exists_fixed_conj hJ₁.prime hbound hf' hfe
  have hM : fixedNormalizer f' = ((fixedNormalizer f).map e.toMonoidHom).map g.toMonoidHom := by
    rw [fixedNormalizer_eq_of_fixed_eq hg, fixedNormalizer_congr, fixedNormalizer_congr]
  obtain ⟨i, hi⟩ := near_conj_class hJ₁ hf' ((fixedNormalizer f).map e.toMonoidHom)
    ⟨(Subgroup.equivMapOfInjective _ g.toMonoidHom g.injective).trans
      (MulEquiv.subgroupCongr hM.symm)⟩
  refine ⟨(i : H), i.2, ?_⟩
  calc ((fixedNormalizer f).map J₀.subtype).map φ.toMonoidHom
      = ((fixedNormalizer f).map e.toMonoidHom).map (J₀.map φ.toMonoidHom).subtype := by
        rw [Subgroup.map_map, Subgroup.map_map]
        rfl
    _ = ((fixedNormalizer f').map (MulAut.conj i).toMonoidHom).map
          (J₀.map φ.toMonoidHom).subtype := by rw [← hi]
    _ = ((fixedNormalizer f').map (J₀.map φ.toMonoidHom).subtype).map
          (MulAut.conj (i : H)).toMonoidHom := by
        rw [Subgroup.map_map, Subgroup.map_map]
        congr 1

omit [Finite H] in
theorem Thm210.isDirectProduct_of_map {Γ' : Type*} [Group Γ'] {f : H →* Γ'}
    (hf : Function.Injective f) {S : Set (Subgroup H)} {K : Subgroup H}
    (h : IsDirectProduct ((Subgroup.map f) '' S) (K.map f)) : IsDirectProduct S K where
  commute := by
    intro J hJ L hL hne x hx y hy
    have hne' : J.map f ≠ L.map f := fun he => hne (Subgroup.map_injective hf he)
    have := h.commute (J.map f) ⟨J, hJ, rfl⟩ (L.map f) ⟨L, hL, rfl⟩ hne' (f x) ⟨x, hx, rfl⟩
      (f y) ⟨y, hy, rfl⟩
    exact hf (by simpa [map_mul] using this.eq)
  indep := by
    intro J hJ
    have hsub : (Subgroup.map f) '' (S \ {J}) ⊆ (Subgroup.map f) '' S \ {J.map f} := by
      rintro _ ⟨L, ⟨hL, hLJ⟩, rfl⟩
      exact ⟨⟨L, hL, rfl⟩, fun he => hLJ (Subgroup.map_injective hf he)⟩
    have h2 : sSup ((Subgroup.map f) '' (S \ {J})) = (sSup (S \ {J})).map f := by
      rw [sSup_image, (Subgroup.gc_map_comap f).l_sSup]
    have hd := h.indep ⟨J, hJ, rfl⟩
    rw [disjoint_iff, eq_bot_iff]
    intro x hx
    obtain ⟨hxJ, hxS⟩ := Subgroup.mem_inf.mp hx
    have h4 : f x ∈ sSup ((Subgroup.map f) '' (S \ {J})) := by
      rw [h2]
      exact ⟨x, hxS, rfl⟩
    have h3 : f x ∈ (J.map f) ⊓ sSup ((Subgroup.map f) '' S \ {J.map f}) :=
      Subgroup.mem_inf.mpr ⟨⟨x, hxJ, rfl⟩, sSup_le_sSup hsub h4⟩
    rw [disjoint_iff.mp hd, Subgroup.mem_bot] at h3
    exact Subgroup.mem_bot.mpr (hf (by rw [h3, map_one]))
  sSup_eq := by
    apply Subgroup.map_injective hf
    rw [← h.sSup_eq, sSup_image, (Subgroup.gc_map_comap f).l_sSup]

omit [Finite H] in
theorem Thm210.comap_sSup_of_le {Γ' : Type*} [Group Γ'] {f : H →* Γ'} (hf : Function.Injective f)
    {𝒮 : Set (Subgroup Γ')} (h𝒮 : ∀ K ∈ 𝒮, K ≤ f.range) :
    (sSup 𝒮).comap f = sSup ((Subgroup.comap f) '' 𝒮) := by
  apply Subgroup.map_injective hf
  have hS : sSup 𝒮 ≤ f.range := sSup_le h𝒮
  have h1 : ∀ K ∈ 𝒮, (K.comap f).map f = K := fun K hK => by
    rw [Subgroup.map_comap_eq]
    exact inf_eq_right.mpr (h𝒮 K hK)
  have e1 : ((sSup 𝒮).comap f).map f = sSup 𝒮 := by
    rw [Subgroup.map_comap_eq]
    exact inf_eq_right.mpr hS
  have e2 : (sSup ((Subgroup.comap f) '' 𝒮)).map f = sSup 𝒮 := by
    refine le_antisymm ?_ (sSup_le fun K hK => ?_)
    · rw [Subgroup.map_le_iff_le_comap]
      refine sSup_le fun L hL => ?_
      obtain ⟨K', hK', rfl⟩ := hL
      exact Subgroup.comap_mono (le_sSup hK')
    · calc K = (K.comap f).map f := (h1 K hK).symm
        _ ≤ (sSup ((Subgroup.comap f) '' 𝒮)).map f :=
          Subgroup.map_mono (le_sSup ⟨K, hK, rfl⟩)
  rw [e1, e2]

omit [Finite H] in
theorem Thm210.exists_frame_map {X : Type*} [Group X] {ι : H →* X} (hι : Function.Injective ι)
    {J₀ : Subgroup H} {p : ℕ} {f : MulAut ↥(J₀.map ι)} (hf : orderOf f = p) :
    ∃ f₀ : MulAut ↥J₀, orderOf f₀ = p ∧
      ((fixedNormalizer f₀).map J₀.subtype).map ι =
        (fixedNormalizer f).map (J₀.map ι).subtype := by
  let e₁ : ↥J₀ ≃* ↥(J₀.map ι) := Subgroup.equivMapOfInjective J₀ ι hι
  refine ⟨MulAut.congr e₁.symm f, by rw [orderOf_congr, hf], ?_⟩
  rw [fixedNormalizer_congr, Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext z
  have := congrArg Subtype.val (e₁.apply_symm_apply z)
  exact this

end Abstract


section Semisimple

variable {p : ℕ} {A G : Subgroup Γ} [Finite Γ]

@[expose] def kH (A G : Subgroup Γ) (J₀ : Subgroup ↥G) : Subgroup ↥G :=
  (kJ A (J₀.map G.subtype)).comap G.subtype

theorem SemisimpleAction.isDirectProduct_lcalOf (h : SemisimpleAction p A G) :
    IsDirectProduct (lcalOf ↥G) (⊤ : Subgroup ↥G) := by
  refine isDirectProduct_of_map G.subtype_injective ?_
  have : (⊤ : Subgroup ↥G).map G.subtype = G := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  rw [this, ← lcal_eq_image]
  exact h.isDirectProduct_lcal

theorem SemisimpleAction.exists_frame_lcalOf
    (h : SemisimpleAction p A G) {J₀ : Subgroup ↥G}
    (hJ₀ : J₀ ∈ lcalOf ↥G) :
    NearSimple p ↥J₀ ∧ ∃ f : MulAut ↥J₀, orderOf f = p ∧
      kH A G J₀ = (fixedNormalizer f).map J₀.subtype := by
  have hJ : J₀.map G.subtype ∈ lcal G := by
    rw [lcal_eq_image]
    exact ⟨J₀, hJ₀, rfl⟩
  let e₁ : ↥J₀ ≃* ↥(J₀.map G.subtype) :=
    Subgroup.equivMapOfInjective J₀ G.subtype G.subtype_injective
  refine ⟨nearSimple_of_mulEquiv e₁.symm (h.nearSimple hJ), ?_⟩
  obtain ⟨f, hf, -, -, hM, -⟩ := h.exists_frame_data hJ
  obtain ⟨f₀, hf₀, hmap⟩ := exists_frame_map G.subtype_injective hf
  refine ⟨f₀, hf₀, ?_⟩
  unfold kH
  rw [← hM, ← hmap, Subgroup.comap_map_eq_self_of_injective G.subtype_injective]

theorem SemisimpleAction.subgroupOf_mOf
    (h : SemisimpleAction p A G) :
    (mOf A G).subgroupOf G = sSup {X | ∃ J₀ ∈ lcalOf ↥G, X = kH A G J₀} := by
  have h1 : {X | ∃ J₀ ∈ lcalOf ↥G, X = kH A G J₀} =
      (Subgroup.comap G.subtype) '' {X | ∃ J ∈ lcal G, X = kJ A J} := by
    ext X
    constructor
    · rintro ⟨J₀, hJ₀, rfl⟩
      refine ⟨kJ A (J₀.map G.subtype), ⟨J₀.map G.subtype, ?_, rfl⟩, rfl⟩
      rw [lcal_eq_image]
      exact ⟨J₀, hJ₀, rfl⟩
    · rintro ⟨_, ⟨J, hJ, rfl⟩, rfl⟩
      rw [lcal_eq_image] at hJ
      obtain ⟨J₀, hJ₀, rfl⟩ := hJ
      exact ⟨J₀, hJ₀, rfl⟩
  rw [h1, ← comap_sSup_of_le G.subtype_injective, h.mOf_eq_kProd]
  · rfl
  · rintro _ ⟨J, hJ, rfl⟩
    rw [Subgroup.range_subtype]
    exact (kJ_le A J).trans (lcal_le hJ)

theorem SemisimpleAction.exists_conj_map_mOf
    (h : SemisimpleAction p A G) (φ : MulAut ↥G) :
    ∃ g : ↥G, ((mOf A G).subgroupOf G |>.map φ.toMonoidHom).map (MulAut.conj g).toMonoidHom =
      (mOf A G).subgroupOf G := by
  rw [h.subgroupOf_mOf]
  refine exists_conj_map_sSup_eq h.isDirectProduct_lcalOf (kH A G) ?_ φ ?_ ?_ ?_
  · intro J₀ _
    have := Subgroup.comap_mono (f := G.subtype) (kJ_le A (J₀.map G.subtype))
    rwa [Subgroup.comap_map_eq_self_of_injective G.subtype_injective] at this
  · intro J₀ hJ₀
    exact (map_mem_lcalOf_iff φ).mpr hJ₀
  · intro J₀ hJ₀
    exact (map_mem_lcalOf_iff φ.symm).mpr hJ₀
  · intro J₀ hJ₀
    have hJ₁ : J₀.map φ.toMonoidHom ∈ lcalOf ↥G := (map_mem_lcalOf_iff φ).mpr hJ₀
    obtain ⟨-, f₀, hf₀, hk₀⟩ := h.exists_frame_lcalOf hJ₀
    obtain ⟨hN₁, f₁, hf₁, hk₁⟩ := h.exists_frame_lcalOf hJ₁
    obtain ⟨i, hi, heq⟩ := exists_conj_map_fixedNormalizer φ rfl hN₁ hf₀ hf₁
    exact ⟨i, hi, by rw [hk₀, hk₁]; exact heq⟩

end Semisimple

end CFSG.SignalizerFunctorTheorem.McBride.Near
