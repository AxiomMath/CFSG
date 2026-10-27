module

public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.A3Structure312Quotient
public import CFSG.LieType.SteinbergBRMulEquivCores

public section

namespace CFSG.Quasithin.H13.LocDbl

open CFSG.Open CFSG.Quasithin

section Map

variable {G G' : Type*} [Group G] [Group G'] [Finite G] [Finite G']

omit [Finite G] [Finite G'] in
theorem isSolvable_ker_inf (f : G →* G') (hf : Group.IsSolvable f.ker) (X : Subgroup G) :
    Group.IsSolvable ↥(f.ker ⊓ X) := by
  have := hf
  exact Group.isSolvable_of_isSolvable_injective
    (f := Subgroup.inclusion (inf_le_left : f.ker ⊓ X ≤ f.ker)) (Subgroup.inclusion_injective _)

theorem map_mem_cComp_of_ker (f : G →* G') (hf : Group.IsSolvable f.ker) {X L : Subgroup G}
    (hL : L ∈ cComp X) : L.map f ∈ cComp (X.map f) :=
  A312.map_mem_cComp f (isSolvable_ker_inf f hf X) hL

omit [Finite G] [Finite G'] in
theorem comap_map_inf_eq (f : G →* G') {X L : Subgroup G} (hLX : L ≤ X) :
    (L.map f).comap f ⊓ X = L ⊔ (f.ker ⊓ X) := by
  rw [Subgroup.comap_map_eq]
  have hn : L ≤ Subgroup.normalizer (f.ker : Set G) := by
    rw [Subgroup.normalizer_eq_top_iff.mpr inferInstance]
    exact le_top
  have h := A3.eq_sup_inf_of_le_sup hn (le_inf le_sup_left hLX)
    (inf_le_left : (L ⊔ f.ker) ⊓ X ≤ L ⊔ f.ker)
  rw [h, inf_right_comm, inf_eq_right.mpr (le_sup_right : f.ker ≤ L ⊔ f.ker), inf_comm]

omit [Finite G'] in
theorem perfectCore_sup_ker_inf (f : G →* G') (hf : Group.IsSolvable f.ker) {X L : Subgroup G}
    (hL : L ∈ cComp X) : perfectCore (L ⊔ (f.ker ⊓ X)) = L := by
  have hLX : L ≤ X := le_of_mem_cComp hL
  have hn : L ≤ Subgroup.normalizer ((f.ker ⊓ X : Subgroup G) : Set G) := fun l hl =>
    Subgroup.inf_normalizer_le_normalizer_inf
      ⟨by rw [Subgroup.normalizer_eq_top_iff.mpr inferInstance]; trivial,
        Subgroup.le_normalizer (hLX hl)⟩
  exact (cComp_commutator_perfectCore hL inf_le_right (isSolvable_ker_inf f hf X) hn).2

omit [Finite G'] in
theorem map_injOn_cComp (f : G →* G') (hf : Group.IsSolvable f.ker) (X : Subgroup G) :
    Set.InjOn (Subgroup.map f) (cComp X) := by
  intro L₁ h₁ L₂ h₂ h
  have e1 : L₁ ⊔ (f.ker ⊓ X) = L₂ ⊔ (f.ker ⊓ X) := by
    rw [← comap_map_inf_eq f (le_of_mem_cComp h₁), ← comap_map_inf_eq f (le_of_mem_cComp h₂)]
    have h' : L₁.map f = L₂.map f := h
    rw [h']
  rw [← perfectCore_sup_ker_inf f hf h₁, ← perfectCore_sup_ker_inf f hf h₂, e1]

theorem map_surjOn_cComp (f : G →* G') (hf : Group.IsSolvable f.ker) (X : Subgroup G) :
    Set.SurjOn (Subgroup.map f) (cComp X) (cComp (X.map f)) := by
  intro K' hK'
  set J : Subgroup G := K'.comap f ⊓ X with hJ
  have hK'le : K' ≤ X.map f := le_of_mem_cComp hK'
  have hJmap : J.map f = K' := by
    refine le_antisymm ((Subgroup.map_mono inf_le_left).trans (Subgroup.map_comap_le f K')) ?_
    intro k' hk'
    obtain ⟨x, hxX, hx⟩ := hK'le hk'
    exact ⟨x, ⟨show f x ∈ K' from hx ▸ hk', hxX⟩, hx⟩
  have hJsub : IsSubnormal J X :=
    A3.subnormal_inf_right (A3.subnormal_comap f (subnormal_of_mem_cComp hK'))
      (Subgroup.le_comap_map f X)
  have hcore_map : (perfectCore J).map f = K' := by
    rw [map_perfectCore, hJmap, perfectCore_eq_self_of_perfect (perfect_of_mem_cComp hK')]
  have hcore_ne : perfectCore J ≠ ⊥ := by
    intro h
    apply ne_bot_of_mem_cComp hK'
    rw [← hcore_map, h, Subgroup.map_bot]
  obtain ⟨L, hLmin⟩ := (Set.toFinite {M : Subgroup G | M ≤ perfectCore J ∧ M ≠ ⊥ ∧
      ⁅M, M⁆ = M ∧ IsSubnormal M X}).exists_minimal
    ⟨perfectCore J, le_rfl, hcore_ne, perfectCore_perfect J, A3.subnormal_perfectCore hJsub⟩
  obtain ⟨hLle, hLne, hLperf, hLsub⟩ := hLmin.prop
  have hL : L ∈ cComp X := by
    refine ⟨hLne, hLperf, hLsub, fun M hML hMne hMperf hMsub => ?_⟩
    exact hML.ne (hLmin.eq_of_le ⟨hML.le.trans hLle, hMne, hMperf, hMsub⟩ hML.le)
  refine ⟨L, hL, ?_⟩
  have hLf : L.map f ∈ cComp (X.map f) := map_mem_cComp_of_ker f hf hL
  have hle : L.map f ≤ K' := by
    rw [← hcore_map]
    exact Subgroup.map_mono hLle
  by_contra hne
  exact not_subnormal_of_mem_cComp hK' (lt_of_le_of_ne hle hne) (ne_bot_of_mem_cComp hLf)
    (perfect_of_mem_cComp hLf) (subnormal_of_mem_cComp hLf)

theorem cComp_map_bijOn_of_ker (f : G →* G') (hf : Group.IsSolvable f.ker) (X : Subgroup G) :
    Set.BijOn (Subgroup.map f) (cComp X) (cComp (X.map f)) :=
  ⟨fun _ hL => map_mem_cComp_of_ker f hf hL, map_injOn_cComp f hf X, map_surjOn_cComp f hf X⟩

omit [Finite G'] in
theorem isSolvable_ker_of_injective (f : G →* G') (hf : Function.Injective f) :
    Group.IsSolvable f.ker := by
  rw [(MonoidHom.ker_eq_bot_iff f).mpr hf]
  infer_instance

end Map

section Conj

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem map_conj_eq_iff {t : G} {K : Subgroup G} :
    K.map (MulAut.conj t).toMonoidHom = K ↔ t ∈ Subgroup.normalizer (K : Set G) :=
  Subgroup.mem_normalizer_iff_map_conj_eq.symm

omit [Finite G] in
theorem map_conj_mem_cComp {X L : Subgroup G} (hL : L ∈ cComp X) {g : G}
    (hg : g ∈ Subgroup.normalizer (X : Set G)) :
    L.map (MulAut.conj g).toMonoidHom ∈ cComp X := by
  have h := cComp_map_mulEquiv (MulAut.conj g) hL
  rwa [map_conj_eq_iff.mpr hg] at h

theorem le_normalizer_of_mem_cComp {X L M : Subgroup G} (hL : L ∈ cComp X)
    (hM : M ∈ cComp X) : M ≤ Subgroup.normalizer (L : Set G) := by
  obtain ⟨hLS, hn⟩ := cComp_normal_span_of_le hL
  exact (le_cCompSpan hM).trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hLS).mp hn)

omit [Finite G] in
theorem eq_of_mem_cComp_of_le {X L M : Subgroup G} (hL : L ∈ cComp X) (hM : M ∈ cComp X)
    (hLM : L ≤ M) : L = M := by
  by_contra hne
  exact not_subnormal_of_mem_cComp hM (lt_of_le_of_ne hLM hne) (ne_bot_of_mem_cComp hL)
    (perfect_of_mem_cComp hL) (subnormal_of_mem_cComp hL)

end Conj

section RadQuot

theorem solvRad_subgroupOf {G : Type*} [Group G] [Finite G] (L : Subgroup G) :
    (solvRad L).subgroupOf L = CFSG.solvableRadical ↥L := by
  rw [solvRad_eq_map_solvableRadical, Subgroup.subgroupOf,
    Subgroup.comap_map_eq_self_of_injective L.subtype_injective]

theorem radQuot_simple {G : Type*} [Group G] [Finite G] {X L : Subgroup G} (hL : L ∈ cComp X) :
    IsSimpleGroup (↥L ⧸ CFSG.solvableRadical ↥L) ∧
      ∃ a b : ↥L ⧸ CFSG.solvableRadical ↥L, a * b ≠ b * a := by
  obtain ⟨-, ⟨hsimple, hnonab⟩, -⟩ := cComp_structure hL
  let e : ↥L ⧸ (solvRad L).subgroupOf L ≃* ↥L ⧸ CFSG.solvableRadical ↥L :=
    QuotientGroup.quotientMulEquivOfEq (solvRad_subgroupOf L)
  have := hsimple
  refine ⟨e.symm.isSimpleGroup, ?_⟩
  obtain ⟨a, b, hab⟩ := hnonab
  refine ⟨e a, e b, fun h => hab (e.injective ?_)⟩
  rw [map_mul, map_mul]
  exact h

end RadQuot

section Divisor

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem card_radQuot_dvd (U : Subgroup G) :
    Nat.card (↥U ⧸ CFSG.solvableRadical ↥U) ∣ Nat.card U := by
  rw [← Subgroup.index_eq_card]
  exact Subgroup.index_dvd_card _

theorem card_radQuot_eq_relIndex (V : Subgroup G) :
    Nat.card (↥V ⧸ CFSG.solvableRadical ↥V) = (solvRad V).relIndex V := by
  rw [← Subgroup.index_eq_card, Subgroup.relIndex, solvRad_eq_map_solvableRadical,
    Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective V.subtype_injective]

omit [Finite G] in
theorem card_sup_eq_mul_relIndex {U V : Subgroup G} (hVU : V ≤ Subgroup.normalizer (U : Set G)) :
    Nat.card ↥(U ⊔ V) = Nat.card U * U.relIndex V := by
  set W := U ⊔ V with hW
  have hUW : U ≤ W := le_sup_left
  have hVW : V ≤ W := le_sup_right
  have hWn : W ≤ Subgroup.normalizer (U : Set G) := sup_le Subgroup.le_normalizer hVU
  have hUn : (U.subgroupOf W).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hUW).mpr hWn
  let ψ : ↥V →* ↥W ⧸ U.subgroupOf W :=
    (QuotientGroup.mk' (U.subgroupOf W)).comp (Subgroup.inclusion hVW)
  have hψ : Function.Surjective ψ := by
    intro y
    obtain ⟨⟨x, hx⟩, rfl⟩ := QuotientGroup.mk'_surjective (U.subgroupOf W) y
    have hx' : x ∈ (↑(U ⊔ V) : Set G) := hx
    rw [Subgroup.coe_mul_of_right_le_normalizer_left U V hVU] at hx'
    obtain ⟨u, hu, v, hv, rfl⟩ := hx'
    refine ⟨⟨v, hv⟩, ?_⟩
    simp only [ψ, MonoidHom.comp_apply, QuotientGroup.mk'_apply]
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have hv' : v ∈ Subgroup.normalizer (U : Set G) := hVU hv
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hv') u).mp hu
    simpa [mul_assoc] using this
  have hker : ψ.ker = U.subgroupOf V := by
    ext x
    simp only [ψ, MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    rfl
  have h1 : Nat.card (U.subgroupOf W) * (U.subgroupOf W).index = Nat.card W :=
    Subgroup.card_mul_index _
  have h2 : Nat.card (U.subgroupOf W) = Nat.card U :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUW).toEquiv
  have h3 : (U.subgroupOf W).index = U.relIndex V := by
    rw [Subgroup.relIndex, Subgroup.index_eq_card, ← hker, Subgroup.index_ker,
      MonoidHom.range_eq_top.mpr hψ, Subgroup.card_top]
  rw [← h1, h2, h3]

theorem card_dvd_card_sup_of_mem_cComp {X U V : Subgroup G} (hU : U ∈ cComp X)
    (hV : V ∈ cComp X) (hUV : U ≠ V) :
    Nat.card U * Nat.card (↥V ⧸ CFSG.solvableRadical ↥V) ∣ Nat.card ↥(U ⊔ V) := by
  have hVU : V ≤ Subgroup.normalizer (U : Set G) := le_normalizer_of_mem_cComp hU hV
  have hIsub : IsSubnormal (U ⊓ V) V := by
    refine A3.subnormal_of_normal inf_le_right ?_
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right]
    intro v hv
    exact Subgroup.inf_normalizer_le_normalizer_inf ⟨hVU hv, Subgroup.le_normalizer hv⟩
  have hIlt : U ⊓ V < V := by
    refine lt_of_le_of_ne inf_le_right fun h => hUV ?_
    exact (eq_of_mem_cComp_of_le hV hU (h ▸ inf_le_left)).symm
  have hIrad : U ⊓ V ≤ solvRad V := le_solvRad_of_subnormal_lt hV hIsub hIlt
  have hrel : (solvRad V).relIndex V ∣ U.relIndex V := by
    rw [← Subgroup.inf_relIndex_right U V,
      ← Subgroup.relIndex_mul_relIndex (U ⊓ V) (solvRad V) V hIrad (solvRad_le V)]
    exact dvd_mul_left _ _
  calc Nat.card U * Nat.card (↥V ⧸ CFSG.solvableRadical ↥V)
      ∣ Nat.card U * U.relIndex V := by
        rw [card_radQuot_eq_relIndex]
        exact mul_dvd_mul_left _ hrel
    _ = Nat.card ↥(U ⊔ V) := (card_sup_eq_mul_relIndex hVU).symm

theorem card_dvd_of_mem_cComp {X U V Y : Subgroup G} (hU : U ∈ cComp X) (hV : V ∈ cComp X)
    (hUV : U ≠ V) (hY : U ⊔ V ≤ Y) :
    Nat.card U * Nat.card (↥V ⧸ CFSG.solvableRadical ↥V) ∣ Nat.card Y :=
  (card_dvd_card_sup_of_mem_cComp hU hV hUV).trans (Subgroup.card_dvd_of_le hY)

theorem card_radQuot_congr {U V : Type*} [Group U] [Group V] (e : U ≃* V) :
    Nat.card (U ⧸ CFSG.solvableRadical U) = Nat.card (V ⧸ CFSG.solvableRadical V) :=
  Nat.card_congr (QuotientGroup.congr _ _ e
    (CFSG.LieType.SteinbergBR.solvableRadical_map_equiv e)).toEquiv

theorem distinct_Ccomponents_simple_quotient_product_divisor {F : Type*} [Group F] [Finite F]
    {U V : Subgroup F} (hU : U ∈ cComp (⊤ : Subgroup F)) (hV : V ∈ cComp (⊤ : Subgroup F))
    (hUV : U ≠ V) :
    Nat.card (↥U ⧸ CFSG.solvableRadical ↥U) * Nat.card (↥V ⧸ CFSG.solvableRadical ↥V) ∣
        Nat.card F ∧
      ∀ m : ℕ, Nat.card (↥U ⧸ CFSG.solvableRadical ↥U) = m →
        Nat.card (↥V ⧸ CFSG.solvableRadical ↥V) = m → m ^ 2 ∣ Nat.card F := by
  have h : Nat.card (↥U ⧸ CFSG.solvableRadical ↥U) * Nat.card (↥V ⧸ CFSG.solvableRadical ↥V) ∣
      Nat.card F := by
    have := card_dvd_of_mem_cComp hU hV hUV (le_top : U ⊔ V ≤ ⊤)
    rw [Subgroup.card_top] at this
    exact (mul_dvd_mul_right (card_radQuot_dvd U) _).trans this
  refine ⟨h, fun m hm1 hm2 => ?_⟩
  rw [hm1, hm2, ← sq] at h
  exact h

theorem Ccomponent_full_radical_product_divisor {H K B : Subgroup G} (hB : B ∈ cComp H)
    (hBK : B ≤ K) :
    (∀ s ∈ H ⊓ Subgroup.normalizer (K : Set G), CFSG.conjugate B s ≠ B →
      Nat.card B * Nat.card (↥B ⧸ CFSG.solvableRadical ↥B) ∣ Nat.card K) ∧
    (¬ Nat.card B * Nat.card (↥B ⧸ CFSG.solvableRadical ↥B) ∣ Nat.card K →
      H ⊓ Subgroup.normalizer (K : Set G) ≤ H ⊓ Subgroup.normalizer (B : Set G)) := by
  have key : ∀ s ∈ H ⊓ Subgroup.normalizer (K : Set G), CFSG.conjugate B s ≠ B →
      Nat.card B * Nat.card (↥B ⧸ CFSG.solvableRadical ↥B) ∣ Nat.card K := by
    intro s hs hne
    set C := CFSG.conjugate B s with hC
    have hsH : s⁻¹ ∈ Subgroup.normalizer (H : Set G) :=
      Subgroup.le_normalizer (H.inv_mem hs.1)
    have hCH : C ∈ cComp H := map_conj_mem_cComp hB hsH
    have hCK : C ≤ K := by
      have hsK : s⁻¹ ∈ Subgroup.normalizer (K : Set G) := Subgroup.inv_mem _ hs.2
      rw [hC, CFSG.conjugate, ← map_conj_eq_iff.mpr hsK]
      exact Subgroup.map_mono hBK
    let e : ↥B ≃* ↥C := B.equivMapOfInjective _ (MulAut.conj s⁻¹).injective
    have hcardB : Nat.card (↥C ⧸ CFSG.solvableRadical ↥C) =
        Nat.card (↥B ⧸ CFSG.solvableRadical ↥B) := (card_radQuot_congr e).symm
    have h := card_dvd_of_mem_cComp hB hCH (Ne.symm hne) (sup_le hBK hCK)
    rwa [hcardB] at h
  refine ⟨key, fun hnd s hs => ⟨hs.1, ?_⟩⟩
  by_contra hsB
  refine hnd (key s hs ?_)
  intro h
  apply hsB
  have : s⁻¹ ∈ Subgroup.normalizer (B : Set G) := map_conj_eq_iff.mp h
  simpa using Subgroup.inv_mem _ this

end Divisor

end CFSG.Quasithin.H13.LocDbl
