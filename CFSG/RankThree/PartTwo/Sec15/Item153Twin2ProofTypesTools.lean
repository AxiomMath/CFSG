module

public import CFSG.RankThree.PartTwo.Sec4.Vocabulary
import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_6M11

public section

namespace CFSG.RankThree.PartTwo.Sec15.Proof153Twin2

section Basic

variable {Q : Type*} [Group Q]

theorem eq_bot_of_isPerfect_of_le_center {U : Subgroup Q} (hUp : Group.IsPerfect U)
    (hU : U ≤ Subgroup.center Q) : U = ⊥ := by
  have h := Subgroup.isPerfect_iff.mp hUp
  rw [← h, Subgroup.commutator_eq_bot_iff_le_centralizer]
  exact hU.trans (Subgroup.center_le_centralizer (U : Set Q))

theorem map_center_le_center {P : Type*} [Group P] {φ : P →* Q} (hφ : Function.Surjective φ) :
    (Subgroup.center P).map φ ≤ Subgroup.center Q := by
  rintro _ ⟨z, hz, rfl⟩
  rw [Subgroup.mem_center_iff]
  intro q
  obtain ⟨p, rfl⟩ := hφ q
  rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.mp hz) p]

theorem sup_ker_eq_top_of_map_eq_top {P S : Type*} [Group P] [Group S] {ψ : P →* S}
    {U : Subgroup P} (h : U.map ψ = ⊤) : U ⊔ ψ.ker = ⊤ := by
  rw [eq_top_iff]
  intro p _
  obtain ⟨u, hu, hup⟩ : ψ p ∈ U.map ψ := h ▸ Subgroup.mem_top _
  have hk : u⁻¹ * p ∈ ψ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hup, inv_mul_cancel]
  have : p = u * (u⁻¹ * p) := by group
  rw [this]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hu) (Subgroup.mem_sup_right hk)

end Basic

section Cover

variable {Q P S : Type*} [Group Q] [Group P] [Group S] [IsSimpleGroup S]

theorem sup_map_center_eq_top {ψ : P →* S} (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center P) {φ : P →* Q} (hφ : Function.Surjective φ)
    {U : Subgroup Q} (hU : U.IsSubnormal) (hUp : Group.IsPerfect U) (hU1 : U ≠ ⊥) :
    U ⊔ (Subgroup.center P).map φ = ⊤ := by
  have hsn : ((U.comap φ).map ψ).IsSubnormal := (hU.comap φ).map hψ
  rcases hsn.eq_bot_or_top_of_isSimpleGroup inferInstance with hbot | htop
  · exfalso
    apply hU1
    rw [Subgroup.map_eq_bot_iff] at hbot
    have hle : U ≤ Subgroup.center Q := by
      rw [← Subgroup.map_comap_eq_self_of_surjective hφ U]
      exact (Subgroup.map_mono (hbot.trans hker)).trans (map_center_le_center hφ)
    exact eq_bot_of_isPerfect_of_le_center hUp hle
  · have h1 := sup_ker_eq_top_of_map_eq_top htop
    have hle : (U.comap φ ⊔ ψ.ker).map φ ≤ U ⊔ (Subgroup.center P).map φ := by
      rw [Subgroup.map_sup]
      exact sup_le_sup (Subgroup.map_comap_le _ _) (Subgroup.map_mono hker)
    rw [h1, Subgroup.map_top_of_surjective φ hφ] at hle
    exact top_le_iff.mp hle

theorem eq_bot_or_eq_bot_of_commutator_eq_bot {ψ : P →* S} (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center P) {φ : P →* Q} (hφ : Function.Surjective φ)
    {U V : Subgroup Q} (hU : U.IsSubnormal) (hUp : Group.IsPerfect U) (hVp : Group.IsPerfect V)
    (hUV : ⁅U, V⁆ = ⊥) : U = ⊥ ∨ V = ⊥ := by
  by_cases hU1 : U = ⊥
  · exact Or.inl hU1
  right
  have htop := sup_map_center_eq_top hψ hker hφ hU hUp hU1
  have hle : U ⊔ (Subgroup.center P).map φ ≤ Subgroup.centralizer (V : Set Q) := by
    refine sup_le ?_ ((map_center_le_center hφ).trans (Subgroup.center_le_centralizer _))
    rw [← Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact hUV
  rw [htop] at hle
  refine eq_bot_of_isPerfect_of_le_center hVp fun v hv => ?_
  rw [Subgroup.mem_center_iff]
  intro q
  exact (Subgroup.mem_centralizer_iff.mp (hle (Subgroup.mem_top q)) v hv).symm

end Cover

section Product

variable {T : Type*} [Group T]

theorem inf_le_center_of_commutator_eq_bot {U₀ V₀ : Subgroup T} (hsup : U₀ ⊔ V₀ = ⊤)
    (hcomm : ⁅U₀, V₀⁆ = ⊥) : U₀ ⊓ V₀ ≤ Subgroup.center T := by
  intro x hx
  have hUV := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
  have hVU : V₀ ≤ Subgroup.centralizer (U₀ : Set T) := by
    rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
    exact hcomm
  have hle : U₀ ⊔ V₀ ≤ Subgroup.centralizer ({x} : Set T) := by
    refine sup_le (fun u hu => ?_) (fun v hv => ?_)
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_iff.mp (hVU hx.2) u hu)
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_iff.mp (hUV hx.1) v hv)
  rw [hsup] at hle
  rw [Subgroup.mem_center_iff]
  intro g
  exact (Subgroup.mem_centralizer_singleton_iff.mp (hle (Subgroup.mem_top g)))

theorem surjective_comp_of_sup_eq_top {U₀ V₀ : Subgroup T} [V₀.Normal] (hsup : U₀ ⊔ V₀ = ⊤)
    {P : Type*} [Group P] {φ : P →* U₀} (hφ : Function.Surjective φ) :
    Function.Surjective ((QuotientGroup.mk' V₀).comp (U₀.subtype.comp φ)) := by
  intro x
  obtain ⟨t, rfl⟩ := QuotientGroup.mk'_surjective V₀ x
  have ht : t ∈ ((U₀ ⊔ V₀ : Subgroup T) : Set T) := by
    rw [hsup]
    exact Subgroup.mem_top t
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ (by
    rw [Subgroup.normalizer_eq_top_iff.mpr inferInstance]
    exact le_top)] at ht
  obtain ⟨u, hu, v, hv, rfl⟩ := Set.mem_mul.mp ht
  obtain ⟨p, hp⟩ := hφ ⟨u, hu⟩
  refine ⟨p, ?_⟩
  simp only [MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype, hp,
    QuotientGroup.mk'_apply]
  rw [QuotientGroup.eq]
  have : u⁻¹ * (u * v) = v := by group
  rw [this]
  exact hv

theorem map_facts {Q : Type*} [Group Q] {f : T →* Q} (hf : Function.Surjective f)
    {U : Subgroup T} (hU : U.IsSubnormal) (hUp : Group.IsPerfect U) :
    (U.map f).IsSubnormal ∧ Group.IsPerfect (U.map f) :=
  ⟨hU.map hf, Group.IsPerfect.map f⟩

theorem le_or_le_of_commutator_eq_bot {U₀ V₀ : Subgroup T} [U₀.Normal] [V₀.Normal]
    (hsup : U₀ ⊔ V₀ = ⊤) (hcomm : ⁅U₀, V₀⁆ = ⊥)
    {P₁ S₁ : Type*} [Group P₁] [Group S₁] [IsSimpleGroup S₁] {ψ₁ : P₁ →* S₁}
    (hψ₁ : Function.Surjective ψ₁) (hk₁ : ψ₁.ker ≤ Subgroup.center P₁) {φ₁ : P₁ →* U₀}
    (hφ₁ : Function.Surjective φ₁)
    {P₂ S₂ : Type*} [Group P₂] [Group S₂] [IsSimpleGroup S₂] {ψ₂ : P₂ →* S₂}
    (hψ₂ : Function.Surjective ψ₂) (hk₂ : ψ₂.ker ≤ Subgroup.center P₂) {φ₂ : P₂ →* V₀}
    (hφ₂ : Function.Surjective φ₂)
    {U V : Subgroup T} (hU : U.IsSubnormal) (hUp : Group.IsPerfect U)
    (hVp : Group.IsPerfect V) (hU1 : U ≠ ⊥) (hV1 : V ≠ ⊥) (hUV : ⁅U, V⁆ = ⊥) :
    (U ≤ U₀ ∧ V ≤ V₀) ∨ (U ≤ V₀ ∧ V ≤ U₀) := by
  have h1 : U ≤ V₀ ∨ V ≤ V₀ := by
    have hs := surjective_comp_of_sup_eq_top hsup hφ₁
    obtain ⟨hUs, hUp'⟩ := map_facts (QuotientGroup.mk'_surjective V₀) hU hUp
    have hVp' : Group.IsPerfect (V.map (QuotientGroup.mk' V₀)) := Group.IsPerfect.map _
    have hc : ⁅U.map (QuotientGroup.mk' V₀), V.map (QuotientGroup.mk' V₀)⁆ = ⊥ := by
      rw [← Subgroup.map_commutator, hUV, Subgroup.map_bot]
    rcases eq_bot_or_eq_bot_of_commutator_eq_bot hψ₁ hk₁ hs hUs hUp' hVp' hc with h | h
    · left
      rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h
      exact h
    · right
      rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h
      exact h
  have h2 : U ≤ U₀ ∨ V ≤ U₀ := by
    have hsup' : V₀ ⊔ U₀ = ⊤ := by rw [sup_comm]; exact hsup
    have hs := surjective_comp_of_sup_eq_top hsup' hφ₂
    obtain ⟨hUs, hUp'⟩ := map_facts (QuotientGroup.mk'_surjective U₀) hU hUp
    have hVp' : Group.IsPerfect (V.map (QuotientGroup.mk' U₀)) := Group.IsPerfect.map _
    have hc : ⁅U.map (QuotientGroup.mk' U₀), V.map (QuotientGroup.mk' U₀)⁆ = ⊥ := by
      rw [← Subgroup.map_commutator, hUV, Subgroup.map_bot]
    rcases eq_bot_or_eq_bot_of_commutator_eq_bot hψ₂ hk₂ hs hUs hUp' hVp' hc with h | h
    · left
      rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h
      exact h
    · right
      rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h
      exact h
  have hZ := inf_le_center_of_commutator_eq_bot hsup hcomm
  rcases h1 with hUV₀ | hVV₀ <;> rcases h2 with hUU₀ | hVU₀
  · exact absurd (eq_bot_of_isPerfect_of_le_center hUp ((le_inf hUU₀ hUV₀).trans hZ)) hU1
  · exact Or.inr ⟨hUV₀, hVU₀⟩
  · exact Or.inl ⟨hUU₀, hVV₀⟩
  · exact absurd (eq_bot_of_isPerfect_of_le_center hVp ((le_inf hVU₀ hVV₀).trans hZ)) hV1

theorem sup_eq_of_le_factor {U₀ : Subgroup T} {P S : Type*} [Group P] [Group S]
    [IsSimpleGroup S] {ψ : P →* S} (hψ : Function.Surjective ψ)
    (hk : ψ.ker ≤ Subgroup.center P) {φ : P →* U₀} (hφ : Function.Surjective φ)
    {U : Subgroup T} (hU : U.IsSubnormal) (hUp : Group.IsPerfect U) (hU1 : U ≠ ⊥)
    (hUU₀ : U ≤ U₀) : U ⊔ ((Subgroup.center P).map φ).map U₀.subtype = U₀ := by
  have hUs : (U.subgroupOf U₀).IsSubnormal := hU.subgroupOf
  have : Group.IsPerfect ↥U := hUp
  have hUp' : Group.IsPerfect (U.subgroupOf U₀) :=
    Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hUU₀).symm.toMonoidHom)
      (MulEquiv.surjective _)
  have hU1' : U.subgroupOf U₀ ≠ ⊥ := by
    intro h0
    rw [Subgroup.subgroupOf_eq_bot] at h0
    exact hU1 (disjoint_self.mp (h0.mono_right hUU₀))
  have htop := sup_map_center_eq_top hψ hk hφ hUs hUp' hU1'
  have h := congrArg (Subgroup.map U₀.subtype) htop
  rw [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hUU₀,
    ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h
  exact h

end Product

section CoverType

variable {T : Type*} [Group T]

theorem exists_surjective_ker_eq_center {U U₀ : Subgroup T} (hUU₀ : U ≤ U₀)
    (hsup : U ⊔ (Subgroup.center ↥U₀).map U₀.subtype = U₀) {S : Type*} [Group S]
    (ε : ↥U₀ ⧸ Subgroup.center ↥U₀ ≃* S) :
    ∃ g : ↥U →* S, Function.Surjective g ∧ g.ker = Subgroup.center ↥U ∧
      Nat.card (Subgroup.center ↥U) ∣ Nat.card (Subgroup.center ↥U₀) := by
  set Z₀ := (Subgroup.center ↥U₀).map U₀.subtype with hZ₀
  set g : ↥U →* S := ε.toMonoidHom.comp
    ((QuotientGroup.mk' (Subgroup.center ↥U₀)).comp (Subgroup.inclusion hUU₀)) with hg
  have hZ₀c : ∀ z ∈ Z₀, ∀ x ∈ U₀, x * z = z * x := by
    rintro _ ⟨z, hz, rfl⟩ x hx
    exact congrArg Subtype.val ((Subgroup.mem_center_iff.mp hz) ⟨x, hx⟩)
  have hZU : ∀ z : ↥U, z ∈ Subgroup.center ↥U →
      (⟨z, hUU₀ z.2⟩ : ↥U₀) ∈ Subgroup.center ↥U₀ := by
    intro z hz
    have hle : U ⊔ Z₀ ≤ Subgroup.centralizer ({(z : T)} : Set T) := by
      refine sup_le (fun u hu => ?_) (fun w hw => ?_)
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact congrArg Subtype.val ((Subgroup.mem_center_iff.mp hz) ⟨u, hu⟩)
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact (hZ₀c w hw z (hUU₀ z.2)).symm
    rw [hsup] at hle
    rw [Subgroup.mem_center_iff]
    intro x
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hle x.2))
  have hUN : U ≤ Subgroup.normalizer (Z₀ : Set T) := by
    refine le_trans (fun u hu => ?_) (Subgroup.centralizer_le_normalizer _)
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact (hZ₀c z hz u (hUU₀ hu)).symm
  refine ⟨g, ?_, ?_, ?_⟩
  ·
    intro s
    obtain ⟨q, rfl⟩ := ε.surjective s
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective _ q
    have hx : (x : T) ∈ ((U ⊔ Z₀ : Subgroup T) : Set T) := by
      rw [hsup]
      exact x.2
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hUN] at hx
    obtain ⟨u, hu, w, hw, hxuw⟩ := Set.mem_mul.mp hx
    refine ⟨⟨u, hu⟩, ?_⟩
    simp only [hg, MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom]
    congr 1
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    obtain ⟨w', hw', rfl⟩ := hw
    have : (Subgroup.inclusion hUU₀ ⟨u, hu⟩)⁻¹ * x = w' := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inclusion]
      rw [← hxuw]
      simp
    rw [this]
    exact hw'
  ·
    ext z
    rw [MonoidHom.mem_ker]
    simp only [hg, MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
      map_eq_one_iff _ ε.injective, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    constructor
    · intro hz
      rw [Subgroup.mem_center_iff]
      intro y
      have := (Subgroup.mem_center_iff.mp hz) (Subgroup.inclusion hUU₀ y)
      exact Subgroup.inclusion_injective hUU₀ (by rw [map_mul, map_mul]; exact this)
    · intro hz
      exact hZU z hz
  ·
    have hle : (Subgroup.center ↥U).map (Subgroup.inclusion hUU₀) ≤ Subgroup.center ↥U₀ := by
      rintro _ ⟨z, hz, rfl⟩
      exact hZU z hz
    have h := Subgroup.card_dvd_of_le hle
    rwa [Subgroup.card_map_of_injective (Subgroup.inclusion_injective hUU₀)] at h

end CoverType

section Pairs

variable {T : Type*} [Group T]

theorem false_of_cover {P S : Type*} [Group P] [Group S] [IsSimpleGroup S] {ψ : P →* S}
    (hψ : Function.Surjective ψ) (hk : ψ.ker ≤ Subgroup.center P) {φ : P →* T}
    (hφ : Function.Surjective φ) {U V : Subgroup T} (hU : U.IsSubnormal)
    (hUp : Group.IsPerfect U) (hVp : Group.IsPerfect V) (hU1 : U ≠ ⊥) (hV1 : V ≠ ⊥)
    (hUV : ⁅U, V⁆ = ⊥) : False :=
  (eq_bot_or_eq_bot_of_commutator_eq_bot hψ hk hφ hU hUp hVp hUV).elim hU1 hV1

theorem false_of_mulEquiv_simple {X : Type*} [Group X] [IsSimpleGroup X] (e : T ≃* X)
    {U V : Subgroup T} (hU : U.IsSubnormal) (hUp : Group.IsPerfect U) (hVp : Group.IsPerfect V)
    (hU1 : U ≠ ⊥) (hV1 : V ≠ ⊥) (hUV : ⁅U, V⁆ = ⊥) : False :=
  false_of_cover (ψ := MonoidHom.id X) Function.surjective_id
    (by rw [MonoidHom.ker_id]; exact bot_le) (φ := e.symm.toMonoidHom) e.symm.surjective hU hUp
    hVp hU1 hV1 hUV

theorem false_of_mulEquiv_quasisimple {X : Type*} [Group X] (hX : CFSG.IsQuasisimple X)
    (e : T ≃* X) {U V : Subgroup T} (hU : U.IsSubnormal) (hUp : Group.IsPerfect U)
    (hVp : Group.IsPerfect V) (hU1 : U ≠ ⊥) (hV1 : V ≠ ⊥) (hUV : ⁅U, V⁆ = ⊥) : False := by
  obtain ⟨-, hs, -⟩ := hX
  exact false_of_cover (ψ := QuotientGroup.mk' (Subgroup.center X))
    (QuotientGroup.mk'_surjective _) (by rw [QuotientGroup.ker_mk']) (φ := e.symm.toMonoidHom)
    e.symm.surjective hU hUp hVp hU1 hV1 hUV

theorem tripleCover_cover {P S : Type*} [Group P] [Group S] (ε : P ⧸ Subgroup.center P ≃* S) :
    Function.Surjective (ε.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center P))) ∧
      (ε.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center P))).ker ≤ Subgroup.center P := by
  refine ⟨ε.surjective.comp (QuotientGroup.mk'_surjective _), fun x hx => ?_⟩
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    map_eq_one_iff _ ε.injective, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hx
  exact hx

theorem false_of_isTripleCover {S : Type*} [Group S] [IsSimpleGroup S]
    (h : CFSG.RankThree.PartTwo.Sec4.IsTripleCover T S) {U V : Subgroup T}
    (hU : U.IsSubnormal) (hUp : Group.IsPerfect U) (hVp : Group.IsPerfect V) (hU1 : U ≠ ⊥)
    (hV1 : V ≠ ⊥) (hUV : ⁅U, V⁆ = ⊥) : False := by
  obtain ⟨-, ⟨ε⟩⟩ := h
  obtain ⟨hψ, hk⟩ := tripleCover_cover ε
  exact false_of_cover hψ hk (φ := MonoidHom.id T) Function.surjective_id hU hUp hVp hU1 hV1 hUV

theorem exists_surjective_of_le_tripleCover {S : Type*} [Group S] [IsSimpleGroup S]
    {U₀ : Subgroup T} (h : CFSG.RankThree.PartTwo.Sec4.IsTripleCover ↥U₀ S) {U : Subgroup T}
    (hU : U.IsSubnormal) (hUp : Group.IsPerfect U) (hU1 : U ≠ ⊥) (hUU₀ : U ≤ U₀) :
    ∃ g : ↥U →* S, Function.Surjective g ∧ g.ker = Subgroup.center ↥U ∧
      Nat.card (Subgroup.center ↥U) ∣ 3 := by
  obtain ⟨h3, ⟨ε⟩⟩ := h
  obtain ⟨hψ, hk⟩ := tripleCover_cover ε
  have hsup := sup_eq_of_le_factor hψ hk (φ := MonoidHom.id ↥U₀) Function.surjective_id hU hUp
    hU1 hUU₀
  rw [Subgroup.map_id] at hsup
  obtain ⟨g, hg, hker, hdvd⟩ := exists_surjective_ker_eq_center hUU₀ hsup ε
  exact ⟨g, hg, hker, h3 ▸ hdvd⟩

theorem eq_of_le_simple_factor {X : Type*} [Group X] [IsSimpleGroup X]
    (hZ : Subgroup.center X = ⊥) {U₀ : Subgroup T} (e : ↥U₀ ≃* X) {U : Subgroup T}
    (hU : U.IsSubnormal) (hUp : Group.IsPerfect U) (hU1 : U ≠ ⊥) (hUU₀ : U ≤ U₀) : U = U₀ := by
  have hsup := sup_eq_of_le_factor (ψ := MonoidHom.id X) Function.surjective_id
    (by rw [MonoidHom.ker_id]; exact bot_le) (φ := e.symm.toMonoidHom) e.symm.surjective hU hUp
    hU1 hUU₀
  rwa [hZ, Subgroup.map_bot, Subgroup.map_bot, sup_bot_eq] at hsup

theorem pair_prod {H₁ H₂ : Type*} [Group H₁] [Group H₂] [IsSimpleGroup H₁] [IsSimpleGroup H₂]
    (hZ₁ : Subgroup.center H₁ = ⊥) (hZ₂ : Subgroup.center H₂ = ⊥)
    {U V : Subgroup (H₁ × H₂)} (hU : U.IsSubnormal) (hV : V.IsSubnormal)
    (hUp : Group.IsPerfect U) (hVp : Group.IsPerfect V) (hU1 : U ≠ ⊥) (hV1 : V ≠ ⊥)
    (hUV : ⁅U, V⁆ = ⊥) :
    (Nonempty (↥U ≃* H₁) ∧ Nonempty (↥V ≃* H₂)) ∨
      (Nonempty (↥U ≃* H₂) ∧ Nonempty (↥V ≃* H₁)) := by
  set U₀ := (MonoidHom.snd H₁ H₂).ker with hU₀
  set V₀ := (MonoidHom.fst H₁ H₂).ker with hV₀
  have hsup : U₀ ⊔ V₀ = ⊤ := by
    rw [eq_top_iff]
    rintro ⟨a, b⟩ -
    have : ((a, b) : H₁ × H₂) = (a, 1) * (1, b) := by simp
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (by rw [hU₀, MonoidHom.mem_ker]; rfl))
      (Subgroup.mem_sup_right (by rw [hV₀, MonoidHom.mem_ker]; rfl))
  have hcomm : ⁅U₀, V₀⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    rintro ⟨a, b⟩ hab
    rw [Subgroup.mem_centralizer_iff]
    rintro ⟨a', b'⟩ hab'
    simp only [hU₀, hV₀, MonoidHom.mem_ker, MonoidHom.coe_snd] at hab hab'
    subst hab hab'
    simp
  set φ₁ : H₁ →* U₀ := (MonoidHom.inl H₁ H₂).codRestrict U₀
    (fun a => by rw [hU₀, MonoidHom.mem_ker]; rfl)
  set φ₂ : H₂ →* V₀ := (MonoidHom.inr H₁ H₂).codRestrict V₀
    (fun b => by rw [hV₀, MonoidHom.mem_ker]; rfl)
  have hφ₁ : Function.Surjective φ₁ := by
    rintro ⟨⟨a, b⟩, hab⟩
    simp only [hU₀, MonoidHom.mem_ker, MonoidHom.coe_snd] at hab
    subst hab
    exact ⟨a, rfl⟩
  have hφ₂ : Function.Surjective φ₂ := by
    rintro ⟨⟨a, b⟩, hab⟩
    simp only [hV₀, MonoidHom.mem_ker, MonoidHom.coe_fst] at hab
    subst hab
    exact ⟨b, rfl⟩
  have hφ₁i : Function.Injective φ₁ := fun a a' h => by
    have := congrArg (fun x : U₀ => (x : H₁ × H₂).1) h
    simpa [φ₁] using this
  have hφ₂i : Function.Injective φ₂ := fun b b' h => by
    have := congrArg (fun x : V₀ => (x : H₁ × H₂).2) h
    simpa [φ₂] using this
  set e₁ : ↥U₀ ≃* H₁ := (MulEquiv.ofBijective φ₁ ⟨hφ₁i, hφ₁⟩).symm
  set e₂ : ↥V₀ ≃* H₂ := (MulEquiv.ofBijective φ₂ ⟨hφ₂i, hφ₂⟩).symm
  have hid₁ : (MonoidHom.id H₁).ker ≤ Subgroup.center H₁ := by
    rw [MonoidHom.ker_id]; exact bot_le
  have hid₂ : (MonoidHom.id H₂).ker ≤ Subgroup.center H₂ := by
    rw [MonoidHom.ker_id]; exact bot_le
  rcases le_or_le_of_commutator_eq_bot hsup hcomm Function.surjective_id hid₁ hφ₁
      Function.surjective_id hid₂ hφ₂ hU hUp hVp hU1 hV1 hUV with ⟨hUU, hVV⟩ | ⟨hUV', hVU⟩
  · left
    have hU' := eq_of_le_simple_factor hZ₁ e₁ hU hUp hU1 hUU
    have hV' := eq_of_le_simple_factor hZ₂ e₂ hV hVp hV1 hVV
    exact ⟨⟨(MulEquiv.subgroupCongr hU').trans e₁⟩, ⟨(MulEquiv.subgroupCongr hV').trans e₂⟩⟩
  · right
    have hU' := eq_of_le_simple_factor hZ₂ e₂ hU hUp hU1 hUV'
    have hV' := eq_of_le_simple_factor hZ₁ e₁ hV hVp hV1 hVU
    exact ⟨⟨(MulEquiv.subgroupCongr hU').trans e₂⟩, ⟨(MulEquiv.subgroupCongr hV').trans e₁⟩⟩

end Pairs

theorem exists_e9_alternatingGroup_six :
    ∃ E : Subgroup (alternatingGroup (Fin 6)), CFSG.Assembly.IsElemAbelian 3 E ∧
      Nat.card E = 9 := by
  obtain ⟨E, hcomm, hpow, hcard, -⟩ :=
    CFSG.QuasithinUnique.Unc25G2.exists_elemAbelian_nine_of_commuting
      (a := (⟨List.formPerm [0, 1, 2], Equiv.Perm.mem_alternatingGroup.mpr (by decide)⟩ :
        alternatingGroup (Fin 6)))
      (b := (⟨List.formPerm [3, 4, 5], Equiv.Perm.mem_alternatingGroup.mpr (by decide)⟩ :
        alternatingGroup (Fin 6)))
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
  exact ⟨E, ⟨⟨⟨fun x y => Subtype.ext (hcomm _ x.2 _ y.2)⟩⟩, hpow⟩, hcard⟩

end CFSG.RankThree.PartTwo.Sec15.Proof153Twin2
