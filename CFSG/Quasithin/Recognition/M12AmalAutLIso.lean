module

public import CFSG.Quasithin.Recognition.M12AmalAutIso
public import CFSG.Quasithin.EmptyFaithful.S1422LocAutDefs
public import CFSG.Quasithin.EmptyFaithful.S1422Extra

public section

namespace CFSG.Quasithin.AmalTransport

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7

section Ops

variable {A B : Type*} [Group A] [Group B]

theorem centerOf_map {f : A →* B} (hf : Function.Injective f) (X : Subgroup A) :
    (centerOf X).map f = centerOf (X.map f) := by
  ext y
  simp only [centerOf, Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_centralizer_iff,
    SetLike.mem_coe]
  constructor
  · rintro ⟨x, ⟨hxX, hxc⟩, rfl⟩
    refine ⟨⟨x, hxX, rfl⟩, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    rw [← map_mul, ← map_mul, hxc z hz]
  · rintro ⟨⟨x, hxX, rfl⟩, hc⟩
    refine ⟨x, ⟨hxX, fun z hz => ?_⟩, rfl⟩
    apply hf
    rw [map_mul, map_mul]
    exact hc (f z) ⟨z, hz, rfl⟩

theorem secondCenterOf_map {f : A →* B} (hf : Function.Injective f) (X : Subgroup A) :
    (secondCenterOf X).map f = secondCenterOf (X.map f) := by
  ext y
  simp only [mem_secondCenterOf, Subgroup.mem_map]
  have hcomm : ∀ x z : A, f x * f z * (f x)⁻¹ * (f z)⁻¹ = f (x * z * x⁻¹ * z⁻¹) := by
    intro x z
    simp only [map_mul, map_inv]
  constructor
  · rintro ⟨x, ⟨hxX, hx⟩, rfl⟩
    refine ⟨⟨x, hxX, rfl⟩, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    rw [hcomm, ← centerOf_map hf]
    exact ⟨_, hx z hz, rfl⟩
  · rintro ⟨⟨x, hxX, rfl⟩, hx⟩
    refine ⟨x, ⟨hxX, fun z hz => ?_⟩, rfl⟩
    have h1 := hx (f z) ⟨z, hz, rfl⟩
    rw [hcomm, ← centerOf_map hf] at h1
    obtain ⟨c, hc, hce⟩ := h1
    rw [← hf hce]
    exact hc

theorem omegaOneOf_map {f : A →* B} (hf : Function.Injective f) (X : Subgroup A) :
    (omegaOneOf X).map f = omegaOneOf (X.map f) := by
  unfold omegaOneOf
  rw [MonoidHom.map_closure]
  congr 1
  ext y
  simp only [Set.mem_image, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨x, ⟨hxX, hx2⟩, rfl⟩
    exact ⟨⟨x, hxX, rfl⟩, by rw [← map_pow, hx2, map_one]⟩
  · rintro ⟨⟨x, hxX, rfl⟩, hx2⟩
    refine ⟨x, ⟨hxX, ?_⟩, rfl⟩
    apply hf
    rw [map_pow, map_one]
    exact hx2

theorem omegaOneOf_le (X : Subgroup A) : omegaOneOf X ≤ X :=
  (Subgroup.closure_le X).2 fun _ hx => hx.1

end Ops

section Normalizer

variable {H : Type*} [Group H]

theorem mem_normalizer_of_conj {S : Subgroup H} {g : H} (h1 : ∀ x ∈ S, g * x * g⁻¹ ∈ S)
    (h2 : ∀ x ∈ S, g⁻¹ * x * g ∈ S) : g ∈ Subgroup.normalizer (S : Set H) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨h1 x, fun hx => ?_⟩
  have := h2 _ hx
  have e : g⁻¹ * (g * x * g⁻¹) * g = x := by group
  rwa [e] at this

theorem conj_mem_of_mem_normalizer {S : Subgroup H} {g : H}
    (hg : g ∈ Subgroup.normalizer (S : Set H)) {x : H} (hx : x ∈ S) : g * x * g⁻¹ ∈ S :=
  (Subgroup.mem_normalizer_iff.1 hg x).1 hx

end Normalizer

structure Frame {G E : Type} [Group G] [Group E] (P₁ P₂ : Subgroup G) (K₁ K₂ : Subgroup E) where
  φ1 : ↥P₁ ≃* ↥K₁
  φ2 : ↥P₂ ≃* ↥K₂
  ι : ↥(P₁ ⊓ P₂) →* E
  ι_inj : Function.Injective ι
  ι_mem : ∀ g, ι g ∈ K₁ ⊓ K₂
  ι_surj : ∀ w ∈ K₁ ⊓ K₂, ∃ g, ι g = w
  h1 : ∀ g : ↥(P₁ ⊓ P₂), ((φ1 ⟨g.1, g.2.1⟩ : ↥K₁) : E) = ι g
  h2 : ∀ g : ↥(P₁ ⊓ P₂), ((φ2 ⟨g.1, g.2.2⟩ : ↥K₂) : E) = ι g

noncomputable def Frame.ofIso {G E : Type} [Group G] [Group E] {P₁ P₂ : Subgroup G}
    {K₁ K₂ : Subgroup E}
    (iso : (RankTwoAmalgam.ofSubgroups P₁ P₂).Iso (RankTwoAmalgam.ofSubgroups K₁ K₂)) :
    Frame P₁ P₂ K₁ K₂ where
  φ1 := iso.φ1
  φ2 := iso.φ2
  ι := (K₁ ⊓ K₂).subtype.comp iso.φ12.toMonoidHom
  ι_inj := (K₁ ⊓ K₂).subtype_injective.comp iso.φ12.injective
  ι_mem g := (iso.φ12 g).2
  ι_surj w hw := by
    obtain ⟨g, hg⟩ := iso.φ12.surjective ⟨w, hw⟩
    exact ⟨g, congrArg Subtype.val hg⟩
  h1 g := (congrArg (fun z : ↥K₁ => (z : E)) (iso.comm1 g)).symm
  h2 g := (congrArg (fun z : ↥K₂ => (z : E)) (iso.comm2 g)).symm

section Corr

variable {G E : Type} [Group G] [Group E]

theorem conj_corr {M W : Subgroup G} {N : Subgroup E} (φ : ↥M ≃* ↥N) (hWM : W ≤ M)
    (ι : ↥W →* E) (hφ : ∀ g : ↥W, ((φ ⟨g.1, hWM g.2⟩ : ↥N) : E) = ι g) (m : ↥M) (g g' : ↥W) :
    ι g' = (φ m : E) * ι g * (φ m : E)⁻¹ ↔ (g' : G) = m * g * m⁻¹ := by
  rw [← hφ g', ← hφ g]
  have e : (φ m : E) * (φ ⟨g.1, hWM g.2⟩ : E) * (φ m : E)⁻¹ =
      ((φ (m * ⟨g.1, hWM g.2⟩ * m⁻¹) : ↥N) : E) := by
    simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]
  rw [e]
  constructor
  · intro h
    have h' : φ ⟨g'.1, hWM g'.2⟩ = φ (m * ⟨g.1, hWM g.2⟩ * m⁻¹) := Subtype.ext h
    have := congrArg Subtype.val (φ.injective h')
    simpa using this
  · intro h
    have : (⟨g'.1, hWM g'.2⟩ : ↥M) = m * ⟨g.1, hWM g.2⟩ * m⁻¹ := Subtype.ext (by simpa using h)
    rw [this]

theorem normalizer_tr_iff {M W : Subgroup G} {N : Subgroup E} (φ : ↥M ≃* ↥N) (hWM : W ≤ M)
    (ι : ↥W →* E)
    (hφ : ∀ g : ↥W, ((φ ⟨g.1, hWM g.2⟩ : ↥N) : E) = ι g) {X : Subgroup G} (hXW : X ≤ W) :
    M ≤ Subgroup.normalizer (X : Set G) ↔
      N ≤ Subgroup.normalizer (((X.subgroupOf W).map ι : Subgroup E) : Set E) := by
  have mem_tr : ∀ y : E, y ∈ (X.subgroupOf W).map ι ↔ ∃ g : ↥W, (g : G) ∈ X ∧ ι g = y := by
    intro y
    simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf]
  constructor
  · intro hM n hn
    have key : ∀ m : ↥M, ∀ w ∈ (X.subgroupOf W).map ι,
        (φ m : E) * w * (φ m : E)⁻¹ ∈ (X.subgroupOf W).map ι := by
      intro m w hw
      obtain ⟨g, hgX, rfl⟩ := (mem_tr w).1 hw
      have hmX : (m : G) * g * (m : G)⁻¹ ∈ X := conj_mem_of_mem_normalizer (hM m.2) hgX
      exact (mem_tr _).2 ⟨⟨_, hXW hmX⟩, hmX, (conj_corr φ hWM ι hφ m g _).2 rfl⟩
    have hm : (φ (φ.symm ⟨n, hn⟩) : E) = n := by simp
    refine mem_normalizer_of_conj (fun x hx => ?_) (fun x hx => ?_)
    · have := key (φ.symm ⟨n, hn⟩) x hx
      rwa [hm] at this
    · have := key (φ.symm ⟨n, hn⟩)⁻¹ x hx
      simpa [hm] using this
  · intro hN m hm
    have key : ∀ m : ↥M, ∀ x ∈ X, (m : G) * x * (m : G)⁻¹ ∈ X := by
      intro m x hx
      have hxW : x ∈ W := hXW hx
      have hmem : ((φ m : ↥N) : E) * ι ⟨x, hxW⟩ * ((φ m : ↥N) : E)⁻¹ ∈ (X.subgroupOf W).map ι :=
        conj_mem_of_mem_normalizer (hN (φ m).2) ((mem_tr _).2 ⟨⟨x, hxW⟩, hx, rfl⟩)
      obtain ⟨g', hg'X, hg'⟩ := (mem_tr _).1 hmem
      have h3 := (conj_corr φ hWM ι hφ m ⟨x, hxW⟩ g').1 hg'
      have h3' : (g' : G) = (m : G) * x * (m : G)⁻¹ := h3
      rw [← h3']
      exact hg'X
    refine mem_normalizer_of_conj (fun x hx => key ⟨m, hm⟩ x hx) (fun x hx => ?_)
    simpa using key ⟨m, hm⟩⁻¹ x hx

namespace Frame

variable {P₁ P₂ : Subgroup G} {K₁ K₂ : Subgroup E} (F : Frame P₁ P₂ K₁ K₂)

@[expose] def tr (X : Subgroup G) : Subgroup E := (X.subgroupOf (P₁ ⊓ P₂)).map F.ι

@[expose] def pb (Y : Subgroup E) : Subgroup G := (Y.comap F.ι).map (P₁ ⊓ P₂).subtype

theorem mem_tr {X : Subgroup G} {y : E} :
    y ∈ F.tr X ↔ ∃ g : ↥(P₁ ⊓ P₂), (g : G) ∈ X ∧ F.ι g = y := by
  unfold tr
  simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf]

theorem mem_pb {Y : Subgroup E} {g : G} :
    g ∈ F.pb Y ↔ ∃ hg : g ∈ P₁ ⊓ P₂, F.ι ⟨g, hg⟩ ∈ Y := by
  unfold pb
  simp only [Subgroup.mem_map, Subgroup.mem_comap]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.2, hx⟩
  · rintro ⟨hg, hx⟩
    exact ⟨⟨g, hg⟩, hx, rfl⟩

theorem pb_le (Y : Subgroup E) : F.pb Y ≤ P₁ ⊓ P₂ := Subgroup.map_subtype_le _

theorem tr_mono {X X' : Subgroup G} (h : X ≤ X') : F.tr X ≤ F.tr X' := by
  intro y hy
  obtain ⟨g, hg, rfl⟩ := F.mem_tr.1 hy
  exact F.mem_tr.2 ⟨g, h hg, rfl⟩

theorem tr_le_tr_iff {X X' : Subgroup G} (hX : X ≤ P₁ ⊓ P₂) : F.tr X ≤ F.tr X' ↔ X ≤ X' := by
  refine ⟨fun h x hx => ?_, F.tr_mono⟩
  have hmem : F.ι ⟨x, hX hx⟩ ∈ F.tr X' := h (F.mem_tr.2 ⟨⟨x, hX hx⟩, hx, rfl⟩)
  obtain ⟨g, hg, hgx⟩ := F.mem_tr.1 hmem
  have e : g = ⟨x, hX hx⟩ := F.ι_inj hgx
  have e' : (g : G) = x := congrArg Subtype.val e
  rwa [e'] at hg

theorem card_tr {X : Subgroup G} (hX : X ≤ P₁ ⊓ P₂) : Nat.card (F.tr X) = Nat.card X := by
  unfold tr
  rw [Subgroup.card_map_of_injective F.ι_inj]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hX).toEquiv

theorem tr_pb {Y : Subgroup E} (hY : Y ≤ K₁ ⊓ K₂) : F.tr (F.pb Y) = Y := by
  ext y
  rw [F.mem_tr]
  constructor
  · rintro ⟨g, hg, rfl⟩
    obtain ⟨_, hgY⟩ := F.mem_pb.1 hg
    exact hgY
  · intro hy
    obtain ⟨g, hg⟩ := F.ι_surj y (hY hy)
    exact ⟨g, F.mem_pb.2 ⟨g.2, by simpa [hg] using hy⟩, hg⟩

theorem normalizer_tr1 {X : Subgroup G} (hX : X ≤ P₁ ⊓ P₂) :
    P₁ ≤ Subgroup.normalizer (X : Set G) ↔ K₁ ≤ Subgroup.normalizer (F.tr X : Set E) :=
  normalizer_tr_iff F.φ1 inf_le_left F.ι F.h1 hX

theorem normalizer_tr2 {X : Subgroup G} (hX : X ≤ P₁ ⊓ P₂) :
    P₂ ≤ Subgroup.normalizer (X : Set G) ↔ K₂ ≤ Subgroup.normalizer (F.tr X : Set E) :=
  normalizer_tr_iff F.φ2 inf_le_right F.ι F.h2 hX

theorem isElemAbelian_tr {X : Subgroup G} (hX : X ≤ P₁ ⊓ P₂) :
    IsElemAbelian 2 (F.tr X) ↔ IsElemAbelian 2 X := by
  have hsub : (X.subgroupOf (P₁ ⊓ P₂)).map (P₁ ⊓ P₂).subtype = X :=
    Subgroup.map_subgroupOf_eq_of_le hX
  constructor
  · intro h
    have h1 : IsElemAbelian 2 (X.subgroupOf (P₁ ⊓ P₂)) := isElemAbelian_of_map_injective F.ι_inj h
    have h2 := isElemAbelian_map (P₁ ⊓ P₂).subtype h1
    rwa [hsub] at h2
  · intro h
    have h1 : IsElemAbelian 2 (X.subgroupOf (P₁ ⊓ P₂)) :=
      isElemAbelian_of_map_injective (P₁ ⊓ P₂).subtype_injective (by rwa [hsub])
    exact isElemAbelian_map F.ι h1

noncomputable def equivTr {X : Subgroup G} (hX : X ≤ P₁ ⊓ P₂) : ↥X ≃* ↥(F.tr X) :=
  (Subgroup.subgroupOfEquivOfLe hX).symm.trans
    ((X.subgroupOf (P₁ ⊓ P₂)).equivMapOfInjective F.ι F.ι_inj)

theorem tr_op {Op : ∀ (K : Type) [Group K], Subgroup K → Subgroup K}
    (hmap : ∀ (K L : Type) [Group K] [Group L] (f : K →* L), Function.Injective f →
      ∀ X : Subgroup K, (Op K X).map f = Op L (X.map f))
    (hle : ∀ (K : Type) [Group K] (X : Subgroup K), Op K X ≤ X)
    {X : Subgroup G} (hX : X ≤ P₁ ⊓ P₂) : F.tr (Op G X) = Op E (F.tr X) := by
  unfold tr
  have h1 : (Op G X).subgroupOf (P₁ ⊓ P₂) = Op ↥(P₁ ⊓ P₂) (X.subgroupOf (P₁ ⊓ P₂)) := by
    apply Subgroup.map_injective (P₁ ⊓ P₂).subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le ((hle G X).trans hX),
      hmap ↥(P₁ ⊓ P₂) G (P₁ ⊓ P₂).subtype (P₁ ⊓ P₂).subtype_injective,
      Subgroup.map_subgroupOf_eq_of_le hX]
  rw [h1, hmap ↥(P₁ ⊓ P₂) E F.ι F.ι_inj]

theorem tr_secondCenterOf {X : Subgroup G} (hX : X ≤ P₁ ⊓ P₂) :
    F.tr (secondCenterOf X) = secondCenterOf (F.tr X) :=
  F.tr_op (Op := fun (K : Type) [Group K] (X : Subgroup K) => secondCenterOf X)
    (fun _ _ _ _ _ hf X => secondCenterOf_map hf X) (fun _ _ _ => secondCenterOf_le) hX

theorem tr_omegaOneOf {X : Subgroup G} (hX : X ≤ P₁ ⊓ P₂) :
    F.tr (omegaOneOf X) = omegaOneOf (F.tr X) :=
  F.tr_op (Op := fun (K : Type) [Group K] (X : Subgroup K) => omegaOneOf X)
    (fun _ _ _ _ _ hf X => omegaOneOf_map hf X) (fun _ _ X => omegaOneOf_le X) hX

include F in
theorem pCoreOf_le_inf (hcore : pCoreOf 2 K₁ ≤ K₁ ⊓ K₂) : pCoreOf 2 P₁ ≤ P₁ ⊓ P₂ := by
  intro p hp
  obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.1 hp
  have h1 : (F.φ1 u : E) ∈ pCoreOf 2 K₁ := by
    refine Subgroup.mem_map.2 ⟨F.φ1 u, ?_, rfl⟩
    rw [← CFSG.LieType.BorelTits.map_pCore_mulEquiv 2 F.φ1]
    exact Subgroup.mem_map_of_mem _ hu
  obtain ⟨g, hg⟩ := F.ι_surj _ (hcore h1)
  have e : (⟨g.1, g.2.1⟩ : ↥P₁) = u := by
    apply F.φ1.injective
    apply Subtype.ext
    rw [F.h1 g, hg]
  have e' : (u : G) = g.1 := (congrArg Subtype.val e).symm
  show (u : G) ∈ P₁ ⊓ P₂
  rw [e']
  exact g.2

theorem tr_pCoreOf (hcore : pCoreOf 2 K₁ ≤ K₁ ⊓ K₂) : F.tr (pCoreOf 2 P₁) = pCoreOf 2 K₁ := by
  apply le_antisymm
  · intro y hy
    obtain ⟨g, hgP, rfl⟩ := F.mem_tr.1 hy
    obtain ⟨u, hu, hug⟩ := Subgroup.mem_map.1 hgP
    have hu' : u = ⟨g.1, g.2.1⟩ := Subtype.ext hug
    rw [← F.h1 g, ← hu']
    refine Subgroup.mem_map.2 ⟨F.φ1 u, ?_, rfl⟩
    rw [← CFSG.LieType.BorelTits.map_pCore_mulEquiv 2 F.φ1]
    exact Subgroup.mem_map_of_mem _ hu
  · intro y hy
    obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.1 hy
    obtain ⟨g, hg⟩ := F.ι_surj _ (hcore hy)
    refine F.mem_tr.2 ⟨g, ?_, hg⟩
    rw [← CFSG.LieType.BorelTits.map_pCore_mulEquiv 2 F.φ1] at hv
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.1 hv
    have e : (⟨g.1, g.2.1⟩ : ↥P₁) = u := by
      apply F.φ1.injective
      apply Subtype.ext
      rw [F.h1 g]
      exact hg
    exact ⟨u, hu, (congrArg Subtype.val e).symm⟩

end Frame

end Corr

@[expose] def AutLocalConcl {G : Type} [Group G] (H L2 : Subgroup G) : Prop :=
  Nat.card (secondCenterOf (pCoreOf 2 H)) = 8 ∧
    (∀ x ∈ secondCenterOf (pCoreOf 2 H), x * x = 1) ∧
    (∀ Q : Subgroup G, secondCenterOf (pCoreOf 2 H) ≤ Q → Q ≤ pCoreOf 2 H →
        H ≤ Subgroup.normalizer (Q : Set G) →
        Q = secondCenterOf (pCoreOf 2 H) ∨
        (Nat.card Q = 16 ∧ ∀ x ∈ Q, x * x = 1 → x ∈ secondCenterOf (pCoreOf 2 H)) ∨
        omegaOneOf (pCoreOf 2 H) ≤ Q) ∧
    IsQ8Sq ↥(omegaOneOf (pCoreOf 2 H)) ∧
    ∃ E : Subgroup G, E ≤ omegaOneOf (pCoreOf 2 H) ∧ IsElemAbelian 2 E ∧ Nat.card E = 8 ∧
      L2 ≤ Subgroup.normalizer (E : Set G) ∧
      ∀ V : Subgroup G, V ≤ pCoreOf 2 H → Nat.card V = 4 →
        L2 ≤ Subgroup.normalizer (V : Set G) → V ≤ E

theorem AutLocalConcl.of_iso {G E : Type} [Group G] [Group E] {P₁ P₂ : Subgroup G}
    {K₁ K₂ : Subgroup E}
    (iso : (RankTwoAmalgam.ofSubgroups P₁ P₂).Iso (RankTwoAmalgam.ofSubgroups K₁ K₂))
    (hcore : pCoreOf 2 K₁ ≤ K₁ ⊓ K₂) (h : AutLocalConcl K₁ K₂) : AutLocalConcl P₁ P₂ := by
  obtain ⟨hF8, hF2, hQ, hQ8, E', hE'ω, hE'el, hE'8, hE'N, hE'V⟩ := h
  let F : Frame P₁ P₂ K₁ K₂ := Frame.ofIso iso
  have hPW : pCoreOf 2 P₁ ≤ P₁ ⊓ P₂ := F.pCoreOf_le_inf hcore
  have hP : F.tr (pCoreOf 2 P₁) = pCoreOf 2 K₁ := F.tr_pCoreOf hcore
  have hF : secondCenterOf (pCoreOf 2 P₁) ≤ P₁ ⊓ P₂ := secondCenterOf_le.trans hPW
  have hFtr : F.tr (secondCenterOf (pCoreOf 2 P₁)) = secondCenterOf (pCoreOf 2 K₁) := by
    rw [F.tr_secondCenterOf hPW, hP]
  have hω : omegaOneOf (pCoreOf 2 P₁) ≤ P₁ ⊓ P₂ := (omegaOneOf_le _).trans hPW
  have hωtr : F.tr (omegaOneOf (pCoreOf 2 P₁)) = omegaOneOf (pCoreOf 2 K₁) := by
    rw [F.tr_omegaOneOf hPW, hP]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [← F.card_tr hF, hFtr]
    exact hF8
  · intro x hx
    have hxW : x ∈ P₁ ⊓ P₂ := hF hx
    have hmem : F.ι ⟨x, hxW⟩ ∈ secondCenterOf (pCoreOf 2 K₁) := by
      rw [← hFtr]
      exact F.mem_tr.2 ⟨⟨x, hxW⟩, hx, rfl⟩
    have h1 := hF2 _ hmem
    have h2 : (⟨x, hxW⟩ : ↥(P₁ ⊓ P₂)) * ⟨x, hxW⟩ = 1 :=
      F.ι_inj (by rw [map_mul, map_one]; exact h1)
    have h3 := congrArg Subtype.val h2
    simpa using h3
  · intro Q hFQ hQP hN
    have hQW : Q ≤ P₁ ⊓ P₂ := hQP.trans hPW
    have hlow : secondCenterOf (pCoreOf 2 K₁) ≤ F.tr Q := by
      rw [← hFtr]
      exact F.tr_mono hFQ
    have hup : F.tr Q ≤ pCoreOf 2 K₁ := by
      rw [← hP]
      exact F.tr_mono hQP
    have hNK : K₁ ≤ Subgroup.normalizer (F.tr Q : Set E) := (F.normalizer_tr1 hQW).1 hN
    rcases hQ (F.tr Q) hlow hup hNK with h1 | ⟨h2, h3⟩ | h4
    · left
      refine le_antisymm ?_ hFQ
      rw [← F.tr_le_tr_iff hQW, hFtr]
      exact h1.le
    · right
      left
      refine ⟨by rw [← F.card_tr hQW]; exact h2, fun x hx hx2 => ?_⟩
      have hxW : x ∈ P₁ ⊓ P₂ := hQW hx
      have hmem : F.ι ⟨x, hxW⟩ ∈ F.tr Q := F.mem_tr.2 ⟨⟨x, hxW⟩, hx, rfl⟩
      have hsq : F.ι ⟨x, hxW⟩ * F.ι ⟨x, hxW⟩ = 1 := by
        rw [← map_mul]
        have : (⟨x, hxW⟩ : ↥(P₁ ⊓ P₂)) * ⟨x, hxW⟩ = 1 := Subtype.ext hx2
        rw [this, map_one]
      have h5 := h3 _ hmem hsq
      rw [← hFtr] at h5
      obtain ⟨g, hg, hgx⟩ := F.mem_tr.1 h5
      have e : g = ⟨x, hxW⟩ := F.ι_inj hgx
      have e' : (g : G) = x := congrArg Subtype.val e
      rwa [e'] at hg
    · right
      right
      rw [← F.tr_le_tr_iff hω, hωtr]
      exact h4
  · have e : ↥(omegaOneOf (pCoreOf 2 P₁)) ≃* ↥(omegaOneOf (pCoreOf 2 K₁)) :=
      (F.equivTr hω).trans (MulEquiv.subgroupCongr hωtr)
    exact IsQ8Sq.of_mulEquiv e.symm hQ8
  · have hE'K : E' ≤ K₁ ⊓ K₂ := hE'ω.trans ((omegaOneOf_le _).trans hcore)
    have hEtr : F.tr (F.pb E') = E' := F.tr_pb hE'K
    have hEW : F.pb E' ≤ P₁ ⊓ P₂ := F.pb_le E'
    refine ⟨F.pb E', ?_, ?_, ?_, ?_, ?_⟩
    · rw [← F.tr_le_tr_iff hEW, hEtr, hωtr]
      exact hE'ω
    · exact (F.isElemAbelian_tr hEW).1 (by rw [hEtr]; exact hE'el)
    · rw [← F.card_tr hEW, hEtr]
      exact hE'8
    · exact (F.normalizer_tr2 hEW).2 (by rw [hEtr]; exact hE'N)
    · intro V hVP hV4 hN
      have hVW : V ≤ P₁ ⊓ P₂ := hVP.trans hPW
      have hVup : F.tr V ≤ pCoreOf 2 K₁ := by
        rw [← hP]
        exact F.tr_mono hVP
      have h1 := hE'V (F.tr V) hVup (by rw [F.card_tr hVW]; exact hV4)
        ((F.normalizer_tr2 hVW).1 hN)
      rw [← hEtr] at h1
      exact (F.tr_le_tr_iff hVW).1 h1

end CFSG.Quasithin.AmalTransport
