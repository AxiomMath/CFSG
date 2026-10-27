module

public import CFSG.Quasithin.Vol2.E2SevenPairN

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique B6
open scoped commutatorElement

namespace E2

variable {G : Type} [Group G] [Finite G] {H T M V : Subgroup G}

@[expose] def tiClosure (M V : Subgroup G) : Subgroup G :=
  Subgroup.closure {x | ∃ m ∈ M, x ∈ conjSub m V}

omit [Finite G] in
theorem conjSub_le_tiClosure {m : G} (hm : m ∈ M) : conjSub m V ≤ tiClosure M V :=
  fun _ hx => Subgroup.subset_closure ⟨m, hm, hx⟩

omit [Finite G] in
theorem le_tiClosure : V ≤ tiClosure M V := by
  have h := conjSub_le_tiClosure (M := M) (V := V) M.one_mem
  rwa [conjSub_one] at h

theorem Hyp28.isSylowTwoOf_M (h : Hyp28 H T M V) : IsSylowTwoOf T M := by
  have hMH : M ≤ H := h.minParabolic.maximal.1.le
  have hTM : T ≤ M := h.minParabolic.le
  refine ⟨hTM, h.minParabolic.isSylow.2.1, fun hdvd => h.minParabolic.isSylow.2.2 ?_⟩
  have h1 := Subgroup.relIndex_mul_relIndex T M H hTM hMH
  have h2 : 2 ∣ T.relIndex H := by rw [← h1]; exact Dvd.dvd.mul_right hdvd _
  exact h2

theorem Hyp28.pCoreOf_M_le_T (h : Hyp28 H T M V) : pCoreOf 2 M ≤ T :=
  pCoreOf_two_le_of_isSylowTwoOf h.isSylowTwoOf_M

theorem Hyp28.conjSub_le_pCoreOf (h : Hyp28 H T M V) {m : G} (hm : m ∈ M) :
    conjSub m V ≤ pCoreOf 2 M := by
  intro x hx
  rw [mem_conjSub] at hx
  have h1 := h.le_pCoreOf hx
  have h2 := (Subgroup.mem_normalizer_iff.mp
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M hm) _).mp h1
  simpa [mul_assoc] using h2

theorem Hyp28.commute_of_isTISetIn (h : Hyp28 H T M V) (hTI : IsTISetIn V M) {m v w : G}
    (hm : m ∈ M) (hv : v ∈ V) (hw : w ∈ conjSub m V) : Commute v w := by
  have hO2T := h.pCoreOf_M_le_T
  have hwN : w ∈ Subgroup.normalizer (V : Set G) :=
    h.normal_T (hO2T (h.conjSub_le_pCoreOf hm hw))
  have hv' : m⁻¹ * v * m ∈ Subgroup.normalizer (V : Set G) := by
    have h1 : m⁻¹ * v * m ∈ conjSub m⁻¹ V := by
      rw [mem_conjSub, inv_inv]
      simpa [mul_assoc] using hv
    exact h.normal_T (hO2T (h.conjSub_le_pCoreOf (M.inv_mem hm) h1))
  have hcV : v * w * v⁻¹ * w⁻¹ ∈ V := by
    have h1 : w * v⁻¹ * w⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.mp hwN _).mp (V.inv_mem hv)
    have := V.mul_mem hv h1
    simpa [mul_assoc] using this
  have hcW : v * w * v⁻¹ * w⁻¹ ∈ conjSub m V := by
    rw [mem_conjSub] at hw ⊢
    have h1 : (m⁻¹ * v * m) * (m⁻¹ * w * m) * (m⁻¹ * v * m)⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.mp hv' _).mp hw
    have h2 := V.mul_mem h1 (V.inv_mem hw)
    have e : m⁻¹ * (v * w * v⁻¹ * w⁻¹) * m =
        (m⁻¹ * v * m) * (m⁻¹ * w * m) * (m⁻¹ * v * m)⁻¹ * (m⁻¹ * w * m)⁻¹ := by group
    rw [e]
    exact h2
  by_cases hmN : m ∈ Subgroup.normalizer (V : Set G)
  · have hw' : w ∈ V := by
      rw [conjSub_eq_self hmN] at hw
      exact hw
    have := h.elem.1
    exact setLike_mul_comm hv hw'
  · have hmN' : m⁻¹ ∉ Subgroup.normalizer (V : Set G) := by
      intro hN
      apply hmN
      have := Subgroup.inv_mem (Subgroup.normalizer (V : Set G)) hN
      rwa [inv_inv] at this
    have hbot := hTI.2 m⁻¹ (M.inv_mem hm) hmN'
    have hc' : v * w * v⁻¹ * w⁻¹ ∈ conjSubgroup V m⁻¹ := by
      rw [mem_conjSubgroup_iff]
      rw [mem_conjSub] at hcW
      simpa using hcW
    have hc : v * w * v⁻¹ * w⁻¹ ∈ V ⊓ conjSubgroup V m⁻¹ := ⟨hcV, hc'⟩
    rw [hbot, Subgroup.mem_bot] at hc
    have : v * w = w * v := by
      calc v * w = (v * w * v⁻¹ * w⁻¹) * (w * v) := by group
        _ = w * v := by rw [hc, one_mul]
    exact this

theorem Hyp28.tiClosure_le_pCoreOf (h : Hyp28 H T M V) : tiClosure M V ≤ pCoreOf 2 M :=
  (Subgroup.closure_le _).mpr fun _ ⟨_, hm, hx⟩ => h.conjSub_le_pCoreOf hm hx

theorem Hyp28.isElemAbelian_tiClosure (h : Hyp28 H T M V) (hTI : IsTISetIn V M) :
    IsElemAbelian 2 (tiClosure M V) := by
  set S : Set G := {x | ∃ m ∈ M, x ∈ conjSub m V} with hS
  have hc : ∀ x ∈ S, ∀ y ∈ S, Commute x y := by
    rintro x ⟨m₁, hm₁, hx⟩ y ⟨m₂, hm₂, hy⟩
    rw [mem_conjSub] at hx hy
    have hy' : m₁⁻¹ * y * m₁ ∈ conjSub (m₁⁻¹ * m₂) V := by
      rw [mem_conjSub]
      simpa [mul_assoc] using hy
    have h1 := h.commute_of_isTISetIn hTI (M.mul_mem (M.inv_mem hm₁) hm₂) hx hy'
    have h2 : (m₁⁻¹ * x * m₁) * (m₁⁻¹ * y * m₁) = (m₁⁻¹ * y * m₁) * (m₁⁻¹ * x * m₁) := h1
    show x * y = y * x
    have h3 : m₁ * ((m₁⁻¹ * x * m₁) * (m₁⁻¹ * y * m₁)) * m₁⁻¹ =
        m₁ * ((m₁⁻¹ * y * m₁) * (m₁⁻¹ * x * m₁)) * m₁⁻¹ := by rw [h2]
    simpa [mul_assoc] using h3
  have hp : ∀ x ∈ S, x ^ 2 = 1 := by
    rintro x ⟨m, -, hx⟩
    rw [mem_conjSub] at hx
    have h1 := h.elem.2 _ hx
    have h2 : x ^ 2 = m * (m⁻¹ * x * m) ^ 2 * m⁻¹ := by
      rw [pow_two, pow_two]
      group
    rw [h2, h1, mul_one, mul_inv_cancel]
  have hcomm : IsMulCommutative (Subgroup.closure S) :=
    Subgroup.isMulCommutative_closure fun x hx y hy _ => hc x hx y hy
  refine ⟨hcomm, fun x hx => ?_⟩
  induction hx using Subgroup.closure_induction with
  | mem x hx => exact hp x hx
  | one => exact one_pow 2
  | mul x y hx hy ihx ihy =>
    have hxy : Commute x y := by
      have := hcomm.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩
      exact congrArg Subtype.val this
    rw [hxy.mul_pow, ihx, ihy, one_mul]
  | inv x hx ihx => rw [inv_pow, ihx, inv_one]

omit [Finite G] in
theorem le_normalizer_tiClosure : M ≤ Subgroup.normalizer (tiClosure M V : Set G) := by
  have key : ∀ g ∈ M, ∀ x ∈ tiClosure M V, g * x * g⁻¹ ∈ tiClosure M V := by
    intro g hg x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨m, hm, hxm⟩ := hx
      refine Subgroup.subset_closure ⟨g * m, M.mul_mem hg hm, ?_⟩
      rw [mem_conjSub] at hxm ⊢
      simpa [mul_assoc] using hxm
    | one => simp
    | mul x y _ _ ihx ihy =>
      have := (tiClosure M V).mul_mem ihx ihy
      simpa [mul_assoc] using this
    | inv x _ ihx =>
      have := (tiClosure M V).inv_mem ihx
      simpa [mul_assoc] using this
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact key g hg x
  · intro hx
    have := key g⁻¹ (M.inv_mem hg) _ hx
    simpa [mul_assoc] using this

theorem mem_tauOf_of_commutator_mem_kerIn (hmp : MinParabolic H T M) {A : Subgroup G}
    (hAT : A ≤ T) {t : G} (ht : t ∈ T) (hta : ∀ a ∈ A, ⁅t, a⁆ ∈ kerIn M H) :
    t ∈ E1.tauOf H T A := by
  refine E1.mem_tauOf.mpr ⟨ht,
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H (hmp.isSylow.1 ht), fun a ha => ?_⟩
  have hcT : ⁅t, a⁆ ∈ T := by
    rw [commutatorElement_def]
    exact T.mul_mem (T.mul_mem (T.mul_mem ht (hAT ha)) (T.inv_mem ht)) (T.inv_mem (hAT ha))
  have hz : Subgroup.zpowers ⁅t, a⁆ ≤ pCoreOf 2 H :=
    hmp.le_pCoreOf_of_isPGroup_of_le_kerIn
      (hmp.isSylow.2.1.to_le (Subgroup.zpowers_le.mpr hcT))
      (Subgroup.zpowers_le.mpr (hta a ha))
  exact hz (Subgroup.mem_zpowers _)

theorem solvableRadical_map_le_kerIn {Y : Subgroup G} (hYH : Y ≤ H)
    {L : Subgroup (StarQuot M H)} (hLY : L ≤ star M H Y) (hLn : L.Normal)
    (hs : IsSimpleGroup ↥L) (hnab : ∃ a b : ↥L, a * b ≠ b * a)
    (hC : Subgroup.centralizer (L : Set (StarQuot M H)) = ⊥) :
    (CFSG.solvableRadical ↥Y).map Y.subtype ≤ kerIn M H := by
  set R := (CFSG.solvableRadical ↥Y).map Y.subtype with hRdef
  have hRY : R ≤ Y := Subgroup.map_subtype_le _
  have hRH : R ≤ H := hRY.trans hYH
  have hYR : Y ≤ Subgroup.normalizer (R : Set G) := fun y hy =>
    le_normalizer_map_subtype (CFSG.solvableRadical ↥Y) hy
  have hRs : Group.IsSolvable ↥(star M H R) := by
    have h1 : Group.IsSolvable ↥(CFSG.solvableRadical ↥Y) := A3.solvableRadical_isSolvable
    have h2 : Group.IsSolvable ↥R := Group.isSolvable_of_surjective
      (f := (Subgroup.equivMapOfInjective _ _ Y.subtype_injective).toMonoidHom)
      (MulEquiv.surjective _)
    have h3 : Group.IsSolvable ↥(R.subgroupOf H) := Group.isSolvable_of_surjective
      (f := (Subgroup.subgroupOfEquivOfLe hRH).symm.toMonoidHom) (MulEquiv.surjective _)
    exact Group.isSolvable_of_surjective
      (f := (E2P.starMap M H).subgroupMap (R.subgroupOf H))
      ((E2P.starMap M H).subgroupMap_surjective _)
  have hLN : L ≤ Subgroup.normalizer (star M H R : Set (StarQuot M H)) := by
    intro x hx
    obtain ⟨⟨y, hyH⟩, hyY, rfl⟩ := hLY hx
    exact starMap_mem_normalizer hyH (hYR (Subgroup.mem_subgroupOf.mp hyY))
  have hRL : star M H R ⊓ L = ⊥ := by
    have hnorm : ((star M H R ⊓ L).subgroupOf L).Normal := by
      rw [Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right]
      exact fun y hy => mem_normalizer_inf_of_mem (hLN hy) (Subgroup.le_normalizer hy)
    rcases hs.eq_bot_or_eq_top_of_normal ((star M H R ⊓ L).subgroupOf L) with h0 | h0
    · rw [Subgroup.subgroupOf_eq_bot] at h0
      exact eq_bot_iff.mpr fun x hx => (Subgroup.mem_bot).mpr
        ((Subgroup.disjoint_def.mp h0) hx hx.2)
    · exfalso
      rw [Subgroup.subgroupOf_eq_top] at h0
      have hLs : Group.IsSolvable ↥L := Group.isSolvable_of_isSolvable_injective
        (f := Subgroup.inclusion (h0.trans inf_le_left)) (Subgroup.inclusion_injective _)
      obtain ⟨a, b, hab⟩ := hnab
      exact hab ((IsSimpleGroup.comm_iff_isSolvable).mpr hLs a b)
  have hRC : star M H R ≤ Subgroup.centralizer (L : Set (StarQuot M H)) := by
    intro r hr
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have h1 : l * r * l⁻¹ * r⁻¹ ∈ star M H R := by
      have := (Subgroup.mem_normalizer_iff.mp (hLN hl) r).mp hr
      exact (star M H R).mul_mem this ((star M H R).inv_mem hr)
    have h2 : l * r * l⁻¹ * r⁻¹ ∈ L := by
      have := (hLn.conj_mem _ (L.inv_mem hl) r)
      have h3 := L.mul_mem hl this
      simpa [mul_assoc] using h3
    have h4 : l * r * l⁻¹ * r⁻¹ ∈ star M H R ⊓ L := ⟨h1, h2⟩
    rw [hRL, Subgroup.mem_bot] at h4
    calc l * r = (l * r * l⁻¹ * r⁻¹) * (r * l) := by group
      _ = r * l := by rw [h4, one_mul]
  rw [hC] at hRC
  intro x hx
  have h1 : E2P.starMap M H ⟨x, hRH hx⟩ ∈ star M H R := starMap_mem_star (hRH hx) hx
  have h2 := hRC h1
  rw [Subgroup.mem_bot] at h2
  have h3 : (⟨x, hRH hx⟩ : ↥H) ∈ (E2P.starMap M H).ker := h2
  rw [E2P.ker_starMap, Subgroup.mem_subgroupOf] at h3
  exact h3

theorem card_star_le_card_barRad {Y A : Subgroup G} (hYH : Y ≤ H) (hAY : A ≤ Y)
    (hR : (CFSG.solvableRadical ↥Y).map Y.subtype ≤ kerIn M H) :
    Nat.card (star M H A) ≤ Nat.card (E1.barRad ↥Y (A.subgroupOf Y)) := by
  set ψ : ↥Y →* StarQuot M H := (E2P.starMap M H).comp (Subgroup.inclusion hYH) with hψ
  have hker : CFSG.solvableRadical ↥Y ≤ ψ.ker := by
    intro y hy
    rw [MonoidHom.mem_ker, hψ, MonoidHom.comp_apply]
    have h1 : (y : G) ∈ kerIn M H := hR ⟨y, hy, rfl⟩
    show QuotientGroup.mk' _ (Subgroup.inclusion hYH y) = 1
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact h1
  set φ := QuotientGroup.lift (CFSG.solvableRadical ↥Y) ψ hker with hφ
  have hmap : (E1.barRad ↥Y (A.subgroupOf Y)).map φ = star M H A := by
    unfold E1.barRad
    rw [Subgroup.map_map]
    have e : φ.comp (QuotientGroup.mk' (CFSG.solvableRadical ↥Y)) = ψ := by
      ext y
      rfl
    rw [e]
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact starMap_mem_star (hYH y.2) (Subgroup.mem_subgroupOf.mp hy)
    · rintro ⟨⟨x, hxH⟩, hxA, rfl⟩
      refine ⟨⟨x, hAY (Subgroup.mem_subgroupOf.mp hxA)⟩,
        Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mp hxA), rfl⟩
  rw [← hmap]
  exact Nat.card_le_card_of_surjective (φ.subgroupMap _) (φ.subgroupMap_surjective _)

omit [Finite G] in
theorem le_normalizer_weakClosure_of_le {Ω : Set (Subgroup G)} (hΩ : E1.IsInvColl H Ω)
    (hTH : T ≤ H) : T ≤ Subgroup.normalizer (E1.weakClosure T Ω : Set G) := by
  have key : ∀ t ∈ T, ∀ x ∈ E1.weakClosure T Ω, t * x * t⁻¹ ∈ E1.weakClosure T Ω := by
    intro t ht x hx
    have hle : E1.weakClosure T Ω ≤ (E1.weakClosure T Ω).comap (MulAut.conj t).toMonoidHom := by
      refine iSup₂_le fun A hA => iSup_le fun hAT => ?_
      intro a ha
      rw [Subgroup.mem_comap]
      have h1 : A1b.conjSub t A ∈ Ω := hΩ.conj A hA t (hTH ht)
      have h2 : A1b.conjSub t A ≤ T := by
        intro y hy
        rw [A1b.mem_conjSub_iff] at hy
        have h3 := T.mul_mem (T.mul_mem ht (hAT hy)) (T.inv_mem ht)
        have e : t * (t⁻¹ * y * t) * t⁻¹ = y := by group
        rwa [e] at h3
      exact le_iSup₂_of_le (f := fun A (_ : A ∈ Ω) => ⨆ (_ : A ≤ T), A) _ h1
        (le_iSup_of_le h2 le_rfl) (A1b.mem_conjSub_of_mem ha)
    exact hle hx
  intro t ht
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact key t ht x
  · intro hx
    have := key t⁻¹ (T.inv_mem ht) _ hx
    simpa [mul_assoc] using this

theorem le_nParam_of_forall_isE (hmp : MinParabolic H T M) {E : Subgroup G} (hET : E ≤ T)
    (hE : IsElemAbelian 2 E) (hEJ : ¬ E ≤ kerIn M H) {n : ℕ}
    (hmem : ∀ i : ℕ, 0 < i → i < n → ∀ g ∈ H, A1b.conjSub g E ≤ T → ∀ K' : Subgroup G,
      E1.IsE i H T (A1b.conjSub g E) K' → K' ≤ M) :
    (n : ℕ∞) ≤ E1.nParam H := by
  have hTH : T ≤ H := hmp.isSylow.1
  have hMH : M < H := hmp.maximal.1
  set Ω : Set (Subgroup G) := {A | ∃ g ∈ H, A = A1b.conjSub g E} with hΩdef
  have hΩ : E1.IsInvColl H Ω := by
    refine ⟨?_, ?_, ?_⟩
    · rintro A ⟨g, hg, rfl⟩ x hx
      rw [A1b.mem_conjSub_iff] at hx
      have h1 := H.mul_mem (H.mul_mem hg (hTH (hET hx))) (H.inv_mem hg)
      have e : g * (g⁻¹ * x * g) * g⁻¹ = x := by group
      rwa [e] at h1
    · rintro A ⟨g, hg, rfl⟩
      exact isElemAbelian_cjSub hE
    · rintro A ⟨g, hg, rfl⟩ x hx
      exact ⟨x * g, H.mul_mem hx hg, by rw [A1b.conjSub_mul]⟩
  have hEΩ : E ∈ Ω := ⟨1, H.one_mem, (A1b.conjSub_one E).symm⟩
  have hNW : H ⊓ Subgroup.normalizer (E1.weakClosure T Ω : Set G) ≤ M := by
    refine hmp.le_of_lt (le_inf hTH (le_normalizer_weakClosure_of_le hΩ hTH))
      (lt_of_le_of_ne inf_le_left fun heq => hEJ ?_)
    have hHW : H ≤ Subgroup.normalizer (E1.weakClosure T Ω : Set G) := heq ▸ inf_le_right
    have hW : E1.weakClosure T Ω ≤ T := iSup₂_le fun _ _ => iSup_le fun h => h
    have hWO := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (hW.trans hTH) hHW
      (hmp.isSylow.2.1.to_le hW)
    have hEW : E ≤ E1.weakClosure T Ω :=
      le_iSup₂_of_le (f := fun A (_ : A ∈ Ω) => ⨆ (_ : A ≤ T), A) E hEΩ (le_iSup_of_le hET le_rfl)
    exact hEW.trans (hWO.trans hmp.pCoreOf_le_kerIn)
  have key : ∀ i : ℕ, 0 < i → i < n → ¬ E1.InE i H := by
    intro i hi0 hin hInE
    have h1 := hInE T hmp.isSylow Ω hΩ
    have hE0 : E1.eGen i H T Ω ≤ M := iSup₂_le fun A hA => iSup_le fun hAT =>
      iSup₂_le fun K' hK' => by
        obtain ⟨g, hg, rfl⟩ := hA
        exact hmem i hi0 hin g hg hAT K' hK'
    have : H ≤ M := by
      rw [← h1]
      exact sup_le hE0 hNW
    exact hMH.not_ge this
  by_contra hne
  have hlt : E1.nParam H < n := not_le.mp hne
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp (ne_top_of_lt hlt)
  rw [← hm] at hlt
  have hmn : m < n := by exact_mod_cast hlt
  rcases Nat.eq_zero_or_pos m with hm0 | hm0
  · have hodd := E1.odd_of_nParam_le_zero (H := H) (by rw [← hm, hm0]; rfl)
    have hE1 : E ≠ ⊥ := fun h0 => hEJ (h0 ▸ bot_le)
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (B6.isPGroup_of_isElemAbelian hE)
    have hk0 : k ≠ 0 := by
      rintro rfl
      exact hE1 (Subgroup.eq_bot_of_card_eq E (by simpa using hk))
    have hdvd : 2 ∣ Nat.card H := by
      have h1 : 2 ∣ Nat.card E := by rw [hk]; exact dvd_pow_self 2 hk0
      exact h1.trans (Subgroup.card_dvd_of_le (hET.trans hTH))
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hdvd)
  · exact key m hm0 hmn ((E1.nParam_le_iff hm0).mp (le_of_eq hm.symm))

end E2

end CFSG.Quasithin
