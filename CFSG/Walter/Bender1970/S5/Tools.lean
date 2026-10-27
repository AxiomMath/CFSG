module

public import CFSG.Walter.Bender1970.S5.PSL2Even
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer
public import CFSG.Walter.Bender1970.S4.ComponentTools

public section

namespace CFSG.Walter

open CFSG.GorensteinWalter
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G]

theorem mem_centralizer_of_isTypeL2Even {L : Subgroup G} (hL : GorensteinWalter.IsQuasisimple L)
    (hL2 : IsTypeL2Even (L ⧸ Subgroup.center L)) {r : G}
    (hrN : r ∈ Subgroup.normalizer (L : Set G)) (hr : Odd (orderOf r)) (S : Sylow 2 L)
    (hrS : ∀ x ∈ (S : Subgroup L), r * (x : G) * r⁻¹ = x) :
    r ∈ Subgroup.centralizer (L : Set G) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set φ : MulAut L := L.normalizerMonoidHom ⟨r, hrN⟩ with hφ
  have hφapp : ∀ x : L, ((φ x : L) : G) = r * x * r⁻¹ := fun x =>
    Subgroup.normalizerMonoidHom_apply_apply_coe _ _ x
  set ψ := QuotientGroup.congr (Subgroup.center L) (Subgroup.center L) φ
    (Subgroup.map_center_eq φ) with hψ
  have hψmk : ∀ x : L, ψ (x : L ⧸ Subgroup.center L) = (φ x : L ⧸ Subgroup.center L) :=
    fun x => QuotientGroup.congr_mk _ _ _ _ x
  have hpow : ∀ n : ℕ, ∀ x : L,
      (ψ ^ n) (x : L ⧸ Subgroup.center L) = ((φ ^ n) x : L ⧸ Subgroup.center L) := by
    intro n
    induction n with
    | zero => intro x; rfl
    | succ n ih =>
      intro x
      rw [pow_succ', MulAut.mul_apply, ih, hψmk, pow_succ', MulAut.mul_apply]
  have hφn : φ ^ orderOf r = 1 := by
    rw [hφ, ← map_pow]
    have : (⟨r, hrN⟩ : Subgroup.normalizer (L : Set G)) ^ orderOf r = 1 :=
      Subtype.ext (by rw [Subgroup.coe_pow]; exact pow_orderOf_eq_one r)
    rw [this, map_one]
  have hψn : ψ ^ orderOf r = 1 := by
    apply MulEquiv.ext
    intro y
    induction y using QuotientGroup.induction_on with
    | H x => rw [hpow, hφn]; rfl
  have hψodd : Odd (orderOf ψ) := Odd.of_dvd_nat hr (orderOf_dvd_of_pow_eq_one hψn)
  set Sb : Sylow 2 (L ⧸ Subgroup.center L) := S.mapSurjective (QuotientGroup.mk'_surjective _)
  have hψS : ∀ x ∈ (Sb : Subgroup (L ⧸ Subgroup.center L)), ψ x = x := by
    intro x hx
    rw [Sylow.coe_mapSurjective] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    show ψ (y : L ⧸ Subgroup.center L) = y
    rw [hψmk]
    congr 1
    exact Subtype.ext ((hφapp y).trans (hrS y hy))
  have hψ1 := IsTypeL2Even.mulAut_eq_one hL2 ψ hψodd Sb hψS
  apply mem_centralizer_of_commutator_mem_center hL.2.1
  intro x hx
  have h1 : ψ ((⟨x, hx⟩ : L) : L ⧸ Subgroup.center L) = (⟨x, hx⟩ : L) := by rw [hψ1]; rfl
  rw [hψmk] at h1
  have h2 : (φ ⟨x, hx⟩) * (⟨x, hx⟩ : L)⁻¹ ∈ Subgroup.center L := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv, h1,
      mul_inv_cancel]
  refine ⟨_, h2, ?_⟩
  simp [hφapp]

theorem exists_torus_of_isComponentOf {H K : Subgroup G} (hHA : IsAStar H)
    (hK : IsComponentOf K H) (hK2 : IsTypeL2Even (K ⧸ Subgroup.center K)) (T : Sylow 2 G)
    (hTH : (T : Subgroup G) ≤ H) :
    ∃ R : Subgroup G, R ≤ K ∧
      R ≤ Subgroup.normalizer (((T : Subgroup G) ⊓ K : Subgroup G) : Set G) ∧
      Odd (Nat.card R) ∧
      (∀ u ∈ (T : Subgroup G) ⊓ K, u ≠ 1 → ∀ v ∈ (T : Subgroup G) ⊓ K, v ≠ 1 →
        ∃ r ∈ R, r * u * r⁻¹ = v) ∧
      (∀ ℓ ∈ K, orderOf ℓ = 2 → ¬ R ≤ Subgroup.centralizer ({ℓ} : Set G)) ∧
      ∀ Y : Subgroup G,
        K ⊓ Subgroup.normalizer (((T : Subgroup G) ⊓ K : Subgroup G) : Set G) ≤ Y →
        K ⊓ Subgroup.normalizer (R : Set G) ≤ Y → K ≤ Y := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨f, hf, ⟨e⟩⟩ := hK2
  set φ : K →* PSL(2, GaloisField 2 f) :=
    e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K)) with hφdef
  have hφ : Function.Surjective φ :=
    e.surjective.comp (QuotientGroup.mk'_surjective (Subgroup.center K))
  have hker : φ.ker = Subgroup.center K := by
    ext x
    rw [MonoidHom.mem_ker, hφdef, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      map_eq_one_iff _ e.injective, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hZ := component_odd_center hHA hK
  obtain ⟨P, hP⟩ := component_exists_sylow hK T hTH
  obtain ⟨R₀, hR₀N, hR₀odd, hR₀tr, hR₀inv, hR₀gen⟩ :=
    exists_torus_of_surjective hf hK.2.2.2.1 hZ hφ hker P
  have hmemQ : ∀ x : K, (x : G) ∈ (T : Subgroup G) ⊓ K ↔ x ∈ (P : Subgroup K) := by
    intro x
    rw [← hP]
    constructor
    · rintro ⟨y, hy, hyx⟩
      rwa [← Subtype.ext hyx]
    · intro hx
      exact ⟨x, hx, rfl⟩
  have hNK : ∀ x : K, x ∈ Subgroup.normalizer ((P : Subgroup K) : Set K) ↔
      (x : G) ∈ Subgroup.normalizer (((T : Subgroup G) ⊓ K : Subgroup G) : Set G) := by
    intro x
    rw [← hP]
    constructor
    · intro hx
      rw [Subgroup.mem_normalizer_iff]
      intro y
      constructor
      · rintro ⟨y', hy', rfl⟩
        exact ⟨x * y' * x⁻¹, (Subgroup.mem_normalizer_iff.mp hx y').mp hy', rfl⟩
      · rintro ⟨z, hz, hzy⟩
        have hzy' : (z : G) = (x : G) * y * (x : G)⁻¹ := hzy
        have hyK : y = (x : G)⁻¹ * z * x := by rw [hzy']; group
        refine ⟨x⁻¹ * z * x, ?_, by rw [hyK]; rfl⟩
        have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hx) z).mp hz
        rwa [inv_inv] at this
    · intro hx
      rw [Subgroup.mem_normalizer_iff]
      intro y
      have h1 := Subgroup.mem_normalizer_iff.mp hx y
      constructor
      · intro hy
        obtain ⟨z, hz, hzy⟩ := h1.mp ⟨y, hy, rfl⟩
        have : z = x * y * x⁻¹ := Subtype.ext hzy
        rwa [← this]
      · intro hy
        have h2 : (x : G) * y * (x : G)⁻¹ ∈ (P : Subgroup K).map K.subtype := ⟨_, hy, rfl⟩
        obtain ⟨z, hz, hzy⟩ := h1.mpr h2
        have : z = y := Subtype.ext hzy
        rwa [← this]
  refine ⟨R₀.map K.subtype, Subgroup.map_subtype_le R₀, ?_, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨r, hr, rfl⟩
    exact (hNK r).mp (hR₀N hr)
  · rwa [Subgroup.card_map_of_injective K.subtype_injective]
  · intro u hu hu1 v hv hv1
    obtain ⟨r, hr, hruv⟩ := hR₀tr ⟨u, hu.2⟩ ((hmemQ _).mp hu)
      (fun h => hu1 (congrArg Subtype.val h))
      ⟨v, hv.2⟩ ((hmemQ _).mp hv) (fun h => hv1 (congrArg Subtype.val h))
    exact ⟨r, ⟨r, hr, rfl⟩, congrArg Subtype.val hruv⟩
  · intro ℓ hℓK hℓ hRℓ
    apply hR₀inv ⟨ℓ, hℓK⟩ (by rwa [Subgroup.orderOf_mk])
    intro r hr
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp (hRℓ ⟨r, hr, rfl⟩))
  · intro Y hYN hYR
    have h1 := hR₀gen (Y.subgroupOf K) (fun x hx => Subgroup.mem_subgroupOf.mpr
      (hYN ⟨x.2, (hNK x).mp hx⟩)) (fun x hx => Subgroup.mem_subgroupOf.mpr (hYR ⟨x.2, ?_⟩))
    · intro x hx
      have : (⟨x, hx⟩ : K) ∈ Y.subgroupOf K := h1 ▸ Subgroup.mem_top _
      exact this
    ·
      refine mem_normalizer_of_conj_mem' fun y hy => ?_
      obtain ⟨y', hy', rfl⟩ := hy
      exact ⟨x * y' * x⁻¹, (Subgroup.mem_normalizer_iff.mp hx y').mp hy', rfl⟩

theorem card_inf_mul_card_inf_le
    {Y L J₁ J₂ : Subgroup G} (hY : IsAStar Y) (T : Sylow 2 G)
    (hTY : (T : Subgroup G) ≤ Y) (hTab : IsMulCommutative (T : Subgroup G))
    (hL : IsComponentOf L Y) (hJ₁ : IsComponentOf J₁ Y) (hJ₂ : IsComponentOf J₂ Y)
    (h1 : J₁ ≠ L) (h2 : J₂ ≠ L) (h12 : J₁ ≠ J₂) :
    Nat.card ((T : Subgroup G) ⊓ J₁ : Subgroup G) *
        Nat.card ((T : Subgroup G) ⊓ J₂ : Subgroup G) ≤
      Nat.card ((T : Subgroup G) ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) := by
  have hQ₁ := bender38Component hY hJ₁ T hTY hTab
  have hQV : ∀ {J : Subgroup G}, IsComponentOf J Y → J ≠ L →
      (T : Subgroup G) ⊓ J ≤ (T : Subgroup G) ⊓ Subgroup.centralizer (L : Set G) :=
    fun hJ hJL => inf_le_inf_left _ (le_centralizer_of_isComponentOf_ne hJ hL hJL)
  have hdisj : Disjoint ((T : Subgroup G) ⊓ J₁) ((T : Subgroup G) ⊓ J₂) := by
    rw [disjoint_iff, eq_bot_iff, ← inf_inf_eq_bot T.isPGroup' hQ₁]
    exact le_inf (inf_le_right.trans (inf_le_inf_left _
      (le_centralizer_of_isComponentOf_ne hJ₂ hJ₁ (Ne.symm h12)))) inf_le_left
  have hcomm : (T : Subgroup G) ⊓ J₂ ≤ Subgroup.normalizer
      (((T : Subgroup G) ⊓ J₁ : Subgroup G) : Set G) := fun x hx =>
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun y hy =>
      congrArg Subtype.val (hTab.is_comm.comm ⟨y, hy.1⟩ ⟨x, hx.1⟩))
  rw [← card_sup_eq_mul_of_disjoint_of_le_normalizer _ _ hcomm hdisj]
  exact Subgroup.card_le_of_le (sup_le (hQV hJ₁ h1) (hQV hJ₂ h2))

theorem card_inf_lt_of_not_le_normalizer
    {H K : Subgroup G} (hHA : IsAStar H)
    (hK : IsComponentOf K H) (T : Sylow 2 G) (hTH : (T : Subgroup G) ≤ H)
    (hTab : IsMulCommutative (T : Subgroup G)) (hn : ¬ H ≤ Subgroup.normalizer (K : Set G)) :
    Nat.card ((T : Subgroup G) ⊓ K : Subgroup G) <
      Nat.card ((T : Subgroup G) ⊓ Subgroup.centralizer (K : Set G) : Subgroup G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := mt (le_normalizer_of_forall_map_conj_eq hHA hK T hTH) hn
  push Not at h
  obtain ⟨a, ha, b, hb, hKa, hKb, hab⟩ := h
  have hca := isComponentOf_map_conj hK (Subgroup.le_normalizer ha)
  have hcb := isComponentOf_map_conj hK (Subgroup.le_normalizer hb)
  have hle := card_inf_mul_card_inf_le hHA T hTH hTab hK hca hcb hKa hKb hab
  have hcard : ∀ g : G, IsComponentOf (K.map (MulAut.conj g).toMonoidHom) H →
      Nat.card ((T : Subgroup G) ⊓ K.map (MulAut.conj g).toMonoidHom : Subgroup G) =
        Nat.card ((T : Subgroup G) ⊓ K : Subgroup G) := by
    intro g hg
    rw [(bender38Component hHA hg T hTH hTab).card_eq,
      (bender38Component hHA hK T hTH hTab).card_eq,
      Subgroup.card_map_of_injective (MulAut.conj g).injective]
  rw [hcard a hca, hcard b hcb] at hle
  have h4 := (bender38Component hHA hK T hTH hTab).four_le_card
  nlinarith

theorem le_componentLayerOf_of_le_generalizedFittingSubgroupOf {A P : Subgroup G}
    [Group.IsPerfect P] (hP : P ≤ generalizedFittingSubgroupOf A) :
    P ≤ componentLayerOf A := by
  set W := generalizedFittingSubgroupOf A with hWdef
  have hEW : componentLayerOf A ≤ W := le_sup_right
  have hFW : CFSG.fittingSubgroupOf A ≤ W := le_sup_left
  set E' := (componentLayerOf A).subgroupOf W with hE'
  set F' := (CFSG.fittingSubgroupOf A).subgroupOf W with hF'
  have : E'.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hEW).mpr
    ((generalizedFittingSubgroupOf_le A).trans
      (le_normalizer_of_isNormalIn (componentLayerOf_isNormalIn A)))
  have hsup : F' ⊔ E' = ⊤ := by
    rw [hF', hE', ← Subgroup.subgroupOf_sup hFW hEW, hWdef]
    exact Subgroup.subgroupOf_self _
  set π := QuotientGroup.mk' E' with hπ
  have : Group.IsPerfect (P.subgroupOf W) :=
    Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hP).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hP).symm.surjective
  have : Group.IsPerfect ((P.subgroupOf W).map π) := Group.IsPerfect.map _
  have hF'nil : Group.IsNilpotent F' := by
    have := CFSG.fittingSubgroupOf_isNilpotent A
    exact Group.nilpotent_of_surjective (Subgroup.subgroupOfEquivOfLe hFW).symm.toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hFW).symm.surjective
  have hFs : Group.IsSolvable (F'.map π) :=
    Group.isSolvable_of_surjective (MonoidHom.subgroupMap_surjective π F')
  have hle : (P.subgroupOf W).map π ≤ F'.map π := by
    calc (P.subgroupOf W).map π ≤ (⊤ : Subgroup W).map π := Subgroup.map_mono le_top
      _ = (F' ⊔ E').map π := by rw [hsup]
      _ = F'.map π ⊔ E'.map π := Subgroup.map_sup _ _ _
      _ = F'.map π := by
        rw [(Subgroup.map_eq_bot_iff _).mpr (QuotientGroup.ker_mk' E').ge, sup_bot_eq]
  have hbot := eq_bot_of_isPerfect_of_le_isSolvable hle hFs
  rw [Subgroup.map_eq_bot_iff, hπ, QuotientGroup.ker_mk'] at hbot
  intro x hx
  exact Subgroup.mem_subgroupOf.mp (hbot (Subgroup.mem_subgroupOf.mpr hx :
    (⟨x, hP hx⟩ : W) ∈ P.subgroupOf W))

theorem inf_centralizer_le_fittingSubgroupOf (A : Subgroup G) :
    generalizedFittingSubgroupOf A ⊓ Subgroup.centralizer (componentLayerOf A : Set G) ≤
      CFSG.fittingSubgroupOf A := by
  rintro x ⟨hxF, hxC⟩
  have hEN : componentLayerOf A ≤ Subgroup.normalizer (CFSG.fittingSubgroupOf A : Set G) :=
    (componentLayerOf_isNormalIn A).1.trans
      (le_normalizer_of_isNormalIn (fittingSubgroupOf_isNormalIn A))
  have hx : x ∈ ((CFSG.fittingSubgroupOf A ⊔ componentLayerOf A : Subgroup G) : Set G) := hxF
  rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ hEN] at hx
  obtain ⟨a, ha, e, he, rfl⟩ := hx
  have haC : a ∈ Subgroup.centralizer (componentLayerOf A : Set G) :=
    fittingSubgroupOf_le_centralizer_layer A ha
  have heC : e ∈ Subgroup.centralizer (componentLayerOf A : Set G) := by
    have : e = a⁻¹ * (a * e) := by group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ haC) hxC
  have heZ : e ∈ (Subgroup.center (componentLayerOf A)).map (componentLayerOf A).subtype :=
    ⟨⟨e, he⟩, Subgroup.mem_center_iff.mpr fun y =>
      Subtype.ext ((Subgroup.mem_centralizer_iff.mp heC) y y.2), rfl⟩
  exact Subgroup.mul_mem _ ha (center_componentLayerOf_le_fitting A heZ)

omit [Finite G] in
theorem le_oddCoreOf_of_isNormalIn {N A : Subgroup G} (hN : IsNormalIn N A)
    (hodd : Odd (Nat.card N)) : N ≤ oddCoreOf A := by
  have hNn : (N.subgroupOf A).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hN.1).mpr (le_normalizer_of_isNormalIn hN)
  have hcop : Nat.Coprime 2 (Nat.card (N.subgroupOf A)) := by
    rw [natCard_subgroupOf_of_le hN.1]
    exact Nat.coprime_two_left.mpr hodd
  have hle : N.subgroupOf A ≤ CFSG.pPrimeCore 2 A := le_sSup ⟨hNn, hcop⟩
  intro x hx
  exact ⟨⟨x, hN.1 hx⟩, hle (Subgroup.mem_subgroupOf.mpr hx), rfl⟩

theorem le_centralizer_of_le_centralizer_commutator {U D : Subgroup G}
    (hUD : U ≤ Subgroup.normalizer (D : Set G)) (hcop : Nat.Coprime (Nat.card U) (Nat.card D))
    (h : U ≤ Subgroup.centralizer ((⁅D, U⁆ : Subgroup G) : Set G)) :
    U ≤ Subgroup.centralizer (D : Set G) := by
  have h1 := commutator_le_commutator_commutator D U hUD hcop
  have h2 : ⁅⁅D, U⁆, U⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (Subgroup.le_centralizer_iff.mp h)
  rw [h2, le_bot_iff, Subgroup.commutator_eq_bot_iff_le_centralizer] at h1
  exact Subgroup.le_centralizer_iff.mp h1

theorem mem_normalizer_of_mem_centralizer_of_le {H K R : Subgroup G} (hK : IsComponentOf K H)
    (hRK : R ≤ K) (hR : ¬ R ≤ Subgroup.centralizer (K : Set G)) {g : G} (hgH : g ∈ H)
    (hgR : g ∈ Subgroup.centralizer (R : Set G)) : g ∈ Subgroup.normalizer (K : Set G) := by
  rw [← map_conj_eq_iff_mem_normalizer]
  by_contra hne
  apply hR
  have hc := isComponentOf_map_conj hK (Subgroup.le_normalizer hgH)
  have hRK' : R ≤ K.map (MulAut.conj g).toMonoidHom := by
    intro r hr
    refine ⟨r, hRK hr, ?_⟩
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    have := (Subgroup.mem_centralizer_iff.mp hgR) r hr
    rw [← this, mul_inv_cancel_right]
  exact hRK'.trans (le_centralizer_of_isComponentOf_ne hc hK hne)

end CFSG.Walter
