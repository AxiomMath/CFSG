module

public import CFSG.LocalAnalysis.WeakClosure81.W183Br1Comp
public import CFSG.LocalAnalysis.WeakClosure81.W183B2Defs
import CFSG.LocalAnalysis.WeakClosure81.Twelve

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Quasithin CFSG.Open
  CFSG.QuasithinUnique Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.UniquenessCase.PartTwo

variable {G : Type} [Group G] [Finite G]

private theorem w183_hasQuotShape_of_mulEquiv {K L L' : Subgroup G} (e : ↥L ≃* ↥L')
    (hK : ∀ l : ↥L, (l : G) ∈ K ↔ (e l : G) ∈ K) {P : ∀ (X : Type) [Group X], Prop}
    (hQ : HasQuotShape L K P) : HasQuotShape L' K P := by
  obtain ⟨X, hX, φ, hφs, hφk, hPX⟩ := hQ
  refine ⟨X, hX, φ.comp e.symm.toMonoidHom, hφs.comp e.symm.surjective, ?_, hPX⟩
  intro k
  change φ (e.symm k) = 1 ↔ (k : G) ∈ K
  rw [hφk (e.symm k)]
  have h := hK (e.symm k)
  rwa [show e (e.symm k) = k from e.apply_symm_apply k] at h

private theorem w183_isComponentModN_map_mulEquiv {K H L : Subgroup G} (e : G ≃* G)
    (hK : K.map e.toMonoidHom = K) (hH : H.map e.toMonoidHom = H)
    (h : IsComponentModN K H L) :
    IsComponentModN K H (L.map e.toMonoidHom) := by
  have hfe : Function.Injective e.toMonoidHom := fun a _b hab => e.injective (by simpa using hab)
  refine ⟨h.1, ?_, ?_, ?_, ?_⟩
  · intro k hk
    have hk' : e.symm k ∈ K := by
      rw [← hK] at hk
      obtain ⟨k', hk'K, hk'eq⟩ := Subgroup.mem_map.1 hk
      have hkk : k' = e.symm k := by
        rw [← hk'eq]
        change k' = e.symm (e k')
        rw [e.symm_apply_apply]
      rwa [hkk] at hk'K
    exact Subgroup.mem_map.2 ⟨e.symm k, h.2.1 hk', by simp⟩
  · rintro x ⟨l, hl, rfl⟩
    rw [← hH]
    exact Subgroup.mem_map_of_mem e.toMonoidHom (h.2.2.1 hl)
  · have hsub := h.2.2.2.1.map e.toMonoidHom
    rwa [hH] at hsub
  · refine w183_hasQuotShape_of_mulEquiv
      (Subgroup.equivMapOfInjective L e.toMonoidHom hfe) ?_ h.2.2.2.2
    intro l
    constructor
    · intro hl
      rw [Subgroup.coe_equivMapOfInjective_apply, ← hK]
      exact Subgroup.mem_map_of_mem e.toMonoidHom hl
    · intro hl
      rw [Subgroup.coe_equivMapOfInjective_apply, ← hK] at hl
      obtain ⟨k, hkK, hkeq⟩ := Subgroup.mem_map.1 hl
      have hkl : k = l := e.injective hkeq
      rwa [hkl] at hkK

private theorem w183_isQuasisimple_image_quotient {K H L : Subgroup G}
    (hKn : (K.subgroupOf H).Normal) (hLH : L ≤ H)
    (hQ : HasQuotShape L (K : Set G) (fun X _ => IsQuasisimple X)) :
    IsQuasisimple ((L.subgroupOf H).map (QuotientGroup.mk' (K.subgroupOf H))) := by
  classical
  haveI := hKn
  obtain ⟨X, hX, φ, hφs, hφk, hXq⟩ := hQ
  letI : Group X := hX
  let q := QuotientGroup.mk' (K.subgroupOf H)
  let A : Subgroup (↥H ⧸ (K.subgroupOf H)) := (L.subgroupOf H).map q
  let eL : ↥(L.subgroupOf H) ≃* ↥L := Subgroup.subgroupOfEquivOfLe hLH
  let φ' : ↥(L.subgroupOf H) →* X := φ.comp eL.toMonoidHom
  have hφ's : Function.Surjective φ' := hφs.comp eL.surjective
  let ψ : ↥(L.subgroupOf H) →* A := q.subgroupMap (L.subgroupOf H)
  have hψs : Function.Surjective ψ := q.subgroupMap_surjective (L.subgroupOf H)
  have hker : φ'.ker = ψ.ker := by
    ext k
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
    have h1 : φ' k = 1 ↔ (k : G) ∈ K := by
      show φ (eL k) = 1 ↔ (k : G) ∈ K
      rw [hφk (eL k)]
      rfl
    have h2 : ψ k = 1 ↔ (k : G) ∈ K := by
      constructor
      · intro hk
        have hq1 : q k = 1 := congrArg Subtype.val hk
        rw [show q = QuotientGroup.mk' (K.subgroupOf H) from rfl, QuotientGroup.mk'_apply,
          QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hq1
        exact hq1
      · intro hk
        apply Subtype.ext
        show q k = 1
        rw [show q = QuotientGroup.mk' (K.subgroupOf H) from rfl, QuotientGroup.mk'_apply,
          QuotientGroup.eq_one_iff]
        exact Subgroup.mem_subgroupOf.mpr hk
    exact h1.trans h2.symm
  let e : X ≃* A :=
    (QuotientGroup.quotientKerEquivOfSurjective φ' hφ's).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hker).trans
        (QuotientGroup.quotientKerEquivOfSurjective ψ hψs))
  exact CFSG.IsQuasisimple.of_mulEquiv e.symm hXq

private theorem w183_open_isQuasisimple_of_native {Q : Type} [Group Q]
    (h : CFSG.IsQuasisimple Q) : CFSG.Open.IsQuasisimple Q :=
  ⟨h.1.commutator_eq_top, h.2.1⟩

private theorem w183_isSimpleGroup_cj {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    {A : Subgroup (LGL 2 V)} (h : IsSimpleGroup ↥A) (y : LGL 2 V) :
    IsSimpleGroup ↥(cj y A) := by
  rw [cj]
  exact (MulEquiv.isSimpleGroup_congr
    (Subgroup.equivMapOfInjective A (MulAut.conj y).toMonoidHom
      (MulAut.conj y).injective)).mp h

private theorem w183_nonab_cj {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    {A : Subgroup (LGL 2 V)} (h : ∃ a ∈ A, ∃ b ∈ A, a * b ≠ b * a) (y : LGL 2 V) :
    ∃ a ∈ cj y A, ∃ b ∈ cj y A, a * b ≠ b * a := by
  obtain ⟨a, ha, b, hb, hab⟩ := h
  refine ⟨(MulAut.conj y) a, Subgroup.mem_map.mpr ⟨a, ha, rfl⟩,
    (MulAut.conj y) b, Subgroup.mem_map.mpr ⟨b, hb, rfl⟩, ?_⟩
  intro hconj
  apply hab
  have h1 : (MulAut.conj y) (a * b) = (MulAut.conj y) (b * a) := by
    rw [map_mul, map_mul]
    exact hconj
  exact (MulAut.conj y).injective h1

private theorem w183_center_eq_bot_of_mulEquiv {X Z : Type*} [Group X] [Group Z] (e : X ≃* Z)
    (h : Subgroup.center Z = ⊥) : Subgroup.center X = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  rw [Subgroup.mem_bot]
  have hz' : e z ∈ Subgroup.center Z := by
    rw [Subgroup.mem_center_iff] at hz ⊢
    intro w
    obtain ⟨x, rfl⟩ := e.surjective w
    show e x * e z = e z * e x
    rw [← map_mul, ← map_mul, hz x]
  rw [h, Subgroup.mem_bot] at hz'
  exact e.injective (by rw [hz', map_one])

private theorem w183_center_sup_eq_bot {Y : Type*} [Group Y] {A B : Subgroup Y}
    (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    (hA : Subgroup.center (↥A) = ⊥) (hB : Subgroup.center (↥B) = ⊥) :
    Subgroup.center (↥(A ⊔ B)) = ⊥ := by
  have hAX : A ≤ A ⊔ B := le_sup_left
  have hBX : B ≤ A ⊔ B := le_sup_right
  have hBA : B ≤ Subgroup.normalizer (A : Set Y) := by
    have hcent : B ≤ Subgroup.centralizer (A : Set Y) := by
      intro b hb
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      exact hcomm a ha b hb
    exact hcent.trans (Subgroup.centralizer_le_normalizer (A : Set Y))
  have hAn : (A.subgroupOf (A ⊔ B)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hAX).mpr
      (sup_le Subgroup.le_normalizer hBA)
  haveI := hAn
  rw [eq_bot_iff]
  intro z hz
  rw [Subgroup.mem_bot]
  have hzX : z ∈ A.subgroupOf (A ⊔ B) ⊔ B.subgroupOf (A ⊔ B) := by
    rw [← Subgroup.subgroupOf_sup hAX hBX, Subgroup.subgroupOf_self]
    exact Subgroup.mem_top z
  obtain ⟨a, ha, b, hb, hab⟩ := (Subgroup.mem_sup_of_normal_left).1 hzX
  have haA : (a : Y) ∈ A := Subgroup.mem_subgroupOf.mp ha
  have hbB : (b : Y) ∈ B := Subgroup.mem_subgroupOf.mp hb
  have hab' : (a : Y) * (b : Y) = (z : Y) := congrArg Subtype.val hab
  have ha1 : a = 1 := by
    have hmem : (⟨(a : Y), haA⟩ : ↥A) ∈ Subgroup.center ↥A := by
      rw [Subgroup.mem_center_iff]
      intro x
      apply Subtype.ext
      have hzx : (x : Y) * (z : Y) = (z : Y) * (x : Y) :=
        congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨(x : Y), hAX x.2⟩)
      rw [← hab'] at hzx
      have hbx : (b : Y) * (x : Y) = (x : Y) * (b : Y) :=
        (hcomm (x : Y) x.2 (b : Y) hbB).symm
      have key : (x : Y) * (a : Y) * (b : Y) = (a : Y) * (x : Y) * (b : Y) := by
        calc (x : Y) * (a : Y) * (b : Y) = (x : Y) * ((a : Y) * (b : Y)) := by group
          _ = ((a : Y) * (b : Y)) * (x : Y) := hzx
          _ = (a : Y) * ((b : Y) * (x : Y)) := by group
          _ = (a : Y) * ((x : Y) * (b : Y)) := by rw [hbx]
          _ = (a : Y) * (x : Y) * (b : Y) := by group
      exact mul_right_cancel key
    rw [hA, Subgroup.mem_bot] at hmem
    exact Subtype.ext (by simpa using congrArg Subtype.val hmem)
  have hb1 : b = 1 := by
    have hmem : (⟨(b : Y), hbB⟩ : ↥B) ∈ Subgroup.center ↥B := by
      rw [Subgroup.mem_center_iff]
      intro x
      apply Subtype.ext
      have hzx : (x : Y) * (z : Y) = (z : Y) * (x : Y) :=
        congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨(x : Y), hBX x.2⟩)
      rw [← hab'] at hzx
      have hax : (a : Y) * (x : Y) = (x : Y) * (a : Y) :=
        hcomm (a : Y) haA (x : Y) x.2
      have key : (a : Y) * ((x : Y) * (b : Y)) = (a : Y) * ((b : Y) * (x : Y)) := by
        calc (a : Y) * ((x : Y) * (b : Y)) = (a : Y) * (x : Y) * (b : Y) := by group
          _ = ((x : Y) * (a : Y)) * (b : Y) := by rw [hax]
          _ = (x : Y) * (a : Y) * (b : Y) := by group
          _ = (x : Y) * ((a : Y) * (b : Y)) := by group
          _ = ((a : Y) * (b : Y)) * (x : Y) := hzx
          _ = (a : Y) * ((b : Y) * (x : Y)) := by group
      exact mul_left_cancel key
    rw [hB, Subgroup.mem_bot] at hmem
    exact Subtype.ext (by simpa using congrArg Subtype.val hmem)
  rw [← hab, ha1, hb1, mul_one]

private theorem w183_comap_img {J E K : Subgroup G} (M : ModDataE J E)
    (hker : ∀ h : ↥J, M.ρ h = 1 ↔ (h : G) ∈ K) {A : Subgroup G} (hAJ : A ≤ J)
    (hKA : K ≤ A) : (M.img A).comap M.ρ = A.subgroupOf J := by
  have hkereq : M.ρ.ker = K.subgroupOf J := by
    ext h
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact hker h
  rw [show M.img A = (A.subgroupOf J).map M.ρ from rfl, Subgroup.comap_map_eq, hkereq]
  exact sup_eq_left.mpr (Subgroup.subgroupOf_mono J hKA)

theorem w183_components_commute {H K L₁ L₂ : Subgroup G} (h₁ : IsComponentModN K H L₁)
    (h₂ : IsComponentModN K H L₂) (hne : L₁ ≠ L₂) :
    ∀ a ∈ L₁, ∀ b ∈ L₂, a * b * a⁻¹ * b⁻¹ ∈ K := by
  classical
  haveI hKn : (K.subgroupOf H).Normal := h₁.1
  let q : ↥H →* ↥H ⧸ (K.subgroupOf H) := QuotientGroup.mk' (K.subgroupOf H)
  let A : Subgroup (↥H ⧸ (K.subgroupOf H)) := (L₁.subgroupOf H).map q
  let B : Subgroup (↥H ⧸ (K.subgroupOf H)) := (L₂.subgroupOf H).map q
  have hAcomp : IsComponentOf A ⊤ := by
    refine ⟨le_top, ?_, ?_⟩
    · have hsub : CFSG.Open.IsSubnormal L₁ H := h₁.2.2.2.1
      exact CFSG.Open.IsSubnormal.of_mathlib (hsub.subgroupOf.quotient)
    · exact w183_open_isQuasisimple_of_native
        (w183_isQuasisimple_image_quotient h₁.1 h₁.2.2.1 h₁.2.2.2.2)
  have hBcomp : IsComponentOf B ⊤ := by
    refine ⟨le_top, ?_, ?_⟩
    · have hsub : CFSG.Open.IsSubnormal L₂ H := h₂.2.2.2.1
      exact CFSG.Open.IsSubnormal.of_mathlib (hsub.subgroupOf.quotient)
    · exact w183_open_isQuasisimple_of_native
        (w183_isQuasisimple_image_quotient h₂.1 h₂.2.2.1 h₂.2.2.2.2)
  have hAneB : A ≠ B := by
    intro hAB
    apply hne
    have hqker : q.ker = K.subgroupOf H := by
      ext x
      rw [MonoidHom.mem_ker, show q = QuotientGroup.mk' (K.subgroupOf H) from rfl,
        QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    have hcomapA : A.comap q = L₁.subgroupOf H := by
      rw [show A = (L₁.subgroupOf H).map q from rfl, Subgroup.comap_map_eq, hqker]
      exact sup_eq_left.mpr (Subgroup.subgroupOf_mono H h₁.2.1)
    have hcomapB : B.comap q = L₂.subgroupOf H := by
      rw [show B = (L₂.subgroupOf H).map q from rfl, Subgroup.comap_map_eq, hqker]
      exact sup_eq_left.mpr (Subgroup.subgroupOf_mono H h₂.2.1)
    have hsub : L₁.subgroupOf H = L₂.subgroupOf H := by
      rw [← hcomapA, hAB, hcomapB]
    have hmap := congrArg (Subgroup.map H.subtype) hsub
    rw [Subgroup.map_subgroupOf_eq_of_le h₁.2.2.1,
      Subgroup.map_subgroupOf_eq_of_le h₂.2.2.1] at hmap
    exact hmap
  have hcomm : ⁅A, B⁆ = ⊥ :=
    CFSG.ComponentClassification.LocalComponents.commute_of_ne A B hAcomp hBcomp hAneB
  have hcent : A ≤ Subgroup.centralizer (B : Set (↥H ⧸ (K.subgroupOf H))) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
  intro a ha b hb
  have hqa : q ⟨a, h₁.2.2.1 ha⟩ ∈ A :=
    Subgroup.mem_map.mpr ⟨⟨a, h₁.2.2.1 ha⟩, Subgroup.mem_subgroupOf.mpr ha, rfl⟩
  have hqb : q ⟨b, h₂.2.2.1 hb⟩ ∈ B :=
    Subgroup.mem_map.mpr ⟨⟨b, h₂.2.2.1 hb⟩, Subgroup.mem_subgroupOf.mpr hb, rfl⟩
  have hba : q ⟨b, h₂.2.2.1 hb⟩ * q ⟨a, h₁.2.2.1 ha⟩ =
      q ⟨a, h₁.2.2.1 ha⟩ * q ⟨b, h₂.2.2.1 hb⟩ :=
    Subgroup.mem_centralizer_iff.mp (hcent hqa) _ hqb
  have hq1 : q (⟨a, h₁.2.2.1 ha⟩ * ⟨b, h₂.2.2.1 hb⟩ * ⟨a, h₁.2.2.1 ha⟩⁻¹ *
      ⟨b, h₂.2.2.1 hb⟩⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← hba]
    group
  have hmem : (⟨a, h₁.2.2.1 ha⟩ * ⟨b, h₂.2.2.1 hb⟩ * ⟨a, h₁.2.2.1 ha⟩⁻¹ *
      ⟨b, h₂.2.2.1 hb⟩⁻¹ : ↥H) ∈ K.subgroupOf H := by
    have := hq1
    rw [show q = QuotientGroup.mk' (K.subgroupOf H) from rfl] at this
    rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this
  simpa using Subgroup.mem_subgroupOf.mp hmem

namespace Ctx188

variable {D : Data G} {V₀ V H : Subgroup G} {i j : ℕ}

theorem br1_twoComp (x : Ctx188 D V₀ V H i j) (M : ModDataE H (eOmegaZ H D.T))
    (hK : kerMV V H ≤ Subgroup.centralizer (eOmegaZ H D.T : Set G)) {L : Subgroup G}
    (hLc : IsComponentModN (kerMV V H) H L) (hLT : L ⊔ D.T = H)
    (hQ : HasQuotShape L (kerMV V H : Set G)
      (fun X _ => IsSimpleGroup X ∧ ∃ a b : X, a * b ≠ b * a))
    {t : G} (htT : t ∈ D.T) (hne : conjSubgroup L t ≠ L)
    (hall : ∀ s ∈ D.T, conjSubgroup L s = L ∨ conjSubgroup L s = conjSubgroup L t) :
    Br2TwoComp (M.img H) (M.img D.T) (M.img L) (M.img (conjSubgroup L t)) := by
  classical
  let L₂ : Subgroup G := conjSubgroup L t
  have hDT : D.T ≤ H := x.hyp.hyp171.2.1
  have htH : t ∈ H := hDT htT
  have htHinv : t⁻¹ ∈ H := hDT (D.T.inv_mem htT)
  have hHnorm : H ≤ Subgroup.normalizer (kerMV V H : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (hLc.2.1.trans hLc.2.2.1)).mp hLc.1
  have hKmap : (kerMV V H).map (MulAut.conj t⁻¹).toMonoidHom = kerMV V H :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hHnorm (hDT (D.T.inv_mem htT)))
  have hHmap : H.map (MulAut.conj t⁻¹).toMonoidHom = H :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer htHinv)
  have hL₂c : IsComponentModN (kerMV V H) H L₂ :=
    w183_isComponentModN_map_mulEquiv (MulAut.conj t⁻¹) hKmap hHmap hLc
  have hL₂H : L₂ ≤ H := hL₂c.2.2.1
  have hkerρ : ∀ h : ↥H, M.ρ h = 1 ↔ (h : G) ∈ kerMV V H :=
    fun h => br1_ker_rho_iff x M hK h
  have hPinv : ∀ (X Y : Type) [Group X] [Group Y], X ≃* Y →
      (IsSimpleGroup X ∧ ∃ a b : X, a * b ≠ b * a) →
      (IsSimpleGroup Y ∧ ∃ a b : Y, a * b ≠ b * a) := by
    intro X Y _ _ e h
    refine ⟨(MulEquiv.isSimpleGroup_congr e).mp h.1, ?_⟩
    obtain ⟨a, b, hab⟩ := h.2
    exact ⟨e a, e b, fun hh => hab (e.injective (by simpa using hh))⟩
  have hbase := br1_shape_transport x M hK hLc.2.2.1 hPinv hQ
  have hsimple₁ : IsSimpleGroup ↥(M.img L) := hbase.1
  have hnonab₁ : ∃ a ∈ M.img L, ∃ b ∈ M.img L, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hbase.2
    exact ⟨(a : LGL 2 M.W), a.2, (b : LGL 2 M.W), b.2, fun h => hab (Subtype.ext h)⟩
  let y : LGL 2 M.W := M.ρ ⟨t⁻¹, htHinv⟩
  have hL₂img : M.img L₂ = cj y (M.img L) := by
    have h := M.img_conj (A := L) hLc.2.2.1 (j := ⟨t⁻¹, htHinv⟩)
    rw [inv_inv] at h
    exact h.symm
  have hsimple₂ : IsSimpleGroup ↥(M.img L₂) := by
    rw [hL₂img]
    exact w183_isSimpleGroup_cj hsimple₁ y
  have hnonab₂ : ∃ a ∈ M.img L₂, ∃ b ∈ M.img L₂, a * b ≠ b * a := by
    rw [hL₂img]
    exact w183_nonab_cj hnonab₁ y
  have hcommG := w183_components_commute hLc hL₂c (hne.symm)
  have hcommImg : ∀ a ∈ M.img L, ∀ b ∈ M.img L₂, a * b = b * a := by
    intro a ha b hb
    obtain ⟨j, hjL, rfl⟩ := M.mem_img.1 ha
    obtain ⟨k, hkL₂, rfl⟩ := M.mem_img.1 hb
    have hcommK : (j : G) * (k : G) * (j : G)⁻¹ * (k : G)⁻¹ ∈ kerMV V H :=
      hcommG (j : G) hjL (k : G) hkL₂
    have hker : M.ρ (j * k * j⁻¹ * k⁻¹) = 1 :=
      (hkerρ (j * k * j⁻¹ * k⁻¹)).2 (by simpa using hcommK)
    have h2 : M.ρ j * M.ρ k * (M.ρ j)⁻¹ * (M.ρ k)⁻¹ = 1 := by simpa using hker
    calc M.ρ j * M.ρ k
        = (M.ρ j * M.ρ k * (M.ρ j)⁻¹ * (M.ρ k)⁻¹) * ((M.ρ k) * (M.ρ j)) := by group
      _ = 1 * ((M.ρ k) * (M.ρ j)) := by rw [h2]
      _ = M.ρ k * M.ρ j := by group
  have hneImg : M.img L ≠ M.img L₂ := by
    intro heq
    apply hne
    have hcomapL := w183_comap_img M hkerρ hLc.2.2.1 hLc.2.1
    have hcomapL₂ := w183_comap_img M hkerρ hL₂c.2.2.1 hL₂c.2.1
    have hsub : L.subgroupOf H = L₂.subgroupOf H := by
      rw [← hcomapL, heq, hcomapL₂]
    have := congrArg (Subgroup.map H.subtype) hsub
    rw [Subgroup.map_subgroupOf_eq_of_le hLc.2.2.1,
      Subgroup.map_subgroupOf_eq_of_le hL₂H] at this
    exact this.symm
  have hYsup : M.img H = M.img L ⊔ M.img D.T := by
    rw [← M.img_sup hLc.2.2.1 hDT, hLT]
  have hswap : ∃ w ∈ M.img D.T, cj w (M.img L) = M.img L₂ :=
    ⟨y, M.mem_img.2 ⟨⟨t⁻¹, htHinv⟩, D.T.inv_mem htT, rfl⟩, hL₂img.symm⟩
  let P : LGL 2 M.W → Prop := fun z =>
    (cj z (M.img L) = M.img L ∧ cj z (M.img L₂) = M.img L₂) ∨
      (cj z (M.img L) = M.img L₂ ∧ cj z (M.img L₂) = M.img L)
  have hPmul : ∀ z w : LGL 2 M.W, P z → P w → P (z * w) := by
    intro z w hz hw
    rcases hz with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hw with ⟨k1, k2⟩ | ⟨k1, k2⟩
    · left
      exact ⟨by rw [← cj_cj z w (M.img L), k1, h1],
        by rw [← cj_cj z w (M.img L₂), k2, h2]⟩
    · right
      exact ⟨by rw [← cj_cj z w (M.img L), k1, h2],
        by rw [← cj_cj z w (M.img L₂), k2, h1]⟩
    · right
      exact ⟨by rw [← cj_cj z w (M.img L), k1, h1],
        by rw [← cj_cj z w (M.img L₂), k2, h2]⟩
    · left
      exact ⟨by rw [← cj_cj z w (M.img L), k1, h2],
        by rw [← cj_cj z w (M.img L₂), k2, h1]⟩
  have hPone : P 1 := by
    left
    exact ⟨cj_one _, cj_one _⟩
  have hPinv : ∀ z : LGL 2 M.W, P z → P z⁻¹ := by
    intro z hz
    rcases hz with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left
      refine ⟨?_, ?_⟩
      · have hh := congrArg (fun A => cj z⁻¹ A) h1
        rw [cj_self_inv z (M.img L)] at hh
        exact hh.symm
      · have hh := congrArg (fun A => cj z⁻¹ A) h2
        rw [cj_self_inv z (M.img L₂)] at hh
        exact hh.symm
    · right
      refine ⟨?_, ?_⟩
      · have hh := congrArg (fun A => cj z⁻¹ A) h2
        rw [cj_self_inv z (M.img L₂)] at hh
        exact hh.symm
      · have hh := congrArg (fun A => cj z⁻¹ A) h1
        rw [cj_self_inv z (M.img L)] at hh
        exact hh.symm
  let S : Subgroup (LGL 2 M.W) :=
    { carrier := {z | P z}
      mul_mem' := fun {a b} ha hb => hPmul a b ha hb
      one_mem' := hPone
      inv_mem' := fun {a} ha => hPinv a ha }
  have hL₁S : M.img L ≤ S := by
    intro a ha
    change P a
    left
    refine ⟨?_, ?_⟩
    · exact Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer ha)
    · rw [cj]
      refine Subgroup.mem_normalizer_iff_map_conj_eq.mp ?_
      have hcent₂ : a ∈ Subgroup.centralizer (M.img L₂ : Set (LGL 2 M.W)) := by
        rw [Subgroup.mem_centralizer_iff]
        intro l hl
        exact (hcommImg a ha l hl).symm
      exact Subgroup.centralizer_le_normalizer (M.img L₂ : Set (LGL 2 M.W)) hcent₂
  have hTS : M.img D.T ≤ S := by
    intro b hb
    obtain ⟨s, hs, rfl⟩ := M.mem_img.1 hb
    show (cj (M.ρ s) (M.img L) = M.img L ∧ cj (M.ρ s) (M.img L₂) = M.img L₂) ∨
      (cj (M.ρ s) (M.img L) = M.img L₂ ∧ cj (M.ρ s) (M.img L₂) = M.img L)
    have hcjb_inj : Function.Injective (fun C : Subgroup (LGL 2 M.W) => cj (M.ρ s) C) := by
      intro C D hCD
      have hthis := congrArg (fun C : Subgroup (LGL 2 M.W) => cj (M.ρ s)⁻¹ C) hCD
      rw [cj_self_inv (M.ρ s) C, cj_self_inv (M.ρ s) D] at hthis
      exact hthis
    have hbL : cj (M.ρ s) (M.img L) = M.img (conjSubgroup L (s : G)⁻¹) :=
      M.img_conj (A := L) hLc.2.2.1 s
    have hbL₂ : cj (M.ρ s) (M.img L₂) = M.img (conjSubgroup L (t * (s : G)⁻¹)) := by
      have h := M.img_conj (A := conjSubgroup L t) hL₂H s
      rw [conjSubgroup_conjSubgroup] at h
      exact h
    have h1 : M.img (conjSubgroup L (s : G)⁻¹) = M.img L ∨
        M.img (conjSubgroup L (s : G)⁻¹) = M.img L₂ := by
      rcases hall (s : G)⁻¹ (D.T.inv_mem hs) with h | h
      · left; rw [h]
      · right; rw [h]
    have h2 : M.img (conjSubgroup L (t * (s : G)⁻¹)) = M.img L ∨
        M.img (conjSubgroup L (t * (s : G)⁻¹)) = M.img L₂ := by
      rcases hall (t * (s : G)⁻¹) (D.T.mul_mem htT (D.T.inv_mem hs)) with h | h
      · left; rw [h]
      · right; rw [h]
    rw [hbL, hbL₂]
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
    · exfalso
      refine hneImg (hcjb_inj ?_)
      change cj (M.ρ s) (M.img L) = cj (M.ρ s) (M.img L₂)
      rw [hbL, hbL₂]
      exact h1.trans h2.symm
    · exact Or.inl ⟨h1, h2⟩
    · exact Or.inr ⟨h1, h2⟩
    · exfalso
      refine hneImg (hcjb_inj ?_)
      change cj (M.ρ s) (M.img L) = cj (M.ρ s) (M.img L₂)
      rw [hbL, hbL₂]
      exact h1.trans h2.symm
  have hperm : ∀ z ∈ M.img H, (cj z (M.img L) = M.img L ∧ cj z (M.img L₂) = M.img L₂) ∨
      (cj z (M.img L) = M.img L₂ ∧ cj z (M.img L₂) = M.img L) := by
    intro z hz
    have hz' : z ∈ M.img L ⊔ M.img D.T := hYsup ▸ hz
    change P z
    exact sup_le hL₁S hTS hz'
  have hABY : M.img L ⊔ M.img L₂ ≤ M.img H :=
    sup_le (M.img_mono hLc.2.2.1) (M.img_mono hL₂H)
  have hsupfix : ∀ z ∈ M.img H, cj z (M.img L ⊔ M.img L₂) = M.img L ⊔ M.img L₂ := by
    intro z hz
    rcases hperm z hz with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [cj, Subgroup.map_sup]
      change cj z (M.img L) ⊔ cj z (M.img L₂) = M.img L ⊔ M.img L₂
      rw [h1, h2]
    · rw [cj, Subgroup.map_sup]
      change cj z (M.img L) ⊔ cj z (M.img L₂) = M.img L ⊔ M.img L₂
      rw [h1, h2, sup_comm]
  have hXn : ((M.img L ⊔ M.img L₂).subgroupOf (M.img H)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hABY).mpr fun z hz =>
      Subgroup.mem_normalizer_iff_map_conj_eq.mpr (by simpa [cj] using hsupfix z hz)
  have hXT' : (M.img L ⊔ M.img L₂) ⊔ M.img D.T = M.img H := by
    refine le_antisymm (sup_le hABY (M.img_mono hDT)) ?_
    calc M.img H = M.img L ⊔ M.img D.T := hYsup
      _ ≤ (M.img L ⊔ M.img L₂) ⊔ M.img D.T :=
          sup_le (le_sup_of_le_left le_sup_left) le_sup_right
  have hXT : ((M.img L ⊔ M.img L₂).subgroupOf (M.img H)) ⊔
      ((M.img D.T).subgroupOf (M.img H)) = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hABY (M.img_mono hDT), hXT', Subgroup.subgroupOf_self]
  have hT2 : IsPGroup 2 ↥((M.img D.T).subgroupOf (M.img H)) :=
    (M.isPGroup_img x.hyp.isSylowIn_T.isPGroup).of_equiv
      (Subgroup.subgroupOfEquivOfLe (M.img_mono hDT)).symm
  have hcore : CFSG.pCore 2 ↥(M.img H) = ⊥ :=
    Subgroup.map_injective (M.img H).subtype_injective (by
      show pCoreOf 2 (M.img H) = (⊥ : Subgroup ↥(M.img H)).map (M.img H).subtype
      rw [Subgroup.map_bot, pCoreOf_img_eq_bot x M])
  have hO2 : ∀ N : Subgroup ↥(M.img H), N.Normal → IsPGroup 2 ↥N → N = ⊥ := by
    intro N hNn hNp
    have hle : N ≤ CFSG.pCore 2 ↥(M.img H) := by
      rw [CFSG.pCore_eq_iSup]
      exact le_iSup_of_le N (le_iSup_of_le hNn (le_iSup_of_le hNp le_rfl))
    rw [hcore] at hle
    exact le_bot_iff.mp hle
  have hcenterL : Subgroup.center ↥(M.img L) = ⊥ := by
    refine TauCeti.IsSimpleGroup.center_eq_bot_of_not_isMulCommutative ?_
    intro hc
    obtain ⟨a, ha, b, hb, hab⟩ := hnonab₁
    exact hab (by simpa using congrArg Subtype.val (hc.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩))
  have hcenterL₂ : Subgroup.center ↥(M.img L₂) = ⊥ := by
    refine TauCeti.IsSimpleGroup.center_eq_bot_of_not_isMulCommutative ?_
    intro hc
    obtain ⟨a, ha, b, hb, hab⟩ := hnonab₂
    exact hab (by simpa using congrArg Subtype.val (hc.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩))
  have hcommSub : ∀ a ∈ (M.img L).subgroupOf (M.img H),
      ∀ b ∈ (M.img L₂).subgroupOf (M.img H), a * b = b * a := by
    intro a ha b hb
    apply Subtype.ext
    exact hcommImg a (Subgroup.mem_subgroupOf.mp ha) b (Subgroup.mem_subgroupOf.mp hb)
  have hcenterA : Subgroup.center ↥((M.img L).subgroupOf (M.img H)) = ⊥ :=
    w183_center_eq_bot_of_mulEquiv
      (Subgroup.subgroupOfEquivOfLe (M.img_mono hLc.2.2.1)) hcenterL
  have hcenterB : Subgroup.center ↥((M.img L₂).subgroupOf (M.img H)) = ⊥ :=
    w183_center_eq_bot_of_mulEquiv
      (Subgroup.subgroupOfEquivOfLe (M.img_mono hL₂H)) hcenterL₂
  have hZ : Subgroup.center ↥((M.img L ⊔ M.img L₂).subgroupOf (M.img H)) = ⊥ := by
    have h := w183_center_sup_eq_bot hcommSub hcenterA hcenterB
    rwa [← Subgroup.subgroupOf_sup (M.img_mono hLc.2.2.1) (M.img_mono hL₂H)] at h
  have hcent : ∀ z ∈ M.img H, (∀ l ∈ M.img L, z * l = l * z) →
      (∀ l ∈ M.img L₂, z * l = l * z) → z = 1 := by
    intro z hz hzL hzL₂
    haveI := hXn
    have hcentbot := w183_centralizer_eq_bot hZ hXT hT2 hO2
    have hzc : (⟨z, hz⟩ : ↥(M.img H)) ∈ Subgroup.centralizer
        (((M.img L ⊔ M.img L₂).subgroupOf (M.img H) : Subgroup ↥(M.img H)) :
          Set ↥(M.img H)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro u hu
      have humem : (u : LGL 2 M.W) ∈ M.img L ⊔ M.img L₂ := Subgroup.mem_subgroupOf.mp hu
      apply Subtype.ext
      have key : (u : LGL 2 M.W) * z = z * (u : LGL 2 M.W) := by
        have humem' : (u : LGL 2 M.W) ∈ Subgroup.closure
            ((M.img L : Set (LGL 2 M.W)) ∪ (M.img L₂ : Set (LGL 2 M.W))) := by
          rwa [← Subgroup.sup_eq_closure]
        refine Subgroup.closure_induction (p := fun w _ => w * z = z * w) ?_ ?_ ?_ ?_ humem'
        · rintro w (hw | hw)
          · exact (hzL w hw).symm
          · exact (hzL₂ w hw).symm
        · rw [one_mul, mul_one]
        · rintro x y _ _ hx hy
          rw [mul_assoc, hy, ← mul_assoc, hx, mul_assoc]
        · rintro x _ hx
          calc x⁻¹ * z = x⁻¹ * (z * x) * x⁻¹ := by group
            _ = x⁻¹ * (x * z) * x⁻¹ := by rw [← hx]
            _ = z * x⁻¹ := by group
      exact key
    have h1 : (⟨z, hz⟩ : ↥(M.img H)) = 1 := by
      rw [← Subgroup.mem_bot, ← hcentbot]
      exact hzc
    exact congrArg Subtype.val h1
  have hgen : ∀ z ∈ M.img H, ∃ l ∈ M.img L ⊔ M.img L₂, ∃ w ∈ M.img D.T, z = l * w := by
    intro z hz
    haveI := hXn
    have hzX : (⟨z, hz⟩ : ↥(M.img H)) ∈
        ((M.img L ⊔ M.img L₂).subgroupOf (M.img H)) ⊔
          ((M.img D.T).subgroupOf (M.img H)) := by
      rw [hXT]
      exact Subgroup.mem_top _
    obtain ⟨l, hl, w, hw, hlw⟩ := (Subgroup.mem_sup_of_normal_left).1 hzX
    exact ⟨(l : LGL 2 M.W), Subgroup.mem_subgroupOf.mp hl, (w : LGL 2 M.W),
      Subgroup.mem_subgroupOf.mp hw, (congrArg Subtype.val hlw).symm⟩
  exact ⟨M.img_mono hLc.2.2.1, M.img_mono hL₂H, hsimple₁, hsimple₂, hnonab₁, hnonab₂,
    hcommImg, hneImg, hperm, hswap, hcent, hgen⟩

end Ctx188

end CFSG.LocalAnalysis.WeakClosure81

end
