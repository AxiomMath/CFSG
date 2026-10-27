module

public import CFSG.Quasithin.EmptyFaithful.S146D2
public import CFSG.Quasithin.Background.F918C8
public import CFSG.Quasithin.Background.F918C9
public import CFSG.Quasithin.EmptyFaithful.F918C7

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
open scoped Pointwise commutatorElement

section Center

variable {G : Type} [Group G] [Finite G]

theorem hZ_of_cComp_le {H K₀ : Subgroup G} (hodd : OddCoreModTwoTrivial H) (hK₀H : K₀ ≤ H)
    (hle : ∀ L ∈ cComp H, L ≤ K₀) :
    ∀ x ∈ K₀, (∀ k' ∈ K₀, x * k' * x⁻¹ * k'⁻¹ ∈ pCoreOf 2 H) → x ∈ pCoreOf 2 H := by
  intro x hx hcomm
  have hxH : x ∈ H := hK₀H hx
  have h1 : QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨x, hxH⟩ = 1 := by
    refine eq_one_of_commute_modO2Image hodd fun L hL r hr => ?_
    obtain ⟨z, hz, rfl⟩ := hr
    have hzL : (z : G) ∈ L := Subgroup.mem_subgroupOf.mp hz
    have hc := hcomm _ (hle L hL hzL)
    have hc' : (⟨x, hxH⟩ * z * ⟨x, hxH⟩⁻¹ * z⁻¹ : ↥H) ∈ CFSG.pCore 2 ↥H := by
      rw [← subgroupOf_pCoreOf, Subgroup.mem_subgroupOf]
      exact hc
    have h2 : QuotientGroup.mk' (CFSG.pCore 2 ↥H) (⟨x, hxH⟩ * z * ⟨x, hxH⟩⁻¹ * z⁻¹) = 1 :=
      (QuotientGroup.eq_one_iff _).2 hc'
    simp only [map_mul, map_inv] at h2
    exact mul_inv_eq_one.mp (mul_inv_eq_one.mp (by simpa [mul_assoc] using h2))
  have h3 : (⟨x, hxH⟩ : ↥H) ∈ CFSG.pCore 2 ↥H := (QuotientGroup.eq_one_iff _).1 h1
  rw [← subgroupOf_pCoreOf, Subgroup.mem_subgroupOf] at h3
  exact h3

end Center

section Irr

attribute [local instance] commGroupOfFact

variable {G : Type} [Group G] [Finite G] {T V L V₁ Vp H K I : Subgroup G}

theorem le_normalizer_of_isInv_aut [Fact (IsElemAbelian 2 (tildeOf V₁ (conjClosure I H)))]
    (h : HypF918 T V L V₁ Vp H K) (hIU : I ≤ conjClosure Vp H) {J X : Subgroup G} (hXH : X ≤ H)
    (hV₁J : V₁ ≤ J) (hJ : J ≤ conjClosure I H)
    (hinv : XMod.IsInv ↥(autIH V₁ I H X) (subM V₁ (conjClosure I H) J)) :
    X ≤ Subgroup.normalizer (J : Set G) := by
  intro k hk
  have hIHN := h.conjClosure_le_normalizer_V₁ hIU
  have hIH := le_normalizer_conjClosure I H
  have hkH : k ∈ H := hXH hk
  let φ := actH h.H_le_normalizer_V₁ hIH
  have hmem : ∀ x (hx : x ∈ X), φ ⟨x, hXH hx⟩ ∈ autIH V₁ I H X := by
    intro x hx
    rw [autIH_eq_map h hXH]
    exact ⟨⟨x, hXH hx⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
  have hstab : φ ⟨k, hkH⟩ ∈ stabSub (subM V₁ (conjClosure I H) J) := by
    intro u
    constructor
    · intro hu
      have := hinv ⟨(φ ⟨k, hkH⟩)⁻¹, inv_mem (hmem k hk)⟩ _ hu
      simpa using this
    · intro hu
      exact hinv ⟨φ ⟨k, hkH⟩, hmem k hk⟩ u hu
  exact (actH_mem_stabSub_subM_iff h.H_le_normalizer_V₁ hIHN hIH hV₁J hJ ⟨k, hkH⟩).mp hstab

theorem isIrredOnSection_of_isIrr [Fact (IsElemAbelian 2 (tildeOf V₁ (conjClosure I H)))]
    (h : HypF918 T V L V₁ Vp H K) (hIU : I ≤ conjClosure Vp H) {U₁ : Subgroup G} (hV₁U : V₁ ≤ U₁)
    (hUI : U₁ ≤ conjClosure I H)
    (hirr : XMod.IsIrr ↥(autIH V₁ I H K) (subM V₁ (conjClosure I H) U₁)) :
    IsIrredOnSection K U₁ V₁ ∧ V₁ ≠ U₁ := by
  have hIHN := h.conjClosure_le_normalizer_V₁ hIU
  have hIH := le_normalizer_conjClosure I H
  have hKH : K ≤ H := le_of_mem_cComp h.K_cComp
  have hKU : K ≤ Subgroup.normalizer (U₁ : Set G) :=
    le_normalizer_of_isInv_aut h hIU hKH hV₁U hUI hirr.1
  have hV₁N : K ≤ Subgroup.normalizer (V₁ : Set G) := hKH.trans h.H_le_normalizer_V₁
  have hV₁bot : subM V₁ (conjClosure I H) V₁ = ⊥ := by
    unfold subM
    rw [tildeOf_eq_bot_of_le le_rfl, Subgroup.bot_subgroupOf]
  have hsec : XMod.IsIrrSec ↥(autIH V₁ I H K) (subM V₁ (conjClosure I H) V₁)
      (subM V₁ (conjClosure I H) U₁) := by
    rw [hV₁bot]
    exact hirr.2
  have hne : V₁ ≠ U₁ := by
    intro heq
    have h1 : subM V₁ (conjClosure I H) V₁ = subM V₁ (conjClosure I H) U₁ :=
      congrArg (subM V₁ (conjClosure I H)) heq
    have := hsec.1
    rw [h1] at this
    exact lt_irrefl _ this
  refine ⟨⟨lt_of_le_of_ne hV₁U hne, hKU, hV₁N, fun J hV₁J hJU hKJ => ?_⟩, hne⟩
  exact eq_or_eq_of_isIrrSec h.H_le_normalizer_V₁ hIHN hIH hKH le_rfl hV₁J hJU hUI hKJ hsec

theorem actH_modMk_mul_inv [Fact (IsElemAbelian 2 (tildeOf V₁ (conjClosure I H)))]
    (h : HypF918 T V L V₁ Vp H K) (hIU : I ≤ conjClosure Vp H) (x : ↥H) {a : G}
    (ha : a ∈ conjClosure I H)
    (hx : (x : G) * a * (x : G)⁻¹ * a⁻¹ ∈ conjClosure I H) :
    actH h.H_le_normalizer_V₁ (le_normalizer_conjClosure I H) x
        (modMk (h.conjClosure_le_normalizer_V₁ hIU) a ha) *
      (modMk (h.conjClosure_le_normalizer_V₁ hIU) a ha)⁻¹ =
    modMk (h.conjClosure_le_normalizer_V₁ hIU) ((x : G) * a * (x : G)⁻¹ * a⁻¹) hx := by
  have hIHN := h.conjClosure_le_normalizer_V₁ hIU
  have hxa : (x : G) * a * (x : G)⁻¹ ∈ conjClosure I H :=
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure I H x.2) a).mp ha
  rw [actH_modMk h.H_le_normalizer_V₁ hIHN (le_normalizer_conjClosure I H) x ha,
    ← modMk_inv hIHN ha, ← modMk_mul hIHN hxa ((conjClosure I H).inv_mem ha)]

theorem comm_sup_eq_of_commV [Fact (IsElemAbelian 2 (tildeOf V₁ (conjClosure I H)))]
    (h : HypF918 T V L V₁ Vp H K) (hIU : I ≤ conjClosure Vp H) {U₁ U₂ : Subgroup G}
    (hV₁U₁ : V₁ ≤ U₁) (hU₁ : U₁ ≤ conjClosure I H) (hU₂ : U₂ ≤ conjClosure I H)
    (hsum : commV (autIH V₁ I H K) =
      subM V₁ (conjClosure I H) U₁ ⊔ subM V₁ (conjClosure I H) U₂) :
    ⁅conjClosure I H, K⁆ ⊔ V₁ = U₁ ⊔ U₂ := by
  have hIHN := h.conjClosure_le_normalizer_V₁ hIU
  have hIH := le_normalizer_conjClosure I H
  have hKH : K ≤ H := le_of_mem_cComp h.K_cComp
  have hsupN : subM V₁ (conjClosure I H) (U₁ ⊔ U₂) = commV (autIH V₁ I H K) := by
    rw [hsum, subM_sup hIHN hU₁ hU₂]
  have hV₁UU : V₁ ≤ U₁ ⊔ U₂ := hV₁U₁.trans le_sup_left
  have hUUI : U₁ ⊔ U₂ ≤ conjClosure I H := sup_le hU₁ hU₂
  have hmemc : ∀ a ∈ conjClosure I H, ∀ k ∈ K, k * a * k⁻¹ * a⁻¹ ∈ conjClosure I H := by
    intro a ha k hk
    have := (Subgroup.mem_normalizer_iff.mp (hIH (hKH hk)) a).mp ha
    exact (conjClosure I H).mul_mem this ((conjClosure I H).inv_mem ha)
  have hcomm_le : ⁅conjClosure I H, K⁆ ≤ conjClosure I H := by
    refine Subgroup.commutator_le.mpr fun a ha k hk => ?_
    have h1 := hmemc a ha k hk
    have e : ⁅a, k⁆ = (k * a * k⁻¹ * a⁻¹)⁻¹ := by simp only [commutatorElement_def]; group
    rw [e]
    exact (conjClosure I H).inv_mem h1
  have hgen : ∀ a (ha : a ∈ conjClosure I H) (k : G) (hk : k ∈ K),
      actH h.H_le_normalizer_V₁ hIH ⟨k, hKH hk⟩ (modMk hIHN a ha) * (modMk hIHN a ha)⁻¹ ∈
        commV (autIH V₁ I H K) := by
    intro a ha k hk
    refine Subgroup.subset_closure ⟨actH h.H_le_normalizer_V₁ hIH ⟨k, hKH hk⟩, ?_, _, rfl⟩
    rw [autIH_eq_map h hKH]
    exact ⟨⟨k, hKH hk⟩, Subgroup.mem_subgroupOf.mpr hk, rfl⟩
  have hE1 : ⁅conjClosure I H, K⁆ ≤ U₁ ⊔ U₂ := by
    refine Subgroup.commutator_le.mpr fun a ha k hk => ?_
    have h1 := hmemc a ha k hk
    have h2 := hgen a ha k hk
    rw [actH_modMk_mul_inv h hIU ⟨k, hKH hk⟩ ha h1, ← hsupN] at h2
    have h3 : k * a * k⁻¹ * a⁻¹ ∈ U₁ ⊔ U₂ := (modMk_mem_subM_iff hIHN hV₁UU h1).mp h2
    have e : ⁅a, k⁆ = (k * a * k⁻¹ * a⁻¹)⁻¹ := by simp only [commutatorElement_def]; group
    rw [e]
    exact (U₁ ⊔ U₂).inv_mem h3
  have hE2 : U₁ ⊔ U₂ ≤ ⁅conjClosure I H, K⁆ ⊔ V₁ := by
    have hYI : ⁅conjClosure I H, K⁆ ⊔ V₁ ≤ conjClosure I H :=
      sup_le hcomm_le (hV₁U₁.trans hU₁)
    refine (subM_le_iff hIHN hV₁UU le_sup_right hUUI).1 ?_
    rw [hsupN, commV, Subgroup.closure_le]
    rintro _ ⟨x, hxL, w, rfl⟩
    rw [autIH_eq_map h hKH] at hxL
    obtain ⟨g, hg, rfl⟩ := hxL
    obtain ⟨a, haIH, hau⟩ := exists_mk_of_mem_tilde w
    have hw : w = modMk hIHN (a : G) haIH := Subtype.ext hau.symm
    subst hw
    have hgK : (g : G) ∈ K := Subgroup.mem_subgroupOf.mp hg
    have h1 := hmemc (a : G) haIH (g : G) hgK
    rw [SetLike.mem_coe, actH_modMk_mul_inv h hIU g haIH h1,
      modMk_mem_subM_iff hIHN le_sup_right h1]
    have h2 : ⁅(g : G), (a : G)⁆ ∈ ⁅K, conjClosure I H⁆ := Subgroup.commutator_mem_commutator hgK haIH
    rw [Subgroup.commutator_comm] at h2
    simp only [commutatorElement_def] at h2
    exact Subgroup.mem_sup_left h2
  exact le_antisymm (sup_le (hE1.trans le_rfl) (hV₁UU)) hE2

end Irr

section Three

variable {G : Type} [Group G] {A Q V₁ : Subgroup G}

theorem le_normalizer_of_comm_le (hV₁Q : V₁ ≤ Q) (hQA : Q ≤ A)
    (hA : ∀ x ∈ A, ∀ q ∈ A, x * q * x⁻¹ * q⁻¹ ∈ V₁) : A ≤ Subgroup.normalizer (Q : Set G) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro q
  constructor
  · intro hq
    have h1 : x * q * x⁻¹ * q⁻¹ ∈ Q := hV₁Q (hA x hx q (hQA hq))
    have e : x * q * x⁻¹ = (x * q * x⁻¹ * q⁻¹) * q := by group
    rw [e]
    exact Q.mul_mem h1 hq
  · intro hq
    have h1 := hA x⁻¹ (A.inv_mem hx) _ (hQA hq)
    have e : q = (x⁻¹ * (x * q * x⁻¹) * x⁻¹⁻¹ * (x * q * x⁻¹)⁻¹) * (x * q * x⁻¹) := by group
    rw [e]
    exact Q.mul_mem (hV₁Q h1) hq

end Three

section ThreeH7

attribute [local instance] commGroupOfFact

variable {G : Type} [Group G] [Finite G] {T V L V₁ Vp H K I : Subgroup G}

omit [Finite G] in
theorem commutator_le_normalizer {A K V₁ : Subgroup G} (hA : A ≤ Subgroup.normalizer (V₁ : Set G))
    (hK : K ≤ Subgroup.normalizer (V₁ : Set G)) :
    ⁅A, K⁆ ≤ Subgroup.normalizer (V₁ : Set G) := by
  refine Subgroup.commutator_le.mpr fun a ha k hk => ?_
  rw [commutatorElement_def]
  exact (Subgroup.normalizer (V₁ : Set G)).mul_mem
    ((Subgroup.normalizer (V₁ : Set G)).mul_mem
      ((Subgroup.normalizer (V₁ : Set G)).mul_mem (hA ha) (hK hk)) ((Subgroup.normalizer _).inv_mem (hA ha)))
    ((Subgroup.normalizer _).inv_mem (hK hk))

omit [Finite G] in
theorem commutator_le_conjClosure (h : HypF918 T V L V₁ Vp H K) {I : Subgroup G} :
    ⁅conjClosure I H, K⁆ ≤ conjClosure I H := by
  have hKH : K ≤ H := le_of_mem_cComp h.K_cComp
  refine Subgroup.commutator_le.mpr fun a ha k hk => ?_
  have h1 : k * a * k⁻¹ ∈ conjClosure I H :=
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure I H (hKH hk)) a).mp ha
  have e : ⁅a, k⁆ = a * (k * a⁻¹ * k⁻¹) := by simp only [commutatorElement_def]; group
  have h2 : k * a⁻¹ * k⁻¹ ∈ conjClosure I H :=
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure I H (hKH hk)) a⁻¹).mp
      ((conjClosure I H).inv_mem ha)
  rw [e]
  exact (conjClosure I H).mul_mem ha h2

omit [Finite G] in
theorem le_normalizer_comm_sup (h : HypF918 T V L V₁ Vp H K) {I : Subgroup G} :
    K ≤ Subgroup.normalizer ((⁅conjClosure I H, K⁆ ⊔ V₁ : Subgroup G) : Set G) := by
  intro k hk
  have hKH : K ≤ H := le_of_mem_cComp h.K_cComp
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  have h1 := Subgroup.mem_normalizer_iff_map_conj_eq.mp (le_normalizer_conjClosure I H (hKH hk))
  have h2 := Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hk)
  have h3 := Subgroup.mem_normalizer_iff_map_conj_eq.mp (h.H_le_normalizer_V₁ (hKH hk))
  rw [Subgroup.map_sup, Subgroup.map_commutator, h1, h2, h3]

theorem commutator_le_of_h7 (h : HypF918 T V L V₁ Vp H K) (hIU : I ≤ conjClosure Vp H)
    (hV₁I : V₁ ≤ I)
    (h7 : tildeOf V₁ ⁅conjClosure Vp H, conjClosure K T⁆ = tildeOf V₁ (conjClosure I H)) :
    ⁅conjClosure Vp H, K⁆ ≤ ⁅conjClosure I H, K⁆ ⊔ V₁ := by
  have hKH : K ≤ H := le_of_mem_cComp h.K_cComp
  have hUUN : conjClosure Vp H ≤ Subgroup.normalizer (V₁ : Set G) :=
    h.conjClosure_le_normalizer_V₁ (le_conjClosure Vp H)
  have hV₁IH : V₁ ≤ conjClosure I H := hV₁I.trans (le_conjClosure I H)
  have hfa := factElem h (le_conjClosure Vp H)
  have hUUcomm : ∀ x ∈ conjClosure Vp H, ∀ q ∈ conjClosure Vp H, x * q * x⁻¹ * q⁻¹ ∈ V₁ := by
    intro x hx q hq
    have hxm := secMk_mem_secImg (A := Subgroup.normalizer (V₁ : Set G)) (B := V₁)
      (X := conjClosure Vp H) (x := ⟨x, hUUN hx⟩) hx
    have hqm := secMk_mem_secImg (A := Subgroup.normalizer (V₁ : Set G)) (B := V₁)
      (X := conjClosure Vp H) (x := ⟨q, hUUN hq⟩) hq
    have hc := isElemAbelian_comm hfa.out hxm hqm
    exact commutator_mem_of_secMk_commute (A := Subgroup.normalizer (V₁ : Set G)) (B := V₁)
      (x := ⟨x, hUUN hx⟩) (y := ⟨q, hUUN hq⟩) hc
  have hUK₀ : ⁅conjClosure Vp H, conjClosure K T⁆ ≤ conjClosure I H := by
    intro x hx
    have hxN : x ∈ Subgroup.normalizer (V₁ : Set G) :=
      commutator_le_normalizer hUUN (h.K₀_le_H.trans h.H_le_normalizer_V₁) hx
    have h1 : secMk (Subgroup.normalizer (V₁ : Set G)) V₁ ⟨x, hxN⟩ ∈
        tildeOf V₁ ⁅conjClosure Vp H, conjClosure K T⁆ :=
      secMk_mem_secImg (A := Subgroup.normalizer (V₁ : Set G)) (B := V₁)
        (X := ⁅conjClosure Vp H, conjClosure K T⁆) (x := ⟨x, hxN⟩) hx
    rw [h7] at h1
    exact (secMk_mem_secImg_iff hV₁IH).mp h1
  have hUK : ⁅conjClosure Vp H, K⁆ ≤ conjClosure I H :=
    (Subgroup.commutator_mono le_rfl (le_conjClosure K T)).trans hUK₀
  have hIHUU : conjClosure I H ≤ conjClosure Vp H := by
    refine conjClosure_le fun s hs z hz => ?_
    exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure Vp H hs) z).mp (hIU hz)
  have hcIH : ⁅conjClosure I H, K⁆ ≤ conjClosure I H := commutator_le_conjClosure h
  have hQU : ⁅conjClosure I H, K⁆ ⊔ V₁ ≤ conjClosure Vp H :=
    sup_le (hcIH.trans hIHUU) (hV₁IH.trans hIHUU)
  have hA := le_normalizer_of_comm_le (V₁ := V₁) (Q := ⁅conjClosure I H, K⁆ ⊔ V₁)
    (A := conjClosure Vp H) le_sup_right hQU hUUcomm
  have hP := le_normalizer_comm_sup (I := I) h
  have hperf : ⁅K, K⁆ = K := perfect_of_mem_cComp h.K_cComp
  have hh : ⁅⁅K, conjClosure Vp H⁆, K⁆ ≤ ⁅conjClosure I H, K⁆ ⊔ V₁ := by
    rw [Subgroup.commutator_comm K (conjClosure Vp H)]
    exact (Subgroup.commutator_mono hUK le_rfl).trans le_sup_left
  exact commutator_le_of_commutator_commutator_le hA hP hperf hh

end ThreeH7

end CFSG.Quasithin
