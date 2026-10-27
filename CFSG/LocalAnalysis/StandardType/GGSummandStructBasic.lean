module

public import CFSG.LocalAnalysis.StandardType.GGSixAutKFlatRootCent
public import Mathlib.Algebra.Group.Commutator

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.Sec21

open scoped commutatorElement

section PCoreAux

variable {G : Type} [Group G]

theorem pCoreOf_le' (p : ℕ) (H : Subgroup G) : pCoreOf p H ≤ H := by
  intro x hx
  obtain ⟨y, _, rfl⟩ := Subgroup.mem_map.mp hx
  exact y.2

theorem isPGroup_pCoreOf' (p : ℕ) (H : Subgroup G) : IsPGroup p (pCoreOf p H) := by
  rw [pCoreOf]
  exact CFSG.pCore_isPGroup.map _

theorem conj_mem_pCoreOf' (p : ℕ) {H : Subgroup G} {k o : G} (hk : k ∈ H)
    (ho : o ∈ pCoreOf p H) : k * o * k⁻¹ ∈ pCoreOf p H := by
  rw [pCoreOf] at ho ⊢
  obtain ⟨o', ho', rfl⟩ := ho
  exact ⟨⟨k, hk⟩ * o' * ⟨k, hk⟩⁻¹, CFSG.pCore_normal.conj_mem o' ho' _, rfl⟩

theorem le_pCoreOf_of_normalized (p : ℕ) {Q H : Subgroup G} (hQH : Q ≤ H) (hQp : IsPGroup p Q)
    (hconj : ∀ h ∈ H, ∀ q ∈ Q, h * q * h⁻¹ ∈ Q) : Q ≤ pCoreOf p H := by
  have hnormal : (Q.subgroupOf H).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hQH]
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro n
    constructor
    · exact hconj x hx n
    · intro hn
      have h := hconj x⁻¹ (H.inv_mem hx) (x * n * x⁻¹) hn
      rwa [show x⁻¹ * (x * n * x⁻¹) * x⁻¹⁻¹ = n from by group] at h
  have hsubp : IsPGroup p ↥(Q.subgroupOf H) :=
    hQp.of_equiv (Subgroup.subgroupOfEquivOfLe hQH).symm
  have hcore : Q.subgroupOf H ≤ CFSG.pCore p ↥H := by
    rw [CFSG.pCore_eq_iSup]
    exact le_iSup_of_le (Q.subgroupOf H) (le_iSup_of_le hnormal (le_iSup_of_le hsubp le_rfl))
  rw [← Subgroup.map_subgroupOf_eq_of_le hQH]
  exact Subgroup.map_mono hcore

theorem pCoreOf_le_of_normal (p : ℕ) {A M : Subgroup G} (hle : A ≤ M)
    (hN : (A.subgroupOf M).Normal) : pCoreOf p A ≤ pCoreOf p M := by
  refine le_pCoreOf_of_normalized p ((pCoreOf_le' p A).trans hle) (isPGroup_pCoreOf' p A) ?_
  intro h hh q hq
  have hnorm : h ∈ Subgroup.normalizer (A : Set G) := ggMem_normalizer_of_normal hle hN hh
  have hQ : (pCoreOf p A).map (MulAut.conj h).toMonoidHom ≤ pCoreOf p A := by
    refine le_pCoreOf_of_normalized p ?_ ((isPGroup_pCoreOf' p A).map _) ?_
    · rintro _ ⟨y, hy, rfl⟩
      exact (Subgroup.mem_normalizer_iff.mp hnorm y).mp (pCoreOf_le' p A hy)
    · rintro a ha _ ⟨y, hy, rfl⟩
      have hmem : h⁻¹ * a * h ∈ A := by
        have := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (A : Set G)).inv_mem hnorm)
          a).mp ha
        simpa [mul_assoc] using this
      refine ⟨(h⁻¹ * a * h) * y * (h⁻¹ * a * h)⁻¹, conj_mem_pCoreOf' p hmem hy, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
  exact hQ ⟨q, hq, rfl⟩

theorem pCoreOf_le_of_isSubnormal (p : ℕ) {A Y : Subgroup G} (h : IsSubnormal A Y) :
    pCoreOf p A ≤ pCoreOf p Y := by
  induction h with
  | refl => exact le_rfl
  | @step H M K hle hN hMK ih => exact (pCoreOf_le_of_normal p hle hN).trans ih

theorem pCoreOf_map_conj (p : ℕ) (H : Subgroup G) (g : G) :
    pCoreOf p (H.map (MulAut.conj g).toMonoidHom) =
      (pCoreOf p H).map (MulAut.conj g).toMonoidHom := by
  apply le_antisymm
  ·
    set P' := pCoreOf p (H.map (MulAut.conj g).toMonoidHom) with hP'
    have hP'H : P' ≤ H.map (MulAut.conj g).toMonoidHom := pCoreOf_le' p _
    have key : P'.map (MulAut.conj g⁻¹).toMonoidHom ≤ pCoreOf p H := by
      refine le_pCoreOf_of_normalized p ?_ ((isPGroup_pCoreOf' p _).map _) ?_
      · rintro _ ⟨y, hy, rfl⟩
        obtain ⟨h, hh, hhy⟩ := hP'H hy
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hhy ⊢
        have : g⁻¹ * y * g⁻¹⁻¹ = h := by rw [← hhy]; group
        rw [this]; exact hh
      · rintro h hh _ ⟨y, hy, rfl⟩
        refine ⟨(g * h * g⁻¹) * y * (g * h * g⁻¹)⁻¹,
          conj_mem_pCoreOf' p (H := H.map (MulAut.conj g).toMonoidHom)
            ⟨h, hh, by simp [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]⟩ hy, ?_⟩
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
    intro x hx
    refine ⟨g⁻¹ * x * g⁻¹⁻¹, key ⟨x, hx, by simp [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]⟩, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  · refine le_pCoreOf_of_normalized p (Subgroup.map_mono (pCoreOf_le' p H))
      ((isPGroup_pCoreOf' p H).map _) ?_
    rintro _ ⟨h, hh, rfl⟩ _ ⟨y, hy, rfl⟩
    refine ⟨h * y * h⁻¹, conj_mem_pCoreOf' p hh hy, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group

end PCoreAux

section Component

variable {X : Type} [Group X]

theorem isPGroup_sSup_of_commute {p : ℕ} (𝒮 : Set (Subgroup X)) (hfin : 𝒮.Finite)
    (hp : ∀ A ∈ 𝒮, IsPGroup p A)
    (hc : ∀ A ∈ 𝒮, ∀ A' ∈ 𝒮, A ≠ A' → A ≤ Subgroup.centralizer (A' : Set X)) :
    IsPGroup p (sSup 𝒮 : Subgroup X) := by
  induction 𝒮, hfin using Set.Finite.induction_on with
  | empty => rw [sSup_empty]; exact IsPGroup.of_bot
  | @insert a s has hs ih =>
    rw [sSup_insert]
    have hs' : IsPGroup p (sSup s : Subgroup X) :=
      ih (fun A hA => hp A (Set.mem_insert_of_mem _ hA))
        (fun A hA A' hA' hne => hc A (Set.mem_insert_of_mem _ hA) A'
          (Set.mem_insert_of_mem _ hA') hne)
    have hnorm : a ≤ Subgroup.normalizer ((sSup s : Subgroup X) : Set X) := by
      refine le_trans ?_ (Subgroup.centralizer_le_normalizer ((sSup s : Subgroup X) : Set X))
      rw [Subgroup.le_centralizer_iff]
      refine sSup_le fun A hA => ?_
      have hne : A ≠ a := fun h => has (h ▸ hA)
      exact hc A (Set.mem_insert_of_mem _ hA) a (Set.mem_insert _ _) hne
    exact (hp a (Set.mem_insert _ _)).to_sup_of_normal_right' hs' hnorm

theorem pCoreOf_inf_le_of_isComponent [Finite X] {K V : Subgroup X} (hK : CFSG.IsComponent K)
    (p : ℕ) : pCoreOf p (K ⊓ V) ≤ pCoreOf p V := by
  classical
  let cK : ↥V → Subgroup X := fun v => K.map (MulAut.conj (v : X)).toMonoidHom
  let A : ↥V → Subgroup X := fun v => pCoreOf p (cK v ⊓ V)
  let 𝒪 : Set (Subgroup X) := Set.range A
  have hcK : ∀ v, CFSG.IsComponent (cK v) := fun v =>
    CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj (v : X)) hK
  have hAV : ∀ v, A v ≤ V := fun v => (pCoreOf_le' p _).trans inf_le_right
  have hAK : ∀ v, A v ≤ cK v := fun v => (pCoreOf_le' p _).trans inf_le_left
  have hcomm : ∀ v w, A v ≠ A w → A v ≤ Subgroup.centralizer (A w : Set X) := by
    intro v w hne
    have hne' : cK v ≠ cK w := fun h => hne (by simp only [A, h])
    rcases CFSG.LocalCores.distinct_components_commute (hcK v) (hcK w) with h | h
    · exact absurd h hne'
    · have h1 : cK v ≤ Subgroup.centralizer (cK w : Set X) :=
        Subgroup.commutator_eq_bot_iff_le_centralizer.mp h
      exact (hAK v).trans (h1.trans (Subgroup.centralizer_le (hAK w)))
  have hP : IsPGroup p (sSup 𝒪 : Subgroup X) := by
    refine isPGroup_sSup_of_commute 𝒪 (Set.finite_range _) ?_ ?_
    · rintro _ ⟨v, rfl⟩
      exact isPGroup_pCoreOf' p _
    · rintro _ ⟨v, rfl⟩ _ ⟨w, rfl⟩ hne
      exact hcomm v w hne
  have hle : (sSup 𝒪 : Subgroup X) ≤ V := by
    refine sSup_le ?_
    rintro _ ⟨v, rfl⟩
    exact hAV v
  have hconjA : ∀ (h : ↥V) (v : ↥V),
      (A v).map (MulAut.conj (h : X)).toMonoidHom = A (h * v) := by
    intro h v
    have h1 : (cK v).map (MulAut.conj (h : X)).toMonoidHom = cK (h * v) := by
      simp only [cK, Subgroup.map_map]
      congr 1
      ext x
      simp [MulAut.conj_apply, mul_assoc]
    have h2 : V.map (MulAut.conj (h : X)).toMonoidHom = V := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        simpa [MulAut.conj_apply] using V.mul_mem (V.mul_mem h.2 hy) (V.inv_mem h.2)
      · intro hx
        refine ⟨(h : X)⁻¹ * x * (h : X)⁻¹⁻¹, V.mul_mem (V.mul_mem (V.inv_mem h.2) hx)
          (V.inv_mem (V.inv_mem h.2)), ?_⟩
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
    have h3 : (cK v ⊓ V).map (MulAut.conj (h : X)).toMonoidHom = cK (h * v) ⊓ V := by
      have := Subgroup.map_inf (cK v) V (MulAut.conj (h : X)).toMonoidHom
        (MulAut.conj (h : X)).injective
      rw [h1, h2] at this
      exact this
    simp only [A]
    rw [← h3, pCoreOf_map_conj]
  have hAle : ∀ v : ↥V, A v ≤ (sSup 𝒪 : Subgroup X) := fun v => le_sSup (Set.mem_range_self v)
  have hnormal : ∀ h ∈ V, ∀ q ∈ (sSup 𝒪 : Subgroup X), h * q * h⁻¹ ∈ (sSup 𝒪 : Subgroup X) := by
    intro h hh q hq
    have hmap : ∀ v : ↥V, (A v).map (MulAut.conj h).toMonoidHom ≤ (sSup 𝒪 : Subgroup X) := by
      intro v
      rw [show h = ((⟨h, hh⟩ : ↥V) : X) from rfl, hconjA ⟨h, hh⟩ v]
      exact hAle _
    have hcomap : (sSup 𝒪 : Subgroup X) ≤
        (sSup 𝒪 : Subgroup X).comap (MulAut.conj h).toMonoidHom := by
      refine sSup_le ?_
      rintro _ ⟨v, rfl⟩
      exact Subgroup.map_le_iff_le_comap.mp (hmap v)
    have := hcomap hq
    simpa [MulAut.conj_apply] using this
  have hbig : (sSup 𝒪 : Subgroup X) ≤ pCoreOf p V := le_pCoreOf_of_normalized p hle hP hnormal
  have h1 : A 1 = pCoreOf p (K ⊓ V) := by
    have : cK 1 = K := by
      ext x
      simp [cK, MulAut.conj_apply]
    simp only [A, this]
  rw [← h1]
  exact (le_sSup (Set.mem_range_self (1 : ↥V))).trans hbig

end Component

section Dichotomy

variable {X : Type} [Group X]

theorem commutator_mul_commute {a a' c c' : X} (hca : Commute c a) (hca' : Commute c a')
    (hcc' : Commute c c') (hc'a : Commute c' a) : ⁅a * c, a' * c'⁆ = ⁅a, a'⁆ := by
  rw [commutatorElement_def, commutatorElement_def]
  have e1 : c * a' * c' * c⁻¹ = a' * c' := by
    have h : Commute c (a' * c') := hca'.mul_right hcc'
    calc c * a' * c' * c⁻¹ = c * (a' * c') * c⁻¹ := by group
      _ = a' * c' := h.mul_inv_cancel
  have e2 : c' * a⁻¹ * c'⁻¹ = a⁻¹ := (hc'a.inv_right).mul_inv_cancel
  calc a * c * (a' * c') * (a * c)⁻¹ * (a' * c')⁻¹
      = a * (c * a' * c' * c⁻¹) * a⁻¹ * c'⁻¹ * a'⁻¹ := by group
    _ = a * (a' * c') * a⁻¹ * c'⁻¹ * a'⁻¹ := by rw [e1]
    _ = a * a' * (c' * a⁻¹ * c'⁻¹) * a'⁻¹ := by group
    _ = a * a' * a⁻¹ * a'⁻¹ := by rw [e2]

theorem ggPerfect_le_of_split {A T₁ T₂ P : Subgroup X} (hT₁ : T₁ ≤ A)
    (hT₂ : T₂ ≤ Subgroup.centralizer (A : Set X)) (hPA : P ≤ A) (hperf : ⁅P, P⁆ = P)
    (hP : P ≤ T₁ ⊔ T₂) : P ≤ T₁ := by
  have hcomm : ∀ a ∈ A, ∀ t ∈ T₂, a * t = t * a := fun a ha t ht =>
    Subgroup.mem_centralizer_iff.mp (hT₂ ht) a ha
  let B : Subgroup X :=
    { carrier := {y | ∃ t₁ ∈ T₁, ∃ t₂ ∈ T₂, y = t₁ * t₂}
      mul_mem' := by
        rintro _ _ ⟨a₁, ha₁, b₁, hb₁, rfl⟩ ⟨a₂, ha₂, b₂, hb₂, rfl⟩
        refine ⟨a₁ * a₂, T₁.mul_mem ha₁ ha₂, b₁ * b₂, T₂.mul_mem hb₁ hb₂, ?_⟩
        have h := hcomm a₂ (hT₁ ha₂) b₁ hb₁
        calc a₁ * b₁ * (a₂ * b₂) = a₁ * (b₁ * a₂) * b₂ := by group
          _ = a₁ * (a₂ * b₁) * b₂ := by rw [h]
          _ = a₁ * a₂ * (b₁ * b₂) := by group
      one_mem' := ⟨1, T₁.one_mem, 1, T₂.one_mem, (mul_one 1).symm⟩
      inv_mem' := by
        rintro _ ⟨a, ha, b, hb, rfl⟩
        refine ⟨a⁻¹, T₁.inv_mem ha, b⁻¹, T₂.inv_mem hb, ?_⟩
        have h := hcomm a (hT₁ ha) b hb
        rw [h, mul_inv_rev] }
  have hle : T₁ ⊔ T₂ ≤ B := sup_le (fun t ht => ⟨t, ht, 1, T₂.one_mem, (mul_one t).symm⟩)
    (fun t ht => ⟨1, T₁.one_mem, t, ht, (one_mul t).symm⟩)
  have hdec : ∀ y ∈ P, ∃ t₁ ∈ T₁, ∃ t₂ ∈ T₂, t₂ ∈ A ∧ y = t₁ * t₂ := by
    intro y hy
    obtain ⟨t₁, ht₁, t₂, ht₂, rfl⟩ := hle (hP hy)
    refine ⟨t₁, ht₁, t₂, ht₂, ?_, rfl⟩
    have h1 : t₁⁻¹ * (t₁ * t₂) ∈ A := A.mul_mem (A.inv_mem (hT₁ ht₁)) (hPA hy)
    simpa using h1
  rw [← hperf, Subgroup.commutator_def]
  refine (Subgroup.closure_le _).mpr ?_
  rintro _ ⟨y, hy, y', hy', rfl⟩
  obtain ⟨a, ha, c, hc, hcA, rfl⟩ := hdec y hy
  obtain ⟨a', ha', c', hc', hcA', rfl⟩ := hdec y' hy'
  have hcm : ∀ z ∈ A, Commute c z := fun z hz => (hcomm z hz c hc).symm
  have hcm' : ∀ z ∈ A, Commute c' z := fun z hz => (hcomm z hz c' hc').symm
  rw [commutator_mul_commute (hcm a (hT₁ ha)) (hcm a' (hT₁ ha')) (hcm c' hcA') (hcm' a (hT₁ ha)),
    commutatorElement_def]
  exact T₁.mul_mem (T₁.mul_mem (T₁.mul_mem ha ha') (T₁.inv_mem ha)) (T₁.inv_mem ha')

theorem commutator_sSup_eq_self {𝒞 : Set (Subgroup X)} (h : ∀ S ∈ 𝒞, ⁅S, S⁆ = S) :
    ⁅(sSup 𝒞 : Subgroup X), sSup 𝒞⁆ = sSup 𝒞 := by
  refine le_antisymm (Subgroup.commutator_le.mpr fun a ha b hb => ?_) (sSup_le fun S hS => ?_)
  · rw [commutatorElement_def]
    exact (sSup 𝒞 : Subgroup X).mul_mem ((sSup 𝒞 : Subgroup X).mul_mem
      ((sSup 𝒞 : Subgroup X).mul_mem ha hb) ((sSup 𝒞 : Subgroup X).inv_mem ha))
      ((sSup 𝒞 : Subgroup X).inv_mem hb)
  calc S = ⁅S, S⁆ := (h S hS).symm
    _ ≤ ⁅(sSup 𝒞 : Subgroup X), sSup 𝒞⁆ :=
      Subgroup.commutator_mono (le_sSup hS) (le_sSup hS)

end Dichotomy

section MarkingTransport

variable {A B : Type*} [Group A] [Group B]

theorem ggLargeEvenMarking_of_centerQuot_equiv' (hB : commutator B = ⊤)
    (e : A ⧸ Subgroup.center A ≃* B ⧸ Subgroup.center B)
    {P : LargeEvenMarkProp A} {P' : LargeEvenMarkProp B}
    (hPP' : ∀ (lab : LargeEvenLabel) (R : Type) [Group R] (I F : Set (MulAut R))
      (θ : A ⧸ Subgroup.center A ≃* R), P lab R I F θ → P' lab R I F (e.symm.trans θ))
    (h : LargeEvenMarking A P) : LargeEvenMarking B P' := by
  obtain ⟨-, lab, hlab, hraw⟩ := h
  refine ⟨hB, lab, hlab, largeEvenRawDatum_mono ?_ hraw⟩
  rintro R _ I F ⟨hs, hna, θ, hθ⟩
  exact ⟨hs, hna, e.symm.trans θ, hPP' lab R I F θ hθ⟩

end MarkingTransport

section Abstract

variable {X : Type} [Group X] [Finite X]

@[expose] def GGSummandStruct (E K V Q : Subgroup X) (𝒞 : Set (Subgroup X)) : Prop :=
  pCoreOf 2 (K ⊓ V) = Q ∧
  (∀ P : Subgroup X, P ≤ K ⊓ V → ⁅P, P⁆ = P → P ≤ sSup 𝒞) ∧
  ∀ S ∈ 𝒞, S ≤ K ⊓ V ∧ Q ≤ S ∧ IsSubnormal S (K ⊓ V) ∧ ⁅S, S⁆ = S ∧
    E ≤ Subgroup.normalizer (S : Set X) ∧
    ∀ [(Q.subgroupOf S).Normal], CFSG.Assembly.IsQuasisimple (↥S ⧸ Q.subgroupOf S) ∧
      LargeEvenMarking (↥S ⧸ Q.subgroupOf S) (fun lab _ _ I _ θ => GGChevStTag lab ∧
        ∀ ε ∈ E, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => ∃ s s' : ↥S,
          QuotientGroup.mk s = l ∧ QuotientGroup.mk s' = l' ∧ (s' : X) = ε⁻¹ * s * ε) φ)

section Rho

variable (V E K : Subgroup X) [hN : ((ggRCSU V E K).subgroupOf (E ⊔ K)).Normal]

theorem ggSumH_le : E ⊔ (K ⊓ V) ≤ E ⊔ K := sup_le_sup_left inf_le_left E

abbrev ggSumT : Subgroup (↥(E ⊔ K) ⧸ (ggRCSU V E K).subgroupOf (E ⊔ K)) :=
  ((E ⊔ (K ⊓ V)).subgroupOf (E ⊔ K)).map
    (QuotientGroup.mk' ((ggRCSU V E K).subgroupOf (E ⊔ K)))

@[expose] noncomputable def ggSumSigma : ↥(E ⊔ (K ⊓ V)) →* ↥(ggSumT V E K) :=
  ((QuotientGroup.mk' ((ggRCSU V E K).subgroupOf (E ⊔ K))).comp
    (Subgroup.inclusion (ggSumH_le V E K))).codRestrict _ (fun h =>
      Subgroup.mem_map.mpr ⟨Subgroup.inclusion (ggSumH_le V E K) h,
        Subgroup.mem_subgroupOf.mpr h.2, rfl⟩)

@[expose] noncomputable def ggSumRho : ↥(E ⊔ (K ⊓ V)) →* GGHypQuot (ggSumT V E K) :=
  (QuotientGroup.mk' (CFSG.pCore 2 ↥(ggSumT V E K))).comp (ggSumSigma V E K)

@[expose] noncomputable def ggSumImg (S : Subgroup X) : Subgroup (GGHypQuot (ggSumT V E K)) :=
  (S.subgroupOf (E ⊔ (K ⊓ V))).map (ggSumRho V E K)

end Rho

end Abstract

end CFSG.StandardType
