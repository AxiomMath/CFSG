module

public import CFSG.Quasithin.Background.SimsF5Tr
public import CFSG.Quasithin.Background.SimsF5AT
public import CFSG.Quasithin.Background.SimsF5Count

public section

namespace CFSG.Quasithin.SimsF5

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open CFSG.Open CFSG.Quasithin CFSG.ASVolI.ChF CFSG.Quasithin.H13.F431.U42Aut
open CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion


section Std

variable {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E} {Y : Type} [Group Y]
  {β : Cpl M₁ M₂ Y} {M : Type} [Group M] {ε : Y →* M} {z : M} {Tb : Subgroup E}
  {fb : ↥(M₁ ⊓ M₂)} {μ : Cpl M₁ M₂ ↥M0Dot} {zb : ↥M₁} {Φ : M ≃* ↥MDot}

theorem exists_std (h : HypF5 Gp M₁ M₂ β ε z Tb fb) :
    ∃ (Θ : E ≃* ↥M0Dot) (zb : ↥M₁) (Φ : M ≃* ↥MDot), ε (β.φ1 zb) = z ∧ NmCompat Θ Gp M₁ M₂ ∧
      IsMarkedMuIso (muOfIso Θ h.f431.amalgam.gen) zb fb Tb ∧
      PhiExt β ε (muOfIso Θ h.f431.amalgam.gen) Φ := by
  obtain ⟨Θ, zb, hz, hC, hμ⟩ := exists_marked_compat h
  obtain ⟨Φ, hΦ⟩ := exists_PhiM h hμ.1 hz
  exact ⟨Θ, zb, Φ, hz, hC, hμ, hΦ⟩

theorem tr_R (hμ : IsMarkedMuIso μ zb fb Tb) (hΦ : PhiExt β ε μ Φ) {R : Subgroup M}
    (hR : IsRSylow β ε Tb fb R) : R.map (psiOf Φ) = RDot := by
  refine eq_RDot _ card_MDot_inf_cen_fDot ?_ ?_
  · rw [← tr_cen_f hμ.1 hΦ]
    exact tr_isSylowOf (psiOf_injective Φ) hR.1
  · rw [← tr_TfOf hμ hΦ]
    exact Subgroup.map_mono hR.2

theorem R_facts (h : HypF5 Gp M₁ M₂ β ε z Tb fb) {R : Subgroup M} (hR : IsRSylow β ε Tb fb R) :
    R ≤ HOf β ε fb ∧ R ⊓ M0Of β ε ≤ TfOf β ε Tb fb ∧ (TfOf β ε Tb fb).relIndex R = 2 := by
  obtain ⟨Θ, zb, Φ, hz, hC, hμ, hΦ⟩ := exists_std h
  have hRm := tr_R hμ hΦ hR
  have hinj := psiOf_injective Φ
  refine ⟨fun r hr => ?_, ?_, ?_⟩
  · have h1 : psiOf Φ r ∈ RDot := hRm ▸ ⟨r, hr, rfl⟩
    have h2 : psiOf Φ r ∈ (HOf β ε fb).map (psiOf Φ) := by
      rw [tr_HOf hμ.1 hΦ]
      exact ⟨(RDot_le h1).1, CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _
        (RDot_le_normalizer_EDot M2Dot (Or.inr rfl) h1)⟩
    exact (tr_mem_map_iff hinj).1 h2
  · have : (R ⊓ M0Of β ε).map (psiOf Φ) = (TfOf β ε Tb fb).map (psiOf Φ) := by
      rw [tr_map_inf hinj, hRm, tr_M0Of hμ.1 hΦ, RDot_inf_M0Dot, tr_TfOf hμ hΦ]
    exact (Subgroup.map_injective hinj this).le
  · rw [← Subgroup.relIndex_map_map_of_injective _ _ hinj, hRm, tr_TfOf hμ hΦ]
    exact m4_index_Tf_R

end Std

theorem f56 : F56 := by
  intro E _ Gp M₁ M₂ Y _ β M _ ε z Tb fb h
  haveI := h.f431.finite_M
  obtain ⟨Θ, zb, Φ, hz, hC, hμ, hΦ⟩ := exists_std h
  obtain ⟨R, hR, hTR⟩ := exists_R (ctxOfMarked h hμ.1 hz (hypF5_normalizers' h))
  obtain ⟨-, -, -, h56⟩ := autCtx_conf (ctxOfMarked h hμ.1 hz (hypF5_normalizers' h)) hR hTR
  have hf : (ctxOfMarked h hμ.1 hz (hypF5_normalizers' h)).iso.toG fhB = fOf β ε fb :=
    autIsoOfMarked_toG_fhB h hμ.1
  rw [hf] at h56
  exact h56

theorem f53 : F53 := by
  refine ⟨f53Model, ?_⟩
  intro E _ Gp M₁ M₂ Y _ β M _ ε z Tb fb h
  refine ⟨exists_marked h, ?_, ?_, ?_⟩
  · intro μ zb hz hμ a
    obtain ⟨Φ, hΦ⟩ := exists_PhiM h hμ.1 hz
    have hinj := psiOf_injective Φ
    have hT : bM β ε a ∈ TOf β ε Tb ↔ ((μ.φ12 a : ↥M0Dot) : GL6) ∈ TDot := by
      rw [← tr_mem_map_iff hinj, tr_TOf hμ hΦ, tr_bM hΦ]
    have hzc : IsConj z (bM β ε a) ↔
        ∃ g ∈ MDot, g * zDot * g⁻¹ = ((μ.φ12 a : ↥M0Dot) : GL6) := by
      rw [tr_isConj_iff hinj, psiOf_range, tr_z hμ.1 hΦ hz, tr_bM hΦ]
    have hfc : IsConj (fOf β ε fb) (bM β ε a) ↔
        ∃ g ∈ MDot, g * fDot * g⁻¹ = ((μ.φ12 a : ↥M0Dot) : GL6) := by
      rw [tr_isConj_iff hinj, psiOf_range, tr_fOf hμ.1 hΦ, tr_bM hΦ]
    exact ⟨by rw [hzc, hT], by rw [hfc, hT]⟩
  · intro t ht
    obtain ⟨Θ, zb, Φ, hz, hC, hμ, hΦ⟩ := exists_std h
    rw [tr_isConj_iff (psiOf_injective Φ), psiOf_range, map_mul, map_mul, tr_fOf hμ.1 hΦ,
      tr_tInv hμ.1 hC hΦ ht, tr_z hμ.1 hΦ hz]
    exact conj_zDot_fDot_tDot_zDot
  · obtain ⟨Θ, zb, Φ, hz, hC, hμ, hΦ⟩ := exists_std h
    have hinj := psiOf_injective Φ
    have key : ∀ (X : Subgroup M) (X' : Subgroup GL6), X.map (psiOf Φ) = X' →
        ({x : M | IsConj z x} ∩ (X : Set M)).ncard =
          ({y : GL6 | ∃ g ∈ MDot, g * zDot * g⁻¹ = y} ∩ (X' : Set GL6)).ncard := by
      intro X X' hX
      rw [← Set.ncard_image_of_injective _ hinj, Set.image_inter hinj, tr_image_isConj hinj,
        psiOf_range, tr_z hμ.1 hΦ hz, ← Subgroup.coe_map, hX]
    exact ⟨(key _ _ (tr_A1 hμ.1 hΦ)).trans ncard_zCls_ADot_M1Dot,
      (key _ _ (tr_QTwo hC hΦ)).trans ncard_zCls_Q2Dot,
      (key _ _ (tr_A2 hμ.1 hΦ)).trans ncard_zCls_ADot_M2Dot⟩

section F54Aux

theorem TDot_le_MDot : TDot ≤ MDot :=
  TDot_le_M12.trans (inf_le_left.trans (inf_le_left : M1Dot ≤ MDot))

theorem tr_quot {A B : Type} [Group A] [Group B] {ψ : A →* B} (hψ : Function.Injective ψ)
    {N Q : Subgroup A} {N' Q' : Subgroup B} [(Q.subgroupOf N).Normal] [(Q'.subgroupOf N').Normal]
    (hN : N.map ψ = N') (hQ : Q.map ψ = Q') :
    Nonempty (↥N ⧸ Q.subgroupOf N ≃* ↥N' ⧸ Q'.subgroupOf N') := by
  let e : ↥N ≃* ↥N' := (N.equivMapOfInjective ψ hψ).trans (MulEquiv.subgroupCongr hN)
  have he : (Q.subgroupOf N).map e.toMonoidHom = Q'.subgroupOf N' := by
    ext x
    constructor
    · rintro ⟨n, hn, rfl⟩
      show ψ (n : A) ∈ Q'
      rw [← hQ]
      exact ⟨n, hn, rfl⟩
    · intro hx
      rw [Subgroup.mem_subgroupOf, ← hQ] at hx
      obtain ⟨q, hq, hqx⟩ := hx
      have hxN : (x : B) ∈ N.map ψ := by rw [hN]; exact x.2
      have hqN : q ∈ N := (tr_mem_map_iff hψ).1 (hqx ▸ hxN)
      exact ⟨⟨q, hqN⟩, hq, Subtype.ext hqx⟩
  exact ⟨QuotientGroup.congr _ _ e he⟩

theorem tr_conjAct_apply {M : Type} [Group M] {A : Subgroup M} {g : M}
    (hg : g ∈ Subgroup.normalizer (A : Set M)) (a : ↥A) :
    ((conjAct A ⟨g, hg⟩ a : ↥A) : M) = g * a * g⁻¹ :=
  rfl

theorem tr_transvection {M : Type} [Group M] (Φ : M ≃* ↥MDot) {A : Subgroup M}
    {AD : Subgroup GL6} (hA : A.map (psiOf Φ) = AD) (hsq : ∀ a ∈ AD, a * a = 1) {g : GL6}
    (hgM : g ∈ MDot) (hgN : g ∈ Subgroup.normalizer (AD : Set GL6)) {w : GL6} (hw1 : w ≠ 1)
    (hex : ∃ a ∈ AD, g * a * g⁻¹ * a⁻¹ = w)
    (hall : ∀ a ∈ AD, g * a * g⁻¹ * a⁻¹ = 1 ∨ g * a * g⁻¹ * a⁻¹ = w) :
    ∃ τ ∈ autOn (⊤ : Subgroup M) A, IsTransvection τ := by
  have hinj := psiOf_injective Φ
  have hmemA : ∀ x : M, psiOf Φ x ∈ AD ↔ x ∈ A := fun x => by rw [← hA, tr_mem_map_iff hinj]
  set g' : M := Φ.symm ⟨g, hgM⟩ with hg'def
  have hg' : psiOf Φ g' = g := psiOf_symm Φ hgM
  have hg'N : g' ∈ Subgroup.normalizer (A : Set M) := by
    have : psiOf Φ g' ∈ (Subgroup.normalizer (A : Set M)).map (psiOf Φ) := by
      rw [tr_normalizer, hA, hg']
      exact ⟨hgM, hgN⟩
    exact (tr_mem_map_iff hinj).1 this
  set τ := conjAct A ⟨g', hg'N⟩ with hτ
  have hτv : ∀ a : ↥A, psiOf Φ ((τ a * a⁻¹ : ↥A) : M) = g * psiOf Φ a * g⁻¹ * (psiOf Φ a)⁻¹ := by
    intro a
    rw [Subgroup.coe_mul, Subgroup.coe_inv, tr_conjAct_apply, map_mul, map_mul, map_mul, map_inv,
      map_inv, hg']
  obtain ⟨a0, ha0, hw⟩ := hex
  obtain ⟨a0', ha0'⟩ : ∃ a0' : ↥A, psiOf Φ a0' = a0 := by
    rw [← hA] at ha0
    obtain ⟨x, hx, rfl⟩ := ha0
    exact ⟨⟨x, hx⟩, rfl⟩
  set wA : ↥A := τ a0' * a0'⁻¹ with hwA
  have hwAv : psiOf Φ wA = w := by rw [hτv, ha0', hw]
  have hwA1 : wA ≠ 1 := by
    intro h
    apply hw1
    rw [← hwAv, h, Subgroup.coe_one, map_one]
  have hwA2 : wA * wA = 1 := by
    apply Subtype.ext
    apply hinj
    rw [Subgroup.coe_mul, map_mul, hwAv, Subgroup.coe_one, map_one]
    exact hsq w (by rw [← hwAv]; exact (hmemA _).2 wA.2)
  have hS : ∀ x ∈ {x : ↥A | ∃ a : ↥A, x = τ a * a⁻¹}, x = 1 ∨ x = wA := by
    rintro _ ⟨a, rfl⟩
    rcases hall _ ((hmemA _).2 a.2) with h1 | h1
    · left
      apply Subtype.ext
      apply hinj
      rw [hτv, h1, Subgroup.coe_one, map_one]
    · right
      apply Subtype.ext
      apply hinj
      rw [hτv, h1, hwAv]
  have hcl : Subgroup.closure {x : ↥A | ∃ a : ↥A, x = τ a * a⁻¹} = Subgroup.zpowers wA := by
    apply le_antisymm
    · rw [Subgroup.closure_le]
      intro x hx
      rcases hS x hx with rfl | rfl
      · exact Subgroup.one_mem _
      · exact Subgroup.mem_zpowers _
    · rw [Subgroup.zpowers_le]
      exact Subgroup.subset_closure ⟨a0', rfl⟩
  refine ⟨τ, ⟨⟨g', hg'N⟩, Subgroup.mem_subgroupOf.2 (Subgroup.mem_top _), rfl⟩, ?_, ?_⟩
  · intro h
    apply hwA1
    rw [hwA, h, MulAut.one_apply, mul_inv_cancel]
  · rw [hcl, Nat.card_zpowers]
    exact orderOf_eq_prime (by rw [sq]; exact hwA2) hwA1

end F54Aux

theorem f54 : F54 := by
  intro E _ Gp M₁ M₂ Y _ β M _ ε z Tb fb R h hR t ht
  haveI := h.f431.finite_M
  obtain ⟨Θ, zb, Φ, hz, hC, hμ, hΦ⟩ := exists_std h
  have hinj := psiOf_injective Φ
  have hf : (ctxOfMarked h hμ.1 hz (hypF5_normalizers' h)).iso.toG fhB = fOf β ε fb :=
    autIsoOfMarked_toG_fhB h hμ.1
  have hTi : (autIsoOfMarked h hμ.1).imgG That = TOf β ε Tb := autIsoOfMarked_imgG_That h hμ
  have hR' : CFSG.QuasithinUnique.IsSylowTwoOf R
      (cenOf ((ctxOfMarked h hμ.1 hz (hypF5_normalizers' h)).iso.toG fhB)) := by
    rw [hf]
    exact hR.1
  have hTR' : (ctxOfMarked h hμ.1 hz (hypF5_normalizers' h)).iso.imgG That ⊓
      cenOf ((ctxOfMarked h hμ.1 hz (hypF5_normalizers' h)).iso.toG fhB) ≤ R := by
    rw [hf]
    exact hTi ▸ hR.2
  obtain ⟨-, h54, -, -⟩ := autCtx_conf (ctxOfMarked h hμ.1 hz (hypF5_normalizers' h)) hR' hTR'
  rw [hf] at h54
  have hRm := tr_R hμ hΦ hR
  have ht' := tr_tInv hμ.1 hC hΦ ht
  have hMi : ∀ Mi : Subgroup M, (Mi = MiOne β ε ∨ Mi = MiTwo β ε) →
      ∃ MiDot : Subgroup GL6, (MiDot = M1Dot ∨ MiDot = M2Dot) ∧ Mi.map (psiOf Φ) = MiDot ∧
        MiDot ≤ MDot := by
    rintro Mi (rfl | rfl)
    · exact ⟨M1Dot, Or.inl rfl, tr_MiOne hμ.1 hΦ, inf_le_left⟩
    · exact ⟨M2Dot, Or.inr rfl, tr_MiTwo hμ.1 hΦ, inf_le_left⟩
  refine ⟨⟨h54.1.symm, h54.2.1.symm⟩, ?_, ?_, ?_, ?_⟩
  ·
    have hTt : (TOf β ε Tb ⊓ Subgroup.centralizer ({t} : Set M)).map (psiOf Φ) =
        TDot ⊓ Subgroup.centralizer ({tDot} : Set GL6) := by
      rw [tr_map_inf hinj, tr_TOf hμ hΦ, tr_cen, ht', ← inf_assoc, inf_eq_left.2 TDot_le_MDot]
    obtain ⟨eT⟩ := TDot_inf_cen_tDot
    obtain ⟨eR⟩ := h54.2.2.2.2.1
    obtain ⟨e1⟩ := tr_equiv hinj (TOf β ε Tb ⊓ Subgroup.centralizer ({t} : Set M))
    have e2 := e1.trans ((MulEquiv.subgroupCongr hTt).trans eT)
    exact ⟨⟨eR.trans e2.symm⟩, ⟨e2⟩⟩
  ·
    intro Mi hMi'
    obtain ⟨MiDot, hMiD, hmap, hle⟩ := hMi Mi hMi'
    have hE := tr_EOf hμ.1 hΦ hmap hle
    refine ⟨fun r hr => ?_, ?_⟩
    · have h1 : psiOf Φ r ∈ RDot := hRm ▸ ⟨r, hr, rfl⟩
      have h2 : psiOf Φ r ∈
          (Subgroup.normalizer (EOf Mi (fOf β ε fb) : Set M)).map (psiOf Φ) := by
        rw [tr_normalizer, hE]
        exact ⟨(RDot_le h1).1, RDot_le_normalizer_EDot MiDot hMiD h1⟩
      exact (tr_mem_map_iff hinj).1 h2
    · have hS : (EOf Mi (fOf β ε fb) ⊔ R).map (psiOf Φ) = EDot MiDot ⊔ RDot := by
        rw [Subgroup.map_sup, hE, hRm]
      obtain ⟨e1⟩ := tr_equiv hinj (EOf Mi (fOf β ε fb) ⊔ R)
      obtain ⟨e2⟩ := EDot_sup_RDot MiDot hMiD
      exact ⟨e1.trans ((MulEquiv.subgroupCongr hS).trans e2)⟩
  ·
    have hQ := tr_QTwo hC hΦ
    refine ⟨fun y hy hyt => ?_, ?_, h54.2.2.2.2.2.2.2, h54.2.2.2.2.2.2.1⟩
    · have hA1 : (autIsoOfMarked h hμ.1).imgG A1h = AOf (MiOne β ε) (fOf β ε fb) := by
        have := aOf_M1 (autIsoOfMarked h hμ.1)
        rw [autIsoOfMarked_toG_fhB h hμ.1] at this
        exact this.symm
      have hA2 : (autIsoOfMarked h hμ.1).imgG A2h = AOf (MiTwo β ε) (fOf β ε fb) := by
        have := aOf_M2 (autIsoOfMarked h hμ.1)
        rw [autIsoOfMarked_toG_fhB h hμ.1] at this
        exact this.symm
      have hVA : (autIsoOfMarked h hμ.1).imgG VA = QTwoOf Gp β ε := by
        apply Subgroup.map_injective hinj
        rw [hQ]
        exact (tr_imgG h hμ.1 hΦ VA_le_Bh).trans tr_VA
      have ht1 : (autIsoOfMarked h hμ.1).toG t1B = t := by
        apply hinj
        rw [tr_toG h hμ.1 hΦ, ht', lamG_apply, atCoe_t1B, atLamA_t1A]
      have hy' : y ∈ (autIsoOfMarked h hμ.1).imgG That := hTi ▸ hy
      have hyt' : y ∉ Subgroup.centralizer ({(autIsoOfMarked h hμ.1).toG t1B} : Set M) := by
        rw [ht1]
        exact hyt
      have hcj := cj_A2_eq (autIsoOfMarked h hμ.1) hy' hyt'
      rw [hA2] at hcj
      ext A
      simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
      have hiff := isMaxElemAbelian_imgG_iff (autIsoOfMarked h hμ.1) A
      rw [hTi, hA1, hA2, hVA, ← hcj] at hiff
      exact hiff
    · have hN : (Subgroup.normalizer (QTwoOf Gp β ε : Set M)).map (psiOf Φ) = M2Dot := by
        rw [tr_normalizer, hQ, MDot_inf_normalizer_Q2Dot]
      obtain ⟨e1⟩ := tr_quot hinj hN hQ
      obtain ⟨e2⟩ := M2Dot_quotient_Q2Dot
      exact ⟨e1.trans e2⟩
  ·
    intro Mi hMi'
    obtain ⟨MiDot, hMiD, hmap, hle⟩ := hMi Mi hMi'
    have hA := tr_AOf hμ.1 hΦ hmap hle
    obtain ⟨g, hgT, hgN, w, hw1, hex, hall⟩ := exists_transvection MiDot hMiD
    have hsq : ∀ a ∈ ADot MiDot, a * a = 1 := fun a ha =>
      congrArg Subtype.val ((f53Model.1 MiDot hMiD).2.2.1 ⟨a, ha⟩)
    exact tr_transvection Φ hA hsq (TDot_le_MDot hgT.1) hgN hw1 hex hall

theorem f55 : F55 := by
  intro E _ Gp M₁ M₂ Y _ β M _ ε z Tb fb R h hR
  obtain ⟨Θ, zb, Φ, hz, hC, hμ, hΦ⟩ := exists_std h
  have hinj := psiOf_injective Φ
  have hRm := tr_R hμ hΦ hR
  have hf : ((Θ (fb : E) : ↥M0Dot) : GL6) = fDot := hμ.1.f_eq
  have hD1 := tr_DOne hC hf hΦ
  have hD2 := tr_DTwo hC hf hΦ
  have hD : (DOne Gp β ε fb ⊔ DTwo Gp β ε fb).map (psiOf Φ) = DDot := by
    rw [Subgroup.map_sup, hD1, hD2, DDot1_sup_DDot2]
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · obtain ⟨e1⟩ := tr_equiv hinj (DOne Gp β ε fb)
    obtain ⟨e2⟩ := DDot1_equiv
    exact ⟨e1.trans ((MulEquiv.subgroupCongr hD1).trans e2)⟩
  · obtain ⟨e1⟩ := tr_equiv hinj (DTwo Gp β ε fb)
    obtain ⟨e2⟩ := DDot2_equiv
    exact ⟨e1.trans ((MulEquiv.subgroupCongr hD2).trans e2)⟩
  · obtain ⟨e1⟩ := tr_equiv hinj (DOne Gp β ε fb ⊔ DTwo Gp β ε fb)
    exact ⟨e1.trans ((MulEquiv.subgroupCongr hD).trans DDotEquivS6)⟩
  · have hX : (R ⊓ Subgroup.centralizer
        ((oTwoRes (DOne Gp β ε fb ⊔ DTwo Gp β ε fb) : Subgroup M) : Set M)).map (psiOf Φ) =
        Subgroup.zpowers rhoDot := by
      rw [tr_map_inf hinj, hRm, tr_map_centralizer hinj, psiOf_range, ← Subgroup.coe_map,
        tr_map_oTwoRes hinj, hD, oTwoRes_DDot, ← inf_assoc,
        inf_eq_left.2 (RDot_le.trans inf_le_left), RDot_inf_cen]
    obtain ⟨e1⟩ := tr_equiv hinj (R ⊓ Subgroup.centralizer
        ((oTwoRes (DOne Gp β ε fb ⊔ DTwo Gp β ε fb) : Subgroup M) : Set M))
    obtain ⟨e2⟩ := zpowers_rhoDot_equiv
    exact ⟨e1.trans ((MulEquiv.subgroupCongr hX).trans e2)⟩
  · apply Set.image_injective.2 hinj
    rw [Set.image_mul, ← Subgroup.coe_map, ← Subgroup.coe_map, ← Subgroup.coe_map, hRm, hD,
      tr_cen_f hμ.1 hΦ, RDot_mul_DDot card_MDot_inf_cen_fDot]
  · have hM0 := tr_M0Of hμ.1 hΦ
    obtain ⟨e1⟩ := tr_equiv hinj (M0Of β ε)
    exact ⟨⟨e1.trans ((MulEquiv.subgroupCongr hM0).trans Θ.symm)⟩, ⟨Θ⟩, isAutU42_M0Dot⟩

end CFSG.Quasithin.SimsF5
