module

public import CFSG.LocalAnalysis.WeakClosure81.W183FourDefs
public import CFSG.LocalAnalysis.WeakClosure81.W183FUSec
public import CFSG.LocalAnalysis.WeakClosure81.W183FUY
public import CFSG.LocalAnalysis.WeakClosure81.W183TwoL24Cent
public import CFSG.LocalAnalysis.WeakClosure81.W183Br1Comp2
public import CFSG.LocalAnalysis.WeakClosure81.W183Br1Fam
public import CFSG.LocalAnalysis.WeakClosure81.W18ASCtx
public import CFSG.LocalAnalysis.WeakClosure81.W18Asch5
public import CFSG.GroupTheory.IsCyclicOfLeOfPRankLeOne

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Quasithin CFSG.Open
  CFSG.QuasithinUnique Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.UniquenessCase.PartTwo

variable {G : Type} [Group G] [Finite G]

theorem w183fu_isU3_cj {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    {A : Subgroup (LGL 2 V)} (y : LGL 2 V) (h : IsU3 ↥A 2) : IsU3 ↥(cj y A) 2 :=
  CFSG.Blueprint.LieModel.of_mulEquiv
    (Subgroup.equivMapOfInjective A (MulAut.conj y).toMonoidHom
      (MulAut.conj y).injective) h

private theorem w183fu_hasQuotShape_of_mulEquiv {K L L' : Subgroup G} (e : ↥L ≃* ↥L')
    (hK : ∀ l : ↥L, (l : G) ∈ K ↔ (e l : G) ∈ K) {P : ∀ (X : Type) [Group X], Prop}
    (hQ : HasQuotShape L K P) : HasQuotShape L' K P := by
  obtain ⟨X, hX, φ, hφs, hφk, hPX⟩ := hQ
  refine ⟨X, hX, φ.comp e.symm.toMonoidHom, hφs.comp e.symm.surjective, ?_, hPX⟩
  intro k
  change φ (e.symm k) = 1 ↔ (k : G) ∈ K
  rw [hφk (e.symm k)]
  have h := hK (e.symm k)
  rwa [show e (e.symm k) = k from e.apply_symm_apply k] at h

private theorem w183fu_isComponentModN_map_mulEquiv {K H L : Subgroup G} (e : G ≃* G)
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
  · refine w183fu_hasQuotShape_of_mulEquiv
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

theorem w183fu_component_conj {K H L : Subgroup G} (h : IsComponentModN K H L) {t : G}
    (ht : t ∈ H) {P : ∀ (X : Type) [Group X], Prop}
    (hP : ∀ (X Y : Type) [Group X] [Group Y], X ≃* Y → P X → P Y)
    (hQ : HasQuotShape L (K : Set G) P) :
    IsComponentModN K H (conjSubgroup L t) ∧ HasQuotShape (conjSubgroup L t) (K : Set G) P := by
  have hKH : K ≤ H := h.2.1.trans h.2.2.1
  have hnormK : H ≤ normalizer (K : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKH).mp h.1
  have htK : t ∈ normalizer (K : Set G) := hnormK ht
  have htH : t ∈ normalizer (H : Set G) := Subgroup.le_normalizer ht
  have hKinv : t⁻¹ ∈ normalizer (K : Set G) := (normalizer (K : Set G)).inv_mem htK
  have hHinv : t⁻¹ ∈ normalizer (H : Set G) := (normalizer (H : Set G)).inv_mem htH
  have hKmap : K.map (MulAut.conj t⁻¹).toMonoidHom = K :=
    (Subgroup.mem_normalizer_iff_map_conj_eq (H := K) (g := t⁻¹)).mp hKinv
  have hHmap : H.map (MulAut.conj t⁻¹).toMonoidHom = H :=
    (Subgroup.mem_normalizer_iff_map_conj_eq (H := H) (g := t⁻¹)).mp hHinv
  have hKmem : ∀ l : ↥L, (l : G) ∈ K ↔
      ((Subgroup.equivMapOfInjective L (MulAut.conj t⁻¹).toMonoidHom
        (fun a b hab => (MulAut.conj t⁻¹).injective hab)) l : G) ∈ K := by
    intro l
    change (l : G) ∈ K ↔ (MulAut.conj t⁻¹) (l : G) ∈ K
    have h := (Subgroup.mem_normalizer_iff'' (H := K) (g := t)).mp htK (l : G)
    simpa [MulAut.conj_apply] using h
  have hLc := w183fu_isComponentModN_map_mulEquiv (K := K) (H := H) (L := L)
    (MulAut.conj t⁻¹) hKmap hHmap h
  have hQ' := w183fu_hasQuotShape_of_mulEquiv (K := K)
    (Subgroup.equivMapOfInjective L (MulAut.conj t⁻¹).toMonoidHom
      (fun a b hab => (MulAut.conj t⁻¹).injective hab)) hKmem hQ
  constructor
  · simpa only [CFSG.Quasithin.conjSubgroup] using hLc
  · simpa only [CFSG.Quasithin.conjSubgroup] using hQ'

theorem w183fu_cyclic_five {D : Data G} {V₀ V H : Subgroup G} {i : ℕ} (c : MinCex183 D V₀ V H i)
    (h2 : ¬ Concl182 D V₀ V H i) (h5 : 3 < CFSG.Open.pRank 5 H) :
    ∀ P : Subgroup G, P ≤ H ⊓ D.M → IsPGroup 5 P → IsCyclic ↥P := by
  intro P hPN hP
  have h5' : 3 < CFSG.pRank 5 ↥H := by
    rwa [CFSG.SectionRank.pRank_coe_eq_openPRank]
  have hle := (not_concl182_iff.mp h2).1.2 5 Nat.prime_five (by norm_num) h5'
  have hle' : CFSG.Open.pRank 5 (H ⊓ D.M) ≤ 1 := by
    rwa [CFSG.SectionRank.pRank_coe_eq_openPRank] at hle
  exact CFSG.isCyclic_of_le_of_pRank_le_one Nat.prime_five (by norm_num) hP hPN hle'

namespace Ctx188

variable {D : Data G} {V₀ V H : Subgroup G} {i j : ℕ}

theorem w183fu_preimage_le_M (x : Ctx188 D V₀ V H i j) (M : ModDataE H (eOmegaZ H D.T))
    (hN : calNIn H D.T = {H ⊓ D.M}) {X : Subgroup (LGL 2 M.W)} (hXH : X ≤ M.img H)
    (hTX : M.img D.T ≤ X) (hXne : X ≠ M.img H) :
    ∀ j : ↥H, M.ρ j ∈ X → (j : G) ∈ D.M := by
  intro j hj
  let Xt : Subgroup G := (X.comap M.ρ).map H.subtype
  have hXtH : Xt ≤ H := Subgroup.map_subtype_le _
  have hTXt : D.T ≤ Xt := by
    intro t ht
    have hmem : M.ρ ⟨t, x.hyp.hyp171.2.1 ht⟩ ∈ X :=
      hTX (M.mem_img.2 ⟨⟨t, x.hyp.hyp171.2.1 ht⟩, ht, rfl⟩)
    exact Subgroup.mem_map.2
      ⟨⟨t, x.hyp.hyp171.2.1 ht⟩, Subgroup.mem_comap.2 hmem, rfl⟩
  have hXtne : Xt ≠ H := by
    intro heq
    apply hXne
    refine le_antisymm hXH ?_
    intro r hr
    obtain ⟨h, _hh, hρ⟩ := M.mem_img.1 hr
    have hhXt : (h : G) ∈ Xt := by rw [heq]; exact h.2
    obtain ⟨k, hk, hke⟩ := Subgroup.mem_map.1 hhXt
    rw [Subgroup.mem_comap] at hk
    have hkh : k = h := Subtype.ext hke
    rw [← hρ, ← hkh]
    exact hk
  obtain ⟨Y, hYcal, hXtY⟩ :=
    exists_mem_calNIn_of_lt hTXt (lt_of_le_of_ne hXtH hXtne)
  have hY : Y = H ⊓ D.M := by
    have : Y ∈ ({H ⊓ D.M} : Set (Subgroup G)) := hN ▸ hYcal
    simpa using this
  have hjXt : (j : G) ∈ Xt :=
    Subgroup.mem_map.2 ⟨j, Subgroup.mem_comap.2 hj, rfl⟩
  exact (Subgroup.mem_inf.1 (hY ▸ hXtY hjXt)).2

theorem w183fu_false_of_E25 (x : Ctx188 D V₀ V H i j) (M : ModDataE H (eOmegaZ H D.T))
    (hcyc : ∀ P : Subgroup G, P ≤ H ⊓ D.M → IsPGroup 5 P → IsCyclic ↥P)
    {E : Subgroup (LGL 2 M.W)} (hE : IsElemAbelian 5 E) (hcard : Nat.card E = 25)
    (hEH : E ≤ M.img H) (hEM : ∀ j : ↥H, M.ρ j ∈ E → (j : G) ∈ D.M) : False := by
  classical
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  let Pim : Subgroup ↥H := E.comap M.ρ
  have hPim : ∀ p : ↥Pim, M.ρ (Pim.subtype p) ∈ E := fun p =>
    Subgroup.mem_comap.1 p.2
  let ψ : ↥Pim →* ↥E := (M.ρ.comp Pim.subtype).codRestrict E hPim
  have hψsurj : Function.Surjective ψ := by
    intro e
    obtain ⟨h, _hh, hρ⟩ := M.mem_img.1 (hEH e.2)
    refine ⟨⟨h, Subgroup.mem_comap.2 ?_⟩, ?_⟩
    · rw [hρ]; exact e.2
    · apply Subtype.ext
      exact hρ
  let P : Sylow 5 ↥Pim := Sylow.nonempty.some
  have htop : IsPGroup 5 (⊤ : Subgroup ↥E) :=
    IsPGroup.of_card (n := 2) (by rw [Subgroup.card_top, hcard]; norm_num)
  have hPtop : (P : Subgroup ↥Pim).map ψ = ⊤ := by
    have h := (P.mapSurjective hψsurj).is_maximal' htop le_top
    simpa using h.symm
  let φ : ↥P →* ↥E := ψ.comp (P : Subgroup ↥Pim).subtype
  have hφsurj : Function.Surjective φ := by
    intro e
    have he : (e : ↥E) ∈ (P : Subgroup ↥Pim).map ψ := by
      rw [hPtop]; exact Subgroup.mem_top e
    obtain ⟨p, hp, hpe⟩ := Subgroup.mem_map.1 he
    exact ⟨⟨p, hp⟩, hpe⟩
  let g : ↥Pim →* G := H.subtype.comp Pim.subtype
  have hginj : Function.Injective g :=
    (Subgroup.subtype_injective H).comp (Subgroup.subtype_injective Pim)
  have hQle : (P : Subgroup ↥Pim).map g ≤ H ⊓ D.M := by
    intro y hy
    obtain ⟨p, _hp, rfl⟩ := Subgroup.mem_map.1 hy
    exact Subgroup.mem_inf.2 ⟨(Pim.subtype p).2,
      hEM (Pim.subtype p) (Subgroup.mem_comap.1 p.2)⟩
  have hQp : IsPGroup 5 ((P : Subgroup ↥Pim).map g) := P.isPGroup'.map g
  have hQcyc : IsCyclic ↥((P : Subgroup ↥Pim).map g) := hcyc _ hQle hQp
  have hPcyc : IsCyclic ↥P :=
    (Subgroup.equivMapOfInjective (P : Subgroup ↥Pim) g hginj).isCyclic.mpr hQcyc
  have hEcyc : IsCyclic ↥E :=
    isCyclic_of_surjective (G' := ↥P) φ hφsurj
  have hEncyc : ¬ IsCyclic ↥E := by
    intro hc
    obtain ⟨y, hy⟩ := IsCyclic.exists_generator (α := ↥E)
    have hord : orderOf y = Nat.card ↥E := orderOf_eq_card_of_forall_mem_zpowers hy
    have hy5 : y ^ 5 = 1 := Subtype.ext (by simpa using hE.2 y.1 y.2)
    have hdvd : orderOf y ∣ 5 := orderOf_dvd_of_pow_eq_one hy5
    have hle : orderOf y ≤ 5 := Nat.le_of_dvd (by norm_num) hdvd
    rw [show Nat.card ↥E = 25 from hcard] at hord
    omega
  exact hEncyc hEcyc

end Ctx188

section Certified


theorem fourU34Two_of_inputs (h210 : Asch2_10) (h22 : Asch2_2One) : FourU34Two G := by
  intro h162 h172 h5_4 h5_11 h5_12 h5_13 D V₀ V H i c h2 hK hL g hgT hgK hgi hA
  obtain ⟨L, hLc, hLT, hQ, t, htT, hne⟩ := hL
  have x : Ctx188 D V₀ V H i 3 := c.ctx188_three_AS h162 h5_11 h2
  obtain ⟨M⟩ := exists_modDataE c.hyp.isElemAbelian_eOmegaZ (Hyp183.normalizer_eOmegaZ H D.T)
  have hN : calNIn H D.T = {H ⊓ D.M} := c.calNIn_eq_AS h5_11 h5_13
  have hDT : D.T ≤ H := x.hyp.hyp171.2.1
  have hLH : L ≤ H := hLc.2.2.1
  have hQ' : HasQuotShape L (kerMV V H : Set G) (fun X _ => IsL2 X 2 ∨ IsU3 X 2) := by
    obtain ⟨X, hXg, φ, hφs, hφk, hP⟩ := hQ
    exact ⟨X, hXg, φ, hφs, hφk, Or.inr hP⟩
  have hQbase : HasQuotShape L (kerMV V H : Set G)
      (fun X _ => IsSimpleGroup X ∧ ∃ a b : X, a * b ≠ b * a) := by
    obtain ⟨X, hXg, φ, hφs, hφk, hP⟩ := hQ
    exact ⟨X, hXg, φ, hφs, hφk, w183tp_shape_base (Or.inr hP)⟩
  have hshape : IsU3 ↥(M.img L) 2 :=
    x.br1_shape_transport M hK hLH
      (fun X Y _ _ e h => CFSG.Blueprint.LieModel.of_mulEquiv e h) hQ
  have hr : CFSG.Open.pRank 3 H ≤ 3 := by
    rw [← CFSG.SectionRank.pRank_coe_eq_openPRank 3 H]
    exact (not_concl182_iff.mp h2).1.1
  have hcard := h210 G H D.T (kerMV V H) L x.hyp.kgroup x.hyp.isSylowIn_T hr hLc
    (w183tp_shape_dvd hQ') hLT
  rcases w183tp_asch210_split hcard with hone | ⟨t', ht'T, hne', hall'⟩
  · exact absurd (hone t htT) hne
  · have htwo := x.br1_twoComp M hK hLc hLT hQbase ht'T hne' hall'
    have hT : IsSylowIn 2 (M.img D.T) (M.img H) := x.br1_sylow M
    have htHinv : t'⁻¹ ∈ H := hDT (D.T.inv_mem ht'T)
    have himg2 : M.img (conjSubgroup L t') = cj (M.ρ ⟨t'⁻¹, htHinv⟩) (M.img L) := by
      have h := M.img_conj (A := L) hLH (j := ⟨t'⁻¹, htHinv⟩)
      rw [inv_inv] at h
      exact h.symm
    have hshape₂ : IsU3 ↥(M.img (conjSubgroup L t')) 2 := by
      rw [himg2]
      exact w183fu_isU3_cj _ hshape
    obtain ⟨hL₂c, hQ₂⟩ := w183fu_component_conj hLc (hDT ht'T)
      (fun X Y _ _ e h => CFSG.Blueprint.LieModel.of_mulEquiv e h) hQ
    have hpr := w183fu_pRank_five_gt h22 x.hyp.kgroup hLc hL₂c hne'.symm hQ hQ₂
    have hcyc := w183fu_cyclic_five c h2 hpr
    obtain ⟨E, hE_le, hEab, hEcard⟩ := w183fu_E25 hT htwo hshape hshape₂
    have hXne := w183tp_two_normalizer_ne hT htwo (Or.inr hshape)
    have hTX := le_inf hT.le (w183tp_two_T_normalizes hT htwo)
    have hpre := x.w183fu_preimage_le_M M hN inf_le_left hTX hXne
    exact x.w183fu_false_of_E25 M hcyc hEab hEcard (hE_le.trans inf_le_left)
      (fun j hj => hpre j (hE_le hj))

end Certified

end CFSG.LocalAnalysis.WeakClosure81

end
