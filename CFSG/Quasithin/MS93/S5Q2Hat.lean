module

public import CFSG.Quasithin.MS93.S5A56Hat
public import CFSG.Quasithin.MS93.S5Q2X
public import CFSG.Quasithin.MS93.S33SpS5
public import CFSG.Quasithin.MS93.S5BAux
public import CFSG.Quasithin.MS93.S5BBasic

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement Matrix Pointwise

namespace S5Q2

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}
  {F : Type} [Field F] [Fintype F] {a : ↥M →* ↥(StatedSp 2 F)}

theorem commute_iff_mulVec (h : PUHyp M T L) (hd : S5.IsSp4Data M T L 1 F a)
    (nv : S5.NatVec M T L a) (m : ↥M) (u : ↥(Uq M T L)) :
    (m : G) * u = u * m ↔ MSP.mat (a m) *ᵥ nv.vec u = nv.vec u := by
  have hlift := (sp4Lift_holds G M T L h 1 F _ _ a hd).2.2
  have hMU : M ≤ Subgroup.normalizer (Uq M T L : Set G) := le_normalizer_Uq h.le_normalizer
  refine ⟨nv.mat_mulVec_vec_of_commute m u, fun hfix => ?_⟩
  have hmu : (m : G) * u * (m : G)⁻¹ ∈ Uq M T L :=
    (Subgroup.mem_normalizer_iff.1 (hMU m.2) u).1 u.2
  have h2 : nv.vec ⟨(m : G) * u * (m : G)⁻¹, hmu⟩ = nv.vec u := by
    rw [nv.vec_conj m u hmu]; exact hfix
  have h3 : nv.toVec (⟨(m : G) * u * (m : G)⁻¹, hmu⟩ * u⁻¹) = 1 := by
    rw [map_mul, map_inv]
    apply Multiplicative.toAdd.injective
    rw [toAdd_mul, toAdd_inv, toAdd_one]
    have : Multiplicative.toAdd (nv.toVec ⟨(m : G) * u * (m : G)⁻¹, hmu⟩) =
        Multiplicative.toAdd (nv.toVec u) := h2
    rw [this, add_neg_cancel]
  have h4 := ((nv.ker_iff _).1 h3).2
  have h5 := hlift m m.2 u u.2 h4
  calc (m : G) * u = m * u * (m : G)⁻¹ * m := by group
    _ = u * m := by rw [h5]

omit [Finite G] [Fintype F] in
theorem transv_mulVec_eq_iff {c : MSP.V4 F} (hc : c ≠ 0) (v : MSP.V4 F) :
    MSP.mat (MSP.transv c 1) *ᵥ v = v ↔ MSP.form F c v = 0 := by
  rw [MSP.transv_mulVec, one_mul, add_eq_left, smul_eq_zero]
  exact ⟨fun h' => h'.resolve_right hc, fun h' => Or.inl h'⟩

theorem commute_iff_of_isHatTriple (h : PUHyp M T L) (hd : S5.IsSp4Data M T L 1 F a)
    (hq : Nat.card F = 2) {μ : Vtx (puAmalgam h.le)} (hc : IsCritical _ μ (baseA (puAmalgam h.le)))
    {s₁ s₂ s₃ : (puAmalgam h.le).Universal} (ht : S5.IsHatTriple _ μ (baseA _) s₁ s₂ s₃)
    (hn : s₃ ∉ Subgroup.closure ({s₁, s₂} : Set (puAmalgam h.le).Universal) ⊔
      Qv _ (baseA (puAmalgam h.le)))
    {z : (puAmalgam h.le).Universal} (hz : z ∈ ZM _ (baseA (puAmalgam h.le))) :
    (s₃ * z = z * s₃) ↔ ((s₁ * z = z * s₁) ↔ (s₂ * z = z * s₂)) := by
  have := hd.charP
  obtain ⟨c₁, c₂, hc₁, hc₂, hc₁₂, -, he₁, he₂, he₃⟩ := S5.hat_centers h hd hq hc ht
  have ht' := ht
  have hyp := h.hyp20
  have hb0 := h.critDist_pos
  have hLn : (L.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.L_le).2 h.le_normalizer
  have hcr := ms22_iii _ hyp hb0 h.centHyp hc
  have hadj := adj_geo_one_of_isCritical _ hb0 hcr
  obtain ⟨hs₁, hs₂, hs₃, -⟩ := ht
  have hZ := S5B.zm_eq_zh_sup_uSub h (isMVtx_baseA _) hadj
  have hεst : Qv _ (geo _ (baseA (puAmalgam h.le)) μ 1) ≤ stab _ (baseA (puAmalgam h.le)) :=
    qv_le_stab_of_adj _ hadj.symm
  have hn' : ZH _ (geo _ (baseA (puAmalgam h.le)) μ 1) ≤
      Subgroup.normalizer (S5.uSub h.le L (baseA _) : Set (puAmalgam h.le).Universal) :=
    ((PU.omegaOneCenterOf_le _).trans hεst).trans
      (le_normalizer_commutator (stab_le_normalizer_zm _ _)
        (stab_le_normalizer_puTrans h.le hLn _))
  have hz' : z ∈ ((ZH _ (geo _ (baseA (puAmalgam h.le)) μ 1) : Set (puAmalgam h.le).Universal) *
      (S5.uSub h.le L (baseA _) : Set (puAmalgam h.le).Universal)) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right _ _ hn', ← hZ]
    exact hz
  obtain ⟨w, hw, u, hu, rfl⟩ := hz'
  have hwc : ∀ s ∈ Qv _ (geo _ (baseA (puAmalgam h.le)) μ 1), s * w = w * s := fun s hs =>
    Subgroup.mem_centralizer_iff.1 ((PU.omegaOneCenterOf_le_centerOf _ hw).2) s hs
  have hred : ∀ s ∈ Qv _ (geo _ (baseA (puAmalgam h.le)) μ 1),
      (s * (w * u) = w * u * s ↔ s * u = u * s) := fun s hs => by
    rw [← mul_assoc, hwc s hs, mul_assoc, mul_assoc]
    exact ⟨fun h' => mul_left_cancel h', fun h' => by rw [h']⟩
  rw [hred s₃ hs₃, hred s₁ hs₁, hred s₂ hs₂]
  have hst := S5.ofA_range_eq h.le
  obtain ⟨m₁, rfl⟩ : s₁ ∈ (puAmalgam h.le).ofA.range := hst ▸ hεst hs₁
  obtain ⟨m₂, rfl⟩ : s₂ ∈ (puAmalgam h.le).ofA.range := hst ▸ hεst hs₂
  obtain ⟨m₃, rfl⟩ : s₃ ∈ (puAmalgam h.le).ofA.range := hst ▸ hεst hs₃
  rw [S5B.uSub_baseA h] at hu
  obtain ⟨u₀, hu₀, rfl⟩ := hu
  obtain ⟨nv⟩ := hd.nonempty_natVec
  have hcomm : ∀ m : ↥M, ((puAmalgam h.le).ofA m * (puAmalgam h.le).ofA u₀ =
      (puAmalgam h.le).ofA u₀ * (puAmalgam h.le).ofA m ↔ (m : G) * u₀ = u₀ * m) := fun m => by
    rw [← map_mul, ← map_mul]
    constructor
    · intro h'
      exact congrArg Subtype.val ((puAmalgam h.le).ofA_injective h')
    · intro h'
      exact congrArg _ (Subtype.ext h')
  set u₁ : ↥(Uq M T L) := ⟨u₀, Subgroup.mem_subgroupOf.1 hu₀⟩
  rw [hcomm, hcomm, hcomm, commute_iff_mulVec h hd nv m₃ u₁, commute_iff_mulVec h hd nv m₁ u₁,
    commute_iff_mulVec h hd nv m₂ u₁, he₁ m₁ rfl, he₂ m₂ rfl, he₃ _ _ _ ht' hn m₃ rfl]
  have hc₃ : c₁ + c₂ ≠ 0 := by
    intro h0
    apply hc₁₂
    have : c₁ = -c₂ := eq_neg_of_add_eq_zero_left h0
    rw [this, CharTwo.neg_eq]
  rw [transv_mulVec_eq_iff hc₃, transv_mulVec_eq_iff hc₁, transv_mulVec_eq_iff hc₂,
    LinearMap.map_add₂]
  obtain ⟨e⟩ := MSP.nonempty_ringEquiv_of_card_two hq
  rcases MSP.eq_zero_or_eq_one_of_ringEquiv e (MSP.form F c₁ (nv.vec u₁)) with h1 | h1 <;>
    rcases MSP.eq_zero_or_eq_one_of_ringEquiv e (MSP.form F c₂ (nv.vec u₁)) with h2 | h2 <;>
    simp [h1, h2, CharTwo.add_self_eq_zero]

theorem not_mem_commutator_of_pair (h : PUHyp M T L) (hd : S5.IsSp4Data M T L 1 F a)
    {α' : Vtx (puAmalgam h.le)} (hc : IsCritical _ (baseA (puAmalgam h.le)) α')
    {t t' : (puAmalgam h.le).Universal}
    (ht : t ∈ Qv _ (geo _ α' (baseA (puAmalgam h.le)) 1))
    (h12 : ZM _ (baseA (puAmalgam h.le)) ⊔ Qv _ α' =
      Subgroup.closure ({t, t'} : Set (puAmalgam h.le).Universal) ⊔ Qv _ α')
    {y₀ : ↥M} (hy : (puAmalgam h.le).ofA y₀ ∈ ZM _ α')
    (hy' : t' * (puAmalgam h.le).ofA y₀ = (puAmalgam h.le).ofA y₀ * t')
    (hyt : ¬ t * (puAmalgam h.le).ofA y₀ = (puAmalgam h.le).ofA y₀ * t) :
    a y₀ ∉ commutator (MSP.Sp4 F) := by
  have hyp := h.hyp20
  have hb0 := h.critDist_pos
  have hα' : IsMVtx _ α' := hc.isMVtx_right _ hyp
  have hrel := S5.relIndex_zm_le_two_of_pair h hc ht h12 hy hy'
  rw [puAmalgam.zm_baseA h.le, S5B.relIndex_centralizer_ofA h.le (Z0q_le M T) y₀] at hrel
  have hne : (Subgroup.centralizer ({(y₀ : G)} : Set G)).relIndex (Z0q M T) ≠ 0 :=
    Subgroup.FiniteIndex.index_ne_zero
  have hrelU : (Subgroup.centralizer ({(y₀ : G)} : Set G)).relIndex (Uq M T L) ≤ 2 :=
    (Subgroup.relIndex_le_of_le_right (Uq_le_Z0q h.L_le) hne).trans hrel
  have hy2 : ∃ e : ℕ, (y₀ : G) ^ 2 ^ e = 1 := by
    refine ⟨1, ?_⟩
    have h2 := (isElemAbelian_zm _ hyp hb0 hα').2 _ hy
    rw [← map_pow] at h2
    have h2' : y₀ ^ 2 = 1 := (puAmalgam h.le).ofA_injective (by rw [h2, map_one])
    simpa using congrArg Subtype.val h2'
  have hyO : (y₀ : G) ∉ pCoreOf 2 M := by
    intro hO
    apply hyt
    have hyQ : (puAmalgam h.le).ofA y₀ ∈ Qv _ (baseA (puAmalgam h.le)) := by
      rw [S5B.qv_baseA_eq h]
      exact ⟨y₀, Subgroup.mem_subgroupOf.2 hO, rfl⟩
    have hle : Subgroup.closure ({t, t'} : Set (puAmalgam h.le).Universal) ⊔ Qv _ α' ≤
        Subgroup.centralizer ({(puAmalgam h.le).ofA y₀} : Set _) := by
      rw [← h12]
      refine sup_le (fun x hx => ?_) (fun x hx => ?_)
      · exact Subgroup.mem_centralizer_singleton_iff.2
          ((Subgroup.mem_centralizer_iff.1
            (zm_le_centralizer_qv _ hyp (isMVtx_baseA _) hx) _ hyQ).symm)
      · exact Subgroup.mem_centralizer_singleton_iff.2
          (Subgroup.mem_centralizer_iff.1 (zm_le_centralizer_qv _ hyp hα' hy) x hx)
    have htc := hle (Subgroup.mem_sup_left (Subgroup.subset_closure (Set.mem_insert t _)))
    exact Subgroup.mem_centralizer_singleton_iff.1 htc
  exact not_mem_commutator_of_relIndex_le_two h hd hy2 hyO hrelU

end S5Q2

theorem S5.hatEven_holds :
    ∀ (G : Type) [Group G] [Finite G] (M T L : Subgroup G) (h : PUHyp M T L),
      PUMin M T L → 2 < critDist (puAmalgam h.le) →
      ∀ (k : ℕ) (F : Type) (_ : Field F) (_ : Fintype F) (a : ↥M →* ↥(StatedSp 2 F)),
        IsSp4Data M T L k F a →
        ∀ α' : Vtx (puAmalgam h.le), IsCritical _ (baseA _) α' →
          ∀ t₁ t₂ t₃ : (puAmalgam h.le).Universal, IsHatTriple _ (baseA _) α' t₁ t₂ t₃ →
            t₃ ∉ Subgroup.closure ({t₁, t₂} : Set (puAmalgam h.le).Universal) ⊔ Qv _ α' →
            vIm h.le a (zHat _ (baseA _) α') ≤ commutator ↥(StatedSp 2 F) := by
  intro G _ _ M T L h hmin hb k F _ _ a hd α' hc t₁ t₂ t₃ ht hn
  obtain ⟨hk1, -, -, -⟩ := S33.of_isHatTriple h hd hc ht
  subst hk1
  have hq : Nat.card F = 2 := by rw [Nat.card_eq_fintype_card, hd.2.1, pow_one]
  have hyp := h.hyp20
  have hb0 := h.critDist_pos
  have hα' : IsMVtx _ α' := hc.isMVtx_right _ hyp
  rw [S5.zHat_eq_of_isHatTriple h hd hq hc ht hn]
  obtain ⟨c, hcα'⟩ := exists_eq_smul_baseA _ hα'
  have hgα' : c⁻¹ • α' = baseA (puAmalgam h.le) := by rw [hcα', inv_smul_smul]
  have key : ∀ z ∈ ZM (puAmalgam h.le) α',
      (t₃ * z = z * t₃ ↔ (t₁ * z = z * t₁ ↔ t₂ * z = z * t₂)) := by
    intro z hz
    have hcrit : IsCritical _ (c⁻¹ • baseA (puAmalgam h.le)) (baseA _) := by
      have := (isCritical_smul _ c⁻¹ _ _).2 hc
      rwa [hgα'] at this
    have hT := (S5.isHatTriple_smul _ c⁻¹ _ _ t₁ t₂ t₃).2 ht
    rw [hgα'] at hT
    have hN := (S5.conj_mem_closure_pair_sup_qv c⁻¹ α' t₁ t₂ t₃).not.2 hn
    rw [hgα'] at hN
    have hz' : c⁻¹ * z * c⁻¹⁻¹ ∈ ZM (puAmalgam h.le) (baseA _) := by
      rw [← hgα', zm_smul]
      exact ⟨z, hz, rfl⟩
    have k := S5Q2.commute_iff_of_isHatTriple h hd hq hcrit hT hN hz'
    have hconj : ∀ t : (puAmalgam h.le).Universal,
        (c⁻¹ * t * c⁻¹⁻¹ * (c⁻¹ * z * c⁻¹⁻¹) = c⁻¹ * z * c⁻¹⁻¹ * (c⁻¹ * t * c⁻¹⁻¹) ↔
          t * z = z * t) := fun t => by
      constructor
      · intro h'
        have h'' : c⁻¹ * (t * z) * c⁻¹⁻¹ = c⁻¹ * (z * t) * c⁻¹⁻¹ := by
          calc c⁻¹ * (t * z) * c⁻¹⁻¹ = c⁻¹ * t * c⁻¹⁻¹ * (c⁻¹ * z * c⁻¹⁻¹) := by group
            _ = c⁻¹ * z * c⁻¹⁻¹ * (c⁻¹ * t * c⁻¹⁻¹) := h'
            _ = c⁻¹ * (z * t) * c⁻¹⁻¹ := by group
        simpa using h''
      · intro h'
        calc c⁻¹ * t * c⁻¹⁻¹ * (c⁻¹ * z * c⁻¹⁻¹) = c⁻¹ * (t * z) * c⁻¹⁻¹ := by group
          _ = c⁻¹ * (z * t) * c⁻¹⁻¹ := by rw [h']
          _ = c⁻¹ * z * c⁻¹⁻¹ * (c⁻¹ * t * c⁻¹⁻¹) := by group
    rwa [hconj, hconj, hconj] at k
  have ht' := ht
  obtain ⟨ht₁, ht₂, -, hi₁, hi₂, hi₃, -, h12, -⟩ := ht'
  have h21 : ZM _ (baseA (puAmalgam h.le)) ⊔ Qv _ α' =
      Subgroup.closure ({t₂, t₁} : Set (puAmalgam h.le).Universal) ⊔ Qv _ α' := by
    rw [Set.pair_comm]
    exact h12
  have hZst : ZM _ α' ≤ stab (puAmalgam h.le) (baseA _) := zm_le_stab_of_isCritical _ hyp hb0 hc
  have hst := S5.ofA_range_eq h.le
  have : Finite ↥(ZM (puAmalgam h.le) α') := by
    have hf : Finite ↥(stab (puAmalgam h.le) (baseA _)) := by
      rw [puAmalgam.stab_baseA]
      exact S5B.finite_imM h.le M
    exact Finite.of_injective _ (Subgroup.inclusion_injective hZst)
  rintro g ⟨z₀, hz₀, rfl⟩
  obtain ⟨hzZ, hz3⟩ := Subgroup.mem_inf.1 hz₀
  have hz3' : t₃ * (puAmalgam h.le).ofA z₀ = (puAmalgam h.le).ofA z₀ * t₃ :=
    (Subgroup.mem_centralizer_singleton_iff.1 hz3).symm
  have hk := (key _ hzZ).1 hz3'
  by_cases h1 : t₁ * (puAmalgam h.le).ofA z₀ = (puAmalgam h.le).ofA z₀ * t₁
  ·
    have h2 := hk.1 h1
    have hle : Subgroup.closure ({t₁, t₂} : Set (puAmalgam h.le).Universal) ⊔ Qv _ α' ≤
        Subgroup.centralizer ({(puAmalgam h.le).ofA z₀} : Set _) := by
      refine sup_le ((Subgroup.closure_le _).2 ?_) (fun x hx => ?_)
      · rintro u (rfl | rfl)
        · exact Subgroup.mem_centralizer_singleton_iff.2 h1
        · exact Subgroup.mem_centralizer_singleton_iff.2 h2
      · exact Subgroup.mem_centralizer_singleton_iff.2
          (Subgroup.mem_centralizer_iff.1 (zm_le_centralizer_qv _ hyp hα' hzZ) x hx)
    rw [← h12] at hle
    obtain ⟨nv⟩ := hd.nonempty_natVec
    have ha1 : a z₀ = 1 := by
      refine MSP.ext_mulVec fun w => ?_
      obtain ⟨u, hu⟩ := nv.surj (Multiplicative.ofAdd w)
      have huv : nv.vec u = w := by rw [S5.NatVec.vec, hu]; rfl
      have huM : (u : G) ∈ M := Uq_le h.L_le u.2
      have huZ : (puAmalgam h.le).ofA ⟨u, huM⟩ ∈ ZM (puAmalgam h.le) (baseA _) := by
        rw [puAmalgam.zm_baseA h.le]
        exact ⟨⟨u, huM⟩, Subgroup.mem_subgroupOf.2 (Uq_le_Z0q h.L_le u.2), rfl⟩
      have hc' := Subgroup.mem_centralizer_singleton_iff.1 (hle (Subgroup.mem_sup_left huZ))
      rw [← map_mul, ← map_mul] at hc'
      have hcG : (z₀ : G) * u = u * z₀ :=
        (congrArg Subtype.val ((puAmalgam h.le).ofA_injective hc')).symm
      rw [MSP.mat_one, Matrix.one_mulVec, ← huv]
      exact nv.mat_mulVec_vec_of_commute z₀ u hcG
    rw [ha1]
    exact one_mem _
  ·
    have h2 : ¬ t₂ * (puAmalgam h.le).ofA z₀ = (puAmalgam h.le).ofA z₀ * t₂ :=
      fun h2 => h1 (hk.2 h2)
    obtain ⟨z₁, hz₁Z, hz₁2, hz₁1⟩ : ∃ z₁ ∈ ZM (puAmalgam h.le) α', t₂ * z₁ = z₁ * t₂ ∧
        ¬ t₁ * z₁ = z₁ * t₁ := by
      by_contra hne
      push Not at hne
      set Z := ZM (puAmalgam h.le) α'
      set H₁ := Subgroup.centralizer ({t₁} : Set (puAmalgam h.le).Universal)
      set H₂ := Subgroup.centralizer ({t₂} : Set (puAmalgam h.le).Universal)
      have hsub : H₂ ⊓ Z ≤ H₁ ⊓ Z := by
        rintro y ⟨hy2, hyZ⟩
        refine ⟨Subgroup.mem_centralizer_singleton_iff.2 ?_, hyZ⟩
        exact (hne y hyZ (Subgroup.mem_centralizer_singleton_iff.1 hy2).symm).symm
      have hmul := Subgroup.relIndex_mul_relIndex (H₂ ⊓ Z) (H₁ ⊓ Z) Z hsub inf_le_right
      rw [Subgroup.inf_relIndex_right, Subgroup.inf_relIndex_right, hi₁, hi₂] at hmul
      have h1' : (H₂ ⊓ Z).relIndex (H₁ ⊓ Z) = 1 := by omega
      have hsub' := Subgroup.relIndex_eq_one.1 h1'
      have hall : Z ≤ Subgroup.centralizer ({t₃} : Set (puAmalgam h.le).Universal) := by
        intro y hy
        refine Subgroup.mem_centralizer_singleton_iff.2 ((key y hy).2 ⟨fun hy1 => ?_,
          fun hy2 => ?_⟩).symm
        · have := hsub' ⟨Subgroup.mem_centralizer_singleton_iff.2 hy1.symm, hy⟩
          exact (Subgroup.mem_centralizer_singleton_iff.1 this.1).symm
        · exact hne y hy hy2
      have := Subgroup.relIndex_eq_one.2 hall
      omega
    obtain ⟨z₁₀, rfl⟩ : z₁ ∈ (puAmalgam h.le).ofA.range := hst ▸ hZst hz₁Z
    set z₂₀ : ↥M := z₁₀⁻¹ * z₀ with hz₂₀
    have hz₂Z : (puAmalgam h.le).ofA z₂₀ ∈ ZM (puAmalgam h.le) α' := by
      rw [hz₂₀, map_mul, map_inv]
      exact mul_mem (inv_mem hz₁Z) hzZ
    have hrel₁ : (Subgroup.centralizer ({t₁} : Set (puAmalgam h.le).Universal)).relIndex
        (ZM (puAmalgam h.le) α') ≤ 2 := hi₁.le
    have hz₂1 : t₁ * (puAmalgam h.le).ofA z₂₀ = (puAmalgam h.le).ofA z₂₀ * t₁ := by
      have hm := S5B.inv_mul_mem_of_relIndex_le_two hrel₁ (by omega) hz₁Z hzZ
        (fun h' => hz₁1 (Subgroup.mem_centralizer_singleton_iff.1 h').symm)
        (fun h' => h1 (Subgroup.mem_centralizer_singleton_iff.1 h').symm)
      rw [hz₂₀, map_mul, map_inv]
      exact (Subgroup.mem_centralizer_singleton_iff.1 hm).symm
    have hz₂2 : ¬ t₂ * (puAmalgam h.le).ofA z₂₀ = (puAmalgam h.le).ofA z₂₀ * t₂ := by
      intro h'
      apply h2
      have e : (puAmalgam h.le).ofA z₀ =
          (puAmalgam h.le).ofA z₁₀ * (puAmalgam h.le).ofA z₂₀ := by
        rw [hz₂₀, map_mul, map_inv, mul_inv_cancel_left]
      rw [e]
      calc t₂ * ((puAmalgam h.le).ofA z₁₀ * (puAmalgam h.le).ofA z₂₀)
          = (t₂ * (puAmalgam h.le).ofA z₁₀) * (puAmalgam h.le).ofA z₂₀ := by group
        _ = (puAmalgam h.le).ofA z₁₀ * (t₂ * (puAmalgam h.le).ofA z₂₀) := by rw [hz₁2]; group
        _ = _ := by rw [h']; group
    have ho₁ := S5Q2.not_mem_commutator_of_pair h hd hc ht₁ h12 hz₁Z hz₁2 hz₁1
    have ho₂ := S5Q2.not_mem_commutator_of_pair h hd hc ht₂ h21 hz₂Z hz₂1 hz₂2
    have e : z₀ = z₁₀ * z₂₀ := by rw [hz₂₀, mul_inv_cancel_left]
    rw [e, map_mul]
    exact S5Q2.mul_mem_commutator_of_not_mem hd ho₁ ho₂

end CFSG.Quasithin.MS93
