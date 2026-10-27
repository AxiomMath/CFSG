module

public import CFSG.Monster.B.TwoA.Amalgam.CosetGraphRoot

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Amalgam

open CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Sp8
  CFSG.Monster.B.E6 CFSG.Monster.B.E6.StdF4 CFSG.LieType.Chevalley.C2E6Std
  CFSG.LieType.Chevalley.C2E6Std.FieldExtension

theorem mem_zpowers_conj_iff {G : Type*} [Group G] (g c x : G) :
    x ∈ Subgroup.zpowers (g⁻¹ * c * g) ↔ g * x * g⁻¹ ∈ Subgroup.zpowers c := by
  have hconj : ∀ k : ℤ, (g⁻¹ * c * g) ^ k = g⁻¹ * c ^ k * g := fun k => by
    have h := conj_zpow (i := k) (a := g⁻¹) (b := c)
    rwa [inv_inv] at h
  simp only [Subgroup.mem_zpowers_iff, hconj]
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k, by rw [← hk]; group⟩
  · rintro ⟨k, hk⟩
    exact ⟨k, by rw [hk]; group⟩

theorem rhoV_eq_one_iff
    (θ : Eam ⧸ Subgroup.zpowers cE' ≃* GStar) {v : CVert} {s : Shat}
    (hs : cvMul cv0 s = v) (y : vStab v) :
    rhoV θ hs y = 1 ↔ ((y : Shat) : Dfull) ∈ Subgroup.zpowers (clabel v) := by
  rw [rhoV_apply, rho0_apply, MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff,
    mem_zpowers_subtype_iff, clabel_eq_conj hs, mem_zpowers_conj_iff]
  rfl

@[expose] def nbrLabelS
    (s : Shat) (e : Eam) : Shat := s⁻¹ * toS (cE' * xconj e) * s

theorem coe_nbrLabelS
    (s : Shat) (e : Eam) :
    ((nbrLabelS s e : Shat) : Dfull) =
      clabel (cvMul (nbr a0_mem_Ehat a0_not_mem_N1 (Quotient.mk _ e)) s) := by
  rw [clabel_cvMul, clabel_nbr, nbrLabelS]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_toS, coe_xhatEam]
  rfl

theorem nbrLabelS_mem_vStab
    {v : CVert} {s : Shat} (hs : cvMul cv0 s = v) (e : Eam) :
    nbrLabelS s e ∈ vStab v := by
  rw [mem_vStab, ← hs, nbrLabelS, ← cvMul_mul,
    show s * (s⁻¹ * toS (cE' * xconj e) * s) = toS (cE' * xconj e) * s by group, cvMul_mul,
    cvMul_cv0_toS]

theorem exists_vStab_eq_clabel
    {v : CVert} {s : Shat} (hs : cvMul cv0 s = v)
    (z : cgraph.neighborSet v) : ∃ y : vStab v, ((y : Shat) : Dfull) = clabel z := by
  obtain ⟨e, he⟩ := nbrShift_symm_mk hs z
  exact ⟨⟨nbrLabelS s e, nbrLabelS_mem_vStab hs e⟩, (coe_nbrLabelS s e).trans (by rw [he])⟩

theorem rhoV_eq_of_clabel
    (θ : Eam ⧸ Subgroup.zpowers cE' ≃* GStar) {v : CVert} {s : Shat}
    (hs : cvMul cv0 s = v) (iv : cgraph.neighborSet v ≃ rootClass)
    (hiv : ∀ (e : Eam) (h : cvMul (nbr a0_mem_Ehat a0_not_mem_N1 (Quotient.mk _ e)) s ∈
        cgraph.neighborSet v),
      SemidirectProduct.inl (iv ⟨_, h⟩ : stdGroup) = θ (QuotientGroup.mk (xconj e)))
    (z : cgraph.neighborSet v) (y : vStab v) (hy : ((y : Shat) : Dfull) = clabel z) :
    rhoV θ hs y = SemidirectProduct.inl (iv z : stdGroup) := by
  obtain ⟨e, he⟩ := nbrShift_symm_mk hs z
  have hz : cvMul (nbr a0_mem_Ehat a0_not_mem_N1 (Quotient.mk _ e)) s ∈ cgraph.neighborSet v :=
    he ▸ z.2
  have hzeq : z = ⟨_, hz⟩ := Subtype.ext he
  have hst : stabToEam hs y = cE' * xconj e := by
    apply Subtype.ext
    show ((s * y * s⁻¹ : Shat) : Dfull) = ((cE' * xconj e : Eam) : Dfull)
    have h1 : ((y : Shat) : Dfull) = ((nbrLabelS s e : Shat) : Dfull) := by
      rw [hy, coe_nbrLabelS, ← he]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [h1, nbrLabelS]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_toS]
    group
  have hmk : (QuotientGroup.mk (cE' * xconj e) : Eam ⧸ Subgroup.zpowers cE') =
      QuotientGroup.mk (xconj e) := by
    rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff cE').2 (Subgroup.mem_zpowers _), one_mul]
  rw [rhoV_apply, rho0_apply, hst, hmk, ← hiv e hz, hzeq]

section General

variable (θ : Eam ⧸ Subgroup.zpowers cE' ≃* GStar)
  (hx : θ (QuotientGroup.mk xhatEam) = rootStar)
  (hinj : ∀ e e' : Eam, vtx 0 (chamberOf e) = vtx 0 (chamberOf e') ↔
    (QuotientGroup.mk (e⁻¹ * xhatEam * e) : Eam ⧸ Subgroup.zpowers cE') =
      QuotientGroup.mk (e'⁻¹ * xhatEam * e'))
  (hcomm : ∀ e e' : Eam,
    ((∃ x, (vtx 0 (chamberOf e) ∩ vtx 3 x).Nonempty ∧ (vtx 0 (chamberOf e') ∩ vtx 3 x).Nonempty) ↔
      Commute (QuotientGroup.mk (e⁻¹ * xhatEam * e) : Eam ⧸ Subgroup.zpowers cE')
        (QuotientGroup.mk (e'⁻¹ * xhatEam * e'))))

include hinj in
theorem inl_rootV_nbr
    {v : CVert} {s : Shat} (hs : cvMul cv0 s = v) (e : Eam)
    (h : cvMul (nbr a0_mem_Ehat a0_not_mem_N1 (Quotient.mk _ e)) s ∈ cgraph.neighborSet v) :
    SemidirectProduct.inl (rootV θ hx hinj hs ⟨_, h⟩ : stdGroup) =
      θ (QuotientGroup.mk (xconj e)) :=
  (congrArg (fun z : rootClass => (SemidirectProduct.inl (z : stdGroup) : GStar))
    (rootV_nbr θ hx hinj hs e h)).trans (inl_rootPt_mk θ hx e)

include θ hx hinj hcomm in
theorem local_label_root_of
    (v : CVert) :
    ∃ (ρ : vStab v →* GStar) (iv : cgraph.neighborSet v ≃ rootClass),
      Function.Surjective ρ ∧
      (∀ y : vStab v, ρ y = 1 ↔ ((y : Shat) : Dfull) ∈ Subgroup.zpowers (clabel v)) ∧
      (∀ y : Shat, (cvMul v y = v ∧ ∀ u ∈ cgraph.neighborSet v, cvMul u y = u) ↔
        (y : Dfull) ∈ Subgroup.zpowers (clabel v)) ∧
      orderOf (clabel v) = 2 ∧
      (∀ (g : vStab v) (z : cgraph.neighborSet v),
        SemidirectProduct.inl (iv (stabAct g z) : stdGroup) =
          (ρ g)⁻¹ * SemidirectProduct.inl (iv z : stdGroup) * ρ g) ∧
      (∀ z z' : cgraph.neighborSet v, z ≠ z' →
        (cgraph.Adj z z' ↔ Commute (iv z : stdGroup) (iv z'))) ∧
      (∀ z : cgraph.neighborSet v, ∃ y : vStab v, ((y : Shat) : Dfull) = clabel z) ∧
      ∀ (z : cgraph.neighborSet v) (y : vStab v), ((y : Shat) : Dfull) = clabel z →
        ρ y = SemidirectProduct.inl (iv z : stdGroup) := by
  obtain ⟨s, hs⟩ := cvMul_transitive cv0 v
  exact ⟨rhoV θ hs, rootV θ hx hinj hs, rhoV_surjective θ hs, rhoV_eq_one_iff θ hs,
    kernel_iff θ hx hs, orderOf_clabel v, inl_rootV_stabAct θ hx hinj hs,
    fun _ _ hne => adj_iff_commute_rootV θ hx hinj hcomm hs hne, exists_vStab_eq_clabel hs,
    rhoV_eq_of_clabel θ hs _ (inl_rootV_nbr θ hx hinj hs)⟩

end General

theorem native_local_label_root
    (v : CVert) :
    ∃ (ρ : vStab v →* GStar) (iv : cgraph.neighborSet v ≃ rootClass),
      Function.Surjective ρ ∧
      (∀ y : vStab v, ρ y = 1 ↔ ((y : Shat) : Dfull) ∈ Subgroup.zpowers (clabel v)) ∧
      (∀ y : Shat, (cvMul v y = v ∧ ∀ u ∈ cgraph.neighborSet v, cvMul u y = u) ↔
        (y : Dfull) ∈ Subgroup.zpowers (clabel v)) ∧
      orderOf (clabel v) = 2 ∧
      (∀ (g : vStab v) (z : cgraph.neighborSet v),
        SemidirectProduct.inl (iv (stabAct g z) : stdGroup) =
          (ρ g)⁻¹ * SemidirectProduct.inl (iv z : stdGroup) * ρ g) ∧
      (∀ z z' : cgraph.neighborSet v, z ≠ z' →
        (cgraph.Adj z z' ↔ Commute (iv z : stdGroup) (iv z'))) ∧
      (∀ z : cgraph.neighborSet v, ∃ y : vStab v, ((y : Shat) : Dfull) = clabel z) ∧
      ∀ (z : cgraph.neighborSet v) (y : vStab v), ((y : Shat) : Dfull) = clabel z →
        ρ y = SemidirectProduct.inl (iv z : stdGroup) := by
  obtain ⟨θ, -, -, -, -, -, hx, -, hinj, hcomm⟩ := native_F4_point_root_involution_intertwiner
  exact local_label_root_of θ hx hinj hcomm v

end CFSG.Monster.B.TwoA.Amalgam
