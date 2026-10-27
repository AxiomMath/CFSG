module

public import CFSG.Monster.B.TwoA.Amalgam.CosetGraphRoot
public import CFSG.Monster.B.TwoA.Amalgam.EightOrbitsBridge
public import CFSG.Monster.B.TwoA.Amalgam.TypeFour

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Amalgam

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.C2E6Std
open CFSG.LieType.Chevalley.C2E6Std.FieldExtension
open CFSG.LieType.Chevalley.CosetBuilding CFSG.Monster.B.Geometry CFSG.Monster.B.E6.StdF4
open CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Sp8

@[expose] def cvOrbit
    (H : Subgroup Shat) (u : CVert) : Set CVert := {x | ∃ y ∈ H, cvMul u y = x}

theorem mem_cvOrbit_self
    (H : Subgroup Shat) (u : CVert) : u ∈ cvOrbit H u :=
  ⟨1, H.one_mem, cvMul_one u⟩

theorem cvOrbit_eq_of_mem
    {H : Subgroup Shat} {u x : CVert} (hx : x ∈ cvOrbit H u) :
    cvOrbit H x = cvOrbit H u := by
  obtain ⟨y, hy, rfl⟩ := hx
  ext z
  constructor
  · rintro ⟨y', hy', rfl⟩
    exact ⟨y * y', H.mul_mem hy hy', cvMul_mul u y y'⟩
  · rintro ⟨y', hy', rfl⟩
    refine ⟨y⁻¹ * y', H.mul_mem (H.inv_mem hy) hy', ?_⟩
    rw [← cvMul_mul, mul_inv_cancel_left]

@[expose] def nbrPull
    {v : CVert} (iv : cgraph.neighborSet v ≃ rootClass) (A : Set GStar) :
    Set CVert :=
  {x | ∃ hx : x ∈ cgraph.neighborSet v, SemidirectProduct.inl (iv ⟨x, hx⟩ : stdGroup) ∈ A}

section Pull

variable {v : CVert} (iv : cgraph.neighborSet v ≃ rootClass)

theorem nbrPull_subset (A : Set GStar) : nbrPull iv A ⊆ cgraph.neighborSet v :=
  fun _ hx => hx.fst

theorem mem_nbrPull_iff {A : Set GStar} {x : CVert} (hx : x ∈ cgraph.neighborSet v) :
    x ∈ nbrPull iv A ↔ SemidirectProduct.inl (iv ⟨x, hx⟩ : stdGroup) ∈ A :=
  ⟨fun ⟨_, h⟩ => h, fun h => ⟨hx, h⟩⟩

theorem nbrPull_union (A B : Set GStar) : nbrPull iv (A ∪ B) = nbrPull iv A ∪ nbrPull iv B := by
  ext x
  constructor
  · rintro ⟨hx, h | h⟩
    · exact Or.inl ⟨hx, h⟩
    · exact Or.inr ⟨hx, h⟩
  · rintro (⟨hx, h⟩ | ⟨hx, h⟩)
    · exact ⟨hx, Or.inl h⟩
    · exact ⟨hx, Or.inr h⟩

theorem injective_inl_iv :
    Function.Injective fun u : cgraph.neighborSet v => (SemidirectProduct.inl (iv u : stdGroup) :
      GStar) := fun _ _ h =>
  iv.injective (Subtype.ext (SemidirectProduct.inl_injective h))

theorem range_inl_iv :
    Set.range (fun u : cgraph.neighborSet v => (SemidirectProduct.inl (iv u : stdGroup) : GStar)) =
      SemidirectProduct.inl '' rootClass := by
  ext y
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨_, (iv u).2, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨iv.symm ⟨x, hx⟩, congrArg (fun z : rootClass => (SemidirectProduct.inl (z : stdGroup) :
      GStar)) (iv.apply_symm_apply ⟨x, hx⟩)⟩

theorem ncard_nbrPull {A : Set GStar} (hA : A ⊆ SemidirectProduct.inl '' rootClass) :
    (nbrPull iv A).ncard = A.ncard := by
  have e : nbrPull iv A = Subtype.val '' ((fun u : cgraph.neighborSet v =>
      (SemidirectProduct.inl (iv u : stdGroup) : GStar)) ⁻¹' A) := by
    ext x
    constructor
    · rintro ⟨hx, h⟩
      exact ⟨⟨x, hx⟩, h, rfl⟩
    · rintro ⟨u, h, rfl⟩
      exact ⟨u.2, h⟩
  rw [e, Set.ncard_image_of_injective _ Subtype.val_injective,
    Set.ncard_preimage_of_injective_subset_range (injective_inl_iv iv)
      (by rw [range_inl_iv]; exact hA)]

theorem mem_nbrPull_of {A : Set GStar} (u : cgraph.neighborSet v)
    (hu : SemidirectProduct.inl (iv u : stdGroup) ∈ A) : (u : CVert) ∈ nbrPull iv A :=
  ⟨u.2, hu⟩

theorem nbrPull_singleton {u : cgraph.neighborSet v} :
    nbrPull iv {SemidirectProduct.inl (iv u : stdGroup)} = {(u : CVert)} := by
  ext x
  constructor
  · rintro ⟨hx, h⟩
    have h' := injective_inl_iv iv (Set.mem_singleton_iff.1 h)
    exact Set.mem_singleton_iff.2 (congrArg Subtype.val h')
  · rintro rfl
    exact ⟨u.2, rfl⟩

open _root_.Classical in
@[expose] def nbrRoot (u : CVert) : GStar :=
  if hu : u ∈ cgraph.neighborSet v then SemidirectProduct.inl (iv ⟨u, hu⟩ : stdGroup) else 1

theorem nbrRoot_of_mem {u : CVert} (hu : u ∈ cgraph.neighborSet v) :
    nbrRoot iv u = SemidirectProduct.inl (iv ⟨u, hu⟩ : stdGroup) :=
  dite_eq_left hu

theorem mem_nbrPull_iff_nbrRoot {A : Set GStar} {u : CVert} (hu : u ∈ cgraph.neighborSet v) :
    u ∈ nbrPull iv A ↔ nbrRoot iv u ∈ A := by
  rw [mem_nbrPull_iff iv hu, nbrRoot_of_mem iv hu]

theorem nbrRoot_mem_of_mem_nbrPull {A : Set GStar} {u : CVert} (hu : u ∈ nbrPull iv A) :
    nbrRoot iv u ∈ A :=
  (mem_nbrPull_iff_nbrRoot iv hu.fst).1 hu

theorem image_nbrRoot_nbrPull {A : Set GStar} (hA : A ⊆ SemidirectProduct.inl '' rootClass) :
    nbrRoot iv '' nbrPull iv A = A := by
  ext y
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact nbrRoot_mem_of_mem_nbrPull iv hu
  · intro hy
    obtain ⟨r, hr, rfl⟩ := hA hy
    obtain ⟨u, hu⟩ := iv.surjective ⟨r, hr⟩
    have hur : (SemidirectProduct.inl (iv u : stdGroup) : GStar) = SemidirectProduct.inl r := by
      rw [hu]
    refine ⟨u, ⟨u.2, ?_⟩, ?_⟩
    · show (SemidirectProduct.inl (iv u : stdGroup) : GStar) ∈ A
      rw [hur]
      exact hy
    · rw [nbrRoot_of_mem iv u.2]
      exact hur

theorem existsUnique_mem_nbrPull {ι : Type*} {O : ι → Set GStar}
    (hO : ∀ y ∈ SemidirectProduct.inl '' rootClass, ∃! i, y ∈ O i) (x : CVert)
    (hx : x ∈ cgraph.neighborSet v) : ∃! i, x ∈ nbrPull iv (O i) := by
  obtain ⟨i, hi, huniq⟩ := hO _ ⟨_, (iv ⟨x, hx⟩).2, rfl⟩
  exact ⟨i, ⟨hx, hi⟩, fun j ⟨_, hj⟩ => huniq j hj⟩

end Pull

section Transfer

variable {v : CVert} (iv : cgraph.neighborSet v ≃ rootClass) (ρv : vStab v →* GStar)
  (hiv : ∀ (y : vStab v) (u : cgraph.neighborSet v),
    SemidirectProduct.inl (iv (stabAct y u) : stdGroup) =
      (ρv y)⁻¹ * SemidirectProduct.inl (iv u : stdGroup) * ρv y)

include hiv in
theorem cvOrbit_eq_nbrPull {G₀ : Subgroup Shat} (hG₀ : G₀ ≤ vStab v) {H : Subgroup GStar}
    (hH : ∀ γ, γ ∈ H ↔ ∃ (y : Shat) (hy : y ∈ G₀), ρv ⟨y, hG₀ hy⟩ = γ)
    (u : cgraph.neighborSet v) :
    cvOrbit G₀ u = nbrPull iv (conjOrbit H (SemidirectProduct.inl (iv u : stdGroup))) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨(stabAct ⟨y, hG₀ hy⟩ u).2, (ρv ⟨y, hG₀ hy⟩)⁻¹,
      H.inv_mem ((hH _).2 ⟨y, hy, rfl⟩), ?_⟩
    rw [inv_inv]
    exact (hiv ⟨y, hG₀ hy⟩ u).symm
  · rintro ⟨hx, γ, hγ, hγx⟩
    obtain ⟨y, hy, hyγ⟩ := (hH γ⁻¹).1 (H.inv_mem hγ)
    refine ⟨y, hy, ?_⟩
    have h1 := hiv ⟨y, hG₀ hy⟩ u
    rw [hyγ, inv_inv, hγx] at h1
    have h2 := injective_inl_iv iv h1
    exact congrArg Subtype.val h2

end Transfer

section Shift

variable {s : Shat}

theorem cvMul_cvMul_eq_iff
    (x : CVert) (y : Shat) :
    cvMul (cvMul x s) y = cvMul x s ↔ cvMul x (s * y * s⁻¹) = x := by
  constructor
  · intro h
    rw [cvMul_mul, cvMul_mul, h, cvMul_inv_cancel]
  · intro h
    rw [← cvMul_mul, show s * y = (s * y * s⁻¹) * s by group, cvMul_mul, h]

theorem stabToEam_coe
    {v : CVert} (hs : cvMul cv0 s = v) (y : vStab v) :
    ((stabToEam hs y : Eam) : Dfull) = ((s * y * s⁻¹ : Shat) : Dfull) := rfl

theorem conj_toS_mem_vStab
    {v : CVert} (hs : cvMul cv0 s = v) (e : Eam) :
    s⁻¹ * toS e * s ∈ vStab v := by
  rw [mem_vStab, ← hs, cvMul_cvMul_eq_iff, show s * (s⁻¹ * toS e * s) * s⁻¹ = toS e by group]
  exact cvMul_cv0_toS e

theorem stabToEam_conj_toS
    {v : CVert} (hs : cvMul cv0 s = v) (e : Eam) :
    stabToEam hs ⟨s⁻¹ * toS e * s, conj_toS_mem_vStab hs e⟩ = e := by
  apply Subtype.ext
  rw [stabToEam_coe]
  show ((s * (s⁻¹ * toS e * s) * s⁻¹ : Shat) : Dfull) = e
  rw [show s * (s⁻¹ * toS e * s) * s⁻¹ = toS e by group, coe_toS]

variable (θ : Eam ⧸ Subgroup.zpowers cE' ≃* GStar)

theorem rhoV_conj_toS
    {v : CVert} (hs : cvMul cv0 s = v) (p : Pc 0) :
    rhoV θ hs ⟨s⁻¹ * toS ⟨p, Pc_le_Eam 0 p.2⟩ * s, conj_toS_mem_vStab hs _⟩ = rho1 θ p := by
  rw [rhoV_apply, stabToEam_conj_toS]
  rfl

theorem mem_map_q4P_iff
    {k : Jhat} (hk0 : cvOf (jhatS k) ≠ cv0)
    (hk : ¬ cgraph.Adj cv0 (cvOf (jhatS k))) {v : CVert} (hs : cvMul cv0 s = v) (γ : GStar) :
    γ ∈ (q4P k).map (rho1 θ) ↔ ∃ (y : Shat)
      (hy : y ∈ vStab v ⊓ vStab (cvMul (cvOf (jhatS k)) s)),
      rhoV θ hs ⟨y, (inf_le_left : vStab v ⊓ _ ≤ vStab v) hy⟩ = γ := by
  have hQ := (native_type_four_pair_stabilizer_parabolic_projection k hk0 hk).1
  constructor
  · rintro ⟨q, hq, rfl⟩
    have hq' : (q : Dfull) ∈ Q4 k := hq
    set e : Eam := ⟨q, Pc_le_Eam 0 q.2⟩
    have hfix := (hQ (toS e)).2 hq'
    refine ⟨s⁻¹ * toS e * s, Subgroup.mem_inf.2 ⟨conj_toS_mem_vStab hs e, ?_⟩,
      rhoV_conj_toS θ hs q⟩
    rw [mem_vStab, cvMul_cvMul_eq_iff, show s * (s⁻¹ * toS e * s) * s⁻¹ = toS e by group]
    exact hfix.2
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨hyv, hyw⟩ := Subgroup.mem_inf.1 hy
    have hyw' := (cvMul_cvMul_eq_iff (s := s) (cvOf (jhatS k)) y).1 hyw
    have hyv' : cvMul cv0 (s * y * s⁻¹) = cv0 := by
      rw [mem_vStab, ← hs, cvMul_cvMul_eq_iff] at hyv
      exact hyv
    have hq := (hQ (s * y * s⁻¹)).1 ⟨hyv', hyw'⟩
    refine ⟨⟨_, Q4_le_P1 hq⟩, hq, ?_⟩
    rw [rhoV_apply]
    rfl

theorem mem_Pc_zero_of_fix_partner
    {e : Eam} (h : cvMul (cvOf a0S) (toS e) = cvOf a0S) :
    (e : Dfull) ∈ Pc 0 := by
  have h1 : nbr a0_mem_Ehat a0_not_mem_N1 (Quotient.mk _ 1) = cvOf a0S := by
    rw [nbr_mk, toS_one, mul_one]
  rw [← h1, ← nbr_mk_mul, one_mul] at h
  have h2 := nbr_injective a0_mem_Ehat a0_not_mem_N1 h
  have h3 := p1rel_iff.1 (Quotient.exact h2.symm)
  rwa [inv_one, mul_one] at h3

theorem fix_partner_of_mem_Pc_zero
    {e : Eam} (he : (e : Dfull) ∈ Pc 0) :
    cvMul (cvOf a0S) (toS e) = cvOf a0S := by
  have h := p1Orb_elS a0_mem_Ehat a0_not_mem_N1
  have hm : cvMul (cvOf a0S) (toS e) ∈ p1Orb (cvOf a0S) := ⟨toS e, he, rfl⟩
  rw [h] at hm
  exact hm

variable {f : Chamber ≃ C2E6Std.stdChamber}
  (hadj : ∀ (i : Fin Tag.F4.rank) (x y : Chamber), chamberCS.adj i x y ↔
    stdDistanceF4 (f x) (f y) = 1 ∨ stdDistanceF4 (f x) (f y) = (coxeterSystem .F4).simple i)
  (hfeq : ∀ (z : Chamber) (e : Eam), f (chamberMul z e⁻¹) = θ (QuotientGroup.mk e) • f z)
  (hfB : f baseChamber = c₀)

include hadj hfeq hfB in
theorem mem_parStar_iff_rhoV
    {v : CVert} (hs : cvMul cv0 s = v) (γ : GStar) :
    γ ∈ parStar firstJ ↔ ∃ (y : Shat) (hy : y ∈ vStab v ⊓ vStab (cvMul (cvOf a0S) s)),
      rhoV θ hs ⟨y, (inf_le_left : vStab v ⊓ _ ≤ vStab v) hy⟩ = γ := by
  constructor
  · intro hγ
    obtain ⟨p, rfl⟩ := exists_rho1_eq hadj hfeq hfB hγ
    set e : Eam := ⟨p, Pc_le_Eam 0 p.2⟩
    refine ⟨s⁻¹ * toS e * s, Subgroup.mem_inf.2 ⟨conj_toS_mem_vStab hs e, ?_⟩,
      rhoV_conj_toS θ hs p⟩
    rw [mem_vStab, cvMul_cvMul_eq_iff, show s * (s⁻¹ * toS e * s) * s⁻¹ = toS e by group]
    exact fix_partner_of_mem_Pc_zero p.2
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨hyv, hyv'⟩ := Subgroup.mem_inf.1 hy
    have h1 := (cvMul_cvMul_eq_iff (s := s) (cvOf a0S) y).1 hyv'
    have h2 : cvMul (cvOf a0S) (toS (stabToEam hs ⟨y, hyv⟩)) = cvOf a0S := h1
    have hp := mem_Pc_zero_of_fix_partner h2
    have h3 := rho1_mem_parStar hadj hfeq hfB ⟨_, hp⟩
    rw [rhoV_apply]
    exact h3

end Shift

theorem partner_mem_neighborSet
    {v : CVert} {s : Shat} (hs : cvMul cv0 s = v) :
    cvMul (cvOf a0S) s ∈ cgraph.neighborSet v := by
  rw [← hs]
  exact (cgraph_adj_cvMul cv0 (cvOf a0S) s).2 (adj_cv0_elS a0_mem_Ehat a0_not_mem_N1)

theorem rootV_partner
    (θ : Eam ⧸ Subgroup.zpowers cE' ≃* GStar)
    (hx : θ (QuotientGroup.mk xhatEam) = rootStar)
    (hinj : ∀ e e' : Eam, vtx 0 (chamberOf e) = vtx 0 (chamberOf e') ↔
      (QuotientGroup.mk (e⁻¹ * xhatEam * e) : Eam ⧸ Subgroup.zpowers cE') =
        QuotientGroup.mk (e'⁻¹ * xhatEam * e'))
    {v : CVert} {s : Shat} (hs : cvMul cv0 s = v) :
    (rootV θ hx hinj hs ⟨_, partner_mem_neighborSet hs⟩ : stdGroup) = rootInv := by
  have hu : ((⟨_, partner_mem_neighborSet hs⟩ : cgraph.neighborSet v) : CVert) =
      cvMul (nbr a0_mem_Ehat a0_not_mem_N1 (Quotient.mk _ 1)) s := by
    show cvMul (cvOf a0S) s = _
    rw [nbr_mk, toS_one, mul_one]
  rw [rootV_eq_of_coe θ hx hinj hs hu]
  apply inl_injective
  rw [inl_rootPt_mk, rho0_apply]
  show θ (QuotientGroup.mk (1⁻¹ * xhatEam * 1)) = rootStar
  rw [inv_one, one_mul, mul_one, hx]

end CFSG.Monster.B.TwoA.Amalgam
