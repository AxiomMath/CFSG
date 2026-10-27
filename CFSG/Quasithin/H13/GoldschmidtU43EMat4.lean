module

public import CFSG.Quasithin.H13.GoldschmidtU43EMat3
public import CFSG.Quasithin.H13.GoldschmidtU43ENorm9

public section

namespace CFSG.Quasithin.H13.U43

open CFSG.Quasithin CFSG.Open CFSG.Quasithin.H13.A5.Orth CFSG.Quasithin.H13.A6

variable {G : Type} [Group G]

namespace JWSetup

variable [Finite G] {z : G} (S : JWSetup z) (r : S.Rho)

noncomputable def chiN (n : ↥S.Ng) : Mat3 :=
  Classical.choose (exists_matrix (fun _ => S.pow_three_M _) (evC_basis_bijective r)
    (S.conjM n n.2))

theorem chiN_rep (n : ↥S.Ng) : IsRep (basis r) (S.conjM n n.2) (S.chiN r n) :=
  Classical.choose_spec (exists_matrix (fun _ => S.pow_three_M _) (evC_basis_bijective r)
    (S.conjM n n.2))

theorem conjM_mul (a b : ↥S.Ng) :
    S.conjM ((a * b : ↥S.Ng) : G) (a * b).2 = (S.conjM a a.2).comp (S.conjM b b.2) := by
  ext m
  show ((a : G) * b) * (m : G) * ((a : G) * b)⁻¹ = (a : G) * ((b : G) * m * (b : G)⁻¹) * (a : G)⁻¹
  group

theorem chiN_mul (a b : ↥S.Ng) : S.chiN r (a * b) = S.chiN r a * S.chiN r b := by
  have h1 := (S.chiN_rep r a).comp (S.chiN_rep r b)
  rw [← S.conjM_mul] at h1
  exact (IsRep.unique (evC_basis_bijective r) (S.chiN_rep r (a * b)) h1)

theorem chiN_one : S.chiN r 1 = 1 := by
  have h : S.conjM ((1 : ↥S.Ng) : G) (1 : ↥S.Ng).2 = MonoidHom.id ↥S.Mg := by
    ext m
    show (1 : G) * (m : G) * (1 : G)⁻¹ = m
    group
  have h1 := S.chiN_rep r 1
  rw [h] at h1
  exact IsRep.unique (evC_basis_bijective r) h1 IsRep.one

theorem chiN_z : S.chiN r ⟨z, S.z_mem_Ng⟩ = Zmat :=
  IsRep.unique (evC_basis_bijective r) (S.chiN_rep r _) (S.isRep_z r)

theorem chiN_u : S.chiN r ⟨(S.u : G), S.u_mem_Ng⟩ = Umat :=
  IsRep.unique (evC_basis_bijective r) (S.chiN_rep r _) (S.isRep_u r)

theorem chiN_v : S.chiN r ⟨(S.v : G), S.v_mem_Ng⟩ = Vmat :=
  IsRep.unique (evC_basis_bijective r) (S.chiN_rep r _) (S.isRep_v r)

theorem chiN_of_mem_Mg (n : ↥S.Ng) (hn : (n : G) ∈ S.Mg) : S.chiN r n = 1 := by
  have h : S.conjM (n : G) n.2 = MonoidHom.id ↥S.Mg := by
    ext m
    show (n : G) * (m : G) * (n : G)⁻¹ = m
    rw [mul_inv_eq_iff_eq_mul]
    exact (S.abelian_Mg m m.2 n hn).symm
  have h1 := S.chiN_rep r n
  rw [h] at h1
  exact IsRep.unique (evC_basis_bijective r) h1 IsRep.one

theorem chiN_eq_one_iff (n : ↥S.Ng) : S.chiN r n = 1 ↔ (n : G) ∈ S.Mg := by
  refine ⟨fun h => ?_, S.chiN_of_mem_Mg r n⟩
  apply S.centralizer_Mg
  intro m hm
  have h1 : ∀ a, S.conjM n n.2 (evC (basis r) a) = evC (basis r) ((1 : Mat3).mulVec a) := by
    have h0 := S.chiN_rep r n
    rw [h] at h0
    exact h0
  have h2 : S.conjM n n.2 ⟨m, hm⟩ = ⟨m, hm⟩ := by
    have := h1 (Classical.choose ((evC_basis_bijective r).2 ⟨m, hm⟩))
    have e := Classical.choose_spec ((evC_basis_bijective r).2 ⟨m, hm⟩)
    rw [Matrix.one_mulVec, e] at this
    exact this
  have h3 := congrArg Subtype.val h2
  have h4 : (n : G) * m * (n : G)⁻¹ = m := h3
  rw [mul_inv_eq_iff_eq_mul] at h4
  exact h4.symm

@[expose] noncomputable def chiHom : ↥S.Ng →* Mat3 where
  toFun := S.chiN r
  map_one' := S.chiN_one r
  map_mul' := S.chiN_mul r

@[expose] noncomputable def chiBarU : S.Nbar →* Mat3ˣ :=
  QuotientGroup.lift (S.Mg.subgroupOf S.Ng) (S.chiHom r).toHomUnits (by
    intro n hn
    exact Units.ext (S.chiN_of_mem_Mg r n hn))

@[expose] noncomputable def chiBar (g : S.Nbar) : Mat3 := ((S.chiBarU r g : Mat3ˣ) : Mat3)

theorem chiBar_piN (n : ↥S.Ng) : S.chiBar r (S.piN n) = S.chiN r n := by
  unfold chiBar chiBarU
  rw [show S.piN n = (n : S.Nbar) from rfl, QuotientGroup.lift_mk]
  rfl

theorem chiBar_mul (a b : S.Nbar) : S.chiBar r (a * b) = S.chiBar r a * S.chiBar r b := by
  unfold chiBar
  rw [map_mul, Units.val_mul]

theorem chiBar_one : S.chiBar r 1 = 1 := by
  unfold chiBar
  rw [map_one, Units.val_one]

theorem chiBar_eq_one_iff (g : S.Nbar) : S.chiBar r g = 1 ↔ g = 1 := by
  obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective g
  constructor
  · intro h
    have h1 : S.chiN r n = 1 := h
    have h2 : (n : G) ∈ S.Mg := (S.chiN_eq_one_iff r n).mp h1
    exact (QuotientGroup.eq_one_iff n).mpr h2
  · intro h
    have h2 : (n : G) ∈ S.Mg := (QuotientGroup.eq_one_iff n).mp h
    exact S.chiN_of_mem_Mg r n h2

theorem chiBar_injective : Function.Injective (S.chiBar r) := by
  intro a b hab
  have h1 : S.chiBar r (a * b⁻¹) = 1 := by
    rw [S.chiBar_mul r, hab, ← S.chiBar_mul r, mul_inv_cancel, S.chiBar_one r]
  exact mul_inv_eq_one.mp ((S.chiBar_eq_one_iff r _).mp h1)

noncomputable abbrev ubar : S.Nbar := S.piN ⟨(S.u : G), S.u_mem_Ng⟩

noncomputable abbrev vbar : S.Nbar := S.piN ⟨(S.v : G), S.v_mem_Ng⟩

theorem chiBar_zbar : S.chiBar r S.zbar = Zmat := (S.chiBar_piN r _).trans (S.chiN_z r)

theorem chiBar_ubar : S.chiBar r S.ubar = Umat := (S.chiBar_piN r _).trans (S.chiN_u r)

theorem chiBar_vbar : S.chiBar r S.vbar = Vmat := (S.chiBar_piN r _).trans (S.chiN_v r)

theorem ubar_sq : S.ubar * S.ubar = 1 := by
  rw [← map_mul, ← map_one S.piN]
  congr 1
  have h : (S.u : G) * (S.u : G) = 1 := congrArg Subtype.val S.uu
  exact Subtype.ext h

theorem vbar_sq : S.vbar * S.vbar = S.zbar := by
  rw [← map_mul]
  congr 1
  exact Subtype.ext S.v_sq

theorem ubar_vbar : S.ubar * S.vbar * S.ubar⁻¹ = S.vbar⁻¹ := by
  rw [← map_inv, ← map_mul, ← map_mul, ← map_inv]
  congr 1
  have h : (S.u : G) * (S.v : G) * (S.u : G)⁻¹ = (S.v : G)⁻¹ := congrArg Subtype.val S.u_conj_v
  exact Subtype.ext h

theorem vbar_pow_four : S.vbar ^ 4 = 1 := by
  rw [u43_pow_four, S.vbar_sq, S.zbar_sq]

theorem vbar_sq_ne_one : S.vbar ^ 2 ≠ 1 := by
  rw [pow_two, S.vbar_sq]
  exact S.zbar_ne_one

end JWSetup

end CFSG.Quasithin.H13.U43
