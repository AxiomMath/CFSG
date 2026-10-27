module

public import CFSG.Monster.Existence.EbNative

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Existence

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.Generated CFSG.Monster.B.Short
  CFSG.Monster.B.Rep4371 CFSG.Monster.B CFSG.Monster.VisCert CFSG.Monster.VisQuot
  CFSG.Monster.ScalarKernel CFSG.Monster.B.TwoA.Census

theorem eb_mul_self_of_comm {G : Type*} [Group G] {c r : G} (hcc : c * c = 1) (hrr : r * r = 1)
    (hrc : r * c = c * r) : c * r * (c * r) = 1 := by
  calc c * r * (c * r) = c * (r * c) * r := by simp only [mul_assoc]
    _ = c * (c * r) * r := by rw [hrc]
    _ = (c * c) * (r * r) := by simp only [mul_assoc]
    _ = 1 := by rw [hcc, hrr, mul_one]

theorem eb_eq_of_mul_eq_one {G : Type*} [Group G] {c r : G} (hcc : c * c = 1) (h : c * r = 1) :
    r = c := by
  rw [eq_inv_of_mul_eq_one_right h, inv_eq_of_mul_eq_one_right hcc]

theorem isConj_xGriess_rhoGriess
    {s : Q} (hss : s * s = 1) (hs1 : s ≠ 1)
    (hsh : ¬ IsShortCoord (coordOf s)) : IsConj xGriess (rhoGriess s) := by
  have hmem : rhoEquiv s ∈ involQmat :=
    (rho_mem_involQmat_iff s).2 ⟨hs1, (mul_self_eq_one_iff_qL s).1 hss⟩
  rw [involQmat_eq] at hmem
  rcases hmem with (h | h) | h
  · have h' : rhoGriess s = xGriess := Subtype.ext (Set.mem_singleton_iff.1 h)
    exact h'.symm ▸ IsConj.refl _
  · obtain ⟨r', hr', hrs⟩ := h
    exact absurd (rhoEquiv_injective hrs ▸ hr') hsh
  · obtain ⟨g, hg, hgs⟩ := exists_Gmat_conj_xmat h
    exact isConj_iff.2 ⟨⟨g, Gmat_le_AutO hg⟩, Subtype.ext hgs⟩

theorem eb_rhoGriess_rOneTwo : rhoGriess rOneTwo = tGriess * uGriess := by
  rw [← rTwo_mul_rStar, rhoGriess_mul, rhoGriess_rStar, rhoGriess_rTwo]

theorem eb_rhoGriess_mem_FE_iff {q : Q} :
    rhoGriess q ∈ FE ↔ q = 1 ∨ q = rStar ∨ q = rTwo ∨ q = rOneTwo := by
  constructor
  · rintro (h | h | h | h)
    · exact .inl (rhoGriess_injective (h.trans rhoGriess_one.symm))
    · exact .inr (.inl (rhoGriess_injective (h.trans rhoGriess_rStar.symm)))
    · exact .inr (.inr (.inl (rhoGriess_injective (h.trans rhoGriess_rTwo.symm))))
    · exact .inr (.inr (.inr (rhoGriess_injective (h.trans eb_rhoGriess_rOneTwo.symm))))
  · rintro (rfl | rfl | rfl | rfl)
    · exact .inl rhoGriess_one
    · exact .inr (.inl rhoGriess_rStar)
    · exact .inr (.inr (.inl rhoGriess_rTwo))
    · exact .inr (.inr (.inr eb_rhoGriess_rOneTwo))

theorem eb_rhoGriess_comm {q q' : Q} (h : q * q' = q' * q) :
    rhoGriess q * rhoGriess q' = rhoGriess q' * rhoGriess q := by
  rw [← rhoGriess_mul, ← rhoGriess_mul, h]

theorem eb_comm_of_mem_centralizer_FE {r : Q}
    (h : rhoGriess r ∈ Subgroup.centralizer (FE : Set MGriess)) :
    r * rStar = rStar * r ∧ r * rTwo = rTwo * r := by
  have ht : tGriess ∈ FE := mem_FE.2 (Or.inr (Or.inl rfl))
  have hu : uGriess ∈ FE := mem_FE.2 (Or.inr (Or.inr (Or.inl rfl)))
  have h1 := Subgroup.mem_centralizer_iff.1 h tGriess ht
  have h2 := Subgroup.mem_centralizer_iff.1 h uGriess hu
  rw [← rhoGriess_rStar, ← rhoGriess_mul, ← rhoGriess_mul] at h1
  rw [← rhoGriess_rTwo, ← rhoGriess_mul, ← rhoGriess_mul] at h2
  exact ⟨rhoGriess_injective h1, rhoGriess_injective h2⟩

theorem eb_rStar_mul_self : rStar * rStar = 1 := by
  rw [← pow_two]
  exact sq_eq_one_of_isShort isShortCoord_rStar

theorem eb_rTwo_mul_self : rTwo * rTwo = 1 := by
  rw [← pow_two]
  exact sq_eq_one_of_isShort isShortCoord_rTwo

theorem eb_rOneTwo_mul_self : rOneTwo * rOneTwo = 1 := by
  rw [← pow_two]
  exact sq_eq_one_of_isShort isShortCoord_rOneTwo

theorem phi0_coordOf_rOneTwo' :
    phi0 (coordOf rOneTwo) = phi0 (coordOf rStar) + phi0 (coordOf rTwo) := by
  rw [← rStar_mul_rTwo, phi0_coordOf_mul]

theorem exists_isConj_rho_mul
    {r : Q} (hrr : r * r = 1) (hrt : r * rStar = rStar * r)
    (hru : r * rTwo = rTwo * r) (hF : ¬ (r = 1 ∨ r = rStar ∨ r = rTwo ∨ r = rOneTwo)) :
    ∃ c : Q, (c = 1 ∨ c = rStar ∨ c = rTwo ∨ c = rOneTwo) ∧ IsConj xGriess (rhoGriess (c * r)) := by
  have hro : r * rOneTwo = rOneTwo * r := by
    rw [← rStar_mul_rTwo]
    exact (Commute.mul_right (show Commute r rStar from hrt) (show Commute r rTwo from hru)).eq
  have key : ∀ c : Q, c * c = 1 → r * c = c * r → (c = 1 ∨ c = rStar ∨ c = rTwo ∨ c = rOneTwo) →
      (c * r) * (c * r) = 1 ∧ c * r ≠ 1 := fun c hcc hrc hc =>
    ⟨eb_mul_self_of_comm (G := Q) hcc hrr hrc, fun h => hF (by
      have h' : r = c := eb_eq_of_mul_eq_one (G := Q) hcc h
      rw [h']
      exact hc)⟩
  by_contra hno
  push Not at hno
  have hshort : ∀ c : Q, c * c = 1 → r * c = c * r →
      (c = 1 ∨ c = rStar ∨ c = rTwo ∨ c = rOneTwo) → IsShortCoord (coordOf (c * r)) := by
    intro c hcc hrc hc
    by_contra hsh
    obtain ⟨h1, h2⟩ := key c hcc hrc hc
    exact hno c hc (isConj_xGriess_rhoGriess h1 h2 hsh)
  have s0 := hshort 1 (mul_one 1) (by rw [one_mul, mul_one]) (Or.inl rfl)
  have s1 := hshort rStar eb_rStar_mul_self hrt (Or.inr (Or.inl rfl))
  have s2 := hshort rTwo eb_rTwo_mul_self hru (Or.inr (Or.inr (Or.inl rfl)))
  have s3 := hshort rOneTwo eb_rOneTwo_mul_self hro (Or.inr (Or.inr (Or.inr rfl)))
  have mem : ∀ {x : Q}, IsShortCoord (coordOf x) → phi0 (coordOf x) ∈ shortSet := fun h => h
  refine case1_sound case1OK_eq_true (v := phi0 (coordOf r)) ?_ ?_ ?_ ?_ ?_ ?_
  · exact mem (by simpa using s0)
  · rw [vecX_ebCodeA, bL_comm]
    exact (commute_iff_bL _ _).1 hrt.symm
  · rw [vecX_ebCodeB, bL_comm]
    exact (commute_iff_bL _ _).1 hru.symm
  · rw [vecX_ebCodeA, add_comm, ← phi0_coordOf_mul]
    exact mem s1
  · rw [vecX_ebCodeB, add_comm, ← phi0_coordOf_mul]
    exact mem s2
  · rw [vecX_ebCodeA, vecX_ebCodeB, ← phi0_coordOf_rOneTwo', add_comm, ← phi0_coordOf_mul]
    exact mem s3

theorem eb_case_one
    {e : MGriess}
    (he : e ∈ Subgroup.centralizer (FE : Set MGriess) ⊓
      Subgroup.centralizer ({xGriess} : Set MGriess))
    (hee : e * e = 1) (heF : e ∉ FE)
    (hπ : piVis ⟨(e : SpaceB ≃ₗ[ℚ] SpaceB), mem_Gvis_of_mem_cent_xGriess he.2⟩ = 1) :
    ∃ f ∈ FE, IsConj xGriess (e * f) := by
  obtain ⟨r, hr⟩ := (piVis_eq_one_iff _).1 hπ
  have her : e = rhoGriess r := Subtype.ext hr.symm
  subst her
  have hrr : r * r = 1 := by
    apply rhoGriess_injective
    rw [rhoGriess_mul, hee, rhoGriess_one]
  obtain ⟨hrt, hru⟩ := eb_comm_of_mem_centralizer_FE he.1
  obtain ⟨c, hc, hconj⟩ :=
    exists_isConj_rho_mul hrr hrt hru fun h => heF (eb_rhoGriess_mem_FE_iff.2 h)
  have hcF : rhoGriess c ∈ FE := eb_rhoGriess_mem_FE_iff.2 hc
  exact ⟨rhoGriess c, hcF, by rwa [← rhoGriess_mul]⟩

end CFSG.Monster.Existence
