module

public import CFSG.RankThree.GF2n.Stroth80.HeringSec63Bar

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.Open

variable {G : Type} [Group G] {M Q : Subgroup G} [(Q.subgroupOf M).Normal]

theorem exists_barRep {S : Subgroup G} (x : ↥(bar M Q S)) :
    ∃ s : ↥S, (s : G) ∈ M ∧ HS6.piM M Q (s : G) = x := by
  obtain ⟨g, hgS, hgM, hg⟩ := (HS6.mem_bar (S := S) x.1).mp x.2
  exact ⟨⟨g, hgS⟩, hgM, hg⟩

noncomputable def barRep {S : Subgroup G} (x : ↥(bar M Q S)) : ↥S :=
  (exists_barRep x).choose

theorem barRep_mem {S : Subgroup G} (x : ↥(bar M Q S)) : (barRep x : G) ∈ M :=
  (exists_barRep x).choose_spec.1

theorem piM_barRep {S : Subgroup G} (x : ↥(bar M Q S)) :
    HS6.piM M Q (barRep x : G) = x := (exists_barRep x).choose_spec.2

private theorem piM_barRep_mul {S : Subgroup G} (x y : ↥(bar M Q S)) :
    HS6.piM M Q ((barRep x * barRep y : ↥S) : G) =
      HS6.piM M Q (barRep (x * y) : G) := by
  rw [Subgroup.coe_mul, HS6.piM_mul (barRep_mem x) (barRep_mem y),
    piM_barRep x, piM_barRep y, piM_barRep (x * y)]
  rfl

private theorem inv_mul_barRep_mem {S : Subgroup G} (x y : ↥(bar M Q S)) :
    (((barRep x * barRep y)⁻¹ * barRep (x * y) : ↥S) : G) ∈ Q := by
  have hmul : ((barRep x * barRep y : ↥S) : G) ∈ M := by
    rw [Subgroup.coe_mul]
    exact M.mul_mem (barRep_mem x) (barRep_mem y)
  have hpi := (HS6.piM_eq_iff hmul (barRep_mem (x * y))).mp (piM_barRep_mul x y)
  simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using hpi

theorem barRep_map_mul {S : Subgroup G} {H : Type*} [Monoid H] (f : ↥S →* H)
    (hf : ∀ s : ↥S, (s : G) ∈ Q → f s = 1) (x y : ↥(bar M Q S)) :
    f (barRep (x * y)) = f (barRep x) * f (barRep y) := by
  have hq : (((barRep x * barRep y)⁻¹ * barRep (x * y) : ↥S) : G) ∈ Q :=
    inv_mul_barRep_mem x y
  have hfq : f ((barRep x * barRep y)⁻¹ * barRep (x * y)) = 1 := hf _ hq
  have hsplit : (barRep x * barRep y) *
      ((barRep x * barRep y)⁻¹ * barRep (x * y)) = barRep (x * y) := by group
  rw [← hsplit, f.map_mul, hfq, mul_one]
  exact f.map_mul _ _

theorem barRep_map_one {S : Subgroup G} {H : Type*} [Monoid H] (f : ↥S →* H)
    (hf : ∀ s : ↥S, (s : G) ∈ Q → f s = 1) : f (barRep (1 : ↥(bar M Q S))) = 1 := by
  have hpi : HS6.piM M Q (barRep (1 : ↥(bar M Q S)) : G) = 1 := by
    rw [piM_barRep]
    simp
  exact hf _ ((HS6.piM_eq_one_iff (barRep_mem _)).mp hpi)

noncomputable def barLift {S : Subgroup G} {H : Type*} [Monoid H] (f : ↥S →* H)
    (hf : ∀ s : ↥S, (s : G) ∈ Q → f s = 1) : ↥(bar M Q S) →* H where
  toFun x := f (barRep x)
  map_one' := barRep_map_one f hf
  map_mul' := barRep_map_mul f hf

theorem barLift_piM {S : Subgroup G} {H : Type*} [Monoid H] (f : ↥S →* H)
    (hf : ∀ s : ↥S, (s : G) ∈ Q → f s = 1) (s : ↥S) (hs : (s : G) ∈ M)
    (h : HS6.piM M Q (s : G) ∈ bar M Q S) :
    barLift f hf ⟨HS6.piM M Q (s : G), h⟩ = f s := by
  have hb : barLift f hf ⟨HS6.piM M Q (s : G), h⟩ =
      f (barRep ⟨HS6.piM M Q (s : G), h⟩) := rfl
  have hpi : HS6.piM M Q (barRep ⟨HS6.piM M Q (s : G), h⟩ : G) =
      HS6.piM M Q (s : G) :=
    piM_barRep (S := S) ⟨HS6.piM M Q (s : G), h⟩
  have hq : (((barRep ⟨HS6.piM M Q (s : G), h⟩)⁻¹ * s : ↥S) : G) ∈ Q := by
    have hkey := (HS6.piM_eq_iff (barRep_mem _) hs).mp hpi
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using hkey
  have hfq : f ((barRep ⟨HS6.piM M Q (s : G), h⟩)⁻¹ * s) = 1 := hf _ hq
  have hsplit : barRep ⟨HS6.piM M Q (s : G), h⟩ *
      ((barRep ⟨HS6.piM M Q (s : G), h⟩)⁻¹ * s) = s := by group
  have hfr : f (barRep ⟨HS6.piM M Q (s : G), h⟩) =
      f (barRep ⟨HS6.piM M Q (s : G), h⟩ *
        ((barRep ⟨HS6.piM M Q (s : G), h⟩)⁻¹ * s)) := by
    rw [f.map_mul, hfq, mul_one]
  rw [hb, hfr, hsplit]

end CFSG.RankThree.GF2n.Stroth80
