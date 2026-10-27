module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Std4
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Stmt
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35ChBase

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod

namespace F53.Stellmacher

open CosetGeom F53

namespace S35.Lp

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}
  {β α' m γ' : Geo H M}

omit [Finite G] in
theorem back_vtype_m (hp : S34.PD β α') (hb : Back H M β α' m γ') : vtype m = true :=
  Std.vtype_nbr_S5 hp.vδ' hb.1

omit [Finite G] in
theorem back_vtype_γ (hp : S34.PD β α') (hb : Back H M β α' m γ') : vtype γ' = false :=
  Std.vtype_nbr_S3 (back_vtype_m hp hb) hb.2.1

omit [Finite G] in
theorem back_dist_m (hp : S34.PD β α') (hb : Back H M β α' m γ') : dist β m + 2 = bMin H M := by
  have := hp.dist_eq
  have := hb.2.2.1
  omega

omit [Finite G] in
theorem back_dist_γ (hp : S34.PD β α') (hb : Back H M β α' m γ') : dist β γ' + 3 = bMin H M := by
  have := back_dist_m hp hb
  have := hb.2.2.2
  omega

omit [Finite G] in
theorem back_ne (hp : S34.PD β α') (hb : Back H M β α' m γ') : γ' ≠ α' := by
  rintro rfl
  have := back_dist_γ hp hb
  have := hp.dist_eq
  omega

theorem back_Vn_le_Qm (hS : Sit H M S) (hp : S34.PD β α') (hb : Back H M β α' m γ') :
    Vn β ≤ Qv m :=
  Std.Vn_le_Qv_dist hS (by have := back_dist_m hp hb; omega)

theorem back_Vn_le_inf (hS : Sit H M S) (hp : S34.PD β α') (hb : Back H M β α' m γ') :
    Vn β ≤ stab α' ⊓ stab m :=
  le_inf (Std.PD_Vn_le_stab hS hp).1 (back_Vn_le_Qm hS hp hb |>.trans (Ch.Qv_le_stab' m))

theorem back_comm_γ (hS : Sit H M S) (hp : S34.PD β α') (hb : Back H M β α' m γ') :
    ∀ a ∈ Vn β, ∀ b ∈ Vn γ', a * b = b * a :=
  Std.Vn_commute_dist hS (by have := back_dist_γ hp hb; omega)

theorem back_Zv_m (hS : Sit H M S) (hp : S34.PD β α') (hb : Back H M β α' m γ') :
    Zv γ' ⊔ Zv α' = Zv m ∧ Zv γ' ⊓ Zv α' = ⊥ := by
  have := Std.Zv_ne hS (back_vtype_m hp hb) hb.2.1
    (Std.mem_nbrs_symm.mp hb.1) (back_ne hp hb)
  exact ⟨this.2.1, this.2.2⟩

end S35.Lp

end F53.Stellmacher

end CFSG.Quasithin
