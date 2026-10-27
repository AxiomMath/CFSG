module

public import CFSG.Quasithin.Vol2.GoldschmidtF45RuMain
public import CFSG.Quasithin.Vol2.GoldschmidtF431TitsGeoSetting

public noncomputable section

namespace CFSG.Quasithin.TitsGeo

open CFSG.Quasithin CFSG.Sporadic.Schreier.Tits CFSG.Quasithin.RuType CFSG.Quasithin.H13.F45Ru
  CFSG.Quasithin.H13.F431.F45

local notation "TA" => CFSG.Sporadic.Schreier.Tits.titsA

section Action

instance octActionD : MulAction ↥titsD Vtx :=
  MulAction.compHom Vtx (Subgroup.inclusion titsD_le_titsA)

theorem dsmul_inl (g : ↥titsD) (p : Fin 1755) : g • (Sum.inl p : Vtx) = Sum.inl (g.1 p) := rfl

theorem dsmul_inr (g : ↥titsD) (v : Fin 2925) :
    g • (Sum.inr v : Vtx) = Sum.inr (titsLineHom (Subgroup.inclusion titsD_le_titsA g) v) := rfl

instance octGraphActionD : GraphAction ↥titsD octGraph where
  adj_smul g a b := GraphAction.adj_smul (Subgroup.inclusion titsD_le_titsA g) a b

end Action

section Phi

@[expose] def phiD : ↥titsD →* titsSetting.ι.G0 where
  toFun x := ⟨⟨x.1, by rw [titsH_sup_N]; exact x.2⟩, by
    rw [titsSetting.ι.gen]
    exact Subgroup.mem_top _⟩
  map_one' := rfl
  map_mul' _ _ := rfl

@[expose] def toPermD (k : titsSetting.ι.G0) : Equiv.Perm (Fin 1755) :=
  Subtype.val (Subtype.val k)

theorem toPermD_phiD (x : ↥titsD) : toPermD (phiD x) = x.1 := rfl

theorem phiD_injective : Function.Injective phiD := fun x y h =>
  Subtype.ext (by simpa [toPermD_phiD] using congrArg toPermD h)

theorem phiD_surjective : Function.Surjective phiD := by
  rintro ⟨⟨σ, hσ⟩, hg⟩
  exact ⟨⟨σ, by rw [← titsH_sup_N]; exact hσ⟩, rfl⟩

theorem mem_range_φ1_iff (k : titsSetting.ι.G0) :
    ((k : titsSetting.Yb) ∈ titsSetting.ι.φ1.range) ↔ toPermD k ∈ titsH := by
  constructor
  · rintro ⟨h, hh⟩
    have := congrArg Subtype.val hh
    rw [toPermD, ← this]
    exact h.2
  · intro h
    exact ⟨⟨_, h⟩, rfl⟩

theorem mem_range_φ2_iff (k : titsSetting.ι.G0) :
    ((k : titsSetting.Yb) ∈ titsSetting.ι.φ2.range) ↔ toPermD k ∈ titsN := by
  constructor
  · rintro ⟨h, hh⟩
    have := congrArg Subtype.val hh
    rw [toPermD, ← this]
    exact h.2
  · intro h
    exact ⟨⟨_, h⟩, rfl⟩

end Phi

section Datum

theorem xdatumD (h00 : (0 : Fin 1755) ∈ titsLine (0 : Fin 2925)) :
    XDatum titsSetting phiD octGraph (Sum.inl 0 : Vtx) (Sum.inr 0 : Vtx) where
  inj := phiD_injective
  N_eq := (MonoidHom.range_eq_top.2 phiD_surjective).symm
  dec g := by
    obtain ⟨y, rfl⟩ := phiD_surjective g
    exact ⟨y, 1, one_smul _ _, one_smul _ _, (mul_one _).symm⟩
  stab1 y := by
    rw [smul_xv_iff', mem_range_φ1_iff, dsmul_inl, Sum.inl.injEq, toPermD_phiD]
    constructor
    · intro h
      have := (mem_titsH_iff).1 h
      exact Fin.ext (by rw [this.2])
    · intro h
      exact (mem_titsH_iff).2 ⟨y.2, by rw [h]⟩
  stab2 y := by
    rw [smul_lv_iff', mem_range_φ2_iff, dsmul_inr, Sum.inr.injEq, toPermD_phiD, lineHom_eq_iff]
    constructor
    · intro h
      exact J47.line_fix_of_mem_titsN h
    · intro h
      exact J47.mem_titsN_of y.2 h
  disj y z := by
    rw [dsmul_inl, dsmul_inr]
    exact Sum.inl_ne_inr
  noadj1 y z := by
    rw [dsmul_inl, dsmul_inl]
    exact fun h => h
  noadj2 y z := by
    rw [dsmul_inr, dsmul_inr]
    exact fun h => h
  adj12 := h00

end Datum

end CFSG.Quasithin.TitsGeo
