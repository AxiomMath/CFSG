module

public import CFSG.Quasithin.EmptyFaithful.SzF53DichB1
public import CFSG.Quasithin.EmptyFaithful.SzF53DichB2
public import CFSG.Quasithin.EmptyFaithful.SzF53DichNat
public import CFSG.Quasithin.EmptyFaithful.SzF53B1Main
public import CFSG.Quasithin.EmptyFaithful.SzF53B2E
public import CFSG.Quasithin.EmptyFaithful.SzF53B3Main2
public import CFSG.Quasithin.EmptyFaithful.SzF53A3

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.Quasithin.F53 CFSG.Quasithin.F53Mod
open CFSG.Quasithin.CosetGeom

theorem F53Dichotomy2.noE (hD : F53Dichotomy2) {G : Type} [Group G] [Finite G]
    {H M S : Subgroup G} (hA : F53Amalgam H M S) {E : Subgroup G} (hE : F53EData H S E) :
    False := by
  have hd := hD G H M S hA
  obtain ⟨α, hα⟩ := exists_bAt_eq_bMin hA
  have hb := bMin_pos hA
  cases hv : vtype α with
  | false =>
    have h0 : bAt (γ₀ (H ⊔ M) H M) = bMin H M := (bAt_γ₀_eq hv).trans hα
    have hmod := hd.s5_module _ h0 vtype_γ₀
    rw [Zv_γ₀_eq hA, stab_γ₀ hA.amalgam.le₁] at hmod
    by_cases h1 : bMin H M = 1
    · have hz := hd.zv_central _ _ adj_γ₀_γ₁ h0
      have hfacts := zaFacts_of_modelSec hA.amalgam.sylow₁ hA.quot_left hmod.1
      exact (F53B1.B1Hyp.of_bAt hA (by rw [h0, h1]) hz hfacts).not_F53EData hE
    · have hnat := hmod.2 (by omega)
      exact not_F53EData_of_natural hA hE hnat hnat.irred
        (fun ho => not_isOrthSec_and_isNatSec ho hnat)
  | true =>
    have h1 : bAt (γ₁ (H ⊔ M) H M) = bMin H M := (bAt_γ₁_eq hv).trans hα
    have hr := hd.s3_range _ h1 vtype_γ₁
    by_cases h2 : bMin H M = 2
    · have hz := hd.zv_central _ _ adj_γ₀_γ₁.symm h1
      exact (SzF53B2.B2Setup.of_bAt hA h2 h1 hz).not_F53EData hE
    · exact F53B3.no_E_of_dich2 hA hd (by omega) h1 hE

theorem f53AmalgamStatement_of_dichotomy2 (h : F53Dichotomy2) : F53AmalgamStatement :=
  f53AmalgamStatement_iff_noE.mpr fun _ _ _ _ _ _ hA _ hE => h.noE hA hE

theorem input15208F53Res_of_dichotomy2 (h : F53Dichotomy2) : Input15208F53Res :=
  input15208F53Res_of_amalgam (f53AmalgamStatement_of_dichotomy2 h)

end CFSG.Quasithin
