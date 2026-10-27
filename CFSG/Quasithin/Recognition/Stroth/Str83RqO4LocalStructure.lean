module

public import CFSG.Quasithin.Recognition.Stroth.Str83RqO4Defs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellNatActual

import CFSG.Quasithin.Recognition.Stroth.Str83RqO4Dictionary
import CFSG.Quasithin.Recognition.Stroth.Str83RqO4Class
import CFSG.Quasithin.Recognition.Stroth.Str83RqO4L2Cover
import CFSG.Quasithin.Recognition.St84.EdgeStabB
import CFSG.Quasithin.Vol2.Ch4Sec1Defs

public section

namespace CFSG.Quasithin.Stroth.Rq

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.QuasithinUnique.Setup.Campbell

variable {G : Type} [Group G] [Finite G]

namespace Track

variable {L1 L2 S : Subgroup G} (t : Track L1 L2 S) {X : Subgroup G}

private theorem EX_le_MX (t : Track L1 L2 S) (X : Subgroup G) :
    t.EX X 1 ≤ t.MX X 1 :=
  le_inf inf_le_right ((inf_le_left : t.EX X 1 ≤ t.Qv 1).trans (t.Qv_le_Gv_self 1))

private theorem MX_le_normalizer_EX (t : Track L1 L2 S) (X : Subgroup G) :
    t.MX X 1 ≤ Subgroup.normalizer (t.EX X 1 : Set G) := by
  rintro m hm
  obtain ⟨hmN, hmG⟩ := Subgroup.mem_inf.mp hm
  have hQ : conjSub m (t.Qv 1) = t.Qv 1 :=
    F7.conjSub_eq_of_mem_normalizer (t.Gv_le_normalizer_Qv 1 hmG)
  have hX : conjSub m (Subgroup.normalizer (X : Set G)) =
      Subgroup.normalizer (X : Set G) := by
    rw [← conjSub_normalizer m X, F7.conjSub_eq_of_mem_normalizer hmN]
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  show conjSub m (t.Qv 1 ⊓ Subgroup.normalizer (X : Set G)) = _
  rw [conjSub_inf, hQ, hX]

private theorem nbrKernel_normal (A B : Subgroup G) :
    A ≤ Subgroup.normalizer (nbrKernel A B : Set G) := by
  intro a ha
  rw [Subgroup.mem_normalizer_iff]
  intro x
  rw [mem_nbrKernel_iff, mem_nbrKernel_iff]
  constructor
  · rintro ⟨hxK, hx⟩
    refine ⟨A.mul_mem (A.mul_mem ha hxK) (A.inv_mem ha), ?_⟩
    intro g hg
    have h1 := hx (a⁻¹ * g) (A.mul_mem (A.inv_mem ha) hg)
    convert h1 using 1
    group
  · rintro ⟨hxK, hx⟩
    have hxK' : x = a⁻¹ * (a * x * a⁻¹) * a := by group
    refine ⟨?_, ?_⟩
    · rw [hxK']
      exact A.mul_mem (A.mul_mem (A.inv_mem ha) hxK) ha
    · intro g hg
      have h1 := hx (a * g) (A.mul_mem ha hg)
      convert h1 using 1
      group

theorem ArcL.le_Qv_zero {a f : ℕ} (hfr : Frame L1 L2 S a f)
    (hX : t.ArcL X) (hX2 : IsPGroup 2 X) : X ≤ t.Qv 0 := by
  refine t.le_Qv_of_le_Gw hfr (u := -1) (w := 1) (j := 0) (by norm_num) (by norm_num) hX2 ?_
  have hwin : t.Gw (-1) 1 = t.Gv (-1) ⊓ t.Gv 0 ⊓ t.Gv 1 := by
    have h := t.Gw_sub_one_add_one (c := 0)
    norm_num at h
    exact h
  rw [hwin]
  intro y hy
  have h := hX.le hy
  exact ⟨⟨h.2, h.1.2⟩, h.1.1⟩

theorem ArcL.Zv_zero_le {a f : ℕ} (hfr : Frame L1 L2 S a f)
    (hX : t.ArcL X) (hX2 : IsPGroup 2 X) : t.Zv 0 ≤ normIn X (t.Gw (-1) 1) := by
  have hXQ : X ≤ t.Qv 0 := ArcL.le_Qv_zero t hfr hX hX2
  refine le_inf ?_ ?_
  · exact (t.Zv_le_centralizer 0).trans
      ((Subgroup.centralizer_le (show (X : Set G) ⊆ (t.Qv 0 : Set G) from hXQ)).trans
        (Subgroup.centralizer_le_normalizer _))
  · have hwin : t.Gw (-1) 1 = t.Gv (-1) ⊓ t.Gv 0 ⊓ t.Gv 1 := by
      have h := t.Gw_sub_one_add_one (c := 0)
      norm_num at h
      exact h
    rw [hwin]
    exact le_inf (le_inf ((t.Zv_le_Qv 0).trans (t.Qv_le_Gv hfr 0).1)
      ((t.Zv_le_Qv 0).trans (t.Qv_le_Gv_self 0)))
      ((t.Zv_le_Qv 0).trans (t.Qv_le_Gv hfr 0).2)

private theorem le_Gnbr_one_of_le_MX {a f : ℕ}
    (hfr : Frame L1 L2 S a f) (hX : t.ArcL X) {E : Subgroup G}
    (hE2 : IsPGroup 2 E) (hEM : E ≤ t.MX X 1)
    (hEN : t.MX X 1 ≤ Subgroup.normalizer (E : Set G)) : E ≤ t.Gnbr 1 := by
  have htr : CosetTrans (t.MX X 1) (t.Gv 1) (t.Gv 0) := by
    intro g hg
    obtain ⟨n, hn, hnb⟩ := hX.trans₀ g hg
    exact ⟨n, ⟨hn, hn.2⟩, hnb⟩
  let H' : Subgroup G := (t.MX X 1).map (MulAut.conj t.x₂).toMonoidHom
  let E' : Subgroup G := E.map (MulAut.conj t.x₂).toMonoidHom
  have hH'G : H' ≤ t.Gv 1 := by
    rintro y ⟨z, hz, rfl⟩
    have hzG : z ∈ t.Gv 1 := (Subgroup.mem_inf.mp hz).2
    simpa [MulAut.conj_apply] using
      (t.Gv 1).mul_mem ((t.Gv 1).mul_mem (t.x₂_mem_Gv_one) hzG)
        ((t.Gv 1).inv_mem (t.x₂_mem_Gv_one))
  have hE'H' : E' ≤ H' := Subgroup.map_mono hEM
  have hH'E' : H' ≤ Subgroup.normalizer (E' : Set G) := by
    rintro y ⟨z, hz, rfl⟩
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    show conjSub (t.x₂ * z * t.x₂⁻¹) (conjSub t.x₂ E) = conjSub t.x₂ E
    rw [show t.x₂ * z * t.x₂⁻¹ = t.x₂ * (z * t.x₂⁻¹) by group, conjSub_mul, conjSub_mul,
      conjSub_conjSub_inv, F7.conjSub_eq_of_mem_normalizer (hEN hz)]
  have htr' : CosetTrans H' (t.Gv 1) (t.Gv 2) := by
    have h := CosetTrans.map_conj htr t.x₂
    have h1 : (t.Gv 1).map (MulAut.conj t.x₂).toMonoidHom = t.Gv 1 := by
      simpa using t.map_Gv_x₂ 1
    have h0 : (t.Gv 0).map (MulAut.conj t.x₂).toMonoidHom = t.Gv 2 := by
      simpa using t.map_Gv_x₂ 0
    rw [h1, h0] at h
    simpa [H'] using h
  have hE'gnbr : E' ≤ t.Gnbr 1 :=
    t.le_gnbr_of_cosetTrans hfr 1
      (hE2.map (MulAut.conj t.x₂).toMonoidHom) hE'H' hH'E' hH'G htr'
  have hx2norm : t.x₂ ∈ Subgroup.normalizer (t.Gnbr 1 : Set G) :=
    nbrKernel_normal (t.Gv 1) (t.Gv 2) (t.x₂_mem_Gv_one)
  intro e he
  have hmem : t.x₂ * e * t.x₂⁻¹ ∈ t.Gnbr 1 := by
    have h1 : (MulAut.conj t.x₂) e ∈ E' := Subgroup.mem_map_of_mem _ he
    have h2 : (MulAut.conj t.x₂) e ∈ t.Gnbr 1 := hE'gnbr h1
    simpa [MulAut.conj_apply] using h2
  have h2 := (Subgroup.mem_normalizer_iff.mp
    (Subgroup.inv_mem (Subgroup.normalizer (t.Gnbr 1 : Set G)) hx2norm)
    (t.x₂ * e * t.x₂⁻¹)).mp hmem
  have heq : t.x₂⁻¹ * (t.x₂ * e * t.x₂⁻¹) * (t.x₂⁻¹)⁻¹ = e := by group
  rwa [heq] at h2

private theorem le_Gw_zero_two_of_le_Gnbr {E : Subgroup G} (hEM : E ≤ t.MX X 1)
    (hEgnbr : E ≤ t.Gnbr 1) : E ≤ t.Gw 0 2 := by
  have hEGv0 : E ≤ t.Gv 0 := by
    intro e he
    have hmem := Subgroup.mem_iInf.mp (Subgroup.mem_inf.mp (hEgnbr he)).2
      (⟨t.x₂⁻¹, (t.Gv 1).inv_mem t.x₂_mem_Gv_one⟩ : t.Gv 1)
    obtain ⟨z, hz, hz'⟩ := Subgroup.mem_map.mp hmem
    have hGv2 : t.Gv 2 = (t.Gv 0).map (MulAut.conj t.x₂).toMonoidHom := by
      simpa using (t.map_Gv_x₂ 0).symm
    have hz2mem : z ∈ (t.Gv 0).map (MulAut.conj t.x₂).toMonoidHom := by
      rw [← hGv2]
      exact (Subgroup.mem_inf.mp hz).2
    obtain ⟨w, hw, hwz⟩ := Subgroup.mem_map.mp hz2mem
    have hz2 : z = t.x₂ * w * t.x₂⁻¹ := by
      simpa [MulAut.conj_apply] using hwz.symm
    have hew : e = w := by
      have h1 : (MulAut.conj t.x₂⁻¹) z = e := hz'
      rw [hz2, MulAut.conj_apply] at h1
      have h2 : t.x₂⁻¹ * (t.x₂ * w * t.x₂⁻¹) * t.x₂⁻¹⁻¹ = w := by group
      rw [h2] at h1
      exact h1.symm
    rw [hew]
    exact hw
  have hEGv2 : E ≤ t.Gv 2 :=
    fun e he => (Subgroup.mem_inf.mp (nbrKernel_le (t.Gv 1) (t.Gv 2) (hEgnbr he))).2
  have hwin : t.Gw 0 2 = t.Gv 0 ⊓ t.Gv 1 ⊓ t.Gv 2 := by
    have h := t.Gw_sub_one_add_one (c := 1)
    norm_num at h
    exact h
  rw [hwin]
  exact le_inf (le_inf hEGv0 (hEM.trans inf_le_right)) hEGv2

private theorem pCoreOf_MX_one_le_EX {a f : ℕ}
    (hfr : Frame L1 L2 S a f) (hX : t.ArcL X) :
    pCoreOf 2 (t.MX X 1) ≤ t.EX X 1 := by
  have hE2 : IsPGroup 2 (pCoreOf 2 (t.MX X 1)) :=
    CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  have hEM : pCoreOf 2 (t.MX X 1) ≤ t.MX X 1 :=
    CFSG.LieType.BorelTits.pCoreOf_le 2 _
  have hEgnbr : pCoreOf 2 (t.MX X 1) ≤ t.Gnbr 1 :=
    le_Gnbr_one_of_le_MX t hfr hX hE2 hEM
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (t.MX X 1))
  have hEw : pCoreOf 2 (t.MX X 1) ≤ t.Gw 0 2 :=
    le_Gw_zero_two_of_le_Gnbr t hEM hEgnbr
  have hEQ : pCoreOf 2 (t.MX X 1) ≤ t.Qv 1 :=
    t.le_Qv_of_le_Gw hfr (u := 0) (w := 2) (j := 1) (by norm_num) (by norm_num) hE2 hEw
  exact le_inf hEQ (hEM.trans inf_le_left)

theorem ArcL.pCoreOf_MX_one {a f : ℕ} (hfr : Frame L1 L2 S a f)
    (hX : t.ArcL X) : pCoreOf 2 (t.MX X 1) = t.EX X 1 := by
  have hEX : t.EX X 1 ≤ pCoreOf 2 (t.MX X 1) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (EX_le_MX t X)
      (MX_le_normalizer_EX t X) ((t.isPGroup_Qv 1).to_le inf_le_left)
  exact le_antisymm (pCoreOf_MX_one_le_EX t hfr hX) hEX

theorem ArcL.EX_one_le_pX {a f : ℕ} (hfr : Frame L1 L2 S a f)
    (hX : t.ArcL X) : t.EX X 1 ≤ t.PX X := by
  have hEX2 : IsPGroup 2 (t.EX X 1) := (t.isPGroup_Qv 1).to_le inf_le_left
  have hEXm : t.EX X 1 ≤ t.Gv (-1) := by
    intro e he
    obtain ⟨heQ, heN⟩ := Subgroup.mem_inf.mp he
    have heG0 : e ∈ t.Gv 0 := (t.Qv_le_Gv hfr 1).1 heQ
    have heG1 : e ∈ t.Gv 1 := t.Qv_le_Gv_self 1 heQ
    rcases hX.pair e (Subgroup.mem_inf.mpr ⟨heN, heG0⟩) with h | h
    · exact h.2
    · exfalso
      have hx1inv : t.x₁⁻¹ ∈ t.Gv 1 := by
        have hmem : (t.x₁⁻¹ * e) * e⁻¹ ∈ t.Gv 1 :=
          (t.Gv 1).mul_mem h.1 ((t.Gv 1).inv_mem heG1)
        simpa [mul_assoc] using hmem
      exact t.x₁_not_mem_Gv_one (by simpa using (t.Gv 1).inv_mem hx1inv)
  have hEXw : t.EX X 1 ≤ t.Gw (-1) 1 := by
    have hwin : t.Gw (-1) 1 = t.Gv (-1) ⊓ t.Gv 0 ⊓ t.Gv 1 := by
      have h := t.Gw_sub_one_add_one (c := 0)
      norm_num at h
      exact h
    rw [hwin]
    exact le_inf (le_inf hEXm
      ((inf_le_left : t.EX X 1 ≤ t.Qv 1).trans (t.Qv_le_Gv hfr 1).1))
      ((inf_le_left : t.EX X 1 ≤ t.Qv 1).trans (t.Qv_le_Gv_self 1))
  have hEX0 : t.EX X 1 ≤ t.Qv 0 :=
    t.le_Qv_of_le_Gw hfr (u := -1) (w := 1) (j := 0) (by norm_num) (by norm_num) hEX2 hEXw
  exact le_inf hEX0 (le_inf inf_le_right
    ((inf_le_left : t.EX X 1 ≤ t.Qv 1).trans (t.Qv_le_Gv_self 1)))

theorem LX_one_le_sup {a f : ℕ} (hfr : Frame L1 L2 S a f) :
    t.LX X 1 ≤ L2 ⊔ t.Qv 1 := by
  refine (CFSG.Quasithin.St84.oTwoPrime_mono
    (inf_le_right : t.MX X 1 ≤ t.Gv 1)).trans ?_
  rw [t.oTwoPrime_Gv_one hfr]

theorem LX_one_inf_Qv_one : t.LX X 1 ⊓ t.Qv 1 = t.EX X 1 := by
  refine le_antisymm ?_ (le_inf
    (le_oTwoPrime_of_isPGroup ((t.isPGroup_Qv 1).to_le inf_le_left) (EX_le_MX t X))
    inf_le_left)
  intro y hy
  obtain ⟨hyL, hyQ⟩ := Subgroup.mem_inf.mp hy
  exact Subgroup.mem_inf.mpr ⟨hyQ, (oTwoPrime_le (t.MX X 1) hyL).1⟩

theorem ArcL.isSylowTwoOf_pX_LX_one {a f : ℕ}
    (hfr : Frame L1 L2 S a f) (hX : t.ArcL X) : IsSylowTwoOf (t.PX X) (t.LX X 1) := by
  have hMX := ArcL.isSylowTwoOf_pX_one (t := t) hfr hX
  exact F7.isSylowTwoOf_mono_right hMX
    (le_oTwoPrime_of_isPGroup hMX.2.1 hMX.1) (oTwoPrime_le (t.MX X 1))

theorem ArcL.MX_one_eq_sup {a f : ℕ}
    (hfr : Frame L1 L2 S a f) (hX : t.ArcL X) : t.MX X 1 = t.LX X 1 ⊔ t.K := by
  have hLXle : t.LX X 1 ≤ t.MX X 1 := oTwoPrime_le (t.MX X 1)
  have hPXle : t.PX X ≤ t.LX X 1 :=
    le_oTwoPrime_of_isPGroup ((t.isPGroup_Qv 0).to_le inf_le_left)
      (inf_le_right : t.PX X ≤ t.MX X 1)
  have htrans : CosetTrans (t.LX X 1) (t.Gv 1) (t.Gv 0) :=
    t.cosetTrans_one_of_le_sup hfr (hLXle.trans inf_le_right)
      (ArcL.L2_le_LX_sup_Qv_one t hfr hX)
  have hM01 : t.MX X 1 ⊓ t.Gv 0 = t.PX X ⊔ t.K := by
    have hGW : t.Gw 0 1 = t.Gv 0 ⊓ t.Gv 1 := by simpa using t.Gw_add_one 0
    have h1 : t.MX X 1 ⊓ t.Gv 0 = normIn X (t.Gw 0 1) := by
      rw [hGW]
      change (Subgroup.normalizer (X : Set G) ⊓ t.Gv 1) ⊓ t.Gv 0 =
        Subgroup.normalizer (X : Set G) ⊓ (t.Gv 0 ⊓ t.Gv 1)
      rw [inf_assoc, inf_comm (t.Gv 1) (t.Gv 0)]
    rw [h1, ArcL.normIn_Gw_zero_one t hX, ArcL.normIn_Gw_eq_sup t hfr hX]
  have hMXeq : t.MX X 1 = t.LX X 1 ⊔ (t.MX X 1 ⊓ t.Gv 0) := by
    refine le_antisymm ?_ (sup_le hLXle inf_le_left)
    intro m hm
    obtain ⟨n, hn, hnb⟩ := htrans m ((inf_le_right : t.MX X 1 ≤ t.Gv 1) hm)
    have hnLX : n ∈ t.LX X 1 := hn.1
    have hnbMX : n⁻¹ * m ∈ t.MX X 1 :=
      (t.MX X 1).mul_mem ((t.MX X 1).inv_mem (hLXle hnLX)) hm
    rw [show m = n * (n⁻¹ * m) by group]
    exact Subgroup.mul_mem_sup hnLX (Subgroup.mem_inf.mpr ⟨hnbMX, hnb⟩)
  rw [hMXeq, hM01]
  refine le_antisymm ?_ ?_
  · exact sup_le le_sup_left (sup_le (hPXle.trans le_sup_left) le_sup_right)
  · exact sup_le le_sup_left (le_sup_right.trans le_sup_right)

theorem ArcL.LX_one_eq_sup {a f : ℕ}
    (hfr : Frame L1 L2 S a f) (hX : t.ArcL X) : t.LX X 1 = t.YX X 1 ⊔ t.PX X := by
  have hP := ArcL.isSylowTwoOf_pX_LX_one (t := t) hfr hX
  refine le_antisymm (le_oTwoRes_sup_of_isSylowTwoOf hP) ?_
  exact sup_le (oTwoRes_le (t.LX X 1)) hP.1

theorem ArcL.noCharNormal_pX_LX_one {a f : ℕ}
    (hfr : Frame L1 L2 S a f) (hX : t.ArcL X) (hnc : NoCharNormal (t.PX X) (t.MX X 1)) :
    NoCharNormal (t.PX X) (t.LX X 1) := by
  intro C hCP hCne hCchar hLXnorm
  apply hnc C hCP hCne hCchar
  have hP : IsSylowTwoOf (t.PX X) (t.LX X 1) :=
    ArcL.isSylowTwoOf_pX_LX_one (t := t) hfr hX
  have hfratt := CFSG.Quasithin.H13.Ch4.sup_inf_normalizer_eq
    (M := t.MX X 1) (N := t.LX X 1) (P := t.PX X)
    (oTwoPrime_le (t.MX X 1)) (le_normalizer_oTwoPrime (t.MX X 1)) hP
  have hcharN : Subgroup.normalizer (t.PX X : Set G) ≤
      Subgroup.normalizer (C : Set G) := by
    haveI : (C.subgroupOf (t.PX X)).Characteristic := hCchar
    have hmap : (C.subgroupOf (t.PX X)).map (t.PX X).subtype = C :=
      Subgroup.map_subgroupOf_eq_of_le hCP
    have h := CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
      (H := t.PX X) (K := C.subgroupOf (t.PX X))
    rwa [hmap] at h
  rw [← hfratt]
  exact sup_le hLXnorm (inf_le_right.trans hcharN)

end Track

end CFSG.Quasithin.Stroth.Rq

end