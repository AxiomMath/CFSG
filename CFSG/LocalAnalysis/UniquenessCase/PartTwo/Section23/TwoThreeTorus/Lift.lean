module

import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.TwoThreeFourteenFive
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.BarSubISup
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.TwoThreeTransport

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.TwoConj

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC CFSG.Quasithin Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartTwo

variable {G : Type} [Group G] [Finite G]

theorem sq_eq_one_Vtil {A : Subgroup G} (hA : IsElemAbelian 2 A) (w : Vtil ⊥ A hA) :
    w ^ 2 = 1 := by
  obtain ⟨x, rfl⟩ := mkTil_surjective ⊥ A hA w
  rw [← map_pow, IntMod.sq_eq_one, map_one]

theorem mkTil_mk_eq_one_iff {A : Subgroup G} (hA : IsElemAbelian 2 A) {z : G} (hz : z ∈ A) :
    mkTil ⊥ A hA (IntMod.mk hA ⟨z, hz⟩) = 1 ↔ z = 1 := by
  rw [← map_one (mkTil ⊥ A hA), mkTil_eq_iff, Subgroup.mem_bot]
  show z * (1 : G)⁻¹ = 1 ↔ z = 1
  simp

theorem mkTil_commutator_eq {A : Subgroup G} (hA : IsElemAbelian 2 A) {g : G}
    (hg : g ∈ stabTil ⊥ A) {z : G} (hz : z ∈ A) :
    ∃ hu : g * z * g⁻¹ * z⁻¹ ∈ A, mkTil ⊥ A hA (IntMod.mk hA ⟨g * z * g⁻¹ * z⁻¹, hu⟩) =
      actTil ⊥ A hA ⟨g, hg⟩ (mkTil ⊥ A hA (IntMod.mk hA ⟨z, hz⟩)) *
        (mkTil ⊥ A hA (IntMod.mk hA ⟨z, hz⟩))⁻¹ := by
  have hgz : g * z * g⁻¹ ∈ A :=
    (Subgroup.mem_normalizer_iff.1 (stabTil_le_normalizer ⊥ A hg) z).1 hz
  have hu : g * z * g⁻¹ * z⁻¹ ∈ A := A.mul_mem hgz (A.inv_mem hz)
  refine ⟨hu, ?_⟩
  have hkey : IntMod.mk hA ⟨g * z * g⁻¹ * z⁻¹, hu⟩ =
      actStab ⊥ A hA ⟨g, hg⟩ (IntMod.mk hA ⟨z, hz⟩) * (IntMod.mk hA ⟨z, hz⟩)⁻¹ := by
    refine IntMod.val_injective ?_
    rw [IntMod.val_mul, IntMod.val_inv, actStab_apply_val]
    rfl
  calc mkTil ⊥ A hA (IntMod.mk hA ⟨g * z * g⁻¹ * z⁻¹, hu⟩)
      = mkTil ⊥ A hA (actStab ⊥ A hA ⟨g, hg⟩ (IntMod.mk hA ⟨z, hz⟩) *
          (IntMod.mk hA ⟨z, hz⟩)⁻¹) := by rw [hkey]
    _ = mkTil ⊥ A hA (actStab ⊥ A hA ⟨g, hg⟩ (IntMod.mk hA ⟨z, hz⟩)) *
          (mkTil ⊥ A hA (IntMod.mk hA ⟨z, hz⟩))⁻¹ := by rw [map_mul, map_inv]
    _ = actTil ⊥ A hA ⟨g, hg⟩ (mkTil ⊥ A hA (IntMod.mk hA ⟨z, hz⟩)) *
          (mkTil ⊥ A hA (IntMod.mk hA ⟨z, hz⟩))⁻¹ := by rw [actTil_mk]

theorem le_centralizer_of_mkTil_mem_fixV {A Y : Subgroup G} (hA : IsElemAbelian 2 A)
    (hY : Y ≤ stabTil ⊥ A) {u : G} (hu : u ∈ A)
    (hfix : mkTil ⊥ A hA (IntMod.mk hA ⟨u, hu⟩) ∈ fixV (barSub ⊥ A hA Y)) :
    Y ≤ centralizer ({u} : Set G) := by
  rw [UC22.fixV_barSub_eq_imgTil_centralizer hA hY] at hfix
  obtain ⟨x, hx, hxq⟩ := (mem_imgTil ⊥ A hA (A ⊓ Subgroup.centralizer (Y : Set G))
    (mkTil ⊥ A hA (IntMod.mk hA ⟨u, hu⟩))).1 hfix
  have hxu : x.val = u := by
    have h1 : x.val * u⁻¹ ∈ (⊥ : Subgroup G) :=
      (mkTil_eq_iff ⊥ A hA x (IntMod.mk hA ⟨u, hu⟩)).1 hxq
    exact mul_inv_eq_one.1 (Subgroup.mem_bot.1 h1)
  have hxcent : x.val ∈ Subgroup.centralizer (Y : Set G) := (Subgroup.mem_inf.mp hx).2
  intro y hy
  rw [Subgroup.mem_centralizer_singleton_iff, ← hxu]
  exact Subgroup.mem_centralizer_iff.mp hxcent y hy

private theorem mem_normalizer_subtype_of_mem_normalizer_subgroupOf_Tor6 {P X : Subgroup G}
    (hPX : P ≤ X) (x : ↥X) (hx : x ∈ Subgroup.normalizer (P.subgroupOf X : Set ↥X)) :
    (x : G) ∈ Subgroup.normalizer (P : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at hx ⊢
  intro p
  constructor
  · intro hp
    have h1 : (⟨p, hPX hp⟩ : ↥X) ∈ (P.subgroupOf X : Subgroup ↥X) :=
      Subgroup.mem_subgroupOf.mpr hp
    exact Subgroup.mem_subgroupOf.mp ((hx ⟨p, hPX hp⟩).1 h1)
  · intro hp
    have hpX : p ∈ X := by
      have h1 : p = (x : G)⁻¹ * ((x : G) * p * (x : G)⁻¹) * (x : G) := by group
      rw [h1]
      exact X.mul_mem (X.mul_mem (X.inv_mem x.2) (hPX hp)) x.2
    have h1 : x * (⟨p, hpX⟩ : ↥X) * x⁻¹ ∈ (P.subgroupOf X : Subgroup ↥X) := by
      show (x : G) * p * (x : G)⁻¹ ∈ P
      exact hp
    exact Subgroup.mem_subgroupOf.mp ((hx ⟨p, hpX⟩).2 h1)

private theorem map_barSubHom_sylow_eq_Tor6 {A X P : Subgroup G} (hA : IsElemAbelian 2 A)
    (hX : X ≤ stabTil ⊥ A) (hP : IsSylowIn 2 P X) :
    (((hP.toSylow : Subgroup ↥X).map (barSubHom hA X hX)).map
      (barSub ⊥ A hA X).subtype) = barSub ⊥ A hA P := by
  ext ψ
  constructor
  · rintro ⟨k, hk, rfl⟩
    obtain ⟨x, hx, rfl⟩ := hk
    have hxP : (x : G) ∈ P := Subgroup.mem_subgroupOf.mp hx
    change (barSubHom hA X hX x : MulAut (Vtil ⊥ A hA)) ∈ barSub ⊥ A hA P
    rw [barSubHom_apply]
    rw [show (⟨(x : G), hX x.2⟩ : ↥(stabTil ⊥ A)) =
        ⟨(x : G), hX (hP.le hxP)⟩ from Subtype.ext rfl]
    exact actTil_mem_barSub (X := P) ⊥ A hA hxP (hX (hP.le hxP))
  · intro hψ
    obtain ⟨g, hg, rfl⟩ := (mem_barSub ⊥ A hA P ψ).1 hψ
    refine ⟨barSubHom hA X hX ⟨(g : G), hP.le hg⟩, ?_, ?_⟩
    · refine Subgroup.mem_map.mpr ⟨⟨(g : G), hP.le hg⟩, ?_, rfl⟩
      show (⟨(g : G), hP.le hg⟩ : ↥X) ∈ P.subgroupOf X
      exact Subgroup.mem_subgroupOf.mpr hg
    · change ((barSubHom hA X hX ⟨(g : G), hP.le hg⟩ : ↥(barSub ⊥ A hA X)) :
          MulAut (Vtil ⊥ A hA)) = actTil ⊥ A hA g
      rw [barSubHom_apply]

private theorem mem_normalizer_map_barSubHom_sylow_Tor6 {A X P : Subgroup G}
    (hA : IsElemAbelian 2 A) (hX : X ≤ stabTil ⊥ A) (hP : IsSylowIn 2 P X)
    {φ : MulAut (Vtil ⊥ A hA)} (hφX : φ ∈ barSub ⊥ A hA X)
    (hφn : φ ∈ normalizer (barSub ⊥ A hA P : Set (MulAut (Vtil ⊥ A hA)))) :
    (⟨φ, hφX⟩ : ↥(barSub ⊥ A hA X)) ∈
      Subgroup.normalizer (((hP.toSylow : Subgroup ↥X).map (barSubHom hA X hX) :
        Subgroup ↥(barSub ⊥ A hA X)) : Set ↥(barSub ⊥ A hA X)) := by
  have hKmap := map_barSubHom_sylow_eq_Tor6 hA hX hP
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  refine Subgroup.map_injective (Subgroup.subtype_injective (barSub ⊥ A hA X)) ?_
  calc ((((hP.toSylow : Subgroup ↥X).map (barSubHom hA X hX)).map
          (MulAut.conj (⟨φ, hφX⟩ : ↥(barSub ⊥ A hA X))).toMonoidHom).map
          (barSub ⊥ A hA X).subtype)
      = ((((hP.toSylow : Subgroup ↥X).map (barSubHom hA X hX)).map
          (barSub ⊥ A hA X).subtype).map (MulAut.conj φ).toMonoidHom) := by
        have hcomp : (barSub ⊥ A hA X).subtype.comp
              (MulAut.conj (⟨φ, hφX⟩ : ↥(barSub ⊥ A hA X))).toMonoidHom =
            (MulAut.conj φ).toMonoidHom.comp (barSub ⊥ A hA X).subtype := by
          ext z
          simp [MulAut.conj_apply]
        rw [Subgroup.map_map, Subgroup.map_map, hcomp]
        simp only [Subgroup.map_map, MonoidHom.comp_assoc]
    _ = (barSub ⊥ A hA P).map (MulAut.conj φ).toMonoidHom := by rw [hKmap]
    _ = barSub ⊥ A hA P := (Subgroup.mem_normalizer_iff_map_conj_eq).1 hφn
    _ = (((hP.toSylow : Subgroup ↥X).map (barSubHom hA X hX)).map
          (barSub ⊥ A hA X).subtype) := hKmap.symm

theorem barSub_inf_normalizer_le {A X P : Subgroup G} (hA : IsElemAbelian 2 A)
    (hX : X ≤ stabTil ⊥ A) (hP : IsSylowIn 2 P X) :
    barSub ⊥ A hA X ⊓ normalizer (barSub ⊥ A hA P : Set (MulAut (Vtil ⊥ A hA))) ≤
      barSub ⊥ A hA (X ⊓ normalizer (P : Set G)) := by
  intro φ hφ
  obtain ⟨hφX, hφn⟩ := Subgroup.mem_inf.mp hφ
  have hmem := mem_normalizer_map_barSubHom_sylow_Tor6 hA hX hP hφX hφn
  have hmemN : (⟨φ, hφX⟩ : ↥(barSub ⊥ A hA X)) ∈
      (Subgroup.normalizer (hP.toSylow : Set ↥X)).map (barSubHom hA X hX) := by
    rw [← UC22.normalizer_map_sylow_eq (barSubHom hA X hX)
      (barSubHom_surjective hA X hX) hP.toSylow]
    exact hmem
  obtain ⟨x, hxN, hxf⟩ := Subgroup.mem_map.mp hmemN
  have hxP : (x : G) ∈ Subgroup.normalizer (P : Set G) :=
    mem_normalizer_subtype_of_mem_normalizer_subgroupOf_Tor6 hP.le x hxN
  have hφeq : φ = actTil ⊥ A hA ⟨(x : G), hX x.2⟩ :=
    (congrArg Subtype.val hxf).symm.trans (barSubHom_apply hA X hX x)
  rw [hφeq]
  exact actTil_mem_barSub (X := X ⊓ normalizer (P : Set G)) ⊥ A hA ⟨x.2, hxP⟩ (hX x.2)

theorem commutator_mem_U (D : Data G) {b z : G} (hb : b ∈ D.M) (hz : z ∈ D.Z) :
    b * z * b⁻¹ * z⁻¹ ∈ D.U := by
  have hzU : z ∈ D.U := Data.Z_le_U D hz
  have hbN : b ∈ normalizer (D.U : Set G) := le_normalizer_uCore D.M D.T hb
  have hbz : b * z * b⁻¹ ∈ D.U := (Subgroup.mem_normalizer_iff.1 hbN z).1 hzU
  exact D.U.mul_mem hbz (D.U.inv_mem hzU)

theorem barSub_L_eq_sup {D : Data G} {Ch : Choice2011 G} (c : Ctx23L D Ch) {A : Subgroup G}
    (hA : IsElemAbelian 2 A) (hAN : c.N ≤ normalizer (A : Set G)) {K : Subgroup G}
    (hLK : c.L = ⨆ s : D.T, K.map (MulAut.conj (s : G)).toMonoidHom) {t : G} (htT : t ∈ D.T)
    (htwo : ∀ X ∈ conjSet (barSub ⊥ A hA K) (barSub ⊥ A hA c.N),
      X = barSub ⊥ A hA K ∨ X = barSub ⊥ A hA (K.map (MulAut.conj t).toMonoidHom)) :
    barSub ⊥ A hA c.L =
      barSub ⊥ A hA K ⊔ barSub ⊥ A hA (K.map (MulAut.conj t).toMonoidHom) := by
  have hNstab : c.N ≤ stabTil ⊥ A :=
    le_inf hAN (by rw [Subgroup.normalizer_eq_top]; exact le_top)
  have hKleL : ∀ s : D.T, K.map (MulAut.conj (s : G)).toMonoidHom ≤ c.L := by
    intro s
    rw [hLK]
    exact le_iSup (fun s : D.T => K.map (MulAut.conj (s : G)).toMonoidHom) s
  have hKstab' : ∀ s : D.T, K.map (MulAut.conj (s : G)).toMonoidHom ≤ stabTil ⊥ A :=
    fun s => (hKleL s).trans (c.L_le_N.trans hNstab)
  have hKleL' : K ≤ c.L := by
    refine le_trans ?_ (hKleL ⟨1, D.T.one_mem⟩)
    intro k hk
    exact Subgroup.mem_map.mpr ⟨k, hk, by simp [MulAut.conj_apply]⟩
  have hKstab : K ≤ stabTil ⊥ A := hKleL'.trans (c.L_le_N.trans hNstab)
  refine le_antisymm ?_ ?_
  · rw [hLK, PartTwo.barSub_iSup_of_le hA hKstab']
    refine iSup_le fun s : D.T => ?_
    have hmem : barSub ⊥ A hA (K.map (MulAut.conj (s : G)).toMonoidHom) ∈
        conjSet (barSub ⊥ A hA K) (barSub ⊥ A hA c.N) := by
      refine ⟨actTil ⊥ A hA ⟨(s : G), hNstab (Ctx23L.T_le_N c s.2)⟩,
        actTil_mem_barSub ⊥ A hA (Ctx23L.T_le_N c s.2) (hNstab (Ctx23L.T_le_N c s.2)), ?_⟩
      exact PartTwo.TwelveTwentyThree.barSub_map_conj hA hKstab
        (hNstab (Ctx23L.T_le_N c s.2))
    rcases htwo _ hmem with h | h
    · rw [h]; exact le_sup_left
    · rw [h]; exact le_sup_right
  · refine sup_le (barSub_mono ⊥ A hA hKleL') (barSub_mono ⊥ A hA (hKleL ⟨t, htT⟩))

theorem false_of_map_conj_le_centralizer {D : Data G} {Ch : Choice2011 G} (c : Ctx23L D Ch)
    {K : Subgroup G} (hLK : c.L = ⨆ s : D.T, K.map (MulAut.conj (s : G)).toMonoidHom)
    {t : G} (htT : t ∈ D.T) {u : G} (hu : u ∈ D.U) (hu1 : u ≠ 1)
    (hKu : K.map (MulAut.conj t).toMonoidHom ≤ centralizer ({u} : Set G)) : False := by
  have hcM : centralizer ({u} : Set G) ≤ D.M := Ctx23.centralizer_le_M c.toCtx23 hu hu1
  have hKtM : K.map (MulAut.conj t).toMonoidHom ≤ D.M := hKu.trans hcM
  have htM : t ∈ D.M := D.sylowM.le htT
  have hKleM : K ≤ D.M := by
    intro k hk
    have hkt : t * k * t⁻¹ ∈ K.map (MulAut.conj t).toMonoidHom :=
      Subgroup.mem_map.mpr ⟨k, hk, by simp [MulAut.conj_apply]⟩
    have h1 : t * k * t⁻¹ ∈ D.M := hKtM hkt
    have h2 : k = t⁻¹ * (t * k * t⁻¹) * t := by group
    rw [h2]
    exact D.M.mul_mem (D.M.mul_mem (D.M.inv_mem htM) h1) htM
  have hKsM : ∀ s : D.T, K.map (MulAut.conj (s : G)).toMonoidHom ≤ D.M := by
    intro s x hx
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hx
    have hsM : (s : G) ∈ D.M := D.sylowM.le s.2
    have hkM : k ∈ D.M := hKleM hk
    have hval : (MulAut.conj (s : G)).toMonoidHom k = (s : G) * k * (s : G)⁻¹ := by
      simp [MulAut.conj_apply]
    rw [hval]
    exact D.M.mul_mem (D.M.mul_mem hsM hkM) (D.M.inv_mem hsM)
  have hLM : c.L ≤ D.M := by
    rw [hLK]
    exact iSup_le hKsM
  exact Ctx23L.L_not_le_M c hLM

end CFSG.LocalAnalysis.UniquenessCase.UC22.TwoConj
