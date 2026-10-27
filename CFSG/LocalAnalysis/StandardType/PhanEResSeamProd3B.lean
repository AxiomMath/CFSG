module

public import CFSG.LocalAnalysis.StandardType.PhanEResSeamProd3A

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE.Res

open Matrix CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.RootSystem
  CFSG.LieType.Steinberg CFSG.LieType.Chevalley.CosetBuilding CFSG.Monster.B.Geometry
  CFSG.ClassicalInvolution.Phan.PhanE CFSG.ClassicalInvolution.Phan.PhanE.Flag
  CFSG.LieType.Steinberg.CentralExt.SLClosed CFSG.AGLEmbeddingD2.ParabLevi

variable {K : Type} [Group K] {D : UniversalRootDatum K} {n : Fin D.rank → K}
  {H : Fin D.rank → Subgroup K} {Fld : Type} [Field Fld]

set_option hygiene false in
local notation "W" => (coxeterMatrix D.isFiniteType).Group
set_option hygiene false in
local notation "cs" => (coxeterMatrix D.isFiniteType).toCoxeterSystem

variable {M : ChevModel2 D n H Fld}
  (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
    (weylAction D.isFiniteType) D.roots D.rootGroup n H) (hext : SteinbergExtras D n H)
  {w₀ : W} (F : FrobData D n H w₀)
  (hw₀ : IsLongest (coxeterMatrix D.isFiniteType).toCoxeterSystem Set.univ w₀)
  (hsq : ∀ i, n i * n i = 1)

@[expose] noncomputable def hmbS3_chart [CharP Fld 2] (Lx Ly Lz : SLPath M 1)
    {x y z : Fin D.rank}
    (hx : Lx.e 0 = x) (hy : Ly.e 0 = y) (hz : Lz.e 0 = z)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hmxy : coxeterMatrix D.isFiniteType x y = 2)
    (hmxz : coxeterMatrix D.isFiniteType x z = 2)
    (hmyz : coxeterMatrix D.isFiniteType y z = 2)
    {a : K ⧸ borel D H} {g : K}
    (hR : residue (cs) (stdδ hct) (insert z (insert y {x})) a =
      residue (cs) (stdδ hct) (insert z (insert y {x})) ((g : K) : K ⧸ borel D H)) :
    ChamberIso ((buildingOver (cs) (stdδ hct) (insert z (insert y {x}))).restrict
        (residue (cs) (stdδ hct) (insert z (insert y {x})) a))
      (((flagSys Fld 1).prod (flagSys Fld 1)).prod (flagSys Fld 1)) :=
  let hJx : Set.range Lx.e = ({x} : Set (Fin D.rank)) := hmbS3_range_e_one hx
  let hJz : Set.range Lz.e = ({z} : Set (Fin D.rank)) := hmbS3_range_e_one hz
  let hyx : y ∉ ({x} : Set (Fin D.rank)) := fun h => hxy h.symm
  let hzJ₁ : z ∉ (insert y ({x} : Set (Fin D.rank))) := by
    intro h
    rcases Set.mem_insert_iff.mp h with hzy | hzx
    · exact hyz hzy.symm
    · rw [Set.mem_singleton_iff] at hzx
      exact hxz hzx.symm
  let hcomm_xy : ∀ i ∈ ({x} : Set (Fin D.rank)), coxeterMatrix D.isFiniteType i y = 2 := by
    intro i hi
    rw [Set.mem_singleton_iff] at hi
    rw [hi]
    exact hmxy
  let hcomm_outer : ∀ i ∈ (insert y ({x} : Set (Fin D.rank))),
      coxeterMatrix D.isFiniteType i z = 2 := by
    intro i hi
    rcases Set.mem_insert_iff.mp hi with rfl | hi'
    · exact hmyz
    · rw [Set.mem_singleton_iff] at hi'
      rw [hi']
      exact hmxz
  let combined := hmbSP_chart hct hext Lx Ly hJx hy hyx hcomm_xy (g := g) (hR := rfl)
  let outer := prodChart (stdBuilding hct hext) hzJ₁ hcomm_outer ((g : K) : K ⧸ borel D H)
  let chartZ := slChart hct hext Lz hJz g
  (ChamberIso.restrictCongr (buildingOver (cs) (stdδ hct) (insert z (insert y {x}))) hR).trans
    (outer.trans (combined.prodCongr chartZ))

theorem hmbS3_chart_symm_apply [CharP Fld 2] (Lx Ly Lz : SLPath M 1) {x y z : Fin D.rank}
    (hx : Lx.e 0 = x) (hy : Ly.e 0 = y) (hz : Lz.e 0 = z) (hxy : x ≠ y) (hxz : x ≠ z)
    (hyz : y ≠ z)
    (hmxy : coxeterMatrix D.isFiniteType x y = 2)
    (hmxz : coxeterMatrix D.isFiniteType x z = 2)
    (hmyz : coxeterMatrix D.isFiniteType y z = 2)
    {a : K ⧸ borel D H} {g : K}
    (hR : residue (cs) (stdδ hct) (insert z (insert y {x})) a =
      residue (cs) (stdδ hct) (insert z (insert y {x})) ((g : K) : K ⧸ borel D H))
    (Ax Ay Az : SpecialLinearGroup (Fin 2) Fld) :
    (((hmbS3_chart hct hext Lx Ly Lz hx hy hz hxy hxz hyz hmxy hmxz hmyz hR).Φ.symm
        ((flagAct (SpecialLinearGroup.toGL Ax) (stdFlag Fld 2),
          flagAct (SpecialLinearGroup.toGL Ay) (stdFlag Fld 2)),
            flagAct (SpecialLinearGroup.toGL Az) (stdFlag Fld 2)) :
      ↥(residue (cs) (stdδ hct) (insert z (insert y {x})) a)) : K ⧸ borel D H) =
      ((g * Lx.ε Ax * Ly.ε Ay * Lz.ε Az : K) : K ⧸ borel D H) := by
  let hJx : Set.range Lx.e = ({x} : Set (Fin D.rank)) := hmbS3_range_e_one hx
  let hJz : Set.range Lz.e = ({z} : Set (Fin D.rank)) := hmbS3_range_e_one hz
  let hyx : y ∉ ({x} : Set (Fin D.rank)) := fun h => hxy h.symm
  let hzJ₁ : z ∉ (insert y ({x} : Set (Fin D.rank))) := by
    intro h
    rcases Set.mem_insert_iff.mp h with hzy | hzx
    · exact hyz hzy.symm
    · rw [Set.mem_singleton_iff] at hzx
      exact hxz hzx.symm
  let hcomm_xy : ∀ i ∈ ({x} : Set (Fin D.rank)), coxeterMatrix D.isFiniteType i y = 2 := by
    intro i hi
    rw [Set.mem_singleton_iff] at hi
    rw [hi]
    exact hmxy
  let hcomm_outer : ∀ i ∈ (insert y ({x} : Set (Fin D.rank))),
      coxeterMatrix D.isFiniteType i z = 2 := by
    intro i hi
    rcases Set.mem_insert_iff.mp hi with rfl | hi'
    · exact hmyz
    · rw [Set.mem_singleton_iff] at hi'
      rw [hi']
      exact hmxz
  let combined := hmbSP_chart hct hext Lx Ly hJx hy hyx hcomm_xy (g := g) (hR := rfl)
  let outer := prodChart (stdBuilding hct hext) hzJ₁ hcomm_outer ((g : K) : K ⧸ borel D H)
  let chartZ := slChart hct hext Lz hJz g
  have hchart : hmbS3_chart hct hext Lx Ly Lz hx hy hz hxy hxz hyz hmxy hmxz hmyz hR =
      (ChamberIso.restrictCongr (buildingOver (cs) (stdδ hct) (insert z (insert y {x}))) hR).trans
        (outer.trans (combined.prodCongr chartZ)) := rfl
  rw [hchart]
  let Ex := flagAct (SpecialLinearGroup.toGL Ax) (stdFlag Fld 2)
  let Ey := flagAct (SpecialLinearGroup.toGL Ay) (stdFlag Fld 2)
  let Ez := flagAct (SpecialLinearGroup.toGL Az) (stdFlag Fld 2)
  let p : ↥(residue (cs) (stdδ hct) (insert y {x}) ((g : K) : K ⧸ borel D H)) :=
    combined.Φ.symm (Ex, Ey)
  let q : ↥(residue (cs) (stdδ hct) ({z} : Set (Fin D.rank)) ((g : K) : K ⧸ borel D H)) :=
    chartZ.Φ.symm Ez
  have hp : (p : K ⧸ borel D H) = ((g * Lx.ε Ax * Ly.ε Ay : K) : K ⧸ borel D H) :=
    hmbSP_chart_symm_apply hct hext Lx Ly hJx hy hyx hcomm_xy (g := g) (hR := rfl) Ax Ay
  have hq : (q : K ⧸ borel D H) = ((g * Lz.ε Az : K) : K ⧸ borel D H) :=
    slChart_symm_apply hct hext Lz hJz g Az
  have hmem_z : Lz.ε Az ∈ leviM D ({z} : Set (Fin D.rank)) :=
    hmbS3_eps_mem_leviM hz (by simp) Az
  have hmem_J₁ : Lx.ε Ax * Ly.ε Ay ∈ leviM D (insert y {x}) :=
    mul_mem (hmbS3_eps_mem_leviM hx (by simp) Ax) (hmbS3_eps_mem_leviM hy (by simp) Ay)
  have hyp : ((g * Lx.ε Ax * Ly.ε Ay * Lz.ε Az : K) : K ⧸ borel D H) ∈
      residue (cs) (stdδ hct) ({z} : Set (Fin D.rank)) (p : K ⧸ borel D H) := by
    rw [hp]
    exact mk_mul_mem_residue_of_mem_leviM hct hext (g * Lx.ε Ax * Ly.ε Ay) hmem_z
  have hyq : ((g * Lx.ε Ax * Ly.ε Ay * Lz.ε Az : K) : K ⧸ borel D H) ∈
      residue (cs) (stdδ hct) (insert y {x}) (q : K ⧸ borel D H) := by
    rw [hq]
    have hcomm3 := hmbS3_commute3 (hext := hext) hx hy hz hmxz hmyz Ax Ay Az
    have heq : ((g * Lx.ε Ax * Ly.ε Ay * Lz.ε Az : K) : K ⧸ borel D H) =
        ((g * Lz.ε Az * (Lx.ε Ax * Ly.ε Ay) : K) : K ⧸ borel D H) := by
      rw [show (g * Lx.ε Ax * Ly.ε Ay * Lz.ε Az : K) =
          g * (Lx.ε Ax * Ly.ε Ay * Lz.ε Az) by group,
        show (g * Lz.ε Az * (Lx.ε Ax * Ly.ε Ay) : K) =
          g * (Lz.ε Az * (Lx.ε Ax * Ly.ε Ay)) by group, hcomm3]
    rw [heq]
    exact mk_mul_mem_residue_of_mem_leviM hct hext (g * Lz.ε Az) hmem_J₁
  have houter := prodChart_symm_apply_of_mem (stdBuilding hct hext) hzJ₁ hcomm_outer
    ((g : K) : K ⧸ borel D H) p.2 q.2 hyp hyq
  have hmain : (((outer.trans (combined.prodCongr chartZ)).Φ.symm ((Ex, Ey), Ez) :
      ↥(residue (cs) (stdδ hct) (insert z (insert y {x})) ((g : K) : K ⧸ borel D H))) :
      K ⧸ borel D H) = ((g * Lx.ε Ax * Ly.ε Ay * Lz.ε Az : K) : K ⧸ borel D H) := by
    have hsymm : (combined.prodCongr chartZ).Φ.symm ((Ex, Ey), Ez) = (p, q) := rfl
    have h1 : (outer.trans (combined.prodCongr chartZ)).Φ.symm ((Ex, Ey), Ez) =
        outer.Φ.symm (p, q) := by
      change outer.Φ.symm ((combined.prodCongr chartZ).Φ.symm ((Ex, Ey), Ez)) =
        outer.Φ.symm (p, q)
      rw [hsymm]
    rw [h1]
    exact houter
  exact hmain

theorem hmbS3_chart_coord [CharP Fld 2] (Lx Ly Lz : SLPath M 1) {x y z : Fin D.rank}
    (hx : Lx.e 0 = x) (hy : Ly.e 0 = y) (hz : Lz.e 0 = z) (hxy : x ≠ y) (hxz : x ≠ z)
    (hyz : y ≠ z)
    (hmxy : coxeterMatrix D.isFiniteType x y = 2)
    (hmxz : coxeterMatrix D.isFiniteType x z = 2)
    (hmyz : coxeterMatrix D.isFiniteType y z = 2)
    {a : K ⧸ borel D H} {g : K}
    (hR : residue (cs) (stdδ hct) (insert z (insert y {x})) a =
      residue (cs) (stdδ hct) (insert z (insert y {x})) ((g : K) : K ⧸ borel D H))
    {t : K} (ht : t ∈ ⨆ k, H k) :
    ∃ Dx : GL (Fin 2) Fld, ∃ Dy : GL (Fin 2) Fld, ∃ Dz : GL (Fin 2) Fld,
      (∀ i j, i ≠ j → (Dx : Matrix (Fin 2) (Fin 2) Fld) i j = 0) ∧
      (∀ i j, i ≠ j → (Dy : Matrix (Fin 2) (Fin 2) Fld) i j = 0) ∧
      (∀ i j, i ≠ j → (Dz : Matrix (Fin 2) (Fin 2) Fld) i j = 0) ∧
      ∀ (Ax Ay Az : SpecialLinearGroup (Fin 2) Fld)
        (c : ↥(residue (cs) (stdδ hct) (insert z (insert y {x})) a)),
        (c : K ⧸ borel D H) =
            ((g * t * Lx.ε Ax * Ly.ε Ay * Lz.ε Az : K) : K ⧸ borel D H) →
        (hmbS3_chart hct hext Lx Ly Lz hx hy hz hxy hxz hyz hmxy hmxz hmyz hR).Φ c =
          ((flagAct Dx (flagAct (SpecialLinearGroup.toGL Ax) (stdFlag Fld 2)),
            flagAct Dy (flagAct (SpecialLinearGroup.toGL Ay) (stdFlag Fld 2))),
            flagAct Dz (flagAct (SpecialLinearGroup.toGL Az) (stdFlag Fld 2))) := by
  let hJx : Set.range Lx.e = ({x} : Set (Fin D.rank)) := hmbS3_range_e_one hx
  let hJy : Set.range Ly.e = ({y} : Set (Fin D.rank)) := hmbS3_range_e_one hy
  let hJz : Set.range Lz.e = ({z} : Set (Fin D.rank)) := hmbS3_range_e_one hz
  let hyx : y ∉ ({x} : Set (Fin D.rank)) := fun h => hxy h.symm
  let hzJ₁ : z ∉ (insert y ({x} : Set (Fin D.rank))) := by
    intro h
    rcases Set.mem_insert_iff.mp h with hzy | hzx
    · exact hyz hzy.symm
    · rw [Set.mem_singleton_iff] at hzx
      exact hxz hzx.symm
  let hcomm_xy : ∀ i ∈ ({x} : Set (Fin D.rank)), coxeterMatrix D.isFiniteType i y = 2 := by
    intro i hi
    rw [Set.mem_singleton_iff] at hi
    rw [hi]
    exact hmxy
  let hcomm_outer : ∀ i ∈ (insert y ({x} : Set (Fin D.rank))),
      coxeterMatrix D.isFiniteType i z = 2 := by
    intro i hi
    rcases Set.mem_insert_iff.mp hi with rfl | hi'
    · exact hmyz
    · rw [Set.mem_singleton_iff] at hi'
      rw [hi']
      exact hmxz
  let combined := hmbSP_chart hct hext Lx Ly hJx hy hyx hcomm_xy (g := g) (hR := rfl)
  let outer := prodChart (stdBuilding hct hext) hzJ₁ hcomm_outer ((g : K) : K ⧸ borel D H)
  let chartZ := slChart hct hext Lz hJz g
  have hchart : hmbS3_chart hct hext Lx Ly Lz hx hy hz hxy hxz hyz hmxy hmxz hmyz hR =
      (ChamberIso.restrictCongr (buildingOver (cs) (stdδ hct) (insert z (insert y {x}))) hR).trans
        (outer.trans (combined.prodCongr chartZ)) := rfl
  obtain ⟨Dx, hDx, hcoordx⟩ := slChart_coord_torus hct hext Lx hJx g ht
  obtain ⟨Dy, hDy, hcoordy⟩ := slChart_coord_torus hct hext Ly hJy g ht
  obtain ⟨Dz, hDz, hcoordz⟩ := slChart_coord_torus hct hext Lz hJz g ht
  have hcombined : ∀ (Ax Ay : SpecialLinearGroup (Fin 2) Fld)
      (c₁ : ↥(residue (cs) (stdδ hct) (insert y {x}) ((g : K) : K ⧸ borel D H))),
      (c₁ : K ⧸ borel D H) = ((g * t * Lx.ε Ax * Ly.ε Ay : K) : K ⧸ borel D H) →
      combined.Φ c₁ = (flagAct Dx (flagAct (SpecialLinearGroup.toGL Ax) (stdFlag Fld 2)),
        flagAct Dy (flagAct (SpecialLinearGroup.toGL Ay) (stdFlag Fld 2))) := by
    intro Ax Ay c₁ hc₁
    have htB : t ∈ borel D H := iSup_le_borel ht
    have hmemx : Lx.ε Ax ∈ leviM D ({x} : Set (Fin D.rank)) := hmbS3_eps_mem_leviM hx (by simp) Ax
    have hmemy : Ly.ε Ay ∈ leviM D ({y} : Set (Fin D.rank)) := hmbS3_eps_mem_leviM hy (by simp) Ay
    have htmemx : t * Lx.ε Ax * t⁻¹ ∈ leviM D ({x} : Set (Fin D.rank)) :=
      (Subgroup.mem_normalizer_iff.mp
        (torus_le_normalizer_leviM (D := D) (I := ({x} : Set (Fin D.rank))) hct ht)
        (Lx.ε Ax)).mp hmemx
    have htmemy : t * Ly.ε Ay * t⁻¹ ∈ leviM D ({y} : Set (Fin D.rank)) :=
      (Subgroup.mem_normalizer_iff.mp
        (torus_le_normalizer_leviM (D := D) (I := ({y} : Set (Fin D.rank))) hct ht)
        (Ly.ε Ay)).mp hmemy
    have hp₁ : ((g * t * Lx.ε Ax : K) : K ⧸ borel D H) ∈
        residue (cs) (stdδ hct) ({x} : Set (Fin D.rank)) ((g : K) : K ⧸ borel D H) := by
      rw [hmbSP_mk_mul_torus htB]
      exact mk_mul_mem_residue_of_mem_leviM hct hext g htmemx
    have hp₂ : ((g * t * Ly.ε Ay : K) : K ⧸ borel D H) ∈
        residue (cs) (stdδ hct) ({y} : Set (Fin D.rank)) ((g : K) : K ⧸ borel D H) := by
      rw [hmbSP_mk_mul_torus htB]
      exact mk_mul_mem_residue_of_mem_leviM hct hext g htmemy
    have hyp : (c₁ : K ⧸ borel D H) ∈ residue (cs) (stdδ hct) ({y} : Set (Fin D.rank))
        ((g * t * Lx.ε Ax : K) : K ⧸ borel D H) := by
      rw [hc₁]
      exact mk_mul_mem_residue_of_mem_leviM hct hext (g * t * Lx.ε Ax) hmemy
    have hyq : (c₁ : K ⧸ borel D H) ∈ residue (cs) (stdδ hct) ({x} : Set (Fin D.rank))
        ((g * t * Ly.ε Ay : K) : K ⧸ borel D H) := by
      rw [hc₁]
      have heq : ((g * t * Lx.ε Ax * Ly.ε Ay : K) : K ⧸ borel D H) =
          (((g * t * Ly.ε Ay) * Lx.ε Ax : K) : K ⧸ borel D H) := by
        rw [show (g * t * Lx.ε Ax * Ly.ε Ay : K) =
            g * t * (Lx.ε Ax * Ly.ε Ay) by group,
          show ((g * t * Ly.ε Ay) * Lx.ε Ax : K) =
            g * t * (Ly.ε Ay * Lx.ε Ax) by group,
          hmbSP_commutes_rankOne hext hmxy (Lx.ε Ax) (hmbS3_eps_mem_rankOne hx Ax)
            (Ly.ε Ay) (hmbS3_eps_mem_rankOne hy Ay)]
      rw [heq]
      exact mk_mul_mem_residue_of_mem_leviM hct hext (g * t * Ly.ε Ay) hmemx
    have houter := prodChart_symm_apply_of_mem (stdBuilding hct hext) hyx hcomm_xy
      ((g : K) : K ⧸ borel D H) hp₁ hp₂ hyp hyq
    have hpc : (prodChart (stdBuilding hct hext) hyx hcomm_xy ((g : K) : K ⧸ borel D H)).Φ
        (⟨(c₁ : K ⧸ borel D H), c₁.2⟩ :
          ↥(residue (cs) (stdδ hct) (insert y {x}) ((g : K) : K ⧸ borel D H))) =
        (⟨((g * t * Lx.ε Ax : K) : K ⧸ borel D H), hp₁⟩,
          ⟨((g * t * Ly.ε Ay : K) : K ⧸ borel D H), hp₂⟩) := by
      rw [Equiv.apply_eq_iff_eq_symm_apply]
      exact Subtype.ext houter.symm
    have hΦ : combined.Φ c₁ =
        ((slChart hct hext Lx hJx g).Φ ⟨((g * t * Lx.ε Ax : K) : K ⧸ borel D H), hp₁⟩,
          (slChart hct hext Ly hJy g).Φ ⟨((g * t * Ly.ε Ay : K) : K ⧸ borel D H), hp₂⟩) := by
      change (hmbSP_chart hct hext Lx Ly hJx hy hyx hcomm_xy (g := g) (hR := rfl)).Φ c₁ = _
      rw [hmbSP_chart, ChamberIso.trans_Φ_apply]
      change ((slChart hct hext Lx hJx g).prodCongr (slChart hct hext Ly hJy g)).Φ
          ((prodChart (stdBuilding hct hext) hyx hcomm_xy ((g : K) : K ⧸ borel D H)).Φ
            ((ChamberIso.restrictCongr (buildingOver (cs) (stdδ hct) (insert y {x}))
              (rfl : residue (cs) (stdδ hct) (insert y {x}) ((g : K) : K ⧸ borel D H) =
                residue (cs) (stdδ hct) (insert y {x}) ((g : K) : K ⧸ borel D H))).Φ c₁)) = _
      rw [show (ChamberIso.restrictCongr (buildingOver (cs) (stdδ hct) (insert y {x}))
          (rfl : residue (cs) (stdδ hct) (insert y {x}) ((g : K) : K ⧸ borel D H) =
            residue (cs) (stdδ hct) (insert y {x}) ((g : K) : K ⧸ borel D H))).Φ c₁ =
          (⟨(c₁ : K ⧸ borel D H), c₁.2⟩ :
            ↥(residue (cs) (stdδ hct) (insert y {x}) ((g : K) : K ⧸ borel D H))) from rfl]
      rw [hpc]
      rfl
    rw [hΦ]
    exact Prod.ext (hcoordx Ax _ rfl) (hcoordy Ay _ rfl)
  refine ⟨Dx, Dy, Dz, hDx, hDy, hDz, ?_⟩
  intro Ax Ay Az c hc
  have htB : t ∈ borel D H := iSup_le_borel ht
  have hmem_J₁ : Lx.ε Ax * Ly.ε Ay ∈ leviM D (insert y {x}) :=
    mul_mem (hmbS3_eps_mem_leviM hx (by simp) Ax) (hmbS3_eps_mem_leviM hy (by simp) Ay)
  have hmem_z : Lz.ε Az ∈ leviM D ({z} : Set (Fin D.rank)) :=
    hmbS3_eps_mem_leviM hz (by simp) Az
  have htmem₁ : t * (Lx.ε Ax * Ly.ε Ay) * t⁻¹ ∈ leviM D (insert y {x}) :=
    (Subgroup.mem_normalizer_iff.mp
      (torus_le_normalizer_leviM (D := D) (I := insert y {x}) hct ht)
      (Lx.ε Ax * Ly.ε Ay)).mp hmem_J₁
  have htmem_z : t * Lz.ε Az * t⁻¹ ∈ leviM D ({z} : Set (Fin D.rank)) :=
    (Subgroup.mem_normalizer_iff.mp
      (torus_le_normalizer_leviM (D := D) (I := ({z} : Set (Fin D.rank))) hct ht)
      (Lz.ε Az)).mp hmem_z
  have hp : ((g * t * Lx.ε Ax * Ly.ε Ay : K) : K ⧸ borel D H) ∈
      residue (cs) (stdδ hct) (insert y {x}) ((g : K) : K ⧸ borel D H) := by
    rw [show ((g * t * Lx.ε Ax * Ly.ε Ay : K) : K ⧸ borel D H) =
        ((g * t * (Lx.ε Ax * Ly.ε Ay) : K) : K ⧸ borel D H) by
      rw [show (g * t * Lx.ε Ax * Ly.ε Ay : K) = g * t * (Lx.ε Ax * Ly.ε Ay) by group]]
    rw [hmbSP_mk_mul_torus htB]
    exact mk_mul_mem_residue_of_mem_leviM hct hext g htmem₁
  have hq : ((g * t * Lz.ε Az : K) : K ⧸ borel D H) ∈
      residue (cs) (stdδ hct) ({z} : Set (Fin D.rank)) ((g : K) : K ⧸ borel D H) := by
    rw [hmbSP_mk_mul_torus htB]
    exact mk_mul_mem_residue_of_mem_leviM hct hext g htmem_z
  have hyp : (c : K ⧸ borel D H) ∈
      residue (cs) (stdδ hct) ({z} : Set (Fin D.rank))
        ((g * t * Lx.ε Ax * Ly.ε Ay : K) : K ⧸ borel D H) := by
    rw [hc]
    exact mk_mul_mem_residue_of_mem_leviM hct hext (g * t * Lx.ε Ax * Ly.ε Ay) hmem_z
  have hyq : (c : K ⧸ borel D H) ∈
      residue (cs) (stdδ hct) (insert y {x}) ((g * t * Lz.ε Az : K) : K ⧸ borel D H) := by
    rw [hc]
    have hcomm3 := hmbS3_commute3 (hext := hext) hx hy hz hmxz hmyz Ax Ay Az
    have heq : ((g * t * Lx.ε Ax * Ly.ε Ay * Lz.ε Az : K) : K ⧸ borel D H) =
        (((g * t * Lz.ε Az) * (Lx.ε Ax * Ly.ε Ay) : K) : K ⧸ borel D H) := by
      rw [show (g * t * Lx.ε Ax * Ly.ε Ay * Lz.ε Az : K) =
          g * t * (Lx.ε Ax * Ly.ε Ay * Lz.ε Az) by group,
        show ((g * t * Lz.ε Az) * (Lx.ε Ax * Ly.ε Ay) : K) =
          g * t * (Lz.ε Az * (Lx.ε Ax * Ly.ε Ay)) by group, hcomm3]
    rw [heq]
    exact mk_mul_mem_residue_of_mem_leviM hct hext (g * t * Lz.ε Az) hmem_J₁
  have houter := prodChart_symm_apply_of_mem (stdBuilding hct hext) hzJ₁ hcomm_outer
    ((g : K) : K ⧸ borel D H) hp hq hyp hyq
  have hpc : outer.Φ (⟨(c : K ⧸ borel D H), hR ▸ c.2⟩ :
      ↥(residue (cs) (stdδ hct) (insert z (insert y {x})) ((g : K) : K ⧸ borel D H))) =
      (⟨((g * t * Lx.ε Ax * Ly.ε Ay : K) : K ⧸ borel D H), hp⟩,
        ⟨((g * t * Lz.ε Az : K) : K ⧸ borel D H), hq⟩) := by
    rw [Equiv.apply_eq_iff_eq_symm_apply]
    exact Subtype.ext houter.symm
  have hΦ : (hmbS3_chart hct hext Lx Ly Lz hx hy hz hxy hxz hyz hmxy hmxz hmyz hR).Φ c =
      (combined.Φ ⟨((g * t * Lx.ε Ax * Ly.ε Ay : K) : K ⧸ borel D H), hp⟩,
        chartZ.Φ ⟨((g * t * Lz.ε Az : K) : K ⧸ borel D H), hq⟩) := by
    rw [hchart]
    change ((combined.prodCongr chartZ).Φ (outer.Φ
        ((ChamberIso.restrictCongr (buildingOver (cs) (stdδ hct) (insert z (insert y {x})))
          hR).Φ c))) = _
    have hc' : (ChamberIso.restrictCongr (buildingOver (cs) (stdδ hct) (insert z (insert y {x})))
        hR).Φ c = (⟨(c : K ⧸ borel D H), hR ▸ c.2⟩ :
        ↥(residue (cs) (stdδ hct) (insert z (insert y {x})) ((g : K) : K ⧸ borel D H))) := rfl
    rw [hc', hpc]
    rfl
  rw [hΦ]
  exact Prod.ext
    (hcombined Ax Ay _ rfl)
    (hcoordz Az ⟨((g * t * Lz.ε Az : K) : K ⧸ borel D H), hq⟩ rfl)

end CFSG.ClassicalInvolution.Phan.PhanE.Res

end
