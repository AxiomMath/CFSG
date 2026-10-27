module

public import CFSG.LocalAnalysis.StandardType.PhanEResSeamProd3B

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

private theorem hmbS3_chart_e_x [CharP Fld 2] (Lx Ly Lz : SLPath M 1) {x y z : Fin D.rank}
    (hx : Lx.e 0 = x) (hy : Ly.e 0 = y) (hz : Lz.e 0 = z) (hxy : x ≠ y) (hxz : x ≠ z)
    (hyz : y ≠ z)
    (hmxy : coxeterMatrix D.isFiniteType x y = 2)
    (hmxz : coxeterMatrix D.isFiniteType x z = 2)
    (hmyz : coxeterMatrix D.isFiniteType y z = 2)
    {a : K ⧸ borel D H} {g : K}
    (hR : residue (cs) (stdδ hct) (insert z (insert y {x})) a =
      residue (cs) (stdδ hct) (insert z (insert y {x})) ((g : K) : K ⧸ borel D H)) :
    (hmbS3_chart hct hext Lx Ly Lz hx hy hz hxy hxz hyz hmxy hmxz hmyz hR).e
        ⟨x, Set.mem_insert_of_mem z (Set.mem_insert_of_mem y (Set.mem_singleton x))⟩ =
      Sum.inl (Sum.inl (0 : Fin 1)) := by
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
  rw [hchart, ChamberIso.trans_e_apply]
  change (outer.trans (combined.prodCongr chartZ)).e
      ⟨x, Set.mem_insert_of_mem z (Set.mem_insert_of_mem y (Set.mem_singleton x))⟩ =
    Sum.inl (Sum.inl (0 : Fin 1))
  rw [ChamberIso.trans_e_apply]
  change (combined.prodCongr chartZ).e (outer.e
      ⟨x, Set.mem_insert_of_mem z (Set.mem_insert_of_mem y (Set.mem_singleton x))⟩) =
    Sum.inl (Sum.inl (0 : Fin 1))
  have houter : outer.e ⟨x, Set.mem_insert_of_mem z
        (Set.mem_insert_of_mem y (Set.mem_singleton x))⟩ =
      Sum.inl ⟨x, Set.mem_insert_of_mem y (Set.mem_singleton x)⟩ := by
    change (prodChart (stdBuilding hct hext) hzJ₁ hcomm_outer ((g : K) : K ⧸ borel D H)).e
        ⟨x, Set.mem_insert_of_mem z (Set.mem_insert_of_mem y (Set.mem_singleton x))⟩ = _
    exact prodChart_e_of_mem (hB := stdBuilding hct hext) (hz := hzJ₁) (hcomm := hcomm_outer)
      (c := ((g : K) : K ⧸ borel D H)) (i := x) (Set.mem_insert_of_mem y (Set.mem_singleton x))
  rw [houter]
  change Sum.inl (combined.e ⟨x, Set.mem_insert_of_mem y (Set.mem_singleton x)⟩) =
    Sum.inl (Sum.inl (0 : Fin 1))
  congr 1
  change (hmbSP_chart hct hext Lx Ly hJx hy hyx hcomm_xy (g := g) (hR := rfl)).e
      ⟨x, Set.mem_insert_of_mem y (Set.mem_singleton x)⟩ = Sum.inl (0 : Fin 1)
  rw [hmbSP_chart, ChamberIso.trans_e_apply]
  change ((prodChart (stdBuilding hct hext) hyx hcomm_xy ((g : K) : K ⧸ borel D H)).trans
      ((slChart hct hext Lx hJx g).prodCongr
        (slChart hct hext Ly (hmbS3_range_e_one hy) g))).e
      ⟨x, Set.mem_insert_of_mem y (Set.mem_singleton x)⟩ = Sum.inl (0 : Fin 1)
  rw [ChamberIso.trans_e_apply]
  change ((slChart hct hext Lx hJx g).prodCongr
      (slChart hct hext Ly (hmbS3_range_e_one hy) g)).e
      ((prodChart (stdBuilding hct hext) hyx hcomm_xy ((g : K) : K ⧸ borel D H)).e
        ⟨x, Set.mem_insert_of_mem y (Set.mem_singleton x)⟩) = Sum.inl (0 : Fin 1)
  have hinner : (prodChart (stdBuilding hct hext) hyx hcomm_xy ((g : K) : K ⧸ borel D H)).e
      ⟨x, Set.mem_insert_of_mem y (Set.mem_singleton x)⟩ =
      Sum.inl ⟨x, Set.mem_singleton x⟩ :=
    prodChart_e_of_mem (hB := stdBuilding hct hext) (hz := hyx) (hcomm := hcomm_xy)
      (c := ((g : K) : K ⧸ borel D H)) (i := x) (Set.mem_singleton x)
  rw [hinner]
  change Sum.inl ((slChart hct hext Lx hJx g).e ⟨x, Set.mem_singleton x⟩) =
    Sum.inl (0 : Fin 1)
  congr 1
  rw [show (⟨x, Set.mem_singleton x⟩ : ↥({x} : Set (Fin D.rank))) =
      ⟨Lx.e 0, by rw [hx]; exact Set.mem_singleton x⟩ from Subtype.ext hx.symm]
  exact slChart_e_apply hct hext Lx hJx g 0 (by rw [hx]; exact Set.mem_singleton x)

private theorem hmbS3_chart_e_y [CharP Fld 2] (Lx Ly Lz : SLPath M 1) {x y z : Fin D.rank}
    (hx : Lx.e 0 = x) (hy : Ly.e 0 = y) (hz : Lz.e 0 = z) (hxy : x ≠ y) (hxz : x ≠ z)
    (hyz : y ≠ z)
    (hmxy : coxeterMatrix D.isFiniteType x y = 2)
    (hmxz : coxeterMatrix D.isFiniteType x z = 2)
    (hmyz : coxeterMatrix D.isFiniteType y z = 2)
    {a : K ⧸ borel D H} {g : K}
    (hR : residue (cs) (stdδ hct) (insert z (insert y {x})) a =
      residue (cs) (stdδ hct) (insert z (insert y {x})) ((g : K) : K ⧸ borel D H)) :
    (hmbS3_chart hct hext Lx Ly Lz hx hy hz hxy hxz hyz hmxy hmxz hmyz hR).e
        ⟨y, Set.mem_insert_of_mem z (Set.mem_insert y {x})⟩ =
      Sum.inl (Sum.inr (0 : Fin 1)) := by
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
  rw [hchart, ChamberIso.trans_e_apply]
  change (outer.trans (combined.prodCongr chartZ)).e
      ⟨y, Set.mem_insert_of_mem z (Set.mem_insert y {x})⟩ = Sum.inl (Sum.inr (0 : Fin 1))
  rw [ChamberIso.trans_e_apply]
  change (combined.prodCongr chartZ).e (outer.e
      ⟨y, Set.mem_insert_of_mem z (Set.mem_insert y {x})⟩) = Sum.inl (Sum.inr (0 : Fin 1))
  have houter : outer.e ⟨y, Set.mem_insert_of_mem z (Set.mem_insert y {x})⟩ =
      Sum.inl ⟨y, Set.mem_insert y {x}⟩ := by
    change (prodChart (stdBuilding hct hext) hzJ₁ hcomm_outer ((g : K) : K ⧸ borel D H)).e
        ⟨y, Set.mem_insert_of_mem z (Set.mem_insert y {x})⟩ = _
    exact prodChart_e_of_mem (hB := stdBuilding hct hext) (hz := hzJ₁) (hcomm := hcomm_outer)
      (c := ((g : K) : K ⧸ borel D H)) (i := y) (Set.mem_insert y {x})
  rw [houter]
  change Sum.inl (combined.e ⟨y, Set.mem_insert y {x}⟩) = Sum.inl (Sum.inr (0 : Fin 1))
  congr 1
  change (hmbSP_chart hct hext Lx Ly hJx hy hyx hcomm_xy (g := g) (hR := rfl)).e
      ⟨y, Set.mem_insert y {x}⟩ = Sum.inr (0 : Fin 1)
  rw [hmbSP_chart, ChamberIso.trans_e_apply]
  change ((prodChart (stdBuilding hct hext) hyx hcomm_xy ((g : K) : K ⧸ borel D H)).trans
      ((slChart hct hext Lx hJx g).prodCongr
        (slChart hct hext Ly (hmbS3_range_e_one hy) g))).e
      ⟨y, Set.mem_insert y {x}⟩ = Sum.inr (0 : Fin 1)
  rw [ChamberIso.trans_e_apply]
  change ((slChart hct hext Lx hJx g).prodCongr
      (slChart hct hext Ly (hmbS3_range_e_one hy) g)).e
      ((prodChart (stdBuilding hct hext) hyx hcomm_xy ((g : K) : K ⧸ borel D H)).e
        ⟨y, Set.mem_insert y {x}⟩) = Sum.inr (0 : Fin 1)
  have hinner : (prodChart (stdBuilding hct hext) hyx hcomm_xy ((g : K) : K ⧸ borel D H)).e
      ⟨y, Set.mem_insert y {x}⟩ = Sum.inr ⟨y, rfl⟩ :=
    prodChart_e_self (hB := stdBuilding hct hext) (hz := hyx) (hcomm := hcomm_xy)
      (c := ((g : K) : K ⧸ borel D H))
  rw [hinner]
  change Sum.inr ((slChart hct hext Ly (hmbS3_range_e_one hy) g).e ⟨y, rfl⟩) =
    Sum.inr (0 : Fin 1)
  congr 1
  rw [show (⟨y, rfl⟩ : ↥({y} : Set (Fin D.rank))) =
      ⟨Ly.e 0, by rw [hy]; exact Set.mem_singleton y⟩ from Subtype.ext hy.symm]
  exact slChart_e_apply hct hext Ly (hmbS3_range_e_one hy) g 0
    (by rw [hy]; exact Set.mem_singleton y)

private theorem hmbS3_chart_e_z [CharP Fld 2] (Lx Ly Lz : SLPath M 1) {x y z : Fin D.rank}
    (hx : Lx.e 0 = x) (hy : Ly.e 0 = y) (hz : Lz.e 0 = z) (hxy : x ≠ y) (hxz : x ≠ z)
    (hyz : y ≠ z)
    (hmxy : coxeterMatrix D.isFiniteType x y = 2)
    (hmxz : coxeterMatrix D.isFiniteType x z = 2)
    (hmyz : coxeterMatrix D.isFiniteType y z = 2)
    {a : K ⧸ borel D H} {g : K}
    (hR : residue (cs) (stdδ hct) (insert z (insert y {x})) a =
      residue (cs) (stdδ hct) (insert z (insert y {x})) ((g : K) : K ⧸ borel D H)) :
    (hmbS3_chart hct hext Lx Ly Lz hx hy hz hxy hxz hyz hmxy hmxz hmyz hR).e
        ⟨z, Set.mem_insert z (insert y {x})⟩ = Sum.inr (0 : Fin 1) := by
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
  rw [hchart, ChamberIso.trans_e_apply]
  change (outer.trans (combined.prodCongr chartZ)).e
      ⟨z, Set.mem_insert z (insert y {x})⟩ = Sum.inr (0 : Fin 1)
  rw [ChamberIso.trans_e_apply]
  change (combined.prodCongr chartZ).e (outer.e
      ⟨z, Set.mem_insert z (insert y {x})⟩) = Sum.inr (0 : Fin 1)
  have houter : outer.e ⟨z, Set.mem_insert z (insert y {x})⟩ = Sum.inr ⟨z, rfl⟩ := by
    change (prodChart (stdBuilding hct hext) hzJ₁ hcomm_outer ((g : K) : K ⧸ borel D H)).e
        ⟨z, Set.mem_insert z (insert y {x})⟩ = _
    exact prodChart_e_self (hB := stdBuilding hct hext) (hz := hzJ₁) (hcomm := hcomm_outer)
      (c := ((g : K) : K ⧸ borel D H))
  rw [houter]
  change Sum.inr (chartZ.e ⟨z, rfl⟩) = Sum.inr (0 : Fin 1)
  congr 1
  rw [show (⟨z, rfl⟩ : ↥({z} : Set (Fin D.rank))) =
      ⟨Lz.e 0, by rw [hz]; exact Set.mem_singleton z⟩ from Subtype.ext hz.symm]
  exact slChart_e_apply hct hext Lz hJz g 0 (by rw [hz]; exact Set.mem_singleton z)

private theorem hmbS3_mem_RHS_x {dx dy dz : List ℕ} :
    Sum.inl (Sum.inl (0 : Fin 1)) ∈
      (Sum.inl '' (Sum.inl '' cutTypes 1 dx ∪ Sum.inr '' cutTypes 1 dy) ∪
        Sum.inr '' cutTypes 1 dz : Set ((Fin 1 ⊕ Fin 1) ⊕ Fin 1)) ↔
      (0 : Fin 1) ∈ cutTypes 1 dx := by
  constructor
  · rintro (⟨u, hu, h⟩ | ⟨u, hu, h⟩)
    · obtain ⟨v, hv, hvu⟩ | ⟨v, hv, hvu⟩ := hu
      · have h' := h
        rw [← hvu] at h'
        have h2 : v = 0 := Sum.inl.inj (Sum.inl.inj h')
        rwa [h2] at hv
      · have h' := h
        rw [← hvu] at h'
        exact absurd (Sum.inl.inj h') (by simp)
    · exact absurd h (by simp)
  · intro h
    exact Or.inl ⟨Sum.inl (0 : Fin 1), Or.inl ⟨0, h, rfl⟩, rfl⟩

private theorem hmbS3_mem_RHS_y {dx dy dz : List ℕ} :
    Sum.inl (Sum.inr (0 : Fin 1)) ∈
      (Sum.inl '' (Sum.inl '' cutTypes 1 dx ∪ Sum.inr '' cutTypes 1 dy) ∪
        Sum.inr '' cutTypes 1 dz : Set ((Fin 1 ⊕ Fin 1) ⊕ Fin 1)) ↔
      (0 : Fin 1) ∈ cutTypes 1 dy := by
  constructor
  · rintro (⟨u, hu, h⟩ | ⟨u, hu, h⟩)
    · obtain ⟨v, hv, hvu⟩ | ⟨v, hv, hvu⟩ := hu
      · have h' := h
        rw [← hvu] at h'
        exact absurd (Sum.inl.inj h') (by simp)
      · have h' := h
        rw [← hvu] at h'
        have h2 : v = 0 := Sum.inr.inj (Sum.inl.inj h')
        rwa [h2] at hv
    · exact absurd h (by simp)
  · intro h
    exact Or.inl ⟨Sum.inr (0 : Fin 1), Or.inr ⟨0, h, rfl⟩, rfl⟩

private theorem hmbS3_mem_RHS_z {dx dy dz : List ℕ} :
    Sum.inr (0 : Fin 1) ∈
      (Sum.inl '' (Sum.inl '' cutTypes 1 dx ∪ Sum.inr '' cutTypes 1 dy) ∪
        Sum.inr '' cutTypes 1 dz : Set ((Fin 1 ⊕ Fin 1) ⊕ Fin 1)) ↔
      (0 : Fin 1) ∈ cutTypes 1 dz := by
  constructor
  · rintro (⟨u, hu, h⟩ | ⟨u, hu, h⟩)
    · exact absurd h (by simp)
    · have h2 : u = 0 := Sum.inr.inj h
      rwa [h2] at hu
  · intro h
    exact Or.inr ⟨0, h, rfl⟩

theorem hmbS3_core [CharP Fld 2] (Lx Ly Lz : SLPath M 1) {x y z : Fin D.rank}
    (hx : Lx.e 0 = x) (hy : Ly.e 0 = y) (hz : Lz.e 0 = z) (hxy : x ≠ y) (hxz : x ≠ z)
    (hyz : y ≠ z)
    (hmxy : coxeterMatrix D.isFiniteType x y = 2)
    (hmxz : coxeterMatrix D.isFiniteType x z = 2)
    (hmyz : coxeterMatrix D.isFiniteType y z = 2)
    {a : K ⧸ borel D H} {g : K} {I : Set (Fin D.rank)} {w₀ : W} (F : FrobData D n H w₀)
    (hIJ : I ⊆ insert z (insert y {x}))
    (hR : residue (cs) (stdδ hct) (insert z (insert y {x})) a =
      residue (cs) (stdδ hct) (insert z (insert y {x})) ((g : K) : K ⧸ borel D H))
    (hcore : Gate.flipCore (cs) (stdδ hct) (stdFlip F (nrep hct w₀)) (insert z (insert y {x})) a =
      residue (cs) (stdδ hct) I ((g : K) : K ⧸ borel D H))
    {dx dy dz : List ℕ} (hdx : IsCut 2 dx) (hdy : IsCut 2 dy) (hdz : IsCut 2 dz)
    (hIx : x ∈ I ↔ (0 : Fin 1) ∈ cutTypes 1 dx)
    (hIy : y ∈ I ↔ (0 : Fin 1) ∈ cutTypes 1 dy)
    (hIz : z ∈ I ↔ (0 : Fin 1) ∈ cutTypes 1 dz) :
    ∀ c : ↥(residue (cs) (stdδ hct) (insert z (insert y {x})) a),
      (c : K ⧸ borel D H) ∈ Gate.flipCore (cs) (stdδ hct) (stdFlip F (nrep hct w₀))
          (insert z (insert y {x})) a ↔
        (hmbS3_chart hct hext Lx Ly Lz hx hy hz hxy hxz hyz hmxy hmxz hmyz hR).Φ c ∈
          (refSet Fld 2 dx ×ˢ refSet Fld 2 dy) ×ˢ refSet Fld 2 dz := by
  have hiff : ∀ j : ↥(insert z (insert y ({x} : Set (Fin D.rank)))),
      (j : Fin D.rank) ∈ I ↔
        (hmbS3_chart hct hext Lx Ly Lz hx hy hz hxy hxz hyz hmxy hmxz hmyz hR).e j ∈
          (Sum.inl '' (Sum.inl '' cutTypes 1 dx ∪ Sum.inr '' cutTypes 1 dy) ∪
            Sum.inr '' cutTypes 1 dz : Set ((Fin 1 ⊕ Fin 1) ⊕ Fin 1)) := by
    intro j
    have hjJ : (j : Fin D.rank) ∈ insert z (insert y {x}) := j.2
    rcases Set.mem_insert_iff.mp hjJ with hjz | hjyx
    · have hj : j = (⟨z, Set.mem_insert z (insert y {x})⟩ :
          ↥(insert z (insert y ({x} : Set (Fin D.rank))))) := Subtype.ext hjz
      rw [hj, hmbS3_chart_e_z hct hext Lx Ly Lz hx hy hz hxy hxz hyz hmxy hmxz hmyz hR,
        hIz, hmbS3_mem_RHS_z]
    · rcases Set.mem_insert_iff.mp hjyx with hjy | hjx
      · have hj : j = (⟨y, Set.mem_insert_of_mem z (Set.mem_insert y {x})⟩ :
            ↥(insert z (insert y ({x} : Set (Fin D.rank))))) := Subtype.ext hjy
        rw [hj, hmbS3_chart_e_y hct hext Lx Ly Lz hx hy hz hxy hxz hyz hmxy hmxz hmyz hR,
          hIy, hmbS3_mem_RHS_y]
      · have hj : j = (⟨x, Set.mem_insert_of_mem z
            (Set.mem_insert_of_mem y (Set.mem_singleton x))⟩ :
            ↥(insert z (insert y ({x} : Set (Fin D.rank))))) := Subtype.ext hjx
        rw [hj, hmbS3_chart_e_x hct hext Lx Ly Lz hx hy hz hxy hxz hyz hmxy hmxz hmyz hR,
          hIx, hmbS3_mem_RHS_x]
  have htype : (hmbS3_chart hct hext Lx Ly Lz hx hy hz hxy hxz hyz hmxy hmxz hmyz hR).e ''
      {j : ↥(insert z (insert y ({x} : Set (Fin D.rank)))) | (j : Fin D.rank) ∈ I} =
      Sum.inl '' (Sum.inl '' cutTypes 1 dx ∪ Sum.inr '' cutTypes 1 dy) ∪
        Sum.inr '' cutTypes 1 dz := by
    ext w
    constructor
    · rintro ⟨j, hj, rfl⟩
      exact (hiff j).mp hj
    · intro hw
      rcases hw with (⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩)
      · rcases hu with ⟨v, hv, rfl⟩ | ⟨v, hv, rfl⟩
        · obtain rfl : v = 0 := Subsingleton.elim v 0
          exact ⟨⟨x, Set.mem_insert_of_mem z (Set.mem_insert_of_mem y (Set.mem_singleton x))⟩,
            (hIx).mpr hv,
            hmbS3_chart_e_x hct hext Lx Ly Lz hx hy hz hxy hxz hyz hmxy hmxz hmyz hR⟩
        · obtain rfl : v = 0 := Subsingleton.elim v 0
          exact ⟨⟨y, Set.mem_insert_of_mem z (Set.mem_insert y {x})⟩,
            (hIy).mpr hv,
            hmbS3_chart_e_y hct hext Lx Ly Lz hx hy hz hxy hxz hyz hmxy hmxz hmyz hR⟩
      · obtain rfl : u = 0 := Subsingleton.elim u 0
        exact ⟨⟨z, Set.mem_insert z (insert y {x})⟩, (hIz).mpr hu,
          hmbS3_chart_e_z hct hext Lx Ly Lz hx hy hz hxy hxz hyz hmxy hmxz hmyz hR⟩
  have hresX : (flagSys Fld 1).residue (cutTypes 1 dx) (stdFlag Fld 2) = refSet Fld 2 dx := by
    rw [← residue_flagδ_eq (K := Fld) (cutTypes 1 dx) (stdFlag Fld 2),
      residue_cutTypes_eq hdx (stdFlag_mem_refSet (K := Fld) hdx)]
  have hresY : (flagSys Fld 1).residue (cutTypes 1 dy) (stdFlag Fld 2) = refSet Fld 2 dy := by
    rw [← residue_flagδ_eq (K := Fld) (cutTypes 1 dy) (stdFlag Fld 2),
      residue_cutTypes_eq hdy (stdFlag_mem_refSet (K := Fld) hdy)]
  have hresZ : (flagSys Fld 1).residue (cutTypes 1 dz) (stdFlag Fld 2) = refSet Fld 2 dz := by
    rw [← residue_flagδ_eq (K := Fld) (cutTypes 1 dz) (stdFlag Fld 2),
      residue_cutTypes_eq hdz (stdFlag_mem_refSet (K := Fld) hdz)]
  have hres : (((flagSys Fld 1).prod (flagSys Fld 1)).prod (flagSys Fld 1)).residue
      (Sum.inl '' (Sum.inl '' cutTypes 1 dx ∪ Sum.inr '' cutTypes 1 dy) ∪
        Sum.inr '' cutTypes 1 dz) ((stdFlag Fld 2, stdFlag Fld 2), stdFlag Fld 2) =
      (refSet Fld 2 dx ×ˢ refSet Fld 2 dy) ×ˢ refSet Fld 2 dz := by
    rw [hmbSP_prod_residue, hmbSP_prod_residue, hresX, hresY, hresZ]
  intro c
  have hg_mem : ((g : K) : K ⧸ borel D H) ∈
      residue (cs) (stdδ hct) (insert z (insert y {x})) a :=
    hR.symm ▸ self_mem_residue _ _
  let x₀ : ↥(residue (cs) (stdδ hct) (insert z (insert y {x})) a) :=
    ⟨((g : K) : K ⧸ borel D H), hg_mem⟩
  have hxΦ : (hmbS3_chart hct hext Lx Ly Lz hx hy hz hxy hxz hyz hmxy hmxz hmyz hR).Φ x₀ =
      ((stdFlag Fld 2, stdFlag Fld 2), stdFlag Fld 2) := by
    have h1 := hmbS3_chart_symm_apply hct hext Lx Ly Lz hx hy hz hxy hxz hyz hmxy hmxz hmyz
      hR 1 1 1
    simp only [map_one, flagAct_one, mul_one] at h1
    have h2 : (hmbS3_chart hct hext Lx Ly Lz hx hy hz hxy hxz hyz hmxy hmxz hmyz hR).Φ.symm
        ((stdFlag Fld 2, stdFlag Fld 2), stdFlag Fld 2) = x₀ := Subtype.ext h1
    rw [← h2]
    exact Equiv.apply_symm_apply _ _
  have hmem := mem_residue_iff_of_chamberIso (stdBuilding hct hext)
    (hmbS3_chart hct hext Lx Ly Lz hx hy hz hxy hxz hyz hmxy hmxz hmyz hR) hIJ x₀ c
  rw [htype, hxΦ, hres] at hmem
  rw [hcore]
  exact hmem

end CFSG.ClassicalInvolution.Phan.PhanE.Res

end
