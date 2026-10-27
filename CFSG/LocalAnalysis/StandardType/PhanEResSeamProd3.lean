module

public import CFSG.LocalAnalysis.StandardType.PhanEResSeamProd3Aux

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

@[expose] def NodeKap (L : SLPath M 1) (v : W) (d : List ℕ) (θ : Fld →+* Fld)
    (P : SpecialLinearGroup (Fin 2) Fld) (pol : Bool) : Prop :=
  ∀ k ∈ cutTypes 1 d, ∀ c : Fld,
    nrep hct v * F.φ (L.ε (tv Fld k.castSucc k.succ c)) * (nrep hct v)⁻¹ =
        L.ε (kapMat θ pol P (tv Fld k.castSucc k.succ c)) ∧
      nrep hct v * F.φ (L.ε (tv Fld k.succ k.castSucc c)) * (nrep hct v)⁻¹ =
        L.ε (kapMat θ pol P (tv Fld k.succ k.castSucc c))

@[expose] def StabV2 (d : List ℕ) (N : GL (Fin 2) Fld) : Prop :=
  ∀ b, b < d.length → (Vsub 2 (d.getD b 0)).map (glLin N).toLinearMap = Vsub 2 (d.getD b 0)

include hext hw₀ hsq in
theorem exists_seam_prod3 [CharP Fld 2] (Lx Ly Lz : SLPath M 1) {x y z : Fin D.rank}
    (hx : Lx.e 0 = x) (hy : Ly.e 0 = y) (hz : Lz.e 0 = z) (hxy : x ≠ y) (hxz : x ≠ z)
    (hyz : y ≠ z)
    (hmxy : coxeterMatrix D.isFiniteType x y = 2) (hmxz : coxeterMatrix D.isFiniteType x z = 2)
    (hmyz : coxeterMatrix D.isFiniteType y z = 2)
    {a : K ⧸ borel D H} {g : K} {v : W} {I : Set (Fin D.rank)} {t₀ l₀ : K}
    (hIJ : I ⊆ insert z (insert y {x}))
    (hR : residue (cs) (stdδ hct) (insert z (insert y {x})) a =
      residue (cs) (stdδ hct) (insert z (insert y {x})) ((g : K) : K ⧸ borel D H))
    (hcore : Gate.flipCore (cs) (stdδ hct) (stdFlip F (nrep hct w₀)) (insert z (insert y {x})) a =
      residue (cs) (stdδ hct) I ((g : K) : K ⧸ borel D H))
    (ht₀ : t₀ ∈ ⨆ k, H k) (hl₀ : l₀ ∈ leviM D I)
    (hψ : ∀ l ∈ leviM D I,
      Gate.flipPsi (cs) (stdδ hct) (stdFlip F (nrep hct w₀)) (insert z (insert y {x})) a
          ((g * l : K) : K ⧸ borel D H) =
        ((g * t₀ * l₀ * (nrep hct v * F.φ l * (nrep hct v)⁻¹) : K) : K ⧸ borel D H))
    {dx dy dz : List ℕ} (hdx : IsCut 2 dx) (hdy : IsCut 2 dy) (hdz : IsCut 2 dz)
    (hIx : x ∈ I ↔ (0 : Fin 1) ∈ cutTypes 1 dx) (hIy : y ∈ I ↔ (0 : Fin 1) ∈ cutTypes 1 dy)
    (hIz : z ∈ I ↔ (0 : Fin 1) ∈ cutTypes 1 dz) (θ : Fld →+* Fld)
    (Px Py Pz : SpecialLinearGroup (Fin 2) Fld) (polx poly polz : Bool)
    (hκx : NodeKap hct F Lx v dx θ Px polx) (hκy : NodeKap hct F Ly v dy θ Py poly)
    (hκz : NodeKap hct F Lz v dz θ Pz polz) :
    ∃ (Θ₀ : ChamberIso ((buildingOver (cs) (stdδ hct) (insert z (insert y {x}))).restrict
        (residue (cs) (stdδ hct) (insert z (insert y {x})) a))
          (((flagSys Fld 1).prod (flagSys Fld 1)).prod (flagSys Fld 1)))
      (Nx Ny Nz : GL (Fin 2) Fld),
      StabV2 dx Nx ∧ StabV2 dy Ny ∧ StabV2 dz Nz ∧
      (∀ c : ↥(residue (cs) (stdδ hct) (insert z (insert y {x})) a),
        (c : K ⧸ borel D H) ∈ Gate.flipCore (cs) (stdδ hct) (stdFlip F (nrep hct w₀))
            (insert z (insert y {x})) a ↔
          Θ₀.Φ c ∈ (refSet Fld 2 dx ×ˢ refSet Fld 2 dy) ×ˢ refSet Fld 2 dz) ∧
      ∀ Ax ∈ blockSL Fld 1 dx, ∀ Ay ∈ blockSL Fld 1 dy, ∀ Az ∈ blockSL Fld 1 dz,
        ∀ c c' : ↥(residue (cs) (stdδ hct) (insert z (insert y {x})) a),
        Θ₀.Φ c = ((flagAct (SpecialLinearGroup.toGL Ax) (stdFlag Fld 2),
          flagAct (SpecialLinearGroup.toGL Ay) (stdFlag Fld 2)),
            flagAct (SpecialLinearGroup.toGL Az) (stdFlag Fld 2)) →
        (c' : K ⧸ borel D H) = Gate.flipPsi (cs) (stdδ hct) (stdFlip F (nrep hct w₀))
          (insert z (insert y {x})) a (c : K ⧸ borel D H) →
        Θ₀.Φ c' =
          ((flagAct Nx (flagAct (SpecialLinearGroup.toGL (kapMat θ polx Px Ax)) (stdFlag Fld 2)),
            flagAct Ny (flagAct (SpecialLinearGroup.toGL (kapMat θ poly Py Ay)) (stdFlag Fld 2))),
              flagAct Nz (flagAct (SpecialLinearGroup.toGL (kapMat θ polz Pz Az))
                (stdFlag Fld 2))) := by
  have hPux : ∀ k ∈ cutTypes 1 dx, ∀ c : Fld,
      nrep hct v * F.φ (Lx.ε (tv Fld k.castSucc k.succ c)) * (nrep hct v)⁻¹ =
        Lx.ε (kapMat θ polx Px (tv Fld k.castSucc k.succ c)) :=
    fun k hk c => (hκx k hk c).1
  have hPlx : ∀ k ∈ cutTypes 1 dx, ∀ c : Fld,
      nrep hct v * F.φ (Lx.ε (tv Fld k.succ k.castSucc c)) * (nrep hct v)⁻¹ =
        Lx.ε (kapMat θ polx Px (tv Fld k.succ k.castSucc c)) :=
    fun k hk c => (hκx k hk c).2
  have hPuy : ∀ k ∈ cutTypes 1 dy, ∀ c : Fld,
      nrep hct v * F.φ (Ly.ε (tv Fld k.castSucc k.succ c)) * (nrep hct v)⁻¹ =
        Ly.ε (kapMat θ poly Py (tv Fld k.castSucc k.succ c)) :=
    fun k hk c => (hκy k hk c).1
  have hPly : ∀ k ∈ cutTypes 1 dy, ∀ c : Fld,
      nrep hct v * F.φ (Ly.ε (tv Fld k.succ k.castSucc c)) * (nrep hct v)⁻¹ =
        Ly.ε (kapMat θ poly Py (tv Fld k.succ k.castSucc c)) :=
    fun k hk c => (hκy k hk c).2
  have hPuz : ∀ k ∈ cutTypes 1 dz, ∀ c : Fld,
      nrep hct v * F.φ (Lz.ε (tv Fld k.castSucc k.succ c)) * (nrep hct v)⁻¹ =
        Lz.ε (kapMat θ polz Pz (tv Fld k.castSucc k.succ c)) :=
    fun k hk c => (hκz k hk c).1
  have hPlz : ∀ k ∈ cutTypes 1 dz, ∀ c : Fld,
      nrep hct v * F.φ (Lz.ε (tv Fld k.succ k.castSucc c)) * (nrep hct v)⁻¹ =
        Lz.ε (kapMat θ polz Pz (tv Fld k.succ k.castSucc c)) :=
    fun k hk c => (hκz k hk c).2
  have hκx' : ∀ A ∈ blockSL Fld 1 dx,
      nrep hct v * F.φ (Lx.ε A) * (nrep hct v)⁻¹ = Lx.ε (kapMat θ polx Px A) :=
    hmbSP_kappa_blockSL hct F Lx θ Px polx hPux hPlx
  have hκy' : ∀ A ∈ blockSL Fld 1 dy,
      nrep hct v * F.φ (Ly.ε A) * (nrep hct v)⁻¹ = Ly.ε (kapMat θ poly Py A) :=
    hmbSP_kappa_blockSL hct F Ly θ Py poly hPuy hPly
  have hκz' : ∀ A ∈ blockSL Fld 1 dz,
      nrep hct v * F.φ (Lz.ε A) * (nrep hct v)⁻¹ = Lz.ε (kapMat θ polz Pz A) :=
    hmbSP_kappa_blockSL hct F Lz θ Pz polz hPuz hPlz
  obtain ⟨A₀x, hA₀x, A₀y, hA₀y, A₀z, hA₀z, hl₀_eq⟩ :=
    hmbS3_decomp3 (hext := hext) hx hy hz hmxy hmxz hmyz hIJ hIx hIy hIz hl₀
  obtain ⟨Dx, Dy, Dz, hDx, hDy, hDz, hcoord⟩ :=
    hmbS3_chart_coord hct hext Lx Ly Lz hx hy hz hxy hxz hyz hmxy hmxz hmyz hR ht₀
  refine ⟨hmbS3_chart hct hext Lx Ly Lz hx hy hz hxy hxz hyz hmxy hmxz hmyz hR,
    Dx * SpecialLinearGroup.toGL A₀x, Dy * SpecialLinearGroup.toGL A₀y,
    Dz * SpecialLinearGroup.toGL A₀z, ?_, ?_, ?_, ?_, ?_⟩
  · exact StabV.mul (fun b _ => hmbSP_diag_stabV hDx (dx.getD b 0))
      (hmbSP_blockSL_stabV (m := 1) dx A₀x hA₀x)
  · exact StabV.mul (fun b _ => hmbSP_diag_stabV hDy (dy.getD b 0))
      (hmbSP_blockSL_stabV (m := 1) dy A₀y hA₀y)
  · exact StabV.mul (fun b _ => hmbSP_diag_stabV hDz (dz.getD b 0))
      (hmbSP_blockSL_stabV (m := 1) dz A₀z hA₀z)
  · exact hmbS3_core hct hext Lx Ly Lz hx hy hz hxy hxz hyz hmxy hmxz hmyz F hIJ hR hcore
      hdx hdy hdz hIx hIy hIz
  · intro Ax hAx Ay hAy Az hAz c c' hc hc'
    have hcsymm : (c : K ⧸ borel D H) =
        ((g * Lx.ε Ax * Ly.ε Ay * Lz.ε Az : K) : K ⧸ borel D H) := by
      have h1 := hmbS3_chart_symm_apply hct hext Lx Ly Lz hx hy hz hxy hxz hyz hmxy hmxz hmyz
        hR Ax Ay Az
      have h2 : c = (hmbS3_chart hct hext Lx Ly Lz hx hy hz hxy hxz hyz hmxy hmxz hmyz hR).Φ.symm
          ((flagAct (SpecialLinearGroup.toGL Ax) (stdFlag Fld 2),
            flagAct (SpecialLinearGroup.toGL Ay) (stdFlag Fld 2)),
            flagAct (SpecialLinearGroup.toGL Az) (stdFlag Fld 2)) := by
        rw [← hc]
        exact (Equiv.symm_apply_apply _ _).symm
      rw [show (c : K ⧸ borel D H) = _ from congrArg Subtype.val h2]
      exact h1
    have hl : Lx.ε Ax * Ly.ε Ay * Lz.ε Az ∈ leviM D I :=
      mul_mem (mul_mem (hmbS3_eps_mem_leviM_of_mem_blockSL hx hIx Ax hAx)
        (hmbS3_eps_mem_leviM_of_mem_blockSL hy hIy Ay hAy))
        (hmbS3_eps_mem_leviM_of_mem_blockSL hz hIz Az hAz)
    have hc'' : (c : K ⧸ borel D H) =
        ((g * (Lx.ε Ax * Ly.ε Ay * Lz.ε Az) : K) : K ⧸ borel D H) := by
      rw [hcsymm]
      congr 1
      group
    have hκ : nrep hct v * F.φ (Lx.ε Ax * Ly.ε Ay * Lz.ε Az) * (nrep hct v)⁻¹ =
        Lx.ε (kapMat θ polx Px Ax) * Ly.ε (kapMat θ poly Py Ay) *
          Lz.ε (kapMat θ polz Pz Az) := by
      calc nrep hct v * F.φ (Lx.ε Ax * Ly.ε Ay * Lz.ε Az) * (nrep hct v)⁻¹
          = (nrep hct v * F.φ (Lx.ε Ax) * (nrep hct v)⁻¹) *
              (nrep hct v * F.φ (Ly.ε Ay) * (nrep hct v)⁻¹) *
              (nrep hct v * F.φ (Lz.ε Az) * (nrep hct v)⁻¹) := by
            rw [map_mul, map_mul]
            group
        _ = Lx.ε (kapMat θ polx Px Ax) * Ly.ε (kapMat θ poly Py Ay) *
              Lz.ε (kapMat θ polz Pz Az) := by
            rw [hκx' Ax hAx, hκy' Ay hAy, hκz' Az hAz]
    have hrearr : l₀ * (Lx.ε (kapMat θ polx Px Ax) * Ly.ε (kapMat θ poly Py Ay) *
        Lz.ε (kapMat θ polz Pz Az)) =
        Lx.ε (A₀x * kapMat θ polx Px Ax) * Ly.ε (A₀y * kapMat θ poly Py Ay) *
          Lz.ε (A₀z * kapMat θ polz Pz Az) := by
      have hba : Ly.ε A₀y * Lx.ε (kapMat θ polx Px Ax) =
          Lx.ε (kapMat θ polx Px Ax) * Ly.ε A₀y :=
        (hmbSP_commutes_rankOne hext hmxy (Lx.ε (kapMat θ polx Px Ax))
          (hmbS3_eps_mem_rankOne hx _) (Ly.ε A₀y) (hmbS3_eps_mem_rankOne hy _)).symm
      have hca : Lz.ε A₀z * Lx.ε (kapMat θ polx Px Ax) =
          Lx.ε (kapMat θ polx Px Ax) * Lz.ε A₀z :=
        (hmbSP_commutes_rankOne hext hmxz (Lx.ε (kapMat θ polx Px Ax))
          (hmbS3_eps_mem_rankOne hx _) (Lz.ε A₀z) (hmbS3_eps_mem_rankOne hz _)).symm
      have hcb : Lz.ε A₀z * Ly.ε (kapMat θ poly Py Ay) =
          Ly.ε (kapMat θ poly Py Ay) * Lz.ε A₀z :=
        (hmbSP_commutes_rankOne hext hmyz (Ly.ε (kapMat θ poly Py Ay))
          (hmbS3_eps_mem_rankOne hy _) (Lz.ε A₀z) (hmbS3_eps_mem_rankOne hz _)).symm
      rw [hl₀_eq, show Lx.ε A₀x * Ly.ε A₀y * Lz.ε A₀z *
          (Lx.ε (kapMat θ polx Px Ax) * Ly.ε (kapMat θ poly Py Ay) *
            Lz.ε (kapMat θ polz Pz Az)) =
          Lx.ε A₀x * Ly.ε A₀y * Lz.ε A₀z * Lx.ε (kapMat θ polx Px Ax) *
            Ly.ε (kapMat θ poly Py Ay) * Lz.ε (kapMat θ polz Pz Az) by group,
        hmbS3_rearrange_prod hba hca hcb]
      rw [show Lx.ε A₀x * Lx.ε (kapMat θ polx Px Ax) * Ly.ε A₀y *
            Ly.ε (kapMat θ poly Py Ay) * Lz.ε A₀z * Lz.ε (kapMat θ polz Pz Az) =
            (Lx.ε A₀x * Lx.ε (kapMat θ polx Px Ax)) *
              (Ly.ε A₀y * Ly.ε (kapMat θ poly Py Ay)) *
              (Lz.ε A₀z * Lz.ε (kapMat θ polz Pz Az)) by group,
        ← map_mul, ← map_mul, ← map_mul]
    have hc''' : (c' : K ⧸ borel D H) =
        ((g * t₀ * Lx.ε (A₀x * kapMat θ polx Px Ax) * Ly.ε (A₀y * kapMat θ poly Py Ay) *
          Lz.ε (A₀z * kapMat θ polz Pz Az) : K) : K ⧸ borel D H) := by
      rw [hc', hc'']
      rw [hψ (Lx.ε Ax * Ly.ε Ay * Lz.ε Az) hl]
      congr 1
      rw [hκ]
      rw [show g * t₀ * l₀ * (Lx.ε (kapMat θ polx Px Ax) * Ly.ε (kapMat θ poly Py Ay) *
            Lz.ε (kapMat θ polz Pz Az)) =
            g * t₀ * (l₀ * (Lx.ε (kapMat θ polx Px Ax) * Ly.ε (kapMat θ poly Py Ay) *
              Lz.ε (kapMat θ polz Pz Az))) by group, hrearr]
      group
    rw [hcoord (A₀x * kapMat θ polx Px Ax) (A₀y * kapMat θ poly Py Ay)
      (A₀z * kapMat θ polz Pz Az) c' hc''']
    refine Prod.ext (Prod.ext ?_ ?_) ?_
    · simp only [map_mul, flagAct_mul]
    · simp only [map_mul, flagAct_mul]
    · simp only [map_mul, flagAct_mul]

include hext hw₀ hsq in
theorem exists_seam_exch3 [CharP Fld 2] (Lx Ly Lz : SLPath M 1) {x y z : Fin D.rank}
    (hx : Lx.e 0 = x) (hy : Ly.e 0 = y) (hz : Lz.e 0 = z) (hxy : x ≠ y) (hxz : x ≠ z)
    (hyz : y ≠ z)
    (hmxy : coxeterMatrix D.isFiniteType x y = 2) (hmxz : coxeterMatrix D.isFiniteType x z = 2)
    (hmyz : coxeterMatrix D.isFiniteType y z = 2)
    {a : K ⧸ borel D H} {g : K} {v : W} {I : Set (Fin D.rank)} {t₀ l₀ : K}
    (hIJ : I ⊆ insert z (insert y {x}))
    (hR : residue (cs) (stdδ hct) (insert z (insert y {x})) a =
      residue (cs) (stdδ hct) (insert z (insert y {x})) ((g : K) : K ⧸ borel D H))
    (hcore : Gate.flipCore (cs) (stdδ hct) (stdFlip F (nrep hct w₀)) (insert z (insert y {x})) a =
      residue (cs) (stdδ hct) I ((g : K) : K ⧸ borel D H))
    (ht₀ : t₀ ∈ ⨆ k, H k) (hl₀ : l₀ ∈ leviM D I)
    (hψ : ∀ l ∈ leviM D I,
      Gate.flipPsi (cs) (stdδ hct) (stdFlip F (nrep hct w₀)) (insert z (insert y {x})) a
          ((g * l : K) : K ⧸ borel D H) =
        ((g * t₀ * l₀ * (nrep hct v * F.φ l * (nrep hct v)⁻¹) : K) : K ⧸ borel D H))
    (hIx : x ∈ I) (hIy : y ∈ I) {dz : List ℕ} (hdz : IsCut 2 dz)
    (hIz : z ∈ I ↔ (0 : Fin 1) ∈ cutTypes 1 dz) (θ : Fld →+* Fld)
    (Px Py Pz : SpecialLinearGroup (Fin 2) Fld) (polx poly polz : Bool)
    (hXu₁ : ∀ c : Fld, nrep hct v * F.φ (Lx.ε (tv Fld 0 1 c)) * (nrep hct v)⁻¹ =
      Ly.ε (kapMat θ polx Px (tv Fld 0 1 c)))
    (hXl₁ : ∀ c : Fld, nrep hct v * F.φ (Lx.ε (tv Fld 1 0 c)) * (nrep hct v)⁻¹ =
      Ly.ε (kapMat θ polx Px (tv Fld 1 0 c)))
    (hXu₂ : ∀ c : Fld, nrep hct v * F.φ (Ly.ε (tv Fld 0 1 c)) * (nrep hct v)⁻¹ =
      Lx.ε (kapMat θ poly Py (tv Fld 0 1 c)))
    (hXl₂ : ∀ c : Fld, nrep hct v * F.φ (Ly.ε (tv Fld 1 0 c)) * (nrep hct v)⁻¹ =
      Lx.ε (kapMat θ poly Py (tv Fld 1 0 c)))
    (hκz : NodeKap hct F Lz v dz θ Pz polz) :
    ∃ (Θ₀ : ChamberIso ((buildingOver (cs) (stdδ hct) (insert z (insert y {x}))).restrict
        (residue (cs) (stdδ hct) (insert z (insert y {x})) a))
          (((flagSys Fld 1).prod (flagSys Fld 1)).prod (flagSys Fld 1)))
      (Nx Ny Nz : GL (Fin 2) Fld),
      StabV2 dz Nz ∧
      (∀ c : ↥(residue (cs) (stdδ hct) (insert z (insert y {x})) a),
        (c : K ⧸ borel D H) ∈ Gate.flipCore (cs) (stdδ hct) (stdFlip F (nrep hct w₀))
            (insert z (insert y {x})) a ↔
          (Θ₀.Φ c).2 ∈ refSet Fld 2 dz) ∧
      ∀ Bx By Az : SpecialLinearGroup (Fin 2) Fld, Az ∈ blockSL Fld 1 dz →
        ∀ c c' : ↥(residue (cs) (stdδ hct) (insert z (insert y {x})) a),
        Θ₀.Φ c = ((flagAct (SpecialLinearGroup.toGL Bx) (stdFlag Fld 2),
          flagAct (SpecialLinearGroup.toGL By) (stdFlag Fld 2)),
            flagAct (SpecialLinearGroup.toGL Az) (stdFlag Fld 2)) →
        (c' : K ⧸ borel D H) = Gate.flipPsi (cs) (stdδ hct) (stdFlip F (nrep hct w₀))
          (insert z (insert y {x})) a (c : K ⧸ borel D H) →
        Θ₀.Φ c' =
          ((flagAct Nx (flagAct (SpecialLinearGroup.toGL (kapMat θ poly Py By)) (stdFlag Fld 2)),
            flagAct Ny (flagAct (SpecialLinearGroup.toGL (kapMat θ polx Px Bx)) (stdFlag Fld 2))),
              flagAct Nz (flagAct (SpecialLinearGroup.toGL (kapMat θ polz Pz Az))
                (stdFlag Fld 2))) := by
  classical
  have hcut : IsCut 2 [0, 2] := by
    refine ⟨rfl, rfl, ?_⟩
    intro i hi
    have hi' : i < 1 := by simpa using hi
    interval_cases i <;> simp
  have h0 : (0 : Fin 1) ∈ cutTypes 1 [0, 2] := by
    simp only [cutTypes, Set.mem_setOf_eq]
    intro i hi
    have hi' : i < 2 := by simpa using hi
    interval_cases i <;> simp
  have hIx' : x ∈ I ↔ (0 : Fin 1) ∈ cutTypes 1 [0, 2] := iff_of_true hIx h0
  have hIy' : y ∈ I ↔ (0 : Fin 1) ∈ cutTypes 1 [0, 2] := iff_of_true hIy h0
  have hκx : ∀ X : SpecialLinearGroup (Fin 2) Fld,
      nrep hct v * F.φ (Lx.ε X) * (nrep hct v)⁻¹ = Ly.ε (kapMat θ polx Px X) :=
    hmbSP_kappa_beta hct F Lx Ly (MonoidHom.id _) θ Px polx hXu₁ hXl₁
  have hκy : ∀ Y : SpecialLinearGroup (Fin 2) Fld,
      nrep hct v * F.φ (Ly.ε Y) * (nrep hct v)⁻¹ = Lx.ε (kapMat θ poly Py Y) :=
    hmbSP_kappa_beta hct F Ly Lx (MonoidHom.id _) θ Py poly hXu₂ hXl₂
  have hκz' : ∀ A ∈ blockSL Fld 1 dz,
      nrep hct v * F.φ (Lz.ε A) * (nrep hct v)⁻¹ = Lz.ε (kapMat θ polz Pz A) :=
    hmbSP_kappa_blockSL hct F Lz θ Pz polz (fun k hk c => (hκz k hk c).1)
      (fun k hk c => (hκz k hk c).2)
  obtain ⟨A₀x, -, A₀y, -, A₀z, hA₀z, hl₀_eq⟩ :=
    hmbS3_decomp3 (hext := hext) hx hy hz hmxy hmxz hmyz hIJ hIx' hIy' hIz hl₀
  obtain ⟨Dx, Dy, Dz, -, -, hDz, hcoord⟩ :=
    hmbS3_chart_coord hct hext Lx Ly Lz hx hy hz hxy hxz hyz hmxy hmxz hmyz hR ht₀
  have hrearr : ∀ X Y Z : SpecialLinearGroup (Fin 2) Fld,
      l₀ * (Lx.ε X * Ly.ε Y * Lz.ε Z) =
        Lx.ε (A₀x * X) * Ly.ε (A₀y * Y) * Lz.ε (A₀z * Z) := by
    intro X Y Z
    have hba : Ly.ε A₀y * Lx.ε X = Lx.ε X * Ly.ε A₀y :=
      (hmbSP_commutes_rankOne hext hmxy (Lx.ε X) (hmbS3_eps_mem_rankOne hx _)
        (Ly.ε A₀y) (hmbS3_eps_mem_rankOne hy _)).symm
    have hca : Lz.ε A₀z * Lx.ε X = Lx.ε X * Lz.ε A₀z :=
      (hmbSP_commutes_rankOne hext hmxz (Lx.ε X) (hmbS3_eps_mem_rankOne hx _)
        (Lz.ε A₀z) (hmbS3_eps_mem_rankOne hz _)).symm
    have hcb : Lz.ε A₀z * Ly.ε Y = Ly.ε Y * Lz.ε A₀z :=
      (hmbSP_commutes_rankOne hext hmyz (Ly.ε Y) (hmbS3_eps_mem_rankOne hy _)
        (Lz.ε A₀z) (hmbS3_eps_mem_rankOne hz _)).symm
    rw [hl₀_eq, show Lx.ε A₀x * Ly.ε A₀y * Lz.ε A₀z * (Lx.ε X * Ly.ε Y * Lz.ε Z) =
        Lx.ε A₀x * Ly.ε A₀y * Lz.ε A₀z * Lx.ε X * Ly.ε Y * Lz.ε Z by group,
      hmbS3_rearrange_prod hba hca hcb]
    rw [show Lx.ε A₀x * Lx.ε X * Ly.ε A₀y * Ly.ε Y * Lz.ε A₀z * Lz.ε Z =
        (Lx.ε A₀x * Lx.ε X) * (Ly.ε A₀y * Ly.ε Y) * (Lz.ε A₀z * Lz.ε Z) by group,
      ← map_mul, ← map_mul, ← map_mul]
  refine ⟨hmbS3_chart hct hext Lx Ly Lz hx hy hz hxy hxz hyz hmxy hmxz hmyz hR,
    Dx * SpecialLinearGroup.toGL A₀x, Dy * SpecialLinearGroup.toGL A₀y,
    Dz * SpecialLinearGroup.toGL A₀z, ?_, ?_, ?_⟩
  · exact StabV.mul (fun b _ => hmbSP_diag_stabV hDz (dz.getD b 0))
      (hmbSP_blockSL_stabV (m := 1) dz A₀z hA₀z)
  · intro c
    rw [hmbS3_core hct hext Lx Ly Lz hx hy hz hxy hxz hyz hmxy hmxz hmyz F hIJ hR hcore
      hcut hcut hdz hIx' hIy' hIz c, hmbSP_refSet_two]
    simp [Set.mem_prod]
  · intro Bx By Az hAz c c' hc hc'
    have hcsymm : (c : K ⧸ borel D H) =
        ((g * Lx.ε Bx * Ly.ε By * Lz.ε Az : K) : K ⧸ borel D H) := by
      have h1 := hmbS3_chart_symm_apply hct hext Lx Ly Lz hx hy hz hxy hxz hyz hmxy hmxz hmyz
        hR Bx By Az
      have h2 : c = (hmbS3_chart hct hext Lx Ly Lz hx hy hz hxy hxz hyz hmxy hmxz hmyz hR).Φ.symm
          ((flagAct (SpecialLinearGroup.toGL Bx) (stdFlag Fld 2),
            flagAct (SpecialLinearGroup.toGL By) (stdFlag Fld 2)),
            flagAct (SpecialLinearGroup.toGL Az) (stdFlag Fld 2)) := by
        rw [← hc]
        exact (Equiv.symm_apply_apply _ _).symm
      rw [show (c : K ⧸ borel D H) = _ from congrArg Subtype.val h2]
      exact h1
    have hl : Lx.ε Bx * Ly.ε By * Lz.ε Az ∈ leviM D I :=
      mul_mem (mul_mem (hmbS3_eps_mem_leviM hx hIx Bx) (hmbS3_eps_mem_leviM hy hIy By))
        (hmbS3_eps_mem_leviM_of_mem_blockSL hz hIz Az hAz)
    have hc'' : (c : K ⧸ borel D H) =
        ((g * (Lx.ε Bx * Ly.ε By * Lz.ε Az) : K) : K ⧸ borel D H) := by
      rw [hcsymm]
      congr 1
      group
    have hκ : nrep hct v * F.φ (Lx.ε Bx * Ly.ε By * Lz.ε Az) * (nrep hct v)⁻¹ =
        Ly.ε (kapMat θ polx Px Bx) * Lx.ε (kapMat θ poly Py By) *
          Lz.ε (kapMat θ polz Pz Az) := by
      calc nrep hct v * F.φ (Lx.ε Bx * Ly.ε By * Lz.ε Az) * (nrep hct v)⁻¹
          = (nrep hct v * F.φ (Lx.ε Bx) * (nrep hct v)⁻¹) *
              (nrep hct v * F.φ (Ly.ε By) * (nrep hct v)⁻¹) *
              (nrep hct v * F.φ (Lz.ε Az) * (nrep hct v)⁻¹) := by
            rw [map_mul, map_mul]
            group
        _ = Ly.ε (kapMat θ polx Px Bx) * Lx.ε (kapMat θ poly Py By) *
              Lz.ε (kapMat θ polz Pz Az) := by
            rw [hκx Bx, hκy By, hκz' Az hAz]
    have hswap : Ly.ε (kapMat θ polx Px Bx) * Lx.ε (kapMat θ poly Py By) =
        Lx.ε (kapMat θ poly Py By) * Ly.ε (kapMat θ polx Px Bx) :=
      (hmbSP_commutes_rankOne hext hmxy (Lx.ε (kapMat θ poly Py By))
        (hmbS3_eps_mem_rankOne hx _) (Ly.ε (kapMat θ polx Px Bx))
        (hmbS3_eps_mem_rankOne hy _)).symm
    have hc''' : (c' : K ⧸ borel D H) =
        ((g * t₀ * Lx.ε (A₀x * kapMat θ poly Py By) * Ly.ε (A₀y * kapMat θ polx Px Bx) *
          Lz.ε (A₀z * kapMat θ polz Pz Az) : K) : K ⧸ borel D H) := by
      rw [hc', hc'']
      rw [hψ (Lx.ε Bx * Ly.ε By * Lz.ε Az) hl]
      congr 1
      rw [hκ, hswap]
      rw [show g * t₀ * l₀ * (Lx.ε (kapMat θ poly Py By) * Ly.ε (kapMat θ polx Px Bx) *
            Lz.ε (kapMat θ polz Pz Az)) =
            g * t₀ * (l₀ * (Lx.ε (kapMat θ poly Py By) * Ly.ε (kapMat θ polx Px Bx) *
              Lz.ε (kapMat θ polz Pz Az))) by group,
        hrearr]
      group
    rw [hcoord (A₀x * kapMat θ poly Py By) (A₀y * kapMat θ polx Px Bx)
      (A₀z * kapMat θ polz Pz Az) c' hc''']
    refine Prod.ext (Prod.ext ?_ ?_) ?_
    · simp only [map_mul, flagAct_mul]
    · simp only [map_mul, flagAct_mul]
    · simp only [map_mul, flagAct_mul]

end CFSG.ClassicalInvolution.Phan.PhanE.Res

end
