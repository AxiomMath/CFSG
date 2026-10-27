module

public import CFSG.LocalAnalysis.StandardType.PhanEResSeamProdC

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

include hext hw₀ hsq in
theorem exists_seam_prod [CharP Fld 2] {m₁ : ℕ} (L₁ : SLPath M m₁) (L₂ : SLPath M 1)
    {J₁ : Set (Fin D.rank)} {z : Fin D.rank} (hJ₁ : Set.range L₁.e = J₁) (hz₂ : L₂.e 0 = z)
    (hz : z ∉ J₁)
    (hcomm : ∀ i ∈ J₁, coxeterMatrix D.isFiniteType i z = 2)
    {a : K ⧸ borel D H} {g : K} {v : W} {I : Set (Fin D.rank)} {t₀ l₀ : K}
    (hIJ : I ⊆ insert z J₁)
    (hR : residue (cs) (stdδ hct) (insert z J₁) a =
      residue (cs) (stdδ hct) (insert z J₁) ((g : K) : K ⧸ borel D H))
    (hcore : Gate.flipCore (cs) (stdδ hct) (stdFlip F (nrep hct w₀)) (insert z J₁) a =
      residue (cs) (stdδ hct) I ((g : K) : K ⧸ borel D H))
    (ht₀ : t₀ ∈ ⨆ k, H k) (hl₀ : l₀ ∈ leviM D I)
    (hψ : ∀ l ∈ leviM D I,
      Gate.flipPsi (cs) (stdδ hct) (stdFlip F (nrep hct w₀)) (insert z J₁) a
          ((g * l : K) : K ⧸ borel D H) =
        ((g * t₀ * l₀ * (nrep hct v * F.φ l * (nrep hct v)⁻¹) : K) : K ⧸ borel D H))
    {d₁ d₂ : List ℕ} (hd₁ : IsCut (m₁ + 1) d₁) (hd₂ : IsCut 2 d₂)
    (hI₁ : ∀ k, L₁.e k ∈ I ↔ k ∈ cutTypes m₁ d₁) (hI₂ : z ∈ I ↔ (0 : Fin 1) ∈ cutTypes 1 d₂)
    (θ : Fld →+* Fld) (P₁ : SpecialLinearGroup (Fin (m₁ + 1)) Fld)
    (P₂ : SpecialLinearGroup (Fin 2) Fld) (pol₁ pol₂ : Bool)
    (hPu₁ : ∀ k ∈ cutTypes m₁ d₁, ∀ c : Fld,
      nrep hct v * F.φ (L₁.ε (tv Fld k.castSucc k.succ c)) * (nrep hct v)⁻¹ =
        L₁.ε (kapMat θ pol₁ P₁ (tv Fld k.castSucc k.succ c)))
    (hPl₁ : ∀ k ∈ cutTypes m₁ d₁, ∀ c : Fld,
      nrep hct v * F.φ (L₁.ε (tv Fld k.succ k.castSucc c)) * (nrep hct v)⁻¹ =
        L₁.ε (kapMat θ pol₁ P₁ (tv Fld k.succ k.castSucc c)))
    (hPu₂ : ∀ k ∈ cutTypes 1 d₂, ∀ c : Fld,
      nrep hct v * F.φ (L₂.ε (tv Fld k.castSucc k.succ c)) * (nrep hct v)⁻¹ =
        L₂.ε (kapMat θ pol₂ P₂ (tv Fld k.castSucc k.succ c)))
    (hPl₂ : ∀ k ∈ cutTypes 1 d₂, ∀ c : Fld,
      nrep hct v * F.φ (L₂.ε (tv Fld k.succ k.castSucc c)) * (nrep hct v)⁻¹ =
        L₂.ε (kapMat θ pol₂ P₂ (tv Fld k.succ k.castSucc c))) :
    ∃ (Θ₀ : ChamberIso ((buildingOver (cs) (stdδ hct) (insert z J₁)).restrict
        (residue (cs) (stdδ hct) (insert z J₁) a)) ((flagSys Fld m₁).prod (flagSys Fld 1)))
      (N₁ : GL (Fin (m₁ + 1)) Fld) (N₂ : GL (Fin 2) Fld),
      (∀ b, b < d₁.length → (Vsub (m₁ + 1) (d₁.getD b 0)).map (glLin N₁).toLinearMap =
        Vsub (m₁ + 1) (d₁.getD b 0)) ∧
      (∀ b, b < d₂.length → (Vsub 2 (d₂.getD b 0)).map (glLin N₂).toLinearMap =
        Vsub 2 (d₂.getD b 0)) ∧
      (∀ c : ↥(residue (cs) (stdδ hct) (insert z J₁) a),
        (c : K ⧸ borel D H) ∈
            Gate.flipCore (cs) (stdδ hct) (stdFlip F (nrep hct w₀)) (insert z J₁) a ↔
          Θ₀.Φ c ∈ refSet Fld (m₁ + 1) d₁ ×ˢ refSet Fld 2 d₂) ∧
      ∀ A₁ ∈ blockSL Fld m₁ d₁, ∀ A₂ ∈ blockSL Fld 1 d₂,
        ∀ c c' : ↥(residue (cs) (stdδ hct) (insert z J₁) a),
        Θ₀.Φ c = (flagAct (SpecialLinearGroup.toGL A₁) (stdFlag Fld (m₁ + 1)),
          flagAct (SpecialLinearGroup.toGL A₂) (stdFlag Fld 2)) →
        (c' : K ⧸ borel D H) = Gate.flipPsi (cs) (stdδ hct) (stdFlip F (nrep hct w₀))
          (insert z J₁) a (c : K ⧸ borel D H) →
        Θ₀.Φ c' =
          (flagAct N₁ (flagAct (SpecialLinearGroup.toGL (kapMat θ pol₁ P₁ A₁))
              (stdFlag Fld (m₁ + 1))),
            flagAct N₂ (flagAct (SpecialLinearGroup.toGL (kapMat θ pol₂ P₂ A₂))
              (stdFlag Fld 2))) := by
  classical
  have hlevi : leviM D I =
      (blockSL Fld m₁ d₁).map L₁.ε ⊔ (blockSL Fld 1 d₂).map L₂.ε :=
    hmbSP_leviM_eq L₁ L₂ hJ₁ hz₂ hIJ hI₁ hI₂
  have hcommBlocks : ∀ a ∈ (blockSL Fld m₁ d₁).map L₁.ε,
      ∀ b ∈ (blockSL Fld 1 d₂).map L₂.ε, a * b = b * a := by
    intro a ha b hb
    obtain ⟨A₁, -, rfl⟩ := Subgroup.mem_map.mp ha
    obtain ⟨A₂, -, rfl⟩ := Subgroup.mem_map.mp hb
    exact hmbSP_commute hext L₁ L₂ hJ₁ hz₂ hz hcomm A₁ A₂
  obtain ⟨A₀₁, hA₀₁, A₀₂, hA₀₂, hl₀eq⟩ := hmbSP_decomp L₁ L₂ hlevi hcommBlocks hl₀
  have hcap₁ := hmbSP_kappa_blockSL hct F L₁ θ P₁ pol₁ hPu₁ hPl₁
  have hcap₂ := hmbSP_kappa_blockSL hct F L₂ θ P₂ pol₂ hPu₂ hPl₂
  obtain ⟨Dt₁, Dt₂, hdiag₁, hdiag₂, hcoord⟩ :=
    hmbSP_coord_prod hct hext L₁ L₂ hJ₁ hz₂ hz hcomm hR ht₀
  have hg_mem : ((g : K) : K ⧸ borel D H) ∈
      residue (cs) (stdδ hct) (insert z J₁) a :=
    hR.symm ▸ self_mem_residue (insert z J₁) ((g : K) : K ⧸ borel D H)
  let x : ↥(residue (cs) (stdδ hct) (insert z J₁) a) :=
    ⟨((g : K) : K ⧸ borel D H), hg_mem⟩
  have hsymm : (hmbSP_chart hct hext L₁ L₂ hJ₁ hz₂ hz hcomm hR).Φ.symm
      (stdFlag Fld (m₁ + 1), stdFlag Fld 2) = x := by
    apply Subtype.ext
    have h := hmbSP_chart_symm_apply hct hext L₁ L₂ hJ₁ hz₂ hz hcomm hR
      (1 : SpecialLinearGroup (Fin (m₁ + 1)) Fld) (1 : SpecialLinearGroup (Fin 2) Fld)
    simpa [map_one, flagAct_one] using h
  have hxΦ : (hmbSP_chart hct hext L₁ L₂ hJ₁ hz₂ hz hcomm hR).Φ x =
      (stdFlag Fld (m₁ + 1), stdFlag Fld 2) := by
    rw [← hsymm]
    exact Equiv.apply_symm_apply _ _
  refine ⟨hmbSP_chart hct hext L₁ L₂ hJ₁ hz₂ hz hcomm hR,
    Dt₁ * SpecialLinearGroup.toGL A₀₁, Dt₂ * SpecialLinearGroup.toGL A₀₂,
    ?_, ?_, ?_, ?_⟩
  · intro b hb
    exact hmbSP_stabV_mul (hmbSP_diag_stabV hdiag₁ (d₁.getD b 0))
      (hmbSP_blockSL_stabV d₁ A₀₁ hA₀₁ b hb)
  · intro b hb
    exact hmbSP_stabV_mul (hmbSP_diag_stabV hdiag₂ (d₂.getD b 0))
      (hmbSP_blockSL_stabV d₂ A₀₂ hA₀₂ b hb)
  · intro c
    have htype : (hmbSP_chart hct hext L₁ L₂ hJ₁ hz₂ hz hcomm hR).e ''
        {j : ↥(insert z J₁) | (j : Fin D.rank) ∈ I} =
        Sum.inl '' cutTypes m₁ d₁ ∪ Sum.inr '' cutTypes 1 d₂ := by
      ext t
      constructor
      · rintro ⟨j, hj, rfl⟩
        rcases Set.mem_insert_iff.mp j.2 with hjz | hjJ
        · have hje : j = ⟨z, Set.mem_insert z J₁⟩ := Subtype.ext hjz
          rw [hje, hmbSP_chart_e_inr hct hext L₁ L₂ hJ₁ hz₂ hz hcomm hR]
          exact Or.inr ⟨0, (hI₂).mp (hjz ▸ hj), rfl⟩
        · obtain ⟨k, hk⟩ := show (j : Fin D.rank) ∈ Set.range L₁.e by
            rw [hJ₁]; exact hjJ
          have hk' : L₁.e k ∈ J₁ := hk.symm ▸ hjJ
          have hj' : j = ⟨L₁.e k, Set.mem_insert_of_mem z hk'⟩ := Subtype.ext hk.symm
          rw [hj', hmbSP_chart_e_inl hct hext L₁ L₂ hJ₁ hz₂ hz hcomm hR k hk']
          exact Or.inl ⟨k, (hI₁ k).mp (hk.symm ▸ hj), rfl⟩
      · rintro (⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩)
        · have hk' : L₁.e k ∈ J₁ := hJ₁ ▸ Set.mem_range_self k
          exact ⟨⟨L₁.e k, Set.mem_insert_of_mem z hk'⟩, (hI₁ k).mpr hk,
            hmbSP_chart_e_inl hct hext L₁ L₂ hJ₁ hz₂ hz hcomm hR k hk'⟩
        · fin_cases k
          exact ⟨⟨z, Set.mem_insert z J₁⟩, (hI₂).mpr hk,
            hmbSP_chart_e_inr hct hext L₁ L₂ hJ₁ hz₂ hz hcomm hR⟩
    have hresid : (((flagSys Fld m₁).prod (flagSys Fld 1)).residue
        (Sum.inl '' cutTypes m₁ d₁ ∪ Sum.inr '' cutTypes 1 d₂)
        (stdFlag Fld (m₁ + 1), stdFlag Fld 2)) =
        refSet Fld (m₁ + 1) d₁ ×ˢ refSet Fld 2 d₂ := by
      rw [hmbSP_prod_residue (flagSys Fld m₁) (flagSys Fld 1) (cutTypes m₁ d₁)
        (cutTypes 1 d₂) (stdFlag Fld (m₁ + 1)) (stdFlag Fld 2)]
      congr 1
      · rw [← residue_flagδ_eq (K := Fld) (cutTypes m₁ d₁) (stdFlag Fld (m₁ + 1)),
          residue_cutTypes_eq hd₁ (stdFlag_mem_refSet (K := Fld) hd₁)]
      · rw [← residue_flagδ_eq (K := Fld) (cutTypes 1 d₂) (stdFlag Fld 2),
          residue_cutTypes_eq hd₂ (stdFlag_mem_refSet (K := Fld) hd₂)]
    have hmem := mem_residue_iff_of_chamberIso (stdBuilding hct hext)
      (hmbSP_chart hct hext L₁ L₂ hJ₁ hz₂ hz hcomm hR) hIJ x c
    rw [htype, hxΦ, hresid] at hmem
    rw [hcore]
    exact hmem
  · intro A₁ hA₁ A₂ hA₂ c c' hc hc'
    have hAlevi : L₁.ε A₁ * L₂.ε A₂ ∈ leviM D I := by
      rw [hlevi]
      exact Subgroup.mul_mem
        (H := (blockSL Fld m₁ d₁).map L₁.ε ⊔ (blockSL Fld 1 d₂).map L₂.ε)
        (Subgroup.mem_sup_left (Subgroup.mem_map_of_mem L₁.ε hA₁))
        (Subgroup.mem_sup_right (Subgroup.mem_map_of_mem L₂.ε hA₂))
    have hcl : (c : K ⧸ borel D H) =
        ((g * (L₁.ε A₁ * L₂.ε A₂) : K) : K ⧸ borel D H) := by
      have h1 : (hmbSP_chart hct hext L₁ L₂ hJ₁ hz₂ hz hcomm hR).Φ.symm
          (flagAct (SpecialLinearGroup.toGL A₁) (stdFlag Fld (m₁ + 1)),
           flagAct (SpecialLinearGroup.toGL A₂) (stdFlag Fld 2)) = c :=
        (Equiv.symm_apply_eq _).mpr hc.symm
      calc (c : K ⧸ borel D H)
          = (((hmbSP_chart hct hext L₁ L₂ hJ₁ hz₂ hz hcomm hR).Φ.symm
              (flagAct (SpecialLinearGroup.toGL A₁) (stdFlag Fld (m₁ + 1)),
               flagAct (SpecialLinearGroup.toGL A₂) (stdFlag Fld 2)) :
              ↥(residue (cs) (stdδ hct) (insert z J₁) a)) : K ⧸ borel D H) := by
              rw [h1]
        _ = ((g * L₁.ε A₁ * L₂.ε A₂ : K) : K ⧸ borel D H) :=
              hmbSP_chart_symm_apply hct hext L₁ L₂ hJ₁ hz₂ hz hcomm hR A₁ A₂
        _ = ((g * (L₁.ε A₁ * L₂.ε A₂) : K) : K ⧸ borel D H) := by rw [mul_assoc]
    have hκ : nrep hct v * F.φ (L₁.ε A₁ * L₂.ε A₂) * (nrep hct v)⁻¹ =
        L₁.ε (kapMat θ pol₁ P₁ A₁) * L₂.ε (kapMat θ pol₂ P₂ A₂) := by
      rw [map_mul]
      calc nrep hct v * (F.φ (L₁.ε A₁) * F.φ (L₂.ε A₂)) * (nrep hct v)⁻¹
          = (nrep hct v * F.φ (L₁.ε A₁) * (nrep hct v)⁻¹) *
            (nrep hct v * F.φ (L₂.ε A₂) * (nrep hct v)⁻¹) := by group
        _ = L₁.ε (kapMat θ pol₁ P₁ A₁) * L₂.ε (kapMat θ pol₂ P₂ A₂) := by
              rw [hcap₁ A₁ hA₁, hcap₂ A₂ hA₂]
    have hψl := hψ (L₁.ε A₁ * L₂.ε A₂) hAlevi
    have hmain : (c' : K ⧸ borel D H) =
        ((g * t₀ * L₁.ε (A₀₁ * kapMat θ pol₁ P₁ A₁) *
          L₂.ε (A₀₂ * kapMat θ pol₂ P₂ A₂) : K) : K ⧸ borel D H) := by
      have hK : g * t₀ * l₀ *
            (nrep hct v * F.φ (L₁.ε A₁ * L₂.ε A₂) * (nrep hct v)⁻¹) =
          g * t₀ * L₁.ε (A₀₁ * kapMat θ pol₁ P₁ A₁) *
            L₂.ε (A₀₂ * kapMat θ pol₂ P₂ A₂) := by
        rw [hκ, hl₀eq]
        calc g * t₀ * (L₁.ε A₀₁ * L₂.ε A₀₂) *
              (L₁.ε (kapMat θ pol₁ P₁ A₁) * L₂.ε (kapMat θ pol₂ P₂ A₂))
            = g * t₀ * (L₁.ε A₀₁ *
                (L₂.ε A₀₂ * L₁.ε (kapMat θ pol₁ P₁ A₁)) *
                L₂.ε (kapMat θ pol₂ P₂ A₂)) := by group
          _ = g * t₀ * (L₁.ε A₀₁ *
                (L₁.ε (kapMat θ pol₁ P₁ A₁) * L₂.ε A₀₂) *
                L₂.ε (kapMat θ pol₂ P₂ A₂)) := by
                rw [← hmbSP_commute hext L₁ L₂ hJ₁ hz₂ hz hcomm
                  (kapMat θ pol₁ P₁ A₁) A₀₂]
          _ = g * t₀ * (L₁.ε A₀₁ * L₁.ε (kapMat θ pol₁ P₁ A₁)) *
                (L₂.ε A₀₂ * L₂.ε (kapMat θ pol₂ P₂ A₂)) := by group
          _ = g * t₀ * L₁.ε (A₀₁ * kapMat θ pol₁ P₁ A₁) *
                L₂.ε (A₀₂ * kapMat θ pol₂ P₂ A₂) := by
                rw [map_mul, map_mul]
      calc (c' : K ⧸ borel D H)
          = Gate.flipPsi (cs) (stdδ hct) (stdFlip F (nrep hct w₀)) (insert z J₁) a
              (c : K ⧸ borel D H) := hc'
        _ = ((g * t₀ * l₀ * (nrep hct v * F.φ (L₁.ε A₁ * L₂.ε A₂) *
              (nrep hct v)⁻¹) : K) : K ⧸ borel D H) := by
              rw [hcl]; exact hψl
        _ = ((g * t₀ * L₁.ε (A₀₁ * kapMat θ pol₁ P₁ A₁) *
              L₂.ε (A₀₂ * kapMat θ pol₂ P₂ A₂) : K) : K ⧸ borel D H) := by rw [hK]
    have hcoord' := hcoord (A₀₁ * kapMat θ pol₁ P₁ A₁)
      (A₀₂ * kapMat θ pol₂ P₂ A₂) c' hmain
    calc (hmbSP_chart hct hext L₁ L₂ hJ₁ hz₂ hz hcomm hR).Φ c'
        = (flagAct Dt₁
              (flagAct (SpecialLinearGroup.toGL (A₀₁ * kapMat θ pol₁ P₁ A₁))
                (stdFlag Fld (m₁ + 1))),
           flagAct Dt₂
              (flagAct (SpecialLinearGroup.toGL (A₀₂ * kapMat θ pol₂ P₂ A₂))
                (stdFlag Fld 2))) := hcoord'
      _ = (flagAct (Dt₁ * SpecialLinearGroup.toGL A₀₁)
              (flagAct (SpecialLinearGroup.toGL (kapMat θ pol₁ P₁ A₁))
                (stdFlag Fld (m₁ + 1))),
           flagAct (Dt₂ * SpecialLinearGroup.toGL A₀₂)
              (flagAct (SpecialLinearGroup.toGL (kapMat θ pol₂ P₂ A₂))
                (stdFlag Fld 2))) := by
            simp only [map_mul, flagAct_mul]

end CFSG.ClassicalInvolution.Phan.PhanE.Res

end
