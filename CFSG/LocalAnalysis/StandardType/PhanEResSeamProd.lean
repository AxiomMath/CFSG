module

public import CFSG.LocalAnalysis.StandardType.PhanEResSeamProdP

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
theorem exists_seam_exch [CharP Fld 2] {m₁ : ℕ} (L₁ : SLPath M m₁) (L₂ : SLPath M 1)
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
    {d₁ : List ℕ} (hd₁ : IsCut (m₁ + 1) d₁) {k₁ : Fin m₁} (hk₁ : cutTypes m₁ d₁ = {k₁})
    (hI₁ : ∀ k, L₁.e k ∈ I ↔ k ∈ cutTypes m₁ d₁) (hI₂ : z ∈ I)
    (β : SpecialLinearGroup (Fin 2) Fld →* SpecialLinearGroup (Fin (m₁ + 1)) Fld)
    (hβu : ∀ c : Fld, β (tv Fld 0 1 c) = tv Fld k₁.castSucc k₁.succ c)
    (hβl : ∀ c : Fld, β (tv Fld 1 0 c) = tv Fld k₁.succ k₁.castSucc c)
    (θ : Fld →+* Fld) (P₁ P₂ : SpecialLinearGroup (Fin 2) Fld) (pol₁ pol₂ : Bool)
    (hXu₁ : ∀ c : Fld, nrep hct v * F.φ (L₁.ε (β (tv Fld 0 1 c))) * (nrep hct v)⁻¹ =
      L₂.ε (kapMat θ pol₁ P₁ (tv Fld 0 1 c)))
    (hXl₁ : ∀ c : Fld, nrep hct v * F.φ (L₁.ε (β (tv Fld 1 0 c))) * (nrep hct v)⁻¹ =
      L₂.ε (kapMat θ pol₁ P₁ (tv Fld 1 0 c)))
    (hXu₂ : ∀ c : Fld, nrep hct v * F.φ (L₂.ε (tv Fld 0 1 c)) * (nrep hct v)⁻¹ =
      L₁.ε (β (kapMat θ pol₂ P₂ (tv Fld 0 1 c))))
    (hXl₂ : ∀ c : Fld, nrep hct v * F.φ (L₂.ε (tv Fld 1 0 c)) * (nrep hct v)⁻¹ =
      L₁.ε (β (kapMat θ pol₂ P₂ (tv Fld 1 0 c)))) :
    ∃ (Θ₀ : ChamberIso ((buildingOver (cs) (stdδ hct) (insert z J₁)).restrict
        (residue (cs) (stdδ hct) (insert z J₁) a)) ((flagSys Fld m₁).prod (flagSys Fld 1)))
      (N₁ : GL (Fin (m₁ + 1)) Fld) (N₂ : GL (Fin 2) Fld),
      (∀ b, b < d₁.length → (Vsub (m₁ + 1) (d₁.getD b 0)).map (glLin N₁).toLinearMap =
        Vsub (m₁ + 1) (d₁.getD b 0)) ∧
      (∀ c : ↥(residue (cs) (stdδ hct) (insert z J₁) a),
        (c : K ⧸ borel D H) ∈
            Gate.flipCore (cs) (stdδ hct) (stdFlip F (nrep hct w₀)) (insert z J₁) a ↔
          (Θ₀.Φ c).1 ∈ refSet Fld (m₁ + 1) d₁) ∧
      ∀ B₁ B₂ : SpecialLinearGroup (Fin 2) Fld,
        ∀ c c' : ↥(residue (cs) (stdδ hct) (insert z J₁) a),
        Θ₀.Φ c = (flagAct (SpecialLinearGroup.toGL (β B₁)) (stdFlag Fld (m₁ + 1)),
          flagAct (SpecialLinearGroup.toGL B₂) (stdFlag Fld 2)) →
        (c' : K ⧸ borel D H) = Gate.flipPsi (cs) (stdδ hct) (stdFlip F (nrep hct w₀))
          (insert z J₁) a (c : K ⧸ borel D H) →
        Θ₀.Φ c' =
          (flagAct N₁ (flagAct (SpecialLinearGroup.toGL (β (kapMat θ pol₂ P₂ B₂)))
              (stdFlag Fld (m₁ + 1))),
            flagAct N₂ (flagAct (SpecialLinearGroup.toGL (kapMat θ pol₁ P₁ B₁))
              (stdFlag Fld 2))) := by
  classical
  have hmem0 : (0 : Fin 1) ∈ cutTypes 1 [0,2] := by
    simp only [cutTypes, Set.mem_setOf_eq]
    intro i hi
    have hi' : i < 2 := by simpa using hi
    interval_cases i <;> simp
  have hI₂' : z ∈ I ↔ (0 : Fin 1) ∈ cutTypes 1 [0,2] :=
    ⟨fun _ => hmem0, fun _ => hI₂⟩
  have hd₂ : IsCut 2 [0,2] := by
    refine ⟨rfl, rfl, ?_⟩
    intro i hi
    have hi' : i < 1 := by simpa using hi
    interval_cases i <;> simp
  have hlevi : leviM D I =
      (blockSL Fld m₁ d₁).map L₁.ε ⊔ (blockSL Fld 1 [0,2]).map L₂.ε :=
    hmbSP_leviM_eq L₁ L₂ hJ₁ hz₂ hIJ hI₁ hI₂'
  have hcommBlocks : ∀ a ∈ (blockSL Fld m₁ d₁).map L₁.ε,
      ∀ b ∈ (blockSL Fld 1 [0,2]).map L₂.ε, a * b = b * a := by
    intro a ha b hb
    obtain ⟨A₁, -, rfl⟩ := Subgroup.mem_map.mp ha
    obtain ⟨A₂, -, rfl⟩ := Subgroup.mem_map.mp hb
    exact hmbSP_commute hext L₁ L₂ hJ₁ hz₂ hz hcomm A₁ A₂
  obtain ⟨A₀₁, hA₀₁, A₀₂, hA₀₂, hl₀eq⟩ := hmbSP_decomp L₁ L₂ hlevi hcommBlocks hl₀
  obtain ⟨X, -, hX⟩ := Subgroup.mem_map.mp (hmbSP_blockSL_le_map_beta hk₁ β hβu hβl hA₀₁)
  have hβX : β X ∈ blockSL Fld m₁ d₁ := by rw [hX]; exact hA₀₁
  have hcap₁ := hmbSP_kappa_beta hct F L₁ L₂ β θ P₁ pol₁ hXu₁ hXl₁
  have hcap₂ := hmbSP_kappa_snd hct F L₁ L₂ β θ P₂ pol₂ hXu₂ hXl₂
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
    Dt₁ * SpecialLinearGroup.toGL (β X), Dt₂ * SpecialLinearGroup.toGL A₀₂,
    ?_, ?_, ?_⟩
  · intro b hb
    exact hmbSP_stabV_mul (hmbSP_diag_stabV hdiag₁ (d₁.getD b 0))
      (hmbSP_blockSL_stabV d₁ (β X) hβX b hb)
  · intro c
    have htype : (hmbSP_chart hct hext L₁ L₂ hJ₁ hz₂ hz hcomm hR).e ''
        {j : ↥(insert z J₁) | (j : Fin D.rank) ∈ I} =
        Sum.inl '' cutTypes m₁ d₁ ∪ Sum.inr '' cutTypes 1 [0,2] := by
      ext t
      constructor
      · rintro ⟨j, hj, rfl⟩
        rcases Set.mem_insert_iff.mp j.2 with hjz | hjJ
        · have hje : j = ⟨z, Set.mem_insert z J₁⟩ := Subtype.ext hjz
          rw [hje, hmbSP_chart_e_inr hct hext L₁ L₂ hJ₁ hz₂ hz hcomm hR]
          exact Or.inr ⟨0, (hI₂').mp (hjz ▸ hj), rfl⟩
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
          exact ⟨⟨z, Set.mem_insert z J₁⟩, (hI₂').mpr hk,
            hmbSP_chart_e_inr hct hext L₁ L₂ hJ₁ hz₂ hz hcomm hR⟩
    have hresid : (((flagSys Fld m₁).prod (flagSys Fld 1)).residue
        (Sum.inl '' cutTypes m₁ d₁ ∪ Sum.inr '' cutTypes 1 [0,2])
        (stdFlag Fld (m₁ + 1), stdFlag Fld 2)) =
        refSet Fld (m₁ + 1) d₁ ×ˢ (Set.univ : Set (FlagK Fld 2)) := by
      rw [hmbSP_prod_residue (flagSys Fld m₁) (flagSys Fld 1) (cutTypes m₁ d₁)
        (cutTypes 1 [0,2]) (stdFlag Fld (m₁ + 1)) (stdFlag Fld 2)]
      congr 1
      · rw [← residue_flagδ_eq (K := Fld) (cutTypes m₁ d₁) (stdFlag Fld (m₁ + 1)),
          residue_cutTypes_eq hd₁ (stdFlag_mem_refSet (K := Fld) hd₁)]
      · rw [← residue_flagδ_eq (K := Fld) (cutTypes 1 [0,2]) (stdFlag Fld 2),
          residue_cutTypes_eq hd₂ (stdFlag_mem_refSet (K := Fld) hd₂), hmbSP_refSet_two]
    have hmem := mem_residue_iff_of_chamberIso (stdBuilding hct hext)
      (hmbSP_chart hct hext L₁ L₂ hJ₁ hz₂ hz hcomm hR) hIJ x c
    rw [htype, hxΦ, hresid] at hmem
    rw [hcore, hmem]
    simp only [Set.mem_prod, Set.mem_univ, and_true]
  · intro B₁ B₂ c c' hc hc'
    have hβB₁ : β B₁ ∈ blockSL Fld m₁ d₁ := hmbSP_beta_mem_blockSL hk₁ β hβu hβl B₁
    have hlevi₁ : L₁.ε (β B₁) ∈ leviM D I := by
      rw [hlevi]
      exact Subgroup.mem_sup_left (Subgroup.mem_map_of_mem L₁.ε hβB₁)
    have hlevi₂ : L₂.ε B₂ ∈ leviM D I := by
      have h := hmbSP_range_eps_le_leviM L₂ (Set.mem_range_self B₂)
      rw [hmbSP_range_e_one hz₂] at h
      have hle : leviM D ({z} : Set (Fin D.rank)) ≤ leviM D I := by
        rw [leviM]
        refine iSup₂_le fun i hi => ?_
        rw [Set.mem_singleton_iff] at hi
        subst hi
        exact rankOne_le_leviM hI₂
      exact hle h
    have hAlevi : L₁.ε (β B₁) * L₂.ε B₂ ∈ leviM D I :=
      (leviM D I).mul_mem hlevi₁ hlevi₂
    have hcl : (c : K ⧸ borel D H) =
        ((g * (L₁.ε (β B₁) * L₂.ε B₂) : K) : K ⧸ borel D H) := by
      have h1 : (hmbSP_chart hct hext L₁ L₂ hJ₁ hz₂ hz hcomm hR).Φ.symm
          (flagAct (SpecialLinearGroup.toGL (β B₁)) (stdFlag Fld (m₁ + 1)),
           flagAct (SpecialLinearGroup.toGL B₂) (stdFlag Fld 2)) = c :=
        (Equiv.symm_apply_eq _).mpr hc.symm
      calc (c : K ⧸ borel D H)
          = (((hmbSP_chart hct hext L₁ L₂ hJ₁ hz₂ hz hcomm hR).Φ.symm
              (flagAct (SpecialLinearGroup.toGL (β B₁)) (stdFlag Fld (m₁ + 1)),
               flagAct (SpecialLinearGroup.toGL B₂) (stdFlag Fld 2)) :
              ↥(residue (cs) (stdδ hct) (insert z J₁) a)) : K ⧸ borel D H) := by
              rw [h1]
        _ = ((g * L₁.ε (β B₁) * L₂.ε B₂ : K) : K ⧸ borel D H) :=
              hmbSP_chart_symm_apply hct hext L₁ L₂ hJ₁ hz₂ hz hcomm hR (β B₁) B₂
        _ = ((g * (L₁.ε (β B₁) * L₂.ε B₂) : K) : K ⧸ borel D H) := by rw [mul_assoc]
    have hκ : nrep hct v * F.φ (L₁.ε (β B₁) * L₂.ε B₂) * (nrep hct v)⁻¹ =
        L₂.ε (kapMat θ pol₁ P₁ B₁) * L₁.ε (β (kapMat θ pol₂ P₂ B₂)) := by
      rw [map_mul]
      calc nrep hct v * (F.φ (L₁.ε (β B₁)) * F.φ (L₂.ε B₂)) * (nrep hct v)⁻¹
          = (nrep hct v * F.φ (L₁.ε (β B₁)) * (nrep hct v)⁻¹) *
            (nrep hct v * F.φ (L₂.ε B₂) * (nrep hct v)⁻¹) := by group
        _ = L₂.ε (kapMat θ pol₁ P₁ B₁) * L₁.ε (β (kapMat θ pol₂ P₂ B₂)) := by
              rw [hcap₁ B₁, hcap₂ B₂]
    have hψl := hψ (L₁.ε (β B₁) * L₂.ε B₂) hAlevi
    have hmain : (c' : K ⧸ borel D H) =
        ((g * t₀ * L₁.ε (β (X * kapMat θ pol₂ P₂ B₂)) *
          L₂.ε (A₀₂ * kapMat θ pol₁ P₁ B₁) : K) : K ⧸ borel D H) := by
      have hK : g * t₀ * l₀ *
            (nrep hct v * F.φ (L₁.ε (β B₁) * L₂.ε B₂) * (nrep hct v)⁻¹) =
          g * t₀ * L₁.ε (β (X * kapMat θ pol₂ P₂ B₂)) *
            L₂.ε (A₀₂ * kapMat θ pol₁ P₁ B₁) := by
        rw [hκ, hl₀eq, ← hX]
        simp only [map_mul]
        have hcomm' : L₂.ε A₀₂ * L₂.ε (kapMat θ pol₁ P₁ B₁) *
              L₁.ε (β (kapMat θ pol₂ P₂ B₂)) =
            L₁.ε (β (kapMat θ pol₂ P₂ B₂)) *
              (L₂.ε A₀₂ * L₂.ε (kapMat θ pol₁ P₁ B₁)) := by
          rw [← map_mul, ← hmbSP_commute hext L₁ L₂ hJ₁ hz₂ hz hcomm
            (β (kapMat θ pol₂ P₂ B₂)) (A₀₂ * kapMat θ pol₁ P₁ B₁), map_mul]
        rw [show g * t₀ * (L₁.ε (β X) * L₂.ε A₀₂) *
              (L₂.ε (kapMat θ pol₁ P₁ B₁) * L₁.ε (β (kapMat θ pol₂ P₂ B₂)))
            = g * t₀ * (L₁.ε (β X) *
              (L₂.ε A₀₂ * L₂.ε (kapMat θ pol₁ P₁ B₁) *
              L₁.ε (β (kapMat θ pol₂ P₂ B₂)))) by group]
        rw [hcomm']
        group
      calc (c' : K ⧸ borel D H)
          = Gate.flipPsi (cs) (stdδ hct) (stdFlip F (nrep hct w₀)) (insert z J₁) a
              (c : K ⧸ borel D H) := hc'
        _ = ((g * t₀ * l₀ * (nrep hct v * F.φ (L₁.ε (β B₁) * L₂.ε B₂) *
              (nrep hct v)⁻¹) : K) : K ⧸ borel D H) := by
              rw [hcl]; exact hψl
        _ = ((g * t₀ * L₁.ε (β (X * kapMat θ pol₂ P₂ B₂)) *
              L₂.ε (A₀₂ * kapMat θ pol₁ P₁ B₁) : K) : K ⧸ borel D H) := by rw [hK]
    have hcoord' := hcoord (β (X * kapMat θ pol₂ P₂ B₂))
      (A₀₂ * kapMat θ pol₁ P₁ B₁) c' hmain
    calc (hmbSP_chart hct hext L₁ L₂ hJ₁ hz₂ hz hcomm hR).Φ c'
        = (flagAct Dt₁
              (flagAct (SpecialLinearGroup.toGL (β (X * kapMat θ pol₂ P₂ B₂)))
                (stdFlag Fld (m₁ + 1))),
           flagAct Dt₂
              (flagAct (SpecialLinearGroup.toGL (A₀₂ * kapMat θ pol₁ P₁ B₁))
                (stdFlag Fld 2))) := hcoord'
      _ = (flagAct (Dt₁ * SpecialLinearGroup.toGL (β X))
              (flagAct (SpecialLinearGroup.toGL (β (kapMat θ pol₂ P₂ B₂)))
                (stdFlag Fld (m₁ + 1))),
           flagAct (Dt₂ * SpecialLinearGroup.toGL A₀₂)
              (flagAct (SpecialLinearGroup.toGL (kapMat θ pol₁ P₁ B₁))
                (stdFlag Fld 2))) := by
            simp only [map_mul, flagAct_mul]

end CFSG.ClassicalInvolution.Phan.PhanE.Res

end
