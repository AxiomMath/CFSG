module

public import CFSG.LocalAnalysis.StandardType.PhanEResSeamProdB
import CFSG.ClassicalGroups.SpecialLinear.CyclicRootGroups

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

section Decomp

variable {m₁ : ℕ}

private theorem hmbSP_I_eq (L₁ : SLPath M m₁) (L₂ : SLPath M 1)
    {J₁ : Set (Fin D.rank)} {z : Fin D.rank} (hJ₁ : Set.range L₁.e = J₁) (hz₂ : L₂.e 0 = z)
    {I : Set (Fin D.rank)} (hIJ : I ⊆ insert z J₁)
    {d₁ d₂ : List ℕ} (hI₁ : ∀ k, L₁.e k ∈ I ↔ k ∈ cutTypes m₁ d₁)
    (hI₂ : z ∈ I ↔ (0 : Fin 1) ∈ cutTypes 1 d₂) :
    I = L₁.e '' cutTypes m₁ d₁ ∪ L₂.e '' cutTypes 1 d₂ := by
  ext x
  constructor
  · intro hx
    rcases Set.mem_insert_iff.mp (hIJ hx) with hxz | hxJ₁
    · rw [hxz] at hx ⊢
      exact Or.inr ⟨0, (hI₂).mp hx, hz₂⟩
    · obtain ⟨k, rfl⟩ := hJ₁ ▸ hxJ₁
      exact Or.inl ⟨k, (hI₁ k).mp hx, rfl⟩
  · rintro (⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩)
    · exact (hI₁ k).mpr hk
    · fin_cases k
      simpa [hz₂] using (hI₂).mpr hk

theorem hmbSP_leviM_eq (L₁ : SLPath M m₁) (L₂ : SLPath M 1)
    {J₁ : Set (Fin D.rank)} {z : Fin D.rank} (hJ₁ : Set.range L₁.e = J₁) (hz₂ : L₂.e 0 = z)
    {I : Set (Fin D.rank)} (hIJ : I ⊆ insert z J₁)
    {d₁ d₂ : List ℕ} (hI₁ : ∀ k, L₁.e k ∈ I ↔ k ∈ cutTypes m₁ d₁)
    (hI₂ : z ∈ I ↔ (0 : Fin 1) ∈ cutTypes 1 d₂) :
    leviM D I = (blockSL Fld m₁ d₁).map L₁.ε ⊔ (blockSL Fld 1 d₂).map L₂.ε := by
  rw [hmbSP_I_eq L₁ L₂ hJ₁ hz₂ hIJ hI₁ hI₂]
  simp only [leviM, iSup_union, map_blockSL]

private theorem hmbSP_mem_sup_of_commute {A B : Subgroup K}
    (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {x : K} (hx : x ∈ A ⊔ B) :
    ∃ a ∈ A, ∃ b ∈ B, a * b = x := by
  rw [Subgroup.sup_eq_closure A B] at hx
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    rcases hy with hyA | hyB
    · exact ⟨y, hyA, 1, B.one_mem, by simp⟩
    · exact ⟨1, A.one_mem, y, hyB, by simp⟩
  | one => exact ⟨1, A.one_mem, 1, B.one_mem, by simp⟩
  | mul y z hy hz ihy ihz =>
    obtain ⟨a₁, ha₁, b₁, hb₁, rfl⟩ := ihy
    obtain ⟨a₂, ha₂, b₂, hb₂, rfl⟩ := ihz
    refine ⟨a₁ * a₂, A.mul_mem ha₁ ha₂, b₁ * b₂, B.mul_mem hb₁ hb₂, ?_⟩
    calc (a₁ * a₂) * (b₁ * b₂) = a₁ * (a₂ * b₁) * b₂ := by group
      _ = a₁ * (b₁ * a₂) * b₂ := by rw [hcomm a₂ ha₂ b₁ hb₁]
      _ = (a₁ * b₁) * (a₂ * b₂) := by group
  | inv y hy ihy =>
    obtain ⟨a, ha, b, hb, rfl⟩ := ihy
    refine ⟨a⁻¹, A.inv_mem ha, b⁻¹, B.inv_mem hb, ?_⟩
    rw [_root_.mul_inv_rev, ← hcomm a⁻¹ (A.inv_mem ha) b⁻¹ (B.inv_mem hb)]

theorem hmbSP_decomp (L₁ : SLPath M m₁) (L₂ : SLPath M 1)
    {d₁ d₂ : List ℕ} {I : Set (Fin D.rank)}
    (hlevi : leviM D I = (blockSL Fld m₁ d₁).map L₁.ε ⊔ (blockSL Fld 1 d₂).map L₂.ε)
    (hcomm : ∀ a ∈ (blockSL Fld m₁ d₁).map L₁.ε, ∀ b ∈ (blockSL Fld 1 d₂).map L₂.ε,
      a * b = b * a)
    {l₀ : K} (hl₀ : l₀ ∈ leviM D I) :
    ∃ A₀₁ ∈ blockSL Fld m₁ d₁, ∃ A₀₂ ∈ blockSL Fld 1 d₂,
      l₀ = L₁.ε A₀₁ * L₂.ε A₀₂ := by
  obtain ⟨y, hy, z, hz, hyz⟩ := hmbSP_mem_sup_of_commute hcomm (hlevi ▸ hl₀)
  obtain ⟨A₀₁, hA₀₁, hA₁⟩ := Subgroup.mem_map.mp hy
  obtain ⟨A₀₂, hA₀₂, hA₂⟩ := Subgroup.mem_map.mp hz
  refine ⟨A₀₁, hA₀₁, A₀₂, hA₀₂, ?_⟩
  rw [← hA₁, ← hA₂] at hyz
  exact hyz.symm

end Decomp

section SeamAux

theorem hmbSP_chart_e_inl [CharP Fld 2] {m₁ : ℕ} (L₁ : SLPath M m₁)
    (L₂ : SLPath M 1)
    {J₁ : Set (Fin D.rank)} {z : Fin D.rank} (hJ₁ : Set.range L₁.e = J₁) (hz₂ : L₂.e 0 = z)
    (hz : z ∉ J₁) (hcomm : ∀ i ∈ J₁, coxeterMatrix D.isFiniteType i z = 2)
    {a : K ⧸ borel D H} {g : K}
    (hR : residue (cs) (stdδ hct) (insert z J₁) a =
      residue (cs) (stdδ hct) (insert z J₁) ((g : K) : K ⧸ borel D H))
    (k : Fin m₁) (hk : L₁.e k ∈ J₁) :
    (hmbSP_chart hct hext L₁ L₂ hJ₁ hz₂ hz hcomm hR).e
      ⟨L₁.e k, Set.mem_insert_of_mem z hk⟩ = Sum.inl k := by
  rw [show (hmbSP_chart hct hext L₁ L₂ hJ₁ hz₂ hz hcomm hR).e
        ⟨L₁.e k, Set.mem_insert_of_mem z hk⟩ =
      (Equiv.sumCongr (slChart hct hext L₁ hJ₁ g).e
        (slChart hct hext L₂ (hmbSP_range_e_one hz₂) g).e)
        ((prodChart (stdBuilding hct hext) hz hcomm ((g : K) : K ⧸ borel D H)).e
          ⟨L₁.e k, Set.mem_insert_of_mem z hk⟩) from rfl]
  rw [prodChart_e_of_mem (hB := stdBuilding hct hext) (hz := hz) (hcomm := hcomm)
    (c := ((g : K) : K ⧸ borel D H)) hk]
  rw [show (Equiv.sumCongr (slChart hct hext L₁ hJ₁ g).e
        (slChart hct hext L₂ (hmbSP_range_e_one hz₂) g).e)
        (Sum.inl (⟨L₁.e k, hk⟩ : ↥J₁)) =
      Sum.inl ((slChart hct hext L₁ hJ₁ g).e ⟨L₁.e k, hk⟩) from rfl]
  rw [slChart_e_apply hct hext L₁ hJ₁ g k hk]

theorem hmbSP_chart_e_inr [CharP Fld 2] {m₁ : ℕ} (L₁ : SLPath M m₁)
    (L₂ : SLPath M 1)
    {J₁ : Set (Fin D.rank)} {z : Fin D.rank} (hJ₁ : Set.range L₁.e = J₁) (hz₂ : L₂.e 0 = z)
    (hz : z ∉ J₁) (hcomm : ∀ i ∈ J₁, coxeterMatrix D.isFiniteType i z = 2)
    {a : K ⧸ borel D H} {g : K}
    (hR : residue (cs) (stdδ hct) (insert z J₁) a =
      residue (cs) (stdδ hct) (insert z J₁) ((g : K) : K ⧸ borel D H)) :
    (hmbSP_chart hct hext L₁ L₂ hJ₁ hz₂ hz hcomm hR).e
      ⟨z, Set.mem_insert z J₁⟩ = Sum.inr (0 : Fin 1) := by
  rw [show (hmbSP_chart hct hext L₁ L₂ hJ₁ hz₂ hz hcomm hR).e
        ⟨z, Set.mem_insert z J₁⟩ =
      (Equiv.sumCongr (slChart hct hext L₁ hJ₁ g).e
        (slChart hct hext L₂ (hmbSP_range_e_one hz₂) g).e)
        ((prodChart (stdBuilding hct hext) hz hcomm ((g : K) : K ⧸ borel D H)).e
          ⟨z, Set.mem_insert z J₁⟩) from rfl]
  rw [prodChart_e_self (hB := stdBuilding hct hext) (hz := hz) (hcomm := hcomm)
    (c := ((g : K) : K ⧸ borel D H))]
  rw [show (Equiv.sumCongr (slChart hct hext L₁ hJ₁ g).e
        (slChart hct hext L₂ (hmbSP_range_e_one hz₂) g).e)
        (Sum.inr (⟨z, rfl⟩ : ↥({z} : Set (Fin D.rank)))) =
      Sum.inr ((slChart hct hext L₂ (hmbSP_range_e_one hz₂) g).e ⟨z, rfl⟩) from rfl]
  congr 1
  have h := slChart_e_apply hct hext L₂ (hmbSP_range_e_one hz₂) g (0 : Fin 1)
    (show L₂.e 0 ∈ ({z} : Set (Fin D.rank)) by rw [hz₂]; exact rfl)
  simpa [hz₂] using h

theorem hmbSP_coord_prod [CharP Fld 2] {m₁ : ℕ}
    (L₁ : SLPath M m₁) (L₂ : SLPath M 1)
    {J₁ : Set (Fin D.rank)} {z : Fin D.rank} (hJ₁ : Set.range L₁.e = J₁) (hz₂ : L₂.e 0 = z)
    (hz : z ∉ J₁) (hcomm : ∀ i ∈ J₁, coxeterMatrix D.isFiniteType i z = 2)
    {a : K ⧸ borel D H} {g : K}
    (hR : residue (cs) (stdδ hct) (insert z J₁) a =
      residue (cs) (stdδ hct) (insert z J₁) ((g : K) : K ⧸ borel D H))
    {t : K} (ht : t ∈ ⨆ k, H k) :
    ∃ Dt₁ : GL (Fin (m₁ + 1)) Fld, ∃ Dt₂ : GL (Fin 2) Fld,
      (∀ i j, i ≠ j → (Dt₁ : Matrix (Fin (m₁ + 1)) (Fin (m₁ + 1)) Fld) i j = 0) ∧
      (∀ i j, i ≠ j → (Dt₂ : Matrix (Fin 2) (Fin 2) Fld) i j = 0) ∧
      ∀ (A₁ : SpecialLinearGroup (Fin (m₁ + 1)) Fld) (A₂ : SpecialLinearGroup (Fin 2) Fld)
        (c : ↥(residue (cs) (stdδ hct) (insert z J₁) a)),
        (c : K ⧸ borel D H) = ((g * t * L₁.ε A₁ * L₂.ε A₂ : K) : K ⧸ borel D H) →
        (hmbSP_chart hct hext L₁ L₂ hJ₁ hz₂ hz hcomm hR).Φ c =
          (flagAct Dt₁ (flagAct (SpecialLinearGroup.toGL A₁) (stdFlag Fld (m₁ + 1))),
            flagAct Dt₂ (flagAct (SpecialLinearGroup.toGL A₂) (stdFlag Fld 2))) := by
  have hJ₂ : Set.range L₂.e = ({z} : Set (Fin D.rank)) := hmbSP_range_e_one hz₂
  obtain ⟨Dt₁, hdiag₁, hcoord₁⟩ := slChart_coord_torus hct hext L₁ hJ₁ g ht
  obtain ⟨Dt₂, hdiag₂, hcoord₂⟩ := slChart_coord_torus hct hext L₂ _ g ht
  refine ⟨Dt₁, Dt₂, hdiag₁, hdiag₂, ?_⟩
  intro A₁ A₂ c hc
  have hmem₁ : L₁.ε A₁ ∈ leviM D J₁ := by
    have h := hmbSP_range_eps_le_leviM L₁ (Set.mem_range_self A₁)
    rwa [hJ₁] at h
  have hmem₂ : L₂.ε A₂ ∈ leviM D ({z} : Set (Fin D.rank)) := by
    have h := hmbSP_range_eps_le_leviM L₂ (Set.mem_range_self A₂)
    rwa [hJ₂] at h
  have htB : t ∈ borel D H := iSup_le_borel ht
  have htmem₁ : t * L₁.ε A₁ * t⁻¹ ∈ leviM D J₁ :=
    (Subgroup.mem_normalizer_iff.mp
      (torus_le_normalizer_leviM (D := D) (I := J₁) hct ht) (L₁.ε A₁)).mp hmem₁
  have htmem₂ : t * L₂.ε A₂ * t⁻¹ ∈ leviM D ({z} : Set (Fin D.rank)) :=
    (Subgroup.mem_normalizer_iff.mp
      (torus_le_normalizer_leviM (D := D) (I := ({z} : Set (Fin D.rank))) hct ht)
      (L₂.ε A₂)).mp hmem₂
  have hgp₁ : ((g * t * L₁.ε A₁ : K) : K ⧸ borel D H) ∈
      residue (cs) (stdδ hct) J₁ ((g : K) : K ⧸ borel D H) := by
    rw [hmbSP_mk_mul_torus (D := D) (H := H) htB]
    exact mk_mul_mem_residue_of_mem_leviM hct hext g htmem₁
  have hgp₂ : ((g * t * L₂.ε A₂ : K) : K ⧸ borel D H) ∈
      residue (cs) (stdδ hct) ({z} : Set (Fin D.rank)) ((g : K) : K ⧸ borel D H) := by
    rw [hmbSP_mk_mul_torus (D := D) (H := H) htB]
    exact mk_mul_mem_residue_of_mem_leviM hct hext g htmem₂
  let p₁ : ↥(residue (cs) (stdδ hct) J₁ ((g : K) : K ⧸ borel D H)) :=
    ⟨((g * t * L₁.ε A₁ : K) : K ⧸ borel D H), hgp₁⟩
  let p₂ : ↥(residue (cs) (stdδ hct) ({z} : Set (Fin D.rank))
      ((g : K) : K ⧸ borel D H)) :=
    ⟨((g * t * L₂.ε A₂ : K) : K ⧸ borel D H), hgp₂⟩
  have hyp : (c : K ⧸ borel D H) ∈
      residue (cs) (stdδ hct) ({z} : Set (Fin D.rank)) p₁ := by
    rw [hc]
    exact mk_mul_mem_residue_of_mem_leviM hct hext (g * t * L₁.ε A₁) hmem₂
  have hyq : (c : K ⧸ borel D H) ∈ residue (cs) (stdδ hct) J₁ p₂ := by
    rw [hc]
    have hcm := hmbSP_commute hext L₁ L₂ hJ₁ hz₂ hz hcomm A₁ A₂
    have heq : ((g * t * L₁.ε A₁ * L₂.ε A₂ : K) : K ⧸ borel D H) =
        ((g * t * L₂.ε A₂ * L₁.ε A₁ : K) : K ⧸ borel D H) := by
      rw [show (g * t * L₁.ε A₁ * L₂.ε A₂ : K) = g * t * (L₁.ε A₁ * L₂.ε A₂) by group,
        show (g * t * L₂.ε A₂ * L₁.ε A₁ : K) = g * t * (L₂.ε A₂ * L₁.ε A₁) by group, hcm]
    rw [heq]
    exact mk_mul_mem_residue_of_mem_leviM hct hext (g * t * L₂.ε A₂) hmem₁
  have hpc : (prodChart (stdBuilding hct hext) hz hcomm
      ((g : K) : K ⧸ borel D H)).Φ
      ((ChamberIso.restrictCongr (buildingOver (cs) (stdδ hct) (insert z J₁)) hR).Φ c) =
      (p₁, p₂) := by
    rw [Equiv.apply_eq_iff_eq_symm_apply]
    apply Subtype.ext
    have h := prodChart_symm_apply_of_mem (stdBuilding hct hext) hz hcomm
      ((g : K) : K ⧸ borel D H) p₁.2 p₂.2 hyp hyq
    rw [Subtype.eta p₁, Subtype.eta p₂] at h
    rw [h]
    rfl
  have hΦ : (hmbSP_chart hct hext L₁ L₂ hJ₁ hz₂ hz hcomm hR).Φ c =
      ((slChart hct hext L₁ hJ₁ g).Φ p₁, (slChart hct hext L₂ (hmbSP_range_e_one hz₂) g).Φ p₂) := by
    rw [show (hmbSP_chart hct hext L₁ L₂ hJ₁ hz₂ hz hcomm hR).Φ c =
        ((slChart hct hext L₁ hJ₁ g).prodCongr (slChart hct hext L₂ (hmbSP_range_e_one hz₂) g)).Φ
          ((prodChart (stdBuilding hct hext) hz hcomm ((g : K) : K ⧸ borel D H)).Φ
            ((ChamberIso.restrictCongr (buildingOver (cs) (stdδ hct) (insert z J₁)) hR).Φ c))
        from rfl]
    rw [hpc]
    rfl
  rw [hΦ, hcoord₁ A₁ p₁ rfl, hcoord₂ A₂ p₂ rfl]

theorem hmbSP_beta_mem_blockSL {m₁ : ℕ} {d₁ : List ℕ} {k₁ : Fin m₁}
    (hk₁ : cutTypes m₁ d₁ = {k₁})
    (β : SpecialLinearGroup (Fin 2) Fld →* SpecialLinearGroup (Fin (m₁ + 1)) Fld)
    (hβu : ∀ c : Fld, β (tv Fld 0 1 c) = tv Fld k₁.castSucc k₁.succ c)
    (hβl : ∀ c : Fld, β (tv Fld 1 0 c) = tv Fld k₁.succ k₁.castSucc c)
    (X : SpecialLinearGroup (Fin 2) Fld) : β X ∈ blockSL Fld m₁ d₁ := by
  have hcomap : Subgroup.comap β (blockSL Fld m₁ d₁) = ⊤ := by
    refine CFSG.ClassicalGroups.SpecialLinear.eq_top_of_forall_transvection_mem _
      fun i j hij c => ?_
    rw [Subgroup.mem_comap]
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · change β (tv Fld 0 1 c) ∈ blockSL Fld m₁ d₁
      rw [hβu c]
      exact Subgroup.subset_closure ⟨k₁, by rw [hk₁]; exact rfl, c, Or.inl rfl⟩
    · change β (tv Fld 1 0 c) ∈ blockSL Fld m₁ d₁
      rw [hβl c]
      exact Subgroup.subset_closure ⟨k₁, by rw [hk₁]; exact rfl, c, Or.inr rfl⟩
    · exact absurd rfl hij
  exact show X ∈ Subgroup.comap β (blockSL Fld m₁ d₁) from by
    rw [hcomap]; exact Subgroup.mem_top X

theorem hmbSP_blockSL_le_map_beta {m₁ : ℕ} {d₁ : List ℕ} {k₁ : Fin m₁}
    (hk₁ : cutTypes m₁ d₁ = {k₁})
    (β : SpecialLinearGroup (Fin 2) Fld →* SpecialLinearGroup (Fin (m₁ + 1)) Fld)
    (hβu : ∀ c : Fld, β (tv Fld 0 1 c) = tv Fld k₁.castSucc k₁.succ c)
    (hβl : ∀ c : Fld, β (tv Fld 1 0 c) = tv Fld k₁.succ k₁.castSucc c) :
    blockSL Fld m₁ d₁ ≤ (⊤ : Subgroup (SpecialLinearGroup (Fin 2) Fld)).map β := by
  rw [blockSL, Subgroup.closure_le]
  rintro A ⟨k, hk, c, h | h⟩
  · have hk' : k = k₁ := by simpa [hk₁] using hk
    subst hk'
    rw [h]
    exact Subgroup.mem_map.mpr ⟨tv Fld 0 1 c, Subgroup.mem_top _, hβu c⟩
  · have hk' : k = k₁ := by simpa [hk₁] using hk
    subst hk'
    rw [h]
    exact Subgroup.mem_map.mpr ⟨tv Fld 1 0 c, Subgroup.mem_top _, hβl c⟩

theorem hmbSP_refSet_two : refSet Fld 2 [0,2] = Set.univ := by
  ext x
  simp only [refSet, Set.mem_setOf_eq, Set.mem_univ, iff_true]
  intro i hi
  simp only [List.length_cons, List.length_nil] at hi
  interval_cases i
  · show x.E 0 = Vsub (K := Fld) 2 0
    rw [show Vsub (K := Fld) 2 0 = ⊥ by
      rw [Submodule.eq_bot_iff]
      intro v hv
      funext j
      exact hv j (Nat.zero_le _)]
    exact (Submodule.finrank_eq_zero).mp (x.dim 0 (by omega))
  · show x.E 2 = Vsub (K := Fld) 2 2
    rw [show Vsub (K := Fld) 2 2 = ⊤ by
      rw [Submodule.eq_top_iff']
      intro v j hj
      exact absurd hj (not_le_of_gt j.isLt)]
    exact x.top 2 (by omega)

theorem hmbSP_kappa_beta {m₁ : ℕ} {v : W} (L₁ : SLPath M m₁) (L₂ : SLPath M 1)
    (β : SpecialLinearGroup (Fin 2) Fld →* SpecialLinearGroup (Fin (m₁ + 1)) Fld)
    (θ : Fld →+* Fld) (P : SpecialLinearGroup (Fin 2) Fld) (pol : Bool)
    (hXu : ∀ c : Fld, nrep hct v * F.φ (L₁.ε (β (tv Fld 0 1 c))) * (nrep hct v)⁻¹ =
      L₂.ε (kapMat θ pol P (tv Fld 0 1 c)))
    (hXl : ∀ c : Fld, nrep hct v * F.φ (L₁.ε (β (tv Fld 1 0 c))) * (nrep hct v)⁻¹ =
      L₂.ε (kapMat θ pol P (tv Fld 1 0 c))) :
    ∀ X : SpecialLinearGroup (Fin 2) Fld,
      nrep hct v * F.φ (L₁.ε (β X)) * (nrep hct v)⁻¹ = L₂.ε (kapMat θ pol P X) := by
  let f : SpecialLinearGroup (Fin 2) Fld →* K :=
    (MulAut.conj (nrep hct v)).toMonoidHom.comp (F.φ.comp (L₁.ε.comp β))
  let g : SpecialLinearGroup (Fin 2) Fld →* K := L₂.ε.comp (kapMat θ pol P)
  have hfg : f = g := by
    refine sl_hom_ext_simple (fun k c => ?_) (fun k c => ?_)
    · fin_cases k
      simpa [f, g, MonoidHom.comp_apply, MulAut.conj_apply] using hXu c
    · fin_cases k
      simpa [f, g, MonoidHom.comp_apply, MulAut.conj_apply] using hXl c
  intro X
  have h := congrFun (congrArg DFunLike.coe hfg) X
  simpa [f, g, MonoidHom.comp_apply, MulAut.conj_apply] using h

theorem hmbSP_kappa_snd {m₁ : ℕ} {v : W} (L₁ : SLPath M m₁) (L₂ : SLPath M 1)
    (β : SpecialLinearGroup (Fin 2) Fld →* SpecialLinearGroup (Fin (m₁ + 1)) Fld)
    (θ : Fld →+* Fld) (P : SpecialLinearGroup (Fin 2) Fld) (pol : Bool)
    (hXu : ∀ c : Fld, nrep hct v * F.φ (L₂.ε (tv Fld 0 1 c)) * (nrep hct v)⁻¹ =
      L₁.ε (β (kapMat θ pol P (tv Fld 0 1 c))))
    (hXl : ∀ c : Fld, nrep hct v * F.φ (L₂.ε (tv Fld 1 0 c)) * (nrep hct v)⁻¹ =
      L₁.ε (β (kapMat θ pol P (tv Fld 1 0 c)))) :
    ∀ Y : SpecialLinearGroup (Fin 2) Fld,
      nrep hct v * F.φ (L₂.ε Y) * (nrep hct v)⁻¹ = L₁.ε (β (kapMat θ pol P Y)) := by
  let f : SpecialLinearGroup (Fin 2) Fld →* K :=
    (MulAut.conj (nrep hct v)).toMonoidHom.comp (F.φ.comp L₂.ε)
  let g : SpecialLinearGroup (Fin 2) Fld →* K := L₁.ε.comp (β.comp (kapMat θ pol P))
  have hfg : f = g := by
    refine sl_hom_ext_simple (fun k c => ?_) (fun k c => ?_)
    · fin_cases k
      simpa [f, g, MonoidHom.comp_apply, MulAut.conj_apply] using hXu c
    · fin_cases k
      simpa [f, g, MonoidHom.comp_apply, MulAut.conj_apply] using hXl c
  intro Y
  have h := congrFun (congrArg DFunLike.coe hfg) Y
  simpa [f, g, MonoidHom.comp_apply, MulAut.conj_apply] using h

end SeamAux

end CFSG.ClassicalInvolution.Phan.PhanE.Res

end
