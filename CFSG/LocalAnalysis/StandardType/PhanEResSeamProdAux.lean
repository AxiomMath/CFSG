module

public import CFSG.LocalAnalysis.StandardType.PhanEResSeamProdA

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE.Res

open Matrix CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.RootSystem
  CFSG.LieType.Steinberg CFSG.LieType.Chevalley.CosetBuilding CFSG.Monster.B.Geometry
  CFSG.ClassicalInvolution.Phan.PhanE CFSG.ClassicalInvolution.Phan.PhanE.Flag
  CFSG.LieType.Steinberg.CentralExt.SLClosed CFSG.AGLEmbeddingD2.ParabLevi
open scoped commutatorElement

variable {K : Type} [Group K] {D : UniversalRootDatum K} {n : Fin D.rank → K}
  {H : Fin D.rank → Subgroup K} {Fld : Type} [Field Fld]

set_option hygiene false in
local notation "W" => (coxeterMatrix D.isFiniteType).Group
set_option hygiene false in
local notation "cs" => (coxeterMatrix D.isFiniteType).toCoxeterSystem

section Range

variable {M : ChevModel2 D n H Fld} {m : ℕ}

private theorem hmbSP_cutTypes_zero_eq_univ (m : ℕ) :
    cutTypes m [0, m + 1] = Set.univ := by
  ext j
  simp only [cutTypes, Set.mem_setOf_eq, Set.mem_univ, iff_true]
  intro i hi
  have hi' : i < 2 := by simpa using hi
  interval_cases i
  · simp
  · simp only [List.getD_cons_zero, List.getD_cons_succ, List.getD_nil]
    have hj : j.val < m := j.isLt
    omega

private theorem hmbSP_blockSL_top {m : ℕ} {d : List ℕ} (huniv : cutTypes m d = Set.univ) :
    blockSL Fld m d = ⊤ := by
  rw [blockSL]
  have hset : {A : SpecialLinearGroup (Fin (m + 1)) Fld | ∃ k : Fin m, k ∈ cutTypes m d ∧
      ∃ c : Fld, A = tv Fld k.castSucc k.succ c ∨ A = tv Fld k.succ k.castSucc c} =
      {A : SpecialLinearGroup (Fin (m + 1)) Fld | ∃ k : Fin m, ∃ c : Fld,
        A = tv Fld k.castSucc k.succ c ∨ A = tv Fld k.succ k.castSucc c} := by
    ext A; constructor
    · rintro ⟨k, _, c, h⟩; exact ⟨k, c, h⟩
    · rintro ⟨k, c, h⟩; exact ⟨k, huniv ▸ Set.mem_univ k, c, h⟩
  rw [hset]
  exact hmbSP_closure_simple_eq_top

theorem hmbSP_range_eps_le_leviM (L : SLPath M m) :
    Set.range L.ε ⊆ (leviM D (Set.range L.e) : Set K) := by
  have hmap := map_blockSL L [0, m + 1]
  rw [hmbSP_blockSL_top (hmbSP_cutTypes_zero_eq_univ m)] at hmap
  intro x hx
  obtain ⟨A, rfl⟩ := hx
  have hxmap : L.ε A ∈ Subgroup.map L.ε
      (⊤ : Subgroup (SpecialLinearGroup (Fin (m + 1)) Fld)) :=
    ⟨A, Subgroup.mem_top A, rfl⟩
  rw [hmap] at hxmap
  rwa [hmbSP_cutTypes_zero_eq_univ m, Set.image_univ] at hxmap

theorem hmbSP_commutes_rankOne (hext : SteinbergExtras D n H) {i j : Fin D.rank}
    (h2 : coxeterMatrix D.isFiniteType i j = 2) :
    ∀ x ∈ rankOne D.rootGroup i, ∀ y ∈ rankOne D.rootGroup j, x * y = y * x := by
  have hij : i ≠ j := by
    rintro rfl
    have h1 : coxeterMatrix D.isFiniteType i i = 1 := by
      unfold CFSG.LieType.RootSystem.coxeterMatrix
      rw [TauCeti.coxeterMatrixOfCartanMatrix_apply, D.isFiniteType.apply_self]
      norm_num [TauCeti.coxeterOrder_four]
    rw [h1] at h2
    omega
  have hA : D.cartan i j = 0 :=
    (TauCeti.coxeterMatrixOfCartanMatrix_apply_eq_two_iff D.cartan D.isFiniteType.apply_self
      (fun _ _ h => D.isFiniteType.apply_mul_apply_mem_of_ne h)
      (fun _ _ h => (D.isFiniteType.apply_eq_zero_iff).1 h) hij).1 h2
  exact hmbSP_commutes_rankOne_of_cartan hext hij hA

theorem hmbSP_commute (hext : SteinbergExtras D n H) {M : ChevModel2 D n H Fld} {m₁ : ℕ}
    (L₁ : SLPath M m₁) (L₂ : SLPath M 1) {J₁ : Set (Fin D.rank)} {z : Fin D.rank}
    (hJ₁ : Set.range L₁.e = J₁) (hz₂ : L₂.e 0 = z) (hz : z ∉ J₁)
    (hcomm : ∀ i ∈ J₁, coxeterMatrix D.isFiniteType i z = 2)
    (A₁ : SpecialLinearGroup (Fin (m₁ + 1)) Fld) (A₂ : SpecialLinearGroup (Fin 2) Fld) :
    L₁.ε A₁ * L₂.ε A₂ = L₂.ε A₂ * L₁.ε A₁ := by
  have h1 : L₁.ε A₁ ∈ leviM D J₁ := by
    have h := hmbSP_range_eps_le_leviM L₁ (Set.mem_range_self A₁)
    rwa [hJ₁] at h
  have hrange₂ : Set.range L₂.e = ({z} : Set (Fin D.rank)) := by
    ext i; constructor
    · rintro ⟨k, rfl⟩
      rw [Set.mem_singleton_iff]
      fin_cases k
      exact hz₂
    · intro hi
      exact ⟨0, by rw [Set.mem_singleton_iff] at hi; rw [hz₂, hi]⟩
  have h2 : L₂.ε A₂ ∈ rankOne D.rootGroup z := by
    have hmem : L₂.ε A₂ ∈ leviM D ({z} : Set (Fin D.rank)) := by
      have h := hmbSP_range_eps_le_leviM L₂ (Set.mem_range_self A₂)
      rwa [hrange₂] at h
    have hle : leviM D ({z} : Set (Fin D.rank)) ≤ rankOne D.rootGroup z := by
      rw [leviM]
      refine iSup₂_le fun i hi => ?_
      rw [Set.mem_singleton_iff] at hi
      rw [hi]
    exact hle hmem
  have hle : leviM D J₁ ≤ Subgroup.centralizer (rankOne D.rootGroup z : Set K) := by
    rw [leviM]
    refine iSup₂_le fun i hi => ?_
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (hmbSP_commutes_rankOne hext (hcomm i hi) x hx y hy).symm
  have hc := hle h1
  rw [Subgroup.mem_centralizer_iff] at hc
  exact (hc (L₂.ε A₂) h2).symm

end Range

section Kappa

variable {M : ChevModel2 D n H Fld}

theorem hmbSP_kappa_blockSL (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H) {w₀ : W} (F : FrobData D n H w₀)
    {m : ℕ} (L : SLPath M m) {v : W} (θ : Fld →+* Fld)
    (P : SpecialLinearGroup (Fin (m + 1)) Fld) (pol : Bool) {d : List ℕ}
    (hPu : ∀ k ∈ cutTypes m d, ∀ c : Fld,
      nrep hct v * F.φ (L.ε (tv Fld k.castSucc k.succ c)) * (nrep hct v)⁻¹ =
        L.ε (kapMat θ pol P (tv Fld k.castSucc k.succ c)))
    (hPl : ∀ k ∈ cutTypes m d, ∀ c : Fld,
      nrep hct v * F.φ (L.ε (tv Fld k.succ k.castSucc c)) * (nrep hct v)⁻¹ =
        L.ε (kapMat θ pol P (tv Fld k.succ k.castSucc c))) :
    ∀ A ∈ blockSL Fld m d,
      nrep hct v * F.φ (L.ε A) * (nrep hct v)⁻¹ = L.ε (kapMat θ pol P A) := by
  let κ : K →* K := (MulAut.conj (nrep hct v)).toMonoidHom.comp F.φ
  have hκ : ∀ x : K, κ x = nrep hct v * F.φ x * (nrep hct v)⁻¹ := by
    intro x; rfl
  intro A hA
  change κ (L.ε A) = L.ε (kapMat θ pol P A)
  induction hA using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with ⟨k, hk, c, h | h⟩
    · rw [h, hκ]; exact hPu k hk c
    · rw [h, hκ]; exact hPl k hk c
  | one => simp
  | mul x y hx hy ihx ihy => simp only [map_mul, ihx, ihy]
  | inv x hx ih => simp only [map_inv, ih]

end Kappa

section Chart

variable {M : ChevModel2 D n H Fld}

theorem hmbSP_range_e_one {L : SLPath M 1} {z : Fin D.rank} (hz : L.e 0 = z) :
    Set.range L.e = ({z} : Set (Fin D.rank)) := by
  ext i
  constructor
  · rintro ⟨k, rfl⟩
    rw [Set.mem_singleton_iff]
    fin_cases k
    exact hz
  · intro hi
    rw [Set.mem_singleton_iff] at hi
    exact ⟨0, by rw [hz, hi]⟩

@[expose] noncomputable def hmbSP_chart [CharP Fld 2] {m₁ : ℕ}
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H) (hext : SteinbergExtras D n H)
    (L₁ : SLPath M m₁) (L₂ : SLPath M 1)
    {J₁ : Set (Fin D.rank)} {z : Fin D.rank} (hJ₁ : Set.range L₁.e = J₁) (hz₂ : L₂.e 0 = z)
    (hz : z ∉ J₁) (hcomm : ∀ i ∈ J₁, coxeterMatrix D.isFiniteType i z = 2)
    {a : K ⧸ borel D H} {g : K}
    (hR : residue (cs) (stdδ hct) (insert z J₁) a =
      residue (cs) (stdδ hct) (insert z J₁) ((g : K) : K ⧸ borel D H)) :
    ChamberIso ((buildingOver (cs) (stdδ hct) (insert z J₁)).restrict
      (residue (cs) (stdδ hct) (insert z J₁) a)) ((flagSys Fld m₁).prod (flagSys Fld 1)) :=
  (ChamberIso.restrictCongr (buildingOver (cs) (stdδ hct) (insert z J₁)) hR).trans
    ((prodChart (stdBuilding hct hext) hz hcomm ((g : K) : K ⧸ borel D H)).trans
      ((slChart hct hext L₁ hJ₁ g).prodCongr
        (slChart hct hext L₂ (hmbSP_range_e_one hz₂) g)))

theorem hmbSP_chart_symm_apply [CharP Fld 2] {m₁ : ℕ}
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H) (hext : SteinbergExtras D n H)
    (L₁ : SLPath M m₁) (L₂ : SLPath M 1)
    {J₁ : Set (Fin D.rank)} {z : Fin D.rank} (hJ₁ : Set.range L₁.e = J₁) (hz₂ : L₂.e 0 = z)
    (hz : z ∉ J₁) (hcomm : ∀ i ∈ J₁, coxeterMatrix D.isFiniteType i z = 2)
    {a : K ⧸ borel D H} {g : K}
    (hR : residue (cs) (stdδ hct) (insert z J₁) a =
      residue (cs) (stdδ hct) (insert z J₁) ((g : K) : K ⧸ borel D H))
    (A₁ : SpecialLinearGroup (Fin (m₁ + 1)) Fld) (A₂ : SpecialLinearGroup (Fin 2) Fld) :
    (((hmbSP_chart hct hext L₁ L₂ hJ₁ hz₂ hz hcomm hR).Φ.symm
        (flagAct (SpecialLinearGroup.toGL A₁) (stdFlag Fld (m₁ + 1)),
          flagAct (SpecialLinearGroup.toGL A₂) (stdFlag Fld 2)) :
      ↥(residue (cs) (stdδ hct) (insert z J₁) a)) : K ⧸ borel D H) =
      ((g * L₁.ε A₁ * L₂.ε A₂ : K) : K ⧸ borel D H) := by
  have hJ₂ : Set.range L₂.e = ({z} : Set (Fin D.rank)) := hmbSP_range_e_one hz₂
  have hmem₁ : L₁.ε A₁ ∈ leviM D J₁ := by
    have h := hmbSP_range_eps_le_leviM L₁ (Set.mem_range_self A₁)
    rwa [hJ₁] at h
  have hmem₂ : L₂.ε A₂ ∈ leviM D ({z} : Set (Fin D.rank)) := by
    have h := hmbSP_range_eps_le_leviM L₂ (Set.mem_range_self A₂)
    rwa [hJ₂] at h
  let p₁ : ↥(residue (cs) (stdδ hct) J₁ ((g : K) : K ⧸ borel D H)) :=
    (slChart hct hext L₁ hJ₁ g).Φ.symm
      (flagAct (SpecialLinearGroup.toGL A₁) (stdFlag Fld (m₁ + 1)))
  let p₂ : ↥(residue (cs) (stdδ hct) ({z} : Set (Fin D.rank))
      ((g : K) : K ⧸ borel D H)) :=
    (slChart hct hext L₂ hJ₂ g).Φ.symm
      (flagAct (SpecialLinearGroup.toGL A₂) (stdFlag Fld 2))
  have hp₁ : (p₁ : K ⧸ borel D H) = ((g * L₁.ε A₁ : K) : K ⧸ borel D H) :=
    slChart_symm_apply hct hext L₁ hJ₁ g A₁
  have hp₂ : (p₂ : K ⧸ borel D H) = ((g * L₂.ε A₂ : K) : K ⧸ borel D H) :=
    slChart_symm_apply hct hext L₂ hJ₂ g A₂
  have hmain : ((prodChart (stdBuilding hct hext) hz hcomm
      ((g : K) : K ⧸ borel D H)).Φ.symm (p₁, p₂) : K ⧸ borel D H) =
      ((g * L₁.ε A₁ * L₂.ε A₂ : K) : K ⧸ borel D H) := by
    have hyp : ((g * L₁.ε A₁ * L₂.ε A₂ : K) : K ⧸ borel D H) ∈
        residue (cs) (stdδ hct) ({z} : Set (Fin D.rank)) p₁ := by
      rw [hp₁]
      exact mk_mul_mem_residue_of_mem_leviM hct hext (g * L₁.ε A₁) hmem₂
    have hyq : ((g * L₁.ε A₁ * L₂.ε A₂ : K) : K ⧸ borel D H) ∈
        residue (cs) (stdδ hct) J₁ p₂ := by
      rw [hp₂]
      have hc := hmbSP_commute hext L₁ L₂ hJ₁ hz₂ hz hcomm A₁ A₂
      have heq : ((g * L₁.ε A₁ * L₂.ε A₂ : K) : K ⧸ borel D H) =
          ((g * L₂.ε A₂ * L₁.ε A₁ : K) : K ⧸ borel D H) := by
        rw [show (g * L₁.ε A₁ * L₂.ε A₂ : K) = g * (L₁.ε A₁ * L₂.ε A₂) by group,
          show (g * L₂.ε A₂ * L₁.ε A₁ : K) = g * (L₂.ε A₂ * L₁.ε A₁) by group, hc]
      rw [heq]
      exact mk_mul_mem_residue_of_mem_leviM hct hext (g * L₂.ε A₂) hmem₁
    have h := prodChart_symm_apply_of_mem (stdBuilding hct hext) hz hcomm
      ((g : K) : K ⧸ borel D H) p₁.2 p₂.2 hyp hyq
    rwa [Subtype.eta p₁, Subtype.eta p₂] at h
  exact hmain

theorem hmbSP_mk_mul_torus {g x t : K} (ht : t ∈ borel D H) :
    ((g * t * x : K) : K ⧸ borel D H) = ((g * (t * x * t⁻¹) : K) : K ⧸ borel D H) := by
  rw [QuotientGroup.eq]
  have h : (g * t * x)⁻¹ * (g * (t * x * t⁻¹)) = t⁻¹ := by group
  rw [h]
  exact inv_mem ht

end Chart

end CFSG.ClassicalInvolution.Phan.PhanE.Res

end
