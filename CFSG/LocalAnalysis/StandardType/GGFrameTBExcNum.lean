module

public import CFSG.LocalAnalysis.StandardType.GGFrameTBTw
public import CFSG.LocalAnalysis.StandardType.GGFrameModelStep
public import CFSG.LocalAnalysis.StandardType.GGCoxReflConv

public section

namespace CFSG.StandardType.FrameRoute

open CFSG CFSG.Assembly

private theorem frameExcNum_frameReflSet_subset_coxRefl {G : Type} [Group G] [Finite G]
    {Bs : Subgroup G} (hBs : IsElemAbelian 3 Bs) {n : ℕ} {M : CoxeterMatrix (Fin n)}
    {𝒜 : Subgroup (MulAut ↥Bs)} {e : M.Group ≃* ↥𝒜}
    (hpres : GGCoxeterPres 3 𝒜 M e)
    (h3 : ∀ i j : Fin n, i ≠ j → M.M i j ≤ 3)
    (hnt : ∀ φ ∈ 𝒜, ¬ GGIsTransvection 3 φ) :
    frameReflSet 𝒜 ⊆ ggCoxRefl M e := by
  intro φ hφ
  exact ggCoxRefl_of_isReflection Nat.prime_three (by norm_num) hBs hpres h3 hnt hφ.1 hφ.2

private theorem frameExcNum_coxRefl_subset_frameReflSet {G : Type} [Group G] [Finite G]
    {Bs : Subgroup G} {n : ℕ} {M : CoxeterMatrix (Fin n)}
    {𝒜 : Subgroup (MulAut ↥Bs)} {e : M.Group ≃* ↥𝒜}
    (hpres : GGCoxeterPres 3 𝒜 M e) :
    ggCoxRefl M e ⊆ frameReflSet 𝒜 := by
  intro φ hφ
  refine ⟨?_, ggCoxRefl_isReflection (p := 3) hpres.2 hφ⟩
  obtain ⟨w, i, rfl⟩ := hφ
  exact (e (w * M.simple i * w⁻¹)).2

private noncomputable def frameExcNum_pre {G : Type} [Group G] [Finite G] {Bs : Subgroup G}
    {n : ℕ} {M : CoxeterMatrix (Fin n)} {𝒜 : Subgroup (MulAut ↥Bs)}
    (e : M.Group ≃* ↥𝒜) {ρ : ↥𝒜 →* FEMat n}
    (hρ : ∀ i, ρ (e (M.simple i)) = feS n i) (t : feT n) :
    MulAut ↥Bs :=
  ((frameModel_feT e hρ t.2).choose : MulAut ↥Bs)

private theorem frameExcNum_pre_mem {G : Type} [Group G] [Finite G] {Bs : Subgroup G}
    {n : ℕ} {M : CoxeterMatrix (Fin n)} {𝒜 : Subgroup (MulAut ↥Bs)}
    {e : M.Group ≃* ↥𝒜} (hpres : GGCoxeterPres 3 𝒜 M e) {ρ : ↥𝒜 →* FEMat n}
    (hρ : ∀ i, ρ (e (M.simple i)) = feS n i) (t : feT n) :
    frameExcNum_pre e hρ t ∈ frameReflSet 𝒜 :=
  frameExcNum_coxRefl_subset_frameReflSet hpres
    (frameModel_feT e hρ t.2).choose_spec.1

private theorem frameExcNum_pre_rho {G : Type} [Group G] [Finite G] {Bs : Subgroup G}
    {n : ℕ} {M : CoxeterMatrix (Fin n)} {𝒜 : Subgroup (MulAut ↥Bs)}
    {e : M.Group ≃* ↥𝒜} (hpres : GGCoxeterPres 3 𝒜 M e) {ρ : ↥𝒜 →* FEMat n}
    (hρ : ∀ i, ρ (e (M.simple i)) = feS n i) (t : feT n) :
    ρ ⟨frameExcNum_pre e hρ t, (frameExcNum_pre_mem hpres hρ t).1⟩ = t :=
  (frameModel_feT e hρ t.2).choose_spec.2

private theorem frameExcNum_pre_eq {G : Type} [Group G] [Finite G] {Bs : Subgroup G}
    {n : ℕ} {M : CoxeterMatrix (Fin n)} {𝒜 : Subgroup (MulAut ↥Bs)}
    {e : M.Group ≃* ↥𝒜} (hpres : GGCoxeterPres 3 𝒜 M e) {ρ : ↥𝒜 →* FEMat n}
    (hρi : Function.Injective ρ) (hρ : ∀ i, ρ (e (M.simple i)) = feS n i)
    {t : feT n} {s : MulAut ↥Bs} (hs : s ∈ frameReflSet 𝒜)
    (hst : ρ ⟨s, hs.1⟩ = t) :
    frameExcNum_pre e hρ t = s := by
  have h1 : ρ ⟨frameExcNum_pre e hρ t, (frameExcNum_pre_mem hpres hρ t).1⟩ =
      ρ ⟨s, hs.1⟩ := by
    rw [frameExcNum_pre_rho hpres hρ t, hst]
  exact congrArg Subtype.val (hρi h1)

private theorem frameExcNum_rho_mem {G : Type} [Group G] [Finite G] {Bs : Subgroup G}
    (hBs : IsElemAbelian 3 Bs) {n : ℕ} {M : CoxeterMatrix (Fin n)}
    {𝒜 : Subgroup (MulAut ↥Bs)} {e : M.Group ≃* ↥𝒜}
    (hpres : GGCoxeterPres 3 𝒜 M e)
    (h3 : ∀ i j : Fin n, i ≠ j → M.M i j ≤ 3)
    (hnt : ∀ φ ∈ 𝒜, ¬ GGIsTransvection 3 φ) {ρ : ↥𝒜 →* FEMat n}
    (hρ : ∀ i, ρ (e (M.simple i)) = feS n i) {φ : MulAut ↥Bs}
    (hφ : φ ∈ frameReflSet 𝒜) : ρ ⟨φ, hφ.1⟩ ∈ feT n :=
  frameModel_coxRefl e hρ
    (frameExcNum_frameReflSet_subset_coxRefl hBs hpres h3 hnt hφ)

private theorem frameExcNum_comm_iff {G : Type} [Group G] {Bs : Subgroup G} {n : ℕ}
    {𝒜 : Subgroup (MulAut ↥Bs)} {ρ : ↥𝒜 →* FEMat n} (hρi : Function.Injective ρ)
    {φ ψ : MulAut ↥Bs} (hφ : φ ∈ 𝒜) (hψ : ψ ∈ 𝒜) :
    (φ * ψ = ψ * φ) ↔
      (ρ ⟨φ, hφ⟩ * ρ ⟨ψ, hψ⟩ = ρ ⟨ψ, hψ⟩ * ρ ⟨φ, hφ⟩) := by
  constructor
  · intro h
    rw [← map_mul, ← map_mul]
    exact congrArg ρ (Subtype.ext h)
  · intro h
    have hsub : (⟨φ, hφ⟩ : ↥𝒜) * ⟨ψ, hψ⟩ = ⟨ψ, hψ⟩ * ⟨φ, hφ⟩ := by
      apply hρi
      simpa only [map_mul] using h
    exact congrArg Subtype.val hsub

private theorem frameExcNum_noncomm_iff {G : Type} [Group G] {Bs : Subgroup G} {n : ℕ}
    {𝒜 : Subgroup (MulAut ↥Bs)} {ρ : ↥𝒜 →* FEMat n} (hρi : Function.Injective ρ)
    {φ ψ : MulAut ↥Bs} (hφ : φ ∈ 𝒜) (hψ : ψ ∈ 𝒜) :
    (φ * ψ ≠ ψ * φ) ↔
      (ρ ⟨φ, hφ⟩ * ρ ⟨ψ, hψ⟩ ≠ ρ ⟨ψ, hψ⟩ * ρ ⟨φ, hφ⟩) :=
  not_congr (frameExcNum_comm_iff hρi hφ hψ)

private theorem frameExcNum_ncard_reflSet {G : Type} [Group G] [Finite G] {Bs : Subgroup G}
    (hBs : IsElemAbelian 3 Bs) {n : ℕ} {M : CoxeterMatrix (Fin n)}
    {𝒜 : Subgroup (MulAut ↥Bs)} {e : M.Group ≃* ↥𝒜}
    (hpres : GGCoxeterPres 3 𝒜 M e)
    (h3 : ∀ i j : Fin n, i ≠ j → M.M i j ≤ 3)
    (hnt : ∀ φ ∈ 𝒜, ¬ GGIsTransvection 3 φ) {ρ : ↥𝒜 →* FEMat n}
    (hρi : Function.Injective ρ) (hρ : ∀ i, ρ (e (M.simple i)) = feS n i) :
    (frameReflSet 𝒜).ncard = (feT n).ncard := by
  refine Set.ncard_congr (fun φ hφ => ρ ⟨φ, hφ.1⟩) ?_ ?_ ?_
  · intro φ hφ
    exact frameExcNum_rho_mem hBs hpres h3 hnt hρ hφ
  · intro φ ψ hφ hψ h
    exact congrArg Subtype.val (hρi h)
  · intro t ht
    obtain ⟨φ, hcx, hφt⟩ := frameModel_feT e hρ ht
    exact ⟨(φ : MulAut ↥Bs), frameExcNum_coxRefl_subset_frameReflSet hpres hcx, hφt⟩

private theorem frameExcNum_ncard_nonComm {G : Type} [Group G] [Finite G] {Bs : Subgroup G}
    (hBs : IsElemAbelian 3 Bs) {n : ℕ} {M : CoxeterMatrix (Fin n)}
    {𝒜 : Subgroup (MulAut ↥Bs)} {e : M.Group ≃* ↥𝒜}
    (hpres : GGCoxeterPres 3 𝒜 M e)
    (h3 : ∀ i j : Fin n, i ≠ j → M.M i j ≤ 3)
    (hnt : ∀ φ ∈ 𝒜, ¬ GGIsTransvection 3 φ) {ρ : ↥𝒜 →* FEMat n}
    (hρi : Function.Injective ρ) (hρ : ∀ i, ρ (e (M.simple i)) = feS n i)
    {φ : MulAut ↥Bs} (hφ : φ ∈ frameReflSet 𝒜) :
    {ψ | ψ ∈ frameReflSet 𝒜 ∧ φ * ψ ≠ ψ * φ}.ncard =
      {t | t ∈ feT n ∧ ρ ⟨φ, hφ.1⟩ * t ≠ t * ρ ⟨φ, hφ.1⟩}.ncard := by
  refine Set.ncard_congr (fun ψ hψ => ρ ⟨ψ, hψ.1.1⟩) ?_ ?_ ?_
  · intro ψ hψ
    obtain ⟨hψset, hne⟩ := hψ
    exact ⟨frameExcNum_rho_mem hBs hpres h3 hnt hρ hψset,
      (frameExcNum_noncomm_iff hρi hφ.1 hψset.1).mp hne⟩
  · intro ψ χ hψ hχ h
    exact congrArg Subtype.val (hρi h)
  · intro t ht
    obtain ⟨htfeT, hne⟩ := ht
    refine ⟨frameExcNum_pre e hρ ⟨t, htfeT⟩,
      ⟨frameExcNum_pre_mem hpres hρ ⟨t, htfeT⟩, ?_⟩,
      frameExcNum_pre_rho hpres hρ ⟨t, htfeT⟩⟩
    intro h
    have h' := (frameExcNum_comm_iff hρi hφ.1
      (frameExcNum_pre_mem hpres hρ ⟨t, htfeT⟩).1).mp h
    rw [frameExcNum_pre_rho hpres hρ ⟨t, htfeT⟩] at h'
    exact hne h'

private theorem frameExcNum_path_lift {G : Type} [Group G] [Finite G] {Bs : Subgroup G}
    {n : ℕ} {M : CoxeterMatrix (Fin n)}
    {𝒜 : Subgroup (MulAut ↥Bs)} {e : M.Group ≃* ↥𝒜}
    (hpres : GGCoxeterPres 3 𝒜 M e) {ρ : ↥𝒜 →* FEMat n}
    (hρi : Function.Injective ρ) (hρ : ∀ i, ρ (e (M.simple i)) = feS n i)
    {r t : feT n}
    (h : Relation.ReflTransGen
      (fun a b => a ∈ feT n ∧ b ∈ feT n ∧ a * b ≠ b * a)
      (r : FEMat n) (t : FEMat n)) :
    Relation.ReflTransGen
      (fun a b => a ∈ frameReflSet 𝒜 ∧ b ∈ frameReflSet 𝒜 ∧ a * b ≠ b * a)
      (frameExcNum_pre e hρ r) (frameExcNum_pre e hρ t) := by
  refine h.head_induction_on
    (motive := fun a _ => ∀ ha : a ∈ feT n,
      Relation.ReflTransGen
        (fun a b => a ∈ frameReflSet 𝒜 ∧ b ∈ frameReflSet 𝒜 ∧ a * b ≠ b * a)
        (frameExcNum_pre e hρ ⟨a, ha⟩) (frameExcNum_pre e hρ t)) ?_ ?_ r.2
  · intro _
    exact Relation.ReflTransGen.refl
  · intro a c h' _ ih ha
    obtain ⟨_, hc, hne⟩ := h'
    refine Relation.ReflTransGen.head ?_ (ih hc)
    have hpa := frameExcNum_pre_mem hpres hρ ⟨a, ha⟩
    have hpc := frameExcNum_pre_mem hpres hρ ⟨c, hc⟩
    refine ⟨hpa, hpc, (frameExcNum_noncomm_iff hρi hpa.1 hpc.1).mpr ?_⟩
    rwa [frameExcNum_pre_rho hpres hρ ⟨a, ha⟩,
      frameExcNum_pre_rho hpres hρ ⟨c, hc⟩]


theorem frameNumIs_frameConn_of_frameRep {G : Type} [Group G] [Finite G] {Bs : Subgroup G}
    (hBs : IsElemAbelian 3 Bs) {n : ℕ} {M : CoxeterMatrix (Fin n)} {𝒜 : Subgroup (MulAut ↥Bs)}
    {e : M.Group ≃* ↥𝒜} (hpres : GGCoxeterPres 3 𝒜 M e)
    (h3 : ∀ i j : Fin n, i ≠ j → M.M i j ≤ 3) (hnt : ∀ φ ∈ 𝒜, ¬ GGIsTransvection 3 φ)
    {ρ : ↥𝒜 →* FEMat n} (hρi : Function.Injective ρ) (hρ : ∀ i, ρ (e (M.simple i)) = feS n i)
    {N d : ℕ} (hN : (feT n).ncard = N)
    (hd : ∀ r ∈ feT n, {t | t ∈ feT n ∧ r * t ≠ t * r}.ncard = d)
    (hconn : ∀ r ∈ feT n, ∀ t ∈ feT n,
      Relation.ReflTransGen (fun a b => a ∈ feT n ∧ b ∈ feT n ∧ a * b ≠ b * a) r t) :
    FrameNumIs 𝒜 N (some d) ∧ FrameConn 𝒜 := by
  classical
  have hcard : (frameReflSet 𝒜).ncard = N := by
    rw [frameExcNum_ncard_reflSet hBs hpres h3 hnt hρi hρ, hN]
  have hrefl : ∀ φ ∈ frameReflSet 𝒜, frameNonComm 𝒜 φ = d := by
    intro φ hφ
    rw [frameNonComm, frameExcNum_ncard_nonComm hBs hpres h3 hnt hρi hρ hφ]
    exact hd (ρ ⟨φ, hφ.1⟩) (frameExcNum_rho_mem hBs hpres h3 hnt hρ hφ)
  have hconn' : FrameConn 𝒜 := by
    intro φ hφ ψ hψ
    have hpφ : ρ ⟨φ, hφ.1⟩ ∈ feT n :=
      frameExcNum_rho_mem hBs hpres h3 hnt hρ hφ
    have hpψ : ρ ⟨ψ, hψ.1⟩ ∈ feT n :=
      frameExcNum_rho_mem hBs hpres h3 hnt hρ hψ
    have hpath := hconn (ρ ⟨φ, hφ.1⟩) hpφ (ρ ⟨ψ, hψ.1⟩) hpψ
    have hlift := frameExcNum_path_lift hpres hρi hρ
      (r := ⟨ρ ⟨φ, hφ.1⟩, hpφ⟩) (t := ⟨ρ ⟨ψ, hψ.1⟩, hpψ⟩) hpath
    have e1 : frameExcNum_pre e hρ ⟨ρ ⟨φ, hφ.1⟩, hpφ⟩ = φ :=
      frameExcNum_pre_eq hpres hρi hρ hφ rfl
    have e2 : frameExcNum_pre e hρ ⟨ρ ⟨ψ, hψ.1⟩, hpψ⟩ = ψ :=
      frameExcNum_pre_eq hpres hρi hρ hψ rfl
    rwa [e1, e2] at hlift
  refine ⟨?_, hconn'⟩
  change (frameReflSet 𝒜).ncard = N ∧ ∀ φ ∈ frameReflSet 𝒜, frameNonComm 𝒜 φ = d
  exact ⟨hcard, hrefl⟩

theorem ggTorusTBGroup_of_pow_le {p r s : ℕ} {R : Type} [Group R] {I : Set (MulAut R)}
    {L' : Type} [Group L'] [Finite L'] {ψ : L' →* R} {A : Subgroup (MulAut L')}
    (h : GGTorusTBGroup p r R I L' ψ A) (hs : p ^ s ≤ Nat.card A) :
    GGTorusTBGroup p s R I L' ψ A := by
  obtain ⟨hψ, hker, hperf, hAe, hAI, _, h3, hsc⟩ := h
  exact ⟨hψ, hker, hperf, hAe, hAI, hs, h3, hsc⟩

theorem frameTBBody_of_rowGe {lab : LargeEvenLabel} {N : ℕ} {d : Option ℕ}
    (hnum : frameLabNum lab = (N, d))
    (h : LargeEvenLabelAll lab fun R _ I _ => ∀ r : ℕ, 6 ≤ r → GGTorusReflGenW 3 r R I ∧
      ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R) (A : Subgroup (MulAut L')),
        GGTorusTBGroup 3 r R I L' ψ A →
          (FrameNumIs (ggAutomizer (MulAut.conj : L' →* MulAut L').range A) N d ∧
            FrameConn (ggAutomizer (MulAut.conj : L' →* MulAut L').range A)) ∧
          ∃ S : Subgroup L', IsPGroup 3 S ∧ ¬ IsCyclic S) :
    LargeEvenLabelAll lab (frameTBBody lab) :=
  h.mono fun R _ I _ hR r hr _ => by
    rw [hnum]
    exact hR r hr

end CFSG.StandardType.FrameRoute

end
