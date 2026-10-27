module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimePairE6
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeRetIotaAux

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.StandardType CFSG.StandardType.GGFinModel CFSG.LieType.Chevalley
  CFSG.StandardType.S2MathFi1035Pos CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.StandardType.LieCore
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp CFSG.LieType.Steinberg.Adjoint
  CFSG.Timmesfeld
open CFSG.Open (StatedLieTag StatedLieAdmissible)

@[expose] def RetIotaSpec {τ : Tag} (β : Fin 6 → Fin τ.rank → ℤ)
    (ι : (Fin τ.rank → ℤ) → (Fin Tag.E6.rank → ℤ)) : Prop :=
  Set.BijOn ι (rootsOfFam β Set.univ) {γ' | IsRoot Tag.E6 γ'} ∧
  (∀ k : Fin 6, ι (β k) = Pi.single k 1) ∧
  (∀ γ ∈ rootsOfFam β Set.univ, ∑ k : Fin 6, ι γ k • β k = γ) ∧
  (∀ γ ∈ rootsOfFam β Set.univ, ι (-γ) = -ι γ) ∧
  (∀ γ ∈ rootsOfFam β Set.univ, ∀ δ ∈ rootsOfFam β Set.univ,
    CFSG.LieType.Steinberg.Adjoint.iform (ι γ) (ι δ) = CFSG.LieType.Steinberg.Adjoint.iform γ δ)

theorem rckRet_isRoot_E6_of_norm_two
    {u : Fin Tag.E6.rank → ℤ} (h : CFSG.LieType.Steinberg.Adjoint.iform u u = 2) :
    IsRoot Tag.E6 u :=
  rckIo_isRoot_E6_of_iform_self_eq_two h

theorem rckRet_iota
    {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {β : Fin 6 → Fin τ.rank → ℤ} (hroot : ∀ b, IsRoot τ (β b))
    (hnon : ∀ c d : Fin 6, c ≠ d → ¬ edgeE 6 c d → ¬ edgeE 6 d c →
      CFSG.LieType.Steinberg.Adjoint.iform (β c) (β d) = 0)
    (hedge : ∀ c d : Fin 6, edgeE 6 c d →
      CFSG.LieType.Steinberg.Adjoint.iform (β c) (β d) = -1) :
    ∃ ι : (Fin τ.rank → ℤ) → (Fin Tag.E6.rank → ℤ), RetIotaSpec β ι := by
  classical
  have hτsl : CFSG.HardMathSupport.Timmesfeld.LangTorus.SimplyLacedTag τ := by
    rcases hτ with h | h | h <;>
      simp [CFSG.HardMathSupport.Timmesfeld.LangTorus.SimplyLacedTag, h]
  let β' : Fin Tag.E6.rank → Fin τ.rank → ℤ := β
  have hnorm : ∀ b : Fin Tag.E6.rank, iform (β' b) (β' b) = 2 :=
    fun b => rckIo_iform_self_eq_two_sl hτsl (hroot b)
  have hgram : ∀ c d : Fin Tag.E6.rank, iform (β' c) (β' d) = Tag.E6.cartan c d := by
    intro c d
    by_cases hcd : c = d
    · subst hcd
      rw [hnorm c]
      exact (rckIo_cartan_diag_E6 c).symm
    · by_cases he : edgeE 6 c d
      · rw [hedge c d he]
        exact (rckIo_cartan_edge_E6 c d he).symm
      · by_cases he' : edgeE 6 d c
        · rw [iform_comm, hedge d c he']
          exact (rckIo_cartan_edge_E6 d c he').symm.trans (rckIo_cartan_comm_E6 c d).symm
        · rw [hnon c d hcd he he']
          exact (rckIo_cartan_nonedge_E6 c d hcd he he').symm
  let L : (Fin Tag.E6.rank → ℤ) → (Fin τ.rank → ℤ) := rckIo_L β'
  let ι : (Fin τ.rank → ℤ) → (Fin Tag.E6.rank → ℤ) := fun γ =>
    if h : ∃ v : Fin Tag.E6.rank → ℤ, L v = γ then Classical.choose h else 0
  have hLι : ∀ γ ∈ rootsOfFam β Set.univ, L (ι γ) = γ := by
    intro γ hγ
    have hex : ∃ v : Fin Tag.E6.rank → ℤ, L v = γ := by
      obtain ⟨-, n, -, hrep⟩ := hγ
      rcases hrep with hrep | hrep
      · refine ⟨fun k => (n k : ℤ), ?_⟩
        rw [hrep]
        rfl
      · refine ⟨fun k => -(n k : ℤ), ?_⟩
        rw [hrep]
        change rckIo_L β' (fun k => -(n k : ℤ)) = -∑ b : Fin 6, (n b : ℤ) • β b
        rw [show (fun k : Fin Tag.E6.rank => -(n k : ℤ)) =
            -(fun k : Fin Tag.E6.rank => (n k : ℤ)) from rfl,
          rckIo_L_neg]
        rfl
    show L (if h : ∃ v, L v = γ then Classical.choose h else 0) = γ
    rw [dif_pos hex]
    exact Classical.choose_spec hex
  have hsingle : ∀ k : Fin 6, ι (β k) = Pi.single k 1 := by
    intro k
    have hβk : β k ∈ rootsOfFam β Set.univ := (rckA4_mem_rootsOfFam β hroot k).1
    have h1 : L (ι (β k)) = β k := hLι (β k) hβk
    have h2 : L (Pi.single k 1) = β k := rckIo_L_single β' k
    exact rckIo_L_inj hgram (h1.trans h2.symm)
  have hsumL : ∀ γ ∈ rootsOfFam β Set.univ, rckIo_L β' (ι γ) = γ :=
    fun γ hγ => hLι γ hγ
  have hsum : ∀ γ ∈ rootsOfFam β Set.univ, ∑ k : Fin 6, ι γ k • β k = γ :=
    fun γ hγ => hsumL γ hγ
  have hneg : ∀ γ ∈ rootsOfFam β Set.univ, ι (-γ) = -ι γ := by
    intro γ hγ
    have hγmem : γ ∈ rootsOfFam β Set.univ := hγ
    obtain ⟨hr, n, hn, hrep⟩ := hγ
    have hγ' : -γ ∈ rootsOfFam β Set.univ := by
      refine ⟨IsRoot.neg hr, n, hn, ?_⟩
      rcases hrep with hrep | hrep
      · exact Or.inr (by rw [hrep])
      · exact Or.inl (by rw [hrep, neg_neg])
    have h1 : L (ι (-γ)) = -γ := hLι (-γ) hγ'
    have h2 : L (-(ι γ)) = -γ := by
      change rckIo_L β' (-(ι γ)) = -γ
      rw [rckIo_L_neg, hsumL γ hγmem]
    exact rckIo_L_inj hgram (h1.trans h2.symm)
  have hform : ∀ γ ∈ rootsOfFam β Set.univ, ∀ δ ∈ rootsOfFam β Set.univ,
      (CFSG.LieType.Steinberg.Adjoint.iform (τ := Tag.E6) (ι γ) (ι δ)) = iform γ δ :=
    fun γ hγ δ hδ => by
      have h := rckIo_L_iform hgram (ι γ) (ι δ)
      rw [hsumL γ hγ, hsumL δ hδ] at h
      exact h.symm
  have hmaps : Set.MapsTo ι (rootsOfFam β Set.univ) {γ' | IsRoot Tag.E6 γ'} := by
    intro γ hγ
    have h1 : iform (ι γ) (ι γ) = iform γ γ := hform γ hγ γ hγ
    have h2 : iform (ι γ) (ι γ) = 2 := by
      rw [h1, rckIo_iform_self_eq_two_sl hτsl hγ.1]
    exact rckIo_isRoot_E6_of_iform_self_eq_two h2
  have hinj : Set.InjOn ι (rootsOfFam β Set.univ) := by
    intro γ hγ δ hδ h
    calc γ = L (ι γ) := (hLι γ hγ).symm
      _ = L (ι δ) := by rw [h]
      _ = δ := hLι δ hδ
  have hsurj : Set.SurjOn ι (rootsOfFam β Set.univ) {γ' | IsRoot Tag.E6 γ'} := by
    intro γ' hγ'
    let γ : Fin τ.rank → ℤ := L γ'
    have hγnorm : iform γ γ = 2 := by
      have h := rckIo_L_iform hgram γ' γ'
      rw [rckIo_iform_self_eq_two_sl (Or.inr (Or.inl rfl)) hγ'] at h
      exact h
    have hγroot : IsRoot τ γ := by
      rcases hτ with hE6 | hE7 | hE8
      · subst hE6
        exact rckIo_isRoot_E6_of_iform_self_eq_two hγnorm
      · subst hE7
        exact ExcFramesHalf.isRoot_of_iform_self_eq_two (Or.inl rfl) hγnorm
      · subst hE8
        exact ExcFramesHalf.isRoot_of_iform_self_eq_two (Or.inr rfl) hγnorm
    have hγΨ : γ ∈ rootsOfFam β Set.univ := by
      refine ⟨hγroot, ?_⟩
      rcases IsRoot.height_pos_or_neg hγ' with hpos | hneg
      · have hnn : ∀ k, 0 ≤ γ' k := (IsRoot.height_pos_iff hγ').1 hpos
        refine ⟨fun k => (γ' k).toNat, fun b _ => Set.mem_univ b, Or.inl ?_⟩
        calc γ = ∑ k, γ' k • β k := rfl
          _ = ∑ k, ((γ' k).toNat : ℤ) • β k := by
                refine Finset.sum_congr rfl fun k _ => ?_
                rw [Int.toNat_of_nonneg (hnn k)]
      · have hnp : ∀ k, γ' k ≤ 0 := (IsRoot.height_neg_iff hγ').1 hneg
        refine ⟨fun k => (-γ' k).toNat, fun b _ => Set.mem_univ b, Or.inr ?_⟩
        calc γ = ∑ k, γ' k • β k := rfl
          _ = -∑ k, ((-γ' k).toNat : ℤ) • β k := by
                rw [← Finset.sum_neg_distrib]
                refine Finset.sum_congr rfl fun k _ => ?_
                have hk : (0 : ℤ) ≤ -γ' k := by have := hnp k; omega
                rw [Int.toNat_of_nonneg hk, ← neg_smul, neg_neg]
    refine ⟨γ, hγΨ, ?_⟩
    have h1 : L (ι γ) = L γ' := by
      change rckIo_L β' (ι γ) = rckIo_L β' γ'
      rw [hsumL γ hγΨ]
    exact rckIo_L_inj hgram h1
  exact ⟨ι, Set.BijOn.mk hmaps hinj hsurj, hsingle, hsum, hneg, hform⟩

theorem rckRet_weyl_transport
    {τ : Tag} {β : Fin 6 → Fin τ.rank → ℤ} {ι : (Fin τ.rank → ℤ) → (Fin Tag.E6.rank → ℤ)}
    (hι : RetIotaSpec β ι) {w : WeylGroup τ}
    (hw : w ∈ Subgroup.closure {s : WeylGroup τ | ∃ γ ∈ rootsOfFam β Set.univ,
      s = rootReflection γ}) :
    ∃ w' : WeylGroup Tag.E6, ∀ γ ∈ rootsOfFam β Set.univ,
      w • γ ∈ rootsOfFam β Set.univ ∧ w' • ι γ = ι (w • γ) := by
  classical
  obtain ⟨hbij, hsingle, hsum, hneg, hform⟩ := hι
  obtain ⟨hmaps, hinj, hsurj⟩ := hbij
  let βE : Fin Tag.E6.rank → Fin τ.rank → ℤ := β
  have hsumL : ∀ γ ∈ rootsOfFam β Set.univ, rckIo_L βE (ι γ) = γ :=
    fun γ hγ => hsum γ hγ
  have hnorm : ∀ {γ : Fin τ.rank → ℤ}, γ ∈ rootsOfFam β Set.univ → iform γ γ = 2 := by
    intro γ hγ
    have h1 : iform (ι γ) (ι γ) = iform γ γ := hform γ hγ γ hγ
    have h2 : iform (ι γ) (ι γ) = 2 :=
      rckIo_iform_self_eq_two_sl (Or.inr (Or.inl rfl)) (hmaps hγ)
    rw [h2] at h1
    exact h1.symm
  have hrefl : ∀ {γ₀ : Fin τ.rank → ℤ}, γ₀ ∈ rootsOfFam β Set.univ → ∀ v,
      rootReflection γ₀ • v = v - iform γ₀ v • γ₀ := by
    intro γ₀ hγ₀ v
    have hcp : corootPair γ₀ v = iform γ₀ v := by
      have := corootPair_mul hγ₀.1 v
      rw [hnorm hγ₀] at this
      omega
    rw [rootReflection_smul hγ₀.1, hcp]
  have hreflE6 : ∀ {γ₀ : Fin Tag.E6.rank → ℤ}, IsRoot Tag.E6 γ₀ → ∀ v,
      rootReflection γ₀ • v = v - iform γ₀ v • γ₀ := by
    intro γ₀ hγ₀ v
    have hcp : corootPair γ₀ v = iform γ₀ v := by
      have := corootPair_mul hγ₀ v
      rw [rckIo_iform_self_eq_two_sl (Or.inr (Or.inl rfl)) hγ₀] at this
      omega
    rw [rootReflection_smul hγ₀, hcp]
  have hgen : ∀ s ∈ ({s : WeylGroup τ | ∃ γ ∈ rootsOfFam β Set.univ,
      s = rootReflection γ}),
      ∃ w' : WeylGroup Tag.E6, ∀ γ ∈ rootsOfFam β Set.univ,
        s • γ ∈ rootsOfFam β Set.univ ∧ w' • ι γ = ι (s • γ) := by
    rintro s ⟨γ₀, hγ₀, rfl⟩
    have hιγ₀ : IsRoot Tag.E6 (ι γ₀) := hmaps hγ₀
    refine ⟨rootReflection (ι γ₀), ?_⟩
    intro γ hγ
    have hιγ : IsRoot Tag.E6 (ι γ) := hmaps hγ
    have hE6 : rootReflection (ι γ₀) • ι γ = ι γ - iform (ι γ₀) (ι γ) • ι γ₀ :=
      hreflE6 hιγ₀ (ι γ)
    have hrootE6 : IsRoot Tag.E6 (rootReflection (ι γ₀) • ι γ) :=
      IsRoot.smul hιγ (rootReflection (ι γ₀))
    obtain ⟨δ, hδ, hδι⟩ := hsurj hrootE6
    have hLrefl : rckIo_L βE (rootReflection (ι γ₀) • ι γ) = rootReflection γ₀ • γ := by
      rw [hE6, rckIo_L_sub, rckIo_L_smul, hsumL γ₀ hγ₀, hsumL γ hγ,
        hform γ₀ hγ₀ γ hγ, hrefl hγ₀ γ]
    have hδeq : rootReflection γ₀ • γ = δ := by
      rw [← hLrefl, ← hδι, hsumL δ hδ]
    refine ⟨?_, ?_⟩
    · rw [hδeq]; exact hδ
    · rw [hδeq]; exact hδι.symm
  have hP : ∃ w' : WeylGroup Tag.E6, ∀ γ ∈ rootsOfFam β Set.univ,
      w • γ ∈ rootsOfFam β Set.univ ∧ w' • ι γ = ι (w • γ) := by
    induction hw using Subgroup.closure_induction with
    | mem s hs => exact hgen s hs
    | one =>
        refine ⟨1, ?_⟩
        intro γ hγ
        exact ⟨by rw [one_smul]; exact hγ, by rw [one_smul, one_smul]⟩
    | mul y z hy hz ihy ihz =>
        obtain ⟨wy, hwy⟩ := ihy
        obtain ⟨wz, hwz⟩ := ihz
        refine ⟨wy * wz, ?_⟩
        intro γ hγ
        obtain ⟨hzγ, hzι⟩ := hwz γ hγ
        obtain ⟨hyzγ, hyι⟩ := hwy (z • γ) hzγ
        refine ⟨by rw [mul_smul]; exact hyzγ, ?_⟩
        simp only [mul_smul, hzι, hyι]
    | inv y hy ihy =>
        obtain ⟨wy, hwy⟩ := ihy
        refine ⟨wy⁻¹, ?_⟩
        intro γ hγ
        have hιγ : IsRoot Tag.E6 (ι γ) := hmaps hγ
        have hvroot : IsRoot Tag.E6 (wy⁻¹ • ι γ) := IsRoot.smul hιγ wy⁻¹
        obtain ⟨δ, hδ, hδι⟩ := hsurj hvroot
        have hyδ : y • δ ∈ rootsOfFam β Set.univ := (hwy δ hδ).1
        have hyιδ : wy • ι δ = ι (y • δ) := (hwy δ hδ).2
        have hγeq : y • δ = γ := by
          apply hinj hyδ hγ
          rw [← hyιδ, hδι, smul_inv_smul]
        refine ⟨?_, ?_⟩
        · rw [← hγeq, inv_smul_smul]
          exact hδ
        · rw [← hδι, ← hγeq, inv_smul_smul]
  exact hP

theorem rckRet_torus_val
    {τ : Tag} {β : Fin 6 → Fin τ.rank → ℤ} {ι : (Fin τ.rank → ℤ) → (Fin Tag.E6.rank → ℤ)}
    (hι : RetIotaSpec β ι) {b : ModGL τ GGL} (hb : b ∈ torusGroup τ GGL) :
    ∀ γ ∈ rootsOfFam β Set.univ,
      rckRootVal (rootDiagUnit Tag.E6 (fun k : Fin Tag.E6.rank => rckRootVal b (β k))) (ι γ) =
        rckRootVal b γ := by
  intro γ hγ
  obtain ⟨hbij, hsingle, hsum, hneg, hform⟩ := hι
  let βE : Fin Tag.E6.rank → Fin τ.rank → ℤ := β
  have hsumE : ∀ γ ∈ rootsOfFam β Set.univ, ∑ k : Fin Tag.E6.rank, ι γ k • βE k = γ :=
    fun γ hγ => hsum γ hγ
  set a : Fin Tag.E6.rank → GGLˣ := fun k => rckRootVal b (β k) with ha
  have hcoord : rckTorusCoord (rootDiagUnit Tag.E6 a) = a := rckIo_coord_rootDiagUnit a
  have hL : rckRootVal (rootDiagUnit Tag.E6 a) (ι γ) = rootChar a (ι γ) := by
    change rootChar (rckTorusCoord (rootDiagUnit Tag.E6 a)) (ι γ) = rootChar a (ι γ)
    rw [hcoord]
  have hR : rckRootVal b γ = rootChar (rckTorusCoord b) γ := rfl
  rw [hL, hR]
  conv_rhs => rw [← hsumE γ hγ]
  rw [rckIo_rootChar_sum (rckTorusCoord b) Finset.univ (fun k : Fin Tag.E6.rank => ι γ k) βE]
  conv_lhs => rw [show ι γ = ∑ k : Fin Tag.E6.rank,
      ι γ k • (Pi.single k 1 : Fin Tag.E6.rank → ℤ) from
    (rckIo_sum_single (ι γ)).symm]
  rw [rckIo_rootChar_sum a Finset.univ (fun k : Fin Tag.E6.rank => ι γ k)
    (fun k : Fin Tag.E6.rank => (Pi.single k 1 : Fin Tag.E6.rank → ℤ))]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [rckIo_rootChar_single]
  rfl

end CFSG.StandardType.RCKRP

end
