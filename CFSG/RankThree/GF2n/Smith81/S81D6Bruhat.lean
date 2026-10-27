module

public import CFSG.RankThree.GF2n.Smith81.S81D6Fe3b

public noncomputable section

namespace CFSG.RankThree.GF2n.Smith81.D6Spin

open CFSG.RankThree.GF2n.Smith81.E7Model CFSG.LieType.Steinberg.Minuscule
  CFSG.Blueprint.Chevalley


variable {K : Type} [Field K]

theorem presPiece_of_single {g : Module.End K (V K)}
    (h : ∀ a, g (Finsupp.single a 1) ∈ Piece K (pr a theta)) : PresPiece g := by
  intro i v hv
  have hsum : v = ∑ a ∈ v.support, v a • (Finsupp.single a (1 : K) : V K) := by
    conv_lhs => rw [← Finsupp.sum_single v]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finsupp.smul_single, smul_eq_mul, mul_one]
  rw [hsum, map_sum]
  rw [mem_Piece_iff]
  intro b hb
  rw [Finsupp.finset_sum_apply]
  refine Finset.sum_eq_zero fun a ha => ?_
  rw [map_smul, Finsupp.smul_apply]
  have hai : pr a theta = i := by
    by_contra hne
    exact (Finsupp.mem_support_iff.1 ha) (mem_Piece_iff.1 hv a hne)
  have hb' : pr b theta ≠ pr a theta := by rw [hai]; exact hb
  rw [mem_Piece_iff.1 (h a) b hb', smul_zero]

theorem tor_mem_GG {t : ↥(e7Data_valid.minGroup K)} (ht : t ∈ Tor K) :
    (t : (Module.End K (V K))ˣ) ∈ GG K := by
  have key : ∀ s : ↥(e7Data_valid.minGroup K), s ∈ Tor K →
      PresPiece ((s : (Module.End K (V K))ˣ) : Module.End K (V K)) := by
    intro s hs
    refine presPiece_of_single fun a => ?_
    obtain ⟨c, hc⟩ := endo_tor_single hs a
    have hc' : ((s : (Module.End K (V K))ˣ) : Module.End K (V K)) (Finsupp.single a 1) =
        c • Finsupp.single a 1 := hc
    rw [hc']
    rw [mem_Piece_iff]
    intro b hb
    have hne : a ≠ b := fun hab => hb (by rw [hab])
    rw [Finsupp.smul_apply, Finsupp.single_apply, if_neg hne, smul_zero]
  show PresPiece ((t : (Module.End K (V K))ˣ) : Module.End K (V K)) ∧
    PresPiece (((t : (Module.End K (V K))ˣ)⁻¹ : (Module.End K (V K))ˣ) : Module.End K (V K))
  exact ⟨key t ht, key t⁻¹ (inv_mem ht)⟩

theorem nW_mem_GG_of_mem_FF [CharP K 2] (w : W7 K)
    (hw : ((nW K w : ↥(e7Data_valid.minGroup K)) : (Module.End K (V K))ˣ) ∈ FF K) :
    ((nW K w : ↥(e7Data_valid.minGroup K)) : (Module.End K (V K))ˣ) ∈ GG K := by
  set n : (Module.End K (V K))ˣ := ((nW K w : ↥(e7Data_valid.minGroup K)) : (Module.End K (V K))ˣ)
    with hn
  have hFF : PresFil (n : Module.End K (V K)) ∧
      PresFil ((n⁻¹ : (Module.End K (V K))ˣ) : Module.End K (V K)) := hw
  have hmono : ∀ a : Fin e7Data.d, ∃ b : Fin e7Data.d,
      (n : Module.End K (V K)) (Finsupp.single a 1) = Finsupp.single b 1 :=
    endo_nW_single w
  choose π hπ using hmono
  have hinv : ∀ a, ((n⁻¹ : (Module.End K (V K))ˣ) : Module.End K (V K)) (Finsupp.single (π a) 1) =
      Finsupp.single a 1 := by
    intro a
    have h := congrArg (fun f : Module.End K (V K) => f (Finsupp.single a 1)) (Units.inv_mul n)
    simp only [Module.End.mul_apply, Module.End.one_apply] at h
    rw [hπ a] at h
    exact h
  have hdeg : ∀ a, pr (π a) theta = pr a theta := by
    intro a
    have h1 : pr a theta ≤ pr (π a) theta := by
      by_contra hlt
      push Not at hlt
      have hF := hFF.1 (pr a theta) _ (piece_mem_fil (single_mem_Piece (K := K) a))
      rw [hπ a] at hF
      have := mem_Fil_iff.1 hF (π a) hlt
      simp at this
    have h2 : pr (π a) theta ≤ pr a theta := by
      by_contra hlt
      push Not at hlt
      have hF := hFF.2 (pr (π a) theta) _ (piece_mem_fil (single_mem_Piece (K := K) (π a)))
      rw [hinv a] at hF
      have := mem_Fil_iff.1 hF a hlt
      simp at this
    omega
  have hinj : Function.Injective π := by
    intro a a' h
    have e : (n : Module.End K (V K)) (Finsupp.single a 1) =
        (n : Module.End K (V K)) (Finsupp.single a' 1) := by rw [hπ a, hπ a', h]
    have e' : (Finsupp.single a (1 : K) : V K) = Finsupp.single a' 1 := by
      have := congrArg (fun v : V K => ((n⁻¹ : (Module.End K (V K))ˣ) : Module.End K (V K)) v) e
      simpa only [← Module.End.mul_apply, Units.inv_mul, Module.End.one_apply] using this
    exact Finsupp.single_left_injective one_ne_zero e'
  have hsurj : Function.Surjective π := Finite.injective_iff_surjective.1 hinj
  have hP : PresPiece (n : Module.End K (V K)) := by
    refine presPiece_of_single fun a => ?_
    rw [hπ a, ← hdeg a]
    exact single_mem_Piece (π a)
  have hP' : PresPiece ((n⁻¹ : (Module.End K (V K))ˣ) : Module.End K (V K)) := by
    refine presPiece_of_single fun b => ?_
    obtain ⟨a, rfl⟩ := hsurj b
    rw [hinv a, hdeg a]
    exact single_mem_Piece a
  exact ⟨hP, hP'⟩

theorem Lam_bruhat [CharP K 2] {g : ↥(e7Data_valid.minGroup K)}
    (hg : (g : (Module.End K (V K))ˣ) ∈ Lam K) :
    ∃ w : W7 K, ∃ b₁ ∈ BorL K, ∃ b₂ ∈ BorL K, g = b₁ * nW K w * b₂ := by
  obtain ⟨w, c₁, hc₁, c₂, hc₂, hg'⟩ := bruhat_decomp g
  obtain ⟨u₁, hu₁, t₁, ht₁, rfl⟩ := bor_eq_mul hc₁
  obtain ⟨u₂, hu₂, t₂, ht₂, rfl⟩ := bor_eq_mul hc₂
  obtain ⟨ν₁, hν₁, s₁, hs₁, e₁⟩ := uni_decomp hu₁
  obtain ⟨ν₂, hν₂, s₂, hs₂, e₂⟩ := uni_decomp hu₂
  have hs₁E : s₁ ∈ EGrp K := UL_le_E hs₁
  have hs₂E : s₂ ∈ EGrp K := UL_le_E hs₂
  set σ₁ : ↥(e7Data_valid.minGroup K) := ⟨s₁, hs₁E⟩ with hσ₁
  set σ₂ : ↥(e7Data_valid.minGroup K) := ⟨s₂, hs₂E⟩ with hσ₂
  have hb₁ : σ₁ * t₁ ∈ BorL K :=
    mem_BorL_iff.2 ⟨σ₁, Subgroup.mem_comap.2 hs₁, t₁, ht₁, rfl⟩
  have hb₂ : σ₂ * t₂ ∈ BorL K :=
    mem_BorL_iff.2 ⟨σ₂, Subgroup.mem_comap.2 hs₂, t₂, ht₂, rfl⟩
  refine ⟨w, σ₁ * t₁, hb₁, σ₂ * t₂, hb₂, ?_⟩
  set N : (Module.End K (V K))ˣ := ((nW K w : ↥(e7Data_valid.minGroup K)) : (Module.End K (V K))ˣ)
    with hNdef
  set B₁ : (Module.End K (V K))ˣ := s₁ * (t₁ : (Module.End K (V K))ˣ) with hB₁def
  set B₂ : (Module.End K (V K))ˣ := s₂ * (t₂ : (Module.End K (V K))ˣ) with hB₂def
  have hB₁G : B₁ ∈ GG K := mul_mem (UL_le_GG hs₁) (tor_mem_GG ht₁)
  have hB₂G : B₂ ∈ GG K := mul_mem (UL_le_GG hs₂) (tor_mem_GG ht₂)
  have hgG : (g : (Module.End K (V K))ˣ) ∈ GG K := Lam_le_GG hg
  have hgu : (g : (Module.End K (V K))ˣ) = ν₁ * B₁ * N * (ν₂ * B₂) := by
    have h := congrArg Subtype.val hg'
    simp only [Subgroup.coe_mul] at h
    rw [h, e₁, e₂]
    simp only [hB₁def, hB₂def, hNdef, mul_assoc]
  set ν₂' : (Module.End K (V K))ˣ := B₂⁻¹ * ν₂ * B₂ with hν₂'def
  have hν₂' : ν₂' ∈ NN K := FF_conj_NN (GG_le_FF (inv_mem hB₂G)) hν₂
  set M : (Module.End K (V K))ˣ := B₁ * N * B₂ with hMdef
  have hgM : (g : (Module.End K (V K))ˣ) = ν₁ * M * ν₂' := by
    rw [hgu, hMdef, hν₂'def]
    group
  have hNFF : N ∈ FF K := by
    have e : N = B₁⁻¹ * ν₁⁻¹ * (g : (Module.End K (V K))ˣ) * ν₂'⁻¹ * B₂⁻¹ := by
      rw [hgM, hMdef]
      group
    rw [e]
    exact mul_mem (mul_mem (mul_mem (mul_mem (inv_mem (GG_le_FF hB₁G)) (inv_mem (NN_le_FF hν₁)))
      (GG_le_FF hgG)) (inv_mem (NN_le_FF hν₂'))) (inv_mem (GG_le_FF hB₂G))
  have hNG : N ∈ GG K := nW_mem_GG_of_mem_FF w hNFF
  have hMG : M ∈ GG K := mul_mem (mul_mem hB₁G hNG) hB₂G
  set ν : (Module.End K (V K))ˣ := ν₁ * (M * ν₂' * M⁻¹) with hνdef
  have hνN : ν ∈ NN K := mul_mem hν₁ (FF_conj_NN (GG_le_FF hMG) hν₂')
  have hνM : ν = (g : (Module.End K (V K))ˣ) * M⁻¹ := by
    rw [hgM, hνdef]
    group
  have hνG : ν ∈ GG K := by
    rw [hνM]
    exact mul_mem hgG (inv_mem hMG)
  have hν1 : ν = 1 := NN_inf_GG hνN hνG
  have hgMeq : (g : (Module.End K (V K))ˣ) = M := by
    have h := hνM
    rw [hν1] at h
    exact mul_inv_eq_one.1 h.symm
  apply Subtype.ext
  rw [hgMeq, hMdef, hB₁def, hB₂def]
  simp only [Subgroup.coe_mul, hNdef]
  rfl

end CFSG.RankThree.GF2n.Smith81.D6Spin
