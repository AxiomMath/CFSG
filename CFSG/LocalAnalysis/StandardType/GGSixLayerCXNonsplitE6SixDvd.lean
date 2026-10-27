module

public import CFSG.RankThree.PartOne.KE6.Phi6Solvable
public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitE6SixCard
public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitE6Gen
public import CFSG.RankThree.PartOne.KE6.Phi3Solvable

public noncomputable section

namespace CFSG.RankThree.PartOne.KE6

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.RankThree.E6 CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.Classical2
open CFSG.RankThree.PartOne.KE (twistedTorus mem_twistedTorus adjEmb adjEmb_injective adjEmb_mem
  adjEmb_frobenius sigma_embedding_data subtorusImage mem_subtorusImage_iff twistedTorusOf
  twistedFixedPoints mem_twistedFixedPoints subtorusSigma subtorusSigma_le_twistedTorusOf)
open CFSG.Assembly (IsComponentOf)
open scoped Matrix Pointwise

namespace NonsplitLayers


theorem e6_six_components_dvd (K : Type) [Field K] [Finite K] {ℓ f : ℕ} [Fact ℓ.Prime]
    [CharP K ℓ] (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hpq : (p : ℤ) ∣ (Nat.card K : ℤ) ^ 2 - (Nat.card K : ℤ) + 1)
    (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L ℓ] :
    ∀ x : adjointGroup .E6 K, orderOf x = p →
      ∀ X : Subgroup (adjointGroup .E6 K),
        IsComponentOf X (Subgroup.centralizer ({x} : Set (adjointGroup .E6 K))) →
          p ∣ Nat.card X := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have : Fintype K := Fintype.ofFinite K
  set Fr : L →+* L := iterateFrobenius L ℓ f with hFrdef
  have hFr : ∀ c, Fr c = c ^ (ℓ ^ f) := fun c => iterateFrobenius_def ℓ f c
  have hFrK : ∀ c, Fr c = c ^ Nat.card K := fun c => by
    rw [hK]
    exact hFr c
  have hℓ : ℓ.Prime := Fact.out
  have hq0 : ((ℓ ^ f : ℕ) : L) = 0 := by
    rw [Nat.cast_pow, CharP.cast_eq_zero, zero_pow (by omega)]
  have hpq' : (p : ℤ) ∣ ((ℓ ^ f : ℕ) : ℤ) ^ 2 - ((ℓ ^ f : ℕ) : ℤ) + 1 := by
    rw [hK] at hpq
    exact hpq
  obtain ⟨hpL, ⟨ζ, hζ⟩, hr⟩ := phi6_prime_setup hq0 hp hpq'
  have hp7 : 7 ≤ p := (e6Six_data hp hp3 hpq').2.2.2.2.1
  have hordW : ¬ p ∣ Nat.card (WeylGroup Tag.E6) := by
    have : Fintype (WeylGroup Tag.E6) := Fintype.ofFinite _
    rw [(CFSG.RankThree.Chevalley.E6_weyl_length_polynomial).2]
    intro hd
    have h51840 : p ∣ 2 ^ 7 * 3 ^ 4 * 5 := by norm_num; exact hd
    rcases (Nat.Prime.dvd_mul hp).1 h51840 with h | h
    · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
      · exact absurd (Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h)) (by omega)
      · exact absurd (Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h)) (by omega)
    · exact absurd (Nat.le_of_dvd (by norm_num) h) (by omega)
  obtain ⟨g0, hg0C, hg0, hperf, hconj⟩ := e6_six_frame K hf hK hp hp3 hpq L
  intro x hx X hX
  have hpg : IsPGroup p (Subgroup.zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx, pow_one])
  obtain ⟨c, hc⟩ := hconj _ hpg
  have hh := hc x (Subgroup.mem_zpowers x)
  set ι : adjointGroup .E6 K →* ModGL .E6 L := adjEmb .E6 K L with hιdef
  set h : ModGL .E6 L := g0⁻¹ * ι (c * x * c⁻¹) * g0 with hhdef
  obtain ⟨b, hb⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup (mem_twistedTorus.1 hh).1
  have hb' : rootDiagUnit .E6 b = g0⁻¹ * ι (c * x * c⁻¹) * g0 := hb.symm
  have hordh : orderOf h = p := by
    have e1 : orderOf h = orderOf (ι (c * x * c⁻¹)) := by
      have := orderOf_injective (MulAut.conj g0⁻¹).toMonoidHom (MulAut.conj g0⁻¹).injective
        (ι (c * x * c⁻¹))
      rw [hhdef]
      simpa [MulAut.conj_apply] using this
    have e2 : orderOf (ι (c * x * c⁻¹)) = orderOf (c * x * c⁻¹) :=
      orderOf_injective ι adjEmb_injective _
    have e3 : orderOf (c * x * c⁻¹) = orderOf x := by
      have := orderOf_injective (MulAut.conj c).toMonoidHom (MulAut.conj c).injective x
      simpa [MulAut.conj_apply] using this
    rw [e1, e2, e3, hx]
  have hhp : h ^ p = 1 := hordh ▸ pow_orderOf_eq_one h
  have hh1 : h ≠ 1 := fun h1 => by
    rw [h1, orderOf_one] at hordh
    exact hp.one_lt.ne hordh
  have hhT : h ∈ phi6TorusTorsion L Fr p := ⟨hh, hhp⟩
  have htri : torusRootKernel h = ∅ ∨
      (∃ w : WeylGroup Tag.E6,
        (w • ·) '' torusRootKernel h = parabolicRoots Tag.E6 support13) ∨
      ∃ w : WeylGroup Tag.E6,
        (w • ·) '' torusRootKernel h = parabolicRoots Tag.E6 supportA2A2 := by
    have : NeZero p := ⟨hp.ne_zero⟩
    obtain ⟨⟨a, a'⟩, hab⟩ := (mem_phi6TorusTorsion_iff hFr hζ hr h).1 hhT
    have hab0 : (a, a') ≠ 0 := fun h0 => hh1 (by rw [← hab, h0, ofAdd_zero, map_one])
    have hker0 : torusRootKernel h = rootKernel (eisensteinColumn (((ℓ ^ f : ℕ)) : ZMod p) a a') := by
      rw [← hab]
      exact torusRootKernel_phi3TorsionHom hζ _ a a'
    rw [hker0]
    exact rootKernel_eisenstein_trichotomy hp3 hr hab0
  have hnC : phi6N L ∈ adjointGroup .E6 L := canonicalRep_mem_adjointGroup _ L _
  have hNorm : torusGroup .E6 L ⊔ rootSpan .E6 L (torusRootKernel h) ≤
      Subgroup.normalizer (rootSpan .E6 L (torusRootKernel h) : Set (ModGL .E6 L)) :=
    torusGroup_sup_rootSpan_le_normalizer fun α hα => hα.1
  have finish : ∀ (S : Set (Fin Tag.E6.rank → ℤ)) (hS : ∀ α ∈ S, IsRoot Tag.E6 α)
      (hSn : ∀ α ∈ S, -α ∈ S) (hSeq : S = torusRootKernel h) {ι' : Type}
      (P : ι' → Subgroup (ModGL .E6 L)) (hPfin : ∀ i, Finite (P i))
      (hPq : ∀ i, CFSG.IsQuasisimple (P i)) (hPQ : ∀ i, P i ≤ rootSpan .E6 L S)
      (hPR : ∀ i, P i ≤ twistedFixedPoints (phi6N L) (Units.map (entrywiseHom Fr)))
      (hPadj : ∀ i, P i ≤ adjointGroup .E6 L)
      (hPnorm : ∀ i, ∀ y ∈ torusGroup .E6 L ⊔ rootSpan .E6 L S,
        y ∈ twistedFixedPoints (phi6N L) (Units.map (entrywiseHom Fr)) →
        ∀ u ∈ P i, y * u * y⁻¹ ∈ P i)
      (hPcent : ∀ y ∈ torusGroup .E6 L ⊔ rootSpan .E6 L S,
        y ∈ twistedFixedPoints (phi6N L) (Units.map (entrywiseHom Fr)) →
        (∀ i, ∀ u ∈ P i, y * u = u * y) →
        y ∈ subtorusSigma (phi6N L) (Units.map (entrywiseHom Fr)) S)
      (hPdvd : ∀ i, p ∣ Nat.card ↥(P i)),
      p ∣ Nat.card X := by
    intro S hS hSn hSeq ι' P hPfin hPq hPQ hPR hPadj hPnorm hPcent hPdvd
    have hcS : c * x * c⁻¹ ∈ subtorusImage ι g0
        (subtorusSigma (phi6N L) (Units.map (entrywiseHom Fr)) S) := by
      rw [mem_subtorusImage_iff]
      refine Subgroup.mem_inf.2 ⟨hh, Subgroup.mem_centralizer_iff.2 fun g hg => ?_⟩
      have hle := rootSpan_le_centralizer (K := L) b (S := S) (by
        rw [hSeq, ← torusRootKernel_rootDiagUnit, hb])
      have h1 := Subgroup.mem_centralizer_singleton_iff.1 (hle hg)
      rw [hb'] at h1
      exact h1
    have hkerZ : ∀ a : Fin Tag.E6.rank → Lˣ, rootDiagUnit .E6 a = g0⁻¹ * ι (c * x * c⁻¹) * g0 →
        rootCharKernel a ⊆ S := fun a ha => by
      have : a = b := rootDiagUnit_injective (ha.trans hb'.symm)
      rw [this, hSeq, ← torusRootKernel_rootDiagUnit, hb]
    obtain ⟨ψ, hψinj, -, hψHQ, hψR, -, hPψ, -⟩ := sigma_embedding_data ι adjEmb_injective adjEmb_mem
      (Units.map (entrywiseHom Fr)) (adjEmb_frobenius Fr hFrK) (phi6N L) g0 hg0C hg0 hperf hp
      hordW hS hSn P hPfin hPq hPQ hPR hPadj hPnorm hPcent hx c hcS hkerZ
    exact CFSG.StandardType.E6Nonsplit.dvd_card_of_isComponentOf_of_layers ψ hψinj P hPψ hPq
      (fun i d u hu => hPnorm i (ψ d) (hψHQ d) (mem_twistedFixedPoints.2 (hψR d)) u hu)
      (Z := (twistedTorus (phi6N L) Fr : Set (ModGL .E6 L)))
      (fun a ha b hb => phi3_torusGroup_comm a (mem_twistedTorus.1 ha).1 b
        (mem_twistedTorus.1 hb).1)
      (fun d hd => subtorusSigma_le_twistedTorusOf _ _ _
        (hPcent (ψ d) (hψHQ d) (mem_twistedFixedPoints.2 (hψR d)) hd))
      hPdvd hX
  rcases htri with hreg | hA2 | hA2A2
  ·
    refine finish ∅ (fun α hα => hα.elim) (fun α hα => hα.elim) (by rw [hreg]) (ι' := Empty)
      (fun e => e.elim) (fun e => e.elim) (fun e => e.elim) (fun e => e.elim) (fun e => e.elim)
      (fun e => e.elim) (fun e => e.elim) (fun y hy hyR _ => ?_) (fun e => e.elim)
    have hspan : rootSpan Tag.E6 L (∅ : Set (Fin Tag.E6.rank → ℤ)) = ⊥ := by
      simp [rootSpan]
    rw [hspan, sup_bot_eq] at hy
    refine Subgroup.mem_inf.2 ⟨mem_twistedTorus.2 ⟨hy, hyR⟩, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    rw [hspan] at hg
    have : g = 1 := hg
    rw [this, one_mul, mul_one]
  ·
    have hrootneg : ∀ α ∈ torusRootKernel h, -α ∈ torusRootKernel h := fun α hα => by
      rw [hb, torusRootKernel_rootDiagUnit] at hα ⊢
      exact ⟨CFSG.LieType.Chevalley.IsRoot.neg hα.1, by rw [rootChar_neg', hα.2, inv_one]⟩
    obtain ⟨hfin, hqs, -, hC6, hcentQ⟩ := phi6_A2_case (K := K) hℓ hf hK hFr hp hp3 hpq' hh hordh
      hA2
    refine finish (torusRootKernel h) (fun α hα => hα.1) hrootneg rfl (ι' := Unit)
      (fun _ => phi6Qθ L Fr (torusRootKernel h)) (fun _ => hfin) (fun _ => hqs)
      (fun _ => inf_le_left) (fun _ => inf_le_right)
      (fun _ => inf_le_left.trans (rootSpan_le_adjointGroup L _))
      (fun _ y hy hyR u hu => phi6Qθ_conj_mem (hNorm hy) hyR hu) (fun y hy hyR hc => ?_)
      (fun _ => phi6_A2_layer_card hℓ hf hK hFr hp hp3 hpq' hh hordh hA2)
    have hyH : y ∈ torusGroup .E6 L := hC6 ⟨hy, Subgroup.mem_centralizer_iff.2 fun u hu =>
      (hc () u hu).symm⟩
    have hcent := hcentQ y hyH (fun u hu => hc () u hu)
    exact Subgroup.mem_inf.2 ⟨mem_twistedTorus.2 ⟨hyH, mem_twistedFixedPoints.1 hyR⟩,
      Subgroup.mem_centralizer_iff.2 fun g hg => (hcent g hg).symm⟩
  ·
    have hrootneg : ∀ α ∈ torusRootKernel h, -α ∈ torusRootKernel h := fun α hα => by
      rw [hb, torusRootKernel_rootDiagUnit] at hα ⊢
      exact ⟨CFSG.LieType.Chevalley.IsRoot.neg hα.1, by rw [rootChar_neg', hα.2, inv_one]⟩
    obtain ⟨hfin, hqs, -, -, -, hC6, hcentQ⟩ := phi6_A2A2_case (K := K) hℓ hf hK hFr hp hp3 hpq'
      hh hordh hA2A2
    refine finish (torusRootKernel h) (fun α hα => hα.1) hrootneg rfl (ι' := Unit)
      (fun _ => phi6P L Fr (torusRootKernel h)) (fun _ => hfin) (fun _ => hqs)
      (fun _ => (phi6P_le _).trans inf_le_left)
      (fun _ => (phi6P_le _).trans inf_le_right)
      (fun _ => (phi6P_le _).trans (inf_le_left.trans (rootSpan_le_adjointGroup L _)))
      (fun _ y hy hyR u hu => phi6P_conj_mem (hNorm hy) hyR hu) (fun y hy hyR hc => ?_)
      (fun _ => phi6_A2A2_layer_card hℓ hf hK hFr hp hp3 hpq' hh hordh hA2A2)
    have hyH : y ∈ torusGroup .E6 L := hC6 ⟨hy, Subgroup.mem_centralizer_iff.2 fun u hu =>
      (hc () u hu).symm⟩
    have hcent := hcentQ y hyH (fun u hu => hc () u hu)
    exact Subgroup.mem_inf.2 ⟨mem_twistedTorus.2 ⟨hyH, mem_twistedFixedPoints.1 hyR⟩,
      Subgroup.mem_centralizer_iff.2 fun g hg => (hcent g hg).symm⟩


end NonsplitLayers

end CFSG.RankThree.PartOne.KE6
