module

public import CFSG.LocalAnalysis.StandardType.GGResE6DepLabels
public import CFSG.LocalAnalysis.StandardType.GGSlNsRootGenModel
public import CFSG.LocalAnalysis.StandardType.GGSixLSixSevenA3BstarRank
public import CFSG.LocalAnalysis.StandardType.GGSecFivePumpBstar

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Polynomial

private theorem eq_one_of_mem_center_of_pow_eq_one
    {d p : ℕ} {F X : Type} [Field F] [Finite F] [Group X]
    (φ : Matrix.SpecialLinearGroup (Fin d) F →* X) (hφ : Function.Surjective φ)
    (hker : ∀ x, φ x ∈ Subgroup.center X →
      x ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin d) F))
    (hd : 3 ≤ d) (hp : p.Prime) (hp2 : p ≠ 2) (hpF : p ∣ Nat.card F + 1)
    {z : X} (hz : z ∈ Subgroup.center X) (hzp : z ^ p = 1) : z = 1 := by
  have hSLperf : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin d) F) :=
    ⟨CFSG.ClassicalModels.specialLinear_commutator_eq_top_of_three_le hd⟩
  have hker' : φ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin d) F) :=
    fun x hx => hker x (by rw [MonoidHom.mem_ker.mp hx]; exact Subgroup.one_mem _)
  have hcomap : (Subgroup.center X).comap φ =
      Subgroup.center (Matrix.SpecialLinearGroup (Fin d) F) :=
    CFSG.LocalCores.comap_center_eq_of_perfect hSLperf φ hφ hker'
  obtain ⟨u, rfl⟩ := hφ z
  have hu : u ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin d) F) := by
    have h1 : u ∈ (Subgroup.center X).comap φ := by
      rw [Subgroup.mem_comap]
      exact hz
    rwa [hcomap] at h1
  have hdvd : orderOf u ∣ Nat.card F - 1 :=
    (Subgroup.orderOf_dvd_natCard (Subgroup.center (Matrix.SpecialLinearGroup (Fin d) F)) hu).trans
      (card_center_specialLinear_dvd (d := d) (K := F) (by omega))
  have huq : u ^ (Nat.card F - 1) = 1 := (orderOf_dvd_iff_pow_eq_one).mp hdvd
  have hzq : (φ u) ^ (Nat.card F - 1) = 1 := by rw [← map_pow, huq, map_one]
  have hpF' : ¬ p ∣ Nat.card F - 1 := by
    intro h1
    have hsub : Nat.card F + 1 - (Nat.card F - 1) = 2 := by
      have := Nat.card_pos (α := F)
      omega
    have h2 : p ∣ 2 := by
      rw [← hsub]
      exact Nat.dvd_sub hpF h1
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2)
  have hcop : Nat.Coprime p (Nat.card F - 1) := (hp.coprime_iff_not_dvd).mpr hpF'
  have hord : orderOf (φ u) ∣ 1 := by
    rw [← hcop.gcd_eq_one]
    exact Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hzp) (orderOf_dvd_of_pow_eq_one hzq)
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hord)

theorem exists_frame_of_linMinus
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G}
    {L D J X : Subgroup G} (hc : GGConfig p B Bs x L D J) {r f : ℕ} (hpq : p ∣ 2 ^ f + 1)
    (hmark : GGInnerDiagOnLabel (fun _ lab => lab = ⟨.A, r, f⟩) p Bs X)
    (h3 : ∀ hN : Bs ≤ Subgroup.normalizer (X : Set G), p ^ 3 ≤ Nat.card (ggGamma X hN).range) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2) (g : F[X])
      (_ : Fact (Irreducible g)) (hC : (CoordSL.rootMat g).det = 1)
      (hCp : CoordSL.rootMat g ^ p = 1) (s t : ℕ)
      (ε : Fin (r + 1) ≃ (Fin (CoordSL.rootPB g).dim × Fin s) ⊕ Fin t)
      (φ : Matrix.SpecialLinearGroup (Fin (r + 1)) F →* G),
      Nat.card F = 2 ^ f ∧ g ∣ cyclotomic p F ∧ AdjoinRoot.root g ^ p = 1 ∧
        φ.range = X ∧ φ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin (r + 1)) F) ∧
        3 ≤ s ∧ (CoordSL.frameHom φ 1 ε hC hCp).range = Bs ⊓ X ∧
        Bs ⊓ X ⊓ Subgroup.centralizer (X : Set G) = ⊥ ∧
        (Bs ⊓ X) ⊔ (Bs ⊓ Subgroup.centralizer (X : Set G)) = Bs := by
  classical
  obtain ⟨hXperf, lab, hlab, hraw⟩ := hmark
  have heq : lab = ⟨.A, r, f⟩ := by
    obtain ⟨R, _, I, F, hs, hna, θ, heq, -⟩ := largeEvenRawDatum_exists hraw
    exact heq
  subst lab
  dsimp only [LargeEvenRawDatum] at hraw
  obtain ⟨F, hField, hFinite, hF, hs, hna, θ, -, hN, hI⟩ := hraw
  let : Field F := hField
  let : Finite F := hFinite
  have : CharP F 2 := charP_two_of_card hF
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := hc.1.2.2.2.2.2.1.2.1
  have hpF : p ∣ Nat.card F + 1 := by rw [hF]; exact hpq
  have hpF' : ¬ p ∣ Nat.card F - 1 := by
    intro h1
    have hsub : Nat.card F + 1 - (Nat.card F - 1) = 2 := by
      have := Nat.card_pos (α := F)
      omega
    have h2 : p ∣ 2 := by
      rw [← hsub]
      exact Nat.dvd_sub hpF h1
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2)
  have hpF0 : (p : F) ≠ 0 := OrdPNS.natCast_ne_zero_of_charTwo hp hp2
  obtain ⟨g, hg, hgd⟩ := exists_irreducible_dvd_cyclotomic (K := F) hp
  have : Fact (Irreducible g) := ⟨hg⟩
  have hC : (CoordSL.rootMat g).det = 1 := CoordSL.det_rootMat hp hpF' hpF0 hgd
  have hCp : CoordSL.rootMat g ^ p = 1 := CoordSL.rootMat_pow_eq_one hp hpF0 hgd
  have hroot : AdjoinRoot.root g ^ p = 1 :=
    (CoordSL.root_isPrimitiveRoot hp hpF0 hgd).pow_eq_one
  have : NeZero p := ⟨hp.ne_zero⟩
  have hBs : IsElemAbelian p Bs := hc.2.1.2.1
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs :=
    hc.2.1.2.2.2
  have h3 : p ^ 3 ≤ Nat.card (ggGamma X hN).range := h3 hN
  have hBsI : ∀ (b : G) (hb : b ∈ Bs), ggLAut X θ ⟨b, hN hb⟩ ∈
      LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin (r + 1)) F)) Set.univ :=
    fun b hb => ggLAut_mem_of_induces X θ hN hI hb
  have hTB : GGTorusTBGroup p 3
      (LargeEvenProj (LargeEvenSLGroup (Fin (r + 1)) F))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin (r + 1)) F)) Set.univ)
      X (ggQuotHom θ) (ggGamma X hN).range :=
    ggTorusTBGroup_of_card hc (le_refl 3) hXperf θ hN hBsI h3
  have hTB' := hTB.mulEquiv (TypeA.recipeEquiv (r + 1) F)
    (fun _ hφ => TypeA.congr_recipeEquiv_mem hφ)
  obtain ⟨hψ, hker, hperf, hA, hAI, -, h3', hsc⟩ := hTB'
  obtain ⟨s, t, ε, φ', hφ's, hφ'c, hs3, hM⟩ :=
    SlNsRootGen.exists_isBlockTorusModel (p := p) (d := r + 1)
      hp hp2 hpF hgd hC hψ hker hperf hA hAI h3' hsc
  let φ : Matrix.SpecialLinearGroup (Fin (r + 1)) F →* G := X.subtype.comp φ'
  have hframe_eq : ∀ t : Fin s → ZMod p,
      (CoordSL.frameHom φ 1 ε hC hCp) (Multiplicative.ofAdd t) =
        X.subtype (φ' ((SlNsRootGen.torusSL ε hC hCp) (Multiplicative.ofAdd t))) := by
    intro t
    rw [CoordSL.frameHom_apply, SlNsRootGen.torusSL_apply]
    simp only [one_mul, inv_one, mul_one]
    rfl
  have hφrange : φ.range = X := by
    calc φ.range = (φ'.range).map X.subtype := MonoidHom.range_comp _ _
      _ = (⊤ : Subgroup ↥X).map X.subtype := by rw [MonoidHom.range_eq_top.mpr hφ's]
      _ = X := by rw [Subgroup.map_top, Subgroup.range_subtype]
  have hφker : φ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin (r + 1)) F) := by
    intro u hu
    apply hφ'c
    have h1 : X.subtype (φ' u) = (1 : G) := MonoidHom.mem_ker.mp hu
    have h2 : φ' u = 1 := Subgroup.subtype_injective X (by simpa using h1)
    rw [h2]
    exact Subgroup.one_mem _
  have hcard : (CoordSL.rootPB g).dim * s + t = r + 1 := by
    have h1 := Fintype.card_congr ε
    simp only [Fintype.card_fin, Fintype.card_sum, Fintype.card_prod] at h1
    omega
  have hdim : 0 < (CoordSL.rootPB g).dim := CoordSL.rootPB_dim_pos g
  have hd : 3 ≤ r + 1 := by
    have hdim1 : 1 ≤ (CoordSL.rootPB g).dim := hdim
    have h3le : 3 ≤ (CoordSL.rootPB g).dim * s := by
      simpa using Nat.mul_le_mul hdim1 hs3
    omega
  have hZ : Bs ⊓ X ⊓ Subgroup.centralizer (X : Set G) = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro z hz
    have hzBs : z ∈ Bs := (Subgroup.mem_inf.mp hz.1).1
    have hzX : z ∈ X := (Subgroup.mem_inf.mp hz.1).2
    have hzC : z ∈ Subgroup.centralizer (X : Set G) := hz.2
    have hzcenter : (⟨z, hzX⟩ : ↥X) ∈ Subgroup.center ↥X := by
      rw [Subgroup.mem_center_iff]
      intro x
      apply Subtype.ext
      exact Subgroup.mem_centralizer_iff.mp hzC (x : G) x.2
    have hzp : (⟨z, hzX⟩ : ↥X) ^ p = 1 :=
      Subtype.ext (by simpa using hBs.2 z hzBs)
    have h1 : (⟨z, hzX⟩ : ↥X) = 1 :=
      eq_one_of_mem_center_of_pow_eq_one φ' hφ's hφ'c hd hp hp2 hpF hzcenter hzp
    simpa using congrArg Subtype.val h1
  have hcentral_of_conj : ∀ (b : G) (hb : b ∈ Bs) (wX : ↥X),
      (ggGamma X hN) ⟨b, hb⟩ = MulAut.conj wX →
      (X.subtype wX : G) ∈ Bs →
      (X.subtype wX : G)⁻¹ * b ∈ Bs ⊓ Subgroup.centralizer (X : Set G) := by
    intro b hb wX hconj hwBs
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · exact Bs.mul_mem (Bs.inv_mem hwBs) hb
    · rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have hbx : b * x * b⁻¹ = (X.subtype wX : G) * x * (X.subtype wX : G)⁻¹ := by
        have h1 := congrArg (fun y : ↥X => (y : G))
          (congrArg (fun f : MulAut ↥X => f ⟨x, hx⟩) hconj)
        rw [ggGamma_coe, MulAut.conj_apply] at h1
        simpa using h1
      calc x * ((X.subtype wX : G)⁻¹ * b)
          = (X.subtype wX : G)⁻¹ *
              ((X.subtype wX : G) * x * (X.subtype wX : G)⁻¹) * b := by group
        _ = (X.subtype wX : G)⁻¹ * (b * x * b⁻¹) * b := by rw [← hbx]
        _ = ((X.subtype wX : G)⁻¹ * b) * x := by group
  have hframe_le : (CoordSL.frameHom φ 1 ε hC hCp).range ≤ Bs ⊓ X := by
    rintro _ ⟨a, rfl⟩
    let t : Fin s → ZMod p := Multiplicative.toAdd a
    have ha : a = Multiplicative.ofAdd t := rfl
    rw [ha, hframe_eq t]
    let wX : ↥X := φ' ((SlNsRootGen.torusSL ε hC hCp) (Multiplicative.ofAdd t))
    change (X.subtype wX : G) ∈ Bs ⊓ X
    refine Subgroup.mem_inf.mpr ⟨?_, wX.2⟩
    refine hSC (X.subtype wX) ?_ ?_
    · rw [Subgroup.mem_centralizer_iff]
      intro b hb
      obtain ⟨t', ht'⟩ := (SlNsRootGen.IsBlockTorusModel.mem_iff hM hCp).mp
        (show (ggGamma X hN) ⟨b, hb⟩ ∈ (ggGamma X hN).range from ⟨⟨b, hb⟩, rfl⟩)
      have hcomm : φ' ((SlNsRootGen.torusSL ε hC hCp) (Multiplicative.ofAdd t')) * wX =
          wX * φ' ((SlNsRootGen.torusSL ε hC hCp) (Multiplicative.ofAdd t')) := by
        have hτ : (SlNsRootGen.torusSL ε hC hCp) (Multiplicative.ofAdd t') *
            (SlNsRootGen.torusSL ε hC hCp) (Multiplicative.ofAdd t) =
            (SlNsRootGen.torusSL ε hC hCp) (Multiplicative.ofAdd t) *
            (SlNsRootGen.torusSL ε hC hCp) (Multiplicative.ofAdd t') := by
          simp_rw [SlNsRootGen.torusSL_apply]
          exact SLNS.nsSL_comm ε hC _ _
        simpa only [map_mul] using congrArg φ' hτ
      have hconj : φ' ((SlNsRootGen.torusSL ε hC hCp) (Multiplicative.ofAdd t')) *
          wX * (φ' ((SlNsRootGen.torusSL ε hC hCp) (Multiplicative.ofAdd t')))⁻¹ = wX := by
        rw [hcomm]
        group
      have hcoe := ggGamma_coe X hN ⟨b, hb⟩ wX
      rw [ht', MulAut.conj_apply, hconj] at hcoe
      have hcoe' : (X.subtype wX : G) = b * X.subtype wX * b⁻¹ := by simpa using hcoe
      calc b * X.subtype wX = (b * X.subtype wX * b⁻¹) * b := by group
        _ = X.subtype wX * b := by rw [← hcoe']
    · have hwp : wX ^ p = 1 := by
        have hτp : ((SlNsRootGen.torusSL ε hC hCp) (Multiplicative.ofAdd t)) ^ p = 1 := by
          rw [SlNsRootGen.torusSL_apply]
          exact SLNS.nsSL_pow_p ε hC hCp _
        change (φ' ((SlNsRootGen.torusSL ε hC hCp) (Multiplicative.ofAdd t))) ^ p = 1
        rw [← map_pow, hτp, map_one]
      rw [← map_pow, hwp, map_one]
  have hframe_ge : Bs ⊓ X ≤ (CoordSL.frameHom φ 1 ε hC hCp).range := by
    rintro b ⟨hbBs, hbX⟩
    obtain ⟨t, ht⟩ := (SlNsRootGen.IsBlockTorusModel.mem_iff hM hCp).mp
      (show (ggGamma X hN) ⟨b, hbBs⟩ ∈ (ggGamma X hN).range from ⟨⟨b, hbBs⟩, rfl⟩)
    let wX : ↥X := φ' ((SlNsRootGen.torusSL ε hC hCp) (Multiplicative.ofAdd t))
    have hwBs : (X.subtype wX : G) ∈ Bs := by
      have h := hframe_le (show (CoordSL.frameHom φ 1 ε hC hCp) (Multiplicative.ofAdd t) ∈
        (CoordSL.frameHom φ 1 ε hC hCp).range from ⟨Multiplicative.ofAdd t, rfl⟩)
      exact (Subgroup.mem_inf.mp (by rwa [hframe_eq t] at h)).1
    have hcw := hcentral_of_conj b hbBs wX ht hwBs
    have hcwX : (X.subtype wX : G)⁻¹ * b ∈ X := X.mul_mem (X.inv_mem wX.2) hbX
    have hmem : (X.subtype wX : G)⁻¹ * b ∈
        Bs ⊓ X ⊓ Subgroup.centralizer (X : Set G) :=
      Subgroup.mem_inf.mpr
        ⟨Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hcw).1, hcwX⟩,
          (Subgroup.mem_inf.mp hcw).2⟩
    have hzero : (X.subtype wX : G)⁻¹ * b = 1 := by
      have hbot : (X.subtype wX : G)⁻¹ * b ∈ (⊥ : Subgroup G) := by
        rw [← hZ]
        exact hmem
      exact Subgroup.mem_bot.mp hbot
    have hbw : b = X.subtype wX := by
      calc b = X.subtype wX * ((X.subtype wX : G)⁻¹ * b) := by group
        _ = X.subtype wX * 1 := by rw [hzero]
        _ = X.subtype wX := by group
    exact ⟨Multiplicative.ofAdd t, by rw [hframe_eq t, hbw]⟩
  have hframe_range : (CoordSL.frameHom φ 1 ε hC hCp).range = Bs ⊓ X :=
    le_antisymm hframe_le hframe_ge
  have hsup : (Bs ⊓ X) ⊔ (Bs ⊓ Subgroup.centralizer (X : Set G)) = Bs := by
    apply le_antisymm
    · exact sup_le inf_le_left inf_le_left
    · intro b hbBs
      obtain ⟨t, ht⟩ := (SlNsRootGen.IsBlockTorusModel.mem_iff hM hCp).mp
        (show (ggGamma X hN) ⟨b, hbBs⟩ ∈ (ggGamma X hN).range from ⟨⟨b, hbBs⟩, rfl⟩)
      let wX : ↥X := φ' ((SlNsRootGen.torusSL ε hC hCp) (Multiplicative.ofAdd t))
      have hwBs : (X.subtype wX : G) ∈ Bs := by
        have h := hframe_le (show (CoordSL.frameHom φ 1 ε hC hCp) (Multiplicative.ofAdd t) ∈
          (CoordSL.frameHom φ 1 ε hC hCp).range from ⟨Multiplicative.ofAdd t, rfl⟩)
        exact (Subgroup.mem_inf.mp (by rwa [hframe_eq t] at h)).1
      have hcw := hcentral_of_conj b hbBs wX ht hwBs
      have hb_eq : b = (X.subtype wX : G) * ((X.subtype wX : G)⁻¹ * b) := by group
      rw [hb_eq]
      exact Subgroup.mul_mem_sup (Subgroup.mem_inf.mpr ⟨hwBs, wX.2⟩) hcw
  exact ⟨F, hField, hFinite, inferInstance, g, inferInstance, hC, hCp, s, t, ε, φ,
    hF, hgd, hroot, hφrange, hφker, hs3, hframe_range, hZ, hsup⟩

theorem exists_frame_of_linMinus_side
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K X : Subgroup G} (hH : GGResHyp p B Bs x L D J y K)
    (hX : X = L ∨ X = K) {r f : ℕ} (hpq : p ∣ 2 ^ f + 1)
    (hmark : GGInnerDiagOnLabel (fun _ lab => lab = ⟨.A, r, f⟩) p Bs X) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2) (g : F[X])
      (_ : Fact (Irreducible g)) (hC : (CoordSL.rootMat g).det = 1)
      (hCp : CoordSL.rootMat g ^ p = 1) (s t : ℕ)
      (ε : Fin (r + 1) ≃ (Fin (CoordSL.rootPB g).dim × Fin s) ⊕ Fin t)
      (φ : Matrix.SpecialLinearGroup (Fin (r + 1)) F →* G),
      Nat.card F = 2 ^ f ∧ g ∣ cyclotomic p F ∧ AdjoinRoot.root g ^ p = 1 ∧
        φ.range = X ∧ φ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin (r + 1)) F) ∧
        3 ≤ s ∧ (CoordSL.frameHom φ 1 ε hC hCp).range = Bs ⊓ X ∧
        Bs ⊓ X ⊓ Subgroup.centralizer (X : Set G) = ⊥ ∧
        (Bs ⊓ X) ⊔ (Bs ⊓ Subgroup.centralizer (X : Set G)) = Bs :=
  exists_frame_of_linMinus hH.1 hpq hmark fun hN => GGResHyp.pow_three_le_card_range hH hX hN

theorem GGResHyp.exists_two_subgroup_of_linMinus_side
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K X : Subgroup G} (hH : GGResHyp p B Bs x L D J y K)
    (hX : X = L ∨ X = K) {r f : ℕ} (hpq : p ∣ 2 ^ f + 1)
    (hmark : GGInnerDiagOnLabel (fun _ lab => lab = ⟨.A, r, f⟩) p Bs X) :
    ∃ Q : Subgroup G, Q ≤ X ∧ Q ≠ ⊥ ∧ IsPGroup 2 Q ∧
      Bs ≤ Subgroup.normalizer (Q : Set G) := by
  classical
  obtain ⟨F, hF, hfin, hchar, g, hg, hC, hCp, s, t, ε, φ,
    -, -, -, hφ, hker, hs, hframe, -, hprod⟩ :=
    exists_frame_of_linMinus_side hH hX hpq hmark
  letI : Field F := hF
  letI : Finite F := hfin
  letI : CharP F 2 := hchar
  letI : Fact (Irreducible g) := hg
  obtain ⟨Q, hQR, hQ1, hQ2, hQN⟩ :=
    CoordSL.exists_isPGroup_two_le_range_normalized_by_frameHom hker 1 ε hC hCp (by omega)
  have hQX : Q ≤ X := hφ ▸ hQR
  have hBX : Bs ⊓ X ≤ Subgroup.normalizer (Q : Set G) := by
    rw [← hframe]
    exact hQN
  have hCX : Subgroup.centralizer (X : Set G) ≤ Subgroup.normalizer (Q : Set G) :=
    (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hQX)).trans
      (Subgroup.centralizer_le_normalizer _)
  refine ⟨Q, hQX, hQ1, hQ2, ?_⟩
  rw [← hprod]
  exact sup_le hBX (inf_le_right.trans hCX)

theorem GGResHyp.bstar_eq_of_linMinus_side
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K X : Subgroup G} (hH : GGResHyp p B Bs x L D J y K)
    (hX : X = L ∨ X = K) {r f : ℕ} (hpq : p ∣ 2 ^ f + 1)
    (hmark : GGInnerDiagOnLabel (fun _ lab => lab = ⟨.A, r, f⟩) p Bs X) : Bs = B := by
  obtain ⟨Q, -, hQ1, hQ2, hQN⟩ := hH.exists_two_subgroup_of_linMinus_side hX hpq hmark
  exact ggBstar_eq_of_normalizes_two hH.1 hQ2 hQ1 hQN

theorem GGResHyp.iOne_of_linMinus_side
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K X : Subgroup G} (hH : GGResHyp p B Bs x L D J y K)
    (hX : X = L ∨ X = K) {r f : ℕ} (hpq : p ∣ 2 ^ f + 1)
    (hmark : GGInnerDiagOnLabel (fun _ lab => lab = ⟨.A, r, f⟩) p Bs X) :
    Bs ⊓ Subgroup.centralizer (J : Set G) = D := by
  rw [hH.bstar_eq_of_linMinus_side hX hpq hmark]
  exact hH.1.2.2.1.2.2.2.2.2.2.symm

end CFSG.StandardType

end
