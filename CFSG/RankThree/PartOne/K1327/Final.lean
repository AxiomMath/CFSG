module

public import CFSG.RankThree.PartOne.K1327.Assemble
public import CFSG.RankThree.PartOne.K1320.L4CentT8
public import CFSG.RankThree.PartOne.K1320.L4Sl3
public import CFSG.RankThree.PartOne.U4F.Main

public section

namespace CFSG.RankThree.PartOne.K1327

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.S13K
open CFSG.RankThree.PartOne.KFU CFSG.RankThree.PartOne.KFQ CFSG.RankThree.PartOne.K1320
open CFSG.Assembly.LowTwoRank (StatedClassicalModel StatedProj StatedSL)
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

@[expose] def KF1327Q : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G) (f : ℕ),
    Sec12Hyp G p A c L E → Sec12Facts G p A c L E → Sec13Facts G p A c L E →
    ¬ Outcome152Five p E A (lieGenerated p E) → E = A → ¬ IsLThreeTypeAt p L →
    2 ≤ f → p ∣ 2 ^ f + 1 → StatedClassicalModel (L ⧸ Subgroup.center L) .PSL 4 2 f →
    Nonempty (reflectionGroup p E ≃* Multiplicative (ZMod 2) × Equiv.Perm (Fin 4)) →
    ∀ (r : ℕ) (R : Subgroup G), r.Prime → r ∣ 2 ^ f - 1 → Nat.card R = r → R ≤ L →
      (∀ x ∈ R, ∀ e ∈ E, x * e = e * x) →
      (∀ (y : G) (hy : y ∈ Subgroup.normalizer (E : Set G)),
        conjAut E y hy ∈ reflectionGroup p E → conjBy y R = R) →
      ∀ s s' : MulAut E, s ∈ reflectionSet p E → s ∈ torusImage E L →
        s' ∈ reflectionSet p E → s' ∈ torusImage E L → KFAt p E f s → KFAt p E f s' →
        s ≠ s' → s * s' = s' * s →
        R ≤ Subgroup.centralizer (kZero p E s : Set G) →
        R ≤ Subgroup.centralizer (kZero p E s' : Set G) →
      ∀ zs : MulAut E, zs ∈ reflectionSet p E → (∀ g ∈ torusImage E L, g * zs = zs * g) →
        zs ∉ torusImage E L → autMovedInG E zs = Subgroup.zpowers c → KFAt p E (2 * f) zs →
        kZero p E zs ≤ Subgroup.centralizer (kZero p E s : Set G) →
        kZero p E zs ≤ Subgroup.centralizer (kZero p E s' : Set G) → R ≤ kZero p E zs →
        StatedClassicalModel (↥(pElementSubgroup p (Subgroup.centralizer (R : Set G))) ⧸
          aschbacherSolvableCore p ↥(pElementSubgroup p (Subgroup.centralizer (R : Set G)))) .PSU 4 2 f

variable {G : Type} [Group G] [Finite G]

theorem kf1320L4'_holds_Q
    (hGA : CFSG.Open.GriessAllModelsStatement)
    (hS : SchreierFor InCatalog) (hRe : Sec13Reinst) (hCD : KFCommDistinct)
    (hTwo : TwoActionInputs) (hFull : K156.Full106Stmt) (hQ : KF1327Q) : KF1320L4' := by
  intro G _ _ p A c L E f h hF hF13 hT hEA hnL3 hf1 hpf hmodel hweyl
  have hp := h.prime
  have hp5 := Sec12Three.five_le h
  have hp2 : p ≠ 2 := by omega
  have hf2 : 2 ≤ f := by
    by_contra hlt
    have hf : f = 1 := by omega
    subst hf
    have hle := Nat.le_of_dvd (by norm_num) hpf
    omega
  have hcard : Nat.card E = p ^ 3 := by rw [hEA]; exact h.A_card
  have hcE : c ∈ E := h.A_le_E h.c_mem
  have hweyl' := hweyl
  obtain ⟨eX⟩ := hweyl
  obtain ⟨z, hz⟩ := exists_inverter h hF13 eX
  obtain ⟨B⟩ := exists_bridge h hF13 hcard eX
  obtain ⟨hZ, -, K, _, _, _, ⟨fr⟩⟩ := row8Frame_of hGA h hF hF13 hEA hf1 hpf hmodel
  obtain ⟨eL⟩ := exists_eL h hF hcard hz hf2 hmodel
  have h4q : 4 ≤ Nat.card K := by
    rw [fr.hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2
  obtain ⟨r, hr, hrf⟩ := Nat.exists_prime_and_dvd
    (show 2 ^ f - 1 ≠ 1 by
      have : 4 ≤ 2 ^ f := by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2
      omega)
  have hr2 : r ≠ 2 := prime_ne_two_of_dvd_two_pow_sub_one hf1 hrf
  have hrq : r ∣ Nat.card K - 1 := by rw [fr.hK]; exact hrf
  have hpq : p ∣ Nat.card K + 1 := by rw [fr.hK]; exact hpf
  have hM7 : ∀ g : ↥(M8 K), g ∈ (blk8M (K := K)).range →
      g ∈ Subgroup.centralizer (T8 p K : Set ↥(M8 K)) → g ^ r = 1 → g ∈ Rr K r :=
    fun g h1 h2 h3 => eq_of_mem_centralizer_T8 hp hp2 hpq hr hr2 hrq h1 h2 h3
  have hDist : ∀ t ∈ reflectionSet p E, KFLiftAt p E t → HasTwoSub E (kZero p E t) →
      fr.r₀ * t = t * fr.r₀ → DistinctCommute p fr.r₀ t :=
    fun t ht hLt hsp hcomm e I₁ I₂ hes het he1 hI₁ hI₂ hne hK₁ hK₂ =>
      hCD G p A c L E h hF hF13 hT fr.r₀ fr.mem₀ t ht (KFAt.toLiftAt fr.kf₀) hLt
        (Or.inr (Or.inr hsp)) hcomm e (Subgroup.mem_inf.2 ⟨hes, het⟩) he1 I₁ hI₁ I₂ hI₂ hne hK₁ hK₂
  obtain ⟨zs, hcore⟩ := fr.row8_core hS hRe h hF hF13 hT hEA hZ hcard B hz hf2
    hpf eL hr hrf hM7 hDist
  obtain ⟨hRL, hR0, hR0', hRE⟩ := fr.R_data h hF hF13 hZ hEA (Rm := Rr K r)
    (by rintro _ ⟨ζ, -, rfl⟩; exact ⟨ζ, rfl⟩)
  have hRcard : Nat.card (fr.lft (Rr K r)) = r := by
    rw [fr.lft_card hZ]
    exact rootsOfUnity_card hr hrq
  have hr0ne : fr.r₀ ≠ fr.r₀' := fr.r₀_ne h hF13 hZ
  obtain ⟨hcomm₀, -, -, -⟩ := fr.u_data h hF13 hZ eL
  have hQmodel := hQ G p A c L E f h hF hF13 hT hEA hnL3 hf2 hpf hmodel ⟨eX⟩ r
    (fr.lft (Rr K r)) hr hrf hRcard hRL hRE hcore.R_norm fr.r₀ fr.r₀' fr.mem₀ fr.mem₀L
    fr.mem₀' fr.mem₀'L fr.kf₀ fr.kf₀' hr0ne hcomm₀ hR0 hR0' zs hcore.mem hcore.comm hcore.notL
    hcore.mov hcore.kfAt hcore.cent₀ hcore.cent₀' hcore.R_le
  have hJmodel : StatedClassicalModel
      ↥(pElementSubgroup p (Subgroup.centralizer (fr.lft (Rr K r) : Set G))) .PSU 4 2 f :=
    statedModel_Jof hGA hS hRe hTwo hFull h hF hF13 hT hEA hf2 hpf hz B fr hZ hr hrq hcore hR0 hR0'
      hRE hQmodel
  have hK1eq : kZero p E fr.r₀ = fr.lft (slB K 0 1) := fr.kz₀ h hF13 hZ
  have hK1'eq : kZero p E fr.r₀' = fr.lft (slB K 2 3) := fr.kz₀' h hF13 hZ
  have hK1req : kZero p E fr.r₁ = fr.lft ((blk8M (K := K)).range) := fr.kz₁ h hF13 hZ
  obtain ⟨hl, hhl⟩ := fr.surj (q8 K (hcyc K))
  have hlft1 : conjBy (hl : G) (fr.lft (slB K 0 1)) = fr.lft (slB K 1 2) := by
    have := conjBy_liftM (ε := fr.ε) (ψ := q8 K) (slB K 0 1) (hcyc K) hl hhl
    rw [hcyc_conj_slB_zero_one] at this
    exact this
  have hlft2 : conjBy (hl : G) (fr.lft (slB K 2 3)) = fr.lft (slB K 0 3) := by
    have := conjBy_liftM (ε := fr.ε) (ψ := q8 K) (slB K 2 3) (hcyc K) hl hhl
    rw [hcyc_conj_slB_two_three] at this
    exact this
  have hlftR : conjBy (hl : G) (fr.lft (Rr K r)) ≤ fr.lft (slB K 0 1) ⊔ fr.lft (slB K 2 3) := by
    have := conjBy_liftM (ε := fr.ε) (ψ := q8 K) (Rr K r) (hcyc K) hl hhl
    have h2 : fr.lft ((Rr K r).map (MulAut.conj (hcyc K)).toMonoidHom) ≤
        fr.lft (slB K 0 1 ⊔ slB K 2 3) := liftM_mono (hcyc_conj_Rr_le r)
    rw [fr.lft_sup hZ] at h2
    exact this ▸ h2
  have hm1 : StatedClassicalModel ↥(kZero p E fr.r₀) .PSL 2 2 f := fr.kf₀.2.1
  have hm3 : StatedClassicalModel ↥(kZero p E zs) .PSL 2 2 (2 * f) := hcore.kfAt.2.1
  have hm2 : StatedClassicalModel ↥(fr.lft (slB K 1 2)) .PSL 2 2 f := by
    rw [← hlft1]
    exact (Equivariance.statedClassicalModel_conjBy_iff (hl : G) _).2 (hK1eq ▸ hm1)
  have hz3 : Subgroup.center ↥(kZero p E zs) = ⊥ := (KFAt.toLiftAt hcore.kfAt).2.1
  have hz1 : Subgroup.center ↥(kZero p E fr.r₀) = ⊥ := (KFAt.toLiftAt fr.kf₀).2.1
  obtain ⟨hCT, hnotle, hcFK3, hcFK2, hdisj, hdecK3, hdecK2⟩ :=
    fr.torus_facts h hF13 hZ hr hr2 hrq hcore.cent₀ hcore.cent₀' hcore.R_le hz3
  have hFe : IsElementaryAbelian r ↥(fr.lft (torusF K r)) :=
    isElementaryAbelian_liftM fr.surj (fr.inj hZ) (Row8Frame.q8_inj (K := K))
      (torusF_isElementaryAbelian hr)
  set J : Subgroup G := pElementSubgroup p (Subgroup.centralizer (fr.lft (Rr K r) : Set G)) with hJ
  have hK1J : kZero p E fr.r₀ ≤ J :=
    kZero_le_pElementSubgroup fr.r₀ (le_centralizer_symm hR0)
  have hK1'J : kZero p E fr.r₀' ≤ J :=
    kZero_le_pElementSubgroup fr.r₀' (le_centralizer_symm hR0')
  have hUeq : conjBy (hl : G) J = pElementSubgroup p
      (Subgroup.centralizer (conjBy (hl : G) (fr.lft (Rr K r)) : Set G)) := by
    rw [hJ, ← Equivariance.pElementSubgroup_conjBy, Equivariance.centralizer_conjBy]
  have hK3U : kZero p E zs ≤ conjBy (hl : G) J := by
    rw [hUeq]
    refine kZero_le_pElementSubgroup zs ?_
    have hc : kZero p E zs ≤ Subgroup.centralizer ((kZero p E fr.r₀ ⊔ kZero p E fr.r₀' :
        Subgroup G) : Set G) := fun x hx => mem_centralizer_sup.2 ⟨hcore.cent₀ hx, hcore.cent₀' hx⟩
    refine hc.trans (Subgroup.centralizer_le ?_)
    rw [hK1eq, hK1'eq]
    exact hlftR
  have hK2U : fr.lft (slB K 1 2) ≤ conjBy (hl : G) J := by
    rw [← hlft1, ← hK1eq]
    exact Subgroup.map_mono hK1J
  have hUmodel : StatedClassicalModel ↥(conjBy (hl : G) J) .PSU 4 2 f :=
    (Equivariance.statedClassicalModel_conjBy_iff (hl : G) J).2 hJmodel
  have hgen : kZero p E zs ⊔ fr.lft (slB K 1 2) = conjBy (hl : G) J :=
    U4F.kf1330Gen_holds G f r (conjBy (hl : G) J) (kZero p E zs) (fr.lft (slB K 1 2))
      (fr.lft (torusF K r)) hf2 hr hrf hUmodel hK3U hK2U hm3 hm2 hFe hcFK3 hcFK2 hdisj hdecK3
      hdecK2 hnotle
  have hLI : L ≤ lieGenerated p E := by
    have h1 : L = fr.lft (slB K 0 1 ⊔ (blk8M (K := K)).range) := by
      rw [← blkA_zero_range (K := K), blkA_zero_sup_blk8M h4q]
      exact (liftM_top (q8_surj (K := K))).symm
    rw [h1, fr.lft_sup hZ, ← hK1eq, ← hK1req]
    exact sup_le (le_sSup ⟨fr.r₀, fr.mem₀, (KFAt.toLiftAt fr.kf₀).isKt⟩)
      (le_sSup ⟨fr.r₁, fr.mem₁, (KFAt.toLiftAt fr.kf₁).isKt⟩)
  have hK1I : kZero p E fr.r₀ ≤ lieGenerated p E :=
    le_sSup ⟨fr.r₀, fr.mem₀, (KFAt.toLiftAt fr.kf₀).isKt⟩
  have hK3I : kZero p E zs ≤ lieGenerated p E :=
    le_sSup ⟨zs, hcore.mem, (KFAt.toLiftAt hcore.kfAt).isKt⟩
  have hK2I : fr.lft (slB K 1 2) ≤ lieGenerated p E := (fr.lft_le _).trans hLI
  have hFI : fr.lft (torusF K r) ≤ lieGenerated p E := (fr.lft_le _).trans hLI
  set I₀ : Subgroup G := kZero p E fr.r₀ ⊔ fr.lft (slB K 1 2) ⊔ kZero p E zs with hI₀
  have hK2I₀ : fr.lft (slB K 1 2) ≤ I₀ := le_sup_right.trans le_sup_left
  have hK3I₀ : kZero p E zs ≤ I₀ := le_sup_right
  have hK1I₀ : kZero p E fr.r₀ ≤ I₀ := le_sup_left.trans le_sup_left
  have hUI₀ : conjBy (hl : G) J ≤ I₀ := by
    rw [← hgen]
    exact sup_le hK3I₀ hK2I₀
  have hLI₀ : L ≤ I₀ := by
    have h1 : L = fr.lft (slB K 0 1 ⊔ slB K 1 2 ⊔ slB K 0 3) := by
      rw [slB_chain_sup h4q]
      exact (liftM_top (q8_surj (K := K))).symm
    rw [h1, fr.lft_sup hZ, fr.lft_sup hZ, ← hK1eq]
    refine sup_le (sup_le hK1I₀ hK2I₀) ?_
    rw [← hlft2, ← hK1'eq]
    exact (Subgroup.map_mono hK1'J).trans hUI₀
  have hhlI₀ : (hl : G) ∈ I₀ := hLI₀ hl.2
  have hJI₀ : J ≤ I₀ := by
    intro x hx
    have hxU : (hl : G) * x * (hl : G)⁻¹ ∈ conjBy (hl : G) J := by
      rw [Equivariance.mem_conjBy]
      have : (hl : G)⁻¹ * ((hl : G) * x * (hl : G)⁻¹) * (hl : G) = x := by group
      rw [this]
      exact hx
    have := I₀.mul_mem (I₀.mul_mem (I₀.inv_mem hhlI₀) (hUI₀ hxU)) hhlI₀
    simpa [mul_assoc] using this
  have hJnorm : ∀ (y : G) (hy : y ∈ Subgroup.normalizer (E : Set G)),
      conjAut E y hy ∈ reflectionGroup p E → conjBy y J = J := by
    intro y hy hyX
    rw [hJ, ← Equivariance.pElementSubgroup_conjBy, ← Equivariance.centralizer_conjBy,
      hcore.R_norm y hy hyX]
  have hIle : lieGenerated p E ≤ I₀ :=
    fr.lieGenerated_le h hF13 hcard B hcore hLI₀ hK3I₀ hJI₀ hK1J hJnorm
  have hI₀eq : kZero p E fr.r₀ ⊔ fr.lft (slB K 1 2) ⊔ kZero p E zs = lieGenerated p E :=
    le_antisymm (sup_le (sup_le hK1I hK2I) hK3I) hIle
  have hcomm13 : kZero p E fr.r₀ ≤ Subgroup.centralizer (kZero p E zs : Set G) ∧
      kZero p E fr.r₀ ⊓ kZero p E zs = ⊥ :=
    ⟨le_centralizer_symm hcore.cent₀,
      inf_eq_bot_of_centralizes' (le_centralizer_symm hcore.cent₀) hz1⟩
  have hL3 : CentrallyLThree f ↥(kZero p E fr.r₀ ⊔ fr.lft (slB K 1 2)) := by
    left
    have heq : kZero p E fr.r₀ ⊔ fr.lft (slB K 1 2) = fr.lft (slB K 0 1 ⊔ slB K 1 2) := by
      rw [hK1eq, fr.lft_sup hZ]
    obtain ⟨K', i1, i2, hK', ⟨e⟩⟩ := isSLModel_slB_pair (K := K) fr.hK
    exact ⟨K', i1, i2, hK', ⟨(MulEquiv.subgroupCongr heq).trans
      ((liftEquiv fr.surj (fr.inj hZ) (Row8Frame.q8_inj (K := K)) _).trans e)⟩⟩
  have hUmod : StatedClassicalModel ↥(fr.lft (slB K 1 2) ⊔ kZero p E zs) .PSU 4 2 f := by
    have : fr.lft (slB K 1 2) ⊔ kZero p E zs = conjBy (hl : G) J := by
      rw [sup_comm]; exact hgen
    exact Equivariance.statedClassicalModel_of_mulEquiv (MulEquiv.subgroupCongr this.symm) hUmodel
  exact ⟨r, fr.lft (torusF K r), kZero p E fr.r₀, fr.lft (slB K 1 2), kZero p E zs, hr, hrf, hFe,
    hFI, hK1I, hK2I, hK3I, hI₀eq, hm1, hm2, hm3, hcomm13, hL3, hUmod, hCT, hnotle⟩

end CFSG.RankThree.PartOne.K1327
