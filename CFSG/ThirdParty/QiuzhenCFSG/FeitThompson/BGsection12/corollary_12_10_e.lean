module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection12.corollary_12_10_d

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise

/-!
# corollary_12_10_e
-/

section Section12

variable {G : Type*} [Group G] [Finite G] [IsMinCE G]

omit [Finite G] [IsMinCE G] in
private lemma CFSG.mem_of_mem_subgroupOf {H K : Subgroup G} {x : K} (hx : x ∈ H.subgroupOf K) : (x : G) ∈ H :=
  (Subgroup.mem_subgroupOf (H := H) (K := K)).mp hx

set_option maxHeartbeats 800000

/-- Corollary 12.10(e). -/
public theorem CFSG.corollary_12_10_e
    {M E E₁₂ E₁ E₂ E₃ : Subgroup G} {x : G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hxM : x ∈ M) (hxne : x ≠ 1)
    (hxπ : subgroupPrimeSet (Subgroup.zpowers x) ⊆ section12Tau2Primes M)
    (hcent : elementCentralizerIn (section10Msigma M) x ≠ ⊥) :
    section9MaximalSubgroupsContaining (Subgroup.centralizer ({x} : Set G)) = {M} := by
  classical
  rcases hE with ⟨hcomp, hE12Hall, hE1Hall, hE2Hall, hE3Hall⟩
  have hEM : E ≤ M := hcomp.2.1
  have hE2E : E₂ ≤ E := (section12_E2_hall_in_E hE12Hall hE2Hall).1
  -- Solvability
  have hM_solv : IsSolvable M :=
    IsMinCE.proper_subgroups_solvable M (lt_top_iff_ne_top.2 hM.1)
  have hE_solv : IsSolvable E :=
    IsMinCE.proper_subgroups_solvable E (lt_top_iff_ne_top.2 (by
      intro hEtop; have htop_le_M : (⊤ : Subgroup G) ≤ M := by simpa [hEtop] using hEM
      exact hM.1 (top_le_iff.mp htop_le_M)))
  -- PUnit instances
  letI : MulDistribMulAction PUnit.{1} M :=
    { smul := fun _ m => m
      one_smul := by intro m; rfl
      mul_smul := by intro a b m; rfl
      smul_mul := by intro a m n; rfl
      smul_one := by intro a; rfl }
  letI : MulDistribMulAction PUnit.{1} E :=
    { smul := fun _ e => e
      one_smul := by intro e; rfl
      mul_smul := by intro a b e; rfl
      smul_mul := by intro a e f; rfl
      smul_one := by intro a; rfl }
  have hcopM : Nat.Coprime (Nat.card PUnit.{1}) (Nat.card M) := by simp
  have hcopE : Nat.Coprime (Nat.card PUnit.{1}) (Nat.card E) := by simp
  -- Basic facts
  have h_center_bot : Subgroup.center G = ⊥ := center_eq_bot_of_min_ce (G := G)
  have hMsigma_le_M : section10Msigma M ≤ M := by
    simpa [section10Msigma] using Subgroup.map_subtype_le (section10MsigmaSubgroup M)
  have hMσ_normal : (section10MsigmaSubgroup M).Normal := section10MsigmaSubgroup_normal M
  -- M_σ is Hall σ(M)-subgroup of M; E is Hall σ'(M)-subgroup of M
  have hMσ_hall : IsHallSubgroup (section10SigmaPrimes M) (section10MsigmaSubgroup M) :=
    (theorem_10_2_b hM).2
  have hE_hall : IsHallSubgroup ((section10SigmaPrimes M)ᶜ : Set Nat.Primes) (E.subgroupOf M) := by
    have hcomp' : (E.subgroupOf M).IsComplement' (section10MsigmaSubgroup M) :=
      section12_complement_to_msigma_isComplement' (M := M) (E := E) hcomp
    refine isHallSubgroup_of (G := M) (section10SigmaPrimes M)ᶜ (E.subgroupOf M) ?_ ?_
    · intro q hqE hqσ
      have hqNidx : q.val ∣ (section10MsigmaSubgroup M).index := by
        simpa [hcomp'.index_eq_card] using hqE
      exact (hMσ_hall.p_in_pi_of_p_dvd_index q hqNidx) hqσ
    · intro q hq_not_σc hqEidx
      have hqN : q.val ∣ Nat.card (section10MsigmaSubgroup M) := by
        simpa [hcomp'.symm.index_eq_card] using hqEidx
      have hqσ : q ∈ section10SigmaPrimes M := hMσ_hall.p_in_pi_of_p_dvd_card q hqN
      exact hq_not_σc hqσ
  -- E₂ is Hall τ₂(M)-subgroup of E, and E₂ is abelian
  rcases section12_E2_hall_in_E hE12Hall hE2Hall with ⟨hE2E', hHallE2⟩
  have hE2comm : IsMulCommutative E₂ :=
    (corollary_12_10_b hM ⟨hcomp, hE12Hall, hE1Hall, hE2Hall, hE3Hall⟩).1
  -- ============================================================
  -- STEP 1: Conjugate x into E
  -- ============================================================
  -- ⟨x⟩ is σ(M)'-subgroup of M
  have hcard_zx_sub : Nat.card ((Subgroup.zpowers x).subgroupOf M) = Nat.card (Subgroup.zpowers x) :=
    section12_card_subgroupOf_eq (Subgroup.zpowers_le.mpr hxM)
  have hx_pi_σ' : IsPiSubgroup (G := M) ((section10SigmaPrimes M)ᶜ : Set Nat.Primes)
      ((Subgroup.zpowers x).subgroupOf M) := by
    intro p hp
    rw [hcard_zx_sub] at hp
    have hp_mem : p ∈ subgroupPrimeSet (Subgroup.zpowers x) := by
      dsimp [subgroupPrimeSet]; exact hp
    have hpτ2 : p ∈ section12Tau2Primes M := hxπ hp_mem
    rcases (by simpa [section12Tau2Primes] using hpτ2) with ⟨hp_not_σ, _⟩
    simpa [Set.mem_compl_iff] using hp_not_σ
  have hxM_inv : IsInvariant PUnit.{1} M ((Subgroup.zpowers x).subgroupOf M) :=
    ⟨fun _ _ => ⟨id, id⟩⟩
  rcases proposition_1_5_b hM_solv hcopM ((section10SigmaPrimes M)ᶜ : Set Nat.Primes)
      ((Subgroup.zpowers x).subgroupOf M) hx_pi_σ' hxM_inv with ⟨H_M, hHMhall, _, hx_sub_HM⟩
  rcases exists_conj_eq_of_isHallSubgroup_of_solvable hM_solv hHMhall hE_hall with ⟨g₁ : M, hg₁⟩
  -- hg₁ : E.subgroupOf M = H_M.map (MulAut.conj g₁).toMonoidHom
  -- Now we construct x₁ = g₁ x g₁⁻¹ ∈ E
  let xM : M := ⟨x, hxM⟩
  have hxM_zpowers : xM ∈ ((Subgroup.zpowers x).subgroupOf M) := by
    rw [Subgroup.mem_subgroupOf]
    exact Subgroup.mem_zpowers x
  have hxM_HM : xM ∈ H_M := hx_sub_HM hxM_zpowers
  have hxM_conj_HM : (MulAut.conj g₁) xM ∈ H_M.map (MulAut.conj g₁).toMonoidHom :=
    Subgroup.mem_map.mpr ⟨xM, hxM_HM, rfl⟩
  have hxM_conj_Esub : (MulAut.conj g₁) xM ∈ E.subgroupOf M := by
    rw [hg₁]; exact hxM_conj_HM
  have hx₁_E_val : ((MulAut.conj g₁) xM : G) ∈ E :=
    mem_of_mem_subgroupOf hxM_conj_Esub
  -- Convert to the element x₁ : G
  set x₁ : G := (g₁ : G) * x * (g₁ : G)⁻¹
  have hx₁_val_eq : ((MulAut.conj g₁) xM : G) = x₁ := by
    dsimp [x₁, xM, MulAut.conj_apply]
  have hx₁_E : x₁ ∈ E := by simpa [hx₁_val_eq] using hx₁_E_val
  have hg₁_G_M : (g₁ : G) ∈ M := g₁.property
  have hx₁_M : x₁ ∈ M :=
    Subgroup.mul_mem M (Subgroup.mul_mem M hg₁_G_M hxM) (Subgroup.inv_mem M hg₁_G_M)
  have hx₁_ne : x₁ ≠ 1 := by
    intro h; apply hxne
    calc x = (g₁ : G)⁻¹ * x₁ * (g₁ : G) := by dsimp [x₁]; group
      _ = (g₁ : G)⁻¹ * 1 * (g₁ : G) := by rw [h]
      _ = 1 := by simp
  have hx₁_π : subgroupPrimeSet (Subgroup.zpowers x₁) ⊆ section12Tau2Primes M := by
    have h_order_eq : orderOf x₁ = orderOf x := by
      dsimp [x₁, MulAut.conj_apply]
      exact (MulAut.conj (g₁ : G)).orderOf_eq x
    have hcard_eq : Nat.card (Subgroup.zpowers x₁) = Nat.card (Subgroup.zpowers x) := by
      simp [Nat.card_zpowers, h_order_eq]
    intro p hp
    dsimp [subgroupPrimeSet] at hp ⊢
    rw [hcard_eq] at hp
    have hp' : p ∈ subgroupPrimeSet (Subgroup.zpowers x) := by dsimp [subgroupPrimeSet]; exact hp
    exact hxπ hp'
  have hcent₁_aux (y : G) (hy : y ∈ elementCentralizerIn (section10Msigma M) x) :
      (g₁ : G) * y * (g₁ : G)⁻¹ ∈ elementCentralizerIn (section10Msigma M) x₁ := by
    rw [elementCentralizerIn, Subgroup.mem_inf]
    rcases Subgroup.mem_inf.mp hy with ⟨hyMσ, hyCx⟩
    have hy_M : y ∈ M := hMsigma_le_M hyMσ
    refine ⟨?_, ?_⟩
    · have hyMσ_subgroup : (⟨y, hy_M⟩ : M) ∈ section10MsigmaSubgroup M := by
        rw [section10Msigma] at hyMσ
        rw [Subgroup.mem_map] at hyMσ
        rcases hyMσ with ⟨z, hz, hzval⟩
        have hz_eq : z = ⟨y, hy_M⟩ := Subtype.ext (by simpa using hzval)
        rw [← hz_eq]
        exact hz
      have hmem' : (⟨(g₁ : G), hg₁_G_M⟩ : M) * (⟨y, hy_M⟩ : M) *
          (⟨(g₁ : G), hg₁_G_M⟩ : M)⁻¹ ∈ section10MsigmaSubgroup M :=
        hMσ_normal.conj_mem _ hyMσ_subgroup _
      rw [section10Msigma, Subgroup.mem_map]
      refine ⟨(⟨(g₁ : G), hg₁_G_M⟩ : M) * (⟨y, hy_M⟩ : M) *
        (⟨(g₁ : G), hg₁_G_M⟩ : M)⁻¹, hmem', ?_⟩
      simp
    · rw [Subgroup.mem_centralizer_singleton_iff]
      calc
        (g₁ : G) * y * (g₁ : G)⁻¹ * x₁ =
            (g₁ : G) * y * (g₁ : G)⁻¹ * ((g₁ : G) * x * (g₁ : G)⁻¹) := rfl
        _ = (g₁ : G) * y * x * (g₁ : G)⁻¹ := by group
        _ = (g₁ : G) * (y * x) * (g₁ : G)⁻¹ := by group
        _ = (g₁ : G) * (x * y) * (g₁ : G)⁻¹ := by
          rw [Subgroup.mem_centralizer_singleton_iff.mp hyCx]
        _ = ((g₁ : G) * x * (g₁ : G)⁻¹) * ((g₁ : G) * y * (g₁ : G)⁻¹) := by group
        _ = x₁ * ((g₁ : G) * y * (g₁ : G)⁻¹) := rfl
  have hcent₁ : elementCentralizerIn (section10Msigma M) x₁ ≠ ⊥ := by
    intro hbot₁; apply hcent
    rw [Subgroup.eq_bot_iff_forall]
    intro y hy
    have h_conj := hcent₁_aux y hy
    rw [hbot₁] at h_conj
    have h_one : (g₁ : G) * y * (g₁ : G)⁻¹ = 1 := Subgroup.mem_bot.mp h_conj
    have hy_one : y = 1 := by
      calc
        y = (g₁ : G)⁻¹ * ((g₁ : G) * y * (g₁ : G)⁻¹) * (g₁ : G) := by group
        _ = (g₁ : G)⁻¹ * 1 * (g₁ : G) := by rw [h_one]
        _ = 1 := by simp
    simpa using hy_one
  -- ============================================================
  -- STEP 2: Conjugate x₁ into E₂
  -- ============================================================
  have hcard_zx₁_sub : Nat.card ((Subgroup.zpowers x₁).subgroupOf E) = Nat.card (Subgroup.zpowers x₁) :=
    section12_card_subgroupOf_eq (Subgroup.zpowers_le.mpr hx₁_E)
  have hx₁E_pi : IsPiSubgroup (G := E) (section12Tau2Primes M)
      ((Subgroup.zpowers x₁).subgroupOf E) := by
    intro p hp
    rw [hcard_zx₁_sub] at hp
    have hp_mem : p ∈ subgroupPrimeSet (Subgroup.zpowers x₁) := by
      dsimp [subgroupPrimeSet]; exact hp
    exact hx₁_π hp_mem
  have hx₁E_inv : IsInvariant PUnit.{1} E ((Subgroup.zpowers x₁).subgroupOf E) :=
    ⟨fun _ _ => ⟨id, id⟩⟩
  rcases proposition_1_5_b hE_solv hcopE (section12Tau2Primes M)
      ((Subgroup.zpowers x₁).subgroupOf E) hx₁E_pi hx₁E_inv with ⟨H_E, hHEhall, _, hx₁_sub_HE⟩
  rcases exists_conj_eq_of_isHallSubgroup_of_solvable hE_solv hHEhall hHallE2 with ⟨g₂ : E, hg₂⟩
  -- hg₂ : E₂.subgroupOf E = H_E.map (MulAut.conj g₂).toMonoidHom
  let x₁E : E := ⟨x₁, hx₁_E⟩
  have hx₁E_zpowers : x₁E ∈ ((Subgroup.zpowers x₁).subgroupOf E) := by
    rw [Subgroup.mem_subgroupOf]
    exact Subgroup.mem_zpowers x₁
  have hx₁E_HE : x₁E ∈ H_E := hx₁_sub_HE hx₁E_zpowers
  have hx₁E_conj_HE : (MulAut.conj g₂) x₁E ∈ H_E.map (MulAut.conj g₂).toMonoidHom :=
    Subgroup.mem_map.mpr ⟨x₁E, hx₁E_HE, rfl⟩
  have hx₁E_conj_E2sub : (MulAut.conj g₂) x₁E ∈ E₂.subgroupOf E := by
    rw [hg₂]; exact hx₁E_conj_HE
  have hx₂_E2_val : ((MulAut.conj g₂) x₁E : G) ∈ E₂ :=
    mem_of_mem_subgroupOf hx₁E_conj_E2sub
  set x₂ : G := (g₂ : G) * x₁ * (g₂ : G)⁻¹
  have hx₂_val_eq : ((MulAut.conj g₂) x₁E : G) = x₂ := by
    dsimp [x₂, x₁E, MulAut.conj_apply]
  have hx₂_E2 : x₂ ∈ E₂ := by simpa [hx₂_val_eq] using hx₂_E2_val
  have hg₂_G_M : (g₂ : G) ∈ M := hEM g₂.property
  have hx₂_M : x₂ ∈ M :=
    Subgroup.mul_mem M (Subgroup.mul_mem M hg₂_G_M hx₁_M) (Subgroup.inv_mem M hg₂_G_M)
  have hx₂_ne : x₂ ≠ 1 := by
    intro h; apply hx₁_ne
    calc x₁ = (g₂ : G)⁻¹ * x₂ * (g₂ : G) := by dsimp [x₂]; group
      _ = (g₂ : G)⁻¹ * 1 * (g₂ : G) := by rw [h]
      _ = 1 := by simp
  have hx₂_π : subgroupPrimeSet (Subgroup.zpowers x₂) ⊆ section12Tau2Primes M := by
    have h_order_eq : orderOf x₂ = orderOf x₁ := by
      dsimp [x₂, MulAut.conj_apply]
      exact (MulAut.conj (g₂ : G)).orderOf_eq x₁
    have hcard_eq : Nat.card (Subgroup.zpowers x₂) = Nat.card (Subgroup.zpowers x₁) := by
      simp [Nat.card_zpowers, h_order_eq]
    intro p hp
    dsimp [subgroupPrimeSet] at hp ⊢
    rw [hcard_eq] at hp
    have hp' : p ∈ subgroupPrimeSet (Subgroup.zpowers x₁) := by dsimp [subgroupPrimeSet]; exact hp
    exact hx₁_π hp'
  have hcent₂_aux (y : G) (hy : y ∈ elementCentralizerIn (section10Msigma M) x₁) :
      (g₂ : G) * y * (g₂ : G)⁻¹ ∈ elementCentralizerIn (section10Msigma M) x₂ := by
    rw [elementCentralizerIn, Subgroup.mem_inf]
    rcases Subgroup.mem_inf.mp hy with ⟨hyMσ, hyCx⟩
    have hy_M : y ∈ M := hMsigma_le_M hyMσ
    refine ⟨?_, ?_⟩
    · have hyMσ_subgroup : (⟨y, hy_M⟩ : M) ∈ section10MsigmaSubgroup M := by
        rw [section10Msigma] at hyMσ
        rw [Subgroup.mem_map] at hyMσ
        rcases hyMσ with ⟨z, hz, hzval⟩
        have hz_eq : z = ⟨y, hy_M⟩ := Subtype.ext (by simpa using hzval)
        rw [← hz_eq]
        exact hz
      have hmem' : (⟨(g₂ : G), hg₂_G_M⟩ : M) * (⟨y, hy_M⟩ : M) *
          (⟨(g₂ : G), hg₂_G_M⟩ : M)⁻¹ ∈ section10MsigmaSubgroup M :=
        hMσ_normal.conj_mem _ hyMσ_subgroup _
      rw [section10Msigma, Subgroup.mem_map]
      refine ⟨(⟨(g₂ : G), hg₂_G_M⟩ : M) * (⟨y, hy_M⟩ : M) *
        (⟨(g₂ : G), hg₂_G_M⟩ : M)⁻¹, hmem', ?_⟩
      simp
    · rw [Subgroup.mem_centralizer_singleton_iff]
      calc
        (g₂ : G) * y * (g₂ : G)⁻¹ * x₂ =
            (g₂ : G) * y * (g₂ : G)⁻¹ * ((g₂ : G) * x₁ * (g₂ : G)⁻¹) := rfl
        _ = (g₂ : G) * y * x₁ * (g₂ : G)⁻¹ := by group
        _ = (g₂ : G) * (y * x₁) * (g₂ : G)⁻¹ := by group
        _ = (g₂ : G) * (x₁ * y) * (g₂ : G)⁻¹ := by
          rw [Subgroup.mem_centralizer_singleton_iff.mp hyCx]
        _ = ((g₂ : G) * x₁ * (g₂ : G)⁻¹) * ((g₂ : G) * y * (g₂ : G)⁻¹) := by group
        _ = x₂ * ((g₂ : G) * y * (g₂ : G)⁻¹) := rfl
  have hcent₂ : elementCentralizerIn (section10Msigma M) x₂ ≠ ⊥ := by
    intro hbot₂; apply hcent₁
    rw [Subgroup.eq_bot_iff_forall]
    intro y hy
    have h_conj := hcent₂_aux y hy
    rw [hbot₂] at h_conj
    have h_one : (g₂ : G) * y * (g₂ : G)⁻¹ = 1 := Subgroup.mem_bot.mp h_conj
    have hy_one : y = 1 := by
      calc
        y = (g₂ : G)⁻¹ * ((g₂ : G) * y * (g₂ : G)⁻¹) * (g₂ : G) := by group
        _ = (g₂ : G)⁻¹ * 1 * (g₂ : G) := by rw [h_one]
        _ = 1 := by simp
    simpa using hy_one
  -- ============================================================
  -- E₂ is abelian, so E₂ ⊆ C_G(x₂)
  -- ============================================================
  have hE2_cent_x₂ : E₂ ≤ Subgroup.centralizer ({x₂} : Set G) := by
    intro y hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact setLike_mul_comm (s := E₂) hy hx₂_E2
  -- ============================================================
  -- STEP 3: Pick p ∈ τ₂(M) dividing |x₂|, find A ∈ E_p^2(E₂) ⊆ C_G(x₂)
  -- ============================================================
  have h_exists_prime : ∃ p : Nat.Primes, p.val ∣ orderOf x₂ := by
    by_cases h_order1 : orderOf x₂ = 1
    · exact False.elim (hx₂_ne (orderOf_eq_one_iff.mp h_order1))
    · have h_gt_one : 1 < orderOf x₂ :=
        Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨ne_of_gt (orderOf_pos x₂), h_order1⟩
      rcases Nat.exists_prime_and_dvd h_gt_one.ne' with ⟨p, hp_prime, hp_dvd⟩
      exact ⟨⟨p, hp_prime⟩, hp_dvd⟩
  rcases h_exists_prime with ⟨p, hp_order⟩
  have hp_card : p.val ∣ Nat.card (Subgroup.zpowers x₂) := by
    rw [Nat.card_zpowers]; exact hp_order
  have hp_mem : p ∈ subgroupPrimeSet (Subgroup.zpowers x₂) := by
    dsimp [subgroupPrimeSet]; exact hp_card
  have hpτ2 : p ∈ section12Tau2Primes M := hx₂_π hp_mem
  haveI : Fact p.val.Prime := ⟨p.2⟩
  -- Get A ∈ E_p^2(E) and conjugate into E₂
  rcases section12_exists_rankTwo_in_E_of_tau2 hM
      ⟨hcomp, hE12Hall, hE1Hall, hE2Hall, hE3Hall⟩ hpτ2 with ⟨A, hA⟩
  have hA_E : A ≤ E := section12_rankTwo_le hA
  rcases section12_rankTwo_elementary hA with ⟨hAcard, hAelem⟩
  haveI : IsElementaryAbelian p.val A := hAelem
  have hA_p : IsPGroup p.val A := IsElementaryAbelian.isPGroup p.val A
  -- A is a τ₂(M)-subgroup of E; conjugate into E₂
  have hcard_Asub : Nat.card (A.subgroupOf E) = Nat.card A :=
    section12_card_subgroupOf_eq hA_E
  have hA_pi : IsPiSubgroup (G := E) (section12Tau2Primes M) (A.subgroupOf E) := by
    intro q hq_dvd
    rw [hcard_Asub] at hq_dvd
    rw [hAcard] at hq_dvd
    have hq_dvd_p : q.val ∣ p.val := q.property.dvd_of_dvd_pow hq_dvd
    have hq_eq_p : q = p :=
      Subtype.ext ((Nat.prime_dvd_prime_iff_eq q.property p.property).mp hq_dvd_p)
    subst hq_eq_p; exact hpτ2
  have hA_inv : IsInvariant PUnit.{1} E (A.subgroupOf E) := ⟨fun _ _ => ⟨id, id⟩⟩
  rcases proposition_1_5_b hE_solv hcopE (section12Tau2Primes M)
      (A.subgroupOf E) hA_pi hA_inv with ⟨H_A, hHAhall, _, hA_sub_HA⟩
  rcases exists_conj_eq_of_isHallSubgroup_of_solvable hE_solv hHAhall hHallE2 with ⟨h : E, hh⟩
  set hG : G := (h : G)
  let A' : Subgroup G := A.map (MulAut.conj hG).toMonoidHom
  haveI : IsElementaryAbelian p.val A' :=
    IsElementaryAbelian.map (p := p.val) (A := A) (MulAut.conj hG).toMonoidHom
  have hA'_E2 : A' ≤ E₂ := by
    intro y hy
    rcases Subgroup.mem_map.mp hy with ⟨a, ha, rfl⟩
    let aE : E := ⟨a, hA_E ha⟩
    have haE_sub : aE ∈ A.subgroupOf E := by
      simpa [Subgroup.mem_subgroupOf] using ha
    have haE_HA : aE ∈ H_A := hA_sub_HA haE_sub
    have haE_conj_HE : (MulAut.conj h) aE ∈ H_A.map (MulAut.conj h).toMonoidHom :=
      Subgroup.mem_map.mpr ⟨aE, haE_HA, rfl⟩
    have haE_conj_E2sub : (MulAut.conj h) aE ∈ E₂.subgroupOf E := by
      rw [hh]; exact haE_conj_HE
    have haE_conj_E2 : ((MulAut.conj h) aE : G) ∈ E₂ :=
      mem_of_mem_subgroupOf haE_conj_E2sub
    have hval : ((MulAut.conj h) aE : G) = hG * a * hG⁻¹ := by
      dsimp [hG, aE, MulAut.conj_apply]
    simpa [hval] using haE_conj_E2
  have hA'_M : A' ∈ section12RankTwoElementaryAbelianIn p M := by
    have hA'_M_le : A' ≤ M := hA'_E2.trans (hE2E.trans hEM)
    have h_iso : A ≃* A' :=
      Subgroup.equivMapOfInjective A (MulAut.conj hG).toMonoidHom (MulAut.conj hG).injective
    have hA'card : Nat.card A' = p.val ^ 2 := by
      calc
        Nat.card A' = Nat.card A := Nat.card_congr h_iso.symm.toEquiv
        _ = p.val ^ 2 := hAcard
    have hA'_elem : A' ∈ elementaryAbelianSubgroupsOfRank p.val 2 G := ⟨hA'card, by infer_instance⟩
    exact ⟨hA'_M_le, hA'_elem⟩
  have hA'_cent_x₂ : A' ≤ Subgroup.centralizer ({x₂} : Set G) := by
    intro a ha
    have ha_E2 : a ∈ E₂ := hA'_E2 ha
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact setLike_mul_comm (s := E₂) ha_E2 hx₂_E2
  -- ============================================================
  -- STEP 4: Apply Theorem 12.5(e) to prove result for x₂
  -- ============================================================
  -- Helper: conjugation preserves maximality
  have h_maximal_conj {H : Subgroup G} {g : G} (hH : H ∈ section9MaximalSubgroups G) :
      H.map (MulAut.conj g).toMonoidHom ∈ section9MaximalSubgroups G :=
    ((MulAut.conj g : G ≃* G).mapSubgroup.isCoatom_iff H).mpr hH
  -- Prove the result for x₂
  have h_result_x₂ : section9MaximalSubgroupsContaining
      (Subgroup.centralizer ({x₂} : Set G)) = {M} := by
    ext L
    constructor
    · intro hL
      rcases hL with ⟨hLmax, hLcont⟩
      by_cases hLM : L = M
      · simp [hLM]
      · have hA'_L : A' ≤ L := hA'_cent_x₂.trans hLcont
        have hL_A' : L ∈ section9MaximalSubgroupsContaining A' := ⟨hLmax, hA'_L⟩
        have hMσ_inf_bot : section10Msigma M ⊓ L = ⊥ :=
          theorem_12_5_e hM hpτ2 hA'_M L hL_A' hLM
        have hcent₂_le : elementCentralizerIn (section10Msigma M) x₂ ≤
            section10Msigma M ⊓ L := by
          intro y hy
          rw [elementCentralizerIn, Subgroup.mem_inf] at hy
          rcases hy with ⟨hyMσ, hyCx₂⟩
          refine ⟨hyMσ, ?_⟩
          rw [Subgroup.mem_centralizer_singleton_iff] at hyCx₂
          exact hLcont (by rw [Subgroup.mem_centralizer_singleton_iff]; exact hyCx₂)
        have hbot : elementCentralizerIn (section10Msigma M) x₂ = ⊥ :=
          le_bot_iff.mp (hcent₂_le.trans (by rw [hMσ_inf_bot]))
        exact absurd hbot hcent₂
    · intro hL
      have hL_single : L ∈ ({M} : Set (Subgroup G)) := by simpa using hL
      have hL_eq_M : L = M := by simpa using hL_single
      rw [hL_eq_M]
      have h_cent_le_M : Subgroup.centralizer ({x₂} : Set G) ≤ M := by
        by_contra h_not
        have h_cent_proper : Subgroup.centralizer ({x₂} : Set G) ≠ ⊤ := by
          intro htop
          have hx₂_center : x₂ ∈ Subgroup.center G := by
            rw [Subgroup.mem_center_iff]
            intro g
            have : g ∈ Subgroup.centralizer ({x₂} : Set G) := by
              rw [htop]; exact Subgroup.mem_top g
            rw [Subgroup.mem_centralizer_singleton_iff] at this
            exact this
          rw [h_center_bot] at hx₂_center
          exact hx₂_ne (Subgroup.mem_bot.mp hx₂_center)
        rcases eq_top_or_exists_le_coatom (Subgroup.centralizer ({x₂} : Set G)) with
          h_top | ⟨N, hNcoatom, hNcent⟩
        · exact h_cent_proper h_top
        · have hNmax : N ∈ section9MaximalSubgroups G := hNcoatom
          by_cases hNM : N = M
          · exact h_not (hNcent.trans (by simp [hNM]))
          · have hA'_N : A' ≤ N := hA'_cent_x₂.trans hNcent
            have hN_A' : N ∈ section9MaximalSubgroupsContaining A' := ⟨hNmax, hA'_N⟩
            have hMσ_inf_bot : section10Msigma M ⊓ N = ⊥ :=
              theorem_12_5_e hM hpτ2 hA'_M N hN_A' hNM
            have hcent₂_le : elementCentralizerIn (section10Msigma M) x₂ ≤
                section10Msigma M ⊓ N := by
              intro y hy
              rw [elementCentralizerIn, Subgroup.mem_inf] at hy
              rcases hy with ⟨hyMσ, hyCx₂⟩
              refine ⟨hyMσ, ?_⟩
              rw [Subgroup.mem_centralizer_singleton_iff] at hyCx₂
              exact hNcent (by rw [Subgroup.mem_centralizer_singleton_iff]; exact hyCx₂)
            have hbot : elementCentralizerIn (section10Msigma M) x₂ = ⊥ :=
              le_bot_iff.mp (hcent₂_le.trans (by rw [hMσ_inf_bot]))
            exact absurd hbot hcent₂
      exact ⟨hM, h_cent_le_M⟩
  -- ============================================================
  -- STEP 5: Translate result from x₂ back to x
  -- ============================================================
  set gM : G := (g₂ : G) * (g₁ : G)
  have hgM_M : gM ∈ M := Subgroup.mul_mem M hg₂_G_M hg₁_G_M
  have hx₂_conj : x₂ = gM * x * gM⁻¹ := by
    dsimp [x₂, x₁, gM]; group
  have h_cent_conj : Subgroup.centralizer ({x₂} : Set G) =
      (Subgroup.centralizer ({x} : Set G)).map (MulAut.conj gM).toMonoidHom := by
    ext y
    constructor
    · intro hy
      rw [Subgroup.mem_map]
      refine ⟨gM⁻¹ * y * gM, ?_, ?_⟩
      · rw [Subgroup.mem_centralizer_singleton_iff]
        calc
          (gM⁻¹ * y * gM) * x = gM⁻¹ * (y * (gM * x * gM⁻¹)) * gM := by group
          _ = gM⁻¹ * ((gM * x * gM⁻¹) * y) * gM := by
            have hy_eq := Subgroup.mem_centralizer_singleton_iff.mp hy
            rw [hx₂_conj] at hy_eq
            rw [hy_eq]
          _ = x * (gM⁻¹ * y * gM) := by group
      · simp [MulAut.conj_apply, mul_assoc]
    · intro hy
      rw [Subgroup.mem_map] at hy
      rcases hy with ⟨z, hz, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc
        (gM * z * gM⁻¹) * x₂ = (gM * z * gM⁻¹) * (gM * x * gM⁻¹) := by rw [hx₂_conj]
        _ = gM * (z * x) * gM⁻¹ := by group
        _ = gM * (x * z) * gM⁻¹ := by rw [Subgroup.mem_centralizer_singleton_iff.mp hz]
        _ = (gM * x * gM⁻¹) * (gM * z * gM⁻¹) := by group
        _ = x₂ * (gM * z * gM⁻¹) := by rw [hx₂_conj]
  -- Now deduce the result for x
  ext L
  constructor
  · intro hL
    rcases hL with ⟨hLmax, hLcent⟩
    have hL_conj_max : L.map (MulAut.conj gM).toMonoidHom ∈ section9MaximalSubgroups G :=
      h_maximal_conj hLmax
    have h_cent_conj_le : Subgroup.centralizer ({x₂} : Set G) ≤
        L.map (MulAut.conj gM).toMonoidHom := by
      rw [h_cent_conj]; exact Subgroup.map_mono hLcent
    have hL_conj : L.map (MulAut.conj gM).toMonoidHom ∈
        section9MaximalSubgroupsContaining (Subgroup.centralizer ({x₂} : Set G)) :=
      ⟨hL_conj_max, h_cent_conj_le⟩
    rw [h_result_x₂] at hL_conj
    have hL_conj_eq_M : L.map (MulAut.conj gM).toMonoidHom = M := by simpa using hL_conj
    have hgM_inv_M : gM⁻¹ ∈ M := Subgroup.inv_mem M hgM_M
    have hL_eq_M : L = M := by
      calc
        L = (L.map (MulAut.conj gM).toMonoidHom).map (MulAut.conj gM⁻¹).toMonoidHom := by
          ext z; simp [Subgroup.mem_map, MulAut.conj_apply, mul_assoc]
        _ = M.map (MulAut.conj gM⁻¹).toMonoidHom := by rw [hL_conj_eq_M]
        _ = M := by
          ext z
          constructor
          · intro hz
            rcases Subgroup.mem_map.mp hz with ⟨w, hw, rfl⟩
            exact Subgroup.mul_mem M (Subgroup.mul_mem M hgM_inv_M hw) (Subgroup.inv_mem M hgM_inv_M)
          · intro hz
            apply Subgroup.mem_map.mpr
            refine ⟨gM * z * gM⁻¹, Subgroup.mul_mem M (Subgroup.mul_mem M hgM_M hz) hgM_inv_M, ?_⟩
            simp [mul_assoc]
    simp [hL_eq_M]
  · intro hL
    have hL_single : L ∈ ({M} : Set (Subgroup G)) := by simpa using hL
    have hL_eq_M : L = M := by simpa using hL_single
    rw [hL_eq_M]
    have hM_cent_x₂ : Subgroup.centralizer ({x₂} : Set G) ≤ M := by
      have hmem : M ∈ ({M} : Set (Subgroup G)) := by simp
      rw [← h_result_x₂] at hmem
      exact hmem.2
    have h_cent_x_le_M : Subgroup.centralizer ({x} : Set G) ≤ M := by
      -- From h_cent_conj: C_G(x₂) = gM · C_G(x) · gM⁻¹
      -- and hM_cent_x₂: C_G(x₂) ≤ M
      have h_map_le_M : (Subgroup.centralizer ({x} : Set G)).map (MulAut.conj gM).toMonoidHom ≤ M := by
        rw [← h_cent_conj]
        exact hM_cent_x₂
      intro z hz
      have hz_map : gM * z * gM⁻¹ ∈ (Subgroup.centralizer ({x} : Set G)).map (MulAut.conj gM).toMonoidHom :=
        Subgroup.mem_map.mpr ⟨z, hz, rfl⟩
      have hz_map_M : gM * z * gM⁻¹ ∈ M := h_map_le_M hz_map
      -- Conjugate back: z = gM⁻¹ * (gM * z * gM⁻¹) * gM ∈ M
      have hz_M : gM⁻¹ * (gM * z * gM⁻¹) * gM ∈ M := Subgroup.mul_mem M
        (Subgroup.mul_mem M (Subgroup.inv_mem M hgM_M) hz_map_M) hgM_M
      simpa [mul_assoc] using hz_M
    exact ⟨hM, h_cent_x_le_M⟩

end Section12
