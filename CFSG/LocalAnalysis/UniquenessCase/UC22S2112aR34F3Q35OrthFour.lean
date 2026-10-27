module

public import CFSG.ClassicalInvolution.SmallOrth.Orth3Block
import CFSG.GroupTheory.PermutingProducts
import CFSG.GroupTheory.ABGLocalTools.Basic
import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81X10OrthO2Ns

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

section PermGroup

open Subgroup
open scoped Pointwise

private theorem perm_coe_sup_eq_mul_of_mul_eq_mul {G : Type*} [Group G] {A B : Subgroup G}
    (hAB : (A : Set G) * B = B * A) :
    ((A ⊔ B : Subgroup G) : Set G) = (A : Set G) * B := by
  let S : Subgroup G :=
    { carrier := (A : Set G) * B
      one_mem' := ⟨1, A.one_mem, 1, B.one_mem, one_mul 1⟩
      mul_mem' := by
        rintro a b ⟨a₁, ha₁, b₁, hb₁, rfl⟩ ⟨a₂, ha₂, b₂, hb₂, rfl⟩
        have hba : b₁ * a₂ ∈ (B : Set G) * (A : Set G) := ⟨b₁, hb₁, a₂, ha₂, rfl⟩
        rw [← hAB] at hba
        obtain ⟨a₃, ha₃, b₃, hb₃, hba_eq⟩ := hba
        refine ⟨a₁ * a₃, A.mul_mem ha₁ ha₃, b₃ * b₂, B.mul_mem hb₃ hb₂, ?_⟩
        calc
          (a₁ * a₃) * (b₃ * b₂) = a₁ * (a₃ * b₃) * b₂ := by group
          _ = a₁ * (b₁ * a₂) * b₂ := by rw [show a₃ * b₃ = b₁ * a₂ from hba_eq]
          _ = (a₁ * b₁) * (a₂ * b₂) := by group
      inv_mem' := by
        rintro a ⟨x, hx, y, hy, rfl⟩
        have hyx : y⁻¹ * x⁻¹ ∈ (B : Set G) * (A : Set G) :=
          ⟨y⁻¹, B.inv_mem hy, x⁻¹, A.inv_mem hx, rfl⟩
        rw [← hAB] at hyx
        obtain ⟨x', hx', y', hy', hyx_eq⟩ := hyx
        exact ⟨x', hx', y', hy', by rw [hyx_eq]; group⟩ }
  have hle : A ⊔ B ≤ S :=
    sup_le (fun x hx => ⟨x, hx, 1, B.one_mem, mul_one x⟩)
      (fun y hy => ⟨1, A.one_mem, y, hy, one_mul y⟩)
  refine le_antisymm (fun g hg => hle hg) ?_
  rintro g ⟨x, hx, y, hy, rfl⟩
  exact (A ⊔ B).mul_mem (Subgroup.mem_sup_left hx) (Subgroup.mem_sup_right hy)

private lemma perm_card_eq_one_or_prime {X : Type*} [Group X] [Finite X] {r : ℕ} (hr : r.Prime)
    {B N : Subgroup X} (hBN : B ≤ N) (hB : IsPGroup r B) (hNr : ¬ r ^ 2 ∣ Nat.card N) :
    Nat.card B = 1 ∨ Nat.card B = r := by
  obtain ⟨k, hk⟩ := hB.exists_card_dvd_pow
  obtain ⟨j, _, hj⟩ := (Nat.dvd_prime_pow hr (m := k)).mp hk
  have hBdvd : Nat.card B ∣ Nat.card N := Subgroup.card_dvd_of_le hBN
  rw [hj] at hBdvd
  have hj1 : j ≤ 1 := by
    rcases Nat.lt_or_ge j 2 with h | h
    · omega
    · exfalso
      apply hNr
      exact (pow_dvd_pow r h).trans hBdvd
  rcases Nat.lt_or_ge j 1 with h | h
  · left
    rw [hj, show j = 0 by omega]
    norm_num
  · right
    rw [hj, show j = 1 by omega]
    norm_num

private lemma perm_card_mulAut_eq {X : Type*} [Group X] [Finite X] {r : ℕ} (hr : r.Prime)
    {B : Subgroup X} (hB : Nat.card B = r) : Nat.card (MulAut B) = r - 1 := by
  have hcyc : IsCyclic B := @isCyclic_of_prime_card B _ r ⟨hr⟩ hB
  rw [IsCyclic.card_mulAut B, hB, Nat.totient_prime hr]

private lemma perm_two_dvd_card_ker {S A : Type*} [Group S] [Finite S] [Group A] {r : ℕ}
    (hr8 : ¬ 8 ∣ r - 1) (hS : Nat.card S = 8) (hA : Nat.card A = r - 1) (φ : S →* A) :
    2 ∣ Nat.card φ.ker := by
  have hrange_dvd8 : Nat.card φ.range ∣ 8 := by
    have h := Subgroup.card_range_dvd φ
    rwa [hS] at h
  have hrange_dvdr : Nat.card φ.range ∣ r - 1 := by
    have h := Subgroup.card_subgroup_dvd_card φ.range
    rwa [hA] at h
  have hrange_ne8 : Nat.card φ.range ≠ 8 := fun h => hr8 (h ▸ hrange_dvdr)
  obtain ⟨k, hk3, hk⟩ :=
    (Nat.dvd_prime_pow (p := 2) Nat.prime_two (m := 3)).mp (by simpa using hrange_dvd8)
  have hrange_le4 : Nat.card φ.range ≤ 4 := by
    have hk' : Nat.card φ.range = 2 ^ k := hk
    rw [hk']
    have hk2 : k ≤ 2 := by
      rcases Nat.lt_or_ge k 3 with h | h
      · omega
      · exfalso
        apply hrange_ne8
        rw [hk', show k = 3 by omega]
        norm_num
    interval_cases k <;> norm_num
  have hker_mul : Nat.card φ.ker * Nat.card φ.range = 8 := by
    rw [Subgroup.card_ker_mul_card_range φ, hS]
  have hker_ne1 : Nat.card φ.ker ≠ 1 := by
    intro h
    apply hrange_ne8
    rw [h, one_mul] at hker_mul
    exact hker_mul
  have hker_dvd8 : Nat.card φ.ker ∣ 8 := ⟨Nat.card φ.range, hker_mul.symm⟩
  have hker2 : IsPGroup 2 φ.ker :=
    IsPGroup.of_card_dvd_pow (n := 3) (by simpa using hker_dvd8)
  rcases hker2.card_eq_or_dvd with h | h
  · exact absurd h hker_ne1
  · exact h

private theorem eq_bot_of_permutes_of_forall_involution {G : Type} [Group G] [Finite G]
    {r : ℕ} (hr : r.Prime) (hr5 : 5 ≤ r) (hr7 : r ≠ 7) (hr8 : ¬ 8 ∣ r - 1)
    {N B : Subgroup G} (P : Sylow 2 G) (hPN : (P : Subgroup G) ≤ normalizer (N : Set G))
    (hBN : B ≤ N) (hB : IsPGroup r B)
    (hperm : (B : Set G) * (P : Set G) = (P : Set G) * (B : Set G))
    (hN2 : (Nat.card N).factorization 2 = 3) (hNr : ¬ r ^ 2 ∣ Nat.card N)
    (hinv : ∀ t ∈ N, t ^ 2 = 1 → t ≠ 1 → ∀ b ∈ B, Commute t b → b = 1) :
    B = ⊥ := by
  classical
  let S : Subgroup G := (P : Subgroup G) ⊓ N
  have hPsyl : CFSG.ABGLocalTools.IsSylowOf 2 (P : Subgroup G) ⊤ := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff]
    exact ⟨le_top, P.isPGroup', by rw [Subgroup.relIndex_top_right]; exact P.not_dvd_index⟩
  have hPNsup : (P : Subgroup G) ⊔ N ≤ Subgroup.normalizer (N : Set G) :=
    sup_le hPN (Subgroup.le_normalizer (H := N))
  have hSsyl : CFSG.ABGLocalTools.IsSylowOf 2 S N :=
    (hPsyl.of_le le_sup_left le_top).inf_of_le_normalizer le_sup_right hPNsup
  have hScard : Nat.card S = 8 := by
    have h := hSsyl.card_eq
    rw [hN2] at h
    norm_num at h
    exact h
  have hSN : S ≤ N := hSsyl.le
  rcases perm_card_eq_one_or_prime hr hBN hB hNr with hB1 | hBr
  · exact Subgroup.eq_bot_of_card_eq B hB1
  have hpermS : (B : Set G) * (S : Set G) = (S : Set G) * (B : Set G) :=
    CFSG.GroupTheory.permutes_inf_of_le hBN hperm
  let T : Subgroup G := B ⊔ S
  have hBT : B ≤ T := le_sup_left
  have hST : S ≤ T := le_sup_right
  have hTcoe : (T : Set G) = (B : Set G) * (S : Set G) :=
    perm_coe_sup_eq_mul_of_mul_eq_mul hpermS
  have hTcard_le : Nat.card T ≤ 8 * r := by
    have h1 : Nat.card T ≤ Nat.card B * Nat.card S := by
      calc Nat.card T = Nat.card ((T : Subgroup G) : Set G) := rfl
        _ = Nat.card ((B : Set G) * (S : Set G)) := by rw [hTcoe]
        _ ≤ Nat.card (B : Set G) * Nat.card (S : Set G) := Set.natCard_mul_le
        _ = Nat.card B * Nat.card S := rfl
    rw [hBr, hScard] at h1
    linarith
  have h8dvd : 8 ∣ Nat.card T := by
    have h := Subgroup.card_dvd_of_le hST
    rwa [hScard] at h
  have hrdvd : r ∣ Nat.card T := by
    have h := Subgroup.card_dvd_of_le hBT
    rwa [hBr] at h
  have hnot8 : ¬ r ∣ 8 := by
    intro h
    have h23 : r ∣ 2 ^ 3 := by simpa using h
    have h2 : r ∣ 2 := hr.dvd_of_dvd_pow h23
    have h3 : r = 2 := (Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp h2
    omega
  have h8r_dvd : 8 * r ∣ Nat.card T := by
    have hcop : Nat.Coprime 8 r := by
      have h := hr.coprime_pow_of_not_dvd (m := 1) hnot8
      rwa [pow_one] at h
    exact hcop.mul_dvd_of_dvd_of_dvd h8dvd hrdvd
  have hTcard : Nat.card T = 8 * r :=
    Nat.le_antisymm hTcard_le (Nat.le_of_dvd Nat.card_pos h8r_dvd)
  have hBsub : IsPGroup r (B.subgroupOf T) := hB.comap_subtype (K := T)
  have hBindex : (B.subgroupOf T).index = 8 := by
    have h := Subgroup.card_mul_index (B.subgroupOf T)
    have hBcard' : Nat.card (B.subgroupOf T) = r := by
      rw [← hBr]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBT).toEquiv
    rw [hBcard', hTcard, mul_comm 8 r] at h
    exact Nat.eq_of_mul_eq_mul_left hr.pos h
  have hnotdvd : ¬ r ∣ (B.subgroupOf T).index := by
    rw [hBindex]
    exact hnot8
  let Bsil : Sylow r T :=
    @IsPGroup.toSylow r T _ ⟨hr⟩ (B.subgroupOf T) hBsub hnotdvd
  have hBsil_coe : (Bsil : Subgroup T) = B.subgroupOf T :=
    @IsPGroup.toSylow_coe r T _ ⟨hr⟩ (B.subgroupOf T) hBsub hnotdvd
  have hdvd : Nat.card (Sylow r T) ∣ 8 := by
    have h := @Sylow.card_dvd_index r T _ ⟨hr⟩ _ Bsil
    rwa [hBsil_coe, hBindex] at h
  have hmod : Nat.card (Sylow r T) ≡ 1 [MOD r] :=
    @card_sylow_modEq_one r T _ ⟨hr⟩ _
  have huniq : Nat.card (Sylow r T) = 1 := by
    obtain ⟨k, hk3, hk⟩ :=
      (Nat.dvd_prime_pow (p := 2) Nat.prime_two (m := 3)).mp (by simpa using hdvd)
    have hk' : Nat.card (Sylow r T) = 2 ^ k := hk
    rw [hk'] at hmod ⊢
    interval_cases k
    · norm_num
    · exfalso
      have h1 : r ∣ 1 := hmod.symm.dvd'
      have h2 : r = 1 := Nat.dvd_one.mp h1
      omega
    · exfalso
      have h1 : r ∣ 3 := hmod.symm.dvd'
      rcases (Nat.dvd_prime (by decide : Nat.Prime 3)).mp h1 with h1 | h1 <;> omega
    · exfalso
      have h1 : r ∣ 7 := hmod.symm.dvd'
      rcases (Nat.dvd_prime (by decide : Nat.Prime 7)).mp h1 with h1 | h1 <;> omega
  have hsub : Subsingleton (Sylow r T) :=
    Finite.card_le_one_iff_subsingleton.mp (by omega)
  have hBnormal : (B.subgroupOf T).Normal := by
    have h := @Sylow.normal_of_subsingleton T _ r hsub Bsil
    rwa [hBsil_coe] at h
  have hTnorm : T ≤ Subgroup.normalizer (B : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hBT).mp hBnormal
  have hSnorm : S ≤ Subgroup.normalizer (B : Set G) := le_trans hST hTnorm
  let φ : S →* MulAut B :=
    (Subgroup.normalizerMonoidHom B).comp (Subgroup.inclusion hSnorm)
  have hMulAut : Nat.card (MulAut B) = r - 1 := perm_card_mulAut_eq hr hBr
  have h2dvd : 2 ∣ Nat.card φ.ker := perm_two_dvd_card_ker hr8 hScard hMulAut φ
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := φ.ker) 2 h2dvd
  let tS : S := x
  have htker : φ tS = 1 := MonoidHom.mem_ker.mp x.2
  have htS2 : orderOf tS = 2 := by
    rw [Subgroup.orderOf_coe, hx]
  have htS_sq : tS ^ 2 = 1 := by
    have h := pow_orderOf_eq_one tS
    rwa [htS2] at h
  have ht_sq : (tS : G) ^ 2 = 1 := by
    simpa using congrArg (fun y : S => (y : G)) htS_sq
  have htG2 : orderOf (tS : G) = 2 := by
    rw [Subgroup.orderOf_coe, htS2]
  have htne : (tS : G) ≠ 1 := by
    intro h
    rw [h, orderOf_one] at htG2
    omega
  have hcomm : ∀ b ∈ B, Commute (tS : G) b := by
    intro b hb
    have hfix : (Subgroup.normalizerMonoidHom B (Subgroup.inclusion hSnorm tS)) ⟨b, hb⟩ =
        ⟨b, hb⟩ := by
      have h := congrArg (fun e : MulAut B => e ⟨b, hb⟩) htker
      simpa [φ] using h
    have hcoe := Subgroup.normalizerMonoidHom_apply_apply_coe B
      (Subgroup.inclusion hSnorm tS) ⟨b, hb⟩
    have hx' : ((Subgroup.inclusion hSnorm tS : Subgroup.normalizer (B : Set G)) : G) =
        (tS : G) := rfl
    rw [hx', hfix] at hcoe
    rw [Commute]
    calc (tS : G) * b = (tS : G) * b * (tS : G)⁻¹ * (tS : G) := by group
      _ = b * (tS : G) := by
        rw [show (tS : G) * b * (tS : G)⁻¹ = b from hcoe.symm]
  refine (Subgroup.eq_bot_iff_forall B).mpr ?_
  intro b hb
  exact hinv (tS : G) (hSN tS.2) ht_sq htne b hb (hcomm b hb)

end PermGroup

section EigenFour

private def eigenPlus {F W : Type} [Field F] [AddCommGroup W] [Module F W]
    (w : W ≃ₗ[F] W) : Submodule F W :=
  LinearMap.ker (w.toLinearMap - LinearMap.id)

private def eigenMinus {F W : Type} [Field F] [AddCommGroup W] [Module F W]
    (w : W ≃ₗ[F] W) : Submodule F W :=
  LinearMap.ker (w.toLinearMap + LinearMap.id)

private lemma eigen_isCompl {F W : Type} [Field F] [AddCommGroup W] [Module F W]
    (h2 : (2 : F) ≠ 0) {w : W ≃ₗ[F] W} (hw : w * w = 1) :
    IsCompl (eigenPlus w) (eigenMinus w) := by
  constructor
  · rw [disjoint_iff, Submodule.eq_bot_iff]
    intro v hv
    rw [Submodule.mem_inf] at hv
    obtain ⟨hv1, hv2⟩ := hv
    simp [eigenPlus, eigenMinus, LinearMap.mem_ker] at hv1 hv2
    have hv1' : w v = v := sub_eq_zero.mp hv1
    have hv2' : w v = -v := by rwa [add_eq_zero_iff_eq_neg] at hv2
    have h2v : (2 : F) • v = 0 := by
      calc (2 : F) • v = v + v := by rw [two_smul]
        _ = v - (-v) := by rw [sub_neg_eq_add]
        _ = w v - w v := by rw [← hv2', hv1']
        _ = 0 := sub_self _
    exact (smul_eq_zero.mp h2v).resolve_left h2
  · rw [codisjoint_iff, Submodule.eq_top_iff']
    intro v
    let vp : W := (2⁻¹ : F) • (v + w v)
    let vm : W := (2⁻¹ : F) • (v - w v)
    have hww : w (w v) = v := by
      simpa [LinearEquiv.mul_apply] using congrArg (fun e : W ≃ₗ[F] W => e v) hw
    have hvp : vp ∈ eigenPlus w := by
      rw [eigenPlus, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply]
      have hwvp : w vp = vp := by
        calc w vp = w ((2⁻¹ : F) • (v + w v)) := rfl
          _ = (2⁻¹ : F) • (w (v + w v)) := by rw [map_smul]
          _ = (2⁻¹ : F) • (w v + w (w v)) := by rw [map_add]
          _ = (2⁻¹ : F) • (w v + v) := by rw [hww]
          _ = (2⁻¹ : F) • (v + w v) := by rw [add_comm]
          _ = vp := rfl
      change w vp - vp = 0
      rw [hwvp, sub_self]
    have hvm : vm ∈ eigenMinus w := by
      rw [eigenMinus, LinearMap.mem_ker, LinearMap.add_apply, LinearMap.id_apply]
      have hwvm : w vm = -vm := by
        calc w vm = w ((2⁻¹ : F) • (v - w v)) := rfl
          _ = (2⁻¹ : F) • (w (v - w v)) := by rw [map_smul]
          _ = (2⁻¹ : F) • (w v - w (w v)) := by rw [map_sub]
          _ = (2⁻¹ : F) • (w v - v) := by rw [hww]
          _ = -(2⁻¹ : F) • (v - w v) := by
            rw [show w v - v = -(v - w v) from by abel, smul_neg, neg_smul]
          _ = -vm := by simp [vm]
      change w vm + vm = 0
      rw [hwvm, neg_add_cancel]
    have hsum : v = vp + vm := by
      have hvec : (v + w v) + (v - w v) = v + v := by abel
      calc v = (2⁻¹ * 2 : F) • v := by rw [inv_mul_cancel₀ h2, one_smul]
        _ = (2⁻¹ : F) • ((2 : F) • v) := by rw [smul_smul]
        _ = (2⁻¹ : F) • (v + v) := by rw [two_smul]
        _ = (2⁻¹ : F) • ((v + w v) + (v - w v)) := by rw [hvec]
        _ = vp + vm := by rw [smul_add]
    rw [hsum]
    exact Submodule.add_mem_sup hvp hvm

private lemma eigenPlus_ne_bot {F W : Type} [Field F] [AddCommGroup W] [Module F W]
    (h2 : (2 : F) ≠ 0) {w : W ≃ₗ[F] W} (hw : w * w = 1)
    (hwn : w ≠ LinearEquiv.neg F) : eigenPlus w ≠ ⊥ := by
  intro h
  have hc := eigen_isCompl h2 hw
  have htop : eigenMinus w = ⊤ := by
    have hsup := hc.2
    rw [codisjoint_iff, h, bot_sup_eq] at hsup
    exact hsup
  have hwneg : w = LinearEquiv.neg F := by
    ext v
    have hv : v ∈ eigenMinus w := by rw [htop]; exact Submodule.mem_top
    simp only [eigenMinus, LinearMap.mem_ker, LinearMap.add_apply,
      LinearMap.id_apply] at hv
    have hv' : w v = -v := by
      rwa [add_eq_zero_iff_eq_neg] at hv
    simpa [LinearEquiv.neg_apply] using hv'
  exact hwn hwneg

private lemma eigenMinus_ne_bot {F W : Type} [Field F] [AddCommGroup W] [Module F W]
    (h2 : (2 : F) ≠ 0) {w : W ≃ₗ[F] W} (hw : w * w = 1)
    (hw1 : w ≠ 1) : eigenMinus w ≠ ⊥ := by
  intro h
  have hc := eigen_isCompl h2 hw
  have htop : eigenPlus w = ⊤ := by
    have hsup := hc.2
    rw [codisjoint_iff, h, sup_bot_eq] at hsup
    exact hsup
  have hwone : w = 1 := by
    ext v
    have hv : v ∈ eigenPlus w := by rw [htop]; exact Submodule.mem_top
    simp only [eigenPlus, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.id_apply] at hv
    have hv' : w v = v := by
      rwa [sub_eq_zero] at hv
    simpa using hv'
  exact hw1 hwone

private lemma eigen_beta_maps_plus {F W : Type} [Field F] [AddCommGroup W] [Module F W]
    {w β : W ≃ₗ[F] W} (hc : w * β = β * w) :
    ∀ v ∈ eigenPlus w, β v ∈ eigenPlus w := by
  intro v hv
  rw [eigenPlus, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply] at hv ⊢
  have hv' : w v = v := sub_eq_zero.mp hv
  have hcomm : w (β v) = β (w v) := by
    simpa [LinearEquiv.mul_apply] using congrArg (fun e : W ≃ₗ[F] W => e v) hc
  simp [hcomm, hv']

private lemma eigen_beta_maps_minus {F W : Type} [Field F] [AddCommGroup W] [Module F W]
    {w β : W ≃ₗ[F] W} (hc : w * β = β * w) :
    ∀ v ∈ eigenMinus w, β v ∈ eigenMinus w := by
  intro v hv
  rw [eigenMinus, LinearMap.mem_ker, LinearMap.add_apply, LinearMap.id_apply] at hv ⊢
  have hv' : w v = -v := by
    rwa [add_eq_zero_iff_eq_neg] at hv
  have hcomm : w (β v) = β (w v) := by
    simpa [LinearEquiv.mul_apply] using congrArg (fun e : W ≃ₗ[F] W => e v) hc
  simp [hcomm, hv', map_neg]

private lemma eigen_card_linearEquiv_eq_card_GL {F U : Type} [Field F] [AddCommGroup U]
    [Module F U] [FiniteDimensional F U] [Finite U] {d : ℕ}
    (hd : Module.finrank F U = d) :
    Nat.card (U ≃ₗ[F] U) = Nat.card (GL (Fin d) F) := by
  let b : Module.Basis (Fin d) F U := Module.finBasisOfFinrankEq F U hd
  let e1 : (U ≃ₗ[F] U) ≃* LinearMap.GeneralLinearGroup F U :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv F U).symm
  let e2 : LinearMap.GeneralLinearGroup F U ≃* GL (Fin d) F :=
    (Matrix.GeneralLinearGroup.toLin' b).symm
  exact Nat.card_congr (e1.trans e2).toEquiv

private lemma eigen_prime_not_dvd_card_GL {F : Type} [Field F] [Finite F]
    {r : ℕ} (hr : r.Prime) (hrq : ¬ r ∣ Nat.card F)
    (hr1 : ¬ r ∣ Nat.card F - 1) (hr2 : ¬ r ∣ Nat.card F ^ 2 - 1)
    (hr3 : ¬ r ∣ Nat.card F ^ 3 - 1) {d : ℕ} (hd : d = 1 ∨ d = 2 ∨ d = 3) :
    ¬ r ∣ Nat.card (GL (Fin d) F) := by
  let : Fintype F := Fintype.ofFinite F
  have hrq' : ¬ r ∣ Fintype.card F := by simpa [Nat.card_eq_fintype_card] using hrq
  have hr1' : ¬ r ∣ Fintype.card F - 1 := by simpa [Nat.card_eq_fintype_card] using hr1
  have hr2' : ¬ r ∣ Fintype.card F ^ 2 - 1 := by simpa [Nat.card_eq_fintype_card] using hr2
  have hr3' : ¬ r ∣ Fintype.card F ^ 3 - 1 := by simpa [Nat.card_eq_fintype_card] using hr3
  rcases hd with rfl | rfl | rfl
  · rw [Matrix.card_GL_field, Fin.prod_univ_one]
    simpa using hr1'
  · rw [Matrix.card_GL_field, Fin.prod_univ_two]
    simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one]
    have hq2 : Fintype.card F ^ 2 - Fintype.card F = Fintype.card F * (Fintype.card F - 1) := by
      rw [pow_two, Nat.mul_sub_left_distrib, Nat.mul_one]
    rw [hq2]
    exact Nat.Prime.not_dvd_mul hr hr2'
      (Nat.Prime.not_dvd_mul hr hrq' (by simpa using hr1'))
  · rw [Matrix.card_GL_field, Fin.prod_univ_three]
    simp only [Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one]
    have hq3a : Fintype.card F ^ 3 - Fintype.card F =
        Fintype.card F * (Fintype.card F ^ 2 - 1) := by
      rw [pow_succ, Nat.mul_sub_left_distrib, Nat.mul_one]
      rw [mul_comm (Fintype.card F ^ 2) (Fintype.card F)]
    have hq3b : Fintype.card F ^ 3 - Fintype.card F ^ 2 =
        Fintype.card F ^ 2 * (Fintype.card F - 1) := by
      rw [pow_succ', Nat.mul_sub_left_distrib, Nat.mul_one]
      rw [mul_comm (Fintype.card F) (Fintype.card F ^ 2)]
    rw [hq3a, hq3b]
    have h23 : ¬ r ∣ (Fintype.card F ^ 2 - 1) * (Fintype.card F - 1) :=
      Nat.Prime.not_dvd_mul hr hr2' hr1'
    have h234 : ¬ r ∣ ((Fintype.card F ^ 2 - 1) * (Fintype.card F - 1)) * Fintype.card F :=
      Nat.Prime.not_dvd_mul hr h23 hrq'
    have h2345 : ¬ r ∣ (((Fintype.card F ^ 2 - 1) * (Fintype.card F - 1)) *
        Fintype.card F) * Fintype.card F ^ 2 :=
      Nat.Prime.not_dvd_mul hr h234 (by
        rw [pow_two]
        exact Nat.Prime.not_dvd_mul hr hrq' hrq')
    have hfinal : ¬ r ∣ (Fintype.card F ^ 3 - 1) *
        ((((Fintype.card F ^ 2 - 1) * (Fintype.card F - 1)) * Fintype.card F) *
          Fintype.card F ^ 2) :=
      Nat.Prime.not_dvd_mul hr hr3' h2345
    simpa [mul_assoc, mul_comm, mul_left_comm] using hfinal

private lemma eigen_prime_not_dvd_card_linearEquiv {F U : Type} [Field F] [Finite F]
    [AddCommGroup U] [Module F U] [FiniteDimensional F U] [Finite U]
    {r : ℕ} (hr : r.Prime) (hrq : ¬ r ∣ Nat.card F)
    (hr1 : ¬ r ∣ Nat.card F - 1) (hr2 : ¬ r ∣ Nat.card F ^ 2 - 1)
    (hr3 : ¬ r ∣ Nat.card F ^ 3 - 1)
    (hd : Module.finrank F U = 1 ∨ Module.finrank F U = 2 ∨ Module.finrank F U = 3) :
    ¬ r ∣ Nat.card (U ≃ₗ[F] U) := by
  rcases hd with hd1 | hd2 | hd3
  · rw [eigen_card_linearEquiv_eq_card_GL hd1]
    exact eigen_prime_not_dvd_card_GL hr hrq hr1 hr2 hr3 (Or.inl rfl)
  · rw [eigen_card_linearEquiv_eq_card_GL hd2]
    exact eigen_prime_not_dvd_card_GL hr hrq hr1 hr2 hr3 (Or.inr (Or.inl rfl))
  · rw [eigen_card_linearEquiv_eq_card_GL hd3]
    exact eigen_prime_not_dvd_card_GL hr hrq hr1 hr2 hr3 (Or.inr (Or.inr rfl))

private lemma eigen_order_eq_one_of_prime_not_dvd {G : Type} [Group G] [Finite G]
    {r k : ℕ} (hr : r.Prime) {x : G} (hx : x ^ (r ^ k) = 1)
    (hdiv : ¬ r ∣ Nat.card G) : x = 1 := by
  have h1 : orderOf x ∣ r ^ k := orderOf_dvd_of_pow_eq_one hx
  rcases (Nat.dvd_prime_pow hr).mp h1 with ⟨j, hj, hxj⟩
  have h2 : orderOf x ∣ Nat.card G := orderOf_dvd_natCard x
  rw [hxj] at h2
  have hj0 : j = 0 := by
    by_contra hjne
    have hdiv' : r ∣ r ^ j := dvd_pow_self r hjne
    exact hdiv (dvd_trans hdiv' h2)
  rw [hj0, pow_zero] at hxj
  exact orderOf_eq_one_iff.mp hxj

private theorem eq_one_of_commute_involution_of_finrank_four {F W : Type} [Field F] [Finite F]
    [AddCommGroup W] [Module F W] [FiniteDimensional F W] (h2 : (2 : F) ≠ 0)
    (hdim : Module.finrank F W = 4) {r k : ℕ} (hr : r.Prime) (hrq : ¬ r ∣ Nat.card F)
    (hr1 : ¬ r ∣ Nat.card F - 1) (hr2 : ¬ r ∣ Nat.card F ^ 2 - 1)
    (hr3 : ¬ r ∣ Nat.card F ^ 3 - 1) {w β : W ≃ₗ[F] W} (hw : w * w = 1) (hw1 : w ≠ 1)
    (hwn : w ≠ LinearEquiv.neg F) (hβ : β ^ (r ^ k) = 1) (hc : w * β = β * w) : β = 1 := by
  have : Finite W := Module.finite_of_finite F
  have : Finite (eigenPlus w) := Subtype.finite
  have : Finite (eigenMinus w) := Subtype.finite
  have : Finite (eigenPlus w ≃ₗ[F] eigenPlus w) :=
    FunLike.finite (eigenPlus w ≃ₗ[F] eigenPlus w)
  have : Finite (eigenMinus w ≃ₗ[F] eigenMinus w) :=
    FunLike.finite (eigenMinus w ≃ₗ[F] eigenMinus w)
  have hcompl := eigen_isCompl h2 hw
  have hWp_ne : eigenPlus w ≠ ⊥ := eigenPlus_ne_bot h2 hw hwn
  have hWm_ne : eigenMinus w ≠ ⊥ := eigenMinus_ne_bot h2 hw hw1
  have hdim_sum : Module.finrank F (eigenPlus w) + Module.finrank F (eigenMinus w) = 4 := by
    rw [← hdim]
    exact Submodule.finrank_add_eq_of_isCompl hcompl
  have hdim_plus : Module.finrank F (eigenPlus w) = 1 ∨ Module.finrank F (eigenPlus w) = 2 ∨
      Module.finrank F (eigenPlus w) = 3 := by
    have hpos : 0 < Module.finrank F (eigenPlus w) := by
      by_contra h
      have : Module.finrank F (eigenPlus w) = 0 := by omega
      exact hWp_ne (Submodule.finrank_eq_zero.mp this)
    have hlt : Module.finrank F (eigenPlus w) < 4 := by
      by_contra h
      have : Module.finrank F (eigenPlus w) = 4 := by omega
      have htop : eigenPlus w = ⊤ := by
        have hfin : Module.finrank F (eigenPlus w) = Module.finrank F W := by
          rw [this, hdim]
        exact Submodule.eq_top_of_finrank_eq hfin
      have hwone : w = 1 := by
        ext v
        have hv : v ∈ eigenPlus w := by rw [htop]; exact Submodule.mem_top
        simp only [eigenPlus, LinearMap.mem_ker, LinearMap.sub_apply,
          LinearMap.id_apply] at hv
        have hv' : w v = v := sub_eq_zero.mp hv
        simpa using hv'
      exact hw1 hwone
    omega
  have hdim_minus : Module.finrank F (eigenMinus w) = 1 ∨ Module.finrank F (eigenMinus w) = 2 ∨
      Module.finrank F (eigenMinus w) = 3 := by
    have hpos : 0 < Module.finrank F (eigenMinus w) := by
      by_contra h
      have : Module.finrank F (eigenMinus w) = 0 := by omega
      exact hWm_ne (Submodule.finrank_eq_zero.mp this)
    have hlt : Module.finrank F (eigenMinus w) < 4 := by
      by_contra h
      have : Module.finrank F (eigenMinus w) = 4 := by omega
      have htop : eigenMinus w = ⊤ := by
        have hfin : Module.finrank F (eigenMinus w) = Module.finrank F W := by
          rw [this, hdim]
        exact Submodule.eq_top_of_finrank_eq hfin
      have hwneg : w = LinearEquiv.neg F := by
        ext v
        have hv : v ∈ eigenMinus w := by rw [htop]; exact Submodule.mem_top
        simp only [eigenMinus, LinearMap.mem_ker, LinearMap.add_apply,
          LinearMap.id_apply] at hv
        have hv' : w v = -v := by
          rwa [add_eq_zero_iff_eq_neg] at hv
        simpa [LinearEquiv.neg_apply] using hv'
      exact hwn hwneg
    omega
  have hβstab_plus : β ∈ CFSG.ClassicalGroups.Orthogonal.Small.stabSub (eigenPlus w) := by
    rw [CFSG.ClassicalGroups.Orthogonal.Small.mem_stabSub]
    intro x
    constructor
    · exact eigen_beta_maps_plus hc x
    · intro hx
      have hβU : ∀ v ∈ eigenPlus w, β v ∈ eigenPlus w := eigen_beta_maps_plus hc
      have hmap : (eigenPlus w).map (β : W →ₗ[F] W) = eigenPlus w := by
        have hle : (eigenPlus w).map (β : W →ₗ[F] W) ≤ eigenPlus w := by
          rw [Submodule.map_le_iff_le_comap]
          intro v hv
          exact hβU v hv
        have hdim := LinearEquiv.finrank_map_eq β (eigenPlus w)
        exact Submodule.eq_of_le_of_finrank_eq hle hdim
      rw [← hmap] at hx
      rw [Submodule.mem_map] at hx
      obtain ⟨y, hy, hxy⟩ := hx
      have hyx : y = x := β.injective hxy
      rwa [← hyx]
  have hβstab_minus : β ∈ CFSG.ClassicalGroups.Orthogonal.Small.stabSub (eigenMinus w) := by
    rw [CFSG.ClassicalGroups.Orthogonal.Small.mem_stabSub]
    intro x
    constructor
    · exact eigen_beta_maps_minus hc x
    · intro hx
      have hβU : ∀ v ∈ eigenMinus w, β v ∈ eigenMinus w := eigen_beta_maps_minus hc
      have hmap : (eigenMinus w).map (β : W →ₗ[F] W) = eigenMinus w := by
        have hle : (eigenMinus w).map (β : W →ₗ[F] W) ≤ eigenMinus w := by
          rw [Submodule.map_le_iff_le_comap]
          intro v hv
          exact hβU v hv
        have hdim := LinearEquiv.finrank_map_eq β (eigenMinus w)
        exact Submodule.eq_of_le_of_finrank_eq hle hdim
      rw [← hmap] at hx
      rw [Submodule.mem_map] at hx
      obtain ⟨y, hy, hxy⟩ := hx
      have hyx : y = x := β.injective hxy
      rwa [← hyx]
  let βp := CFSG.ClassicalGroups.Orthogonal.Small.resHom (eigenPlus w) ⟨β, hβstab_plus⟩
  let βm := CFSG.ClassicalGroups.Orthogonal.Small.resHom (eigenMinus w) ⟨β, hβstab_minus⟩
  have hβp_pow : βp ^ (r ^ k) = 1 := by
    ext v
    have h := CFSG.ClassicalGroups.Orthogonal.Small.resHom_pow_apply hβstab_plus (r ^ k) v
    rw [hβ] at h
    simpa using h
  have hβm_pow : βm ^ (r ^ k) = 1 := by
    ext v
    have h := CFSG.ClassicalGroups.Orthogonal.Small.resHom_pow_apply hβstab_minus (r ^ k) v
    rw [hβ] at h
    simpa using h
  have hβp_eq_one : βp = 1 := by
    exact eigen_order_eq_one_of_prime_not_dvd hr hβp_pow
      (eigen_prime_not_dvd_card_linearEquiv hr hrq hr1 hr2 hr3 hdim_plus)
  have hβm_eq_one : βm = 1 := by
    exact eigen_order_eq_one_of_prime_not_dvd hr hβm_pow
      (eigen_prime_not_dvd_card_linearEquiv hr hrq hr1 hr2 hr3 hdim_minus)
  ext v
  obtain ⟨vp, vm, hsum⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.exists_add_of_isCompl hcompl v
  have hβvp : β (vp : W) = vp := by
    have h := CFSG.ClassicalGroups.Orthogonal.Small.resHom_apply (eigenPlus w)
      ⟨β, hβstab_plus⟩ vp
    have h' : ((βp vp : eigenPlus w) : W) = β (vp : W) := h
    rw [hβp_eq_one] at h'
    simpa using h'.symm
  have hβvm : β (vm : W) = vm := by
    have h := CFSG.ClassicalGroups.Orthogonal.Small.resHom_apply (eigenMinus w)
      ⟨β, hβstab_minus⟩ vm
    have h' : ((βm vm : eigenMinus w) : W) = β (vm : W) := h
    rw [hβm_eq_one] at h'
    simpa using h'.symm
  calc β v = β ((vp : W) + (vm : W)) := by rw [hsum]
    _ = β (vp : W) + β (vm : W) := by rw [map_add]
    _ = (vp : W) + (vm : W) := by rw [hβvp, hβvm]
    _ = v := hsum.symm

end EigenFour

section OmegaFour

open Subgroup
open CFSG.ComponentClassification
open CFSG.ComponentClassification.CatalogueBOrthogonalFourNonsplit
open CFSG.ComponentClassification.GSThmB.X10Orth

private theorem omegaFour_neg_mem_center_orthogonalGroup {K W : Type} [Field K]
    [AddCommGroup W] [Module K W] (Q : QuadraticForm K W)
    (g : TauCeti.QuadraticMap.orthogonalGroup Q) (hg : (g : W ≃ₗ[K] W) = LinearEquiv.neg K) :
    g ∈ Subgroup.center (TauCeti.QuadraticMap.orthogonalGroup Q) := by
  rw [Subgroup.mem_center_iff]
  intro h
  apply Subtype.ext
  change (↑h : W ≃ₗ[K] W) * ↑g = ↑g * ↑h
  rw [hg]
  apply LinearEquiv.ext
  intro x
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, LinearEquiv.neg_apply,
    LinearEquiv.neg_apply]
  exact LinearMap.map_neg (↑h : W →ₗ[K] W) x

private theorem natCard_commutator_orthogonalGroup_nonsplit_four {K W : Type} [Field K]
    [Finite K] [AddCommGroup W] [Module K W] [FiniteDimensional K W] (hodd : Odd (Nat.card K))
    (Q : QuadraticForm K W) (hQ : Q.polarBilin.Nondegenerate) (hdim : Module.finrank K W = 4)
    (hno : ¬ ∃ S : Submodule K W, Module.finrank K S = 2 ∧ ∀ x ∈ S, Q x = 0) :
    Nat.card (commutator (TauCeti.QuadraticMap.orthogonalGroup Q)) * 2 =
      Nat.card K ^ 2 * (Nat.card K ^ 4 - 1) := by
  have h2 := CatalogueBOddQuadratic.two_ne_zero_of_odd_card hodd
  obtain ⟨δ, hns, d, ψ, e, hψ, he, hcomm, hq, hsq⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.orthogonal_nonsplit_four_derived hodd Q hQ hdim hno
  have : Fact (¬ IsSquare (δ : K)) := ⟨hns⟩
  have : Finite (extension (δ : K)) :=
    Finite.of_equiv (K × K) (QuadraticAlgebra.equivProd (δ : K) 0).symm
  have hcardI : Nat.card (specialImage (δ : K) h2) * 2 =
      Nat.card (extension (δ : K)) * (Nat.card (extension (δ : K)) ^ 2 - 1) :=
    card_specialImage (δ : K) h2
  have hext : Nat.card (extension (δ : K)) = Nat.card K ^ 2 := extension_card (δ : K)
  have hcardΩ : Nat.card (commutator (TauCeti.QuadraticMap.orthogonalGroup Q)) =
      Nat.card (specialImage (δ : K) h2) := by
    rw [hcomm]
    exact (Nat.card_congr ((specialImage (δ : K) h2).equivMapOfInjective
      e.symm.toMonoidHom e.symm.injective).toEquiv).symm
  have hpow : (Nat.card K ^ 2) ^ 2 = Nat.card K ^ 4 := by
    rw [← pow_mul]
  rw [hcardΩ, hcardI, hext, hpow]

private theorem neg_not_mem_commutator_orthogonalGroup_nonsplit_four {K W : Type} [Field K]
    [Finite K] [AddCommGroup W] [Module K W] [FiniteDimensional K W] (hodd : Odd (Nat.card K))
    (Q : QuadraticForm K W) (hQ : Q.polarBilin.Nondegenerate) (hdim : Module.finrank K W = 4)
    (hno : ¬ ∃ S : Submodule K W, Module.finrank K S = 2 ∧ ∀ x ∈ S, Q x = 0)
    (g : TauCeti.QuadraticMap.orthogonalGroup Q) (hg : (g : W ≃ₗ[K] W) = LinearEquiv.neg K) :
    g ∉ commutator (TauCeti.QuadraticMap.orthogonalGroup Q) := by
  intro hgΩ
  have h2 := CatalogueBOddQuadratic.two_ne_zero_of_odd_card hodd
  obtain ⟨δ, hns, d, ψ, e, hψ, he, hcomm, hq, hsq⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.orthogonal_nonsplit_four_derived hodd Q hQ hdim hno
  have : Fact (¬ IsSquare (δ : K)) := ⟨hns⟩
  have : Finite (extension (δ : K)) :=
    Finite.of_equiv (K × K) (QuadraticAlgebra.equivProd (δ : K) 0).symm
  let I := specialImage (δ : K) h2
  have : IsSimpleGroup I := isSimpleGroup_specialImage (δ : K) h2
  let eΩ : commutator (TauCeti.QuadraticMap.orthogonalGroup Q) ≃* I :=
    (MulEquiv.subgroupCongr hcomm).trans
      (I.equivMapOfInjective e.symm.toMonoidHom e.symm.injective).symm
  have hΩsimple : IsSimpleGroup (commutator (TauCeti.QuadraticMap.orthogonalGroup Q)) :=
    MulEquiv.isSimpleGroup eΩ
  have : Nontrivial (commutator (TauCeti.QuadraticMap.orthogonalGroup Q)) := hΩsimple.toNontrivial
  have : Group.IsPerfect (commutator (TauCeti.QuadraticMap.orthogonalGroup Q)) := hq.1
  have hΩnoncomm : ¬ IsMulCommutative (commutator (TauCeti.QuadraticMap.orthogonalGroup Q)) :=
    Group.IsPerfect.not_isMulCommutative
      (commutator (TauCeti.QuadraticMap.orthogonalGroup Q))
  have hcenter : Subgroup.center (commutator (TauCeti.QuadraticMap.orthogonalGroup Q)) = ⊥ :=
    TauCeti.IsSimpleGroup.center_eq_bot_of_not_isMulCommutative hΩnoncomm
  have hgO : g ∈ Subgroup.center (TauCeti.QuadraticMap.orthogonalGroup Q) :=
    omegaFour_neg_mem_center_orthogonalGroup Q g hg
  have hgΩ_center : (⟨g, hgΩ⟩ : commutator (TauCeti.QuadraticMap.orthogonalGroup Q)) ∈
      Subgroup.center (commutator (TauCeti.QuadraticMap.orthogonalGroup Q)) := by
    rw [Subgroup.mem_center_iff]
    intro h
    apply Subtype.ext
    exact (Subgroup.mem_center_iff.mp hgO) (h : TauCeti.QuadraticMap.orthogonalGroup Q)
  have hg_eq_one : (⟨g, hgΩ⟩ : commutator (TauCeti.QuadraticMap.orthogonalGroup Q)) = 1 := by
    rw [hcenter] at hgΩ_center
    exact Subgroup.mem_bot.mp hgΩ_center
  have hgO_eq_one : (g : W ≃ₗ[K] W) = 1 := by
    have h1 : (g : TauCeti.QuadraticMap.orthogonalGroup Q) = 1 := congrArg Subtype.val hg_eq_one
    calc (g : W ≃ₗ[K] W) =
        ((1 : TauCeti.QuadraticMap.orthogonalGroup Q) : W ≃ₗ[K] W) :=
          congrArg (fun x : TauCeti.QuadraticMap.orthogonalGroup Q => (x : W ≃ₗ[K] W)) h1
      _ = 1 := Subgroup.coe_one (TauCeti.QuadraticMap.orthogonalGroup Q)
  have hneg_eq_one : (LinearEquiv.neg K : W ≃ₗ[K] W) = 1 := by
    rw [← hg, hgO_eq_one]
  have hW : Nontrivial W :=
    Module.nontrivial_of_finrank_pos (R := K) (M := W) (by rw [hdim]; norm_num)
  obtain ⟨x, hx⟩ := exists_ne (0 : W)
  have hx' : (LinearEquiv.neg K) x = (1 : W ≃ₗ[K] W) x := by rw [hneg_eq_one]
  rw [LinearEquiv.one_eq_refl, LinearEquiv.neg_apply, LinearEquiv.refl_apply] at hx'
  have hsum : x + x = 0 := by
    have h := congrArg (fun y => y + x) hx'
    simp only [neg_add_cancel] at h
    exact h.symm
  have h2x : (2 : K) • x = 0 := by
    simpa [two_smul] using hsum
  exact hx ((smul_eq_zero.mp h2x).resolve_left h2)

end OmegaFour

section StabOrth

open Subgroup QuadraticMap
open CFSG.ClassicalGroups.Orthogonal.Small CFSG.LocalAnalysis.ComponentInitial
open scoped Pointwise

private theorem stabOrth_maps_U_of_maps_W
    {F V : Type} [Field F] [AddCommGroup V] [Module F V]
    {Q : QuadraticForm F V} {W U : Submodule F V}
    (hQ : Q.polarBilin.Nondegenerate)
    (hc : IsCompl W U)
    (horth : ∀ w ∈ W, ∀ u ∈ U, polar Q w u = 0)
    {c : V ≃ₗ[F] V}
    (hcO : c ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hW : c ∈ stabSub W) :
    ∀ u ∈ U, c u ∈ U := by
  intro u hu
  have hQW : (Q.comp W.subtype).polarBilin.Nondegenerate :=
    nondegenerate_comp_subtype hQ hc horth
  obtain ⟨w, u', hwu⟩ := exists_add_of_isCompl hc (c u)
  have hw : w = 0 := by
    apply hQW.2 w
    intro v
    rw [polarBilin_apply_apply, polar_comp_subtype_apply]
    have hvW : c.symm v ∈ W := by
      have hmem : c (c.symm (v : V)) ∈ W := by
        rw [LinearEquiv.apply_symm_apply]
        exact v.2
      exact (mem_stabSub.mp hW (c.symm (v : V))).mpr hmem
    have hv : polar Q ((v : W) : V) (c u) = polar Q (((⟨c.symm v, hvW⟩ : W) : V)) u := by
      have h := TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hcO (⟨c.symm v, hvW⟩ : W) u
      rwa [LinearEquiv.apply_symm_apply] at h
    have h0 : polar Q (((⟨c.symm v, hvW⟩ : W) : V)) u = 0 := horth _ hvW _ hu
    have hvu : polar Q ((v : W) : V) (c u) = 0 := by rw [hv, h0]
    have hsplit : polar Q ((v : W) : V) (c u) =
        polar Q ((v : W) : V) ((w : W) : V) + polar Q ((v : W) : V) ((u' : U) : V) := by
      rw [hwu, polar_add_right]
    have hu'0 : polar Q ((v : W) : V) ((u' : U) : V) = 0 := horth _ v.2 _ u'.2
    rw [hvu, hu'0, add_zero] at hsplit
    exact hsplit.symm
  rw [hwu, hw]
  simp

private theorem stabOrth_stabSub_of_mem_orthogonalGroup
    {F V : Type} [Field F] [AddCommGroup V] [Module F V]
    {Q : QuadraticForm F V} {W U : Submodule F V}
    (hQ : Q.polarBilin.Nondegenerate)
    (hc : IsCompl W U)
    (horth : ∀ w ∈ W, ∀ u ∈ U, polar Q w u = 0)
    {c : V ≃ₗ[F] V}
    (hcO : c ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hW : c ∈ stabSub W) :
    c ∈ stabSub U := by
  rw [mem_stabSub]
  intro x
  constructor
  · intro hx
    exact stabOrth_maps_U_of_maps_W hQ hc horth hcO hW x hx
  · intro hx
    have hcO' : c⁻¹ ∈ TauCeti.QuadraticMap.orthogonalGroup Q := Subgroup.inv_mem _ hcO
    have hW' : c⁻¹ ∈ stabSub W := Subgroup.inv_mem _ hW
    have h := stabOrth_maps_U_of_maps_W hQ hc horth hcO' hW' (c x) hx
    change c.symm (c x) ∈ U at h
    rwa [LinearEquiv.symm_apply_apply] at h

theorem eq_bot_of_stabSub_orthogonal_nonsplit_four
    {X : Type} [Group X] [Finite X] {F V : Type} [Field F] [Finite F] [AddCommGroup V]
    [Module F V] [FiniteDimensional F V] (hodd : Odd (Nat.card F)) {Q : QuadraticForm F V}
    (hQ : Q.polarBilin.Nondegenerate) {W U : Submodule F V} (hc : IsCompl W U)
    (horth : ∀ w ∈ W, ∀ u ∈ U, polar Q w u = 0) (hdim : Module.finrank F W = 4)
    (hno : ¬ ∃ S : Submodule F W, Module.finrank F S = 2 ∧ ∀ x ∈ S, Q.comp W.subtype x = 0)
    {φ : X →* (V ≃ₗ[F] V)} (hφ : Function.Injective φ)
    (hφO : ∀ x, φ x ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hrange : ⁅TauCeti.QuadraticMap.orthogonalGroup Q,
      TauCeti.QuadraticMap.orthogonalGroup Q⁆ ≤ φ.range)
    {r : ℕ} (hr : r.Prime) (hr5 : 5 ≤ r) (hr7 : r ≠ 7) (hr8 : ¬ 8 ∣ r - 1)
    (hrq : ¬ r ∣ Nat.card F) (hr1 : ¬ r ∣ Nat.card F - 1) (hr2 : ¬ r ∣ Nat.card F ^ 2 - 1)
    (hr3 : ¬ r ∣ Nat.card F ^ 3 - 1)
    (hN2 : (Nat.card F ^ 2 * (Nat.card F ^ 4 - 1) / 2).factorization 2 = 3)
    (hNr : ¬ r ^ 2 ∣ Nat.card F ^ 2 * (Nat.card F ^ 4 - 1) / 2)
    (P : Sylow 2 X) (hP : ∀ y ∈ (P : Subgroup X), φ y ∈ stabSub W)
    {B : Subgroup X} (hB : IsPGroup r B)
    (hperm : (B : Set X) * (P : Set X) = (P : Set X) * (B : Set X))
    (hBW : ∀ x ∈ B, φ x ∈ stabSub W) (hBU : ∀ x ∈ B, ∀ u ∈ U, φ x u = u) :
    B = ⊥ := by
  let QW := Q.comp W.subtype
  have hQW : QW.polarBilin.Nondegenerate := nondegenerate_comp_subtype hQ hc horth
  let O₀ := TauCeti.QuadraticMap.orthogonalGroup QW
  let Ω₀ := commutator O₀
  let ι := (orthExtend hc).comp O₀.subtype
  have hinj_ext : Function.Injective (orthExtend hc) :=
    (orthogonal_complement_elementary_embedding Q hc horth).1
  have hinj_ι : Function.Injective ι :=
    hinj_ext.comp (fun _ _ h => Subtype.ext h)
  have hιO : ∀ g : O₀, ι g ∈ TauCeti.QuadraticMap.orthogonalGroup Q := fun g =>
    (orthogonal_complement_elementary_embedding Q hc horth).2.1 g.1 g.2
  let N₀ := Ω₀.map ι
  have hN₀_le_range : N₀ ≤ φ.range := by
    have hmap : N₀ = ⁅ι.range, ι.range⁆ := by
      dsimp only [N₀, Ω₀]
      rw [_root_.commutator_def, map_commutator, Subgroup.map_top]
    rw [hmap]
    have hrange_le : ι.range ≤ TauCeti.QuadraticMap.orthogonalGroup Q := by
      rintro _ ⟨g, -, rfl⟩
      exact hιO g
    exact (commutator_mono hrange_le hrange_le).trans hrange
  let N := N₀.comap φ
  have hNcard : Nat.card N = Nat.card F ^ 2 * (Nat.card F ^ 4 - 1) / 2 := by
    have hcard_N : Nat.card N = Nat.card Ω₀ := by
      have hmap_eq : Subgroup.map φ N = N₀ := by
        dsimp only [N]
        exact Subgroup.map_comap_eq_self hN₀_le_range
      have h1 : Nat.card N₀ = Nat.card N := by
        rw [← hmap_eq]
        exact Subgroup.card_map_of_injective hφ
      have h2 : Nat.card N₀ = Nat.card Ω₀ := by
        dsimp only [N₀]
        exact Subgroup.card_map_of_injective hinj_ι
      rw [← h1, h2]
    have hΩcard := natCard_commutator_orthogonalGroup_nonsplit_four hodd QW hQW hdim hno
    rw [hcard_N]
    exact Nat.eq_div_of_mul_eq_left (by norm_num) hΩcard
  have hPN : (P : Subgroup X) ≤ normalizer (N : Set X) := by
    have hconj_mem : ∀ y ∈ (P : Subgroup X), ∀ n ∈ N, y * n * y⁻¹ ∈ N := by
      intro y hy n hn
      have hn' : φ n ∈ N₀ := hn
      obtain ⟨ω, hω, hω_eq⟩ := hn'
      let c := φ y
      have hcO : c ∈ TauCeti.QuadraticMap.orthogonalGroup Q := hφO y
      have hW : c ∈ stabSub W := hP y hy
      have hU : c ∈ stabSub U :=
        stabOrth_stabSub_of_mem_orthogonalGroup hQ hc horth hcO hW
      let ρ : O₀ := ⟨resHom W ⟨c, hW⟩, resHom_mem_orthogonalGroup hcO hW⟩
      have hρΩ : ρ * ω * ρ⁻¹ ∈ Ω₀ :=
        Subgroup.Normal.conj_mem (inferInstance : Ω₀.Normal) ω hω ρ
      have hconj : c * ι ω * c⁻¹ = ι (ρ * ω * ρ⁻¹) := by
        change c * orthExtend hc (ω : W ≃ₗ[F] W) * c⁻¹ =
          orthExtend hc ((ρ * ω * ρ⁻¹ : O₀) : W ≃ₗ[F] W)
        rw [conj_orthExtend hc hW hU (ω : W ≃ₗ[F] W)]
        simp only [ρ, Subgroup.coe_mul, Subgroup.coe_inv]
      change φ (y * n * y⁻¹) ∈ N₀
      rw [map_mul, map_mul, map_inv, ← hω_eq]
      change c * ι ω * c⁻¹ ∈ N₀
      rw [hconj]
      exact Subgroup.mem_map.mpr ⟨ρ * ω * ρ⁻¹, hρΩ, rfl⟩
    intro y hy
    rw [Subgroup.mem_normalizer_iff]
    intro n
    constructor
    · intro hn
      exact hconj_mem y hy n hn
    · intro hn
      have hy' : y⁻¹ ∈ (P : Subgroup X) := Subgroup.inv_mem _ hy
      have h := hconj_mem y⁻¹ hy' (y * n * y⁻¹) hn
      have h_eq : y⁻¹ * (y * n * y⁻¹) * (y⁻¹)⁻¹ = n := by group
      rwa [h_eq] at h
  have hBN : B ≤ N := by
    intro x hx
    change φ x ∈ N₀
    let ρ : O₀ := ⟨resHom W ⟨φ x, hBW x hx⟩, resHom_mem_orthogonalGroup (hφO x) (hBW x hx)⟩
    have hιρ : ι ρ = φ x := by
      apply LinearEquiv.ext
      intro v
      obtain ⟨w, u, hwu⟩ := exists_add_of_isCompl hc v
      rw [hwu]
      have h1 : ι ρ ((w : V) + u) = (ρ.1 w : V) + u := by
        change orthExtend hc (ρ : W ≃ₗ[F] W) ((w : V) + u) = ((ρ : W ≃ₗ[F] W) w : V) + u
        exact orthExtend_apply hc (ρ : W ≃ₗ[F] W) w u
      have h2 : φ x ((w : V) + u) = (φ x w : V) + u := by
        rw [map_add, hBU x hx (u : V) u.2]
      have h3 : (ρ.1 w : V) = φ x w := rfl
      rw [h1, h2, h3]
    obtain ⟨a, ha⟩ := hB ⟨x, hx⟩
    have hxa : x ^ (r ^ a) = 1 := by
      have := congrArg (fun y : B => (y : X)) ha
      simpa using this
    have hφxa : φ x ^ (r ^ a) = 1 := by
      rw [← map_pow, hxa, map_one]
    have hρa : ρ ^ (r ^ a) = 1 := by
      apply hinj_ι
      rw [map_pow, hιρ, hφxa, map_one]
    obtain ⟨δ, hns, d, ψ, e, hψ, he, hcomm, hq, hsq⟩ :=
      orthogonal_nonsplit_four_derived hodd QW hQW hdim hno
    have hρΩ : ρ ∈ Ω₀ := by
      have hodd_pow : Odd (r ^ a) := Odd.pow (Nat.Prime.odd_of_ne_two hr (by omega))
      have h2m : 2 * ((r ^ a + 1) / 2) = r ^ a + 1 := by
        rcases hodd_pow with ⟨m, hm⟩
        rw [hm]
        omega
      have hρ_eq : ρ = (ρ ^ 2) ^ ((r ^ a + 1) / 2) := by
        calc ρ = ρ ^ 1 := by rw [pow_one]
          _ = ρ ^ (r ^ a + 1) := by
            rw [pow_add, hρa, one_mul, pow_one]
          _ = (ρ ^ 2) ^ ((r ^ a + 1) / 2) := by
            nth_rw 1 [← h2m]
            rw [pow_mul]
      rw [hρ_eq]
      exact Subgroup.pow_mem Ω₀ (hsq ρ) ((r ^ a + 1) / 2)
    exact Subgroup.mem_map.mpr ⟨ρ, hρΩ, hιρ⟩
  have hinv : ∀ t ∈ N, t ^ 2 = 1 → t ≠ 1 → ∀ b ∈ B, Commute t b → b = 1 := by
    intro t ht ht2 ht1 b hb hcomm
    have ht' : φ t ∈ N₀ := ht
    obtain ⟨ω, hω, hω_eq⟩ := ht'
    have hbN : b ∈ N := hBN hb
    have hb' : φ b ∈ N₀ := hbN
    obtain ⟨β, hβ, hβ_eq⟩ := hb'
    have hφt2 : φ t ^ 2 = 1 := by rw [← map_pow, ht2, map_one]
    have hω2 : ω ^ 2 = 1 := by
      apply hinj_ι
      rw [map_pow, hω_eq, hφt2]
      simp
    have hω1 : ω ≠ 1 := by
      intro h
      apply ht1
      apply hφ
      rw [← hω_eq, h]
      simp
    have hcomm' : ω * β = β * ω := by
      apply hinj_ι
      rw [map_mul, map_mul, hω_eq, hβ_eq]
      rw [← map_mul, ← map_mul, hcomm.eq]
    obtain ⟨k, hk⟩ := hB ⟨b, hb⟩
    have hbk : b ^ (r ^ k) = 1 := by
      have := congrArg (fun y : B => (y : X)) hk
      simpa using this
    have hβk : β ^ (r ^ k) = 1 := by
      apply hinj_ι
      rw [map_pow, hβ_eq, ← map_pow, hbk]
      simp
    have hwn : (ω : W ≃ₗ[F] W) ≠ LinearEquiv.neg F := by
      intro h
      exact (neg_not_mem_commutator_orthogonalGroup_nonsplit_four hodd QW hQW hdim hno ω h) hω
    have hw : (ω : W ≃ₗ[F] W) * (ω : W ≃ₗ[F] W) = 1 := by
      have := congrArg (fun y : O₀ => (y : W ≃ₗ[F] W)) hω2
      simpa [pow_two] using this
    have hw1 : (ω : W ≃ₗ[F] W) ≠ 1 := by
      intro h
      apply hω1
      exact Subtype.ext h
    have hβk' : (β : W ≃ₗ[F] W) ^ (r ^ k) = 1 := by
      have := congrArg (fun y : O₀ => (y : W ≃ₗ[F] W)) hβk
      simpa using this
    have hcomm'' : (ω : W ≃ₗ[F] W) * (β : W ≃ₗ[F] W) =
        (β : W ≃ₗ[F] W) * (ω : W ≃ₗ[F] W) := by
      have := congrArg (fun y : O₀ => (y : W ≃ₗ[F] W)) hcomm'
      simpa using this
    have hβ_one : β = 1 := by
      have h2 : (2 : F) ≠ 0 :=
        CFSG.ComponentClassification.CatalogueBOddQuadratic.two_ne_zero_of_odd_card hodd
      have hβ_one' : (β : W ≃ₗ[F] W) = 1 :=
        eq_one_of_commute_involution_of_finrank_four (w := (ω : W ≃ₗ[F] W))
          (β := (β : W ≃ₗ[F] W)) h2 hdim hr hrq hr1 hr2 hr3 hw hw1 hwn hβk' hcomm''
      exact Subtype.ext hβ_one'
    have hφb : φ b = 1 := by
      rw [← hβ_eq, hβ_one, map_one]
    exact hφ (by rw [hφb, map_one])
  exact eq_bot_of_permutes_of_forall_involution hr hr5 hr7 hr8 P hPN hBN hB hperm
    (by rw [hNcard]; exact hN2) (by rw [hNcard]; exact hNr) hinv

end StabOrth

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
