module

public import CFSG.Milestones.ASVolI.B610.FamB

public section

namespace CFSG.Quasithin.B610T

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {G : Type} [Group G]

theorem burnsideB610_map_conj_commutator {V Y : Subgroup G} {a : G}
    (haV : a ∈ Subgroup.normalizer (V : Set G)) (haY : a ∈ Subgroup.normalizer (Y : Set G)) :
    (⁅V, Y⁆ : Subgroup G).map (MulAut.conj a).toMonoidHom = ⁅V, Y⁆ := by
  have h1 : V.map (MulAut.conj a).toMonoidHom = V := Subgroup.mem_normalizer_iff_map_conj_eq.mp haV
  have h2 : Y.map (MulAut.conj a).toMonoidHom = Y := Subgroup.mem_normalizer_iff_map_conj_eq.mp haY
  rw [Subgroup.map_commutator, h1, h2]

theorem burnsideB610_le_normalizer_iSup_commutator {ι : Type} {X : ι → Subgroup G}
    {V A : Subgroup G} (hAV : A ≤ Subgroup.normalizer (V : Set G)) {𝒮 : Finset ι}
    (hA : ∀ i ∈ 𝒮, A ≤ Subgroup.normalizer ((X i : Subgroup G) : Set G)) :
    A ≤ Subgroup.normalizer (((⨆ i ∈ 𝒮, ⁅V, X i⁆ : Subgroup G)) : Set G) := by
  have key : ∀ a ∈ A, (⨆ i ∈ 𝒮, (⁅V, X i⁆ : Subgroup G)).map (MulAut.conj a).toMonoidHom ≤
      ⨆ i ∈ 𝒮, (⁅V, X i⁆ : Subgroup G) := by
    intro a ha
    rw [Subgroup.map_le_iff_le_comap]
    refine iSup₂_le fun i hi => ?_
    rw [← Subgroup.map_le_iff_le_comap, burnsideB610_map_conj_commutator (hAV ha) (hA i hi ha)]
    exact le_iSup₂_of_le (f := fun j (_ : j ∈ 𝒮) => (⁅V, X j⁆ : Subgroup G)) i hi le_rfl
  intro a ha
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  apply le_antisymm (key a ha)
  have h1 := Subgroup.map_mono (f := (MulAut.conj a).toMonoidHom) (key a⁻¹ (A.inv_mem ha))
  rw [Subgroup.map_map] at h1
  have e : ((MulAut.conj a).toMonoidHom.comp (MulAut.conj a⁻¹).toMonoidHom) = MonoidHom.id G := by
    ext x
    simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
      MulAut.conj_apply, MonoidHom.id_apply]
    group
  rw [e, Subgroup.map_id] at h1
  exact h1

namespace burnsideB610_Fam

variable {H T V : Subgroup G} {hV : IsElemAbelian 2 V} {F : Type} [Field F] {ι : Type}
  {S : Finset ι} {X : ι → Subgroup G} {D : ∀ i, NatData (X i) V F}

theorem sum_rkIdx_le [Finite G] [Finite F] [DecidableEq ι]
    (hFam : burnsideB610_Fam H T V hV F S X D) (hHV : H ≤ Subgroup.normalizer (V : Set G))
    {A : Subgroup G} (hAV : A ≤ Subgroup.normalizer (V : Set G))
    (hA : ∀ i ∈ S, A ≤ Subgroup.normalizer ((X i : Subgroup G) : Set G)) :
    ∀ 𝒮 : Finset ι, 𝒮 ⊆ S →
      (∑ i ∈ 𝒮, rkIdx (fixV ((D i).img A))) +
          rk ↥((⨆ i ∈ 𝒮, (⁅V, X i⁆ : Subgroup G)) ⊓ Subgroup.centralizer (A : Set G)) ≤
        rk ↥(⨆ i ∈ 𝒮, (⁅V, X i⁆ : Subgroup G)) := by
  intro 𝒮
  induction 𝒮 using Finset.induction_on with
  | empty =>
    intro _
    have he : (⨆ i ∈ (∅ : Finset ι), (⁅V, X i⁆ : Subgroup G)) = ⊥ :=
      le_antisymm (iSup₂_le fun i hi => (Finset.notMem_empty i hi).elim) bot_le
    rw [he, Finset.sum_empty, zero_add]
    exact rk_mono inf_le_left
  | insert Y 𝒮' hY ih =>
    intro hsub
    have hYS : Y ∈ S := hsub (Finset.mem_insert_self Y 𝒮')
    have h𝒮' : 𝒮' ⊆ S := fun i hi => hsub (Finset.mem_insert_of_mem hi)
    have ih' := ih h𝒮'
    rw [Finset.iSup_insert, Finset.sum_insert hY]
    set W' : Subgroup G := ⨆ i ∈ 𝒮', (⁅V, X i⁆ : Subgroup G) with hW'
    set VY : Subgroup G := ⁅V, X Y⁆ with hVY
    set W : Subgroup G := VY ⊔ W' with hW
    set CW : Subgroup G := W ⊓ Subgroup.centralizer (A : Set G) with hCW
    set N₁ : Subgroup G := W' ⊔ CW with hN₁
    have hVYV : VY ≤ V := hFam.commutator_le hHV hYS
    have hW'V : W' ≤ V := iSup₂_le fun i hi => hFam.commutator_le hHV (h𝒮' hi)
    have hWV : W ≤ V := sup_le hVYV hW'V
    have hCWV : CW ≤ V := inf_le_left.trans hWV
    have hN₁V : N₁ ≤ V := sup_le hW'V hCWV
    have hcomm : ∀ {P Q : Subgroup G}, P ≤ V → Q ≤ V → ∀ a ∈ P, ∀ b ∈ Q, a * b = b * a :=
      fun hP hQ a ha b hb => B2F.isElemAbelian_comm hV (hP ha) (hQ hb)
    have e1 : rk ↥N₁ + rk ↥(W' ⊓ CW) = rk ↥W' + rk ↥CW :=
      B2F.rk_sup_add_rk_inf_of_commute (hcomm hW'V hCWV)
    have e2 : W' ⊓ CW = W' ⊓ Subgroup.centralizer (A : Set G) := by
      ext x
      exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, ⟨Subgroup.mem_sup_right h.1, h.2⟩⟩⟩
    have e3 : VY ⊔ N₁ = W :=
      le_antisymm (sup_le le_sup_left (sup_le le_sup_right inf_le_left))
        (sup_le le_sup_left (le_sup_left.trans le_sup_right))
    have e4 : rk ↥(VY ⊔ N₁) + rk ↥(VY ⊓ N₁) = rk ↥VY + rk ↥N₁ :=
      B2F.rk_sup_add_rk_inf_of_commute (hcomm hVYV hN₁V)
    rw [e3] at e4
    rw [e2] at e1
    have hAW' : A ≤ Subgroup.normalizer ((W' : Subgroup G) : Set G) :=
      burnsideB610_le_normalizer_iSup_commutator hAV (fun i hi => hA i (h𝒮' hi))
    have hW'C : W' ≤ Subgroup.centralizer ((X Y : Subgroup G) : Set G) := by
      refine iSup₂_le fun i hi => ?_
      have hiY : i ≠ Y := fun h => hY (h ▸ hi)
      exact Subgroup.le_centralizer_iff.mp (hFam.triv i (h𝒮' hi) Y hYS hiY)
    have hle : VY ⊓ N₁ ≤ burnsideB610_pre (D Y) (fixV ((D Y).img A)) := by
      rintro u ⟨huVY, huN⟩
      have hW'CW : W' ≤ Subgroup.normalizer ((CW : Subgroup G) : Set G) := fun x hx =>
        Subgroup.centralizer_le_normalizer _
          (Subgroup.mem_centralizer_iff.2 fun y hy => (hcomm hW'V hCWV x hx y hy).symm)
      have huN' : u ∈ ((W' ⊔ CW : Subgroup G) : Set G) := huN
      rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hW'CW] at huN'
      obtain ⟨w, hw, c, hc, rfl⟩ := huN'
      refine ⟨⟨w * c, huVY⟩, ?_, rfl⟩
      rintro _ ⟨a', ha', rfl⟩
      show rho (D Y).β (D Y).βsurj (D Y).βker a' ((D Y).β ⟨w * c, huVY⟩) =
        (D Y).β ⟨w * c, huVY⟩
      rw [rho_apply, ← mul_inv_eq_one, ← map_inv, ← map_mul, ← MonoidHom.mem_ker, (D Y).βker,
        Subgroup.mem_subgroupOf]
      have haA : (a' : G) ∈ A := Subgroup.mem_subgroupOf.mp ha'
      have hca : (a' : G) * c = c * a' :=
        (Subgroup.mem_centralizer_iff.mp hc.2 _ haA)
      have haw : (a' : G) * w * (a' : G)⁻¹ ∈ W' :=
        (Subgroup.mem_normalizer_iff.mp (hAW' haA) w).mp hw
      have hcw : c * w⁻¹ = w⁻¹ * c := hcomm hCWV hW'V c hc _ (W'.inv_mem hw)
      have e : ((cW a' ⟨w * c, huVY⟩ * (⟨w * c, huVY⟩ : ↥VY)⁻¹ : ↥VY) : G) =
          (a' : G) * w * (a' : G)⁻¹ * w⁻¹ := by
        rw [Subgroup.coe_mul, coe_cW, Subgroup.coe_inv]
        calc (a' : G) * (w * c) * (a' : G)⁻¹ * (w * c)⁻¹
            = (a' : G) * w * ((a' : G)⁻¹ * ((a' : G) * c)) * (a' : G)⁻¹ * (c⁻¹ * w⁻¹) := by group
          _ = (a' : G) * w * ((a' : G)⁻¹ * (c * a')) * (a' : G)⁻¹ * (c⁻¹ * w⁻¹) := by rw [hca]
          _ = (a' : G) * w * (a' : G)⁻¹ * w⁻¹ := by group
      refine ⟨SetLike.coe_mem _, ?_⟩
      rw [e]
      exact hW'C (W'.mul_mem haw (W'.inv_mem hw))
    have e6 : rk ↥(burnsideB610_pre (D Y) (fixV ((D Y).img A))) +
        rkIdx (fixV ((D Y).img A)) = rk ↥VY := burnsideB610_rk_pre (D Y) (fixV ((D Y).img A))
    have r := rk_mono hle
    omega

theorem chain [Finite G] [Fintype F] [CharP F 2] [DecidableEq ι] {n : ℕ} (hn : 1 ≤ n)
    (hF : Nat.card F = 2 ^ n) (hFam : burnsideB610_Fam H T V hV F S X D)
    (hred : IsTwoReducedIn H V) (hT : IsSylowTwoOf T H) {A : Subgroup G}
    (hA : IsMaxElemAbelian T A) (hAV : ¬ A ≤ Subgroup.centralizer (V : Set G)) :
    rkIdx (fixV (autI hV A)) = rk ↥(autI hV A) ∧
      (∀ i ∈ S, rk ↥((D i).img A) = rkIdx (fixV ((D i).img A))) ∧
      rk ↥(autI hV A) = ∑ i ∈ S, rk ↥((D i).img A) ∧
      rk ↥(burnsideB610_famW S X V ⊓ Subgroup.centralizer (A : Set G)) +
          rkIdx (fixV (autI hV A)) = rk ↥(burnsideB610_famW S X V) := by
  have hHV : H ≤ Subgroup.normalizer (V : Set G) := hred.2.1
  have hVT : V ≤ T := (MinParabolic.le_pCoreOf_of_isTwoReduced hred).trans
    (B6.pCoreOf_two_le_of_isSylowTwoOf hT)
  have hTV : T ≤ Subgroup.normalizer (V : Set G) := hT.1.trans hHV
  have hAN : A ≤ Subgroup.normalizer (V : Set G) := hA.1.trans hTV
  have hAJ : A ≤ thompsonJ T := le_iSup₂_of_le A hA le_rfl
  have hAX : ∀ i ∈ S, A ≤ Subgroup.normalizer ((X i : Subgroup G) : Set G) :=
    fun i hi => hAJ.trans (hFam.thomp i hi)
  have hAnLV : ∀ i ∈ S, A ≤ nLV (X i) V := fun i hi x hx => ⟨hAX i hi hx, hAN hx⟩
  have hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
    B2F.isElemAbelian_comm hA.2.1 ha hb
  have hoff := offenderImages_isFFStarOffender hV hVT hTV ⟨A, ⟨hA, hAV⟩, rfl⟩
  have hoff1 := hoff.2.2.2 ⊥ bot_le
  rw [B1.card_bot_mul_card_fixV] at hoff1
  have hV2 : IsPGroup 2 (IntMod V hV) := by
    intro v
    exact ⟨1, by rw [pow_one]; exact IntMod.sq_eq_one v⟩
  have hc1 := burnsideB610_rk_le_of_card_le hV2 hoff.2.2.1.isPGroup (hV2.to_subgroup _) hoff1
  have hc2 := rk_add_rkIdx (fixV (autI hV A))
  have hca : rkIdx (fixV (autI hV A)) ≤ rk ↥(autI hV A) := by omega
  have hautI : rk ↥(autI hV A) + rk ↥(A ⊓ Subgroup.centralizer (V : Set G)) = rk ↥A :=
    (burnsideB610_rk_of_card_eq_mul (card_autI_mul_card_inf hV hAN).symm).symm
  have hsub := burnsideB610_rk_le_sum hAc
    (fun i => Subgroup.centralizer ((⁅V, X i⁆ : Subgroup G) : Set G)) S
  have hfaith : A ⊓ ⨅ i ∈ S, Subgroup.centralizer ((⁅V, X i⁆ : Subgroup G) : Set G) ≤
      A ⊓ Subgroup.centralizer (V : Set G) := by
    rintro a ⟨haA, ha⟩
    refine ⟨haA, hFam.faith hred (hT.1 (hA.1 haA)) fun i hi => ?_⟩
    exact Subgroup.mem_iInf.mp (Subgroup.mem_iInf.mp ha i) hi
  have hfr := rk_mono hfaith
  have himg : ∀ i ∈ S, rk ↥((D i).img A) +
      rk ↥(A ⊓ Subgroup.centralizer ((⁅V, X i⁆ : Subgroup G) : Set G)) = rk ↥A :=
    fun i hi => burnsideB610_rk_img (D i) (hFam.ker i hi) (hAnLV i hi)
  have hsum_eq : ∑ i ∈ S, (rk ↥A - rk ↥(A ⊓ Subgroup.centralizer
      ((⁅V, X i⁆ : Subgroup G) : Set G))) = ∑ i ∈ S, rk ↥((D i).img A) :=
    Finset.sum_congr rfl fun i hi => by have := himg i hi; omega
  have hb : ∀ i ∈ S, rk ↥((D i).img A) ≤ rkIdx (fixV ((D i).img A)) := fun i hi =>
    burnsideB610_rk_img_le hn hF (D i) ((hFam.le i hi).trans hHV) hA.2.1
  have hbsum : ∑ i ∈ S, rk ↥((D i).img A) ≤ ∑ i ∈ S, rkIdx (fixV ((D i).img A)) :=
    Finset.sum_le_sum hb
  have hcount := hFam.sum_rkIdx_le hHV hAN hAX S subset_rfl
  have hWV := hFam.famW_le hHV
  have hcV : ∀ a ∈ burnsideB610_famW S X V, ∀ b ∈ V ⊓ Subgroup.centralizer (A : Set G),
      a * b = b * a := fun a ha b hb => B2F.isElemAbelian_comm hV (hWV ha) hb.1
  have hw1 := B2F.rk_sup_add_rk_inf_of_commute hcV
  have hw2 : burnsideB610_famW S X V ⊓ (V ⊓ Subgroup.centralizer (A : Set G)) =
      burnsideB610_famW S X V ⊓ Subgroup.centralizer (A : Set G) := by
    rw [← inf_assoc, inf_eq_left.mpr hWV]
  have hw3 : rk ↥(burnsideB610_famW S X V ⊔ (V ⊓ Subgroup.centralizer (A : Set G))) ≤ rk ↥V :=
    rk_mono (sup_le hWV inf_le_left)
  rw [hw2] at hw1
  have hfixA := B2F.rkIdx_fixV_autI hV hAN
  have hWdef : burnsideB610_famW S X V = ⨆ i ∈ S, (⁅V, X i⁆ : Subgroup G) := rfl
  rw [← hWdef] at hcount
  refine ⟨by omega, ?_, by omega, by omega⟩
  have hsumeq : ∑ i ∈ S, rk ↥((D i).img A) = ∑ i ∈ S, rkIdx (fixV ((D i).img A)) := by omega
  exact (Finset.sum_eq_sum_iff_of_le hb).mp hsumeq

end burnsideB610_Fam

end CFSG.Quasithin.B610T
