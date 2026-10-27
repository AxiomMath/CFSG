module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7CKCoordAAux3

public section

namespace CFSG.StandardType.HdRo7C

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private noncomputable def hdRo7CKCoordAux_zmodZpowersEquivB {G : Type} [Group G] [Finite G] {y : G} (p : ℕ)
    (hyp : y ^ p = 1) (hy : y ≠ 1) (hp : Nat.Prime p) :
    Multiplicative (ZMod p) ≃* Subgroup.zpowers y := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  let φ : Multiplicative (ZMod p) →* Subgroup.zpowers y :=
    { toFun := fun m => ⟨y ^ (Multiplicative.toAdd m).val,
        Subgroup.pow_mem _ (Subgroup.mem_zpowers y) (Multiplicative.toAdd m).val⟩
      map_one' := by ext; simp
      map_mul' := by
        intro a b
        ext
        show y ^ (Multiplicative.toAdd (a * b)).val =
          y ^ (Multiplicative.toAdd a).val * y ^ (Multiplicative.toAdd b).val
        rw [show Multiplicative.toAdd (a * b) =
            Multiplicative.toAdd a + Multiplicative.toAdd b from rfl,
          ZMod.val_add, ← pow_eq_pow_mod _ hyp, pow_add] }
  have hdom : Nat.card (Multiplicative (ZMod p)) = p := by
    rw [Nat.card_congr (Multiplicative.toAdd), Nat.card_zmod]
  have hcod : Nat.card ↥(Subgroup.zpowers y) = p := by
    rw [Nat.card_zpowers, orderOf_eq_prime hyp hy]
  have hne : φ.ker ≠ ⊤ := by
    intro h
    have h1 : φ (Multiplicative.ofAdd (1 : ZMod p)) = 1 := by
      have : Multiplicative.ofAdd (1 : ZMod p) ∈ φ.ker := by
        rw [h]; exact Subgroup.mem_top _
      exact MonoidHom.mem_ker.mp this
    have h2 : φ (Multiplicative.ofAdd (1 : ZMod p)) = ⟨y, Subgroup.mem_zpowers y⟩ := by
      apply Subtype.ext
      show y ^ (Multiplicative.toAdd (Multiplicative.ofAdd (1 : ZMod p))).val = y
      rw [show Multiplicative.toAdd (Multiplicative.ofAdd (1 : ZMod p)) = (1 : ZMod p) from rfl,
        ZMod.val_one, pow_one]
    rw [h2] at h1
    exact hy (congrArg Subtype.val h1)
  have hcardker : Nat.card φ.ker = 1 := by
    have hdvd : Nat.card φ.ker ∣ p := by
      have := Subgroup.card_subgroup_dvd_card φ.ker
      rwa [hdom] at this
    rcases (Nat.dvd_prime hp).mp hdvd with h1 | h1
    · exact h1
    · exfalso
      apply hne
      exact Subgroup.eq_top_of_card_eq _ (by rw [h1, hdom])
  have hinj : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff]
    exact Subgroup.eq_bot_of_card_eq _ hcardker
  have hrange : φ.range = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    have h := CFSG.StandardType.TableB.card_range_mul_card_ker φ
    rw [hcardker, mul_one, hdom] at h
    rw [h, hcod]
  exact MulEquiv.ofBijective φ ⟨hinj, MonoidHom.range_eq_top.mp hrange⟩

theorem hdRo7CKCoordAux_model
    (hRig : GGLabelRigidInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K)
    (hrow : GGResRowAt ggRowCorank2C p J K) :
    ∃ (n : ℕ) (hy : y ∈ Bs) (hx : x ∈ Bs) (τ : (Fin (n + 1) → Multiplicative (ZMod p)) ≃* ↥Bs),
      p = 3 ∧ 5 ≤ n ∧ τ (Pi.mulSingle 0 (Multiplicative.ofAdd (1 : ZMod p))) = ⟨y, hy⟩ ∧
      C2CoordModel p Bs K n τ ∧
      ∀ f : Fin (n + 1) → Multiplicative (ZMod p), ((τ f : ↥Bs) : G) ∈ K ↔ f 0 = 1 := by
  have hrow' : GGResRowAt ggRowCorank2C p J K := hrow
  obtain ⟨labJ, labK, hJ2, hK2, hHasJ, hHasK, hp3, htagJ, hnJ, htagK, hnK, hrank⟩ := hrow'
  have hp : Nat.Prime p := hH.1.tableB_facts.1
  have hp2 : p ≠ 2 := by omega
  have hyB : y ∈ B := hH.2.2.2.2.1.1.2.1
  have hy0 : y ∈ Bs := hH.1.2.1.1 hyB
  have hx0 : x ∈ Bs := hH.1.tableB_facts.2.2.1
  obtain ⟨R, hRgrp, I, θ, hBsN, hperf, hTSC, hCP, hcenter, hI, hBs3⟩ :=
    hdRo7CKCoordAux_torus_data hRig hH hrow
  letI : Group R := hRgrp
  have hZK : Subgroup.center ↥K = ⊥ :=
    hdRo7CKCoordAux_center_K_eq_bot hH hrow
  have hinner := hdRo7CKCoordAux_hinner p B Bs x L D J y K hH R I θ hI hZK hBsN hBs3
  obtain ⟨k, τT, hτTinj, hτTsurj, hsgn, hperm, hnorm⟩ :=
    hdRo7CKCoordAux_signedData_K hRig hH hrow R θ hZK hBsN hinner hTSC
  obtain ⟨labK', hlabK', hKlab', htagK', hnK1', h5K', hcard_inf'⟩ :=
    hdRo7CKCoordAux_card_inf_pow hRig hH hrow hBsN hinner
  have hk : k = labK'.rank :=
    hdRo7CLCoordAux_k_eq_of_card p k labK'.rank hp.two_le τT ⟨hτTinj, hτTsurj⟩ hcard_inf'
  have hk5 : 5 ≤ k := by rw [hk]; exact h5K'
  have hCeq : Bs ⊓ Subgroup.centralizer (K : Set G) = Subgroup.zpowers y :=
    hdRo7CKCoordAux_bstar_centralizer_eq hRig hH hrow hBsN hinner
  let τC : Multiplicative (ZMod p) ≃* ↥(Bs ⊓ Subgroup.centralizer (K : Set G)) :=
    (hdRo7CKCoordAux_zmodZpowersEquivB (y := y) p (hdRo7CKCoordAux_y_pow_eq_one hH)
      (hdRo7CKCoordAux_y_ne_one hH) hp).trans (MulEquiv.subgroupCongr hCeq.symm)
  have hC : ∀ m : Multiplicative (ZMod p), (τC m : G) = y ^ (Multiplicative.toAdd m).val := by
    intro m
    simp only [τC, MulEquiv.trans_apply, MulEquiv.subgroupCongr_apply]
    rfl
  let Φ : ↥(Bs ⊓ K) × ↥(Bs ⊓ Subgroup.centralizer (K : Set G)) ≃* ↥Bs :=
    hdRo7CKCoordAux_split_equiv p B Bs x L D J y K hH hZK hBsN hinner
  have hΦ : ∀ (t : ↥(Bs ⊓ K)) (c : ↥(Bs ⊓ Subgroup.centralizer (K : Set G))),
      (Φ (t, c) : G) = (t : G) * (c : G) := fun t c =>
    congrArg Subtype.val
      (hdRo7CKCoordAux_split_equiv_apply p B Bs x L D J y K hH hZK hBsN hinner t c)
  have hKy : ∀ g : ↥K, (g : G) * y * (g : G)⁻¹ = y := by
    intro g
    have hcomm := Subgroup.mem_centralizer_singleton_iff.mp
      (hH.2.2.2.2.1.1.2.2.2.1 g.2)
    rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
  let τ : (Fin (k + 1) → Multiplicative (ZMod p)) ≃* ↥Bs :=
    hdRo7CLCoordAux_tau p B Bs y K k τT ⟨hτTinj, hτTsurj⟩ τC Φ
  refine ⟨k, hy0, hx0, τ, hp3, hk5, ?_, ?_, ?_⟩
  · exact (hdRo7CLCoordAux_tau_mulSingle p B Bs y K k τT ⟨hτTinj, hτTsurj⟩ τC Φ hΦ hC hp
      (hdRo7CKCoordAux_y_pow_eq_one hH) hy0).choose_spec
  · exact hdRo7CLCoordAux_coordModel_tau_of_dirs p B Bs y K k τT ⟨hτTinj, hτTsurj⟩ τC Φ hΦ hC
      hsgn hperm hnorm hKy (hdRo7CKCoordAux_y_pow_eq_one hH) (hdRo7CKCoordAux_y_ne_one hH) hp hy0
  · intro f
    have htau : ((τ f : ↥Bs) : G) =
        (τT (Fin.tail f) : G) * y ^ (Multiplicative.toAdd (f 0)).val :=
      hdRo7CLCoordAux_tau_apply p B Bs y K k τT ⟨hτTinj, hτTsurj⟩ τC Φ hΦ hC f
    constructor
    · intro hmemK
      have htK : (τT (Fin.tail f) : G) ∈ K := (τT (Fin.tail f)).2.2
      have hzK : y ^ (Multiplicative.toAdd (f 0)).val ∈ K := by
        rw [htau] at hmemK
        have heq : y ^ (Multiplicative.toAdd (f 0)).val =
            (τT (Fin.tail f) : G)⁻¹ *
              ((τT (Fin.tail f) : G) * y ^ (Multiplicative.toAdd (f 0)).val) := by group
        rw [heq]
        exact K.mul_mem (K.inv_mem htK) hmemK
      have hzC : y ^ (Multiplicative.toAdd (f 0)).val ∈
          Subgroup.centralizer (K : Set G) := by
        have hyC : y ∈ Bs ⊓ Subgroup.centralizer (K : Set G) := by
          rw [hCeq]; exact Subgroup.mem_zpowers y
        exact Subgroup.pow_mem _ hyC.2 _
      have hcenter : (⟨y ^ (Multiplicative.toAdd (f 0)).val, hzK⟩ : ↥K) ∈
          Subgroup.center ↥K := by
        rw [Subgroup.mem_center_iff]
        intro g
        apply Subtype.ext
        exact Subgroup.mem_centralizer_iff.mp hzC (g : G) g.2
      rw [hZK] at hcenter
      have hz1 : y ^ (Multiplicative.toAdd (f 0)).val = 1 := by
        have h1 : (⟨y ^ (Multiplicative.toAdd (f 0)).val, hzK⟩ : ↥K) = 1 :=
          Subgroup.mem_bot.mp hcenter
        simpa using congrArg Subtype.val h1
      have horder : orderOf y = p :=
        orderOf_eq_prime (hdRo7CKCoordAux_y_pow_eq_one hH) (hdRo7CKCoordAux_y_ne_one hH)
      have hdvd : p ∣ (Multiplicative.toAdd (f 0)).val := by
        have h := orderOf_dvd_iff_pow_eq_one.mpr hz1
        rwa [horder] at h
      haveI : NeZero p := ⟨hp.ne_zero⟩
      have hzero : (Multiplicative.toAdd (f 0)).val = 0 :=
        Nat.eq_zero_of_dvd_of_lt hdvd (ZMod.val_lt _)
      have htoAdd : Multiplicative.toAdd (f 0) = 0 := (ZMod.val_eq_zero _).mp hzero
      apply Multiplicative.toAdd.injective
      rw [htoAdd]
      rfl
    · intro hf0
      have hy1 : y ^ (Multiplicative.toAdd (f 0)).val = 1 := by
        rw [hf0]
        simp
      rw [htau, hy1, mul_one]
      exact (τT (Fin.tail f)).2.2

end CFSG.StandardType.HdRo7C

end
