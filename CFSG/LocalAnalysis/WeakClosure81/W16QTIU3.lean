module

public import CFSG.LocalAnalysis.WeakClosure81.W16QTIPairB
public import CFSG.LocalAnalysis.WeakClosure81.W16QTIX
public import CFSG.LocalAnalysis.WeakClosure81.W16QTIMod
public import CFSG.LocalAnalysis.WeakClosure81.W16QTINat

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.QuasithinUnique.Setup.Campbell
open CFSG.SignalizerFunctorTheorem.Quadratic
open CFSG.CGT.Timmesfeld75
open Subgroup

variable {G : Type} [Group G] [Finite G]

private theorem w16q_iota_one {K : Subgroup G} {X : Type} [Group X] {φ : ↥K →* X}
    {B : Subgroup X} {E : Subgroup G} (D : ModDataB φ B E) : D.ι 1 = 0 := by
  have h : D.ι 1 = D.ι 1 + D.ι 1 := by
    simpa using D.ι_mul 1 E.one_mem 1 E.one_mem
  exact add_left_cancel (show D.ι 1 + D.ι 1 = D.ι 1 + 0 by rw [add_zero]; exact h.symm)

private theorem w16q_iota_inv {K : Subgroup G} {X : Type} [Group X] {φ : ↥K →* X}
    {B : Subgroup X} {E : Subgroup G} (D : ModDataB φ B E) {e : G} (he : e ∈ E) :
    D.ι e⁻¹ = -D.ι e := by
  have h : D.ι (e * e⁻¹) = D.ι e + D.ι e⁻¹ := D.ι_mul e he e⁻¹ (E.inv_mem he)
  rw [mul_inv_cancel, w16q_iota_one D] at h
  exact eq_neg_of_add_eq_zero_left (by rw [add_comm]; exact h.symm)

private theorem w16q_iota_injOn {K : Subgroup G} {X : Type} [Group X] {φ : ↥K →* X}
    {B : Subgroup X} {E : Subgroup G} (D : ModDataB φ B E) :
    Set.InjOn D.ι (E : Set G) := by
  intro e he e' he' h
  have hmem : e * e'⁻¹ ∈ E := E.mul_mem he (E.inv_mem he')
  have h0 : D.ι (e * e'⁻¹) = 0 := by
    rw [D.ι_mul e he e'⁻¹ (E.inv_mem he'), w16q_iota_inv D he', h, add_neg_cancel]
  have h1 : e * e'⁻¹ = 1 := D.ι_eq_zero (e * e'⁻¹) hmem h0
  rwa [mul_inv_eq_one] at h1

private theorem w16q_card_conjSubgroup {A : Subgroup G} (g : G) :
    Nat.card (conjSubgroup A g) = Nat.card A := by
  rw [CFSG.Quasithin.conjSubgroup]
  exact Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective

private theorem w16q_eq_of_subgroupOf_eq {A C B : Subgroup G} (hA : A ≤ B) (hC : C ≤ B)
    (h : A.subgroupOf B = C.subgroupOf B) : A = C := by
  have hinf : A ⊓ B = C ⊓ B := Subgroup.subgroupOf_inj.mp h
  calc A = A ⊓ B := (inf_eq_left.mpr hA).symm
    _ = C ⊓ B := hinf
    _ = C := inf_eq_left.mpr hC

namespace DichCfg

variable {M V₀ V U S H : Subgroup G} {X : Type} [Group X] {φ : ↥(conjClosure V H) →* X}

theorem exists_mSub_eq_mul (d : DichCfg M V₀ V U S H φ) [Finite X] (hK : KGroup1616Input)
    (hn : 1 < E3.mQuot V (iSub16 V H)) (hX : IsU3Shape X (E3.mQuot V (iSub16 V H))) :
    ∃ s : ℕ, mSub V₀ = E3.mQuot V (iSub16 V H) * s := by
  let n : ℕ := E3.mQuot V (iSub16 V H)
  let Y : Subgroup X := SevenK.barSub (conjClosure V H) φ V
  have hYc : Nat.card Y = 2 ^ n := d.shape.1
  have hYel : IsElemAbelian 2 Y := d.isElemAbelian_barSub
  obtain ⟨g, hgK, hgM⟩ := Set.not_subset.1 d.cfg.not_conjClosure_le
  let yk : ↥(conjClosure V H) := ⟨g, hgK⟩
  have hne : conjSubgroup V₀ ((1 : ↥(conjClosure V H)) : G) ≠ conjSubgroup V₀ (yk : G) := by
    intro h
    apply hgM
    have h' : conjSubgroup V₀ (yk : G) = V₀ := by
      rw [← h]
      simpa using CFSG.Quasithin.conjSubgroup_one V₀
    have hN : g ∈ normalizer (V₀ : Set G) := conjSubgroup_eq_iff_mem_normalizer.1 h'
    rwa [d.cfg.cex.hyp.normalizer₀] at hN
  have hφne : conjSubgroup Y (φ (1 : ↥(conjClosure V H))) ≠ conjSubgroup Y (φ yk) := by
    intro h
    exact hne ((d.conj_V₀_eq_iff (1 : ↥(conjClosure V H)) yk).2 h)
  have hcomm := not_comm_of_ne_conj hK hn hX hYel hYc hφne
  have hP : IsL2Pair ↥(yConj V H φ (1 : ↥(conjClosure V H)) ⊔ yConj V H φ yk)
      ((yConj V H φ (1 : ↥(conjClosure V H))).subgroupOf
        (yConj V H φ (1 : ↥(conjClosure V H)) ⊔ yConj V H φ yk)) (2 ^ n) :=
    isL2Pair_conj hK hn hX hYel hYc hφne
  obtain ⟨D⟩ := d.exists_modDataB (1 : ↥(conjClosure V H)) yk
  obtain ⟨P₀, hP₀⟩ := hP.exists_sylow_eq
  let B : Subgroup X := yConj V H φ (1 : ↥(conjClosure V H)) ⊔ yConj V H φ yk
  let H' : Subgroup ↥B := (yConj V H φ yk).subgroupOf B
  have hHle : yConj V H φ yk ≤ B := le_sup_right
  have hH2 : IsPGroup 2 H' := by
    have hyel : IsElemAbelian 2 (yConj V H φ yk) :=
      hYel.map (MulAut.conj (φ yk)⁻¹).toMonoidHom
    exact (hyel.isPGroup).of_equiv (Subgroup.subgroupOfEquivOfLe hHle).symm
  obtain ⟨R, hHR⟩ := hH2.exists_le_sylow
  have hHcard : Nat.card H' = 2 ^ n := by
    have h1 : Nat.card H' = Nat.card (yConj V H φ yk) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHle).toEquiv
    rw [h1]
    change Nat.card (conjSubgroup Y (φ yk)) = 2 ^ n
    rw [CFSG.Quasithin.conjSubgroup,
      Subgroup.card_map_of_injective (MulAut.conj (φ yk)⁻¹).injective, hYc]
  have hRcard : Nat.card (R : Subgroup ↥B) = 2 ^ n := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hP0card : Nat.card (P₀ : Subgroup ↥B) = 2 ^ n := by
      rw [hP₀]
      exact hP.card_eq
    rw [Sylow.card_eq_multiplicity (p := 2) R,
      ← Sylow.card_eq_multiplicity (p := 2) P₀, hP0card]
  have hHR' : H' = (R : Subgroup ↥B) :=
    Subgroup.eq_of_le_of_card_ge hHR (by simp [hRcard, hHcard])
  have hPne : P₀ ≠ R := by
    intro h
    apply hφne
    have h1 : (P₀ : Subgroup ↥B) = (R : Subgroup ↥B) :=
      congrArg (fun S : Sylow 2 ↥B => (S : Subgroup ↥B)) h
    rw [hP₀, ← hHR'] at h1
    exact w16q_eq_of_subgroupOf_eq le_sup_left le_sup_right h1
  obtain ⟨u, hu, hu1, v, hv, hv1, huv⟩ :=
    hP.exists_mul_orderOf_three_of_sylow (P := P₀) (Q := R) hPne
  have huP : u ∈ (yConj V H φ (1 : ↥(conjClosure V H))).subgroupOf
      (yConj V H φ (1 : ↥(conjClosure V H)) ⊔ yConj V H φ yk) := hP₀ ▸ hu
  have huy : (u : X) ∈ yConj V H φ (1 : ↥(conjClosure V H)) :=
    Subgroup.mem_subgroupOf.mp huP
  have hvH : v ∈ H' := hHR'.symm ▸ hv
  have hvy : (v : X) ∈ yConj V H φ yk := Subgroup.mem_subgroupOf.mp hvH
  have hD : ∃ D' : Subgroup ↥B, Nat.card D' = 3 ∧
      ∀ w : D.W, (∀ d ∈ D', D.ρ d w = w) → w = 0 := by
    refine ⟨Subgroup.zpowers (u * v), ?_, ?_⟩
    · rw [show Nat.card (Subgroup.zpowers (u * v)) = orderOf (u * v) from
        Nat.card_zpowers (u * v), huv]
    · intro w hw
      have huvD : u * v ∈ Subgroup.zpowers (u * v) :=
        Subgroup.mem_zpowers_iff.mpr ⟨1, zpow_one _⟩
      have h1 : D.ρ u (D.ρ v w) = w := by
        have h0 : D.ρ (u * v) w = w := hw (u * v) huvD
        rwa [map_mul] at h0
      exact eq_zero_of_mul_fixed d hcomm hne D huy hvy (fun h => hu1 (Subtype.ext h))
        (fun h => hv1 (Subtype.ext h)) (Subgroup.mem_sup_left huy) (Subgroup.mem_sup_right hvy)
        w h1
  obtain ⟨s, hs⟩ := exists_finrank_eq_of_pair (n := n) (by omega) hP D.ρ hD
  have hV₀card : Nat.card V₀ = 2 ^ mSub V₀ :=
    card_eq_two_pow_mSub (d.cfg.cex.hyp.isPGroup.to_le d.cfg.cex.hyp.h6.le)
  have hfin : Module.finrank (ZMod 2) D.W = 2 * mSub V₀ := by
    have h1 := d.natCard_modDataB hne D
    have h3 := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := D.W)
    rw [Nat.card_zmod, h1, hV₀card, ← pow_mul] at h3
    exact (Nat.pow_right_injective (le_refl 2) h3).symm.trans (by ring)
  refine ⟨s, ?_⟩
  have h2 : 2 * mSub V₀ = 2 * (n * s) := by rw [← hfin, hs]; ring
  exact Nat.mul_left_cancel (by norm_num) h2

private theorem w16q_exists_conj_mul_of_ne (d : DichCfg M V₀ V U S H φ) [Finite X]
    (hK : KGroup1616Input) (hn : 1 < E3.mQuot V (iSub16 V H))
    (hX : IsU3Shape X (E3.mQuot V (iSub16 V H)))
    (hm : mSub V₀ = E3.mQuot V (iSub16 V H)) {x y : ↥(conjClosure V H)}
    (hne : conjSubgroup V₀ (x : G) ≠ conjSubgroup V₀ (y : G)) {a b : G}
    (ha : a ∈ conjSubgroup V₀ (x : G)) (hb : b ∈ conjSubgroup V₀ (y : G)) :
    ∃ z : ↥(conjClosure V H), a * b ∈ conjSubgroup V₀ (z : G) := by
  let n : ℕ := E3.mQuot V (iSub16 V H)
  let Y : Subgroup X := SevenK.barSub (conjClosure V H) φ V
  let B : Subgroup X := yConj V H φ x ⊔ yConj V H φ y
  let P : Subgroup ↥B := (yConj V H φ x).subgroupOf B
  have hYc : Nat.card Y = 2 ^ n := d.shape.1
  have hYel : IsElemAbelian 2 Y := d.isElemAbelian_barSub
  have hφne : conjSubgroup Y (φ x) ≠ conjSubgroup Y (φ y) := by
    intro h
    exact hne ((d.conj_V₀_eq_iff x y).2 h)
  have hcomm := not_comm_of_ne_conj hK hn hX hYel hYc hφne
  have hP : IsL2Pair ↥B P (2 ^ n) := isL2Pair_conj hK hn hX hYel hYc hφne
  obtain ⟨D⟩ := d.exists_modDataB x y
  obtain ⟨P₀, hP₀⟩ := hP.exists_sylow_eq
  let H' : Subgroup ↥B := (yConj V H φ y).subgroupOf B
  have hHle : yConj V H φ y ≤ B := le_sup_right
  have hH2 : IsPGroup 2 H' := by
    have hyel : IsElemAbelian 2 (yConj V H φ y) :=
      hYel.map (MulAut.conj (φ y)⁻¹).toMonoidHom
    exact (hyel.isPGroup).of_equiv (Subgroup.subgroupOfEquivOfLe hHle).symm
  obtain ⟨R, hHR⟩ := hH2.exists_le_sylow
  have hHcard : Nat.card H' = 2 ^ n := by
    have h1 : Nat.card H' = Nat.card (yConj V H φ y) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHle).toEquiv
    rw [h1]
    change Nat.card (conjSubgroup Y (φ y)) = 2 ^ n
    rw [CFSG.Quasithin.conjSubgroup,
      Subgroup.card_map_of_injective (MulAut.conj (φ y)⁻¹).injective, hYc]
  have hRcard : Nat.card (R : Subgroup ↥B) = 2 ^ n := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hP0card : Nat.card (P₀ : Subgroup ↥B) = 2 ^ n := by
      rw [hP₀]
      exact hP.card_eq
    rw [Sylow.card_eq_multiplicity (p := 2) R,
      ← Sylow.card_eq_multiplicity (p := 2) P₀, hP0card]
  have hHR' : H' = (R : Subgroup ↥B) :=
    Subgroup.eq_of_le_of_card_ge hHR (by simp [hRcard, hHcard])
  have hPne : P₀ ≠ R := by
    intro h
    apply hφne
    have h1 : (P₀ : Subgroup ↥B) = (R : Subgroup ↥B) :=
      congrArg (fun S : Sylow 2 ↥B => (S : Subgroup ↥B)) h
    rw [hP₀, ← hHR'] at h1
    exact w16q_eq_of_subgroupOf_eq le_sup_left le_sup_right h1
  obtain ⟨u, hu, hu1, v, hv, hv1, huv⟩ :=
    hP.exists_mul_orderOf_three_of_sylow (P := P₀) (Q := R) hPne
  have huP : u ∈ P := hP₀ ▸ hu
  have huy : (u : X) ∈ yConj V H φ x := Subgroup.mem_subgroupOf.mp huP
  have hvH : v ∈ H' := hHR'.symm ▸ hv
  have hvy : (v : X) ∈ yConj V H φ y := Subgroup.mem_subgroupOf.mp hvH
  have hV₀card : Nat.card V₀ = 2 ^ mSub V₀ :=
    card_eq_two_pow_mSub (d.cfg.cex.hyp.isPGroup.to_le d.cfg.cex.hyp.h6.le)
  have hW : Nat.card D.W = (2 ^ n) ^ 2 := by
    rw [d.natCard_modDataB hne D, hV₀card, hm]
  have hST : ({w : D.W | ∀ a' ∈ P, D.ρ a' w = w} : Set D.W) =
      (D.ι '' ((conjSubgroup V₀ (x : G) : Subgroup G) : Set G) : Set D.W) := by
    ext w
    constructor
    · intro hw
      have ha1 : (u : X) ≠ 1 := fun h => hu1 (Subtype.ext h)
      exact (fixed_iff d hcomm D (Or.inl rfl) huy ha1 (Subgroup.mem_sup_left huy) w).1
        (hw u huP)
    · rintro ⟨e, he, hιe⟩
      intro a' ha'
      by_cases ha'1 : a' = 1
      · rw [ha'1, map_one]
        rfl
      · have ha'y : (a' : X) ∈ yConj V H φ x := Subgroup.mem_subgroupOf.mp ha'
        have ha'X1 : (a' : X) ≠ 1 := fun h => ha'1 (Subtype.ext h)
        exact (fixed_iff d hcomm D (Or.inl rfl) ha'y ha'X1 (Subgroup.mem_sup_left ha'y) w).2
          ⟨e, he, hιe⟩
  have hfix : Nat.card {w : D.W // ∀ a' ∈ P, D.ρ a' w = w} = 2 ^ n := by
    change ({w : D.W | ∀ a' ∈ P, D.ρ a' w = w} : Set D.W).ncard = 2 ^ n
    rw [hST]
    have hsub : ((conjSubgroup V₀ (x : G) : Subgroup G) : Set G) ⊆
        ((conjPairSub V₀ x y : Subgroup G) : Set G) := fun e he => Subgroup.mem_sup_left he
    rw [Set.InjOn.ncard_image (Set.InjOn.mono hsub (w16q_iota_injOn D)), ← Nat.card_coe_set_eq]
    change Nat.card (conjSubgroup V₀ (x : G)) = 2 ^ n
    rw [w16q_card_conjSubgroup, hV₀card, hm]
  have hB : ∀ w : D.W, (∀ bB : ↥B, D.ρ bB w = w) → w = 0 := by
    intro w hw
    have h1 : D.ρ u (D.ρ v w) = w := by
      have h0 : D.ρ (u * v) w = w := hw (u * v)
      rwa [map_mul] at h0
    exact eq_zero_of_mul_fixed d hcomm hne D huy hvy (fun h => hu1 (Subtype.ext h))
      (fun h => hv1 (Subtype.ext h)) (Subgroup.mem_sup_left huy) (Subgroup.mem_sup_right hvy)
      w h1
  obtain ⟨gB, hgB⟩ := exists_fixing_conj_of_card_eq (n := n) hn (B := ↥B) (P := P) hP D.ρ
    hW hfix hB (D.ι (a * b))
  have hfixvec : ∃ e ∈ conjSubgroup V₀ (x : G), D.ι e = D.ρ gB (D.ι (a * b)) := by
    have ha1 : (u : X) ≠ 1 := fun h => hu1 (Subtype.ext h)
    exact (fixed_iff d hcomm D (Or.inl rfl) huy ha1 (Subgroup.mem_sup_left huy)
      (D.ρ gB (D.ι (a * b)))).1 (hgB u huP)
  obtain ⟨e, he, hιe⟩ := hfixvec
  obtain ⟨k₀, hk₀φ⟩ := d.bar.surjective ((gB⁻¹ : ↥B) : X)
  have hk₀B : φ k₀ ∈ B := by
    rw [hk₀φ]
    simpa only [Subgroup.coe_inv] using B.inv_mem gB.2
  have hgBeq : (⟨φ k₀, hk₀B⟩ : ↥B) = gB⁻¹ := by
    apply Subtype.ext
    exact hk₀φ
  have heE : e ∈ conjPairSub V₀ x y := Subgroup.mem_sup_left he
  have hρk : D.ρ ⟨φ k₀, hk₀B⟩ (D.ι e) = D.ι ((k₀ : G) * e * (k₀ : G)⁻¹) :=
    D.ρ_ι k₀ hk₀B e heE
  have hstep : D.ι ((k₀ : G) * e * (k₀ : G)⁻¹) = D.ρ gB⁻¹ (D.ι e) := by
    rw [← hρk, hgBeq]
  have hcancel : D.ρ gB⁻¹ (D.ρ gB (D.ι (a * b))) = D.ι (a * b) := by
    have h1 : D.ρ (gB⁻¹ * gB) (D.ι (a * b)) = D.ι (a * b) := by
      rw [inv_mul_cancel, map_one]
      rfl
    rwa [map_mul] at h1
  have hkey : D.ι ((k₀ : G) * e * (k₀ : G)⁻¹) = D.ι (a * b) := by
    rw [hstep, hιe, hcancel]
  have hkE : (k₀ : G) * e * (k₀ : G)⁻¹ ∈ conjPairSub V₀ x y := by
    exact (Subgroup.mem_normalizer_iff.mp (d.mem_normalizer_conjPairSub x y k₀ hk₀B) e).1 heE
  have habE : a * b ∈ conjPairSub V₀ x y :=
    Subgroup.mul_mem _ (Subgroup.mem_sup_left ha) (Subgroup.mem_sup_right hb)
  have hab_eq : a * b = (k₀ : G) * e * (k₀ : G)⁻¹ :=
    (w16q_iota_injOn D) habE hkE hkey.symm
  refine ⟨x * k₀⁻¹, ?_⟩
  rw [mem_conjSubgroup_iff, hab_eq]
  have hxe : (x : G) * e * (x : G)⁻¹ ∈ V₀ := mem_conjSubgroup_iff.mp he
  convert hxe using 1
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  group

theorem exists_mem_conj_mul (d : DichCfg M V₀ V U S H φ) [Finite X] (hK : KGroup1616Input)
    (hn : 1 < E3.mQuot V (iSub16 V H)) (hX : IsU3Shape X (E3.mQuot V (iSub16 V H)))
    (hm : mSub V₀ = E3.mQuot V (iSub16 V H)) (x y : ↥(conjClosure V H)) {a b : G}
    (ha : a ∈ conjSubgroup V₀ (x : G)) (hb : b ∈ conjSubgroup V₀ (y : G)) :
    ∃ z : ↥(conjClosure V H), a * b ∈ conjSubgroup V₀ (z : G) := by
  by_cases hxy : conjSubgroup V₀ (x : G) = conjSubgroup V₀ (y : G)
  · refine ⟨x, ?_⟩
    have hb' : b ∈ conjSubgroup V₀ (x : G) := by rwa [← hxy] at hb
    exact Subgroup.mul_mem _ ha hb'
  · exact w16q_exists_conj_mul_of_ne d hK hn hX hm hxy ha hb

end DichCfg

end CFSG.LocalAnalysis.WeakClosure81

end
