module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ASevenStructureFacts
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ASevenOrderThreeKleinFourThreeCycle
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.KleinFourCentralizerTransport
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

noncomputable section

namespace CFSG.GorensteinWalter

private abbrev A7P := alternatingGroup (Fin 7)
private abbrev aPerm := Equiv.Perm (Fin 7)
private abbrev ASupp := {x : Fin 7 // x ∈ (a7a : aPerm).support}
private abbrev ACompl := {x : Fin 7 // x ∉ (a7a : aPerm).support}


set_option maxRecDepth 1000000 in
private theorem support_inverter_has_negative_sign
    (r a : Equiv.Perm ASupp)
    (ha3 : a.support.card = 3)
    (hra : r * a * r⁻¹ = a⁻¹) :
    Equiv.Perm.sign r = -1 := by
  revert r a
  decide

set_option maxRecDepth 1000000 in
private theorem odd_involution_on_complement_isSwap
    (r : Equiv.Perm ACompl)
    (hr2 : r ^ 2 = 1)
    (hrsign : Equiv.Perm.sign r = -1) :
    r.support.card = 2 := by
  revert r
  decide

set_option maxRecDepth 1000000 in
private theorem odd_involution_on_support_isSwap
    (r : Equiv.Perm ASupp)
    (hr2 : r ^ 2 = 1)
    (hrsign : Equiv.Perm.sign r = -1) :
    r.support.card = 2 := by
  revert r
  decide

set_option maxRecDepth 1000000 in
private theorem involution_commuting_threeCycle_on_support_eq_one
    (r a : Equiv.Perm ASupp)
    (hr2 : r ^ 2 = 1)
    (ha3 : a.support.card = 3)
    (hra : r * a = a * r) : r = 1 := by
  revert r a
  decide

private theorem a7a_threeCycle :
    Equiv.Perm.IsThreeCycle (a7a : aPerm) := by
  exact card_support_eq_three_iff.mp (by decide)

private theorem aCompl_card : Fintype.card ACompl = 4 := by
  change ((a7a : aPerm).supportᶜ).card = 4
  rw [Finset.card_compl, a7a_threeCycle.card_support]
  decide

private theorem threeCycle_not_mem_a7U_of_support_le_compl
    (b : A7P) (hb3 : Equiv.Perm.IsThreeCycle (b : aPerm))
    (hbSupport : (b : aPerm).support ⊆ (a7a : aPerm).supportᶜ) :
    b ∉ a7U := by
  have hcardSupp : (b : aPerm).support.card = 3 := hb3.card_support
  obtain ⟨a, ha⟩ : (b : aPerm).support.Nonempty :=
    Finset.card_pos.mp (by omega)
  have haNot : a ∉ (a7a : aPerm).support :=
    Finset.mem_compl.mp (hbSupport ha)
  have haFix : (a7a : aPerm) a = a := Equiv.Perm.notMem_support.mp haNot
  have hbMove : (b : aPerm) a ≠ a := Equiv.Perm.mem_support.mp ha
  intro hbU
  change b = 1 ∨ b = a7a ∨ b = a7a ^ 2 at hbU
  rcases hbU with hb1 | hba | hba2
  · exact hb3.ne_one (congrArg Subtype.val hb1)
  · apply hbMove
    exact (Equiv.congr_fun (congrArg Subtype.val hba) a).trans haFix
  · apply hbMove
    calc
      (b : aPerm) a = ((a7a : A7P) ^ 2 : A7P).1 a :=
        Equiv.congr_fun (congrArg Subtype.val hba2) a
      _ = a := by simp [pow_two, haFix]

private def complementConjugate
    (r : Equiv.Perm ACompl) (v : A7P) : A7P :=
  ⟨Equiv.Perm.ofSubtype r * (v : aPerm) * (Equiv.Perm.ofSubtype r)⁻¹, by
    change Equiv.Perm.sign
      (Equiv.Perm.ofSubtype r * (v : aPerm) *
        (Equiv.Perm.ofSubtype r)⁻¹) = 1
    rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_mul,
      Equiv.Perm.sign_inv, Equiv.Perm.sign_ofSubtype]
    rw [v.2]
    rcases Int.units_eq_one_or (Equiv.Perm.sign r) with h | h <;>
      rw [h] <;> norm_num⟩

set_option maxRecDepth 1000000 in
private theorem complementConjugate_mem_a7V
    (r : Equiv.Perm ACompl) {v : A7P} (hv : v ∈ a7V) :
    complementConjugate r v ∈ a7V := by
  change v = 1 ∨ v = a7t ∨ v = a7u ∨ v = a7t * a7u at hv
  rcases hv with rfl | rfl | rfl | rfl
  all_goals
    change complementConjugate r _ = 1 ∨
      complementConjugate r _ = a7t ∨
        complementConjugate r _ = a7u ∨
          complementConjugate r _ = a7t * a7u
  all_goals revert r
  all_goals decide

private def complementPermutation
    (r : Equiv.Perm ACompl) (hr : Equiv.Perm.sign r = 1) : A7P :=
  ⟨Equiv.Perm.ofSubtype r, by
    change Equiv.Perm.sign (Equiv.Perm.ofSubtype r) = 1
    rw [Equiv.Perm.sign_ofSubtype, hr]⟩

private theorem complementPermutation_mem_normalizer_a7V
    (r : Equiv.Perm ACompl) (hr : Equiv.Perm.sign r = 1) :
    complementPermutation r hr ∈ Subgroup.normalizer (a7V : Set A7P) := by
  rw [Subgroup.mem_normalizer_iff]
  intro v
  constructor
  · intro hv
    have hc := complementConjugate_mem_a7V r hv
    have heq : complementConjugate r v =
        complementPermutation r hr * v * (complementPermutation r hr)⁻¹ := by
      apply Subtype.ext
      rfl
    exact heq ▸ hc
  · intro hv
    let q : A7P := complementPermutation r hr * v *
      (complementPermutation r hr)⁻¹
    have hqV : q ∈ a7V := hv
    have hc := complementConjugate_mem_a7V r⁻¹ hqV
    have hcv : complementConjugate r⁻¹ q = v := by
      apply Subtype.ext
      dsimp [complementConjugate, q, complementPermutation]
      simp only [map_inv]
      group
    rwa [hcv] at hc

set_option maxRecDepth 1000000 in
private theorem even_involution_complement_mem_a7V
    (r : Equiv.Perm ACompl)
    (hr2 : r ^ 2 = 1)
    (hrsign : Equiv.Perm.sign r = 1) :
    complementPermutation r hrsign ∈ a7V := by
  have hperm :
      Equiv.Perm.ofSubtype r = (1 : aPerm) ∨
        Equiv.Perm.ofSubtype r = (a7t : aPerm) ∨
          Equiv.Perm.ofSubtype r = (a7u : aPerm) ∨
            Equiv.Perm.ofSubtype r = (a7t * a7u : A7P) := by
    revert r
    decide
  change complementPermutation r hrsign = 1 ∨
    complementPermutation r hrsign = a7t ∨
      complementPermutation r hrsign = a7u ∨
        complementPermutation r hrsign = a7t * a7u
  rcases hperm with h | h | h | h
  · exact Or.inl (Subtype.ext h)
  · exact Or.inr (Or.inl (Subtype.ext h))
  · exact Or.inr (Or.inr (Or.inl (Subtype.ext h)))
  · exact Or.inr (Or.inr (Or.inr (Subtype.ext h)))

private def blockSwap
    (p q r : ASupp) (x y z : ACompl) : aPerm :=
  Equiv.swap p.1 x.1 * Equiv.swap q.1 y.1 * Equiv.swap r.1 z.1

set_option maxRecDepth 1000000 in
private theorem blockSwap_sign
    (p q r : ASupp) (x y z : ACompl) :
    Equiv.Perm.sign (blockSwap p q r x y z) = -1 := by
  have cross (u : ASupp) (v : ACompl) : u.1 ≠ v.1 := by
    intro huv
    exact v.2 (huv ▸ u.2)
  simp [blockSwap, Equiv.Perm.sign_mul, cross]

set_option maxRecDepth 1000000 in
private theorem blockSwap_commutes
    (p q r : ASupp) (x y z : ACompl)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    blockSwap p q r x y z *
        ((Equiv.swap p q).subtypeCongr (Equiv.swap x y)) =
      ((Equiv.swap p q).subtypeCongr (Equiv.swap x y)) *
        blockSwap p q r x y z := by
  revert p q r x y z
  decide

set_option maxRecDepth 1000000 in
private theorem blockSwap_mul_supportSwap_sq
    (p q r : ASupp) (x y z : ACompl)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    (blockSwap p q r x y z *
        Equiv.Perm.ofSubtype (Equiv.swap p q)) ^ 2 =
      (Equiv.swap p q).subtypeCongr (Equiv.swap x y) := by
  revert p q r x y z
  decide

set_option maxRecDepth 1000000 in
private theorem blockSwap_maps_support_to_complement
    (p q r : ASupp) (x y z : ACompl)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    ∀ a : Fin 7, a ∈ (a7a : aPerm).support →
      blockSwap p q r x y z a ∉ (a7a : aPerm).support := by
  have cross (u : ASupp) (v : ACompl) : u.1 ≠ v.1 := by
    intro huv
    exact v.2 (huv ▸ u.2)
  have val_ne {u v : ACompl} (h : u ≠ v) : u.1 ≠ v.1 := by
    intro huv
    exact h (Subtype.ext huv)
  have hsuppCard : Fintype.card ASupp = 3 := a7a_threeCycle.card_support
  have htrioCard : ({p, q, r} : Finset ASupp).card = 3 := by
    simp [hpq, hpr, hqr]
  have htrio : ({p, q, r} : Finset ASupp) = Finset.univ := by
    exact (Finset.card_eq_iff_eq_univ _).mp (by
      rw [htrioCard]
      exact hsuppCard.symm)
  intro a ha
  have haCases : (⟨a, ha⟩ : ASupp) = p ∨
      (⟨a, ha⟩ : ASupp) = q ∨ (⟨a, ha⟩ : ASupp) = r := by
    have hm : (⟨a, ha⟩ : ASupp) ∈ ({p, q, r} : Finset ASupp) := by
      rw [htrio]
      exact Finset.mem_univ _
    simpa using hm
  rcases haCases with hap | haq | har
  · have ha' : a = p.1 := congrArg Subtype.val hap
    subst a
    have hc : blockSwap p q r x y z p.1 = x.1 := by
      dsimp [blockSwap]
      rw [Equiv.swap_apply_of_ne_of_ne
          (fun h => hpr (Subtype.ext h)) (cross p z),
        Equiv.swap_apply_of_ne_of_ne
          (fun h => hpq (Subtype.ext h)) (cross p y),
        Equiv.swap_apply_left]
    rw [hc]
    exact x.2
  · have ha' : a = q.1 := congrArg Subtype.val haq
    subst a
    have hc : blockSwap p q r x y z q.1 = y.1 := by
      dsimp [blockSwap]
      rw [Equiv.swap_apply_of_ne_of_ne
          (fun h => hqr (Subtype.ext h)) (cross q z),
        Equiv.swap_apply_left,
        Equiv.swap_apply_of_ne_of_ne
          (Ne.symm (cross p y)) (val_ne hxy).symm]
    rw [hc]
    exact y.2
  · have ha' : a = r.1 := congrArg Subtype.val har
    subst a
    have hc : blockSwap p q r x y z r.1 = z.1 := by
      dsimp [blockSwap]
      rw [Equiv.swap_apply_left,
        Equiv.swap_apply_of_ne_of_ne
          (Ne.symm (cross q z)) (val_ne hyz).symm,
        Equiv.swap_apply_of_ne_of_ne
          (Ne.symm (cross p z)) (val_ne hxz).symm]
    rw [hc]
    exact z.2

private theorem kleinFour_eq_a7V_of_centralizes_a7U
    (V : Subgroup A7P) (hVK : IsKleinFour V)
    (hVcent : V ≤ Subgroup.centralizer (a7U : Set A7P)) :
    V = a7V := by
  apply Subgroup.eq_of_le_of_card_ge (K := a7V)
  · intro v hv
    let vp : aPerm := v
    let ap : aPerm := a7a
    let P : Fin 7 → Prop := fun a => a ∈ ap.support
    have hvcommA : vp * ap = ap * vp := by
      have hc := (Subgroup.mem_centralizer_iff.mp (hVcent hv)) a7a (by
        change a7a = 1 ∨ a7a = a7a ∨ a7a = a7a ^ 2
        exact Or.inr (Or.inl rfl))
      exact congrArg Subtype.val hc.symm
    have hvconjA : vp * ap * vp⁻¹ = ap := by
      calc
        vp * ap * vp⁻¹ = (ap * vp) * vp⁻¹ := by rw [hvcommA]
        _ = ap := by simp
    have hmap : ap.support.map vp.toEmbedding = ap.support := by
      rw [← Equiv.Perm.support_conj, hvconjA]
    have hvP : ∀ a, P (vp a) ↔ P a := by
      intro a
      change vp a ∈ ap.support ↔ a ∈ ap.support
      constructor
      · intro ha
        rw [← hmap] at ha
        rcases Finset.mem_map.mp ha with ⟨b, hb, hba⟩
        have hba' : b = a := vp.injective hba
        simpa [hba'] using hb
      · intro ha
        rw [← hmap]
        exact Finset.mem_map.mpr ⟨a, ha, rfl⟩
    let vP : Equiv.Perm {a // P a} := vp.subtypePerm hvP
    let vN : Equiv.Perm {a // ¬P a} :=
      vp.subtypePerm (fun a => not_congr (hvP a))
    let vV : V := ⟨v, hv⟩
    have hv2p : vp ^ 2 = 1 := by
      have hv2V : vV ^ 2 = 1 := hVK.mul_self vV
      have hv2A : v ^ 2 = 1 := by
        simpa [vV] using congrArg (fun z : V => (z : A7P)) hv2V
      simpa [vp] using congrArg Subtype.val hv2A
    have hvP2 : vP ^ 2 = 1 := by
      apply Equiv.ext
      intro a
      apply Subtype.ext
      change vp (vp a.1) = a.1
      exact Equiv.congr_fun hv2p a.1
    have hvN2 : vN ^ 2 = 1 := by
      apply Equiv.ext
      intro a
      apply Subtype.ext
      change vp (vp a.1) = a.1
      exact Equiv.congr_fun hv2p a.1
    have haP : ∀ a, P (ap a) ↔ P a :=
      fun a => Equiv.Perm.apply_mem_support
    let aP : Equiv.Perm {a // P a} := ap.subtypePerm haP
    have haPcard : aP.support.card = 3 := by
      rw [Equiv.Perm.support_subtypePerm]
      change (Finset.univ.filter fun a : ASupp =>
        (a7a : aPerm) a ≠ a).card = 3
      have hall : (Finset.univ.filter fun a : ASupp =>
          (a7a : aPerm) a ≠ a) = Finset.univ := by
        ext a
        simp [Equiv.Perm.mem_support.mp a.2]
      rw [hall]
      exact a7a_threeCycle.card_support
    have hvPa : vP * aP = aP * vP := by
      apply Equiv.ext
      intro a
      apply Subtype.ext
      change vp (ap a.1) = ap (vp a.1)
      exact Equiv.congr_fun hvcommA a.1
    have hvPone : vP = 1 :=
      involution_commuting_threeCycle_on_support_eq_one
        vP aP hvP2 haPcard hvPa
    let split : Equiv.Perm {a // P a} × Equiv.Perm {a // ¬P a} →*
        aPerm := Equiv.Perm.subtypeCongrHom P
    have hvSplit : split (vP, vN) = vp := by
      apply Equiv.ext
      intro a
      by_cases ha : P a
      · simp [split, vP, vN, Equiv.Perm.subtypeCongrHom, ha]
      · simp [split, vP, vN, Equiv.Perm.subtypeCongrHom, ha]
    have hvNsign : Equiv.Perm.sign vN = 1 := by
      have hsign := congrArg Equiv.Perm.sign hvSplit
      change Equiv.Perm.sign (vP.subtypeCongr vN) =
        Equiv.Perm.sign vp at hsign
      rw [Equiv.Perm.sign_subtypeCongr] at hsign
      have hvpsign : Equiv.Perm.sign vp = 1 := v.2
      rw [hvPone] at hsign
      simpa only [Equiv.Perm.sign_one, one_mul, hvpsign] using hsign
    have hcomp := even_involution_complement_mem_a7V vN hvN2 hvNsign
    have hcompSplit : split (1, vN) = Equiv.Perm.ofSubtype vN := by
      apply Equiv.ext
      intro a
      by_cases ha : P a
      · simp [split, Equiv.Perm.subtypeCongrHom, ha,
          Equiv.Perm.ofSubtype_apply_of_not_mem]
      · simp [split, Equiv.Perm.subtypeCongrHom, ha,
          Equiv.Perm.ofSubtype_apply_of_mem]
    have heq : complementPermutation vN hvNsign = v := by
      apply Subtype.ext
      change Equiv.Perm.ofSubtype vN = vp
      rw [← hcompSplit, ← hvSplit, hvPone]
    exact heq ▸ hcomp
  · rw [hVK.card_four,
      aSeven_structure_fact_1_8_ii_centralizer.2.2.2.card_four]

private theorem exists_commuting_support_swap
    (s : A7P) (hsI : IsInvolution s)
    (hsInv : ∀ x : A7P, x ∈ a7U → s * x * s⁻¹ = x⁻¹) :
    ∃ g : A7P, g * s = s * g ∧ g ^ 2 = s ∧
      ∀ a : Fin 7, a ∈ (a7a : aPerm).support →
        (g : aPerm) a ∉ (a7a : aPerm).support := by
  let sp : aPerm := s
  let ap : aPerm := a7a
  let P : Fin 7 → Prop := fun x => x ∈ ap.support
  have hsA : sp * ap * sp⁻¹ = ap⁻¹ := by
    exact congrArg Subtype.val (hsInv a7a (by
      change a7a = 1 ∨ a7a = a7a ∨ a7a = a7a ^ 2
      exact Or.inr (Or.inl rfl)))
  have hmap : ap.support.map sp.toEmbedding = ap.support := by
    rw [← Equiv.Perm.support_conj, hsA, Equiv.Perm.support_inv]
  have hsP : ∀ x, P (sp x) ↔ P x := by
    intro x
    change sp x ∈ ap.support ↔ x ∈ ap.support
    constructor
    · intro hx
      rw [← hmap] at hx
      rcases Finset.mem_map.mp hx with ⟨y, hy, heq⟩
      have hyx : y = x := sp.injective heq
      simpa [hyx] using hy
    · intro hx
      rw [← hmap]
      exact Finset.mem_map.mpr ⟨x, hx, rfl⟩
  let sP : Equiv.Perm {x // P x} := sp.subtypePerm hsP
  let sN : Equiv.Perm {x // ¬ P x} :=
    sp.subtypePerm (fun x => not_congr (hsP x))
  have hs2p : sp ^ 2 = 1 := by
    simpa [sp] using congrArg Subtype.val hsI.2
  have hsP2 : sP ^ 2 = 1 := by
    apply Equiv.ext
    intro x
    apply Subtype.ext
    change sp (sp x.1) = x.1
    exact Equiv.congr_fun hs2p x.1
  have hsN2 : sN ^ 2 = 1 := by
    apply Equiv.ext
    intro x
    apply Subtype.ext
    change sp (sp x.1) = x.1
    exact Equiv.congr_fun hs2p x.1
  have haP : ∀ x, P (ap x) ↔ P x := fun x => Equiv.Perm.apply_mem_support
  let aP : Equiv.Perm {x // P x} := ap.subtypePerm haP
  have haPcard : aP.support.card = 3 := by
    rw [Equiv.Perm.support_subtypePerm]
    change (Finset.univ.filter fun x : ASupp => (a7a : aPerm) x ≠ x).card = 3
    have hall : (Finset.univ.filter fun x : ASupp => (a7a : aPerm) x ≠ x) =
        Finset.univ := by
      ext x
      simp [Equiv.Perm.mem_support.mp x.2]
    rw [hall]
    change Fintype.card ASupp = 3
    exact a7a_threeCycle.card_support
  have hsPa : sP * aP * sP⁻¹ = aP⁻¹ := by
    apply Equiv.ext
    intro x
    apply Subtype.ext
    change (sp * ap * sp⁻¹) x.1 = ap⁻¹ x.1
    exact Equiv.congr_fun hsA x.1
  have hsPsign : Equiv.Perm.sign sP = -1 :=
    support_inverter_has_negative_sign sP aP haPcard hsPa
  let split : Equiv.Perm {x // P x} × Equiv.Perm {x // ¬ P x} →*
      Equiv.Perm (Fin 7) := Equiv.Perm.subtypeCongrHom P
  have hsSplit : split (sP, sN) = sp := by
    ext x
    by_cases hx : P x
    · simp [split, sP, sN, hx, Equiv.Perm.subtypeCongrHom]
    · simp [split, sP, sN, hx, Equiv.Perm.subtypeCongrHom]
  have hsNsign : Equiv.Perm.sign sN = -1 := by
    have hsign := congrArg Equiv.Perm.sign hsSplit
    change Equiv.Perm.sign (sP.subtypeCongr sN) =
      Equiv.Perm.sign sp at hsign
    rw [Equiv.Perm.sign_subtypeCongr] at hsign
    have hspSign : Equiv.Perm.sign sp = 1 := s.2
    have hsign' : (-1 : ℤˣ) * Equiv.Perm.sign sN = 1 := by
      have hleft := congrArg
        (fun z : ℤˣ => z * Equiv.Perm.sign sN) hsPsign
      exact hleft.symm.trans (hsign.trans hspSign)
    rcases Int.units_eq_one_or (Equiv.Perm.sign sN) with h | h
    · rw [h] at hsign'
      norm_num at hsign'
    · exact h
  have hsNsupport : sN.support.card = 2 :=
    odd_involution_on_complement_isSwap sN hsN2 hsNsign
  have hsNSwap : Equiv.Perm.IsSwap sN :=
    Equiv.Perm.card_support_eq_two.mp hsNsupport
  rcases hsNSwap with ⟨x, y, hxy, hsNxy⟩
  have hcardN : Fintype.card {x // ¬ P x} = 4 := by
    change Fintype.card ACompl = 4
    exact aCompl_card
  have hthree : 3 ≤ Cardinal.mk {x // ¬ P x} := by
    rw [Cardinal.mk_fintype, hcardN]
    norm_num
  obtain ⟨z, hzx, hzy⟩ := Cardinal.exists_ne_ne_of_three_le hthree x y
  have hxz : x ≠ z := Ne.symm hzx
  have hyz : y ≠ z := Ne.symm hzy
  have hsPsupport : sP.support.card = 2 :=
    odd_involution_on_support_isSwap sP hsP2 hsPsign
  have hsPSwap : Equiv.Perm.IsSwap sP :=
    Equiv.Perm.card_support_eq_two.mp hsPsupport
  rcases hsPSwap with ⟨p, q, hpq, hsPpq⟩
  have hcardP : Fintype.card {x // P x} = 3 := by
    change Fintype.card ASupp = 3
    exact a7a_threeCycle.card_support
  have hthreeP : 3 ≤ Cardinal.mk {x // P x} := by
    rw [Cardinal.mk_fintype, hcardP]
    norm_num
  obtain ⟨r, hrp, hrq⟩ := Cardinal.exists_ne_ne_of_three_le hthreeP p q
  have hpr : p ≠ r := Ne.symm hrp
  have hqr : q ≠ r := Ne.symm hrq
  let cperm : aPerm := blockSwap p q r x y z
  let pperm : aPerm := Equiv.Perm.ofSubtype sP
  let gperm : aPerm := cperm * pperm
  have hcSign : Equiv.Perm.sign cperm = -1 := by
    simpa [cperm, P, ap] using blockSwap_sign p q r x y z
  have hpSign : Equiv.Perm.sign pperm = -1 := by
    simpa [pperm, Equiv.Perm.sign_ofSubtype] using hsPsign
  have hgSign : Equiv.Perm.sign gperm = 1 := by
    rw [show Equiv.Perm.sign gperm =
        Equiv.Perm.sign cperm * Equiv.Perm.sign pperm by
      exact Equiv.Perm.sign_mul cperm pperm]
    rw [hcSign, hpSign]
    norm_num
  let g : A7P := ⟨gperm, hgSign⟩
  have hsSwapSplit :
      (Equiv.swap p q).subtypeCongr (Equiv.swap x y) = sp := by
    calc
      (Equiv.swap p q).subtypeCongr (Equiv.swap x y) =
          split (sP, sN) := by rw [hsPpq, hsNxy]; rfl
      _ = sp := hsSplit
  have hcComm : cperm * sp = sp * cperm := by
    rw [← hsSwapSplit]
    simpa [cperm, P, ap] using
      blockSwap_commutes p q r x y z hpq hpr hqr hxy hxz hyz
  have hpSplit : split (sP, 1) = pperm := by
    apply Equiv.ext
    intro a
    by_cases ha : P a
    · simp [split, pperm, Equiv.Perm.subtypeCongrHom, ha,
        Equiv.Perm.ofSubtype_apply_of_mem]
    · simp [split, pperm, Equiv.Perm.subtypeCongrHom, ha,
        Equiv.Perm.ofSubtype_apply_of_not_mem]
  have hpComm : pperm * sp = sp * pperm := by
    have hpair : (sP, 1) * (sP, sN) = (sP, sN) * (sP, 1) := by
      ext <;> simp
    have hmap := congrArg split hpair
    simpa only [map_mul, hpSplit, hsSplit] using hmap
  have hgCommPerm : gperm * sp = sp * gperm := by
    dsimp [gperm]
    calc
      (cperm * pperm) * sp = cperm * (pperm * sp) := by group
      _ = cperm * (sp * pperm) := by rw [hpComm]
      _ = (cperm * sp) * pperm := by group
      _ = (sp * cperm) * pperm := by rw [hcComm]
      _ = sp * (cperm * pperm) := by group
  have hgComm : g * s = s * g := Subtype.ext hgCommPerm
  have hgSqPerm : gperm ^ 2 = sp := by
    calc
      gperm ^ 2 =
          (Equiv.swap p q).subtypeCongr (Equiv.swap x y) := by
            simpa [gperm, cperm, pperm, hsPpq] using
              blockSwap_mul_supportSwap_sq p q r x y z
                hpq hpr hqr hxy hxz hyz
      _ = sp := hsSwapSplit
  have hgSq : g ^ 2 = s := Subtype.ext hgSqPerm
  have hgMapsSupport : ∀ a : Fin 7, a ∈ ap.support →
      gperm a ∉ ap.support := by
    intro a ha
    have hpa : P (pperm a) := by
      change pperm a ∈ ap.support
      change (Equiv.Perm.ofSubtype sP) a ∈ ap.support
      rw [Equiv.Perm.ofSubtype_apply_of_mem sP ha]
      exact (sP ⟨a, ha⟩).2
    change cperm (pperm a) ∉ ap.support
    simpa [cperm, P, ap] using
      blockSwap_maps_support_to_complement p q r x y z
        hpq hpr hqr hxy hxz hyz (pperm a) hpa
  exact ⟨g, hgComm, hgSq, by simpa [g, ap, gperm] using hgMapsSupport⟩

private theorem fixed_exists_distinct_inverted_normalizer_conjugator
    (s : A7P) (hsI : IsInvolution s)
    (hsInv : ∀ x : A7P, x ∈ a7U → s * x * s⁻¹ = x⁻¹) :
    ∃ g b : A7P, g * s = s * g ∧ g ^ 2 = s ∧
      b = g * a7a * g⁻¹ ∧
      Equiv.Perm.IsThreeCycle (b : aPerm) ∧ b ∉ a7U ∧
      b ∈ Subgroup.normalizer (a7V : Set A7P) ∧
      s * b * s⁻¹ = b⁻¹ := by
  obtain ⟨g, hgComm, hgSq, hgMapsSupport⟩ :=
    exists_commuting_support_swap s hsI hsInv
  let b : A7P := g * a7a * g⁻¹
  have hbperm3 : Equiv.Perm.IsThreeCycle (b : aPerm) := by
    change ((g : aPerm) * (a7a : aPerm) * (g : aPerm)⁻¹).cycleType = {3}
    rw [Equiv.Perm.cycleType_conj]
    exact a7a_threeCycle
  have hbSupport : (b : aPerm).support ⊆ (a7a : aPerm).supportᶜ := by
    change ((g : aPerm) * (a7a : aPerm) * (g : aPerm)⁻¹).support ⊆ _
    rw [Equiv.Perm.support_conj]
    intro a ha
    rcases Finset.mem_map.mp ha with ⟨u, hu, rfl⟩
    exact Finset.mem_compl.mpr (hgMapsSupport u hu)
  have hbNotU : b ∉ a7U :=
    threeCycle_not_mem_a7U_of_support_le_compl b hbperm3 hbSupport
  have hbInvariant : ∀ a : Fin 7,
      ((b : aPerm) a ∉ (a7a : aPerm).support) ↔
        a ∉ (a7a : aPerm).support := by
    intro a
    simpa using Equiv.Perm.isInvariant_of_support_le hbSupport a
  let bN : Equiv.Perm ACompl := (b : aPerm).subtypePerm hbInvariant
  have hbOf : Equiv.Perm.ofSubtype bN = (b : aPerm) := by
    apply Equiv.Perm.ofSubtype_subtypePerm hbInvariant
    intro a ha
    have hamem : a ∈ (b : aPerm).support := Equiv.Perm.mem_support.mpr ha
    exact Finset.mem_compl.mp (hbSupport hamem)
  have hbNSign : Equiv.Perm.sign bN = 1 := by
    calc
      Equiv.Perm.sign bN =
          Equiv.Perm.sign (Equiv.Perm.ofSubtype bN) := by
            rw [Equiv.Perm.sign_ofSubtype]
      _ = Equiv.Perm.sign (b : aPerm) := congrArg Equiv.Perm.sign hbOf
      _ = 1 := b.2
  have hbNorm : b ∈ Subgroup.normalizer (a7V : Set A7P) := by
    have hn := complementPermutation_mem_normalizer_a7V bN hbNSign
    have heq : complementPermutation bN hbNSign = b := by
      apply Subtype.ext
      exact hbOf
    exact heq ▸ hn
  have hbInv : s * b * s⁻¹ = b⁻¹ := by
    dsimp [b]
    have hsg : s * g = g * s := hgComm.symm
    have hgInvComm : g⁻¹ * s⁻¹ = s⁻¹ * g⁻¹ := by
      exact (congrArg Inv.inv hgComm).symm
    calc
      s * (g * a7a * g⁻¹) * s⁻¹ =
          (s * g) * a7a * (g⁻¹ * s⁻¹) := by group
      _ = (g * s) * a7a * (s⁻¹ * g⁻¹) := by rw [hsg, hgInvComm]
      _ = g * (s * a7a * s⁻¹) * g⁻¹ := by group
      _ = g * a7a⁻¹ * g⁻¹ := by
        rw [hsInv a7a (by
          change a7a = 1 ∨ a7a = a7a ∨ a7a = a7a ^ 2
          exact Or.inr (Or.inl rfl))]
      _ = (g * a7a * g⁻¹)⁻¹ := by group
  exact ⟨g, b, hgComm, hgSq, rfl, hbperm3, hbNotU, hbNorm, hbInv⟩

/-- An order-three subgroup of `A7` centralized by a Klein four has a
distinct conjugate inside the Klein-four normalizer. If an involution
inverts the original subgroup, the conjugator can be chosen to centralize
that involution, so the conjugate is inverted as well. -/
public theorem aSeven_exists_distinct_inverted_conjugate_normalizing_kleinFour
    (U V : Subgroup (alternatingGroup (Fin 7)))
    (hUcard : Nat.card U = 3)
    (hVK : IsKleinFour V)
    (hVcent : V ≤ Subgroup.centralizer
      (U : Set (alternatingGroup (Fin 7))))
    (s : alternatingGroup (Fin 7)) (hsI : IsInvolution s)
    (hsInv : ∀ x : alternatingGroup (Fin 7), x ∈ U →
      s * x * s⁻¹ = x⁻¹) :
    ∃ g : alternatingGroup (Fin 7), g * s = s * g ∧ g ^ 2 = s ∧
      U.map (MulAut.conj g).toMonoidHom ≠ U ∧
      U.map (MulAut.conj g).toMonoidHom ≤
        Subgroup.normalizer (V : Set (alternatingGroup (Fin 7))) ∧
      ∀ x : alternatingGroup (Fin 7),
        x ∈ U.map (MulAut.conj g).toMonoidHom →
        s * x * s⁻¹ = x⁻¹ := by
  classical
  have hUne : U ≠ ⊥ := by
    intro hbot
    have hcard : Nat.card U = 1 := by rw [hbot]; simp
    omega
  let : Nontrivial U := (Subgroup.nontrivial_iff_ne_bot U).mpr hUne
  obtain ⟨u, hu⟩ := exists_ne (1 : U)
  have huOrderU : orderOf u = 3 := by
    have hdiv : orderOf u ∣ 3 := by
      rw [← hUcard]
      exact orderOf_dvd_natCard u
    rcases (Nat.dvd_prime Nat.prime_three).mp hdiv with h1 | h3
    · exact False.elim (hu (orderOf_eq_one_iff.mp h1))
    · exact h3
  have huOrder : orderOf (u : A7P) = 3 := by
    simpa only [Subgroup.orderOf_coe] using huOrderU
  have hVcentu : V ≤ Subgroup.centralizer ({(u : A7P)} : Set A7P) := by
    intro v hv
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hc := (Subgroup.mem_centralizer_iff.mp (hVcent hv))
      (u : A7P) u.2
    exact hc.symm
  have hu3 : Equiv.Perm.IsThreeCycle (u : aPerm) :=
    aSeven_isThreeCycle_of_order_three_and_kleinFour_centralizer
      u huOrder V hVK hVcentu
  obtain ⟨k, hku⟩ := isConj_iff.mp
    (alternatingGroup.isThreeCycle_isConj (by norm_num) hu3 a7a_threeCycle)
  let e : A7P ≃* A7P := MulAut.conj k
  let U0 : Subgroup A7P := U.map e.toMonoidHom
  let V0 : Subgroup A7P := V.map e.toMonoidHom
  let s0 : A7P := e s
  have hU0card : Nat.card U0 = 3 := by
    rw [Subgroup.card_map_of_injective e.injective, hUcard]
  have haU0 : a7a ∈ U0 := by
    apply Subgroup.mem_map.mpr
    exact ⟨u, u.2, hku⟩
  have ha7UleU0 : a7U ≤ U0 := by
    intro a ha
    change a = 1 ∨ a = a7a ∨ a = a7a ^ 2 at ha
    rcases ha with rfl | rfl | rfl
    · exact U0.one_mem
    · exact haU0
    · exact U0.pow_mem haU0 2
  have ha7UeqU0 : a7U = U0 :=
    Subgroup.eq_of_le_of_card_ge ha7UleU0 (by
      rw [aSeven_structure_fact_1_8_ii_centralizer.1, hU0card])
  have hU0eq : U0 = a7U := ha7UeqU0.symm
  have hV0K : IsKleinFour V0 :=
    isKleinFour_map_mulEquiv_cross V hVK e
  have hV0centU0 : V0 ≤ Subgroup.centralizer (U0 : Set A7P) :=
    centralizer_map_le_of_mulEquiv e U V hVcent
  have hV0eq : V0 = a7V :=
    kleinFour_eq_a7V_of_centralizes_a7U V0 hV0K (by
      simpa [hU0eq] using hV0centU0)
  have hs0I : IsInvolution s0 := by
    constructor
    · intro hs01
      apply hsI.1
      apply e.injective
      simpa [s0] using hs01
    · simpa [s0, map_pow] using congrArg e hsI.2
  have hs0Inv : ∀ x : A7P, x ∈ a7U → s0 * x * s0⁻¹ = x⁻¹ := by
    intro x hx
    have hxU0 : x ∈ U0 := by rw [hU0eq]; exact hx
    rcases Subgroup.mem_map.mp hxU0 with ⟨y, hy, rfl⟩
    simpa [s0] using congrArg e (hsInv y hy)
  obtain ⟨g0, b0, hg0s, hg0sq, hb0eq, _hb03, hb0not, hb0norm, _hb0inv⟩ :=
    fixed_exists_distinct_inverted_normalizer_conjugator s0 hs0I hs0Inv
  let g : A7P := e.symm g0
  let b : A7P := e.symm b0
  have hgs : g * s = s * g := by
    apply e.injective
    simpa [g, s0] using hg0s
  have hgsq : g ^ 2 = s := by
    apply e.injective
    simpa [g, s0, map_pow] using hg0sq
  have hUeqZ : U = Subgroup.zpowers (u : A7P) := by
    have hzle : Subgroup.zpowers (u : A7P) ≤ U :=
      Subgroup.zpowers_le.mpr u.2
    have hzeq : Subgroup.zpowers (u : A7P) = U :=
      Subgroup.eq_of_le_of_card_ge hzle (by
        rw [Nat.card_zpowers, huOrder, hUcard])
    exact hzeq.symm
  have hgb : (MulAut.conj g) (u : A7P) = b := by
    have heu : e (u : A7P) = a7a := by
      simpa [e, MulAut.conj_apply] using hku
    apply e.injective
    change e (g * (u : A7P) * g⁻¹) = e b
    simpa [g, b, e.map_mul, e.map_inv, heu] using hb0eq.symm
  let L : Subgroup A7P := U.map (MulAut.conj g).toMonoidHom
  have hLeq : L = Subgroup.zpowers b := by
    dsimp [L]
    rw [hUeqZ, MonoidHom.map_zpowers]
    exact congrArg Subgroup.zpowers hgb
  have hbnotU : b ∉ U := by
    intro hbU
    have hebU0 : e b ∈ U0 := Subgroup.mem_map.mpr ⟨b, hbU, rfl⟩
    have heb : e b = b0 := e.apply_symm_apply b0
    rw [hU0eq, heb] at hebU0
    exact hb0not hebU0
  have hLne : L ≠ U := by
    intro hLU
    apply hbnotU
    rw [← hLU, hLeq]
    exact Subgroup.mem_zpowers b
  have transport_normalizer
      (c0 : A7P) (hc0 : c0 ∈ Subgroup.normalizer (a7V : Set A7P))
      (c1 : A7P) (hc1 : e c1 = c0) :
      ∀ v : A7P, v ∈ V → c1 * v * c1⁻¹ ∈ V := by
    intro v hv
    have hevV0 : e v ∈ V0 := Subgroup.mem_map.mpr ⟨v, hv, rfl⟩
    have hev7 : e v ∈ a7V := by rwa [← hV0eq]
    have hout7 := (Subgroup.mem_normalizer_iff.mp hc0 (e v)).1 hev7
    have hout0 : c0 * e v * c0⁻¹ ∈ V0 := by rwa [hV0eq]
    rcases Subgroup.mem_map.mp hout0 with ⟨w, hw, hwEq⟩
    have heConj : e (c1 * v * c1⁻¹) = c0 * e v * c0⁻¹ := by
      rw [e.map_mul, e.map_mul, e.map_inv, hc1]
    have horig : c1 * v * c1⁻¹ = w :=
      e.injective (heConj.trans hwEq.symm)
    rw [horig]
    exact hw
  have hforward : ∀ v : A7P, v ∈ V → b * v * b⁻¹ ∈ V := by
    apply transport_normalizer b0 hb0norm b
    exact e.apply_symm_apply b0
  have hbackward : ∀ v : A7P, v ∈ V → b⁻¹ * v * (b⁻¹)⁻¹ ∈ V := by
    apply transport_normalizer b0⁻¹
      ((Subgroup.normalizer (a7V : Set A7P)).inv_mem hb0norm) b⁻¹
    simp [b]
  have hbnormV : b ∈ Subgroup.normalizer (V : Set A7P) := by
    rw [Subgroup.mem_normalizer_iff]
    intro v
    constructor
    · exact hforward v
    · intro hv
      have hback := hbackward (b * v * b⁻¹) hv
      have heq : b⁻¹ * (b * v * b⁻¹) * (b⁻¹)⁻¹ = v := by group
      rw [heq] at hback
      exact hback
  have hLnorm : L ≤ Subgroup.normalizer (V : Set A7P) := by
    rw [hLeq, Subgroup.zpowers_le]
    exact hbnormV
  have hLinv : ∀ x : A7P, x ∈ L → s * x * s⁻¹ = x⁻¹ := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
    change s * (g * y * g⁻¹) * s⁻¹ = (g * y * g⁻¹)⁻¹
    have hsg : s * g = g * s := hgs.symm
    have hgInvComm : g⁻¹ * s⁻¹ = s⁻¹ * g⁻¹ := by
      exact (congrArg Inv.inv hgs).symm
    calc
      s * (g * y * g⁻¹) * s⁻¹ =
          (s * g) * y * (g⁻¹ * s⁻¹) := by group
      _ = (g * s) * y * (s⁻¹ * g⁻¹) := by rw [hsg, hgInvComm]
      _ = g * (s * y * s⁻¹) * g⁻¹ := by group
      _ = g * y⁻¹ * g⁻¹ := by rw [hsInv y hy]
      _ = (g * y * g⁻¹)⁻¹ := by group
  exact ⟨g, hgs, hgsq, hLne, hLnorm, hLinv⟩


end CFSG.GorensteinWalter
