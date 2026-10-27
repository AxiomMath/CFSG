module

public import CFSG.LocalAnalysis.WeakClosure81.EightTailPThreeSym

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Equiv Equiv.Perm CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup
open CFSG.Timmesfeld.Bridge.Asc72
open CFSG.LocalAnalysis.WeakClosure81.SevenK
open scoped commutatorElement

@[expose] def commE {E Y : Type} [CommGroup E] [Group Y] (α : Y →* MulAut E) (d : Y) :
    Subgroup E :=
  ((MonoidHom.id E) / (α d).toMonoidHom).range

private theorem w85g_mem_commE {E Y : Type} [CommGroup E] [Group Y] (α : Y →* MulAut E)
    (d : Y) (z : E) : z ∈ commE α d ↔ ∃ w : E, w * (α d w)⁻¹ = z := by
  simp [commE, MonoidHom.mem_range, MonoidHom.div_apply, div_eq_mul_inv]

private theorem w85g_map_commE_le {E Y : Type} [CommGroup E] [Group Y] (α : Y →* MulAut E)
    (u d : Y) : (commE α d).map (α u).toMonoidHom ≤ commE α (u * d * u⁻¹) := by
  intro y hy
  rw [Subgroup.mem_map] at hy
  obtain ⟨z, hz, rfl⟩ := hy
  rw [w85g_mem_commE] at hz ⊢
  obtain ⟨w, hw⟩ := hz
  refine ⟨α u w, ?_⟩
  rw [← hw]
  have h : α (u * d * u⁻¹) (α u w) = α u (α d w) := by
    have hm : α (u * d * u⁻¹) = α u * α d * (α u)⁻¹ := by rw [map_mul, map_mul, map_inv]
    rw [hm, MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply]
    simp
  rw [h, map_mul, map_inv]
  rfl

private theorem w85g_map_commE {E Y : Type} [CommGroup E] [Group Y] (α : Y →* MulAut E)
    (u d : Y) : (commE α d).map (α u).toMonoidHom = commE α (u * d * u⁻¹) := by
  apply le_antisymm (w85g_map_commE_le α u d)
  have h1 := w85g_map_commE_le α u⁻¹ (u * d * u⁻¹)
  have h2 : u⁻¹ * (u * d * u⁻¹) * (u⁻¹)⁻¹ = d := by group
  rw [h2] at h1
  have h4 : commE α (u * d * u⁻¹) ≤ (commE α d).map (α u).toMonoidHom := by
    have h5 := Subgroup.map_mono (f := (α u).toMonoidHom) h1
    have hcomp : (α u).toMonoidHom.comp (α u⁻¹).toMonoidHom = MonoidHom.id E := by
      ext x
      simp [MonoidHom.comp_apply]
    rw [Subgroup.map_map, hcomp, Subgroup.map_id] at h5
    exact h5
  exact h4

private theorem w85g_exists_two_ne {m : ℕ} (hm : 5 ≤ m) (a b : Fin m) (hab : a ≠ b) :
    ∃ c d : Fin m, c ≠ d ∧ c ≠ a ∧ c ≠ b ∧ d ≠ a ∧ d ≠ b := by
  classical
  let s : Finset (Fin m) := (Finset.univ.erase a).erase b
  have hb : b ∈ (Finset.univ : Finset (Fin m)).erase a :=
    Finset.mem_erase.mpr ⟨hab.symm, Finset.mem_univ b⟩
  have hcard1 : s.card = m - 2 := by
    unfold s
    rw [Finset.card_erase_of_mem hb, Finset.card_erase_of_mem (Finset.mem_univ a),
      Finset.card_univ, Fintype.card_fin]
    omega
  have hcard : 1 < s.card := by omega
  obtain ⟨c, hc, hca⟩ := Finset.exists_mem_ne hcard a
  have hc_ne_b : c ≠ b := (Finset.mem_erase.mp hc).1
  have hcard2 : 1 < (s.erase c).card := by
    rw [Finset.card_erase_of_mem hc, hcard1]
    omega
  obtain ⟨d, hd, hdc⟩ := Finset.exists_mem_ne hcard2 c
  have hds : d ∈ s := (Finset.mem_erase.mp hd).2
  have hd_ne_b : d ≠ b := (Finset.mem_erase.mp hds).1
  have hd_ne_a : d ≠ a := (Finset.mem_erase.mp (Finset.mem_erase.mp hds).2).1
  exact ⟨c, d, hdc.symm, hca, hc_ne_b, hd_ne_a, hd_ne_b⟩

private theorem w85g_commE_mul_le {E Y : Type} [CommGroup E] [Group Y] (α : Y →* MulAut E)
    (r s : Y) : commE α (r * s) ≤ commE α s ⊔ commE α r := by
  intro x hx
  rw [w85g_mem_commE] at hx
  obtain ⟨y, hy⟩ := hx
  rw [← hy]
  have h1 : y * (α s y)⁻¹ ∈ commE α s := (w85g_mem_commE α s _).mpr ⟨y, rfl⟩
  have h2 : α s y * (α r (α s y))⁻¹ ∈ commE α r :=
    (w85g_mem_commE α r _).mpr ⟨α s y, rfl⟩
  have heq : y * (α (r * s) y)⁻¹ = (y * (α s y)⁻¹) * (α s y * (α r (α s y))⁻¹) := by
    rw [map_mul, MulAut.mul_apply]
    group
  rw [heq]
  exact Subgroup.mul_mem_sup h1 h2

private theorem w85g_commE_inv {E Y : Type} [CommGroup E] [Group Y] (α : Y →* MulAut E)
    (r : Y) : commE α r⁻¹ = commE α r := by
  apply le_antisymm
  · intro x hx
    have hinv : x⁻¹ ∈ commE α r := by
      rw [w85g_mem_commE] at hx
      obtain ⟨w, hw⟩ := hx
      exact (w85g_mem_commE α r x⁻¹).mpr ⟨α r⁻¹ w, by
        have hx' : x⁻¹ = (α r⁻¹ w) * w⁻¹ := by rw [← hw]; group
        rw [hx']
        have h : α r (α r⁻¹ w) = w := by simp
        rw [h]⟩
    simpa using inv_mem hinv
  · intro x hx
    have hinv : x⁻¹ ∈ commE α r⁻¹ := by
      rw [w85g_mem_commE] at hx
      obtain ⟨w, hw⟩ := hx
      exact (w85g_mem_commE α r⁻¹ x⁻¹).mpr ⟨α r w, by
        have hx' : x⁻¹ = (α r w) * w⁻¹ := by rw [← hw]; group
        rw [hx']
        have h : α r⁻¹ (α r w) = w := by simp
        rw [h]⟩
    simpa using inv_mem hinv

private theorem w85g_commE_one {E Y : Type} [CommGroup E] [Group Y] (α : Y →* MulAut E) :
    commE α (1 : Y) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [w85g_mem_commE] at hx
  obtain ⟨w, hw⟩ := hx
  rw [← hw]
  simp

private theorem w85g_odd_card_fusionOddCore {Y : Type} [Group Y] [Finite Y] :
    Odd (Nat.card (fusionOddCore Y)) := by
  have h : fusionOddCore Y = CFSG.pPrimeCore 2 Y := by
    unfold fusionOddCore CFSG.pPrimeCore
    congr 1
    ext N
    simp only [Set.mem_setOf_eq]
    rw [Nat.coprime_two_left]
  rw [h]
  exact Nat.coprime_two_left.1 CFSG.pPrimeCore_coprime_card

private theorem w85g_zpow_eq_one_or_of_sq {Y : Type} [Group Y] {t : Y} (ht : t * t = 1)
    (n : ℤ) : t ^ n = 1 ∨ t ^ n = t := by
  have h2 : t ^ (2 : ℕ) = 1 := by rw [pow_two]; exact ht
  have hdvd : orderOf t ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr h2
  have hcases : orderOf t = 1 ∨ orderOf t = 2 :=
    (Nat.dvd_prime (by norm_num : Nat.Prime 2)).mp hdvd
  rcases hcases with h1 | h2'
  · left
    have ht1 : t = 1 := by
      have := pow_orderOf_eq_one t
      rwa [h1, pow_one] at this
    rw [ht1, one_zpow]
  · rw [← zpow_mod_orderOf t n, show (orderOf t : ℤ) = (2 : ℤ) by exact_mod_cast h2']
    rcases Int.emod_two_eq_zero_or_one n with h0 | h1'
    · left; rw [h0, zpow_zero]
    · right; rw [h1', zpow_one]

private theorem w85g_exists_third {m : ℕ} (hm : 3 ≤ m) {a b : Fin m} (hab : a ≠ b) :
    ∃ j : Fin m, j ≠ a ∧ j ≠ b := by
  have hb : b ∈ (Finset.univ : Finset (Fin m)).erase a :=
    Finset.mem_erase.mpr ⟨hab.symm, Finset.mem_univ b⟩
  have hcard : ((Finset.univ.erase a).erase b).card = m - 2 := by
    rw [Finset.card_erase_of_mem hb, Finset.card_erase_of_mem (Finset.mem_univ a),
      Finset.card_univ, Fintype.card_fin]
    omega
  have hpos : 0 < ((Finset.univ.erase a).erase b).card := by omega
  obtain ⟨j, hj⟩ := Finset.card_pos.mp hpos
  exact ⟨j, (Finset.mem_erase.mp (Finset.mem_erase.mp hj).2).1, (Finset.mem_erase.mp hj).1⟩

private theorem w85g_center_perm_eq_bot {m : ℕ} (hm : 3 ≤ m) :
    Subgroup.center (Perm (Fin m)) = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  rw [Subgroup.mem_bot]
  apply Equiv.ext
  intro i
  by_contra hne
  obtain ⟨j, hji, hjg⟩ := w85g_exists_third hm (a := g i) (b := i) hne
  have hij : i ≠ j := fun h => hjg h.symm
  have hcomm : g * Equiv.swap i j = Equiv.swap i j * g :=
    (Subgroup.mem_center_iff.mp hg (Equiv.swap i j)).symm
  rcases (w85g_mul_swap_commute_iff hij).mp hcomm with ⟨hi, -⟩ | ⟨hgi, -⟩
  · exact hne hi
  · exact hji hgi.symm

private theorem w85g_ker_eq_bot_of_perm {Y : Type} [Group Y] [Finite Y] {m : ℕ}
    (ψ : Y →* Perm (Fin m)) (hker : ψ.ker ≤ Subgroup.center Y) (hodd : Odd (Nat.card ψ.ker))
    (hsurj : Function.Surjective ψ) (hgen : Subgroup.closure {y : Y | y * y = 1} = ⊤)
    (hm : 0 < m) : ψ.ker = ⊥ := by
  have hm1 : m - 1 + 1 = m := Nat.sub_add_cancel (Nat.succ_le_of_lt hm)
  let iso : Perm (Fin (m - 1 + 1)) ≃* Perm (Fin m) := Equiv.permCongrHom (finCongr hm1)
  let σ : Y →* Perm (Fin (m - 1 + 1)) := iso.symm.toMonoidHom.comp ψ
  have hσker : σ.ker = ψ.ker := by
    show (iso.symm.toMonoidHom.comp ψ).ker = ψ.ker
    rw [MonoidHom.ker_comp_of_injective ψ iso.symm.toMonoidHom iso.symm.injective]
  have hσker_le : σ.ker ≤ Subgroup.center Y := by rw [hσker]; exact hker
  have hσodd : Odd (Nat.card σ.ker) := by rw [hσker]; exact hodd
  have hσsurj : Function.Surjective σ := iso.symm.surjective.comp hsurj
  have := ker_eq_bot_of_closure_involutions σ hσker_le hσodd hσsurj hgen
  rwa [hσker] at this

theorem commE_sup_eq_top {Y E : Type} [Group Y] [Finite Y] [CommGroup E] [Finite E]
    (α : Y →* MulAut E) (hE : ∀ x : E, x * x = 1) {m : ℕ}
    {e : Y ⧸ fusionOddCore Y ≃* Perm (Fin m)} {t : Y} {P : Sylow 2 Y} (h : SymSetting e t P)
    (hnc : ¬ fusionOddCore Y ≤ Subgroup.center Y)
    (hC : ∀ x : E, (∀ r ∈ ⁅fusionOddCore Y, Subgroup.zpowers t⁆, α r x = x) → x = 1) :
    (⨆ o ∈ fusionOddCore Y, commE α (o * t * o⁻¹)) = ⊤ := by
  classical
  let F : Subgroup E := ⨆ o ∈ fusionOddCore Y, commE α (o * t * o⁻¹)
  change F = ⊤
  let S : Subgroup Y :=
    { carrier := {r | commE α r ≤ F}
      one_mem' := by
        show commE α (1 : Y) ≤ F
        rw [w85g_commE_one]; exact bot_le
      mul_mem' := by
        intro a b ha hb
        exact (w85g_commE_mul_le α a b).trans (sup_le hb ha)
      inv_mem' := by
        intro a ha
        change commE α a⁻¹ ≤ F
        rw [w85g_commE_inv]; exact ha }
  have htF : commE α t ≤ F := by
    refine le_iSup_of_le (1 : Y) ?_
    refine le_iSup_of_le (fusionOddCore Y).one_mem ?_
    rw [one_mul, inv_one, mul_one]
  have hconjF : ∀ o ∈ fusionOddCore Y, commE α (o * t * o⁻¹) ≤ F := by
    intro o ho
    exact le_iSup_of_le o (le_iSup_of_le ho le_rfl)
  have hgen : ∀ g₁ ∈ fusionOddCore Y, ∀ g₂ ∈ Subgroup.zpowers t,
      commE α ⁅g₁, g₂⁆ ≤ F := by
    intro g₁ hg₁ g₂ hg₂
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg₂
    rcases w85g_zpow_eq_one_or_of_sq h.mul_self n with hn | hn
    · rw [hn]
      have h1 : ⁅g₁, (1 : Y)⁆ = 1 := by simp [commutatorElement_def]
      rw [h1, w85g_commE_one]; exact bot_le
    · rw [hn]
      have hcomm : ⁅g₁, t⁆ = (g₁ * t * g₁⁻¹) * t := by
        rw [commutatorElement_def, inv_eq_of_mul_eq_one_right h.mul_self]
      rw [hcomm]
      exact (w85g_commE_mul_le α (g₁ * t * g₁⁻¹) t).trans (sup_le htF (hconjF g₁ hg₁))
  let R : Subgroup Y := ⁅fusionOddCore Y, Subgroup.zpowers t⁆
  have hR_le_S : R ≤ S := by
    change ⁅fusionOddCore Y, Subgroup.zpowers t⁆ ≤ S
    rw [Subgroup.commutator_def, Subgroup.closure_le]
    rintro g ⟨g₁, hg₁, g₂, hg₂, rfl⟩
    exact hgen g₁ hg₁ g₂ hg₂
  have hcommE_R : ∀ r ∈ R, commE α r ≤ F := fun r hr => hR_le_S hr
  let αR : R →* MulAut E := α.comp R.subtype
  have hcop : Nat.Coprime (Nat.card R) (Nat.card E) := by
    have hRle : R ≤ fusionOddCore Y := by
      show ⁅fusionOddCore Y, Subgroup.zpowers t⁆ ≤ fusionOddCore Y
      exact Subgroup.commutator_le_left (H₁ := fusionOddCore Y) (H₂ := Subgroup.zpowers t)
    have hoddR : Odd (Nat.card R) :=
      Odd.of_dvd_nat w85g_odd_card_fusionOddCore (Subgroup.card_dvd_of_le hRle)
    have hE2 : IsPGroup 2 E :=
      isPGroup_iff_pow_pow_eq_one.mpr (fun x => ⟨1, by simpa [pow_two] using hE x⟩)
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2)).mp hE2
    rw [hk]
    exact Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr hoddR)
  have hsolv : Group.IsSolvable E := inferInstance
  letI : MulDistribMulAction R E := MulDistribMulAction.compHom E αR
  have hfixed_bot : CFSG.fixedPointSubgroup R E = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hx' : ∀ a : R, αR a x = x := fun a => by
      have h := hx a
      rwa [show a • x = αR a x from rfl] at h
    rw [Subgroup.mem_bot]
    exact hC x (fun r hr => by
      have := hx' ⟨r, hr⟩
      simpa [αR] using this)
  have hsup := CFSG.fixedPointSubgroup_sup_commutatorAction_eq_top_of_solvable_coprime
    (A := R) (G := E) hsolv hcop
  rw [hfixed_bot, bot_sup_eq] at hsup
  have hcAF : CFSG.commutatorAction R E ≤ F := by
    rw [CFSG.commutatorAction, CFSG.commutatorSubgroup, Subgroup.closure_le]
    rintro x ⟨a, y, -, hx⟩
    rw [hx]
    have hmem : commE α (a : Y) ≤ F := hcommE_R (a : Y) a.2
    refine hmem ?_
    exact (w85g_mem_commE α (a : Y) _).mpr ⟨y⁻¹, by
      show y⁻¹ * (α (a : Y) y⁻¹)⁻¹ = y⁻¹ * (a • y)
      rw [map_inv, inv_inv]
      rfl⟩
  rw [hsup] at hcAF
  exact top_le_iff.mp hcAF

theorem exists_disjoint_centralizes {Y E : Type} [Group Y] [Finite Y] [CommGroup E] [Finite E]
    (α : Y →* MulAut E) {m : ℕ} {e : Y ⧸ fusionOddCore Y ≃* Perm (Fin m)} {t : Y}
    {P : Sylow 2 Y} (h : SymSetting e t P)
    (hti : ∀ d ∈ {y : Y | IsConj t y}, ∀ d' ∈ {y : Y | IsConj t y}, d ≠ d' →
      commE α d ⊓ commE α d' = ⊥) :
    ∃ σ : Y, σ ≠ 1 ∧ IsConj t σ ∧ ∀ o ∈ fusionOddCore Y, ∀ x ∈ commE α (o * t * o⁻¹),
      α σ x = x := by
  classical
  obtain ⟨a, b, hab, hswap⟩ := h.swap
  obtain ⟨c, d, hcd, hca, hcb, hda, hdb⟩ :=
    w85g_exists_two_ne (m := m) (by have := h.six_le; omega) a b hab
  have hconj : IsConj (symPi e t) (Equiv.swap c d) := by
    rw [hswap]; exact isConj_swap hab hcd
  obtain ⟨g, hg⟩ := isConj_iff.mp hconj
  have hsurj : Function.Surjective (symPi e) := by
    simpa [symPi] using e.surjective.comp (QuotientGroup.mk'_surjective (fusionOddCore Y))
  obtain ⟨y, hy⟩ := hsurj g
  have hσimg : symPi e (y * t * y⁻¹) = Equiv.swap c d := by
    simp only [map_mul, map_inv, hy, hg]
  refine ⟨y * t * y⁻¹, ?_, ?_, ?_⟩
  · intro h1
    have h2 : symPi e (y * t * y⁻¹) = 1 := by rw [h1]; simp
    rw [hσimg] at h2
    have h3 : (Equiv.swap c d) c = (1 : Perm (Fin m)) c := by rw [h2]
    simp only [Equiv.swap_apply_left, Equiv.Perm.one_apply] at h3
    exact hcd h3.symm
  · exact isConj_iff.mpr ⟨y, rfl⟩
  · intro o ho x hx
    have ho' : symPi e o = 1 := by
      have hmk : QuotientGroup.mk' (fusionOddCore Y) o = 1 := (QuotientGroup.eq_one_iff o).mpr ho
      show symPi e o = 1
      rw [symPi, MonoidHom.comp_apply, hmk, map_one]
    have hsym_d : symPi e (o * t * o⁻¹) = Equiv.swap a b := by
      simp only [map_mul, map_inv, ho', hswap]
      simp
    have hσD : (y * t * y⁻¹) ∈ {y : Y | IsConj t y} := isConj_iff.mpr ⟨y, rfl⟩
    have hdD : (o * t * o⁻¹) ∈ {y : Y | IsConj t y} := isConj_iff.mpr ⟨o, rfl⟩
    have hne_sd : (y * t * y⁻¹) ≠ (o * t * o⁻¹) := by
      intro hEq
      have hsame : symPi e (y * t * y⁻¹) = symPi e (o * t * o⁻¹) := by rw [hEq]
      rw [hσimg, hsym_d] at hsame
      have h3 := congrArg (fun f : Perm (Fin m) => f c) hsame
      simp only [Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne hca hcb] at h3
      exact hcd h3.symm
    have hσ2 : (y * t * y⁻¹) * (y * t * y⁻¹) = 1 := by
      rw [show (y * t * y⁻¹) * (y * t * y⁻¹) = y * (t * t) * y⁻¹ by group, h.mul_self]
      group
    have hd2 : (o * t * o⁻¹) * (o * t * o⁻¹) = 1 := by
      rw [show (o * t * o⁻¹) * (o * t * o⁻¹) = o * (t * t) * o⁻¹ by group, h.mul_self]
      group
    have hsym_prod : symPi e ((y * t * y⁻¹) * (o * t * o⁻¹)) =
        Equiv.swap c d * Equiv.swap a b := by
      rw [map_mul, hσimg, hsym_d]
    have hcomm_swaps : Commute (Equiv.swap c d) (Equiv.swap a b) := by
      have hnd : [c, d, a, b].Nodup := by
        simp [hcd, hca, hcb, hda, hdb, hab]
      exact (Equiv.Perm.disjoint_swap_swap hnd).commute
    have hsq : (Equiv.swap c d * Equiv.swap a b)^2 = 1 := by
      rw [pow_two]
      calc (Equiv.swap c d * Equiv.swap a b) * (Equiv.swap c d * Equiv.swap a b)
          = Equiv.swap c d * (Equiv.swap a b * Equiv.swap c d) * Equiv.swap a b := by group
        _ = Equiv.swap c d * (Equiv.swap c d * Equiv.swap a b) * Equiv.swap a b := by
              rw [← hcomm_swaps.eq]
        _ = (Equiv.swap c d * Equiv.swap c d) * (Equiv.swap a b * Equiv.swap a b) := by group
        _ = 1 := by rw [Equiv.swap_mul_self c d, Equiv.swap_mul_self a b, one_mul]
    have hne_swap : Equiv.swap c d * Equiv.swap a b ≠ 1 := by
      intro h1
      have h3 : (Equiv.swap c d * Equiv.swap a b) c = (1 : Perm (Fin m)) c := by rw [h1]
      simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_left,
        Equiv.swap_apply_of_ne_of_ne hca hcb, Equiv.Perm.one_apply] at h3
      exact hcd h3.symm
    have horder_img : orderOf (Equiv.swap c d * Equiv.swap a b) = 2 :=
      orderOf_eq_prime (p := 2) (by rw [pow_two]; exact hsq) hne_swap
    have hdvd : 2 ∣ orderOf ((y * t * y⁻¹) * (o * t * o⁻¹)) := by
      have h1 := orderOf_map_dvd (symPi e) ((y * t * y⁻¹) * (o * t * o⁻¹))
      rw [hsym_prod, horder_img] at h1
      exact h1
    have htwo : orderOf ((y * t * y⁻¹) * (o * t * o⁻¹)) ∣ 2 := by
      rcases h.oddClass.2.1.2 _ hσD _ hdD with hle | hodd
      · exact hle
      · exact absurd hdvd hodd.not_two_dvd_nat
    have hne_x : (y * t * y⁻¹) * (o * t * o⁻¹) ≠ 1 := by
      intro h1
      have h2 : symPi e ((y * t * y⁻¹) * (o * t * o⁻¹)) = 1 := by rw [h1]; simp
      rw [hsym_prod] at h2
      have h3 : (Equiv.swap c d * Equiv.swap a b) c = (1 : Perm (Fin m)) c := by rw [h2]
      simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_left,
        Equiv.swap_apply_of_ne_of_ne hca hcb, Equiv.Perm.one_apply] at h3
      exact hcd h3.symm
    have hx2 : ((y * t * y⁻¹) * (o * t * o⁻¹))^2 = 1 :=
      (orderOf_dvd_iff_pow_eq_one).mp htwo
    have horder_x : orderOf ((y * t * y⁻¹) * (o * t * o⁻¹)) = 2 :=
      orderOf_eq_prime hx2 hne_x
    have hcomm : Commute (y * t * y⁻¹) (o * t * o⁻¹) := by
      rw [CFSG.Timmesfeld.commute_iff_mul_sq_eq_one hσ2 hd2]
      exact hx2
    have hfix : (y * t * y⁻¹) * (o * t * o⁻¹) * (y * t * y⁻¹)⁻¹ = (o * t * o⁻¹) := by
      rw [inv_eq_of_mul_eq_one_right hσ2, hcomm.eq, mul_assoc, hσ2, mul_one]
    have hmap : (commE α (o * t * o⁻¹)).map (α (y * t * y⁻¹)).toMonoidHom =
        commE α (o * t * o⁻¹) := by
      rw [w85g_map_commE, hfix]
    have hmem_d : α (y * t * y⁻¹) x ∈ commE α (o * t * o⁻¹) := by
      rw [← hmap]
      exact Subgroup.mem_map_of_mem _ hx
    have hx2' : x * (α (y * t * y⁻¹) x)⁻¹ ∈ commE α (o * t * o⁻¹) :=
      mul_mem hx (inv_mem hmem_d)
    have hx1 : x * (α (y * t * y⁻¹) x)⁻¹ ∈ commE α (y * t * y⁻¹) :=
      (w85g_mem_commE α (y * t * y⁻¹) _).mpr ⟨x, rfl⟩
    have hmeminf : x * (α (y * t * y⁻¹) x)⁻¹ ∈
        commE α (y * t * y⁻¹) ⊓ commE α (o * t * o⁻¹) := ⟨hx1, hx2'⟩
    rw [hti _ hσD _ hdD hne_sd] at hmeminf
    exact (mul_inv_eq_one.mp (Subgroup.mem_bot.mp hmeminf)).symm

theorem false_of_noncentral_O {Y E : Type} [Group Y] [Finite Y] [CommGroup E] [Finite E]
    (α : Y →* MulAut E) (hα : Function.Injective α) (hE : ∀ x : E, x * x = 1) {m : ℕ}
    {e : Y ⧸ fusionOddCore Y ≃* Perm (Fin m)} {t : Y} {P : Sylow 2 Y} (h : SymSetting e t P)
    (hnc : ¬ fusionOddCore Y ≤ Subgroup.center Y)
    (hti : ∀ d ∈ {y : Y | IsConj t y}, ∀ d' ∈ {y : Y | IsConj t y}, d ≠ d' →
      commE α d ⊓ commE α d' = ⊥)
    (hC : ∀ x : E, (∀ r ∈ ⁅fusionOddCore Y, Subgroup.zpowers t⁆, α r x = x) → x = 1) :
    False := by
  obtain ⟨σ, hσ1, _hσconj, hσfix⟩ := exists_disjoint_centralizes α h hti
  have htop := commE_sup_eq_top α hE h hnc hC
  have hfixF : ∀ x ∈ (⨆ o ∈ fusionOddCore Y, commE α (o * t * o⁻¹)), α σ x = x := by
    intro x hx
    refine Subgroup.iSup_induction (C := fun y : E => α σ y = y)
      (fun o : Y => ⨆ (_ : o ∈ fusionOddCore Y), commE α (o * t * o⁻¹)) hx ?_ ?_ ?_
    · intro o y hy
      refine Subgroup.iSup_induction (C := fun z : E => α σ z = z)
        (fun (_ : o ∈ fusionOddCore Y) => commE α (o * t * o⁻¹)) hy ?_ ?_ ?_
      · intro ho' z hz
        exact hσfix o ho' z hz
      · simp
      · intro a b ha hb
        rw [map_mul, ha, hb]
    · simp
    · intro a b ha hb
      rw [map_mul, ha, hb]
  have hαeq : α σ = α 1 := by
    ext x
    rw [hfixF x (by rw [htop]; trivial)]
    simp
  exact hσ1 (hα hαeq)

variable {G : Type} [Group G] [Finite G] {V H T : Subgroup G}
  {X : Type} [Group X] [Finite X] {φ : ↥(kGenIn V H) →* X}

structure ModuleData (V H T : Subgroup G) {X : Type} [Group X] (φ : ↥(kGenIn V H) →* X)
    (E : Type) [CommGroup E] (α : X →* MulAut E) (ι : E →* G) : Prop where
  faithful : Function.Injective α
  exp_two : ∀ x : E, x * x = 1
  inj : Function.Injective ι
  range : ι.range = eSub V H T
  act : ∀ (k : ↥(kGenIn V H)) (x : E), ι (α (φ k) x) = k * ι x * (k : G)⁻¹

private theorem w85g_exists_conjAction (s : TailSetup V H T φ) :
    ∃ (E : Type) (_ : CommGroup E) (_ : Finite E) (α : X →* MulAut E) (ι : E →* G),
      ModuleData V H T φ E α ι := by
  classical
  have h83 := s.hyp83
  let E := ↥(eSub V H T)
  let cE : CommGroup E :=
    { (inferInstance : Group E) with mul_comm := h83.isMulCommutative_eSub.is_comm.comm }
  letI : CommGroup E := cE
  haveI : Finite E := inferInstance
  let ι : E →* G := (eSub V H T).subtype
  have hHEN : H ≤ Subgroup.normalizer (eSub V H T : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h83.eSub_le_H).mp h83.eSub_subgroupOf_normal
  have hKEN : kGenIn V H ≤ Subgroup.normalizer (eSub V H T : Set G) :=
    (kGenIn_le_H h83.le_H).trans hHEN
  let ψ : ↥(kGenIn V H) →* MulAut E :=
    (Subgroup.normalizerMonoidHom (H := eSub V H T)).comp (Subgroup.inclusion hKEN)
  have hψker : ∀ k : ↥(kGenIn V H), ψ k = 1 ↔ φ k = 1 := by
    intro k
    rw [s.bar.ker_iff k]
    show (Subgroup.normalizerMonoidHom (H := eSub V H T))
        (Subgroup.inclusion hKEN k) = 1 ↔ (k : G) ∈
          Subgroup.centralizer (eSub V H T : Set G)
    rw [← MonoidHom.mem_ker, Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf]
    rfl
  let α : X →* MulAut E :=
    (MonoidHom.liftOfSurjective (f := φ) s.bar.surjective) ⟨ψ, fun k hk => (hψker k).mpr hk⟩
  have hαφ : ∀ k, α (φ k) = ψ k := by
    intro k
    have h := MonoidHom.liftOfRightInverse_comp_apply
      (f := φ) (f_inv := Function.surjInv s.bar.surjective)
      (Function.rightInverse_surjInv s.bar.surjective)
      (⟨ψ, fun k hk => (hψker k).mpr hk⟩) k
    simpa [α] using h
  refine ⟨E, cE, inferInstance, α, ι, ?_, ?_, ?_, ?_, ?_⟩
  · intro a b hab
    obtain ⟨ka, rfl⟩ := s.bar.surjective a
    obtain ⟨kb, rfl⟩ := s.bar.surjective b
    rw [hαφ ka, hαφ kb] at hab
    have hk' : ψ (ka * kb⁻¹) = 1 := by
      rw [map_mul, map_inv, hab, mul_inv_cancel]
    have hk : φ (ka * kb⁻¹) = 1 := (hψker (ka * kb⁻¹)).mp hk'
    rw [map_mul, map_inv] at hk
    exact mul_inv_eq_one.mp hk
  · intro x
    refine Subtype.ext ?_
    rw [Subgroup.coe_mul, Subgroup.coe_one]
    simpa [pow_two] using h83.isElemAbelian_eSub.2 x x.2
  · exact (eSub V H T).subtype_injective
  · exact Subgroup.range_subtype _
  · intro k x
    have h1 : α (φ k) x = ψ k x := by rw [hαφ]
    rw [h1]
    show (((eSub V H T).normalizerMonoidHom (Subgroup.inclusion hKEN k)) x : G) =
      (k : G) * (x : G) * (k : G)⁻¹
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
    rfl

private theorem w85g_gap5_commutator_mem {V H T : Subgroup G} (h83 : Hyp83 V H T) {h : G}
    (hh : h ∈ H) {c : G} (hc : c ∈ conjSubgroup V h) {e : G} (he : e ∈ eSub V H T) :
    e * c * e⁻¹ * c⁻¹ ∈ eSub V H T ∧ e * c * e⁻¹ * c⁻¹ ∈ conjSubgroup V h := by
  have heC : e ∈ Subgroup.centralizer (eSub V H T : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact congrArg Subtype.val (h83.isMulCommutative_eSub.is_comm.comm ⟨a, ha⟩ ⟨e, he⟩)
  have hN : e ∈ Subgroup.normalizer (conjSubgroup V h : Set G) :=
    h83.mem_normalizer_conjSubgroup_of_mem_centralizer hh heC
  have h1 : e * c * e⁻¹ ∈ conjSubgroup V h := (Subgroup.mem_normalizer_iff.1 hN c).1 hc
  have hcH : c ∈ H := by
    have h2 : h * c * h⁻¹ ∈ V := mem_conjSubgroup_iff.1 hc
    have h3 : h⁻¹ * (h * c * h⁻¹) * h ∈ H :=
      H.mul_mem (H.mul_mem (H.inv_mem hh) (h83.le_H h2)) hh
    rwa [show h⁻¹ * (h * c * h⁻¹) * h = c by group] at h3
  have hE := (Subgroup.normal_subgroupOf_iff h83.eSub_le_H).mp h83.eSub_subgroupOf_normal
  have h4 : c * e⁻¹ * c⁻¹ ∈ eSub V H T := hE e⁻¹ c ((eSub V H T).inv_mem he) hcH
  refine ⟨?_, (conjSubgroup V h).mul_mem h1 ((conjSubgroup V h).inv_mem hc)⟩
  simpa [mul_assoc] using (eSub V H T).mul_mem he h4

private theorem w85g_commE_ti (s : TailSetup V H T φ) {t : X}
    (ht : barSub (kGenIn V H) φ V = Subgroup.zpowers t)
    {E : Type} [CommGroup E] {α : X →* MulAut E} {ι : E →* G}
    (hM : ModuleData V H T φ E α ι) :
    ∀ d ∈ {y : X | IsConj t y}, ∀ d' ∈ {y : X | IsConj t y}, d ≠ d' →
      commE α d ⊓ commE α d' = ⊥ := by
  classical
  intro d hd d' hd' hne
  have h83 := s.hyp83
  have ht_mem : t ∈ barSub (kGenIn V H) φ V := by
    rw [ht]; exact Subgroup.mem_zpowers t
  have ht2 : t * t = 1 := by
    have h := (isElemAbelian_barSub h83.elemAbelian φ).2 t ht_mem
    simpa [pow_two] using h
  have hd1 : d ≠ 1 := by
    intro h1
    apply hne
    have ht1 : t = 1 := isConj_one_left.mp (by simpa [h1] using hd)
    rw [ht1] at hd'
    rw [h1, isConj_one_right.mp hd']
  have hd'1 : d' ≠ 1 := by
    intro h1
    apply hne
    have ht1 : t = 1 := isConj_one_left.mp (by simpa [h1] using hd')
    rw [ht1] at hd
    rw [isConj_one_right.mp hd, h1]
  obtain ⟨v, hvV, hvφ⟩ := mem_barSub.mp ht_mem
  obtain ⟨w, hw⟩ := isConj_iff.mp hd
  obtain ⟨w', hw'⟩ := isConj_iff.mp hd'
  obtain ⟨k, hk⟩ := s.bar.surjective w
  obtain ⟨k', hk'⟩ := s.bar.surjective w'
  let k₁ : ↥(kGenIn V H) := k⁻¹
  let k₁' : ↥(kGenIn V H) := k'⁻¹
  let X : Subgroup G := conjSubgroup V (k₁ : G)
  let Y : Subgroup G := conjSubgroup V (k₁' : G)
  have hk1 : φ k₁ = w⁻¹ := by
    show φ k⁻¹ = w⁻¹
    rw [map_inv, hk]
  have hk1' : φ k₁' = (w')⁻¹ := by
    show φ k'⁻¹ = (w')⁻¹
    rw [map_inv, hk']
  have hd_eq : d = φ (k * v * k⁻¹) := by
    rw [← hw, ← hk, ← hvφ, map_mul, map_mul, map_inv]
  have hd_eq' : d' = φ (k' * v * k'⁻¹) := by
    rw [← hw', ← hk', ← hvφ, map_mul, map_mul, map_inv]
  have hbar_d : barSub (kGenIn V H) φ X = Subgroup.zpowers d := by
    show barSub (kGenIn V H) φ (conjSubgroup V (k₁ : G)) = Subgroup.zpowers d
    rw [barSub_conjSubgroup, hk1, ht, conjSubgroup, inv_inv, MonoidHom.map_zpowers]
    change Subgroup.zpowers ((MulAut.conj w) t) = Subgroup.zpowers d
    rw [MulAut.conj_apply, ← hw]
  have hbar_d' : barSub (kGenIn V H) φ Y = Subgroup.zpowers d' := by
    show barSub (kGenIn V H) φ (conjSubgroup V (k₁' : G)) = Subgroup.zpowers d'
    rw [barSub_conjSubgroup, hk1', ht, conjSubgroup, inv_inv, MonoidHom.map_zpowers]
    change Subgroup.zpowers ((MulAut.conj w') t) = Subgroup.zpowers d'
    rw [MulAut.conj_apply, ← hw']
  have hXmem : ((k * v * k⁻¹ : ↥(kGenIn V H)) : G) ∈ X := by
    show ((k * v * k⁻¹ : ↥(kGenIn V H)) : G) ∈ conjSubgroup V (k₁ : G)
    rw [mem_conjSubgroup_iff]
    have hk1g : (k₁ : G) = (k : G)⁻¹ := rfl
    rw [hk1g]
    have hsimp : (k : G)⁻¹ * ((k * v * k⁻¹ : ↥(kGenIn V H)) : G) * ((k : G)⁻¹)⁻¹ = (v : G) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [hsimp]
    exact hvV
  have hYmem : ((k' * v * k'⁻¹ : ↥(kGenIn V H)) : G) ∈ Y := by
    show ((k' * v * k'⁻¹ : ↥(kGenIn V H)) : G) ∈ conjSubgroup V (k₁' : G)
    rw [mem_conjSubgroup_iff]
    have hk1g : (k₁' : G) = (k' : G)⁻¹ := rfl
    rw [hk1g]
    have hsimp : (k' : G)⁻¹ * ((k' * v * k'⁻¹ : ↥(kGenIn V H)) : G) * ((k' : G)⁻¹)⁻¹ = (v : G) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [hsimp]
    exact hvV
  have hleX : ∀ z ∈ commE α d, ι z ∈ X := by
    intro z hz
    rw [w85g_mem_commE] at hz
    obtain ⟨y, hy⟩ := hz
    rw [← hy]
    have hyE : ι y ∈ eSub V H T := hM.range ▸ (MonoidHom.mem_range.mpr ⟨y, rfl⟩)
    have hh : (k₁ : G) ∈ H := by
      show (k : G)⁻¹ ∈ H
      exact H.inv_mem (kGenIn_le_H h83.le_H k.2)
    have hcomm := w85g_gap5_commutator_mem h83 hh hXmem hyE
    have hkey : ι (y * (α d y)⁻¹) =
        ι y * ((k * v * k⁻¹ : ↥(kGenIn V H)) : G) * (ι y)⁻¹ *
          ((k * v * k⁻¹ : ↥(kGenIn V H)) : G)⁻¹ := by
      rw [map_mul, map_inv, hd_eq, hM.act]
      group
    rw [hkey]
    exact hcomm.2
  have hleY : ∀ z ∈ commE α d', ι z ∈ Y := by
    intro z hz
    rw [w85g_mem_commE] at hz
    obtain ⟨y, hy⟩ := hz
    rw [← hy]
    have hyE : ι y ∈ eSub V H T := hM.range ▸ (MonoidHom.mem_range.mpr ⟨y, rfl⟩)
    have hh : (k₁' : G) ∈ H := by
      show (k' : G)⁻¹ ∈ H
      exact H.inv_mem (kGenIn_le_H h83.le_H k'.2)
    have hcomm := w85g_gap5_commutator_mem h83 hh hYmem hyE
    have hkey : ι (y * (α d' y)⁻¹) =
        ι y * ((k' * v * k'⁻¹ : ↥(kGenIn V H)) : G) * (ι y)⁻¹ *
          ((k' * v * k'⁻¹ : ↥(kGenIn V H)) : G)⁻¹ := by
      rw [map_mul, map_inv, hd_eq', hM.act]
      group
    rw [hkey]
    exact hcomm.2
  have hXne : X ≠ Y := by
    intro hXY
    apply hne
    have hd_in : d ∈ Subgroup.zpowers d' := by
      rw [← hbar_d', ← hXY, hbar_d]
      exact Subgroup.mem_zpowers d
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hd_in
    have hd2 : d * d = 1 := by
      rw [← hw, show (w * t * w⁻¹) * (w * t * w⁻¹) = w * (t * t) * w⁻¹ by group, ht2]
      group
    have hd'2 : d' * d' = 1 := by
      rw [← hw', show (w' * t * (w')⁻¹) * (w' * t * (w')⁻¹) = w' * (t * t) * (w')⁻¹ by group, ht2]
      group
    rcases w85g_zpow_eq_one_or_of_sq hd'2 n with h | h
    · exact absurd (hn.symm.trans h) hd1
    · exact hn.symm.trans h
  rw [eq_bot_iff]
  intro z hz
  obtain ⟨hz1, hz2⟩ := Subgroup.mem_inf.mp hz
  rw [Subgroup.mem_bot]
  apply hM.inj
  rw [map_one]
  have hzX : ι z ∈ X := hleX z hz1
  have hzY : ι z ∈ Y := hleY z hz2
  have hbot : X ⊓ Y = ⊥ := by
    rcases inf_conjSubgroup_eq_bot_or_eq h83.isTI (k₁ : G) (k₁' : G) with h | h
    · exact h
    · exact absurd h hXne
  have hzin : ι z ∈ X ⊓ Y := Subgroup.mem_inf.mpr ⟨hzX, hzY⟩
  rw [hbot, Subgroup.mem_bot] at hzin
  exact hzin

theorem exists_moduleData (s : TailSetup V H T φ) {t : X}
    (ht : barSub (kGenIn V H) φ V = Subgroup.zpowers t) :
    ∃ (E : Type) (_ : CommGroup E) (_ : Finite E) (α : X →* MulAut E) (ι : E →* G),
      ModuleData V H T φ E α ι ∧
        ∀ d ∈ {y : X | IsConj t y}, ∀ d' ∈ {y : X | IsConj t y}, d ≠ d' →
          commE α d ⊓ commE α d' = ⊥ := by
  obtain ⟨E, cE, fE, α, ι, hM⟩ := w85g_exists_conjAction s
  exact ⟨E, cE, fE, α, ι, hM, w85g_commE_ti s ht hM⟩

private theorem w85g_commutator_commutator_eq_of_coprime {A : Type} [Group A]
    {P X : Subgroup A} (hXP : X ≤ Subgroup.normalizer (P : Set A))
    (hcop : Nat.Coprime (Nat.card X) (Nat.card P)) :
    ⁅⁅P, X⁆, X⁆ = ⁅P, X⁆ := by
  classical
  have : Subgroup.Normalizes X P := ⟨hXP⟩
  have h2 : CFSG.commutatorAction₂ (A := ↥X) (G := ↥P) =
      CFSG.commutatorAction (A := ↥X) (G := ↥P) :=
    CFSG.commutatorAction₂_eq_commutatorAction_of_coprime (G := ↥P) (A := ↥X) hcop
  have hmap : (CFSG.commutatorAction (A := ↥X) (G := ↥P)).map P.subtype = ⁅P, X⁆ :=
    CFSG.commutatorAction_subgroup_conj_map_eq_commutator P X hXP
  have hmap2 : (CFSG.commutatorAction₂ (A := ↥X) (G := ↥P)).map P.subtype ≤ ⁅⁅P, X⁆, X⁆ := by
    let C : Subgroup ↥P := CFSG.commutatorAction (A := ↥X) (G := ↥P)
    let S : Set ↥P := {x : ↥P | ∃ a : ↥X, ∃ h : ↥P, h ∈ C ∧ x = h⁻¹ * (a • h)}
    calc (CFSG.commutatorAction₂ (A := ↥X) (G := ↥P)).map P.subtype =
          (Subgroup.closure S).map P.subtype := rfl
      _ = Subgroup.closure (P.subtype '' S) := by
        simpa using (MonoidHom.map_closure (f := P.subtype) S)
      _ ≤ ⁅⁅P, X⁆, X⁆ := by
        refine (Subgroup.closure_le (K := ⁅⁅P, X⁆, X⁆)).2 ?_
        rintro _ ⟨y, hy, rfl⟩
        rcases hy with ⟨a, h, hhC, rfl⟩
        have hhcomm : (h : A) ∈ ⁅P, X⁆ := by
          rw [← hmap]
          exact Subgroup.mem_map_of_mem P.subtype hhC
        have hcomm : ⁅(h : A)⁻¹, (a : A)⁆ ∈ ⁅⁅P, X⁆, X⁆ :=
          Subgroup.commutator_mem_commutator ((⁅P, X⁆ : Subgroup A).inv_mem hhcomm) a.2
        simpa [commutatorElement_def, Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe,
          hXP, mul_assoc] using hcomm
  refine le_antisymm ?_ fun x hx => ?_
  · exact (Subgroup.le_normalizer_iff_commutator_le_left).mp
      (Subgroup.normalizer_commutator_ge_right P X)
  · rw [← hmap, ← h2] at hx
    exact hmap2 hx

private theorem w85g_exists_ne_one_fixed {W : Type} [CommGroup W] [Finite W]
    (hW : Even (Nat.card W)) (T : Subgroup (MulAut W)) (hT : IsPGroup 2 T) :
    ∃ v : W, v ≠ 1 ∧ ∀ x ∈ T, x v = v := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := hT.card_modEq_card_fixedPoints W
  have hF1 : (1 : W) ∈ MulAction.fixedPoints ↥T W := fun t => by
    show (t : MulAut W) 1 = 1
    exact map_one _
  haveI : Nonempty (MulAction.fixedPoints ↥T W) := ⟨⟨1, hF1⟩⟩
  have h' : Nat.card W % 2 = Nat.card (MulAction.fixedPoints ↥T W) % 2 := h
  have hFeven : Nat.card (MulAction.fixedPoints ↥T W) % 2 = 0 := by
    rw [← h']
    exact Nat.even_iff.mp hW
  have hgt : 1 < Nat.card (MulAction.fixedPoints ↥T W) := by
    by_contra hle
    have hpos : 0 < Nat.card (MulAction.fixedPoints ↥T W) := Nat.card_pos
    have : Nat.card (MulAction.fixedPoints ↥T W) = 1 := by omega
    omega
  haveI : Nontrivial (MulAction.fixedPoints ↥T W) := Finite.one_lt_card_iff_nontrivial.mp hgt
  obtain ⟨c, hc⟩ := exists_ne (⟨1, hF1⟩ : MulAction.fixedPoints ↥T W)
  refine ⟨c, fun h1 => hc (Subtype.ext h1), fun x hx => ?_⟩
  have := c.2 ⟨x, hx⟩
  exact this

private theorem w85g_R_ne_bot {Y : Type} [Group Y] [Finite Y] {m : ℕ}
    {e : Y ⧸ fusionOddCore Y ≃* Perm (Fin m)} {t : Y} {P : Sylow 2 Y} (hS : SymSetting e t P)
    (hnc : ¬ fusionOddCore Y ≤ Subgroup.center Y) :
    (⁅fusionOddCore Y, Subgroup.zpowers t⁆ : Subgroup Y) ≠ ⊥ := by
  intro hbot
  apply hnc
  have htC : t ∈ Subgroup.centralizer (fusionOddCore Y : Set Y) := by
    rw [Subgroup.mem_centralizer_iff]
    intro o ho
    have h1 : ⁅o, t⁆ ∈ (⁅fusionOddCore Y, Subgroup.zpowers t⁆ : Subgroup Y) :=
      Subgroup.commutator_mem_commutator ho (Subgroup.mem_zpowers t)
    rw [hbot, Subgroup.mem_bot, commutatorElement_def] at h1
    have h2 : o * t * o⁻¹ = t := by
      have := congrArg (· * t) h1
      simpa [mul_assoc] using this
    have h3 : o * t = t * o := by
      have := congrArg (· * o) h2
      simpa [mul_assoc] using this
    exact h3
  have hXle : (⊤ : Subgroup Y) ≤ Subgroup.centralizer (fusionOddCore Y : Set Y) := by
    rw [← hS.oddClass.2.2, Subgroup.closure_le]
    intro d hd
    obtain ⟨w, hw⟩ := isConj_iff.mp hd
    rw [← hw]
    exact (inferInstance : (Subgroup.centralizer (fusionOddCore Y : Set Y)).Normal).conj_mem
      t htC w
  intro o ho
  rw [Subgroup.mem_center_iff]
  intro y
  exact (Subgroup.mem_centralizer_iff.mp (hXle (Subgroup.mem_top y)) o ho).symm

private theorem w85g_R_not_centralizes_t {Y : Type} [Group Y] [Finite Y] {m : ℕ}
    {e : Y ⧸ fusionOddCore Y ≃* Perm (Fin m)} {t : Y} {P : Sylow 2 Y} (hS : SymSetting e t P)
    (hnc : ¬ fusionOddCore Y ≤ Subgroup.center Y) :
    ¬ (⁅fusionOddCore Y, Subgroup.zpowers t⁆ : Subgroup Y) ≤
        Subgroup.centralizer ({t} : Set Y) := by
  intro hle
  have hRne := w85g_R_ne_bot hS hnc
  have hcop : Nat.Coprime (Nat.card (Subgroup.zpowers t)) (Nat.card (fusionOddCore Y)) := by
    have hodd := w85g_odd_card_fusionOddCore (Y := Y)
    have hdvd : Nat.card (Subgroup.zpowers t) ∣ 2 := by
      rw [Nat.card_zpowers]
      exact orderOf_dvd_iff_pow_eq_one.mpr (by rw [pow_two]; exact hS.mul_self)
    exact Nat.Coprime.of_dvd_left hdvd (Nat.coprime_two_left.mpr hodd)
  have hnorm : Subgroup.zpowers t ≤ Subgroup.normalizer (fusionOddCore Y : Set Y) := by
    rw [Subgroup.normalizer_eq_top_iff.mpr (inferInstance : (fusionOddCore Y).Normal)]
    exact le_top
  have heq : (⁅⁅fusionOddCore Y, Subgroup.zpowers t⁆, Subgroup.zpowers t⁆ : Subgroup Y) =
      ⁅fusionOddCore Y, Subgroup.zpowers t⁆ :=
    w85g_commutator_commutator_eq_of_coprime hnorm hcop
  have hsub : (⁅⁅fusionOddCore Y, Subgroup.zpowers t⁆, Subgroup.zpowers t⁆ : Subgroup Y) ≤ ⊥ := by
    rw [Subgroup.commutator_le]
    intro r hr s hs
    have hrC : r ∈ Subgroup.centralizer ({t} : Set Y) := hle hr
    have hrt : Commute t r := Subgroup.mem_centralizer_iff.mp hrC t (Set.mem_singleton t)
    have hcomm : Commute r s := by
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hs
      exact hrt.symm.zpow_right n
    rw [Subgroup.mem_bot, commutatorElement_def, hcomm.eq]
    group
  rw [heq] at hsub
  exact hRne (le_bot_iff.mp hsub)

private theorem w85g_conjAut_R (s : TailSetup V H T φ) (hV : Hyp7 V)
    (hT : IsSylowIn 2 T (H ⊓ Subgroup.normalizer (V : Set G))) {t : X}
    (ht : barSub (kGenIn V H) φ V = Subgroup.zpowers t) {m : ℕ}
    {e : X ⧸ fusionOddCore X ≃* Perm (Fin m)} {P : Sylow 2 X} (hS : SymSetting e t P)
    {a : G} (ha : a ∈ T) :
    ∃ σ : X ≃* X, (∀ k : ↥(kGenIn V H),
      σ (φ k) = φ ⟨a * (k : G) * a⁻¹,
        (Subgroup.mem_normalizer_iff.1 (s.hyp83.le_normalizer_kGenIn ha) (k : G)).1 k.2⟩) ∧
      ⁅fusionOddCore X, Subgroup.zpowers t⁆.map σ.toMonoidHom =
        ⁅fusionOddCore X, Subgroup.zpowers t⁆ := by
  classical
  have h83 := s.hyp83
  have haH : a ∈ H := h83.T_le_H ha
  have haV : a ∈ Subgroup.normalizer (V : Set G) := (hT.le ha).2
  have hNa : a ∈ Subgroup.normalizer (kGenIn V H : Set G) := h83.le_normalizer_kGenIn ha
  have hNa' : a⁻¹ ∈ Subgroup.normalizer (kGenIn V H : Set G) := Subgroup.inv_mem _ hNa
  have hKmem : ∀ k : ↥(kGenIn V H), a * (k : G) * a⁻¹ ∈ kGenIn V H := fun k =>
    (Subgroup.mem_normalizer_iff.1 hNa (k : G)).1 k.2
  let cj : ↥(kGenIn V H) →* ↥(kGenIn V H) :=
    { toFun := fun k => ⟨a * k * a⁻¹, hKmem k⟩
      map_one' := by ext; simp
      map_mul' := fun x y => by ext; simp [mul_assoc] }
  have hcj_coe : ∀ k, ((cj k : ↥(kGenIn V H)) : G) = a * (k : G) * a⁻¹ := fun k => rfl
  have hcj_ker : (φ.comp cj).ker = φ.ker := by
    ext k
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MonoidHom.mem_ker,
      s.bar.ker_iff (cj k), s.bar.ker_iff k]
    constructor
    · intro hk
      have := h83.conj_mem_centralizer_eSub (H.inv_mem haH) hk
      simpa [hcj_coe, mul_assoc] using this
    · intro hk
      exact h83.conj_mem_centralizer_eSub haH hk
  let σ₀ : X →* X := (φ.liftOfSurjective s.bar.surjective) ⟨φ.comp cj, hcj_ker.ge⟩
  have hσ₀ : ∀ k, σ₀ (φ k) = φ (cj k) := by
    intro k
    have h := MonoidHom.liftOfRightInverse_comp_apply (f := φ)
      (f_inv := Function.surjInv s.bar.surjective)
      (Function.rightInverse_surjInv s.bar.surjective) (⟨φ.comp cj, hcj_ker.ge⟩) k
    simpa [σ₀] using h
  have hcji : Function.Injective σ₀ := by
    intro x y hxy
    obtain ⟨kx, rfl⟩ := s.bar.surjective x
    obtain ⟨ky, rfl⟩ := s.bar.surjective y
    rw [hσ₀ kx, hσ₀ ky] at hxy
    have hk : kx * ky⁻¹ ∈ (φ.comp cj).ker := by
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply]
      rw [show cj (kx * ky⁻¹) = cj kx * (cj ky)⁻¹ by rw [map_mul, map_inv]]
      rw [map_mul, map_inv, hxy, mul_inv_cancel]
    have hk2 : kx * ky⁻¹ ∈ φ.ker := hcj_ker.le hk
    rw [MonoidHom.mem_ker, map_mul, map_inv, mul_inv_eq_one] at hk2
    rw [hk2]
  have hcjsurj : Function.Surjective (φ.comp cj) := by
    intro y
    obtain ⟨k, hk⟩ := s.bar.surjective y
    have hkK : a⁻¹ * (k : G) * a ∈ kGenIn V H := by
      simpa only [inv_inv] using (Subgroup.mem_normalizer_iff.1 hNa' (k : G)).1 k.2
    refine ⟨⟨a⁻¹ * (k : G) * a, hkK⟩, ?_⟩
    show φ (cj ⟨a⁻¹ * (k : G) * a, hkK⟩) = y
    have he : cj ⟨a⁻¹ * (k : G) * a, hkK⟩ = k := by ext; simp [cj, mul_assoc]
    rw [he, hk]
  have hcjs : Function.Surjective σ₀ := by
    intro y
    obtain ⟨w, hw⟩ := hcjsurj y
    exact ⟨φ w, by rw [hσ₀ w]; exact hw⟩
  let σ : X ≃* X := MulEquiv.ofBijective σ₀ ⟨hcji, hcjs⟩
  have hσ : ∀ k, σ (φ k) = φ (cj k) := fun k => hσ₀ k
  have ht1 : t ≠ 1 := by
    intro h
    obtain ⟨a', b', hab, hswap⟩ := hS.swap
    rw [h, map_one] at hswap
    exact hab (Equiv.swap_eq_one_iff.mp hswap.symm)
  have hσt : σ t = t := by
    obtain ⟨v, hvV, hvφ⟩ := mem_barSub.mp (by rw [ht]; exact Subgroup.mem_zpowers t :
      t ∈ barSub (kGenIn V H) φ V)
    have hmem : σ t ∈ Subgroup.zpowers t := by
      have h1 : σ t = φ (cj v) := by rw [← hvφ, hσ v]
      rw [h1, ← ht]
      refine mem_barSub.mpr ⟨cj v, ?_, rfl⟩
      rw [hcj_coe]
      exact (Subgroup.mem_normalizer_iff.1 haV (v : G)).1 hvV
    have hne : σ t ≠ 1 := by
      intro h
      have h' : σ₀ t = σ₀ 1 := by
        change σ t = σ 1
        rw [h, map_one]
      exact ht1 (hcji h')
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hmem
    rcases w85g_zpow_eq_one_or_of_sq hS.mul_self n with h | h
    · exact absurd (hn.symm.trans h) hne
    · exact hn.symm.trans h
  refine ⟨σ, fun k => hσ k, ?_⟩
  rw [Subgroup.map_commutator]
  congr 1
  · exact w85g_fusionOddCore_map_mulEquiv σ
  · rw [MonoidHom.map_zpowers]
    exact congrArg Subgroup.zpowers hσt

private theorem w85g_normalizer_zpowers_eq_centralizer (A : Type) [Group A] :
    ∀ (u : A), u * u = 1 →
      Subgroup.normalizer (Subgroup.zpowers u : Set A) = Subgroup.centralizer ({u} : Set A) := by
  intro u hu
  apply le_antisymm
  · intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    rw [Subgroup.mem_normalizer_iff] at hx
    have h1 : x * u * x⁻¹ ∈ Subgroup.zpowers u := (hx u).mp (Subgroup.mem_zpowers u)
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp h1
    rcases w85g_zpow_eq_one_or_of_sq hu n with h | h
    · have hx1 : x * u * x⁻¹ = 1 := hn.symm.trans h
      have hu1 : u = 1 := by
        have h2 : x * u = x * 1 := by
          have := congrArg (· * x) hx1
          simpa [mul_assoc] using this
        exact mul_left_cancel h2
      rw [hu1]; simp
    · have hxu : x * u * x⁻¹ = u := hn.symm.trans h
      calc u * x = x * u * x⁻¹ * x := by rw [hxu]
        _ = x * u := by group
  · intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    rw [Subgroup.mem_centralizer_iff] at hx
    have h : x * u * x⁻¹ = u := by
      have := hx u (Set.mem_singleton u)
      rw [← this]; group
    have hfix : ∀ n : ℤ, x * u ^ n * x⁻¹ = u ^ n := fun n => by rw [← conj_zpow, h]
    constructor
    · intro hy
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hy
      rw [← hn, hfix n]
      exact Subgroup.mem_zpowers_iff.mpr ⟨n, rfl⟩
    · intro hy
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hy
      have heq : y = u ^ n := by
        have h1 : x * y * x⁻¹ = u ^ n := hn.symm
        have h2 : x * y * x⁻¹ = x * u ^ n * x⁻¹ := by rw [h1, hfix n]
        have h3 : x * y = x * u ^ n := by
          have := congrArg (· * x) h2
          simpa [mul_assoc] using this
        exact mul_left_cancel h3
      rw [heq]
      exact Subgroup.mem_zpowers_iff.mpr ⟨n, rfl⟩

private theorem w85g_exists_tauAction (s : TailSetup V H T φ) {E : Type} [CommGroup E]
    {α : X →* MulAut E} {ι : E →* G} (hM : ModuleData V H T φ E α ι) :
    ∃ τ : ↥T →* MulAut E, ∀ (a : ↥T) (y : E), ι (τ a y) = (a : G) * ι y * (a : G)⁻¹ := by
  classical
  have h83 := s.hyp83
  have hHEN : H ≤ Subgroup.normalizer (eSub V H T : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h83.eSub_le_H).mp h83.eSub_subgroupOf_normal
  have hTEN : T ≤ Subgroup.normalizer (eSub V H T : Set G) := h83.T_le_H.trans hHEN
  let f : E →* ↥(eSub V H T) :=
    { toFun := fun y => ⟨ι y, hM.range ▸ MonoidHom.mem_range.mpr ⟨y, rfl⟩⟩
      map_one' := Subtype.ext (map_one ι)
      map_mul' := fun x y => Subtype.ext (map_mul ι x y) }
  have hfinj : Function.Injective f := fun x y hxy => hM.inj (Subtype.ext_iff.mp hxy)
  have hfsurj : Function.Surjective f := by
    intro z
    have hz : (z : G) ∈ ι.range := hM.range.symm ▸ z.2
    obtain ⟨y, hy⟩ := MonoidHom.mem_range.mp hz
    exact ⟨y, Subtype.ext hy⟩
  let eι : E ≃* ↥(eSub V H T) := MulEquiv.ofBijective f ⟨hfinj, hfsurj⟩
  let normT : ↥T →* MulAut ↥(eSub V H T) :=
    (Subgroup.normalizerMonoidHom (H := eSub V H T)).comp (Subgroup.inclusion hTEN)
  let tau : ↥T →* MulAut E := ((MulAut.congr eι).symm).toMonoidHom.comp normT
  refine ⟨tau, ?_⟩
  intro a y
  have hτ : tau a y = eι.symm (normT a (eι y)) := rfl
  have hval : ∀ z : ↥(eSub V H T), ι (eι.symm z) = (z : G) := by
    intro z
    have h : (f (eι.symm z) : G) = (z : G) :=
      congrArg Subtype.val (MulEquiv.apply_symm_apply eι z)
    exact h
  have hnorm : (normT a (eι y) : G) = (a : G) * (eι y : G) * (a : G)⁻¹ := by
    simp only [normT, MonoidHom.comp_apply, Subgroup.normalizerMonoidHom_apply_apply_coe]
    rfl
  rw [hτ, hval, hnorm]
  rfl

private theorem w85g_exists_fixed_T (s : TailSetup V H T φ) {m : ℕ}
    {e : X ⧸ fusionOddCore X ≃* Perm (Fin m)} {t : X} {P : Sylow 2 X} (hS : SymSetting e t P)
    (ht : barSub (kGenIn V H) φ V = Subgroup.zpowers t) {E : Type} [CommGroup E]
    {α : X →* MulAut E} {ι : E →* G} (hM : ModuleData V H T φ E α ι) {x : E}
    (hx : ∀ r ∈ (⁅fusionOddCore X, Subgroup.zpowers t⁆ : Subgroup X), α r x = x) (hx1 : x ≠ 1) :
    ∃ z : E, z ≠ 1 ∧ (∀ r ∈ (⁅fusionOddCore X, Subgroup.zpowers t⁆ : Subgroup X), α r z = z) ∧
      ∀ a ∈ T, (a : G) * ι z * (a : G)⁻¹ = ι z := by
  classical
  haveI : Finite E := Finite.of_injective ι hM.inj
  have h83 := s.hyp83
  have hV : Hyp7 V := ⟨h83.elemAbelian, h83.two_lt_card, h83.isTI⟩
  have hT : IsSylowIn 2 T (H ⊓ Subgroup.normalizer (V : Set G)) := h83.sylow
  let R : Subgroup X := ⁅fusionOddCore X, Subgroup.zpowers t⁆
  let C : Subgroup E :=
    { carrier := {y : E | ∀ r ∈ R, α r y = y}
      one_mem' := by intro r _; simp
      mul_mem' := by intro a b ha hb r hr; rw [map_mul, ha r hr, hb r hr]
      inv_mem' := by intro a ha r hr; rw [map_inv, ha r hr] }
  obtain ⟨τ, hτ⟩ := w85g_exists_tauAction s hM
  have hE2 : IsPGroup 2 E :=
    isPGroup_iff_pow_pow_eq_one.mpr (fun y => ⟨1, by simpa [pow_two] using hM.exp_two y⟩)
  have hτC : ∀ a : ↥T, ∀ y ∈ C, τ a y ∈ C := by
    intro a y hy r hr
    obtain ⟨σ, hσφ, hσR⟩ := w85g_conjAut_R s hV hT ht hS a.2
    have hequiv : ∀ x' : X, τ a (α x' y) = α (σ x') (τ a y) := by
      intro x'
      obtain ⟨k, rfl⟩ := s.bar.surjective x'
      apply hM.inj
      rw [hτ a (α (φ k) y), hM.act k y, hσφ k, hM.act, hτ a y]
      group
    have hsr : σ.symm r ∈ R := by
      have hmem : r ∈ R.map σ.toMonoidHom := by
        rw [show R.map σ.toMonoidHom = R from hσR]
        exact hr
      obtain ⟨s', hs'R, hs'r⟩ := Subgroup.mem_map.mp hmem
      have hs' : s' = σ.symm r := by
        apply σ.injective
        rw [show σ s' = r from by simpa using hs'r]
        simp
      rw [← hs']
      exact hs'R
    calc α r (τ a y) = α (σ (σ.symm r)) (τ a y) := by rw [MulEquiv.apply_symm_apply]
      _ = τ a (α (σ.symm r) y) := (hequiv (σ.symm r)).symm
      _ = τ a y := by rw [hy (σ.symm r) hsr]
  let ρ : ↥T →* MulAut ↥C :=
    { toFun := fun a =>
        { toFun := fun y => ⟨τ a y, hτC a y y.2⟩
          invFun := fun y => ⟨τ a⁻¹ y, hτC a⁻¹ y y.2⟩
          left_inv := fun y => Subtype.ext (by simp)
          right_inv := fun y => Subtype.ext (by simp)
          map_mul' := fun y y' => Subtype.ext (by simp [map_mul]) }
      map_one' := by ext y; simp
      map_mul' := fun a b => by ext y; simp [map_mul] }
  have hCne : C ≠ ⊥ := by
    intro hbot
    apply hx1
    have hxC : x ∈ C := fun r hr => hx r hr
    rw [hbot] at hxC
    exact Subgroup.mem_bot.mp hxC
  have hC2 : IsPGroup 2 C := hE2.of_injective C.subtype C.subtype_injective
  have hCeven : Even (Nat.card C) := by
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2)).mp hC2
    haveI : Nontrivial C := (Subgroup.nontrivial_iff_ne_bot C).mpr hCne
    have hlt : 1 < 2 ^ k := by rw [← hk]; exact Finite.one_lt_card
    have hk0 : k ≠ 0 := by
      intro h0; rw [h0, pow_zero] at hlt; omega
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk0
    rw [hk]
    exact ⟨2 ^ j, by rw [pow_succ]; ring⟩
  have hTgrp : IsPGroup 2 ↥T := h83.sylow.isPGroup
  have hρgrp : IsPGroup 2 ρ.range :=
    hTgrp.of_surjective ρ.rangeRestrict ρ.rangeRestrict_surjective
  obtain ⟨z, hz1, hzfix⟩ := w85g_exists_ne_one_fixed hCeven ρ.range hρgrp
  refine ⟨(z : E), fun h => hz1 (Subtype.ext h), fun r hr => z.2 r hr, fun a ha => ?_⟩
  have hzmem : ρ ⟨a, ha⟩ ∈ ρ.range := MonoidHom.mem_range.mpr ⟨⟨a, ha⟩, rfl⟩
  have hfix : ρ ⟨a, ha⟩ z = z := hzfix _ hzmem
  have hval : τ ⟨a, ha⟩ (z : E) = (z : E) := congrArg Subtype.val hfix
  calc (a : G) * ι (z : E) * (a : G)⁻¹ = ι (τ ⟨a, ha⟩ (z : E)) :=
        (hτ ⟨a, ha⟩ (z : E)).symm
    _ = ι (z : E) := by rw [hval]

theorem centralizer_E_R_eq_bot (hi : CentralizersInM V H T) (s : TailSetup V H T φ) {m : ℕ}
    {e : X ⧸ fusionOddCore X ≃* Perm (Fin m)} {t : X} {P : Sylow 2 X} (hS : SymSetting e t P)
    (ht : barSub (kGenIn V H) φ V = Subgroup.zpowers t)
    (hP : (P : Subgroup X) = barSub (kGenIn V H) φ T)
    (hnc : ¬ fusionOddCore X ≤ Subgroup.center X) {E : Type} [CommGroup E] {α : X →* MulAut E}
    {ι : E →* G} (hM : ModuleData V H T φ E α ι) :
    ∀ x : E, (∀ r ∈ ⁅fusionOddCore X, Subgroup.zpowers t⁆, α r x = x) → x = 1 := by
  intro x hx
  by_contra hx1
  obtain ⟨z, hz1, hzR, hzT⟩ := w85g_exists_fixed_T s hS ht hM hx hx1
  have h83 := s.hyp83
  have hzE : ι z ∈ eSub V H T := hM.range ▸ MonoidHom.mem_range.mpr ⟨z, rfl⟩
  have hzTmem : ι z ∈ T := h83.pCoreOf_le_T (h83.eSub_le_pCoreOf hzE)
  have hzne : ι z ≠ 1 := fun h => hz1 (hM.inj (by simp [h]))
  have hzcomm : ∀ a ∈ T, (ι z) * a = a * (ι z) := by
    intro a ha
    have h := hzT a ha
    have h' : a * ι z = ι z * a := by
      have := congrArg (· * a) h
      simpa [mul_assoc] using this
    exact h'.symm
  obtain ⟨r, hrR, hrC⟩ :=
    Set.not_subset.mp (w85g_R_not_centralizes_t hS hnc)
  obtain ⟨k, rfl⟩ := s.bar.surjective r
  have hαz : α (φ k) z = z := hzR (φ k) hrR
  have hkz : (k : G) * ι z * (k : G)⁻¹ = ι z := by
    have h := congrArg ι hαz
    rw [hM.act k z] at h
    exact h
  have hkcomm : (k : G) * ι z = ι z * (k : G) := by
    have := congrArg (· * (k : G)) hkz
    simpa [mul_assoc] using this
  have hkH : (k : G) ∈ H := kGenIn_le_H h83.le_H k.2
  have hmem : (k : G) ∈ H ⊓ Subgroup.centralizer ({ι z} : Set G) := by
    refine ⟨hkH, ?_⟩
    intro b hb
    rw [Set.mem_singleton_iff] at hb
    rw [hb]
    exact hkcomm.symm
  have hknorm : (k : G) ∈ Subgroup.normalizer (V : Set G) :=
    hi (ι z) hzTmem hzcomm hzne hmem
  have hφnorm : φ k ∈ Subgroup.normalizer (barSub (kGenIn V H) φ V : Set X) :=
    (mem_normalizer_iff_bar s k).mp hknorm
  rw [ht, w85g_normalizer_zpowers_eq_centralizer X t hS.mul_self] at hφnorm
  exact hrC hφnorm

theorem exists_symSetting_noncentral (h711 : ∀ H : Subgroup G, W3Lem711Alt ↥H)
    (hV : Hyp7 V) (hH : IsCalH V H) (hH0 : ¬ IsCalH0 V H)
    (hT : IsSylowIn 2 T (H ⊓ Subgroup.normalizer (V : Set G))) (hKT : H = kGenIn V H ⊔ T)
    {m : ℕ} (hm : 3 < m) (h3 : KBarOddQuotShape V H T (fun X _ => IsSymGp X m))
    (hn : ¬ KBarCenterShape V H T (fun X _ => IsSymGp X m)) :
    ∃ (Y : Type) (_ : Group Y) (_ : Finite Y) (φ' : ↥(kGenIn V H) →* Y)
      (e : Y ⧸ fusionOddCore Y ≃* Perm (Fin m)) (t : Y) (P : Sylow 2 Y),
      TailSetup V H T φ' ∧ SymSetting e t P ∧ barSub (kGenIn V H) φ' V = Subgroup.zpowers t ∧
        (P : Subgroup Y) = barSub (kGenIn V H) φ' T ∧ ¬ fusionOddCore Y ≤ Subgroup.center Y := by
  obtain ⟨X, _, _, φ, d, -⟩ := exists_shapeData h711 hV hH hH0 hT hKT
  have hSym : IsSymGp (X ⧸ fusionOddCore X) m := isSymGp_of_kBarOddQuotShape d h3
  have hS2 : Nat.card (barSub (kGenIn V H) φ V) = 2 :=
    card_barSub_eq_two_of_symGp h711 d hm hSym
  have hm6 : 6 ≤ m := by
    by_contra hlt
    have h45 : m = 4 ∨ m = 5 := by omega
    rcases h45 with h4 | h5
    · exact false_of_symGp_four_five d.situation hS2 (d.central hS2) hSym (Or.inl h4)
    · exact false_of_symGp_four_five d.situation hS2 (d.central hS2) hSym (Or.inr h5)
  obtain ⟨Y, _, _, φ', e, t, P, hs, hS, ht, hP⟩ := exists_symSetting d hS2 hm6 hSym
  refine ⟨Y, _, _, φ', e, t, P, hs, hS, ht, hP, ?_⟩
  intro hOZ
  have hgen : Subgroup.closure {y : Y | y * y = 1} = ⊤ := by
    rw [eq_top_iff, ← hS.oddClass.2.2]
    exact Subgroup.closure_mono (fun d hd => hS.oddClass.2.1.mul_self_eq_one hd)
  have hker : (symPi e).ker = fusionOddCore Y := by
    ext k
    rw [MonoidHom.mem_ker, symPi, MonoidHom.comp_apply]
    exact (MulEquiv.map_eq_one_iff e).trans (QuotientGroup.eq_one_iff k)
  have hker_le : (symPi e).ker ≤ Subgroup.center Y := by
    rw [hker]; exact hOZ
  have hodd : Odd (Nat.card (symPi e).ker) := by
    rw [hker]; exact w85g_odd_card_fusionOddCore
  have hsurj : Function.Surjective (symPi e) :=
    e.surjective.comp (QuotientGroup.mk'_surjective (fusionOddCore Y))
  have hO_bot : fusionOddCore Y = ⊥ := by
    have := w85g_ker_eq_bot_of_perm (symPi e) hker_le hodd hsurj hgen (by omega : 0 < m)
    rwa [hker] at this
  have hYsym : IsSymGp Y m :=
    ⟨(QuotientGroup.quotientBot (G := Y)).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hO_bot).symm.trans e)⟩
  have hZperm : Subgroup.center (Perm (Fin m)) = ⊥ := w85g_center_perm_eq_bot (by omega)
  have hZ : Subgroup.center Y = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    rw [Subgroup.mem_bot]
    obtain ⟨eY⟩ := hYsym
    have hzc : eY z ∈ Subgroup.center (Perm (Fin m)) := by
      rw [Subgroup.mem_center_iff]
      intro w
      obtain ⟨y, rfl⟩ := eY.surjective w
      rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.mp hz y).symm]
    rw [hZperm, Subgroup.mem_bot] at hzc
    exact eY.injective (by simpa using hzc)
  have hcent : IsSymGp (Y ⧸ Subgroup.center Y) m :=
    ⟨(QuotientGroup.quotientMulEquivOfEq hZ).trans
      ((QuotientGroup.quotientBot (G := Y)).trans hYsym.some)⟩
  exact hn (show KBarCenterShape V H T (fun X _ => IsSymGp X m) from
    hasQuotShape_centerPre_of_isBarMap hs.bar hcent)

theorem noncentralO_not_centralizersInM (h711 : ∀ H : Subgroup G, W3Lem711Alt ↥H)
    (hV : Hyp7 V) (hH : IsCalH V H) (hH0 : ¬ IsCalH0 V H)
    (hT : IsSylowIn 2 T (H ⊓ Subgroup.normalizer (V : Set G))) (hKT : H = kGenIn V H ⊔ T)
    {m : ℕ} (hm : 3 < m) (h3 : KBarOddQuotShape V H T (fun X _ => IsSymGp X m))
    (hn : ¬ KBarCenterShape V H T (fun X _ => IsSymGp X m)) : ¬ CentralizersInM V H T := by
  intro hi
  obtain ⟨Y, _, _, φ', e, t, P, s, hS, ht, hP, hnc⟩ :=
    exists_symSetting_noncentral h711 hV hH hH0 hT hKT hm h3 hn
  obtain ⟨E, _, _, α, ι, hM, hti⟩ := exists_moduleData s ht
  exact false_of_noncentral_O α hM.faithful hM.exp_two hS hnc hti
    (centralizer_E_R_eq_bot hi s hS ht hP hnc hM)

theorem noncentralO_not_normalizersInMTwo (hF : W3Lem85ThreeFirst' G) (hV : Hyp7 V)
    (hH : IsCalH V H) (hH0 : ¬ IsCalH0 V H)
    (hT : IsSylowIn 2 T (H ⊓ Subgroup.normalizer (V : Set G))) (hKT : H = kGenIn V H ⊔ T)
    {m : ℕ} (hm : 3 < m) (h3 : KBarOddQuotShape V H T (fun X _ => IsSymGp X m)) :
    ¬ NormalizersInMTwo V H (E3.wClos V 0 T) := by
  intro hii
  have h83 : Hyp83 V H T := Hyp83.of_hyp7 hV hH hH0 hT
  have hVp : IsPGroup 2 V := B2F.isPGroup_of_isElemAbelian h83.elemAbelian
  have hVne : V ≠ ⊥ := h83.ne_bot
  have hrk : 0 < rk ↥V := Nat.pos_of_ne_zero fun h0 =>
    hVne ((rk_eq_zero_iff_of_isPGroup hVp).mp h0)
  have hWne : E3.wClos V 0 T ≠ ⊥ := E3.wClos_ne_bot h83.elemAbelian h83.le_T hrk
  have hWT : E3.wClos V 0 T ≤ T := E3.wClos_le 0 T
  have hW2 : IsPGroup 2 (E3.wClos V 0 T) := hT.isPGroup.to_le hWT
  have hWN : E3.wClos V 0 T ≤
      Subgroup.normalizer (V : Set G) ⊓ Subgroup.normalizer (E3.wClos V 0 T : Set G) :=
    le_inf (hWT.trans h83.T_le_normalizer) le_normalizer
  have hstep : H ⊓ Subgroup.normalizer (E3.wClos V 0 T : Set G) ≤
      Subgroup.normalizer (V : Set G) :=
    hii (E3.wClos V 0 T) hWne hW2 hWN inf_le_right
  have hthree := hF V H T hV hH hH0 hT hKT (Or.inr (Or.inr ⟨m, hm, h3⟩))
  have hHN : H ≤ Subgroup.normalizer (V : Set G) := by
    rw [hthree]
    exact sup_le inf_le_right hstep
  have hVcore : V ≤ pCoreOf 2 H :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hH.1 hHN hVp
  exact hH0 ⟨hH, hVcore⟩

theorem w3Shape86C_holds (h711 : ∀ H : Subgroup G, W3Lem711Alt ↥H) (hB : W3Borel86' G)
    (hS : W3Shape86C' G) (hF : W3Lem85ThreeFirst' G) : W3Shape86C G := by
  intro V H T hV hH hH0 hT hKT hW hcase
  rcases hS V H T hV hH hH0 hT hKT with h1 | h2 | h3
  · rcases h1 with h1 | h1 | ⟨m, hm, hOdd⟩
    · exact Or.inl (Or.inl h1)
    · exact Or.inl (Or.inr (Or.inl h1))
    · by_cases hSym : KBarCenterShape V H T (fun X _ => IsSymGp X m)
      · exact Or.inl (Or.inr (Or.inr ⟨m, hm, hSym⟩))
      · exfalso
        rcases hcase with hi | hii
        · exact noncentralO_not_centralizersInM h711 hV hH hH0 hT hKT hm hOdd hSym hi
        · exact noncentralO_not_normalizersInMTwo hF hV hH hH0 hT hKT hm hOdd hii
  · exact (hB V H T hV hH hH0 hT hKT hW hcase h2).elim
  · exact Or.inr (Or.inr h3)

end CFSG.LocalAnalysis.WeakClosure81

end
