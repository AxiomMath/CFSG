module

public import CFSG.RankThree.PartTwo.Sec19.SimsSolEvenPi
import CFSG.CGT.PushingUpLit.SolK.PermBlock
public import CFSG.CGT.PushingUpLit.BHS.SymNatMaxSwap

public section

namespace CFSG.RankThree.PartTwo.Sec19.SolEven.RSmall

open Equiv Equiv.Perm
open CFSG.CGT.PushingUpLit.BHS (altOn conj_cyc cyc cyc_apply_first cyc_apply_of_ne
  cyc_apply_second cyc_apply_third cyc_inv cyc_isThreeCycle exists_eq_cyc exists_ne_ne
  exists_notMem_finset setStab)
open CFSG.CGT.PushingUpLit.SolK (apply_eq_of_pow_odd block_fixes exists_pow_two_pow_eq_one)

local instance instPermBarAddCommGroup (n : ℕ) : AddCommGroup (permBar n) :=
  { (inferInstance : AddGroup (permBar n)) with
    add_comm := fun x y => by
      obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective x
      obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective y
      rw [← QuotientAddGroup.mk_add, ← QuotientAddGroup.mk_add, add_comm] }

variable {n : ℕ}

abbrev barPt (a : Fin n) : permBar n := ((Pi.single a (1 : ZMod 2) : Fin n → ZMod 2) : permBar n)

theorem barAct_barPt (σ : Perm (Fin n)) (a : Fin n) : barAct σ (barPt a) = barPt (σ a) :=
  barAct_single σ a

@[expose] def PresPair (σ : Perm (Fin n)) (i j : Fin n) : Prop :=
  (σ i = i ∧ σ j = j) ∨ (σ i = j ∧ σ j = i)

private theorem vecPerm_cyc_eq {i j k : Fin n} {z : Fin n → ZMod 2} (hij : z i = z j)
    (hjk : z j = z k) : vecPerm (cyc i j k) z = z := by
  funext m
  rw [vecPerm_apply, cyc_inv]
  simp only [cyc, Perm.mul_apply, swap_apply_def]
  split_ifs <;> simp_all

private theorem zmod2_atoms : ∀ a b c d e f : ZMod 2,
    ((c, d) = (e, f) ∨ (a, b) = (c, d) ∨ (a, b) = (e, f)) →
    (a = c ∧ c = e) ∨ (b = d ∧ d = f) ∨ (a + b = c + d ∧ c + d = e + f) := by decide

private theorem isThreeCycle_mem_of_atoms {α : Type*} [Fintype α] (hα : Fintype.card α ≤ 4)
    (f : Fin n → α) (hn : 5 ≤ n) {H : Subgroup (Perm (Fin n))}
    (hH : ∀ i j k : Fin n, i ≠ j → i ≠ k → j ≠ k → (f j = f k ∨ f i = f j ∨ f i = f k) →
      cyc i j k ∈ H) {σ : Perm (Fin n)} (hσ : σ.IsThreeCycle) : σ ∈ H := by
  classical
  obtain ⟨p, q, r, hpq, hpr, hqr, rfl⟩ := exists_eq_cyc (by omega) hσ
  have hrot : ∀ i j k : Fin n, i ≠ j → i ≠ k → j ≠ k → cyc i j k = cyc j k i := by
    intro i j k hij hik hjk
    ext x
    simp only [cyc, Perm.mul_apply, swap_apply_def]
    split_ifs <;> simp_all
  have hsplit : ∀ p q r d : Fin n, cyc p q d * cyc p d r = cyc p q r := fun p q r d => by
    simp only [cyc, mul_assoc, swap_mul_self_mul]
  have hmate : ∀ p q r : Fin n, p ≠ q → p ≠ r → q ≠ r → ∀ d, d ≠ p → d ≠ q → d ≠ r →
      f d = f p → cyc p q r ∈ H := by
    intro p q r hpq hpr hqr d hdp hdq hdr hfd
    rw [← hsplit p q r d]
    exact H.mul_mem (hH p q d hpq (Ne.symm hdp) (Ne.symm hdq) (Or.inr (Or.inr hfd.symm)))
      (hH p d r (Ne.symm hdp) hpr hdr (Or.inr (Or.inl hfd.symm)))
  have hmate' : ∀ d, d ≠ p → d ≠ q → d ≠ r → ∀ u, (u = p ∨ u = q ∨ u = r) → f d = f u →
      cyc p q r ∈ H := by
    intro d hdp hdq hdr u hu hfd
    rcases hu with rfl | rfl | rfl
    · exact hmate u q r hpq hpr hqr d hdp hdq hdr hfd
    · rw [hrot p u r hpq hpr hqr]
      exact hmate u r p hqr (Ne.symm hpq) (Ne.symm hpr) d hdq hdr hdp hfd
    · rw [hrot p q u hpq hpr hqr, hrot q u p hqr (Ne.symm hpq) (Ne.symm hpr)]
      exact hmate u p q (Ne.symm hpr) (Ne.symm hqr) hpq d hdr hdp hdq hfd
  have hpair : ∀ d e, d ≠ p → d ≠ q → d ≠ r → e ≠ p → e ≠ q → e ≠ r → d ≠ e → f d = f e →
      cyc p q r ∈ H := by
    intro d e hdp hdq hdr hep heq her hde hfde
    have key : ∀ s, s ≠ p → s ≠ d → s ≠ e → cyc p d s ∈ H := by
      intro s hsp hsd hse
      have hc : cyc s d e ∈ H := hH s d e hsd hse hde (Or.inl hfde)
      have h2 : cyc p e d ∈ H :=
        hH p e d (Ne.symm hep) (Ne.symm hdp) (Ne.symm hde) (Or.inl hfde.symm)
      have h3 := H.mul_mem (H.mul_mem hc h2) (H.inv_mem hc)
      rwa [conj_cyc, cyc_apply_of_ne (Ne.symm hsp) (Ne.symm hdp) (Ne.symm hep),
        cyc_apply_third, cyc_apply_second hsd hde] at h3
    rw [← hsplit p q r d, ← cyc_inv p d q]
    exact H.mul_mem (H.inv_mem (key q (Ne.symm hpq) (Ne.symm hdq) (Ne.symm heq)))
      (key r (Ne.symm hpr) (Ne.symm hdr) (Ne.symm her))
  have hlt : Fintype.card α < (Finset.univ : Finset (Fin n)).card := by
    rw [Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨u, -, v, -, huv, hfuv⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to
    (s := (Finset.univ : Finset (Fin n))) (t := (Finset.univ : Finset α)) (by simpa using hlt)
    (f := f) fun _ _ => Finset.mem_univ _
  by_cases hu : u = p ∨ u = q ∨ u = r
  · by_cases hv : v = p ∨ v = q ∨ v = r
    ·
      refine hH p q r hpq hpr hqr ?_
      rcases hu with hu | hu | hu <;> rcases hv with hv | hv | hv <;> subst hu hv <;>
        first
        | exact absurd rfl huv
        | exact Or.inl hfuv
        | exact Or.inl hfuv.symm
        | exact Or.inr (Or.inl hfuv)
        | exact Or.inr (Or.inl hfuv.symm)
        | exact Or.inr (Or.inr hfuv)
        | exact Or.inr (Or.inr hfuv.symm)
    · simp only [not_or] at hv
      exact hmate' v hv.1 hv.2.1 hv.2.2 u hu hfuv.symm
  · simp only [not_or] at hu
    by_cases hv : v = p ∨ v = q ∨ v = r
    · exact hmate' u hu.1 hu.2.1 hu.2.2 v hv hfuv
    · simp only [not_or] at hv
      exact hpair u v hu.1 hu.2.1 hu.2.2 hv.1 hv.2.1 hv.2.2 huv hfuv

theorem isThreeCycle_mem_closure_of_fixes (hn : 5 ≤ n) (v w : permBar n) {σ : Perm (Fin n)}
    (hσ : σ.IsThreeCycle) :
    σ ∈ Subgroup.closure {τ : Perm (Fin n) | τ.IsThreeCycle ∧
      (barAct τ v = v ∨ barAct τ w = w ∨ barAct τ (v + w) = v + w)} := by
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective v
  obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective w
  refine isThreeCycle_mem_of_atoms (α := ZMod 2 × ZMod 2) (by simp) (fun i => (x i, y i)) hn ?_ hσ
  intro i j k hij hik hjk hat
  refine Subgroup.subset_closure ⟨cyc_isThreeCycle hij hik hjk, ?_⟩
  rcases zmod2_atoms _ _ _ _ _ _ hat with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl (by rw [barAct_mk, vecPerm_cyc_eq h1 h2])
  · exact Or.inr (Or.inl (by rw [barAct_mk, vecPerm_cyc_eq h1 h2]))
  · refine Or.inr (Or.inr ?_)
    rw [← QuotientAddGroup.mk_add, barAct_mk, vecPerm_cyc_eq (z := x + y) h1 h2]

theorem eq_of_threeCycle_fixes_mod (hn : 6 ≤ n) {a b : Fin n} (hab : a ≠ b) {v : permBar n}
    (h : ∀ σ : Perm (Fin n), σ.IsThreeCycle → σ a = a → σ b = b →
      barAct σ v = v ∨ barAct σ v = v + (barPt a + barPt b)) :
    v = 0 ∨ v = barPt a ∨ v = barPt b ∨ v = barPt a + barPt b := by
  classical
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective v
  have hinv : ∀ σ : Perm (Fin n), σ.IsThreeCycle → σ a = a → σ b = b → vecPerm σ x = x := by
    intro σ hσ ha hb
    obtain ⟨i₀, hi₀⟩ := exists_notMem_finset (s := σ.support ∪ {a, b}) (by
      have h1 := Finset.card_union_le σ.support {a, b}
      have h2 := hσ.card_support
      have h3 : ({a, b} : Finset (Fin n)).card ≤ 2 := Finset.card_le_two
      omega)
    simp only [Finset.mem_union, mem_support, not_or, not_not, Finset.mem_insert,
      Finset.mem_singleton] at hi₀
    obtain ⟨hi₀σ, hi₀a, hi₀b⟩ := hi₀
    have ha' : σ⁻¹ a = a := by rw [inv_eq_iff_eq, ha]
    have hi₀' : σ⁻¹ i₀ = i₀ := by rw [inv_eq_iff_eq, hi₀σ]
    rcases h σ hσ ha hb with h1 | h2
    · rw [barAct_mk, QuotientAddGroup.eq] at h1
      rcases (mem_zmultiples_allOnes_iff _).1 h1 with h0 | h0
      · exact neg_add_eq_zero.1 h0
      · exfalso
        have := congrFun h0 a
        simp [vecPerm_apply, ha', allOnes, CharTwo.add_self_eq_zero] at this
    · rw [barAct_mk] at h2
      simp only [← QuotientAddGroup.mk_add] at h2
      rw [QuotientAddGroup.eq] at h2
      rcases (mem_zmultiples_allOnes_iff _).1 h2 with h0 | h0
      · exfalso
        have := congrFun h0 a
        simp [vecPerm_apply, ha', Pi.single_apply, hab, ← add_assoc,
          CharTwo.add_self_eq_zero] at this
      · exfalso
        have := congrFun h0 i₀
        simp [vecPerm_apply, hi₀', Pi.single_apply, hi₀a, hi₀b, allOnes, ← add_assoc,
          CharTwo.add_self_eq_zero] at this
  have hconst : ∀ i j, i ≠ a → i ≠ b → j ≠ a → j ≠ b → x i = x j := by
    intro i j hia hib hja hjb
    by_cases hij : i = j
    · rw [hij]
    obtain ⟨k, hk⟩ := exists_notMem_finset (s := {a, b, i, j}) (by
      have : ({a, b, i, j} : Finset (Fin n)).card ≤ 4 := Finset.card_le_four
      omega)
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
    obtain ⟨hka, hkb, hki, hkj⟩ := hk
    have h3 := cyc_isThreeCycle (i := j) (j := k) (k := i) (Ne.symm hkj) (Ne.symm hij) hki
    have hcj : cyc j k i j = i := cyc_apply_first (Ne.symm hij) hki
    have e : (cyc j k i)⁻¹ i = j := by rw [inv_eq_iff_eq, hcj]
    have := congrFun (hinv _ h3 (cyc_apply_of_ne (Ne.symm hja) (Ne.symm hka) (Ne.symm hia))
      (cyc_apply_of_ne (Ne.symm hjb) (Ne.symm hkb) (Ne.symm hib))) i
    rw [vecPerm_apply, e] at this
    exact this.symm
  obtain ⟨i₁, hi₁a, hi₁b⟩ := exists_ne_ne (by omega) a b
  obtain ⟨y, hy, hy0⟩ : ∃ y : Fin n → ZMod 2,
      (y : permBar n) = x ∧ ∀ i, i ≠ a → i ≠ b → y i = 0 := by
    refine ⟨x + fun _ => x i₁, ?_, fun i hia hib => ?_⟩
    · have hc : (((fun _ => x i₁ : Fin n → ZMod 2)) : permBar n) = 0 := by
        rw [QuotientAddGroup.eq_zero_iff, mem_zmultiples_allOnes_iff]
        rcases zmod_two_cases' (x i₁) with h0 | h0
        · exact Or.inl (funext fun _ => h0)
        · exact Or.inr (funext fun _ => h0)
      rw [QuotientAddGroup.mk_add, hc, add_zero]
    · simp [hconst i i₁ hia hib hi₁a hi₁b, CharTwo.add_self_eq_zero]
  have hyeq : y = Pi.single a (y a) + Pi.single b (y b) := by
    funext i
    by_cases hia : i = a
    · subst hia
      simp [Pi.single_apply, hab]
    by_cases hib : i = b
    · subst hib
      simp [Pi.single_apply, hia]
    simp [Pi.single_apply, hia, hib, hy0 i hia hib]
  rw [← hy, hyeq, QuotientAddGroup.mk_add]
  rcases zmod_two_cases' (y a) with ha | ha <;> rcases zmod_two_cases' (y b) with hb | hb <;>
    simp [ha, hb]

theorem eq_one_or_eq_of_presPair (hn : 8 ≤ n) {P : Subgroup (Perm (Fin n))} {σ : Perm (Fin n)}
    (hσP : σ ∈ P) (hσ2 : σ * σ = 1)
    (h : ∀ τ ∈ P, τ ≠ 1 → ∀ i j : Fin n, i ≠ j → (PresPair τ i j ↔ PresPair σ i j)) :
    ∀ τ ∈ P, τ = 1 ∨ τ = σ := by
  classical
  intro τ hτ
  by_cases hτ1 : τ = 1
  · exact Or.inl hτ1
  right
  have hσσ : ∀ i, σ (σ i) = i := fun i => by
    simpa using congrArg (fun g : Perm (Fin n) => g i) hσ2
  have hpσ : ∀ i, σ i ≠ i → PresPair σ i (σ i) := fun i _ => Or.inr ⟨rfl, hσσ i⟩
  have hpν : ∀ ν ∈ P, ν ≠ 1 → ∀ i, σ i ≠ i → PresPair ν i (σ i) :=
    fun ν hν hν1 i hi => (h ν hν hν1 i (σ i) (Ne.symm hi)).2 (hpσ i hi)
  by_cases hM : 5 ≤ (Finset.univ.filter fun i => σ i ≠ i).card
  ·
    by_cases hρ : σ * τ = 1
    · exact mul_left_cancel (hρ.trans hσ2.symm)
    exfalso
    have hT : ∀ ν ∈ P, ν ≠ 1 →
        (Finset.univ.filter fun i => σ i ≠ i ∧ ν i = i).card ≤ 2 := by
      intro ν hν hν1
      rcases (Finset.univ.filter fun i => σ i ≠ i ∧ ν i = i).eq_empty_or_nonempty with
        he | ⟨i₀, hi₀⟩
      · rw [he]
        simp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi₀
      refine (Finset.card_le_card (t := {i₀, σ i₀}) fun i hi => ?_).trans Finset.card_le_two
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      simp only [Finset.mem_insert, Finset.mem_singleton]
      by_cases hii₀ : i = i₀
      · exact Or.inl hii₀
      right
      rcases (h ν hν hν1 i i₀ hii₀).1 (Or.inl ⟨hi.2, hi₀.2⟩) with ⟨h1, _⟩ | ⟨_, h2⟩
      · exact absurd h1 hi.1
      · exact h2.symm
    have hcover : (Finset.univ.filter fun i => σ i ≠ i) ⊆
        (Finset.univ.filter fun i => σ i ≠ i ∧ τ i = i) ∪
          (Finset.univ.filter fun i => σ i ≠ i ∧ (σ * τ) i = i) := by
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union] at hi ⊢
      rcases hpν τ hτ hτ1 i hi with ⟨h1, _⟩ | ⟨h1, _⟩
      · exact Or.inl ⟨hi, h1⟩
      · exact Or.inr ⟨hi, by rw [Perm.mul_apply, h1, hσσ]⟩
    have h1 := hT τ hτ hτ1
    have h2 := hT (σ * τ) (P.mul_mem hσP hτ) hρ
    have h3 := (Finset.card_le_card hcover).trans (Finset.card_union_le _ _)
    omega
  ·
    have hF : 4 ≤ (Finset.univ.filter fun i => σ i = i).card := by
      have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
        (fun i => σ i = i)
      simp only [Finset.card_univ, Fintype.card_fin] at this
      simp only [ne_eq] at hM
      omega
    have hfixed : ∀ f, σ f = f → τ f = f := by
      intro f hf
      have hcard : 1 < ((Finset.univ.filter fun i => σ i = i).erase f).card := by
        rw [Finset.card_erase_of_mem (by simp [hf])]
        omega
      obtain ⟨f', hf', f'', hf'', hne⟩ := Finset.one_lt_card.1 hcard
      simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and] at hf' hf''
      have p1 : PresPair τ f f' := (h τ hτ hτ1 f f' hf'.1.symm).2 (Or.inl ⟨hf, hf'.2⟩)
      have p2 : PresPair τ f f'' := (h τ hτ hτ1 f f'' hf''.1.symm).2 (Or.inl ⟨hf, hf''.2⟩)
      by_contra hτf
      rcases p1 with ⟨h1, _⟩ | ⟨h1, _⟩ <;> rcases p2 with ⟨h2, _⟩ | ⟨h2, _⟩
      · exact hτf h1
      · exact hτf h1
      · exact hτf h2
      · exact hne (h1.symm.trans h2)
    obtain ⟨f₀, hf₀⟩ := Finset.card_pos.1
      (by omega : 0 < (Finset.univ.filter fun i => σ i = i).card)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf₀
    refine Equiv.ext fun k => ?_
    by_cases hk : σ k = k
    · rw [hk]
      exact hfixed k hk
    rcases hpν τ hτ hτ1 k hk with ⟨h1, _⟩ | ⟨h1, _⟩
    · exfalso
      have hkf : k ≠ f₀ := fun e => hk (e ▸ hf₀)
      rcases (h τ hτ hτ1 k f₀ hkf).1 (Or.inl ⟨h1, hfixed f₀ hf₀⟩) with ⟨h2, _⟩ | ⟨_, h3⟩
      · exact hk h2
      · exact hkf (h3.symm.trans hf₀)
    · exact h1

theorem eq_one_or_swap_of_normalized (hn : 7 ≤ n) {a b : Fin n} (hab : a ≠ b)
    {N : Subgroup (Perm (Fin n))} (hN2 : IsPGroup 2 N) (hNab : ∀ τ ∈ N, PresPair τ a b)
    (hnorm : ∀ c : Perm (Fin n), c.IsThreeCycle → c a = a → c b = b →
      ∀ τ ∈ N, c * τ * c⁻¹ ∈ N) :
    ∀ τ ∈ N, τ = 1 ∨ τ = swap a b := by
  classical
  let B : Finset (Fin n) := (Finset.univ.erase a).erase b
  have hmem : ∀ x, x ∈ B ↔ x ≠ a ∧ x ≠ b := fun x => by simp [B, and_comm]
  have hcard : B.card = n - 2 := by
    simp only [B]
    rw [Finset.card_erase_of_mem (by simp [hab.symm]), Finset.card_erase_of_mem (Finset.mem_univ a),
      Finset.card_univ, Fintype.card_fin]
    omega
  have hNB : N ≤ setStab B := by
    intro τ hτ x
    rw [hmem, hmem]
    have inj : ∀ y z, τ y = τ z → y = z := fun y z h => τ.injective h
    rcases hNab τ hτ with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · grind
    · grind
  have hAlt : altOn B ≤ Subgroup.normalizer (N : Set (Perm (Fin n))) := by
    rw [altOn, ← closure_three_cycles_eq_alternating, MonoidHom.map_closure,
      Subgroup.closure_le]
    rintro _ ⟨c, hc, rfl⟩
    have h3 : (ofSubtype c).IsThreeCycle := by
      rw [IsThreeCycle, cycleType_ofSubtype]
      exact hc
    have ha : ofSubtype c a = a := ofSubtype_apply_of_not_mem c (by simp [hmem])
    have hb : ofSubtype c b = b := ofSubtype_apply_of_not_mem c (by simp [hmem])
    have ha' : (ofSubtype c)⁻¹ a = a := by rw [inv_eq_iff_eq, ha]
    have hb' : (ofSubtype c)⁻¹ b = b := by rw [inv_eq_iff_eq, hb]
    refine Subgroup.mem_normalizer_iff.2 fun g => ⟨hnorm _ h3 ha hb g, fun hg => ?_⟩
    simpa [mul_assoc] using hnorm _ h3.inv ha' hb' _ hg
  have hfix := block_fixes hN2 hNB
    (fun τ hτ σ hσ => (Subgroup.mem_normalizer_iff.1 (hAlt hτ) σ).1 hσ)
    (Or.inr (Or.inr (by omega)))
  intro τ hτ
  rcases hNab τ hτ with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · left
    refine Equiv.ext fun x => ?_
    by_cases hxa : x = a
    · rw [hxa, h1, Perm.one_apply]
    by_cases hxb : x = b
    · rw [hxb, h2, Perm.one_apply]
    rw [Perm.one_apply]
    exact hfix τ hτ x ((hmem x).2 ⟨hxa, hxb⟩)
  · right
    refine Equiv.ext fun x => ?_
    by_cases hxa : x = a
    · rw [hxa, h1, swap_apply_left]
    by_cases hxb : x = b
    · rw [hxb, h2, swap_apply_right]
    rw [swap_apply_of_ne_of_ne hxa hxb]
    exact hfix τ hτ x ((hmem x).2 ⟨hxa, hxb⟩)

theorem mem_swap_of_threeCycle_fixed (hn : 6 ≤ n) {a b : Fin n} (hab : a ≠ b)
    {N : Subgroup (Perm (Fin n))} (hN2 : IsPGroup 2 N) (hNab : ∀ τ ∈ N, PresPair τ a b)
    (hnorm : ∀ c : Perm (Fin n), c.IsThreeCycle → c a = a → c b = b →
      ∀ τ ∈ N, c * τ * c⁻¹ ∈ N)
    {ψ : Perm (Fin n)} (hψ : orderOf ψ = 3) (hψa : ψ a = a) (hψb : ψ b = b)
    {φ : Perm (Fin n)} (hφ : φ ∈ N)
    (hfix : ψ * φ * ψ⁻¹ = φ ∨ ψ * φ * ψ⁻¹ = φ * swap a b) :
    φ = 1 ∨ φ = swap a b := by
  classical
  rcases Nat.lt_or_ge 6 n with h7 | h6
  · exact eq_one_or_swap_of_normalized (by omega) hab hN2 hNab hnorm φ hφ
  obtain rfl : n = 6 := le_antisymm h6 hn
  have hφ2 := exists_pow_two_pow_eq_one hN2 hφ
  have hφab := hNab φ hφ
  have hφoff : ∀ p, p ≠ a → p ≠ b → φ p ≠ a ∧ φ p ≠ b := by
    intro p hpa hpb
    rcases hφab with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨fun h => hpa (φ.injective (h.trans h1.symm)),
        fun h => hpb (φ.injective (h.trans h2.symm))⟩
    · exact ⟨fun h => hpb (φ.injective (h.trans h2.symm)),
        fun h => hpa (φ.injective (h.trans h1.symm))⟩
  have hcomm : ∀ p, p ≠ a → p ≠ b → ψ (φ p) = φ (ψ p) := by
    intro p hpa hpb
    have hψpa : ψ p ≠ a := fun h => hpa (ψ.injective (h.trans hψa.symm))
    have hψpb : ψ p ≠ b := fun h => hpb (ψ.injective (h.trans hψb.symm))
    have h1 : (ψ * φ * ψ⁻¹) (ψ p) = φ (ψ p) := by
      rcases hfix with h | h
      · rw [h]
      · rw [h, Perm.mul_apply, swap_apply_of_ne_of_ne hψpa hψpb]
    simpa [Perm.mul_apply] using h1
  have hsupp : ψ.support ⊆ (Finset.univ.erase a).erase b := by
    intro p hp
    rw [mem_support] at hp
    simp only [Finset.mem_erase, Finset.mem_univ, and_true]
    exact ⟨fun h => hp (h ▸ hψb), fun h => hp (h ▸ hψa)⟩
  have hψ3 : ψ.IsThreeCycle := by
    rw [← card_support_eq_three_iff]
    obtain ⟨k, hk⟩ := cycleType_prime_order (hψ ▸ Nat.prime_three)
    have hsum := sum_cycleType ψ
    rw [hk, hψ, Multiset.sum_replicate, smul_eq_mul] at hsum
    have hle := Finset.card_le_card hsupp
    rw [Finset.card_erase_of_mem (by simp [hab.symm]), Finset.card_erase_of_mem (Finset.mem_univ a),
      Finset.card_univ, Fintype.card_fin] at hle
    omega
  obtain ⟨x, y, z, hxy, hxz, hyz, hψeq⟩ := exists_eq_cyc (by omega) hψ3
  have hψx : ψ x = z := by rw [hψeq]; exact cyc_apply_first hxz hyz
  have hψy : ψ y = x := by rw [hψeq]; exact cyc_apply_second hxy hyz
  have hψz : ψ z = y := by rw [hψeq]; exact cyc_apply_third x y z
  have hxa : x ≠ a := fun h => hxz (by rw [← hψx, h, hψa])
  have hxb : x ≠ b := fun h => hxz (by rw [← hψx, h, hψb])
  have hya : y ≠ a := fun h => hxy (by rw [← hψy, h, hψa])
  have hyb : y ≠ b := fun h => hxy (by rw [← hψy, h, hψb])
  have hza : z ≠ a := fun h => hyz (by rw [← hψz, h, hψa])
  have hzb : z ≠ b := fun h => hyz (by rw [← hψz, h, hψb])
  have hmoved : ∀ q, ψ q ≠ q → q = x ∨ q = y ∨ q = z := by
    intro q hq
    by_contra h
    simp only [not_or] at h
    exact hq (by rw [hψeq]; exact cyc_apply_of_ne h.1 h.2.1 h.2.2)
  have h3 : ∀ q, (φ ^ 3) q = φ (φ (φ q)) := fun q => by
    simp only [pow_succ, pow_zero, one_mul, Perm.mul_apply]
  have hφx : φ x = x := by
    have h1 : φ x = x ∨ φ x = y ∨ φ x = z := by
      apply hmoved
      rw [hcomm x hxa hxb, hψx]
      exact fun h => hxz (φ.injective h).symm
    rcases h1 with h | h | h
    · exact h
    · exfalso
      have hz' : φ z = x := by rw [← hψx, ← hcomm x hxa hxb, h, hψy]
      have hy' : φ y = z := by rw [← hψz, ← hcomm z hza hzb, hz', hψx]
      have h4 : (φ ^ 3) x = x := by rw [h3, h, hy', hz']
      exact hxy (h.symm.trans (apply_eq_of_pow_odd hφ2 (by decide) h4)).symm
    · exfalso
      have hz' : φ z = y := by rw [← hψx, ← hcomm x hxa hxb, h, hψz]
      have hy' : φ y = x := by rw [← hψz, ← hcomm z hza hzb, hz', hψy]
      have h4 : (φ ^ 3) x = x := by rw [h3, h, hz', hy']
      exact hxz (h.symm.trans (apply_eq_of_pow_odd hφ2 (by decide) h4)).symm
  have hφz : φ z = z := by rw [← hψx, ← hcomm x hxa hxb, hφx]
  have hφy : φ y = y := by rw [← hψz, ← hcomm z hza hzb, hφz]
  have hcard5 : ({a, b, x, y, z} : Finset (Fin 6)).card = 5 := by
    rw [Finset.card_insert_of_notMem (by simp [hab, hxa.symm, hya.symm, hza.symm]),
      Finset.card_insert_of_notMem (by simp [hxb.symm, hyb.symm, hzb.symm]),
      Finset.card_insert_of_notMem (by simp [hxy, hxz]), Finset.card_pair hyz]
  have hφB : ∀ p, p ≠ a → p ≠ b → φ p = p := by
    intro p hpa hpb
    by_cases hpx : p = x
    · rw [hpx, hφx]
    by_cases hpy : p = y
    · rw [hpy, hφy]
    by_cases hpz : p = z
    · rw [hpz, hφz]
    obtain ⟨hφpa, hφpb⟩ := hφoff p hpa hpb
    have hφpx : φ p ≠ x := fun h => hpx (φ.injective (h.trans hφx.symm))
    have hφpy : φ p ≠ y := fun h => hpy (φ.injective (h.trans hφy.symm))
    have hφpz : φ p ≠ z := fun h => hpz (φ.injective (h.trans hφz.symm))
    have hle : (Finset.univ \ {a, b, x, y, z} : Finset (Fin 6)).card ≤ 1 := by
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), hcard5, Finset.card_univ,
        Fintype.card_fin]
    exact Finset.card_le_one.1 hle (φ p) (by simp [hφpa, hφpb, hφpx, hφpy, hφpz]) p
      (by simp [hpa, hpb, hpx, hpy, hpz])
  rcases hφab with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · left
    refine Equiv.ext fun q => ?_
    by_cases hqa : q = a
    · rw [hqa, h1, Perm.one_apply]
    by_cases hqb : q = b
    · rw [hqb, h2, Perm.one_apply]
    rw [Perm.one_apply]
    exact hφB q hqa hqb
  · right
    refine Equiv.ext fun q => ?_
    by_cases hqa : q = a
    · rw [hqa, h1, swap_apply_left]
    by_cases hqb : q = b
    · rw [hqb, h2, swap_apply_right]
    rw [swap_apply_of_ne_of_ne hqa hqb]
    exact hφB q hqa hqb

theorem eq_of_isSwap_of_mem {P : Subgroup (Perm (Fin n))} (h : ∀ τ ∈ P, τ = 1 ∨ τ.IsSwap)
    {τ τ' : Perm (Fin n)} (hτ : τ ∈ P) (hτ' : τ' ∈ P) (h1 : τ ≠ 1) (h1' : τ' ≠ 1) : τ = τ' := by
  by_contra hne
  have hs : τ.IsSwap := (h τ hτ).resolve_left h1
  have hs' : τ'.IsSwap := (h τ' hτ').resolve_left h1'
  have hprod : (τ * τ').IsSwap := by
    refine (h _ (P.mul_mem hτ hτ')).resolve_left fun h0 => hne ?_
    obtain ⟨z, w, -, rfl⟩ := hs'
    rw [mul_eq_one_iff_eq_inv, swap_inv] at h0
    exact h0
  have hsign := hprod.sign_eq
  rw [map_mul, hs.sign_eq, hs'.sign_eq] at hsign
  exact absurd hsign (by decide)

end CFSG.RankThree.PartTwo.Sec19.SolEven.RSmall
