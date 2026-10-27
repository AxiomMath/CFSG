module

public import CFSG.LocalAnalysis.WeakClosure81.ThreeOneElems

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Equiv Equiv.Perm

namespace ThreeOne

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω] {σ : Perm Ω}

private lemma exists_notMem_of_card_lt {F : Finset Ω} (h : F.card < Fintype.card Ω) :
    ∃ x, x ∉ F := by
  obtain ⟨x, -, hx⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card (s := F) (t := Finset.univ) (by simpa using h)
  exact ⟨x, hx⟩

private lemma exists_notMem_of_card_le {F : Finset Ω} {n : ℕ} (hF : F.card ≤ n)
    (hn : n < Fintype.card Ω) : ∃ x, x ∉ F :=
  exists_notMem_of_card_lt (lt_of_le_of_lt hF hn)

private lemma card_eight_le (a b c d e f g h : Ω) :
    ({a, b, c, d, e, f, g, h} : Finset Ω).card ≤ 8 := by
  have h1 : ({a, b, c, d, e, f, g, h} : Finset Ω).card
      ≤ ({b, c, d, e, f, g, h} : Finset Ω).card + 1 := Finset.card_insert_le _ _
  have h2 : ({b, c, d, e, f, g, h} : Finset Ω).card
      ≤ ({c, d, e, f, g, h} : Finset Ω).card + 1 := Finset.card_insert_le _ _
  have h3 : ({c, d, e, f, g, h} : Finset Ω).card ≤ 6 := Finset.card_le_six
  omega

private lemma exists_apply_notMem_three (hσ : ∀ x, σ (σ x) = x) {α p1 p2 p3 : Ω}
    (hfix : ∀ x, x ≠ α → σ x ≠ x) (h1α : p1 ≠ α) (h2α : p2 ≠ α) (h3α : p3 ≠ α)
    (h12 : p1 ≠ p2) (h13 : p1 ≠ p3) (h23 : p2 ≠ p3) :
    ∃ p ∈ ({p1, p2, p3} : Finset Ω), σ p ∉ ({p1, p2, p3} : Finset Ω) := by
  by_contra h
  push Not at h
  have h1 : σ p1 = p1 ∨ σ p1 = p2 ∨ σ p1 = p3 := by
    simpa only [Finset.mem_insert, Finset.mem_singleton] using h p1 (by simp)
  have h2 : σ p2 = p1 ∨ σ p2 = p2 ∨ σ p2 = p3 := by
    simpa only [Finset.mem_insert, Finset.mem_singleton] using h p2 (by simp)
  have h3 : σ p3 = p1 ∨ σ p3 = p2 ∨ σ p3 = p3 := by
    simpa only [Finset.mem_insert, Finset.mem_singleton] using h p3 (by simp)
  rcases h1 with h1 | h1 | h1
  · exact (hfix p1 h1α) h1
  · have h2v : σ p2 = p1 := by rw [← h1, hσ p1]
    rcases h3 with h3 | h3 | h3
    · exact h23 (by rw [← hσ p3, h3, h1])
    · exact h13 (by rw [← hσ p3, h3, h2v])
    · exact (hfix p3 h3α) h3
  · have h3v : σ p3 = p1 := by rw [← h1, hσ p1]
    rcases h2 with h2 | h2 | h2
    · exact h23 (by rw [← hσ p2, h2, h1])
    · exact (hfix p2 h2α) h2
    · exact h12 (by rw [← hσ p2, h2, h3v])

theorem isThreeCycle_mul_conj {s t z w s' r r' : Ω} (hst : s ≠ t) (hsz : s ≠ z) (hsw : s ≠ w)
    (htz : t ≠ z) (htw : t ≠ w) (hzw : z ≠ w) (hs's : s' ≠ s) (hs't : s' ≠ t) (hs'z : s' ≠ z)
    (hs'w : s' ≠ w) (hrs : r ≠ s) (hrt : r ≠ t) (hrz : r ≠ z) (hrw : r ≠ w) (hr's : r' ≠ s)
    (hr't : r' ≠ t) (hr'z : r' ≠ z) (hr'w : r' ≠ w) :
    IsThreeCycle (swap s t * swap z w *
      ((swap s s' * swap r r') * (swap s t * swap z w) * (swap s s' * swap r r')⁻¹)) := by
  have hgs : (swap s s' * swap r r') s = s' := by
    rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hrs.symm hr's.symm,
      Equiv.swap_apply_left]
  have hgt : (swap s s' * swap r r') t = t := by
    rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hrt.symm hr't.symm,
      Equiv.swap_apply_of_ne_of_ne hst.symm hs't.symm]
  have hgz : (swap s s' * swap r r') z = z := by
    rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hrz.symm hr'z.symm,
      Equiv.swap_apply_of_ne_of_ne hsz.symm hs'z.symm]
  have hgw : (swap s s' * swap r r') w = w := by
    rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hrw.symm hr'w.symm,
      Equiv.swap_apply_of_ne_of_ne hsw.symm hs'w.symm]
  have hconj : (swap s s' * swap r r') * (swap s t * swap z w) * (swap s s' * swap r r')⁻¹
      = swap s' t * swap z w := by
    have hsplit : (swap s s' * swap r r') * (swap s t * swap z w)
        * (swap s s' * swap r r')⁻¹
        = ((swap s s' * swap r r') * swap s t * (swap s s' * swap r r')⁻¹)
          * ((swap s s' * swap r r') * swap z w * (swap s s' * swap r r')⁻¹) := by
      rw [← MulAut.conj_apply, map_mul]
      simp only [MulAut.conj_apply]
    rw [hsplit, ← swap_apply_apply (swap s s' * swap r r') s t,
      ← swap_apply_apply (swap s s' * swap r r') z w, hgs, hgt, hgz, hgw]
  have hnodup : [z, w, s', t].Nodup := by
    refine List.nodup_cons.2 ⟨?_, List.nodup_cons.2 ⟨?_,
      List.nodup_cons.2 ⟨?_, List.nodup_singleton _⟩⟩⟩
    · simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false, not_or]
      exact ⟨hzw, hs'z.symm, htz.symm⟩
    · simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false, not_or]
      exact ⟨hs'w.symm, htw.symm⟩
    · simp only [List.mem_singleton]
      exact hs't
  have hcomm : Commute (swap z w) (swap s' t) :=
    (Equiv.Perm.disjoint_swap_swap hnodup).commute
  have hcancel : swap z w * swap s' t * swap z w = swap s' t := by
    rw [hcomm.eq, mul_assoc, Equiv.swap_mul_self, mul_one]
  have hprod : swap s t * swap z w * (swap s' t * swap z w) = swap s t * swap s' t := by
    rw [mul_assoc (swap s t) (swap z w) (swap s' t * swap z w),
      ← mul_assoc (swap z w) (swap s' t) (swap z w), hcancel]
  rw [hconj, hprod, Equiv.swap_comm s t, Equiv.swap_comm s' t]
  exact isThreeCycle_swap_mul_swap_same hst.symm hs't.symm hs's.symm

theorem exists_isThreeCycle_mem_of_swap_mul_swap_mem (hσ : ∀ x, σ (σ x) = x)
    {H K : Subgroup (Perm Ω)} (hA : alternatingGroup Ω ≤ H)
    (hXK : H ⊓ Subgroup.centralizer {σ} ≤ K) {s t z w : Ω} (hst : s ≠ t) (hsz : s ≠ z)
    (hsw : s ≠ w) (htz : t ≠ z) (htw : t ≠ w) (hzw : z ≠ w) (hs : σ s ≠ s) (hs't : σ s ≠ t)
    (hs'z : σ s ≠ z) (hs'w : σ s ≠ w) (hu : swap s t * swap z w ∈ K) {r : Ω} (hr : σ r ≠ r)
    (hrs : r ∉ ({s, σ s, t, σ t, z, σ z, w, σ w} : Finset Ω)) :
    ∃ c ∈ K, c.IsThreeCycle := by
  have hg : swap s (σ s) * swap r (σ r) ∈ H ⊓ Subgroup.centralizer {σ} :=
    swap_mul_swap_apply_mem_inf hσ hA hs hr
  have hgK : swap s (σ s) * swap r (σ r) ∈ K := hXK hg
  have hr_not : ∀ x ∈ ({s, σ s, t, σ t, z, σ z, w, σ w} : Finset Ω), r ≠ x :=
    fun x hx h => hrs (h ▸ hx)
  have hrs' : r ≠ s := hr_not s (by simp)
  have hrt' : r ≠ t := hr_not t (by simp)
  have hrz' : r ≠ z := hr_not z (by simp)
  have hrw' : r ≠ w := hr_not w (by simp)
  have hσrs : σ r ≠ s := fun h => hr_not (σ s) (by simp) (by rw [← hσ r, h])
  have hσrt : σ r ≠ t := fun h => hr_not (σ t) (by simp) (by rw [← hσ r, h])
  have hσrz : σ r ≠ z := fun h => hr_not (σ z) (by simp) (by rw [← hσ r, h])
  have hσrw : σ r ≠ w := fun h => hr_not (σ w) (by simp) (by rw [← hσ r, h])
  refine ⟨swap s t * swap z w *
    ((swap s (σ s) * swap r (σ r)) * (swap s t * swap z w)
      * (swap s (σ s) * swap r (σ r))⁻¹),
    K.mul_mem hu (K.mul_mem (K.mul_mem hgK hu) (K.inv_mem hgK)), ?_⟩
  exact isThreeCycle_mul_conj hst hsz hsw htz htw hzw hs hs't hs'z hs'w hrs' hrt' hrz' hrw'
    hσrs hσrt hσrz hσrw

theorem exists_isThreeCycle_mem_of_not_le_centralizer (hσ : ∀ x, σ (σ x) = x)
    (hfix : ∀ x, σ x ≠ x) (h10 : 10 ≤ Fintype.card Ω) {H K : Subgroup (Perm Ω)}
    (hA : alternatingGroup Ω ≤ H) (hXK : H ⊓ Subgroup.centralizer {σ} ≤ K)
    (hK : ¬ K ≤ Subgroup.centralizer {σ}) : ∃ c ∈ K, c.IsThreeCycle := by
  obtain ⟨k, hkK, hkC⟩ : ∃ k ∈ K, k ∉ Subgroup.centralizer {σ} := by
    by_contra h
    apply hK
    intro x hx
    by_contra hxC
    exact h ⟨x, hx, hxC⟩
  have hkC' : k * σ ≠ σ * k := fun h =>
    hkC (Subgroup.mem_centralizer_singleton_iff.mpr h)
  have hex : ∃ a, k (σ a) ≠ σ (k a) := by
    by_contra h
    apply hkC'
    ext x
    by_contra hx
    exact h ⟨x, by simpa only [Equiv.Perm.coe_mul, Function.comp_apply] using hx⟩
  obtain ⟨a, ha⟩ := hex
  let c : Ω := k⁻¹ (σ (k a))
  obtain ⟨b, hbF⟩ := exists_notMem_of_card_le
    (F := ({a, σ a, c, σ c} : Finset Ω)) (Finset.card_le_four) (by omega)
  have hb_not : ∀ x ∈ ({a, σ a, c, σ c} : Finset Ω), b ≠ x :=
    fun x hx h => hbF (h ▸ hx)
  have hba : b ≠ a := hb_not a (by simp)
  have hbσa : b ≠ σ a := hb_not (σ a) (by simp)
  have hbc : b ≠ c := hb_not c (by simp)
  have hbσc : b ≠ σ c := hb_not (σ c) (by simp)
  have hbσb : b ≠ σ b := (hfix b).symm
  have hbaa : a ≠ σ a := (hfix a).symm
  have hvX : swap a (σ a) * swap b (σ b) ∈ H ⊓ Subgroup.centralizer {σ} :=
    swap_mul_swap_apply_mem_inf hσ hA (hfix a) (hfix b)
  have hvK : swap a (σ a) * swap b (σ b) ∈ K := hXK hvX
  have huK : k * (swap a (σ a) * swap b (σ b)) * k⁻¹ ∈ K :=
    K.mul_mem (K.mul_mem hkK hvK) (K.inv_mem hkK)
  have hu_eq : k * (swap a (σ a) * swap b (σ b)) * k⁻¹
      = swap (k a) (k (σ a)) * swap (k b) (k (σ b)) := by
    rw [← MulAut.conj_apply, map_mul]
    simp only [MulAut.conj_apply]
    rw [← swap_apply_apply k a (σ a), ← swap_apply_apply k b (σ b)]
  have hu : swap (k a) (k (σ a)) * swap (k b) (k (σ b)) ∈ K := by
    rw [← hu_eq]; exact huK
  obtain ⟨r, hrF⟩ := exists_notMem_of_card_le
    (F := ({k a, σ (k a), k (σ a), σ (k (σ a)), k b, σ (k b), k (σ b),
      σ (k (σ b))} : Finset Ω))
    (card_eight_le (k a) (σ (k a)) (k (σ a)) (σ (k (σ a))) (k b) (σ (k b)) (k (σ b))
      (σ (k (σ b)))) (by omega)
  have hst : k a ≠ k (σ a) := fun h => hbaa (k.injective h)
  have hsz : k a ≠ k b := fun h => hba (k.injective h).symm
  have hsw : k a ≠ k (σ b) := by
    intro h
    have hab : a = σ b := k.injective h
    exact hbσa (by rw [← hσ b, ← hab])
  have htz : k (σ a) ≠ k b := fun h => hbσa (k.injective h).symm
  have htw : k (σ a) ≠ k (σ b) := fun h => hba (σ.injective (k.injective h)).symm
  have hzw : k b ≠ k (σ b) := fun h => hbσb (k.injective h)
  have hs'z : σ (k a) ≠ k b := by
    intro h
    exact hbc (by show b = k⁻¹ (σ (k a)); rw [h]; exact (Equiv.symm_apply_apply k b).symm)
  have hs'w : σ (k a) ≠ k (σ b) := by
    intro h
    have hcb : c = σ b := by
      show k⁻¹ (σ (k a)) = σ b
      rw [h]; exact Equiv.symm_apply_apply k (σ b)
    exact hbσc (by rw [hcb, hσ b])
  exact exists_isThreeCycle_mem_of_swap_mul_swap_mem hσ hA hXK hst hsz hsw htz htw hzw
    (hfix (k a)) ha.symm hs'z hs'w hu (hfix r) hrF

theorem exists_isThreeCycle_mem_of_apply_ne (hσ : ∀ x, σ (σ x) = x) {α : Ω} (hα : σ α = α)
    (hfix : ∀ x, x ≠ α → σ x ≠ x) (h9 : 9 ≤ Fintype.card Ω) {H K : Subgroup (Perm Ω)}
    (hA : alternatingGroup Ω ≤ H) (hXK : H ⊓ Subgroup.centralizer {σ} ≤ K) {k : Perm Ω}
    (hk : k ∈ K) (hkα : k α ≠ α) : ∃ c ∈ K, c.IsThreeCycle := by
  have hβα : k⁻¹ α ≠ α := by
    intro h
    exact hkα (by
      calc k α = k (k⁻¹ α) := by rw [h]
        _ = α := Equiv.apply_symm_apply k α)
  have hσβ : σ (k⁻¹ α) ≠ k⁻¹ α := hfix _ hβα
  obtain ⟨b, hbF⟩ := exists_notMem_of_card_le
    (F := ({α, k⁻¹ α, σ (k⁻¹ α)} : Finset Ω)) (Finset.card_le_three) (by omega)
  have hb_not : ∀ x ∈ ({α, k⁻¹ α, σ (k⁻¹ α)} : Finset Ω), b ≠ x :=
    fun x hx h => hbF (h ▸ hx)
  have hbα : b ≠ α := hb_not α (by simp)
  have hbβ : b ≠ k⁻¹ α := hb_not (k⁻¹ α) (by simp)
  have hbσβ : b ≠ σ (k⁻¹ α) := hb_not (σ (k⁻¹ α)) (by simp)
  have hbσb : b ≠ σ b := (hfix b hbα).symm
  have hvX : swap (k⁻¹ α) (σ (k⁻¹ α)) * swap b (σ b) ∈ H ⊓ Subgroup.centralizer {σ} :=
    swap_mul_swap_apply_mem_inf hσ hA hσβ (hfix b hbα)
  have hvK : swap (k⁻¹ α) (σ (k⁻¹ α)) * swap b (σ b) ∈ K := hXK hvX
  have huK : k * (swap (k⁻¹ α) (σ (k⁻¹ α)) * swap b (σ b)) * k⁻¹ ∈ K :=
    K.mul_mem (K.mul_mem hk hvK) (K.inv_mem hk)
  have hu_eq : k * (swap (k⁻¹ α) (σ (k⁻¹ α)) * swap b (σ b)) * k⁻¹
      = swap α (k (σ (k⁻¹ α))) * swap (k b) (k (σ b)) := by
    rw [← MulAut.conj_apply, map_mul]
    simp only [MulAut.conj_apply]
    rw [← swap_apply_apply k (k⁻¹ α) (σ (k⁻¹ α)), ← swap_apply_apply k b (σ b)]
    rw [show k (k⁻¹ α) = α from Equiv.apply_symm_apply k α]
  have hu : swap α (k (σ (k⁻¹ α))) * swap (k b) (k (σ b)) ∈ K := by
    rw [← hu_eq]; exact huK
  let p1 : Ω := k (σ (k⁻¹ α))
  let p2 : Ω := k b
  let p3 : Ω := k (σ b)
  have hp1α : p1 ≠ α := by
    show k (σ (k⁻¹ α)) ≠ α
    intro h
    exact hσβ (k.injective (by rw [h]; exact (Equiv.apply_symm_apply k α).symm))
  have hp2α : p2 ≠ α := by
    show k b ≠ α
    intro h
    exact hbβ (k.injective (by rw [h]; exact (Equiv.apply_symm_apply k α).symm))
  have hp3α : p3 ≠ α := by
    show k (σ b) ≠ α
    intro h
    have hsb : σ b = k⁻¹ α :=
      k.injective (by rw [h]; exact (Equiv.apply_symm_apply k α).symm)
    exact hbσβ (by rw [← hσ b, hsb])
  have h12 : p1 ≠ p2 := by
    show k (σ (k⁻¹ α)) ≠ k b
    intro h
    exact hbσβ (k.injective h).symm
  have h13 : p1 ≠ p3 := by
    show k (σ (k⁻¹ α)) ≠ k (σ b)
    intro h
    exact hbβ (σ.injective (k.injective h)).symm
  have h23 : p2 ≠ p3 := by
    show k b ≠ k (σ b)
    intro h
    exact hbσb (k.injective h)
  obtain ⟨p, hpS, hσpS⟩ :=
    exists_apply_notMem_three hσ (α := α) hfix hp1α hp2α hp3α h12 h13 h23
  have hpα : p ≠ α := by
    have hpS' : p = p1 ∨ p = p2 ∨ p = p3 := by
      simpa only [Finset.mem_insert, Finset.mem_singleton] using hpS
    rcases hpS' with h | h | h
    · exact fun hp => hp1α (h.symm.trans hp)
    · exact fun hp => hp2α (h.symm.trans hp)
    · exact fun hp => hp3α (h.symm.trans hp)
  have hσpα : σ p ≠ α := by
    intro h
    exact hpα (σ.injective (by rw [h, hα]))
  have hcomm : Commute (swap p2 p3) (swap α p1) := by
    have hnodup : [p2, p3, α, p1].Nodup := by
      refine List.nodup_cons.2 ⟨?_, List.nodup_cons.2 ⟨?_,
        List.nodup_cons.2 ⟨?_, List.nodup_singleton _⟩⟩⟩
      · simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false, not_or]
        exact ⟨h23, hp2α, h12.symm⟩
      · simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false, not_or]
        exact ⟨hp3α, h13.symm⟩
      · simp only [List.mem_singleton]
        exact hp1α.symm
    exact (Equiv.Perm.disjoint_swap_swap hnodup).commute
  have hpS' : p = p1 ∨ p = p2 ∨ p = p3 := by
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hpS
  rcases hpS' with hp | hp | hp
  · subst hp
    have hs'z : σ p1 ≠ p2 := fun h => hσpS (by simp [h])
    have hs'w : σ p1 ≠ p3 := fun h => hσpS (by simp [h])
    obtain ⟨r, hrF⟩ := exists_notMem_of_card_le
      (F := ({p1, σ p1, α, σ α, p2, σ p2, p3, σ p3} : Finset Ω))
      (card_eight_le p1 (σ p1) α (σ α) p2 (σ p2) p3 (σ p3)) (by omega)
    have hrα : r ≠ α := fun h => hrF (by simp [h])
    have hu1 : swap p1 α * swap p2 p3 ∈ K := by
      rw [Equiv.swap_comm p1 α]; exact hu
    exact exists_isThreeCycle_mem_of_swap_mul_swap_mem hσ hA hXK hp1α h12 h13 hp2α.symm
      hp3α.symm h23 (hfix p1 hp1α) hσpα hs'z hs'w hu1 (hfix r hrα) hrF
  · subst hp
    have hs't : σ p2 ≠ p3 := fun h => hσpS (by simp [h])
    have hs'w : σ p2 ≠ p1 := fun h => hσpS (by simp [h])
    obtain ⟨r, hrF⟩ := exists_notMem_of_card_le
      (F := ({p2, σ p2, p3, σ p3, α, σ α, p1, σ p1} : Finset Ω))
      (card_eight_le p2 (σ p2) p3 (σ p3) α (σ α) p1 (σ p1)) (by omega)
    have hrα : r ≠ α := fun h => hrF (by simp [h])
    have hu2 : swap p2 p3 * swap α p1 ∈ K := by
      rw [hcomm.eq]; exact hu
    exact exists_isThreeCycle_mem_of_swap_mul_swap_mem hσ hA hXK h23 hp2α h12.symm hp3α
      h13.symm hp1α.symm (hfix p2 hp2α) hs't hσpα hs'w hu2 (hfix r hrα) hrF
  · subst hp
    have hs't : σ p3 ≠ p2 := fun h => hσpS (by simp [h])
    have hs'w : σ p3 ≠ p1 := fun h => hσpS (by simp [h])
    obtain ⟨r, hrF⟩ := exists_notMem_of_card_le
      (F := ({p3, σ p3, p2, σ p2, α, σ α, p1, σ p1} : Finset Ω))
      (card_eight_le p3 (σ p3) p2 (σ p2) α (σ α) p1 (σ p1)) (by omega)
    have hrα : r ≠ α := fun h => hrF (by simp [h])
    have hu3 : swap p3 p2 * swap α p1 ∈ K := by
      rw [Equiv.swap_comm p3 p2, hcomm.eq]; exact hu
    exact exists_isThreeCycle_mem_of_swap_mul_swap_mem hσ hA hXK h23.symm hp3α h13.symm
      hp2α h12.symm hp1α.symm (hfix p3 hp3α) hs't hσpα hs'w hu3 (hfix r hrα) hrF

end ThreeOne

end CFSG.LocalAnalysis.WeakClosure81

end
