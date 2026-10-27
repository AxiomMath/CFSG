module

public import CFSG.Quasithin.EmptyFaithful.S1417Factor

public section

namespace CFSG.Quasithin.H13.L32A.Blk

open CFSG.Quasithin CFSG.Quasithin.S1417

theorem sl2_three : ∀ a b : SL2, a ^ 3 = 1 → a ≠ 1 → b ^ 3 = 1 → b = 1 ∨ b = a ∨ b = a ^ 2 := by
  decide

theorem conj_eq_of_odd {D : Type*} [Group D] {g l : D} (hgo : Odd (orderOf g)) (hl3 : l ^ 3 = 1)
    (h : g * l * g⁻¹ = 1 ∨ g * l * g⁻¹ = l ∨ g * l * g⁻¹ = l ^ 2) : g * l * g⁻¹ = l := by
  rcases h with h | h | h
  · have hl : l = 1 := by
      calc l = g⁻¹ * (g * l * g⁻¹) * g := by group
        _ = 1 := by rw [h]; group
    rw [h, hl]
  · exact h
  · have hinv : l ^ 2 = l⁻¹ := by
      rw [eq_inv_iff_mul_eq_one, ← pow_succ, hl3]
    rw [hinv] at h
    have h' : g * l⁻¹ * g⁻¹ = l := by
      calc g * l⁻¹ * g⁻¹ = (g * l * g⁻¹)⁻¹ := by group
        _ = l := by rw [h, inv_inv]
    have hc : Commute (g ^ 2) l := by
      rw [pow_two]
      show g * g * l = l * (g * g)
      calc g * g * l = g * (g * l * g⁻¹) * g⁻¹ * (g * g) := by group
        _ = g * l⁻¹ * g⁻¹ * (g * g) := by rw [h]
        _ = l * (g * g) := by rw [h']
    obtain ⟨j, hj⟩ := hgo
    obtain ⟨c, hcdef⟩ : ∃ c, c = (g ^ 2) ^ j := ⟨_, rfl⟩
    have hg1 : g * c = 1 := by
      rw [hcdef, ← pow_mul, ← pow_succ', ← hj, pow_orderOf_eq_one]
    have hcl : c * l = l * c := by
      rw [hcdef]
      exact (hc.pow_left j).eq
    have hl1 : l = l⁻¹ := by
      calc l = (g * c) * l * (g * c)⁻¹ := by rw [hg1]; group
        _ = g * (c * l) * c⁻¹ * g⁻¹ := by group
        _ = g * (l * c) * c⁻¹ * g⁻¹ := by rw [hcl]
        _ = g * l * g⁻¹ := by group
        _ = l⁻¹ := h
    rw [h]
    exact hl1.symm

section Blocks

variable {W : Type} [CommGroup W] {Xh Y : Subgroup (MulAut W)} {I : Finset (Subgroup (MulAut W))}

theorem conjAut_eq_of_mem (hS : BlockSystem Xh Y I) {g : MulAut W} (hg : g ∈ Y)
    {L : Subgroup (MulAut W)} (hL : L ∈ I) : B1.conjAut g L = L := by
  have hYN : Y ≤ Subgroup.normalizer (L : Set (MulAut W)) := by
    rw [hS.Y_eq]
    refine iSup₂_le fun L' hL' => ?_
    by_cases he : L' = L
    · rw [he]
      exact Subgroup.le_normalizer
    · refine le_trans ?_ (Subgroup.centralizer_le_normalizer (s := (L : Set (MulAut W))))
      intro a ha
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      exact (hS.comm L' hL' L hL he a ha b hb).symm
  ext x
  rw [B1.mem_conjAut]
  have h := Subgroup.mem_normalizer_iff.mp (hYN hg) (g⁻¹ * x * g)
  rw [show g * (g⁻¹ * x * g) * g⁻¹ = x by group] at h
  exact h

theorem mem_stabSub_of_mem (hS : BlockSystem Xh Y I) (hYX : Y ≤ Xh) {g : MulAut W} (hg : g ∈ Y)
    {L : Subgroup (MulAut W)} (hL : L ∈ I) : g ∈ stabSub (commV L) := by
  apply S1417.mem_stabSub_of_map_eq
  rw [(hS.perm g (hYX hg) L hL).2, conjAut_eq_of_mem hS hg hL]

theorem eq_of_agree (hS : BlockSystem Xh Y I) {g g' : MulAut W}
    (hF : ∀ w ∈ fixV Y, g w = g' w) (hU : ∀ L ∈ I, ∀ u ∈ commV L, g u = g' u) : g = g' := by
  have hle : fixV Y ⊔ (⨆ L ∈ I, commV L) ≤ MonoidHom.eqLocus g.toMonoidHom g'.toMonoidHom := by
    refine sup_le (fun w hw => hF w hw) (iSup₂_le fun L hL u hu => hU L hL u hu)
  rw [hS.sup] at hle
  exact MulEquiv.ext fun w => hle (Subgroup.mem_top w)

theorem pow_eq_one_of_rep {L : Subgroup (MulAut W)} (hN : ActsAsNaturalL2 L (commV L))
    {g l : MulAut W} (hg : g ∈ stabSub (commV L)) (hl : l ∈ L)
    (hlg : ∀ u ∈ commV L, l u = g u) {n : ℕ} (hn : g ^ n = 1) : l ^ n = 1 := by
  have key : ∀ m : ℕ, ∀ u ∈ commV L, (l ^ m) u = (g ^ m) u := by
    intro m
    induction m with
    | zero => intro u _; rfl
    | succ m ih =>
      intro u hu
      rw [pow_succ, pow_succ, MulAut.mul_apply, MulAut.mul_apply, hlg u hu]
      exact ih _ ((CFSG.Quasithin.mem_stabSub.mp hg u).mpr hu)
  refine eq_one_of_forall_apply_eq hN (fun _ hl' _ hu => commV_stable L hl' hu) (L.pow_mem hl n)
    fun u hu => ?_
  rw [key n u hu, hn, MulAut.one_apply]

theorem cube_of_odd {L : Subgroup (MulAut W)} {U : Subgroup W} (hN : ActsAsNaturalL2 L U)
    {l : MulAut W} (hl : l ∈ L) (hodd : Odd (orderOf l)) : l ^ 3 = 1 := by
  have hdvd : orderOf l ∣ 6 := by
    have h1 : orderOf (⟨l, hl⟩ : L) ∣ Nat.card L := orderOf_dvd_natCard _
    rwa [Subgroup.orderOf_mk, (card_of_actsAsNaturalL2 hN).1] at h1
  have hcop : Nat.Coprime (orderOf l) 2 := Nat.coprime_two_right.mpr hodd
  exact orderOf_dvd_iff_pow_eq_one.mp (hcop.dvd_of_dvd_mul_left (by simpa using hdvd))

theorem block_three {L : Subgroup (MulAut W)} (e : ↥L ≃* SL2) {a b : MulAut W} (ha : a ∈ L)
    (hb : b ∈ L) (ha3 : a ^ 3 = 1) (ha1 : a ≠ 1) (hb3 : b ^ 3 = 1) :
    b = 1 ∨ b = a ∨ b = a ^ 2 := by
  have h3 : e ⟨a, ha⟩ ^ 3 = 1 := by
    rw [← map_pow, show (⟨a, ha⟩ : ↥L) ^ 3 = 1 from Subtype.ext (by simpa using ha3), map_one]
  have h3' : e ⟨b, hb⟩ ^ 3 = 1 := by
    rw [← map_pow, show (⟨b, hb⟩ : ↥L) ^ 3 = 1 from Subtype.ext (by simpa using hb3), map_one]
  have h1 : e ⟨a, ha⟩ ≠ 1 := fun h => ha1 (by
    have := e.injective (h.trans (map_one e).symm)
    exact congrArg Subtype.val this)
  rcases sl2_three _ _ h3 h1 h3' with h | h | h
  · left
    have := congrArg Subtype.val (e.injective (h.trans (map_one e).symm))
    simpa using this
  · right; left
    have := congrArg Subtype.val (e.injective h)
    simpa using this
  · right; right
    rw [← map_pow] at h
    have := congrArg Subtype.val (e.injective h)
    simpa using this

theorem conjAut_eq_of_odd (hS : BlockSystem Xh Y I) (hI : I.card ≤ 2) {g : MulAut W}
    (hg : g ∈ Xh) (hodd : Odd (orderOf g)) {L : Subgroup (MulAut W)} (hL : L ∈ I) :
    B1.conjAut g L = L := by
  classical
  by_contra hne
  set L' := B1.conjAut g L with hL'def
  have hL' : L' ∈ I := (hS.perm g hg L hL).1
  have hpair : ∀ M ∈ I, M = L ∨ M = L' := by
    intro M hM
    by_contra h
    push Not at h
    have hsub : ({L, L', M} : Finset (Subgroup (MulAut W))) ⊆ I := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      exacts [hL, hL', hM]
    have hcard : ({L, L', M} : Finset (Subgroup (MulAut W))).card = 3 := by
      rw [Finset.card_insert_of_notMem, Finset.card_pair (Ne.symm h.2)]
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨Ne.symm hne, Ne.symm h.1⟩
    have := Finset.card_le_card hsub
    omega
  have hgL' : B1.conjAut g L' = L := by
    rcases hpair _ (hS.perm g hg L' hL').1 with h | h
    · exact h
    · exact absurd (conjAut_injective (h.trans hL'def)) hne
  have h2 : B1.conjAut (g ^ 2) L = L := by
    rw [pow_two, conjAut_mul, ← hL'def, hgL']
  have h2j : ∀ j : ℕ, B1.conjAut ((g ^ 2) ^ j) L = L := by
    intro j
    induction j with
    | zero =>
      ext x
      simp [B1.mem_conjAut]
    | succ j ih => rw [pow_succ, conjAut_mul, h2, ih]
  obtain ⟨j, hj⟩ := hodd
  have hg1 : g * (g ^ 2) ^ j = 1 := by
    rw [← pow_mul, ← pow_succ', ← hj, pow_orderOf_eq_one]
  apply hne
  calc L' = B1.conjAut g (B1.conjAut ((g ^ 2) ^ j) L) := by rw [h2j]
    _ = B1.conjAut (g * (g ^ 2) ^ j) L := (conjAut_mul _ _ _).symm
    _ = L := by
      rw [hg1]
      ext x
      simp [B1.mem_conjAut]

theorem comm_of_odd (hS : BlockSystem Xh Y I) (hYX : Y ≤ Xh) (hI : I.card ≤ 2)
    (hXY : ∀ g ∈ Xh, B1.conjAut g Y = Y) {g k : MulAut W} (hg : g ∈ Xh)
    (hgo : Odd (orderOf g)) (hk : k ∈ Y) (hko : Odd (orderOf k)) : g * k = k * g := by
  have hginv : g⁻¹ ∈ Xh := Xh.inv_mem hg
  suffices h : g * k * g⁻¹ = k by
    calc g * k = g * k * g⁻¹ * g := by group
      _ = k * g := by rw [h]
  refine eq_of_agree hS (fun w hw => ?_) fun L hL u hu => ?_
  · have hw' : g⁻¹ w ∈ fixV Y := apply_mem_fixV_of_conj (hXY g⁻¹ hginv) hw
    show g (k (g⁻¹ w)) = k w
    rw [hw' k hk, hw k hk]
    simp
  · have hgL : B1.conjAut g L = L := conjAut_eq_of_odd hS hI hg hgo hL
    have hgL' : B1.conjAut g⁻¹ L = L := conjAut_inv_eq hgL
    have hu' : g⁻¹ u ∈ commV L := by
      have h1 := (hS.perm g⁻¹ hginv L hL).2
      rw [hgL'] at h1
      have h2 := Subgroup.mem_map_of_mem g⁻¹.toMonoidHom hu
      rwa [h1] at h2
    have hst := mem_stabSub_of_mem hS hYX hk hL
    obtain ⟨l, hl, hlk⟩ :=
      exists_apply_eq_of_stab (hS.nat L hL) (fun _ hl _ hu => commV_stable L hl hu) hst
    have hl3 : l ^ 3 = 1 := by
      have hn := pow_eq_one_of_rep (hS.nat L hL) hst hl hlk (pow_orderOf_eq_one k)
      exact cube_of_odd (hS.nat L hL) hl (hko.of_dvd_nat (orderOf_dvd_of_pow_eq_one hn))
    have hgl : g * l * g⁻¹ = l := by
      by_cases hl1 : l = 1
      · rw [hl1]
        group
      obtain ⟨e, -, -⟩ := hS.nat L hL
      have hmem : g * l * g⁻¹ ∈ L := by
        have h1 : g * l * g⁻¹ ∈ B1.conjAut g L := by
          rw [B1.mem_conjAut]
          simpa [mul_assoc] using hl
        rwa [hgL] at h1
      have h3 : (g * l * g⁻¹) ^ 3 = 1 := by
        rw [conj_pow, hl3]
        group
      exact conj_eq_of_odd hgo hl3 (block_three e hl hmem hl3 hl1 h3)
    show g (k (g⁻¹ u)) = k u
    rw [← hlk _ hu', ← hlk u hu]
    show (g * l * g⁻¹) u = l u
    rw [hgl]

end Blocks

end CFSG.Quasithin.H13.L32A.Blk
