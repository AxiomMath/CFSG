module

public import CFSG.Quasithin.EmptyFaithful.S151cTwo
public import CFSG.Quasithin.Recognition.F112WLocal2
public import CFSG.Quasithin.EmptyFaithful.S151cGrp

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits
open CFSG.QuasithinUnique (IsSylowTwoOf)

section TwoBl151c

variable {V : Type} [CommGroup V] [Finite V] {X Tb Xc : Subgroup (MulAut V)}

open Classical in
theorem fix_commV_of_coprime (h : Setting151c X Tb Xc) {r : ℚ} (hr : qhatOf X = (r : WithTop ℚ))
    (hr2 : r ≤ 2) {I : Finset (Subgroup (MulAut V))} (hI : IsBlocks216 (Jhat X) I)
    {L : Subgroup (MulAut V)} (hL : L ∈ I) (hS : S3Block L) {d : MulAut V}
    (hd : ∀ l ∈ L, d * l = l * d) (hcop : Nat.Coprime (orderOf d) 6) :
    ∀ u ∈ commV L, d u = u := by
  have hds : d ∈ stabSub (commV L) :=
    mem_stabSub_commV_of_conjBy (conjBy_eq_self_of_commute hd)
  set ρ : MulAut ↥(commV L) := resHom (commV L) ⟨d, hds⟩ with hρ
  have hρc : ρ ∈ Subgroup.centralizer (autSub L (commV L) : Set (MulAut ↥(commV L))) := by
    rw [Subgroup.mem_centralizer_iff]
    intro φ hφ
    obtain ⟨l, hl, rfl⟩ := mem_autSub.mp hφ
    rw [hρ, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hd l hl).symm
  have h6 := block_card_centralizer h hr hr2 hI hL hS
  have hord1 : orderOf ρ ∣ 6 := by
    have := orderOf_dvd_natCard
      (⟨ρ, hρc⟩ : ↥(Subgroup.centralizer (autSub L (commV L) : Set (MulAut ↥(commV L)))))
    rwa [h6, Subgroup.orderOf_mk] at this
  have hord2 : orderOf ρ ∣ orderOf d := by
    have := orderOf_map_dvd (resHom (commV L)) (⟨d, hds⟩ : ↥(stabSub (commV L)))
    rwa [Subgroup.orderOf_mk] at this
  have hρ1 : orderOf ρ = 1 :=
    (Nat.Coprime.coprime_dvd_left hord2 hcop).eq_one_of_dvd hord1
  have hρ1' : ρ = 1 := orderOf_eq_one_iff.mp hρ1
  intro u hu
  have := congrArg (fun φ : MulAut ↥(commV L) => ((φ ⟨u, hu⟩ : ↥(commV L)) : V)) hρ1'
  simpa [hρ, resHom_apply] using this

open Classical in
theorem not_three_dvd_orderOf (h : Setting151c X Tb Xc) {r : ℚ}
    (hr : qhatOf X = (r : WithTop ℚ)) (hr2 : r ≤ 2) {I : Finset (Subgroup (MulAut V))}
    (hI : IsBlocks216 (Jhat X) I) (hS : ∀ L ∈ I, S3Block L) {L₁ L₂ : Subgroup (MulAut V)}
    (h1 : L₁ ∈ I) (h2 : L₂ ∈ I) (hne : L₁ ≠ L₂) {d : MulAut V} (hdX : d ∈ X)
    (hd1 : ∀ l ∈ L₁, d * l = l * d) (hd2 : ∀ l ∈ L₂, d * l = l * d) : ¬ 3 ∣ orderOf d := by
  intro hdvd
  have hLX : ∀ L ∈ I, L ≤ X := fun L hL => (block_le_J hI hL).trans (Jhat_le X)
  have hord0 : orderOf d ≠ 0 := (orderOf_pos d).ne'
  set d' : MulAut V := d ^ (orderOf d / 3) with hd'
  have hd'3 : orderOf d' = 3 := orderOf_pow_orderOf_div hord0 hdvd
  have hd'cube : d' ^ 3 = 1 := by rw [← hd'3]; exact pow_orderOf_eq_one d'
  have hd'1 : d' ≠ 1 := by
    intro e
    rw [e, orderOf_one] at hd'3
    omega
  have hd'X : d' ∈ X := X.pow_mem hdX _
  have hc1 : ∀ l ∈ L₁, d' * l = l * d' := fun l hl =>
    (Commute.pow_left (show Commute d l from hd1 l hl) _).eq
  have hc2 : ∀ l ∈ L₂, d' * l = l * d' := fun l hl =>
    (Commute.pow_left (show Commute d l from hd2 l hl) _).eq
  obtain ⟨a₂, ha₂L, ha₂3, ha₂1⟩ := (hS L₂ h2).exists_order_three
  have hmem := eq_of_order_three_commute h hI h1
    (block_fittingOf_pgroup3 h hr hr2 hI h1 (hS L₁ h1)) (hLX L₂ h2 ha₂L) hd'X ha₂3 ha₂1 hd'cube
    (hc2 a₂ ha₂L) (fun l hl => hI.comm L₂ h2 L₁ h1 (Ne.symm hne) a₂ ha₂L l hl) hc1
  have hin2 : d' ∈ L₂ := (Subgroup.zpowers_le.mpr ha₂L) hmem
  obtain ⟨⟨e₂⟩, -⟩ := hS L₂ h2
  have hcent : d' ∈ Subgroup.centralizer (L₂ : Set (MulAut V)) :=
    Subgroup.mem_centralizer_iff.mpr fun m hm => (hc2 m hm).symm
  have : d' ∈ L₂ ⊓ Subgroup.centralizer (L₂ : Set (MulAut V)) := ⟨hin2, hcent⟩
  rw [inf_centralizer_eq_bot_D3 e₂] at this
  exact hd'1 (Subgroup.mem_bot.mp this)

open Classical in
theorem odd_mem_Xc_of_two_blocks (h : Setting151c X Tb Xc) {r : ℚ}
    (hr : qhatOf X = (r : WithTop ℚ)) (hr2 : r ≤ 2) {I : Finset (Subgroup (MulAut V))}
    (hI : IsBlocks216 (Jhat X) I) (hS : ∀ L ∈ I, S3Block L) {L₁ L₂ : Subgroup (MulAut V)}
    (h1 : L₁ ∈ I) (h2 : L₂ ∈ I) (hne : L₁ ≠ L₂) (hI2 : ∀ L₃ ∈ I, L₃ = L₁ ∨ L₃ = L₂)
    {d : MulAut V} (hdX : d ∈ X) (hd1 : ∀ l ∈ L₁, d * l = l * d)
    (hd2 : ∀ l ∈ L₂, d * l = l * d) (hodd : Odd (orderOf d)) : d ∈ Xc := by
  have hno3 := not_three_dvd_orderOf h hr hr2 hI hS h1 h2 hne hdX hd1 hd2
  have hcop : Nat.Coprime (orderOf d) 6 := by
    have h6 : (6 : ℕ) = 2 * 3 := by norm_num
    rw [h6]
    exact Nat.Coprime.mul_right (Nat.coprime_two_right.mpr hodd)
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hno3).symm
  have hf1 := fix_commV_of_coprime h hr hr2 hI h1 (hS L₁ h1) hd1 hcop
  have hf2 := fix_commV_of_coprime h hr hr2 hI h2 (hS L₂ h2) hd2 hcop
  have hJ : Jhat X = L₁ ⊔ L₂ := by
    apply le_antisymm
    · rw [hI.sup_eq]
      refine iSup₂_le fun L hL => ?_
      rcases hI2 L hL with rfl | rfl
      · exact le_sup_left
      · exact le_sup_right
    · exact sup_le (block_le_J hI h1) (block_le_J hI h2)
  have hJn : NormalIn X (Jhat X) := fun x hx k hk => Jhat_conj_mem hx hk
  have hWinv : ∀ g ∈ Tb, ∀ u ∈ commV (Jhat X), g u ∈ commV (Jhat X) := fun g hg u hu =>
    hJn.commV_invariant (h.syl.1 hg) hu
  have hWne : commV (Jhat X) ≠ ⊥ := by
    intro e
    apply hI.ne_bot L₁ h1
    exact le_bot_iff.mp ((block_le_J hI h1).trans (eq_bot_of_commV_eq_bot e).le)
  have hpos := rk_inf_fixV_pos_of_isPGroup_two h.sq h.syl.2.1 hWinv hWne
  have hne' : (commV (Jhat X) ⊓ fixV Tb : Subgroup V) ≠ ⊥ := (rk_pos_iff_ne_bot' h.sq).mp hpos
  obtain ⟨⟨z, hz⟩, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne'
  have hz1' : z ≠ 1 := fun e => hz1 (Subtype.ext e)
  have hzW' : z ∈ commV L₁ ⊔ commV L₂ := commV_sup_le151c L₁ L₂ (by rw [← hJ]; exact hz.1)
  obtain ⟨u₁, hu₁, u₂, hu₂, hz'⟩ := Subgroup.mem_sup.mp hzW'
  have hdz : d z = z := by rw [← hz', map_mul, hf1 u₁ hu₁, hf2 u₂ hu₂]
  have hZ1 : Subgroup.zpowers z ≤ fixV Tb := Subgroup.zpowers_le.mpr hz.2
  have hZ1ne : Subgroup.zpowers z ≠ ⊥ := fun e => hz1' (Subgroup.zpowers_eq_bot.mp e)
  refine h.hU _ hZ1 hZ1ne ⟨hdX, ?_⟩
  intro u hu
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
  rw [map_zpow, hdz]

open Classical in
theorem two_blocks_false (h : Setting151c X Tb Xc) {r : ℚ} (hr : qhatOf X = (r : WithTop ℚ))
    (hr2 : r ≤ 2) {I : Finset (Subgroup (MulAut V))} (hI : IsBlocks216 (Jhat X) I)
    (hS : ∀ L ∈ I, S3Block L) (hXc : ∀ L ∈ I, L ≤ Xc) {L₁ L₂ : Subgroup (MulAut V)}
    (h1 : L₁ ∈ I) (h2 : L₂ ∈ I) (hne : L₁ ≠ L₂) : False := by
  have hLX : ∀ L ∈ I, L ≤ X := fun L hL => (block_le_J hI hL).trans (Jhat_le X)
  have hI2 : ∀ L₃ ∈ I, L₃ = L₁ ∨ L₃ = L₂ := by
    intro L₃ h3
    by_contra hcon
    push Not at hcon
    exact three_blocks_false h hr hr2 hI hS h1 h2 h3 hne (Ne.symm hcon.1) (Ne.symm hcon.2)
  have hperm : ∀ x ∈ X, (conjBy x L₁ = L₁ ∧ conjBy x L₂ = L₂) ∨
      (conjBy x L₁ = L₂ ∧ conjBy x L₂ = L₁) := by
    intro x hx
    have a1 := hI2 _ (block_conj_mem h hr hr2 hI h1 hx)
    have a2 := hI2 _ (block_conj_mem h hr hr2 hI h2 hx)
    rcases a1 with a1 | a1
    · rcases a2 with a2 | a2
      · exfalso
        exact hne (conjBy_injective x (a1.trans a2.symm))
      · exact Or.inl ⟨a1, a2⟩
    · rcases a2 with a2 | a2
      · exact Or.inr ⟨a1, a2⟩
      · exfalso
        exact hne (conjBy_injective x (a1.trans a2.symm))
  have hNT : ∀ x ∈ X, ∃ n ∈ stabConj X L₁, ∃ t ∈ Tb, x = n * t := by
    intro x hx
    rcases hperm x hx with ⟨a1, -⟩ | ⟨a1, a2⟩
    · exact ⟨x, ⟨hx, a1⟩, 1, Tb.one_mem, by simp⟩
    · obtain ⟨t, ht, et⟩ := exists_swap_of_orbit_two h (Ne.symm hne) hx a1 (fun y hy => by
        rcases hperm y hy with ⟨b1, -⟩ | ⟨b1, -⟩
        · exact Or.inl b1
        · exact Or.inr b1)
      have htX : t ∈ X := h.syl.1 ht
      have et2 : conjBy t L₂ = L₁ := by
        rcases hperm t htX with ⟨b1, -⟩ | ⟨-, b2⟩
        · exact absurd (b1.symm.trans et) hne
        · exact b2
      have et' : conjBy t⁻¹ L₁ = L₂ := conjBy_inv_eq_of_eq et2
      refine ⟨x * t⁻¹, ⟨X.mul_mem hx (X.inv_mem htX), ?_⟩, t, ht, by group⟩
      rw [← conjBy_conjBy, et', a2]
  obtain ⟨⟨e₁⟩, -⟩ := hS L₁ h1
  obtain ⟨⟨e₂⟩, -⟩ := hS L₂ h2
  set N : Subgroup (MulAut V) := stabConj X L₁ with hN
  have hNn : ∀ x ∈ N, conjBy x L₂ = L₂ := fun x hx =>
    ((hperm x hx.1).resolve_right (fun hh => hne (hx.2.symm.trans hh.1))).2
  have hL₁N : L₁ ≤ N := fun l hl => ⟨hLX L₁ h1 hl, conjBy_eq_self_of_mem hl⟩
  have step1 : ∀ x ∈ N, ∃ l ∈ L₁, ∃ d ∈ N, (∀ m ∈ L₁, d * m = m * d) ∧ x = l * d :=
    fun x hx => exists_mul_eq_of_normalizes_D3 e₁ hL₁N
      (fun y hy => mem_normalizer_of_conjBy_eq hy.2) hx
  set N' : Subgroup (MulAut V) := N ⊓ Subgroup.centralizer (L₁ : Set (MulAut V)) with hN'
  have hL₂N' : L₂ ≤ N' := by
    intro l hl
    have hcomm : ∀ m ∈ L₁, l * m = m * l := fun m hm =>
      hI.comm L₂ h2 L₁ h1 (Ne.symm hne) l hl m hm
    exact ⟨⟨hLX L₂ h2 hl, conjBy_eq_self_of_commute hcomm⟩,
      Subgroup.mem_centralizer_iff.mpr fun m hm => (hcomm m hm).symm⟩
  have step2 : ∀ x ∈ N', ∃ l ∈ L₂, ∃ d ∈ N', (∀ m ∈ L₂, d * m = m * d) ∧ x = l * d :=
    fun x hx => exists_mul_eq_of_normalizes_D3 e₂ hL₂N'
      (fun y hy => mem_normalizer_of_conjBy_eq (hNn y hy.1)) hx
  set D₂ : Subgroup (MulAut V) :=
    X ⊓ Subgroup.centralizer (L₁ : Set (MulAut V)) ⊓ Subgroup.centralizer (L₂ : Set (MulAut V))
    with hD₂
  have hdc : ∀ d ∈ D₂, ∀ m, (m ∈ L₁ ∨ m ∈ L₂) → d * m = m * d := by
    intro d hd m hm
    rcases hm with hm | hm
    · exact (Subgroup.mem_centralizer_iff.mp hd.1.2 m hm).symm
    · exact (Subgroup.mem_centralizer_iff.mp hd.2 m hm).symm
  have hconjmem : ∀ x ∈ X, ∀ l, (l ∈ L₁ ∨ l ∈ L₂) → (x * l * x⁻¹ ∈ L₁ ∨ x * l * x⁻¹ ∈ L₂) := by
    intro x hx l hl
    rcases hl with hl | hl
    · have hm := mem_conjBy_of_mem (g := x) hl
      rcases hperm x hx with ⟨a1, -⟩ | ⟨a1, -⟩
      · rw [a1] at hm; exact Or.inl hm
      · rw [a1] at hm; exact Or.inr hm
    · have hm := mem_conjBy_of_mem (g := x) hl
      rcases hperm x hx with ⟨-, a2⟩ | ⟨-, a2⟩
      · rw [a2] at hm; exact Or.inr hm
      · rw [a2] at hm; exact Or.inl hm
  have hD₂n : NormalIn X D₂ := by
    intro x hx d hd
    have key : ∀ l, (x⁻¹ * l * x ∈ L₁ ∨ x⁻¹ * l * x ∈ L₂) →
        x * d * x⁻¹ * l = l * (x * d * x⁻¹) := by
      intro l hl
      have hc := hdc d hd _ hl
      calc x * d * x⁻¹ * l = x * (d * (x⁻¹ * l * x)) * x⁻¹ := by group
        _ = x * ((x⁻¹ * l * x) * d) * x⁻¹ := by rw [hc]
        _ = l * (x * d * x⁻¹) := by group
    have hinv : ∀ l, (l ∈ L₁ ∨ l ∈ L₂) → (x⁻¹ * l * x ∈ L₁ ∨ x⁻¹ * l * x ∈ L₂) := by
      intro l hl
      simpa using hconjmem x⁻¹ (X.inv_mem hx) l hl
    refine ⟨⟨X.mul_mem (X.mul_mem hx hd.1.1) (X.inv_mem hx), ?_⟩, ?_⟩
    · exact Subgroup.mem_centralizer_iff.mpr fun l hl => (key l (hinv l (Or.inl hl))).symm
    · exact Subgroup.mem_centralizer_iff.mpr fun l hl => (key l (hinv l (Or.inr hl))).symm
  have hD₂Xc : D₂ ≤ Xc := by
    have hsyl : IsSylowTwoOf (Tb ⊓ D₂) D₂ :=
      A4.isSylowTwoOf_inf_normal (h.syl : IsSylowTwoOf Tb X) (inf_le_left.trans inf_le_left)
        hD₂n.le_normalizer
    have hsup := F112W.sup_oTwoUpper_eq_of_isSylowTwoOf hsyl
    rw [← hsup]
    refine sup_le (inf_le_left.trans h.tb_le) ?_
    refine (Subgroup.closure_le Xc).mpr ?_
    rintro d ⟨hd, hodd⟩
    exact odd_mem_Xc_of_two_blocks h hr hr2 hI hS h1 h2 hne hI2 hd.1.1
      (fun l hl => hdc d hd l (Or.inl hl)) (fun l hl => hdc d hd l (Or.inr hl)) hodd
  apply h.xc_ne
  intro x hx
  obtain ⟨n, hn, t, ht, rfl⟩ := hNT x hx
  refine Xc.mul_mem ?_ (h.tb_le ht)
  obtain ⟨l₁, hl₁, d₁, hd₁N, hd₁c, rfl⟩ := step1 n hn
  have hd₁N' : d₁ ∈ N' :=
    ⟨hd₁N, Subgroup.mem_centralizer_iff.mpr fun m hm => (hd₁c m hm).symm⟩
  obtain ⟨l₂, hl₂, d₂, hd₂N', hd₂c, rfl⟩ := step2 d₁ hd₁N'
  have hd₂D : d₂ ∈ D₂ :=
    ⟨⟨hd₂N'.1.1, hd₂N'.2⟩, Subgroup.mem_centralizer_iff.mpr fun m hm => (hd₂c m hm).symm⟩
  exact Xc.mul_mem (hXc L₁ h1 hl₁) (Xc.mul_mem (hXc L₂ h2 hl₂) (hD₂Xc hd₂D))

end TwoBl151c

end CFSG.Quasithin
