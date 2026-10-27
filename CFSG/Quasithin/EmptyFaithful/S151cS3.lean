module

public import CFSG.Quasithin.EmptyFaithful.S151cOm4
public import CFSG.Quasithin.EmptyFaithful.S151cOrbit

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits

section S3Block151c

variable {V : Type} [CommGroup V] [Finite V] {X Tb Xc : Subgroup (MulAut V)}

@[expose] def S3Block (L : Subgroup (MulAut V)) : Prop :=
  Nonempty (↥L ≃* DihedralGroup 3) ∧ rk (commV L) = 4

omit [Finite V] in
theorem S3Block_iff {L : Subgroup (MulAut V)} {W : Subgroup V} (hs : SuppData L (commV L) W) :
    S3Block L ↔ Nonempty (↥(autSub L (commV L)) ≃* DihedralGroup 3) ∧ rk (commV L) = 4 := by
  unfold S3Block
  constructor
  · rintro ⟨⟨e⟩, hr⟩
    exact ⟨⟨hs.restrictEquiv.symm.trans e⟩, hr⟩
  · rintro ⟨⟨e⟩, hr⟩
    exact ⟨⟨hs.restrictEquiv.trans e⟩, hr⟩

theorem S3Block.card_commV {L : Subgroup (MulAut V)} (hS : S3Block L) (hV : ∀ v : V, v ^ 2 = 1) :
    Nat.card (commV L) = 16 := by
  rw [card_eq_two_pow hV, hS.2]
  norm_num

theorem d3_cube_eq : ∀ a b : DihedralGroup 3, a * a * a = 1 → a ≠ 1 → b * b * b = 1 →
    b = 1 ∨ b = a ∨ b = a * a := by
  decide

theorem block_fitting_cube (h : Setting151c X Tb Xc) {r : ℚ} (hr : qhatOf X = (r : WithTop ℚ))
    (hr2 : r ≤ 2) {I : Finset (Subgroup (MulAut V))} (hI : IsBlocks216 (Jhat X) I)
    {L : Subgroup (MulAut V)} (hL : L ∈ I)
    (e : ↥(autSub L (commV L)) ≃* DihedralGroup 3) :
    ∀ x ∈ fittingOf (autSub L (commV L)), x ^ 3 = 1 := by
  intro x hx
  have hH := block_d217hyp h hr hr2 hI hL
  have hYcard : Nat.card (autSub L (commV L)) = 6 := by
    rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
  have hodd := odd_card_fittingOf hH.o2
  have hFdvd : Nat.card (fittingOf (autSub L (commV L))) ∣ 6 :=
    hYcard ▸ Subgroup.card_dvd_of_le (fittingOf_le _)
  have h1 : x ^ Nat.card (fittingOf (autSub L (commV L))) = 1 := by
    have := pow_card_eq_one' (G := ↥(fittingOf (autSub L (commV L)))) (x := ⟨x, hx⟩)
    exact congrArg Subtype.val this
  have h2 : Nat.card (fittingOf (autSub L (commV L))) ∣ 3 := by
    have hcop : Nat.Coprime (Nat.card (fittingOf (autSub L (commV L)))) 2 :=
      Nat.coprime_two_right.mpr hodd
    have h62 : (6 : ℕ) = 3 * 2 := by norm_num
    rw [h62] at hFdvd
    exact hcop.dvd_of_dvd_mul_right hFdvd
  obtain ⟨k, hk⟩ := h2
  rw [hk, pow_mul, h1, one_pow]

theorem block_hfix (h : Setting151c X Tb Xc) {r : ℚ} (hr : qhatOf X = (r : WithTop ℚ))
    (hr2 : r ≤ 2) {I : Finset (Subgroup (MulAut V))} (hI : IsBlocks216 (Jhat X) I)
    {L : Subgroup (MulAut V)} (hL : L ∈ I)
    (e : ↥(autSub L (commV L)) ≃* DihedralGroup 3) :
    ∀ g ∈ autSub L (commV L), orderOf g = 3 → ∀ u : ↥(commV L), g u = u → u = 1 := by
  intro g hg hg3 u hu
  have hH := block_d217hyp h hr hr2 hI hL
  have hUsq : ∀ v : ↥(commV L), v ^ 2 = 1 := fun v => Subtype.ext (h.sq v)
  have hfixF : fixV (fittingOf (autSub L (commV L))) = ⊥ :=
    fixV_fittingOf_eq_bot hUsq hH.o2 hH.comm_fitting
  have hF3 := block_fitting_cube h hr hr2 hI hL e
  have hg3' : g ^ 3 = 1 := by rw [← hg3]; exact pow_orderOf_eq_one g
  have hg1 : g ≠ 1 := by
    rintro rfl
    simp at hg3
  set a : ↥(autSub L (commV L)) := ⟨g, hg⟩ with ha
  have hacube : e a * e a * e a = 1 := by
    have h3 : a ^ 3 = 1 := Subtype.ext hg3'
    have := congrArg e h3
    rw [map_pow, map_one, pow_three'] at this
    exact this
  have hne1 : e a ≠ 1 := fun h' => hg1 (congrArg Subtype.val (e.injective (h'.trans (map_one e).symm)))
  have hu' : u ∈ fixV (fittingOf (autSub L (commV L))) := by
    intro x hx
    have hx' : x ∈ autSub L (commV L) := fittingOf_le _ hx
    have hx3 : (⟨x, hx'⟩ : ↥(autSub L (commV L))) ^ 3 = 1 := Subtype.ext (hF3 x hx)
    have hxc : e ⟨x, hx'⟩ * e ⟨x, hx'⟩ * e ⟨x, hx'⟩ = 1 := by
      have := congrArg e hx3
      rw [map_pow, map_one, pow_three'] at this
      exact this
    rcases d3_cube_eq (e a) (e ⟨x, hx'⟩) hacube hne1 hxc with h1 | h1 | h1
    · have : (⟨x, hx'⟩ : ↥(autSub L (commV L))) = 1 := e.injective (h1.trans (map_one e).symm)
      have hx1 : x = 1 := congrArg Subtype.val this
      rw [hx1]
      rfl
    · have : (⟨x, hx'⟩ : ↥(autSub L (commV L))) = a := e.injective h1
      have hxg : x = g := congrArg Subtype.val this
      rw [hxg]
      exact hu
    · have : (⟨x, hx'⟩ : ↥(autSub L (commV L))) = a * a :=
        e.injective (h1.trans (map_mul e a a).symm)
      have hxg : x = g * g := congrArg Subtype.val this
      rw [hxg]
      show g (g u) = u
      rw [hu, hu]
  rw [hfixF] at hu'
  exact Subgroup.mem_bot.mp hu'

theorem block_fittingOf_pgroup3 (h : Setting151c X Tb Xc) {r : ℚ}
    (hr : qhatOf X = (r : WithTop ℚ)) (hr2 : r ≤ 2) {I : Finset (Subgroup (MulAut V))}
    (hI : IsBlocks216 (Jhat X) I) {L : Subgroup (MulAut V)} (hL : L ∈ I) (hS : S3Block L) :
    IsPGroup 3 (fittingOf L) := by
  have hs := suppData_block h hI hL
  obtain ⟨⟨e⟩, -⟩ := (S3Block_iff hs).mp hS
  have hcube := block_fitting_cube h hr hr2 hI hL e
  rintro ⟨x, hx⟩
  refine ⟨1, Subtype.ext ?_⟩
  have hxL : x ∈ L := fittingOf_le L hx
  have hmem : ((hs.restrictEquiv ⟨x, hxL⟩ : ↥(autSub L (commV L))) : MulAut ↥(commV L)) ∈
      fittingOf (autSub L (commV L)) := by
    rw [hs.restrictEquiv_coe]
    exact fittingOf_autSub_le hs.stab (mem_autSub.mpr ⟨⟨x, hs.stab hxL⟩, hx, rfl⟩)
  have h1 : hs.restrictEquiv ((⟨x, hxL⟩ : ↥L) ^ 3) = 1 := by
    rw [map_pow]
    exact Subtype.ext (hcube _ hmem)
  have h2 : (⟨x, hxL⟩ : ↥L) ^ 3 = 1 := hs.restrictEquiv.injective (h1.trans (map_one _).symm)
  simpa using congrArg Subtype.val h2

omit [Finite V] in
theorem S3Block.exists_order_three {L : Subgroup (MulAut V)} (hS : S3Block L) :
    ∃ a ∈ L, a ^ 3 = 1 ∧ a ≠ 1 := by
  obtain ⟨⟨e⟩, -⟩ := hS
  refine ⟨((e.symm (DihedralGroup.r 1) : ↥L) : MulAut V), (e.symm _).2, ?_, ?_⟩
  · have h3 : (e.symm (DihedralGroup.r 1)) ^ 3 = 1 := by
      have h4 : (DihedralGroup.r 1 : DihedralGroup 3) * DihedralGroup.r 1 * DihedralGroup.r 1 = 1 := by
        decide
      rw [← map_pow, pow_three', h4, map_one]
    exact congrArg Subtype.val h3
  · intro h1
    have h2 : e.symm (DihedralGroup.r 1) = 1 := Subtype.ext h1
    have h3 : (DihedralGroup.r 1 : DihedralGroup 3) = 1 := by
      have := congrArg e h2
      rwa [MulEquiv.apply_symm_apply, map_one] at this
    exact absurd h3 (by decide)

theorem block_card_centralizer (h : Setting151c X Tb Xc) {r : ℚ}
    (hr : qhatOf X = (r : WithTop ℚ)) (hr2 : r ≤ 2) {I : Finset (Subgroup (MulAut V))}
    (hI : IsBlocks216 (Jhat X) I) {L : Subgroup (MulAut V)} (hL : L ∈ I) (hS : S3Block L) :
    Nat.card (Subgroup.centralizer (autSub L (commV L) : Set (MulAut ↥(commV L)))) = 6 := by
  have hs := suppData_block h hI hL
  obtain ⟨⟨e⟩, -⟩ := (S3Block_iff hs).mp hS
  have hUsq : ∀ v : ↥(commV L), v ^ 2 = 1 := fun v => Subtype.ext (h.sq v)
  have hcard : Nat.card ↥(commV L) = 16 := hS.card_commV h.sq
  exact S3mod_card_centralizer_of_equiv hUsq hcard e (block_hfix h hr hr2 hI hL e)

theorem block_isOmegaFourPlus (h : Setting151c X Tb Xc) {r : ℚ}
    (hr : qhatOf X = (r : WithTop ℚ)) (hr2 : r ≤ 2) {I : Finset (Subgroup (MulAut V))}
    (hI : IsBlocks216 (Jhat X) I) {L : Subgroup (MulAut V)} (hL : L ∈ I) (hS : S3Block L) :
    IsOmegaFourPlus (autSub L (commV L) ⊔
      Subgroup.centralizer (autSub L (commV L) : Set (MulAut ↥(commV L)))) := by
  have hs := suppData_block h hI hL
  obtain ⟨⟨e⟩, -⟩ := (S3Block_iff hs).mp hS
  have hUsq : ∀ v : ↥(commV L), v ^ 2 = 1 := fun v => Subtype.ext (h.sq v)
  have hcard : Nat.card ↥(commV L) = 16 := hS.card_commV h.sq
  exact isOmegaFourPlus_of_S3_centralizer hUsq hcard e (block_hfix h hr hr2 hI hL e)

theorem eq_of_order_three_commute (h : Setting151c X Tb Xc) {I : Finset (Subgroup (MulAut V))}
    (hI : IsBlocks216 (Jhat X) I) {L₁ : Subgroup (MulAut V)} (hL₁ : L₁ ∈ I)
    (hFp : IsPGroup 3 (fittingOf L₁)) {a d : MulAut V} (haX : a ∈ X) (hdX : d ∈ X)
    (ha3 : a ^ 3 = 1) (ha1 : a ≠ 1) (hd3 : d ^ 3 = 1) (hda : d * a = a * d)
    (haL : ∀ l ∈ L₁, a * l = l * a) (hdL : ∀ l ∈ L₁, d * l = l * d) :
    d ∈ Subgroup.zpowers a := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨t, htL, ht1, ht2⟩ := block_exists_involution hI hL₁
  by_cases hd1 : d = 1
  · rw [hd1]
    exact Subgroup.one_mem _
  have hoa : orderOf a = 3 := orderOf_eq_prime ha3 ha1
  have hod : orderOf d = 3 := orderOf_eq_prime hd3 hd1
  have hAp : IsPGroup 3 (Subgroup.zpowers a) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, hoa]
    norm_num
  have hDp : IsPGroup 3 (Subgroup.zpowers d) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, hod]
    norm_num
  have hcommAD : ∀ x ∈ Subgroup.zpowers d, ∀ y ∈ Subgroup.zpowers a, x * y = y * x := by
    intro x hx y hy
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact ((show Commute d a from hda).zpow_zpow m n).eq
  set Q : Subgroup (MulAut V) := Subgroup.zpowers d ⊔ Subgroup.zpowers a with hQ
  have hQp : IsPGroup 3 Q := isPGroup_sup_of_commute151c hDp hAp hcommAD
  have hdQ : d ∈ Q := Subgroup.mem_sup_left (Subgroup.mem_zpowers d)
  have haQ : a ∈ Q := Subgroup.mem_sup_right (Subgroup.mem_zpowers a)
  have hQX : Q ≤ X := sup_le (Subgroup.zpowers_le.mpr hdX) (Subgroup.zpowers_le.mpr haX)
  have hQcent : Q ≤ Subgroup.centralizer (L₁ : Set (MulAut V)) := by
    refine sup_le (Subgroup.zpowers_le.mpr ?_) (Subgroup.zpowers_le.mpr ?_)
    · exact Subgroup.mem_centralizer_iff.mpr fun l hl => (hdL l hl).symm
    · exact Subgroup.mem_centralizer_iff.mpr fun l hl => (haL l hl).symm
  have hQF : ∀ q ∈ Q, ∀ x ∈ fittingOf L₁, x * q = q * x := fun q hq x hx =>
    Subgroup.mem_centralizer_iff.mp (hQcent hq) x (fittingOf_le L₁ hx)
  have hQt : ∀ q ∈ Q, t * q = q * t := fun q hq =>
    Subgroup.mem_centralizer_iff.mp (hQcent hq) t htL
  have hcyc : IsCyclic ↥Q :=
    cyclic_of_commuting_pgroup h hI hL₁ Nat.prime_three (by norm_num) hFp htL ht1 ht2 hQX hQp hQF
      hQt
  have hAle : Subgroup.zpowers a ≤ Q := Subgroup.zpowers_le.mpr haQ
  have hDle : Subgroup.zpowers d ≤ Q := Subgroup.zpowers_le.mpr hdQ
  have hA'card : Nat.card ((Subgroup.zpowers a).subgroupOf Q) = 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAle).toEquiv, Nat.card_zpowers, hoa]
  have hD'card : Nat.card ((Subgroup.zpowers d).subgroupOf Q) = 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDle).toEquiv, Nat.card_zpowers, hod]
  have heq : (Subgroup.zpowers a).subgroupOf Q = (Subgroup.zpowers d).subgroupOf Q :=
    IsCyclic.subgroup_eq_iff_card_eq.mpr (by rw [hA'card, hD'card])
  have hdmem : (⟨d, hdQ⟩ : ↥Q) ∈ (Subgroup.zpowers d).subgroupOf Q :=
    Subgroup.mem_subgroupOf.mpr (Subgroup.mem_zpowers d)
  rw [← heq] at hdmem
  exact Subgroup.mem_subgroupOf.mp hdmem

open Classical in
theorem three_blocks_false (h : Setting151c X Tb Xc) {r : ℚ} (hr : qhatOf X = (r : WithTop ℚ))
    (hr2 : r ≤ 2) {I : Finset (Subgroup (MulAut V))} (hI : IsBlocks216 (Jhat X) I)
    (hS : ∀ L ∈ I, S3Block L) {L₁ L₂ L₃ : Subgroup (MulAut V)} (h1 : L₁ ∈ I) (h2 : L₂ ∈ I)
    (h3 : L₃ ∈ I) (h12 : L₁ ≠ L₂) (h13 : L₁ ≠ L₃) (h23 : L₂ ≠ L₃) : False := by
  have hLX : ∀ L ∈ I, L ≤ X := fun L hL => (block_le_J hI hL).trans (Jhat_le X)
  obtain ⟨a₂, ha₂L, ha₂3, ha₂1⟩ := (hS L₂ h2).exists_order_three
  obtain ⟨a₃, ha₃L, ha₃3, ha₃1⟩ := (hS L₃ h3).exists_order_three
  have hmem := eq_of_order_three_commute h hI h1 (block_fittingOf_pgroup3 h hr hr2 hI h1 (hS L₁ h1))
    (hLX L₂ h2 ha₂L) (hLX L₃ h3 ha₃L) ha₂3 ha₂1 ha₃3
    (hI.comm L₃ h3 L₂ h2 (Ne.symm h23) a₃ ha₃L a₂ ha₂L)
    (fun l hl => hI.comm L₂ h2 L₁ h1 (Ne.symm h12) a₂ ha₂L l hl)
    (fun l hl => hI.comm L₃ h3 L₁ h1 (Ne.symm h13) a₃ ha₃L l hl)
  have hin2 : a₃ ∈ L₂ := (Subgroup.zpowers_le.mpr ha₂L) hmem
  have : a₃ ∈ L₂ ⊓ L₃ := ⟨hin2, ha₃L⟩
  rw [block_inf_eq_bot hI h2 h3 h23] at this
  exact ha₃1 (Subgroup.mem_bot.mp this)

end S3Block151c

end CFSG.Quasithin
