module

public import CFSG.Quasithin.EmptyFaithful.S151cPerm
public import CFSG.Quasithin.Background.D216Six

public section

namespace CFSG.Quasithin

open CFSG.Open

section Orbit151c

variable {V : Type*} [CommGroup V] [Finite V] {X Tb Xc : Subgroup (MulAut V)}

omit [Finite V] in
theorem isElemAbelian2_zpowers151c {s : MulAut V} (hs : s ^ 2 = 1) :
    IsElemAbelian2 (Subgroup.zpowers s) :=
  CFSG.Quasithin.StabLat.isElemAbelian2_zpowers hs

omit [CommGroup V] [Finite V] in
theorem isPGroup_sup_of_commute151c {H : Type*} [Group H] {p : ℕ} {K N : Subgroup H}
    (hK : IsPGroup p K) (hN : IsPGroup p N) (h : ∀ a ∈ K, ∀ b ∈ N, a * b = b * a) :
    IsPGroup p ↥(K ⊔ N) := by
  rintro ⟨x, hx⟩
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_sup_of_commute216 h hx
  obtain ⟨i, hi⟩ := hK ⟨a, ha⟩
  obtain ⟨j, hj⟩ := hN ⟨b, hb⟩
  have hi' : a ^ p ^ i = 1 := congrArg Subtype.val hi
  have hj' : b ^ p ^ j = 1 := congrArg Subtype.val hj
  refine ⟨i + j, Subtype.ext ?_⟩
  show (a * b) ^ p ^ (i + j) = 1
  have hc : Commute a b := h a ha b hb
  rw [hc.mul_pow, pow_add, pow_mul, hi', one_pow, mul_comm (p ^ i), pow_mul, hj', one_pow, one_mul]

open Classical in
theorem block_exists_involution {I : Finset (Subgroup (MulAut V))}
    (hI : IsBlocks216 (Jhat X) I) {L : Subgroup (MulAut V)} (hL : L ∈ I) :
    ∃ t ∈ L, t ≠ 1 ∧ t ^ 2 = 1 := by
  obtain ⟨A, hA⟩ := block_qstar_nonempty hI hL
  obtain ⟨r', -, -, ⟨⟨hA2, -⟩, -⟩, -⟩ := QhatStar_spec hA
  have hAL : A ≤ L := le_of_mem_QhatStar216 hA
  obtain ⟨⟨t, htA⟩, ht1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hA2.ne_bot
  exact ⟨t, hAL htA, fun h => ht1 (Subtype.ext h), hA2.isElemAbelian2.2 t htA⟩

open Classical in
theorem block_fitting_pgroup (h : Setting151c X Tb Xc) {r : ℚ} (hr : qhatOf X = (r : WithTop ℚ))
    (hr2 : r ≤ 2) {I : Finset (Subgroup (MulAut V))} (hI : IsBlocks216 (Jhat X) I)
    {L : Subgroup (MulAut V)} (hL : L ∈ I) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ IsPGroup p (fittingOf L) := by
  have hs := suppData_block h hI hL
  have hH := block_d217hyp h hr hr2 hI hL
  have hD := (block_d217 h hr hr2 hI hL).2
  have hq : ∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧ IsPGroup q (fittingOf (autSub L (commV L))) :=
    fitting_pgroup_of_concl hH hD
  obtain ⟨q, hqp, hq2, hqF⟩ := hq
  refine ⟨q, hqp, hq2, fun g => ?_⟩
  have hgL : (g : MulAut V) ∈ L := fittingOf_le L g.2
  have hsg : (g : MulAut V) ∈ stabSub (commV L) := hs.stab hgL
  have hmem : resHom (commV L) ⟨g, hsg⟩ ∈ fittingOf (autSub L (commV L)) :=
    fittingOf_autSub_le hs.stab (mem_autSub.mpr ⟨⟨g, hsg⟩, g.2, rfl⟩)
  obtain ⟨k, hk⟩ := hqF ⟨_, hmem⟩
  have hk' : (resHom (commV L) ⟨g, hsg⟩) ^ q ^ k = 1 := congrArg Subtype.val hk
  have hpow : (g : MulAut V) ^ q ^ k ∈ L := L.pow_mem hgL _
  have e : resHom (commV L) ⟨(g : MulAut V) ^ q ^ k, hs.stab hpow⟩ =
      (resHom (commV L) ⟨g, hsg⟩) ^ q ^ k := by
    rw [← map_pow]
    rfl
  have h3 : (g : MulAut V) ^ q ^ k = 1 :=
    hs.eq_of_resHom_eq hpow L.one_mem (by rw [e, hk']; exact (map_one (resHom (commV L))).symm)
  exact ⟨k, Subtype.ext h3⟩

omit [CommGroup V] [Finite V] in
theorem exists_orderOf_eq_of_isPGroup_ne_bot {G : Type*} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {P : Subgroup G} (hP : IsPGroup p P) (hne : P ≠ ⊥) :
    ∃ x ∈ P, orderOf x = p := by
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hP
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hne (Subgroup.card_eq_one.mp (by simpa using hn))
  have hdvd : p ∣ Nat.card P := by
    rw [hn]
    exact dvd_pow_self p hn0
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥P) p hdvd
  exact ⟨x, x.2, by rw [Subgroup.orderOf_coe]; exact hx⟩

open Classical in
theorem cyclic_of_commuting_pgroup (h : Setting151c X Tb Xc) {I : Finset (Subgroup (MulAut V))}
    (hI : IsBlocks216 (Jhat X) I) {L : Subgroup (MulAut V)} (hL : L ∈ I) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hFp : IsPGroup p (fittingOf L)) {t : MulAut V} (htL : t ∈ L) (ht1 : t ≠ 1)
    (ht2 : t ^ 2 = 1) {Q : Subgroup (MulAut V)} (hQX : Q ≤ X) (hQp : IsPGroup p Q)
    (hQF : ∀ q ∈ Q, ∀ a ∈ fittingOf L, a * q = q * a) (hQt : ∀ q ∈ Q, t * q = q * t) :
    IsCyclic ↥Q := by
  have : Fact p.Prime := ⟨hp⟩
  have hLX : L ≤ X := (block_le_J hI hL).trans (Jhat_le X)
  have hLsolv : Group.IsSolvable ↥L := by
    have := h.solv
    exact Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hLX)
  have htt : t * t = 1 := by rw [← pow_two]; exact ht2
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have hFcent := centralizer_fittingOf_le_of_solvable hLsolv
  set P₁ := fittingOf L with hP₁def
  have hP₁L : P₁ ≤ L := fittingOf_le L
  set P : Subgroup (MulAut V) := P₁ ⊔ Q with hPdef
  have hPp : IsPGroup p P := isPGroup_sup_of_commute151c hFp hQp (fun a ha q hq => hQF q hq a ha)
  have hPX : P ≤ X := sup_le (hP₁L.trans hLX) hQX
  have hQP : Q ≤ P := le_sup_right
  have hP₁P : P₁ ≤ P := le_sup_left
  have htn : ∀ y ∈ P, t * y * t⁻¹ ∈ P := by
    have hN : P ≤ P.comap (MulAut.conj t).toMonoidHom := by
      refine sup_le ?_ ?_
      · intro y hy
        exact hP₁P (conj_mem_fittingOf htL hy)
      · intro y hy
        show t * y * t⁻¹ ∈ P
        have : t * y * t⁻¹ = y := by
          calc t * y * t⁻¹ = (y * t) * t⁻¹ := by rw [hQt y hy]
            _ = y := by group
        rw [this]
        exact hQP hy
    intro y hy
    exact hN hy
  have hnorm : t ∈ Subgroup.normalizer (P : Set (MulAut V)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨htn y, fun hy => ?_⟩
    have := htn _ hy
    have e : t * (t * y * t⁻¹) * t⁻¹ = y := by
      calc t * (t * y * t⁻¹) * t⁻¹ = (t * t) * y * (t⁻¹ * t⁻¹) := by group
        _ = y := by rw [htt, hti, htt]; group
    rwa [e] at this
  have hAn : ∀ a ∈ Subgroup.zpowers t, ∀ y ∈ P, a * y * a⁻¹ ∈ P := fun a ha y hy =>
    (Subgroup.mem_normalizer_iff.mp ((Subgroup.zpowers_le.mpr hnorm) ha) y).mp hy
  have hnotcomm : ¬ ∀ y ∈ P₁, t * y = y * t := by
    intro hc
    have htF : t ∈ L ⊓ Subgroup.centralizer (P₁ : Set (MulAut V)) :=
      ⟨htL, Subgroup.mem_centralizer_iff.mpr fun y hy => (hc y hy).symm⟩
    have ht' : t ∈ P₁ := hFcent htF
    obtain ⟨k, hk⟩ := hFp ⟨t, ht'⟩
    have hk' : t ^ p ^ k = 1 := congrArg Subtype.val hk
    have hord : orderOf t = 2 := orderOf_eq_prime ht2 ht1
    have h2dvd : 2 ∣ p ^ k := hord ▸ orderOf_dvd_of_pow_eq_one hk'
    have : 2 ∣ p := Nat.prime_two.dvd_of_dvd_pow h2dvd
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp this).symm
  have hfaith : ∀ a ∈ Subgroup.zpowers t, (∀ y ∈ P, a * y = y * a) → a = 1 := by
    intro a ha hcomm
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    have hsq : t ^ (2 : ℤ) = 1 := by rw [zpow_two, ← pow_two]; exact ht2
    obtain ⟨m, hm | hm⟩ := Int.even_or_odd' n
    · rw [hm, zpow_mul, hsq, one_zpow]
    · exfalso
      apply hnotcomm
      intro y hy
      have := hcomm y (hP₁P hy)
      have e : t ^ n = t := by rw [hm, zpow_add, zpow_mul, hsq, one_zpow, one_mul, zpow_one]
      rwa [e] at this
  have hAX : Subgroup.zpowers t ≤ X := Subgroup.zpowers_le.mpr (hLX htL)
  have hcyc := isCyclic_inf_centralizer_of_faithful (X := X) (P := P) (A := Subgroup.zpowers t)
    hp2 hPX hPp (isElemAbelian2_zpowers151c ht2) hAX hAn h.sqtk hfaith (Subgroup.mem_zpowers t) ht1
  have hQZ : Q ≤ P ⊓ Subgroup.centralizer ({t} : Set (MulAut V)) := by
    intro q hq
    refine ⟨hQP hq, Subgroup.mem_centralizer_iff.mpr fun x hx => ?_⟩
    rw [Set.mem_singleton_iff.mp hx]
    exact hQt q hq
  have := hcyc
  have hsub : IsCyclic ↥(Q.subgroupOf (P ⊓ Subgroup.centralizer ({t} : Set (MulAut V)))) :=
    inferInstance
  exact isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hQZ).toMonoidHom
    (Subgroup.subgroupOfEquivOfLe hQZ).surjective

open Classical in
theorem orbit_two_fitting_cyclic (h : Setting151c X Tb Xc) {r : ℚ} (hr : qhatOf X = (r : WithTop ℚ))
    (hr2 : r ≤ 2) {I : Finset (Subgroup (MulAut V))} (hI : IsBlocks216 (Jhat X) I)
    {L L₂ : Subgroup (MulAut V)} (hL : L ∈ I) (hL₂ : L₂ ∈ I) (h12 : L ≠ L₂) {x₂ : MulAut V}
    (e₂ : L₂ = conjBy x₂ L) : IsCyclic ↥(fittingOf L) := by
  obtain ⟨p, hp, hp2, hFp⟩ := block_fitting_pgroup h hr hr2 hI hL
  obtain ⟨t, htL, ht1, ht2⟩ := block_exists_involution hI hL
  have hLX : ∀ L' ∈ I, L' ≤ X := fun L' hL' => (block_le_J hI hL').trans (Jhat_le X)
  set P₁ := fittingOf L with hP₁def
  set P₂ := conjBy x₂ P₁ with hP₂def
  have hP₁L : P₁ ≤ L := fittingOf_le L
  have hP₂L : P₂ ≤ L₂ := e₂ ▸ conjBy_mono hP₁L
  have hP₂p : IsPGroup p P₂ := IsPGroup.map hFp (MulAut.conj x₂).toMonoidHom
  have hcyc : IsCyclic ↥P₂ := by
    refine cyclic_of_commuting_pgroup h hI hL hp hp2 hFp htL ht1 ht2 (hP₂L.trans (hLX L₂ hL₂))
      hP₂p (fun q hq a ha => ?_) (fun q hq => ?_)
    · exact hI.comm L hL L₂ hL₂ h12 a (hP₁L ha) q (hP₂L hq)
    · exact hI.comm L hL L₂ hL₂ h12 t htL q (hP₂L hq)
  have e : ↥P₁ ≃* ↥P₂ := Subgroup.equivMapOfInjective P₁ (MulAut.conj x₂).toMonoidHom
    (MulAut.conj x₂).injective
  exact isCyclic_of_surjective e.symm.toMonoidHom e.symm.surjective

open Classical in
theorem not_three_blocks (h : Setting151c X Tb Xc) {r : ℚ} (hr : qhatOf X = (r : WithTop ℚ))
    (hr2 : r ≤ 2) {I : Finset (Subgroup (MulAut V))} (hI : IsBlocks216 (Jhat X) I)
    {L L₂ L₃ : Subgroup (MulAut V)} (hL : L ∈ I) (hL₂ : L₂ ∈ I) (hL₃ : L₃ ∈ I) (h12 : L ≠ L₂)
    (h13 : L ≠ L₃) (h23 : L₂ ≠ L₃) {x₂ x₃ : MulAut V} (e₂ : L₂ = conjBy x₂ L)
    (e₃ : L₃ = conjBy x₃ L) : False := by
  obtain ⟨p, hp, hp2, hFp⟩ := block_fitting_pgroup h hr hr2 hI hL
  have : Fact p.Prime := ⟨hp⟩
  have hLX : ∀ L' ∈ I, L' ≤ X := fun L' hL' => (block_le_J hI hL').trans (Jhat_le X)
  have hLsolv : Group.IsSolvable ↥L := by
    have := h.solv
    exact Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective (hLX L hL))
  obtain ⟨t, htL, ht1, ht2⟩ := block_exists_involution hI hL
  have htt : t * t = 1 := by rw [← pow_two]; exact ht2
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have hFcent := centralizer_fittingOf_le_of_solvable hLsolv
  set P₁ := fittingOf L with hP₁def
  have hP₁ne : P₁ ≠ ⊥ := by
    intro hbot
    apply hI.ne_bot L hL
    refine (Subgroup.eq_bot_iff_forall _).2 fun g hg => ?_
    have hgc : g ∈ L ⊓ Subgroup.centralizer (P₁ : Set (MulAut V)) := by
      refine ⟨hg, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
      have hy1 : y = 1 := by
        have : y ∈ P₁ := hy
        rw [hbot] at this
        simpa using this
      rw [hy1]
      simp
    have h2 := hFcent hgc
    rw [hbot] at h2
    exact h2
  set P₂ := conjBy x₂ P₁ with hP₂def
  set P₃ := conjBy x₃ P₁ with hP₃def
  have hP₁L : P₁ ≤ L := fittingOf_le L
  have hP₂L : P₂ ≤ L₂ := e₂ ▸ conjBy_mono hP₁L
  have hP₃L : P₃ ≤ L₃ := e₃ ▸ conjBy_mono hP₁L
  have hP₂p : IsPGroup p P₂ := IsPGroup.map hFp (MulAut.conj x₂).toMonoidHom
  have hP₃p : IsPGroup p P₃ := IsPGroup.map hFp (MulAut.conj x₃).toMonoidHom
  have hP₂ne : P₂ ≠ ⊥ := by
    intro hbot
    apply hP₁ne
    have := card_conjBy x₂ P₁
    rw [← hP₂def, hbot, Subgroup.card_bot] at this
    exact Subgroup.card_eq_one.mp this.symm
  have hP₃ne : P₃ ≠ ⊥ := by
    intro hbot
    apply hP₁ne
    have := card_conjBy x₃ P₁
    rw [← hP₃def, hbot, Subgroup.card_bot] at this
    exact Subgroup.card_eq_one.mp this.symm
  have hc12 : ∀ a ∈ P₁, ∀ b ∈ P₂, a * b = b * a := fun a ha b hb =>
    hI.comm L hL L₂ hL₂ h12 a (hP₁L ha) b (hP₂L hb)
  have hc13 : ∀ a ∈ P₁, ∀ b ∈ P₃, a * b = b * a := fun a ha b hb =>
    hI.comm L hL L₃ hL₃ h13 a (hP₁L ha) b (hP₃L hb)
  have hc23 : ∀ a ∈ P₂, ∀ b ∈ P₃, a * b = b * a := fun a ha b hb =>
    hI.comm L₂ hL₂ L₃ hL₃ h23 a (hP₂L ha) b (hP₃L hb)
  have hc123 : ∀ a ∈ P₁ ⊔ P₂, ∀ b ∈ P₃, a * b = b * a := by
    intro a ha b hb
    obtain ⟨a₁, ha₁, a₂, ha₂, rfl⟩ := mem_sup_of_commute216 hc12 ha
    calc a₁ * a₂ * b = a₁ * (a₂ * b) := by group
      _ = a₁ * (b * a₂) := by rw [hc23 a₂ ha₂ b hb]
      _ = (a₁ * b) * a₂ := by group
      _ = (b * a₁) * a₂ := by rw [hc13 a₁ ha₁ b hb]
      _ = b * (a₁ * a₂) := by group
  set P := (P₁ ⊔ P₂) ⊔ P₃ with hPdef
  have hPp : IsPGroup p P :=
    isPGroup_sup_of_commute151c (isPGroup_sup_of_commute151c hFp hP₂p hc12) hP₃p hc123
  have hP₁P : P₁ ≤ P :=
    le_trans (le_sup_left : P₁ ≤ P₁ ⊔ P₂) (le_sup_left : P₁ ⊔ P₂ ≤ (P₁ ⊔ P₂) ⊔ P₃)
  have hP₂P : P₂ ≤ P :=
    le_trans (le_sup_right : P₂ ≤ P₁ ⊔ P₂) (le_sup_left : P₁ ⊔ P₂ ≤ (P₁ ⊔ P₂) ⊔ P₃)
  have hP₃P : P₃ ≤ P := le_sup_right
  have hPX : P ≤ X := sup_le (sup_le ((hP₁L).trans (hLX L hL)) (hP₂L.trans (hLX L₂ hL₂)))
    (hP₃L.trans (hLX L₃ hL₃))
  have htP₁ : ∀ y ∈ P₁, t * y * t⁻¹ ∈ P₁ := fun y hy => conj_mem_fittingOf htL hy
  have htP₂ : ∀ y ∈ P₂, t * y * t⁻¹ = y := fun y hy => by
    have := hI.comm L hL L₂ hL₂ h12 t htL y (hP₂L hy)
    rw [this]; group
  have htP₃ : ∀ y ∈ P₃, t * y * t⁻¹ = y := fun y hy => by
    have := hI.comm L hL L₃ hL₃ h13 t htL y (hP₃L hy)
    rw [this]; group
  have htn : ∀ y ∈ P, t * y * t⁻¹ ∈ P := by
    have hN : P ≤ P.comap (MulAut.conj t).toMonoidHom := by
      refine sup_le (sup_le ?_ ?_) ?_
      · intro y hy
        exact hP₁P (htP₁ y hy)
      · intro y hy
        show t * y * t⁻¹ ∈ P
        rw [htP₂ y hy]
        exact hP₂P hy
      · intro y hy
        show t * y * t⁻¹ ∈ P
        rw [htP₃ y hy]
        exact hP₃P hy
    intro y hy
    exact hN hy
  have hnorm : t ∈ Subgroup.normalizer (P : Set (MulAut V)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨htn y, fun hy => ?_⟩
    have := htn _ hy
    have e : t * (t * y * t⁻¹) * t⁻¹ = y := by
      calc t * (t * y * t⁻¹) * t⁻¹ = (t * t) * y * (t⁻¹ * t⁻¹) := by group
        _ = y := by rw [htt, hti, htt]; group
    rwa [e] at this
  have hAn : ∀ a ∈ Subgroup.zpowers t, ∀ y ∈ P, a * y * a⁻¹ ∈ P := fun a ha y hy =>
    (Subgroup.mem_normalizer_iff.mp ((Subgroup.zpowers_le.mpr hnorm) ha) y).mp hy
  have hnotcomm : ¬ ∀ y ∈ P₁, t * y = y * t := by
    intro hc
    have htF : t ∈ L ⊓ Subgroup.centralizer (P₁ : Set (MulAut V)) :=
      ⟨htL, Subgroup.mem_centralizer_iff.mpr fun y hy => (hc y hy).symm⟩
    have ht' : t ∈ P₁ := hFcent htF
    obtain ⟨k, hk⟩ := hFp ⟨t, ht'⟩
    have hk' : t ^ p ^ k = 1 := congrArg Subtype.val hk
    have hord : orderOf t = 2 := orderOf_eq_prime ht2 ht1
    have h2dvd : 2 ∣ p ^ k := hord ▸ orderOf_dvd_of_pow_eq_one hk'
    have : 2 ∣ p := Nat.prime_two.dvd_of_dvd_pow h2dvd
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp this).symm
  have hfaith : ∀ a ∈ Subgroup.zpowers t, (∀ y ∈ P, a * y = y * a) → a = 1 := by
    intro a ha hcomm
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    have hsq : t ^ (2 : ℤ) = 1 := by rw [zpow_two, ← pow_two]; exact ht2
    obtain ⟨m, hm | hm⟩ := Int.even_or_odd' n
    · rw [hm, zpow_mul, hsq, one_zpow]
    · exfalso
      apply hnotcomm
      intro y hy
      have hyP : y ∈ P := hP₁P hy
      have := hcomm y hyP
      have e : t ^ n = t := by rw [hm, zpow_add, zpow_mul, hsq, one_zpow, one_mul, zpow_one]
      rwa [e] at this
  have hAX : Subgroup.zpowers t ≤ X := Subgroup.zpowers_le.mpr (hLX L hL htL)
  have hcyc := isCyclic_inf_centralizer_of_faithful (X := X) (P := P) (A := Subgroup.zpowers t)
    hp2 hPX hPp (isElemAbelian2_zpowers151c ht2) hAX hAn h.sqtk hfaith (Subgroup.mem_zpowers t) ht1
  obtain ⟨y₂, hy₂, ho₂⟩ := exists_orderOf_eq_of_isPGroup_ne_bot hP₂p hP₂ne
  obtain ⟨y₃, hy₃, ho₃⟩ := exists_orderOf_eq_of_isPGroup_ne_bot hP₃p hP₃ne
  set Z : Subgroup (MulAut V) := P ⊓ Subgroup.centralizer ({t} : Set (MulAut V)) with hZ
  have hcentr : ∀ y ∈ P₂ ⊔ P₃, y ∈ Subgroup.centralizer ({t} : Set (MulAut V)) := by
    intro y hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_sup_of_commute216 hc23 hy
    have e1 : t * a * t⁻¹ = a := htP₂ a ha
    have e2 : t * b * t⁻¹ = b := htP₃ b hb
    have h1 : t * a = a * t := by
      calc t * a = (t * a * t⁻¹) * t := by group
        _ = a * t := by rw [e1]
    have h2 : t * b = b * t := by
      calc t * b = (t * b * t⁻¹) * t := by group
        _ = b * t := by rw [e2]
    show (a * b) * t = t * (a * b)
    calc a * b * t = a * (b * t) := by group
      _ = a * (t * b) := by rw [h2]
      _ = (a * t) * b := by group
      _ = (t * a) * b := by rw [h1]
      _ = t * (a * b) := by group
  have hy₂Z : y₂ ∈ Z := ⟨hP₂P hy₂, hcentr y₂ ((le_sup_left : P₂ ≤ P₂ ⊔ P₃) hy₂)⟩
  have hy₃Z : y₃ ∈ Z := ⟨hP₃P hy₃, hcentr y₃ ((le_sup_right : P₃ ≤ P₂ ⊔ P₃) hy₃)⟩
  have hle₂ : Subgroup.zpowers y₂ ≤ Z := Subgroup.zpowers_le.mpr hy₂Z
  have hle₃ : Subgroup.zpowers y₃ ≤ Z := Subgroup.zpowers_le.mpr hy₃Z
  have hHeq : (Subgroup.zpowers y₂).subgroupOf Z = (Subgroup.zpowers y₃).subgroupOf Z := by
    have := hcyc
    rw [IsCyclic.subgroup_eq_iff_card_eq]
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle₂).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle₃).toEquiv, Nat.card_zpowers,
      Nat.card_zpowers, ho₂, ho₃]
  have hy₃mem : y₃ ∈ Subgroup.zpowers y₂ := by
    have h1 : (⟨y₃, hy₃Z⟩ : ↥Z) ∈ (Subgroup.zpowers y₃).subgroupOf Z :=
      Subgroup.mem_subgroupOf.mpr (Subgroup.mem_zpowers y₃)
    rw [← hHeq] at h1
    exact Subgroup.mem_subgroupOf.mp h1
  have hy₃L₂ : y₃ ∈ L₂ := (Subgroup.zpowers_le.mpr (hP₂L hy₂)) hy₃mem
  have hmem : y₃ ∈ L₂ ⊓ L₃ := ⟨hy₃L₂, hP₃L hy₃⟩
  rw [block_inf_eq_bot hI hL₂ hL₃ h23, Subgroup.mem_bot] at hmem
  rw [hmem, orderOf_one] at ho₃
  exact hp.one_lt.ne' ho₃.symm

open Classical in
theorem orbit_le_two (h : Setting151c X Tb Xc) {r : ℚ} (hr : qhatOf X = (r : WithTop ℚ))
    (hr2 : r ≤ 2) {I : Finset (Subgroup (MulAut V))} (hI : IsBlocks216 (Jhat X) I)
    {L : Subgroup (MulAut V)} (hL : L ∈ I) (hnot : ∃ x ∈ X, conjBy x L ≠ L) :
    ∃ L₂ ∈ I, L₂ ≠ L ∧ (∃ x ∈ X, conjBy x L = L₂) ∧
      ∀ x ∈ X, conjBy x L = L ∨ conjBy x L = L₂ := by
  obtain ⟨x₂, hx₂, hne⟩ := hnot
  have hL₂ : conjBy x₂ L ∈ I := block_conj_mem h hr hr2 hI hL hx₂
  refine ⟨conjBy x₂ L, hL₂, hne, ⟨x₂, hx₂, rfl⟩, fun x hx => ?_⟩
  by_contra hcon
  push Not at hcon
  have hLx : conjBy x L ∈ I := block_conj_mem h hr hr2 hI hL hx
  exact not_three_blocks h hr hr2 hI hL hL₂ hLx (Ne.symm hne) (Ne.symm hcon.1)
    (Ne.symm hcon.2) rfl rfl

open Classical in
theorem exists_swap_of_orbit_two (h : Setting151c X Tb Xc) {L L₂ : Subgroup (MulAut V)}
    (hne : L₂ ≠ L) {x₂ : MulAut V} (hx₂ : x₂ ∈ X) (e₂ : conjBy x₂ L = L₂)
    (horb : ∀ x ∈ X, conjBy x L = L ∨ conjBy x L = L₂) : ∃ t ∈ Tb, conjBy t L = L₂ := by
  by_contra hno
  push Not at hno
  have hTb : ∀ t ∈ Tb, conjBy t L = L := fun t ht =>
    (horb t (h.syl.1 ht)).resolve_right (hno t ht)
  let N : Subgroup (MulAut V) :=
    { carrier := {x | x ∈ X ∧ conjBy x L = L}
      one_mem' := ⟨X.one_mem, conjBy_one L⟩
      mul_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        refine ⟨X.mul_mem ha hb, ?_⟩
        rw [← conjBy_conjBy, hb', ha']
      inv_mem' := by
        rintro a ⟨ha, ha'⟩
        refine ⟨X.inv_mem ha, ?_⟩
        calc conjBy a⁻¹ L = conjBy a⁻¹ (conjBy a L) := by rw [ha']
          _ = L := by rw [conjBy_conjBy, inv_mul_cancel, conjBy_one] }
  have hNX : N ≤ X := fun x hx => hx.1
  have hindex : (N.subgroupOf X).index = 2 := by
    rw [Subgroup.index_eq_two_iff]
    refine ⟨⟨x₂, hx₂⟩, fun b => ?_⟩
    have hbX : (b : MulAut V) ∈ X := b.2
    have hbx₂ : (b : MulAut V) * x₂ ∈ X := X.mul_mem hbX hx₂
    have hb₂ : conjBy (b : MulAut V) L₂ = conjBy ((b : MulAut V) * x₂) L := by
      rw [← e₂, conjBy_conjBy]
    show Xor (b * ⟨x₂, hx₂⟩ ∈ N.subgroupOf X) (b ∈ N.subgroupOf X)
    simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul]
    rcases horb b hbX with h1 | h1
    ·
      have hbN : (b : MulAut V) ∈ N := ⟨hbX, h1⟩
      have hnot : (b : MulAut V) * x₂ ∉ N := by
        rintro ⟨-, h2⟩
        apply hne
        have h3 : conjBy (b : MulAut V) L₂ = conjBy (b : MulAut V) L := by rw [hb₂, h2, h1]
        exact conjBy_injective _ h3
      exact Or.inr ⟨hbN, hnot⟩
    · have hbN : (b : MulAut V) ∉ N := fun hb => hne (by rw [← h1, hb.2])
      have hbxN : (b : MulAut V) * x₂ ∈ N := by
        refine ⟨hbx₂, ?_⟩
        rcases horb _ hbx₂ with h3 | h3
        · exact h3
        · exfalso
          apply hne
          have h4 : conjBy (b : MulAut V) L₂ = conjBy (b : MulAut V) L := by rw [hb₂, h3, h1]
          exact conjBy_injective _ h4
      exact Or.inl ⟨hbxN, hbN⟩
  have hTbN : Tb ≤ N := fun t ht => ⟨h.syl.1 ht, hTb t ht⟩
  have h2 : (N.subgroupOf X).index ∣ (Tb.subgroupOf X).index := by
    apply Subgroup.index_dvd_of_le
    intro x hx
    exact Subgroup.mem_subgroupOf.mpr (hTbN (Subgroup.mem_subgroupOf.mp hx))
  rw [hindex] at h2
  exact h.syl.2.2 h2

end Orbit151c

end CFSG.Quasithin
