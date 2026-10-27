module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3OddNc
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1G42Lift
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenGlue3
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenRankTwoInv

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.WeakClosure81
  CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem s16c13bc_le_oddBar {M V₀ V : Subgroup G} (hV : IsElemAbelian 2 V)
    {N : Subgroup (MulAut (Vtil V₀ V hV))} (hNM : N ≤ Mbar M V₀ V hV)
    (hNn : ∀ m ∈ Mbar M V₀ V hV, ∀ x ∈ N, m * x * m⁻¹ ∈ N) (hodd : Odd (Nat.card N)) :
    N ≤ oddBar M V₀ V hV := by
  have hnorm : (N.subgroupOf (Mbar M V₀ V hV)).Normal := by
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer hNM).2 fun m hm => ?_
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨fun hx => ?_, fun hx => ?_⟩
    · simpa using hNn m hm x hx
    · have := hNn m⁻¹ ((Mbar M V₀ V hV).inv_mem hm) _ hx
      simpa [mul_assoc] using this
  exact le_sSup ⟨hNM, hnorm, Nat.coprime_two_left.2 hodd⟩

theorem s16c13bc_insp_of_stable (D : Data G) {V : Subgroup G} (h : Hyp125 D ⊥ V) {p : ℕ}
    (hp : p ∈ D.sig) {Ut : Subgroup (Vtil ⊥ V h.isElemAbelian)} (hU1 : Ut ≠ ⊥)
    (hUfix : Ut ≤ fixV (barSub ⊥ V h.isElemAbelian (E3.wClos V D.k D.T)))
    {Xb : Subgroup (MulAut (Vtil ⊥ V h.isElemAbelian))}
    (hXb : Xb ≤ Mbar D.M ⊥ V h.isElemAbelian) (hXp : IsPGroup p Xb) (hXc : ¬ IsCyclic Xb)
    (hstab : StableUnder Xb Ut) : Insp1613U D V := by
  haveI : Fact p.Prime := ⟨(D.sig_prime p hp).1⟩
  have hV := h.isElemAbelian
  have hP := h.pairFacts
  have hMst : D.M ≤ stabTil ⊥ V := le_stabTil hP.le_normalizer hP.le_normalizer₀
  have hWT : E3.wClos V D.k D.T ≤ D.T := E3.wClos_le_of_forall fun A hA => hA.1
  have hWst : E3.wClos V D.k D.T ≤ stabTil ⊥ V := hWT.trans (D.sylowM.le.trans hMst)
  obtain ⟨X, hXpre, hXp', hXc'⟩ := s16c167_exists_pSub_lift hV hXb hXp hXc
  refine ⟨preTil ⊥ V hV Ut, ?_, ?_, p, hp, X, ?_, hXp', hXc'⟩
  · intro h0
    apply hU1
    have h1 := imgTil_preTil ⊥ V hV Ut
    rw [h0] at h1
    rw [← h1, eq_bot_iff]
    intro q hq
    obtain ⟨x, hx, rfl⟩ := (mem_imgTil ⊥ V hV ⊥ q).1 hq
    rw [Subgroup.mem_bot] at hx ⊢
    have : x = 1 := IntMod.val_injective (by simpa using hx)
    rw [this, map_one]
  · refine le_inf (preTil_le ⊥ V hV Ut) ?_
    intro u hu
    have h1 : u ∈ preTil ⊥ V hV (fixV (barSub ⊥ V hV (E3.wClos V D.k D.T))) :=
      s15_LP_preTil_mono hV hUfix hu
    have h2 := (s15_Glue_mem_preTil_fixV_iff ⊥ V (E3.wClos V D.k D.T) hV hWst
      (preTil_le ⊥ V hV Ut hu)).1 h1
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    have h3 := h2 e he
    rw [Subgroup.mem_bot, mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h3
    exact h3
  · refine le_inf (hXpre.trans inf_le_left) ?_
    intro x hx
    obtain ⟨-, hxst, hxXb⟩ := (mem_preBarSub D.M ⊥ V hV Xb).1 (hXpre hx)
    refine s16c1G_mem_normalizer_of_forall_actTil_mem_imgTil hV (preTil_le ⊥ V hV Ut) hxst ?_
    rw [imgTil_preTil]
    exact fun w hw => hstab _ hxXb w hw

private theorem s16c13bc_mem_stabSub_closure {W : Type} [CommGroup W] {S : Set W} {g : MulAut W}
    (h1 : ∀ s ∈ S, g s ∈ Subgroup.closure S) (h2 : ∀ s ∈ S, g⁻¹ s ∈ Subgroup.closure S) :
    g ∈ stabSub (Subgroup.closure S) := by
  have key : ∀ k : MulAut W, (∀ s ∈ S, k s ∈ Subgroup.closure S) →
      ∀ u ∈ Subgroup.closure S, k u ∈ Subgroup.closure S := by
    intro k hk u hu
    have hle : Subgroup.closure S ≤ (Subgroup.closure S).comap k.toMonoidHom := by
      rw [Subgroup.closure_le]
      exact fun s hs => hk s hs
    exact hle hu
  intro u
  refine ⟨fun hu => ?_, key g h1 u⟩
  have := key g⁻¹ h2 _ hu
  simpa using this

theorem s16c13bc_insp_of_central_pair (D : Data G) {V : Subgroup G} (h : Hyp125 D ⊥ V)
    (hcomm : ⁅oddBar D.M ⊥ V h.isElemAbelian,
      barSub ⊥ V h.isElemAbelian (E3.wClos V D.k D.T)⁆ = ⊥)
    {p : ℕ} (hp : p ∈ D.sig) {z ψ : MulAut (Vtil ⊥ V h.isElemAbelian)}
    (hz : z ∈ oddBar D.M ⊥ V h.isElemAbelian) (hzo : orderOf z = p)
    (hψ : ψ ∈ Mbar D.M ⊥ V h.isElemAbelian) (hψo : orderOf ψ = p) (hψz : ψ * z = z * ψ)
    (hψn : ψ ∉ Subgroup.zpowers z) {n : Vtil ⊥ V h.isElemAbelian} (hn1 : n ≠ 1)
    (hnfix : n ∈ fixV (barSub ⊥ V h.isElemAbelian (E3.wClos V D.k D.T)))
    (hψfix : ψ n = n) : Insp1613U D V := by
  haveI : Fact p.Prime := ⟨(D.sig_prime p hp).1⟩
  have hV := h.isElemAbelian
  set S : Set (Vtil ⊥ V hV) :=
    (fun g : MulAut (Vtil ⊥ V hV) => g n) '' (Subgroup.zpowers z : Set _) with hS
  set Ut : Subgroup (Vtil ⊥ V hV) := Subgroup.closure S with hUt
  have hnS : n ∈ S := ⟨1, Subgroup.one_mem _, rfl⟩
  have hU1 : Ut ≠ ⊥ := by
    intro h0
    have : n ∈ Ut := Subgroup.subset_closure hnS
    rw [h0, Subgroup.mem_bot] at this
    exact hn1 this
  have hUfix : Ut ≤ fixV (barSub ⊥ V hV (E3.wClos V D.k D.T)) := by
    rw [hUt, Subgroup.closure_le]
    rintro _ ⟨g, hg, rfl⟩
    rw [SetLike.mem_coe, mem_fixV]
    intro w hw
    have hgO : g ∈ oddBar D.M ⊥ V hV := (Subgroup.zpowers_le.2 hz) hg
    have hc := Subgroup.commutator_mem_commutator hgO hw
    rw [hcomm, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hc
    calc w (g n) = (w * g) n := rfl
      _ = (g * w) n := by rw [← hc]
      _ = g (w n) := rfl
      _ = g n := by rw [mem_fixV.1 hnfix w hw]
  have hz2 : z ^ p = 1 := hzo ▸ pow_orderOf_eq_one z
  have hψ2 : ψ ^ p = 1 := hψo ▸ pow_orderOf_eq_one ψ
  set Xb : Subgroup (MulAut (Vtil ⊥ V hV)) := Subgroup.closure {z, ψ} with hXb
  have hs : ∀ a ∈ ({z, ψ} : Set (MulAut (Vtil ⊥ V hV))),
      ∀ b ∈ ({z, ψ} : Set (MulAut (Vtil ⊥ V hV))), a * b = b * a := by
    intro a ha b hb
    rcases ha with rfl | ha <;> rcases hb with rfl | hb
    · rfl
    · rw [Set.mem_singleton_iff] at hb
      subst hb
      exact hψz.symm
    · rw [Set.mem_singleton_iff] at ha
      subst ha
      exact hψz
    · rw [Set.mem_singleton_iff] at ha hb
      subst ha
      subst hb
      rfl
  have hcl1 : ∀ x ∈ Xb, ∀ b ∈ ({z, ψ} : Set (MulAut (Vtil ⊥ V hV))), x * b = b * x := by
    intro x hx b hb
    have hle : Xb ≤ Subgroup.centralizer {b} := by
      rw [hXb, Subgroup.closure_le]
      intro a ha
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      exact hs a ha b hb
    exact Subgroup.mem_centralizer_singleton_iff.1 (hle hx)
  have hcl : ∀ x ∈ Xb, ∀ y ∈ Xb, x * y = y * x := by
    intro x hx y hy
    have hle : Xb ≤ Subgroup.centralizer {x} := by
      rw [hXb, Subgroup.closure_le]
      intro a ha
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      exact (hcl1 x hx a ha).symm
    exact (Subgroup.mem_centralizer_singleton_iff.1 (hle hy)).symm
  have hpow : ∀ x ∈ Xb, x ^ p = 1 := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem a ha =>
      rcases ha with rfl | ha
      · exact hz2
      · rw [Set.mem_singleton_iff] at ha
        subst ha
        exact hψ2
    | one => exact one_pow p
    | mul a b ha hb iha ihb =>
      have hc : Commute a b := hcl a ha b hb
      rw [hc.mul_pow, iha, ihb, one_mul]
    | inv a ha iha => rw [inv_pow, iha, inv_one]
  have hzX : z ∈ Xb := Subgroup.subset_closure (Set.mem_insert _ _)
  have hψX : ψ ∈ Xb := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  have hXM : Xb ≤ Mbar D.M ⊥ V hV := by
    rw [hXb, Subgroup.closure_le]
    intro a ha
    rcases ha with rfl | ha
    · exact relPPrimeCore_le _ hz
    · rw [Set.mem_singleton_iff] at ha
      subst ha
      exact hψ
  have hXp : IsPGroup p Xb := by
    rw [IsPGroup.iff_orderOf]
    intro g
    have hg : (g : MulAut (Vtil ⊥ V hV)) ^ p = 1 := hpow g g.2
    have hg' : g ^ p = 1 := Subtype.ext hg
    have hd : orderOf g ∣ p := orderOf_dvd_of_pow_eq_one hg'
    rcases (Nat.dvd_prime (Fact.out : p.Prime)).1 hd with h1 | h1
    · exact ⟨0, by simpa using h1⟩
    · exact ⟨1, by simpa using h1⟩
  have hXc : ¬ IsCyclic Xb := by
    intro hcyc
    obtain ⟨g, hg⟩ := hcyc.exists_generator
    have hgp : g ^ p = 1 := Subtype.ext (hpow g g.2)
    have hcard : Nat.card Xb ∣ p := by
      rw [← orderOf_eq_card_of_forall_mem_zpowers hg]
      exact orderOf_dvd_of_pow_eq_one hgp
    have hzle : Subgroup.zpowers z ≤ Xb := Subgroup.zpowers_le.2 hzX
    have hzcard : Nat.card (Subgroup.zpowers z) = p := by
      rw [Nat.card_zpowers, hzo]
    have hle : Nat.card Xb ≤ Nat.card (Subgroup.zpowers z) := by
      rw [hzcard]
      exact Nat.le_of_dvd (Fact.out : p.Prime).pos hcard
    exact hψn ((Subgroup.eq_of_le_of_card_ge hzle hle) ▸ hψX)
  have hzstab : z ∈ stabSub Ut := by
    refine s16c13bc_mem_stabSub_closure ?_ ?_
    · rintro _ ⟨g, hg, rfl⟩
      refine Subgroup.subset_closure ⟨z * g, Subgroup.mul_mem _ (Subgroup.mem_zpowers z) hg, rfl⟩
    · rintro _ ⟨g, hg, rfl⟩
      refine Subgroup.subset_closure
        ⟨z⁻¹ * g, Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mem_zpowers z)) hg, rfl⟩
  have hψstab : ψ ∈ stabSub Ut := by
    refine centSub_le_stabSub Ut ?_
    rw [mem_centSub]
    intro u hu
    have hle : Ut ≤ fixV (Subgroup.zpowers ψ) := by
      rw [hUt, Subgroup.closure_le]
      rintro _ ⟨g, hg, rfl⟩
      rw [SetLike.mem_coe, mem_fixV_zpowers_iff]
      have hψg : ψ * g = g * ψ := by
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
        exact (Commute.zpow_right (show Commute ψ z from hψz) k).eq
      show ψ (g n) = g n
      calc ψ (g n) = (ψ * g) n := rfl
        _ = (g * ψ) n := by rw [hψg]
        _ = g (ψ n) := rfl
        _ = g n := by rw [hψfix]
    exact mem_fixV_zpowers_iff.1 (hle hu)
  have hstab : StableUnder Xb Ut := by
    have hle : Xb ≤ stabSub Ut := by
      rw [hXb, Subgroup.closure_le]
      intro a ha
      rcases ha with rfl | ha
      · exact hzstab
      · rw [Set.mem_singleton_iff] at ha
        subst ha
        exact hψstab
    exact fun x hx u hu => ((hle hx) u).2 hu
  exact s16c13bc_insp_of_stable D h hp hU1 hUfix hXM hXp hXc hstab

theorem s16c13bc_insp_of_normal_prime (D : Data G) {V : Subgroup G} (h : Hyp125 D ⊥ V)
    (hcomm : ⁅oddBar D.M ⊥ V h.isElemAbelian,
      barSub ⊥ V h.isElemAbelian (E3.wClos V D.k D.T)⁆ = ⊥)
    {p : ℕ} (hp : p ∈ D.sig) {Z : Subgroup (MulAut (Vtil ⊥ V h.isElemAbelian))}
    (hZM : Z ≤ Mbar D.M ⊥ V h.isElemAbelian) (hZc : Nat.card Z = p)
    (hZn : ∀ m ∈ Mbar D.M ⊥ V h.isElemAbelian, ∀ x ∈ Z, m * x * m⁻¹ ∈ Z)
    {n : Vtil ⊥ V h.isElemAbelian} (hn1 : n ≠ 1)
    (hnfix : n ∈ fixV (barSub ⊥ V h.isElemAbelian (E3.wClos V D.k D.T)))
    {ψ : MulAut (Vtil ⊥ V h.isElemAbelian)} (hψ : ψ ∈ Mbar D.M ⊥ V h.isElemAbelian)
    (hψo : orderOf ψ = p) (hψZ : ψ ∉ Z) (hψn : ψ n = n) : Insp1613U D V := by
  have hpp : p.Prime := (D.sig_prime p hp).1
  have hp2 : p ≠ 2 := (D.sig_prime p hp).2
  haveI : Fact p.Prime := ⟨hpp⟩
  have hV := h.isElemAbelian
  haveI : IsCyclic Z := isCyclic_of_prime_card hZc
  obtain ⟨z₀, hz₀⟩ := IsCyclic.exists_generator (α := Z)
  have hzo : orderOf (z₀ : MulAut (Vtil ⊥ V hV)) = p := by
    rw [Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hz₀]
    exact hZc
  have hZodd : Odd (Nat.card Z) := hZc ▸ hpp.odd_of_ne_two hp2
  have hZO : Z ≤ oddBar D.M ⊥ V hV := s16c13bc_le_oddBar hV hZM hZn hZodd
  have hψN : ψ ∈ Subgroup.normalizer (Z : Set (MulAut (Vtil ⊥ V hV))) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨fun hx => hZn ψ hψ x hx, fun hx => ?_⟩
    have := hZn ψ⁻¹ ((Mbar D.M ⊥ V hV).inv_mem hψ) _ hx
    simpa [mul_assoc] using this
  have hψp : ψ ^ p = 1 := hψo ▸ pow_orderOf_eq_one ψ
  have hψC :=
    CFSG.LocalAnalysis.RankThreeUC.AGL81C.mem_centralizer_of_mem_normalizer_of_card_eq_prime
      hpp hZc hψp hψN
  have hψz : ψ * (z₀ : MulAut (Vtil ⊥ V hV)) = (z₀ : MulAut (Vtil ⊥ V hV)) * ψ :=
    (Subgroup.mem_centralizer_iff.1 hψC _ z₀.2).symm
  refine s16c13bc_insp_of_central_pair D h hcomm hp (hZO z₀.2) hzo hψ hψo hψz ?_ hn1 hnfix hψn
  intro hmem
  exact hψZ ((Subgroup.zpowers_le.2 z₀.2) hmem)

theorem s16c13bc_exists_fixed_in (D : Data G) {V : Subgroup G} (h : Hyp125 D ⊥ V)
    {S : Subgroup (Vtil ⊥ V h.isElemAbelian)} (hS : S ≠ ⊥)
    (hst : barSub ⊥ V h.isElemAbelian (E3.wClos V D.k D.T) ≤ stabSub S) :
    ∃ n ∈ S, n ≠ 1 ∧ n ∈ fixV (barSub ⊥ V h.isElemAbelian (E3.wClos V D.k D.T)) := by
  have hV := h.isElemAbelian
  have hP := h.pairFacts
  have hMst : D.M ≤ stabTil ⊥ V := le_stabTil hP.le_normalizer hP.le_normalizer₀
  have hWT : E3.wClos V D.k D.T ≤ D.T := E3.wClos_le_of_forall fun A hA => hA.1
  have hWst : E3.wClos V D.k D.T ≤ stabTil ⊥ V := hWT.trans (D.sylowM.le.trans hMst)
  have hP2 : IsPGroup 2 (E3.wClos V D.k D.T) := D.sylowM.isPGroup.to_le hWT
  have hU2 : IsPGroup 2 (preTil ⊥ V hV S) := hV.isPGroup.to_le (preTil_le ⊥ V hV S)
  have hUne : preTil ⊥ V hV S ≠ ⊥ := by
    intro h0
    apply hS
    have h1 := imgTil_preTil ⊥ V hV S
    rw [h0] at h1
    rw [← h1, eq_bot_iff]
    intro q hq
    obtain ⟨x, hx, rfl⟩ := (mem_imgTil ⊥ V hV ⊥ q).1 hq
    rw [Subgroup.mem_bot] at hx ⊢
    have : x = 1 := IntMod.val_injective (by simpa using hx)
    rw [this, map_one]
  have hPnorm : E3.wClos V D.k D.T ≤ normalizer (preTil ⊥ V hV S : Set G) := by
    intro x hx
    refine s16c1G_mem_normalizer_of_forall_actTil_mem_imgTil hV (preTil_le ⊥ V hV S) (hWst hx) ?_
    rw [imgTil_preTil]
    intro w hw
    exact (hst (actTil_mem_barSub ⊥ V hV hx (hWst hx)) w).2 hw
  obtain ⟨u, huU, hu1, hucomm⟩ := s15_Glue3_exists_fixed hP2 hU2 hUne hPnorm
  have huV : u ∈ V := preTil_le ⊥ V hV S huU
  obtain ⟨x, hxu, hxS⟩ := (mem_preTil ⊥ V hV S).1 huU
  refine ⟨mkTil ⊥ V hV x, hxS, ?_, ?_⟩
  · intro h1
    apply hu1
    have h2 : x ∈ modNull ⊥ V hV := (QuotientGroup.eq_one_iff (N := modNull ⊥ V hV) x).1 h1
    rw [mem_modNull, Subgroup.mem_bot] at h2
    rw [← hxu]
    exact h2
  · have hfix := (s15_Glue_mem_preTil_fixV_iff ⊥ V (E3.wClos V D.k D.T) hV hWst huV).2
      (fun e he => by rw [Subgroup.mem_bot, hucomm e he]; group)
    obtain ⟨x', hx'u, hx'⟩ := (mem_preTil ⊥ V hV _).1 hfix
    have : x' = x := IntMod.val_injective (hx'u.trans hxu.symm)
    exact this ▸ hx'

theorem s16c13bc_exists_fixed (D : Data G) {V : Subgroup G} (h : Hyp125 D ⊥ V) :
    ∃ n : Vtil ⊥ V h.isElemAbelian, n ≠ 1 ∧
      n ∈ fixV (barSub ⊥ V h.isElemAbelian (E3.wClos V D.k D.T)) := by
  have hV := h.isElemAbelian
  have htop : (⊤ : Subgroup (Vtil ⊥ V hV)) ≠ ⊥ := by
    intro h0
    apply h.pairFacts.ne_bot
    have h1 := preTil_top ⊥ V hV
    rw [h0, preTil_bot, inf_bot_eq] at h1
    exact h1.symm
  obtain ⟨n, -, hn1, hn⟩ := s16c13bc_exists_fixed_in D h htop (S := ⊤)
    (fun g _ u => by simp)
  exact ⟨n, hn1, hn⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
