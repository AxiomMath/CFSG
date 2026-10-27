module

public import CFSG.Quasithin.Vol2.Ch8Sec2L829CS5Br
public import CFSG.Quasithin.Vol2.Ch8Sec2L829CS5In
public import CFSG.Quasithin.Vol2.Ch8Sec2L829CS5Lift

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.E3 CFSG.Quasithin.H


section U3Br

variable {G : Type} [Group G] [Finite G]

theorem conjSub_centerSub_of_mem_normalizer_cs5 {Y : Type} [Group Y] {S : Subgroup Y} {b : Y}
    (hb : b ∈ Subgroup.normalizer (S : Set Y)) : B6.conjSub b (centerSub S) = centerSub S := by
  ext z
  rw [B6.mem_conjSub]
  constructor
  · intro h
    have := conj_mem_centerSub_cs5 hb h
    simpa [mul_assoc] using this
  · intro h
    have := conj_mem_centerSub_cs5 (Subgroup.inv_mem _ hb) h
    simpa [mul_assoc] using this

theorem RankOneSyl.center_eq_bot {Y : Type} [Group Y] {X S : Subgroup Y} {q : ℕ}
    (hR : RankOneSyl X S q) : Subgroup.center ↥X = ⊥ := by
  have hSX : S ≤ X := hR.le
  have h := hR.core ((Subgroup.center ↥X).map X.subtype) (fun z hz => by
      obtain ⟨z', hz', rfl⟩ := hz
      refine ⟨z'.2, ?_⟩
      show (z' : Y) ∈ Subgroup.normalizer (S : Set Y)
      refine Subgroup.mem_normalizer_iff.mpr (fun s => ?_)
      constructor
      · intro hs
        have := Subgroup.mem_center_iff.mp hz' ⟨s, hSX hs⟩
        have h2 : (z' : Y) * s = s * z' := congrArg Subtype.val this.symm
        have : (z' : Y) * s * (z' : Y)⁻¹ = s := by rw [h2]; group
        rw [this]; exact hs
      · intro hs
        have hsX : s ∈ X := by
          have := X.mul_mem (X.mul_mem (X.inv_mem z'.2) (hSX hs)) z'.2
          simpa [mul_assoc] using this
        have := Subgroup.mem_center_iff.mp hz' ⟨s, hsX⟩
        have h2 : (z' : Y) * s = s * z' := congrArg Subtype.val this.symm
        have h3 : (z' : Y) * s * (z' : Y)⁻¹ = s := by rw [h2]; group
        rwa [h3] at hs) (fun x hx n hn => by
      obtain ⟨n', hn', rfl⟩ := hn
      have := Subgroup.mem_center_iff.mp hn' ⟨x, hx⟩
      have h2 : (n' : Y) * x = x * n' := congrArg Subtype.val this.symm
      have h3 : x * (n' : Y) * x⁻¹ = n' := by rw [← h2]; group
      show x * (n' : Y) * x⁻¹ ∈ (Subgroup.center ↥X).map X.subtype
      rw [h3]
      exact ⟨n', hn', rfl⟩)
  rw [Subgroup.eq_bot_iff_forall]
  intro z hz
  have : (z : Y) ∈ (Subgroup.center ↥X).map X.subtype := ⟨z, hz, rfl⟩
  rw [h] at this
  exact Subtype.ext (by simpa using this)

@[expose] def RankOneU3 : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (X S : Subgroup Y) (n : ℕ), 2 ≤ n → IsPSU 3 2 n ↥X →
    IsSylowTwoOf S X → RankOneSyl X S (2 ^ n)

theorem u3_branch_cs5 (hfam : RankOneU3) (hU34 : U34Facts)
    {H T M K V : Subgroup G} {h : G} {n : ℕ}
    (hT : IsSylowTwoOf T H) (hTM : T ≤ M) (hHK : H = K ⊔ T)
    (hTK : T ≤ Subgroup.normalizer (K : Set G)) (hVT : V ≤ T) (hVe : IsElemAbelian 2 V)
    (hP7 : H ⊓ M ≤ Subgroup.normalizer (V : Set G)) (hh : h ∈ H)
    (hker : kerIn (M ⊓ ch82I V h) (ch82I V h) = pCoreOf 2 (ch82I V h))
    (hI : IsPSL 2 2 2 (E2.StarQuot (M ⊓ ch82I V h) (ch82I V h)))
    (hn : 2 ≤ n) (hKs : IsPSU 3 2 n ↥(E2.star (H ⊓ M) H K))
    (hBor : E2.IsBorelIn (E2.star (H ⊓ M) H K) (E2.star (H ⊓ M) H ((H ⊓ M) ⊓ K))) :
    ∃ x : G, x ∈ (H ⊓ M) ⊓ K ∧ (∃ a : ℕ, x ^ 5 ^ a = 1) ∧ x ≠ 1 ∧
      ∀ i ∈ ch82I V h, x * i * x⁻¹ * i⁻¹ ∈ kerIn (H ⊓ M) H := by
  have hTH : T ≤ H := hT.1
  have hVH : V ≤ H := hVT.trans hTH
  have hIH : ch82I V h ≤ H := ch82I_le_829 hVH hh
  have hKH : K ≤ H := hHK ▸ le_sup_left
  have hT2 : IsPGroup 2 T := hT.2.1
  haveI hXn : (E2.star (H ⊓ M) H K).Normal := star_normal_cs5 hHK hTK
  have hYX : IsPGroup 2 (E2.StarQuot (H ⊓ M) H ⧸ E2.star (H ⊓ M) H K) :=
    isPGroup_starQuot_quotient_cs5 hT2 hHK hTK
  have hO2 : ∀ N : Subgroup (E2.StarQuot (H ⊓ M) H), N.Normal → IsPGroup 2 N → N = ⊥ :=
    fun N hN hN2 => by
      haveI := hN
      exact normal_twoGroup_starQuot_eq_bot_cs5 hT hTM N hN2
  obtain ⟨S, hS, hB⟩ := hBor
  have hR := hfam _ (E2.star (H ⊓ M) H K) S n hn hKs hS
  have hZX : Subgroup.center ↥(E2.star (H ⊓ M) H K) = ⊥ := hR.center_eq_bot
  have hC := eq_one_of_centralizes_normal_cs5 hZX hYX hO2
  have hBsol : Group.IsSolvable ↥(E2.star (H ⊓ M) H K ⊓
      Subgroup.normalizer (S : Set (E2.StarQuot (H ⊓ M) H))) := by
    have := C41Pf.isSolvable_of_isBorelIn
      (X := E2.star (H ⊓ M) H K) (B := E2.star (H ⊓ M) H ((H ⊓ M) ⊓ K)) ⟨S, hS, hB⟩
    rwa [hB] at this
  set E := E2.star (H ⊓ M) H V with hEdef
  have hE : IsElemAbelian 2 E := isElemAbelian_star_cs5 hVH hVe
  have hEB : E2.star (H ⊓ M) H K ⊓ Subgroup.normalizer (S : Set (E2.StarQuot (H ⊓ M) H)) ≤
      Subgroup.normalizer (E : Set (E2.StarQuot (H ⊓ M) H)) := by
    rw [← hB]
    exact star_le_normalizer_star_cs5 (inf_le_left.trans inf_le_left) hVH (inf_le_left.trans hP7)
  set hs : E2.StarQuot (H ⊓ M) H := QuotientGroup.mk (⟨h, hh⟩ : ↥H) with hsdef
  have hIstar : E2.star (H ⊓ M) H (ch82I V h) = E ⊔ B6.conjSub hs E := by
    unfold ch82I
    obtain ⟨hconjH, hconj⟩ := star_conjSub_cs5 (M := H ⊓ M) hh hVH
    rw [star_sup_cs5 hVH hconjH, hconj]
  have hNnorm : ∀ i ∈ E2.star (H ⊓ M) H (ch82I V h),
      ∀ n ∈ E2.star (H ⊓ M) H (pCoreOf 2 (ch82I V h)),
        i * n * i⁻¹ ∈ E2.star (H ⊓ M) H (pCoreOf 2 (ch82I V h)) := by
    intro i hi n hn
    obtain ⟨a, ha, rfl⟩ := mem_star_cs5.mp hi
    obtain ⟨p, hp, rfl⟩ := mem_star_cs5.mp hn
    refine mem_star_cs5.mpr ⟨a * p * a⁻¹, ?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.mp
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (ch82I V h) ha) (p : G)).mp hp
    · simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
  have hN2 : IsPGroup 2 (E2.star (H ⊓ M) H (pCoreOf 2 (ch82I V h))) :=
    isPGroup_star_cs5 (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)
  have hQ60 : Nat.card (E2.StarQuot (M ⊓ ch82I V h) (ch82I V h)) = 60 :=
    CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_two_two hI
  have hm := (card_star_quot_le_cs5 (H := H) (M := M) hIH hker).trans hQ60.le
  have hns := not_isSolvable_star_cs5 (H := H) hIH hker (not_isSolvable_of_isPSL_two_two_two_829 hI)
  obtain ⟨hZE, hne, hWX, hqq, hcardW⟩ := rk1_main_of_eq hR hC hYX hBsol hE hEB hIstar hNnorm hN2
    hm hns
  have hn2 : n = 2 := by
    by_contra hne2
    have h3 : 3 ≤ n := by omega
    have h8 : 8 ≤ 2 ^ n := calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h3
    have := hqq.trans hcardW
    nlinarith
  subst hn2
  have hSX : S ≤ E2.star (H ⊓ M) H K := hR.le
  have hEX : E ≤ E2.star (H ⊓ M) H K := (hU34 _ (E2.star (H ⊓ M) H K) S hKs hC hS).1 E hE hEB hZE
  have hSnormE : S ≤ Subgroup.normalizer (E : Set (E2.StarQuot (H ⊓ M) H)) := by
    intro s hs'
    have : s ∈ E2.star (H ⊓ M) H K ⊓ Subgroup.normalizer (S : Set (E2.StarQuot (H ⊓ M) H)) :=
      ⟨hSX hs', Subgroup.le_normalizer hs'⟩
    exact hEB this
  have hES : E ≤ S := by
    have hP2 : IsPGroup 2 (S ⊔ E : Subgroup (E2.StarQuot (H ⊓ M) H)) :=
      IsPGroup.to_sup_of_normal_right' hR.isPGroup (isPGroup_of_sq_eq_one_cs5 fun x hx => hE.2 x hx)
        hSnormE
    exact le_sup_right.trans
      (le_of_isPGroup_of_sylow_le_cs5 hR.sylow hP2 le_sup_left (sup_le hSX hEX))
  have hEZ : E = centerSub S := by
    refine le_antisymm (fun x hx => hR.omega1 x (hES hx) ?_) hZE
    have := hE.2 x hx
    simpa [pow_two] using this
  have hIW : E2.star (H ⊓ M) H (ch82I V h) = centerSub S ⊔ B6.conjSub hs (centerSub S) := by
    rw [hIstar, hEZ]
  have hsyl := isSylowTwoOf_conjSub_cs5 hR.sylow hs
  obtain ⟨g, hgX, hgeq⟩ := exists_conj_eq_of_isSylowTwoOf_cs5 hR.sylow hsyl
  have hgN : g ∉ Subgroup.normalizer (S : Set (E2.StarQuot (H ⊓ M) H)) := by
    intro hgN
    apply hne
    rw [hgeq]
    exact B6.conjSub_eq_self hgN
  have hZeq : B6.conjSub hs (centerSub S) = B6.conjSub g (centerSub S) := by
    have hb : g⁻¹ * hs ∈ Subgroup.normalizer (S : Set (E2.StarQuot (H ⊓ M) H)) := by
      refine Subgroup.mem_normalizer_iff_map_conj_eq.mpr ?_
      have : B6.conjSub (g⁻¹ * hs) S = S := by
        rw [B6.conjSub_mul, hgeq, ← B6.conjSub_mul]
        simp [B6.conjSub_one]
      exact this
    have hcZ : B6.conjSub (g⁻¹ * hs) (centerSub S) = centerSub S :=
      conjSub_centerSub_of_mem_normalizer_cs5 hb
    calc B6.conjSub hs (centerSub S) = B6.conjSub (g * (g⁻¹ * hs)) (centerSub S) := by
          rw [mul_inv_cancel_left]
      _ = B6.conjSub g (B6.conjSub (g⁻¹ * hs) (centerSub S)) := B6.conjSub_mul _ _ _
      _ = B6.conjSub g (centerSub S) := by rw [hcZ]
  obtain ⟨hC5, hCB⟩ := (hU34 _ (E2.star (H ⊓ M) H K) S hKs hC hS).2 g hgX hgN
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  set Wg : Subgroup (E2.StarQuot (H ⊓ M) H) := centerSub S ⊔ B6.conjSub g (centerSub S) with hWg
  obtain ⟨c, hc5⟩ := exists_prime_orderOf_dvd_card'
    (G := ↥(E2.star (H ⊓ M) H K ⊓ Subgroup.centralizer (Wg : Set (E2.StarQuot (H ⊓ M) H)))) 5 hC5
  have hc5' : orderOf (c : E2.StarQuot (H ⊓ M) H) = 5 := by
    rw [Subgroup.orderOf_coe]
    exact hc5
  have hc1 : (c : E2.StarQuot (H ⊓ M) H) ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hc5'
    omega
  have hcpow : (c : E2.StarQuot (H ⊓ M) H) ^ 5 ^ 1 = 1 := by
    rw [pow_one, ← hc5']
    exact pow_orderOf_eq_one _
  have hcMKs : (c : E2.StarQuot (H ⊓ M) H) ∈ E2.star (H ⊓ M) H ((H ⊓ M) ⊓ K) := by
    rw [hB]
    exact ⟨c.2.1, hCB c.2⟩
  obtain ⟨x, hxA, hx1, ⟨a5, hx5⟩, m, hxm⟩ :=
    exists_five_lift_star_cs5 (inf_le_left.trans inf_le_left) hcMKs hc1 hcpow
  refine ⟨x, hxA, ⟨a5, hx5⟩, hx1, fun i hi => ?_⟩
  have hxH : x ∈ H := (inf_le_left.trans inf_le_left : (H ⊓ M) ⊓ K ≤ H) hxA
  refine commutator_mem_kerIn_of_star_commute_cs5 hxH (hIH hi) ?_
  rw [hxm]
  have hiW : (QuotientGroup.mk (⟨i, hIH hi⟩ : ↥H) : E2.StarQuot (H ⊓ M) H) ∈ Wg := by
    rw [hWg, ← hZeq, ← hIW]
    exact mem_star_cs5.mpr ⟨⟨i, hIH hi⟩, hi, rfl⟩
  have hcomm : (c : E2.StarQuot (H ⊓ M) H) *
      (QuotientGroup.mk (⟨i, hIH hi⟩ : ↥H) : E2.StarQuot (H ⊓ M) H) =
      (QuotientGroup.mk (⟨i, hIH hi⟩ : ↥H) : E2.StarQuot (H ⊓ M) H) * c :=
    (Subgroup.mem_centralizer_iff.mp c.2.2 _ hiW).symm
  exact (Commute.pow_left (hcomm : Commute _ _) m).eq

end U3Br

end CFSG.Quasithin.H13
