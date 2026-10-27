module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDeltaGlue
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenWitt
public import CFSG.GH74.GLS.IVK.Proofs2.Lemma44bOrd
public import CFSG.RankThree.PartOne.S11d.OutAbstract

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

section Orders

private theorem s16b_card_isL3 {Y : Type} [Group Y] (h : UC22.IsL3 Y 1) : Nat.card Y = 168 := by
  rcases h with ⟨-, h⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
  · obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
    have h1 := CFSG.GH74.GLS.IVK.Proofs2.Lemma44bOrd.card_statedProj_statedSL_three_mul (F := K)
    rw [hK] at h1
    norm_num at h1
    rw [Nat.card_congr e.toEquiv]
    omega
  all_goals exact absurd h0 (by norm_num)

theorem IsE64L3.card_eq {X : Type} [Group X] (h : IsE64L3 X) : Nat.card X = 10752 := by
  obtain ⟨N, hN, ⟨e⟩, hL3⟩ := h
  have hq : Nat.card (X ⧸ N) = 168 := s16b_card_isL3 hL3
  have hn : Nat.card N = 64 := by
    rw [Nat.card_congr e.toEquiv]
    simp
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup N, hq, hn]

end Orders

section Points

variable {W : Type*} [CommGroup W]

private theorem s16b_mem_ptCent {X : Subgroup (MulAut W)} {h : MulAut W} {w : W} :
    h ∈ ptCent X w ↔ h ∈ X ∧ h w = w := by
  unfold ptCent
  rw [Subgroup.mem_inf, MulAction.mem_stabilizer_iff]
  rfl

private theorem s16b_mem_fixV_zpowers {s : MulAut W} {x : W} :
    x ∈ fixV (Subgroup.zpowers s) ↔ s x = x := by
  refine ⟨fun h => h s (Subgroup.mem_zpowers s), fun h y hy => ?_⟩
  have hs : s ∈ MulAction.stabilizer (MulAut W) x := h
  exact Subgroup.zpowers_le.2 hs hy

private theorem s16b_card_ptCent_apply {X : Subgroup (MulAut W)} {g : MulAut W} (hg : g ∈ X)
    (x : W) : Nat.card ↥(ptCent X (g x)) = Nat.card ↥(ptCent X x) := by
  refine Nat.card_congr
    { toFun := fun h => ⟨g⁻¹ * h.1 * g, ?_⟩
      invFun := fun h => ⟨g * h.1 * g⁻¹, ?_⟩
      left_inv := fun h => Subtype.ext ?_
      right_inv := fun h => Subtype.ext ?_ }
  · obtain ⟨h1, h2⟩ := s16b_mem_ptCent.1 h.2
    refine s16b_mem_ptCent.2 ⟨X.mul_mem (X.mul_mem (X.inv_mem hg) h1) hg, ?_⟩
    show g⁻¹ (h.1 (g x)) = x
    rw [h2]
    exact MulAut.inv_apply_self _ _ _
  · obtain ⟨h1, h2⟩ := s16b_mem_ptCent.1 h.2
    refine s16b_mem_ptCent.2 ⟨X.mul_mem (X.mul_mem hg h1) (X.inv_mem hg), ?_⟩
    show g (h.1 (g⁻¹ (g x))) = g x
    rw [MulAut.inv_apply_self]
    exact congrArg g h2
  · show g * (g⁻¹ * h.1 * g) * g⁻¹ = h.1
    group
  · show g⁻¹ * (g * h.1 * g⁻¹) * g = h.1
    group

end Points

section Transvection

variable {W : Type*} [CommGroup W] [Finite W]

private theorem s16b_exists_comm (s : MulAut W) : ∃ φ : W →* W, ∀ x, φ x = s x * x⁻¹ :=
  ⟨MonoidHom.mk' (fun x => s x * x⁻¹) fun a b => by
    rw [map_mul, mul_inv]
    exact mul_mul_mul_comm _ _ _ _, fun _ => rfl⟩

private theorem s16b_transvection (hsq : ∀ x : W, x * x = 1) {s : MulAut W} (hs : s * s = 1)
    (hs1 : s ≠ 1) (hlt : Nat.card W < 4 * Nat.card ↥(fixV (Subgroup.zpowers s))) :
    ∃ u : W, u ≠ 1 ∧ s u = u ∧ (∀ x : W, s x = x ∨ s x = u * x) ∧ ∃ x : W, s x ≠ x := by
  classical
  obtain ⟨φ, hφ⟩ := s16b_exists_comm s
  have hker : φ.ker = fixV (Subgroup.zpowers s) := by
    ext x
    rw [MonoidHom.mem_ker, hφ, mul_inv_eq_one, s16b_mem_fixV_zpowers]
  have hcard := Subgroup.card_ker_mul_card_range φ
  rw [hker] at hcard
  have hpos : 0 < Nat.card ↥(fixV (Subgroup.zpowers s)) := Nat.card_pos
  have hr4 : Nat.card φ.range < 4 := by
    by_contra hge
    push Not at hge
    have : 4 * Nat.card ↥(fixV (Subgroup.zpowers s)) ≤ Nat.card W := by
      rw [← hcard]
      calc 4 * Nat.card ↥(fixV (Subgroup.zpowers s))
          ≤ Nat.card φ.range * Nat.card ↥(fixV (Subgroup.zpowers s)) :=
            Nat.mul_le_mul_right _ hge
        _ = _ := mul_comm _ _
    omega
  have hW2 : IsPGroup 2 W := fun x => ⟨1, by rw [pow_one, sq]; exact hsq x⟩
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2)).mp hW2
  have hdvd : Nat.card φ.range ∣ 2 ^ n := hn ▸ Subgroup.card_range_dvd φ
  obtain ⟨j, hj, hrj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  have hj1 : j ≤ 1 := by
    by_contra hj2
    push Not at hj2
    have : 2 ^ 2 ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hj2
    omega
  have hsx : ∃ x : W, s x ≠ x := by
    by_contra hcon
    push Not at hcon
    exact hs1 (MulEquiv.ext fun x => by simpa using hcon x)
  interval_cases j
  ·
    exfalso
    have h1 : Nat.card φ.range = 1 := by simpa using hrj
    have hbot : φ.range = ⊥ := Subgroup.card_eq_one.1 h1
    obtain ⟨x, hx⟩ := hsx
    have : φ x ∈ φ.range := ⟨x, rfl⟩
    rw [hbot, Subgroup.mem_bot, hφ, mul_inv_eq_one] at this
    exact hx this
  · have h2 : Nat.card φ.range = 2 := by simpa using hrj
    obtain ⟨y, hy1, huniq⟩ := (Nat.card_eq_two_iff' (1 : φ.range)).1 h2
    have hu1 : (y : W) ≠ 1 := fun h => hy1 (Subtype.ext h)
    have hdich : ∀ x : W, φ x = 1 ∨ φ x = (y : W) := by
      intro x
      by_cases hx : φ x = 1
      · exact Or.inl hx
      · refine Or.inr ?_
        have := huniq ⟨φ x, x, rfl⟩ (fun h => hx (congrArg Subtype.val h))
        exact congrArg Subtype.val this
    have hdich' : ∀ x : W, s x = x ∨ s x = (y : W) * x := by
      intro x
      rcases hdich x with h | h
      · rw [hφ, mul_inv_eq_one] at h
        exact Or.inl h
      · refine Or.inr ?_
        rw [hφ, mul_inv_eq_iff_eq_mul] at h
        rw [h, mul_comm]
    refine ⟨y, hu1, ?_, hdich', hsx⟩
    obtain ⟨x0, hx0⟩ := y.2
    have hsx0 : s x0 = (y : W) * x0 := by
      rw [hφ, mul_inv_eq_iff_eq_mul] at hx0
      rw [hx0, mul_comm]
    have e1 : s (s x0) = x0 := by simpa [MulAut.mul_apply] using congrArg (fun f => f x0) hs
    rw [hsx0, map_mul, hsx0] at e1
    have e2 : s (y : W) * (y : W) * x0 = 1 * x0 := by rw [mul_assoc, e1, one_mul]
    have e3 : s (y : W) * (y : W) = 1 := mul_right_cancel e2
    calc s (y : W) = (y : W)⁻¹ := eq_inv_of_mul_eq_one_left e3
      _ = (y : W) := inv_eq_of_mul_eq_one_right (hsq _)

end Transvection

section Orthogonal

private theorem s16b_quadInvariant {W : Type} [CommGroup W] {Q : W → ZMod 2}
    {X : Subgroup (MulAut W)}
    (hE : ∀ w : W, w ≠ 1 → Q w = 0 → IsE64L3 ↥(ptCent X w))
    (hG : ∀ w : W, Q w ≠ 0 → CFSG.Quasithin.IsG2Two ↥(ptCent X w)) :
    ∀ g ∈ X, ∀ x : W, Q (g x) = Q x := by
  intro g hg x
  by_cases hx : x = 1
  · rw [hx, map_one]
  have hgx : g x ≠ 1 := fun h => hx (g.injective (by rw [h, map_one]))
  by_contra hne
  have hcases : (Q x = 0 ∧ Q (g x) ≠ 0) ∨ (Q x ≠ 0 ∧ Q (g x) = 0) := by
    revert hne
    generalize Q x = a
    generalize Q (g x) = b
    revert a b
    decide
  have hcard := s16b_card_ptCent_apply hg x
  rcases hcases with ⟨h0, h1⟩ | ⟨h0, h1⟩
  · have e1 := (hE x hx h0).card_eq
    have e2 := (hG (g x) h1).1
    omega
  · have e1 := (hG x h0).1
    have e2 := (hE (g x) hgx h1).card_eq
    omega

variable {W : Type*} [CommGroup W] [Finite W]

private theorem s16b_no_transvection (hsq : ∀ x : W, x * x = 1) {Q : W → ZMod 2}
    (hQ : IsNondegQuadF2 Q) {X : Subgroup (MulAut W)} (hXQ : ∀ g ∈ X, ∀ x : W, Q (g x) = Q x)
    (hcen : ∀ u : W, Q u ≠ 0 → ∀ g ∈ ptCent X u, (∀ h ∈ ptCent X u, h * g = g * h) → g = 1)
    {s : MulAut W} (hsX : s ∈ X) (hs : s * s = 1) (hs1 : s ≠ 1)
    (hlt : Nat.card W < 4 * Nat.card ↥(fixV (Subgroup.zpowers s))) : False := by
  obtain ⟨u, hu1, hsu, hdich, x0, hx0⟩ := s16b_transvection hsq hs hs1 hlt
  have hsub : ∀ a b : ZMod 2, a - b - a = b := by decide
  have hpol : ∀ g : MulAut W, (∀ x : W, Q (g x) = Q x) →
      ∀ x y : W, polarQ Q (g x) (g y) = polarQ Q x y := by
    intro g hg x y
    unfold polarQ
    rw [← map_mul, hg, hg, hg]
  have hmoved : ∀ x : W, s x ≠ x → polarQ Q u x = Q u := by
    intro x hx
    have hsxu : s x = u * x := (hdich x).resolve_left hx
    have h1 := hXQ s hsX x
    rw [hsxu] at h1
    unfold polarQ
    rw [h1]
    exact hsub (Q x) (Q u)
  have hfixed : ∀ x : W, s x = x → polarQ Q u x = 0 := by
    intro x hx
    have hxx0 : s (x * x0) ≠ x * x0 := by
      rw [map_mul, hx]
      intro h
      exact hx0 (mul_left_cancel h)
    have h1 := hmoved _ hxx0
    rw [hQ.1.2 u x x0, hmoved x0 hx0] at h1
    simpa using h1
  have hQu : Q u ≠ 0 := by
    intro h0
    obtain ⟨y, hy⟩ := hQ.2 u hu1
    apply hy
    by_cases hy' : s y = y
    · exact hfixed y hy'
    · exact (hmoved y hy').trans h0
  have hiff : ∀ z : W, s z = z ↔ polarQ Q u z = 0 := by
    intro z
    refine ⟨hfixed z, fun hz => ?_⟩
    by_contra hne
    have := hmoved z hne
    rw [hz] at this
    exact hQu this.symm
  have hcomm : ∀ g ∈ ptCent X u, g * s = s * g := by
    intro g hg
    obtain ⟨hgX, hgu⟩ := s16b_mem_ptCent.1 hg
    have hB : ∀ z : W, polarQ Q u (g z) = polarQ Q u z := by
      intro z
      have := hpol g (hXQ g hgX) u z
      rwa [hgu] at this
    refine MulEquiv.ext fun z => ?_
    show g (s z) = s (g z)
    by_cases hz : s z = z
    · have hz' : s (g z) = g z := (hiff _).2 (by rw [hB]; exact (hiff z).1 hz)
      rw [hz, hz']
    · have hz' : s (g z) ≠ g z := fun h => hz ((hiff z).2 (by
        have h' := (hiff (g z)).1 h
        rwa [hB] at h'))
      rw [(hdich z).resolve_left hz, (hdich (g z)).resolve_left hz', map_mul, hgu]
  exact hs1 (hcen u hQu s (s16b_mem_ptCent.2 ⟨hsX, hsu⟩) fun h hh => hcomm h hh)

end Orthogonal

section MParam

variable {W : Type*} [CommGroup W] [Finite W]

private theorem s16b_le_rkIdx_of_card_le {k m : ℕ} (hW : Nat.card W = 2 ^ k) (S : Subgroup W)
    (hS : Nat.card S * 2 ^ m ≤ 2 ^ k) : m ≤ rkIdx S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 := Subgroup.index_mul_card S
  rw [hW] at h1
  have hdvd : S.index ∣ 2 ^ k := Dvd.intro _ h1
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have hpos : 0 < Nat.card S := Nat.card_pos
  have h2 : 2 ^ m ≤ 2 ^ j := by
    rw [hj] at h1
    have : Nat.card S * 2 ^ m ≤ Nat.card S * 2 ^ j := by
      calc Nat.card S * 2 ^ m ≤ 2 ^ k := hS
        _ = 2 ^ j * Nat.card S := h1.symm
        _ = Nat.card S * 2 ^ j := mul_comm _ _
    exact Nat.le_of_mul_le_mul_left this hpos
  unfold rkIdx
  rw [hj, padicValNat.prime_pow]
  exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h2

theorem two_le_mParam_of_orthogonal (hsq : ∀ x : W, x * x = 1) (h2 : 2 ≤ rk W) {Q : W → ZMod 2}
    (hQ : IsNondegQuadF2 Q) {X : Subgroup (MulAut W)} (hXQ : ∀ g ∈ X, ∀ x : W, Q (g x) = Q x)
    (hcen : ∀ u : W, Q u ≠ 0 → ∀ g ∈ ptCent X u, (∀ h ∈ ptCent X u, h * g = g * h) → g = 1) :
    2 ≤ E3.mParam X := by
  classical
  have hW2 : IsPGroup 2 W := fun x => ⟨1, by rw [pow_one, sq]; exact hsq x⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2)).mp hW2
  unfold E3.mParam
  split_ifs with hev
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := ↥X) 2 (even_iff_two_dvd.mp hev)
    refine le_csInf ⟨_, (t : MulAut W), t.2, (Subgroup.orderOf_coe t).trans ht, rfl⟩ ?_
    rintro n ⟨s, hsX, hs2, rfl⟩
    have hss : s * s = 1 := by
      have h := pow_orderOf_eq_one s
      rw [hs2, sq] at h
      exact h
    have hs1 : s ≠ 1 := fun h => by rw [h, orderOf_one] at hs2; omega
    refine s16b_le_rkIdx_of_card_le hk _ ?_
    by_contra hnot
    push Not at hnot
    refine s16b_no_transvection hsq hQ hXQ hcen hsX hss hs1 ?_
    rw [hk]
    linarith
  · exact h2

end MParam

section Finite

variable {G : Type} [Group G] [Finite G]

theorem R16_28_m_of_R16_26 (D : Data G) (h26 : R16_26 D) : R16_28_m D := by
  intro V₀ V L hV hS h8
  have hH : Hyp125 D V₀ V := hS.setting.hyp16.hyp125
  obtain ⟨⟨Q, hQ, hQinv⟩, hall⟩ := h26 V₀ V L hV hS h8
  obtain ⟨hE, hG⟩ := hall Q hQ hQinv
  have hXQ := s16b_quadInvariant hE fun w hw => (hG w hw).1
  have hsq : ∀ w : Vtil V₀ V hV, w * w = 1 := fun w => by
    simpa [sq] using s15_Infra_vtil_sq_eq_one V₀ V hV w
  have hcen : ∀ u : Vtil V₀ V hV, Q u ≠ 0 → ∀ g ∈ ptCent (Mbar D.M V₀ V hV) u,
      (∀ h ∈ ptCent (Mbar D.M V₀ V hV) u, h * g = g * h) → g = 1 := by
    intro u hu g hg hcomm
    have hmem : (⟨g, hg⟩ : ↥(ptCent (Mbar D.M V₀ V hV) u)) ∈
        Subgroup.center ↥(ptCent (Mbar D.M V₀ V hV) u) := by
      rw [Subgroup.mem_center_iff]
      intro h
      exact Subtype.ext (hcomm h.1 h.2)
    rw [(hG u hu).1.2.1, Subgroup.mem_bot] at hmem
    exact congrArg Subtype.val hmem
  have hV₀V : V₀ ≤ V := hH.pairFacts.le
  have hrk : rk ↥(⊤ : Subgroup (Vtil V₀ V hV)) + mSub V₀ = mSub V :=
    rk_top_vtil_add_mSub V₀ V hV hV₀V
  have hV₁V : v1Sub D.M V₀ V hV L ≤ V := s15_Infra_v1Sub_le hH hV
  have hrk1 : rk ↥(⊤ : Subgroup (vStar D.M V₀ V hV L)) + mSub (v1Sub D.M V₀ V hV L) = mSub V :=
    rk_top_vtil_add_mSub (v1Sub D.M V₀ V hV L) V hV hV₁V
  have hmono : mSub V₀ ≤ mSub (v1Sub D.M V₀ V hV L) :=
    rk_mono (s15_Infra_le_v1Sub D.M V₀ V hV L)
  have h8rk : rk ↥(⊤ : Subgroup (vStar D.M V₀ V hV L)) = 8 := h8.2.1
  have htop : rk (Vtil V₀ V hV) = rk ↥(⊤ : Subgroup (Vtil V₀ V hV)) := by
    unfold rk
    rw [Subgroup.card_top]
  have h2rk : 2 ≤ rk (Vtil V₀ V hV) := by omega
  exact (hH.pairFacts.mBarGT_iff_lt_mBar 1).2
    (two_le_mParam_of_orthogonal hsq h2rk hQ.1 hXQ hcen)

end Finite

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
