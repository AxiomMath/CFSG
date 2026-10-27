module

public import CFSG.LocalAnalysis.StandardType.GGF4N2Alignment
public import CFSG.LocalAnalysis.StandardType.GGNbrLineCover
public import CFSG.LocalAnalysis.StandardType.GGSecFiveRestGen
import CFSG.GroupTheory.SupCommute
import CFSG.LocalAnalysis.StandardType.GGF4N2CoreBound
import CFSG.LocalAnalysis.StandardType.GGF4N2Rank
import CFSG.LocalAnalysis.StandardType.GGSecFiveBFixLine

public section

namespace CFSG.StandardType

open CFSG.Open CFSG.Assembly

section Lines

variable {G : Type} [Group G]

theorem zpowers_pow_eq_of_pow_five {e : G} (he : e ^ 5 = 1) {m m' : ℕ} (hmm : m * m' % 5 = 1) :
    Subgroup.zpowers (e ^ m) = Subgroup.zpowers e := by
  apply le_antisymm
  · exact Subgroup.zpowers_le.mpr (Subgroup.pow_mem _ (Subgroup.mem_zpowers e) m)
  · rw [Subgroup.zpowers_le]
    refine Subgroup.mem_zpowers_iff.mpr ⟨(m' : ℤ), ?_⟩
    rw [zpow_natCast, ← pow_mul, ← Nat.mod_add_div (m * m') 5, hmm, pow_add, pow_mul, he, one_pow,
      mul_one, pow_one]

theorem zpowers_eq_of_mem_sup_of_orderOf_five {y u e : G} (hy : orderOf y = 5) (hu : orderOf u = 5)
    (hyu : Commute y u) (he : e ∈ Subgroup.zpowers y ⊔ Subgroup.zpowers u) (he1 : e ≠ 1) :
    Subgroup.zpowers e = Subgroup.zpowers u ∨
      ∃ k : ℕ, k < 5 ∧ Subgroup.zpowers e = Subgroup.zpowers (y * u ^ k) := by
  have hy5 : y ^ 5 = 1 := hy ▸ pow_orderOf_eq_one y
  have hu5 : u ^ 5 = 1 := hu ▸ pow_orderOf_eq_one u
  have hpow : ∀ {w : G}, orderOf w = 5 → ∀ a ∈ Subgroup.zpowers w, ∃ n : ℕ, w ^ n = a := by
    intro w hw a ha
    have hfin : IsOfFinOrder w := orderOf_pos_iff.mp (by rw [hw]; norm_num)
    exact (Submonoid.mem_powers_iff _ _).mp (hfin.mem_powers_iff_mem_zpowers.mpr ha)
  have hcomm : ∀ a ∈ Subgroup.zpowers y, ∀ b ∈ Subgroup.zpowers u, Commute a b := by
    intro a ha b hb
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    exact hyu.zpow_zpow i j
  obtain ⟨a, ha, b, hb, rfl⟩ := (CFSG.mem_sup_of_commute hcomm).mp he
  obtain ⟨i, rfl⟩ := hpow hy _ ha
  obtain ⟨j, rfl⟩ := hpow hu _ hb
  have hi : y ^ i = y ^ (i % 5) := by rw [← hy, pow_mod_orderOf]
  have hj : u ^ j = u ^ (j % 5) := by rw [← hu, pow_mod_orderOf]
  rw [hi, hj] at he1 ⊢
  have hi5 : i % 5 < 5 := Nat.mod_lt _ (by norm_num)
  have hj5 : j % 5 < 5 := Nat.mod_lt _ (by norm_num)
  generalize i % 5 = i' at hi5 he1 ⊢
  generalize j % 5 = j' at hj5 he1 ⊢
  have key : ∀ m m' : ℕ, m * m' % 5 = 1 → ∀ i : ℕ, i * m % 5 = 1 → ∀ j : ℕ,
      Subgroup.zpowers (y ^ i * u ^ j) = Subgroup.zpowers (y * u ^ (j * m % 5)) := by
    intro m m' hmm i him j
    have he5 : (y ^ i * u ^ j) ^ 5 = 1 := by
      rw [(hyu.pow_pow i j).mul_pow, ← pow_mul, ← pow_mul, mul_comm i 5, mul_comm j 5, pow_mul,
        pow_mul, hy5, hu5, one_pow, one_pow, one_mul]
    rw [← zpowers_pow_eq_of_pow_five he5 hmm, (hyu.pow_pow i j).mul_pow, ← pow_mul, ← pow_mul,
      ← pow_mod_orderOf y (i * m), hy, him, pow_one, ← pow_mod_orderOf u (j * m), hu]
  have hk : ∀ j : ℕ, j * 1 % 5 < 5 ∧ j * 3 % 5 < 5 ∧ j * 2 % 5 < 5 ∧ j * 4 % 5 < 5 :=
    fun j => ⟨Nat.mod_lt _ (by norm_num), Nat.mod_lt _ (by norm_num), Nat.mod_lt _ (by norm_num),
      Nat.mod_lt _ (by norm_num)⟩
  interval_cases i'
  · left
    rw [pow_zero, one_mul] at he1 ⊢
    interval_cases j'
    · exact absurd (pow_zero u) he1
    · rw [pow_one]
    · exact zpowers_pow_eq_of_pow_five hu5 (m' := 3) (by norm_num)
    · exact zpowers_pow_eq_of_pow_five hu5 (m' := 2) (by norm_num)
    · exact zpowers_pow_eq_of_pow_five hu5 (m' := 4) (by norm_num)
  · exact Or.inr ⟨_, (hk j').1, key 1 1 (by norm_num) 1 (by norm_num) j'⟩
  · exact Or.inr ⟨_, (hk j').2.1, key 3 2 (by norm_num) 2 (by norm_num) j'⟩
  · exact Or.inr ⟨_, (hk j').2.2.1, key 2 3 (by norm_num) 3 (by norm_num) j'⟩
  · exact Or.inr ⟨_, (hk j').2.2.2, key 4 4 (by norm_num) 4 (by norm_num) j'⟩

end Lines

section Range


theorem ggF4N2_mixed_lines
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {y : G} {K : Subgroup G} {Rd Ra : Prop} (hR : GGSecFiveRestGen 5 B Bs x L D J Rd Ra)
    (hNbr : GGNbr 5 B x D J y K) (hL : GGCentralImage .POmegaMinus 4 2 L)
    (hK : GGCentralImage .PSL 6 2 K)
    (hF4 : GGWeylOfType 5 CoxeterMatrix.F₄ (ggAutomizer L Bs ⊔ ggAutomizer K Bs))
    {g : G} (hgL : g ∈ L) (hgN : g ∈ Subgroup.normalizer (Bs : Set G))
    (hginv : ∀ b ∈ Bs ⊓ L, g * b * g⁻¹ = b⁻¹) (hgx : g * x * g⁻¹ = x) :
    ∃ t ∈ K, t ∈ Subgroup.normalizer (Bs : Set G) ∧ t ∈ Subgroup.centralizer (J : Set G) ∧
      t * y * t⁻¹ = y ∧
      (∀ e ∈ D, e ≠ 1 → Subgroup.zpowers e = Subgroup.zpowers (g * y * g⁻¹) ∨
        ∃ k : ℕ, k < 5 ∧ Subgroup.zpowers e = Subgroup.zpowers (y * (g * y * g⁻¹) ^ k)) ∧
      Subgroup.zpowers x = Subgroup.zpowers (y * (g * y * g⁻¹)) ∧
      Subgroup.zpowers (t * x * t⁻¹) = Subgroup.zpowers (y * (g * y * g⁻¹) ^ 4) := by
  classical
  obtain ⟨v, ⟨hvD, -⟩, hvo, hDyv, hgy, t, htK, htN, htJ, hty, htv⟩ :=
    ggF4N2_swap_exchanges_axes hR hNbr hL hK hF4 hgL hgN hginv hgx
  obtain ⟨hxBs, hxy, hyo, hDcl, hDcard, hDE⟩ := ggF4N2_x_data hR hNbr
  have hyD : y ∈ D := hDcl ▸ Subgroup.subset_closure (by simp)
  have hxD : x ∈ D := hDcl ▸ Subgroup.subset_closure (by simp)
  have hDle : D ≤ Subgroup.centralizer ({g ^ 2} : Set G) :=
    ggF4N2L_swap_sq_centralizes hR hL hgL hginv hgx
  obtain ⟨-, -, -, -, -, -, hgD, -⟩ := ggF4N2L_swap_normalizes hR hL hgL hginv hgx
  set u : G := g * y * g⁻¹ with hu_def
  have huo : orderOf u = 5 := by
    rw [hu_def, ← MulAut.conj_apply, MulEquiv.orderOf_eq, hyo]
  have hu5 : u ^ 5 = 1 := huo ▸ pow_orderOf_eq_one u
  have hy5 : y ^ 5 = 1 := hyo ▸ pow_orderOf_eq_one y
  have hcard_zp : ∀ w : G, orderOf w = 5 → Nat.card (Subgroup.zpowers w) = 5 := fun w hw => by
    rw [Nat.card_zpowers, hw]
  have hzeq : ∀ {w w' : G}, orderOf w = 5 → orderOf w' = 5 → w ∈ Subgroup.zpowers w' →
      Subgroup.zpowers w = Subgroup.zpowers w' := fun hw hw' hww =>
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hww)
      (by rw [hcard_zp _ hw, hcard_zp _ hw'])
  have huv : Subgroup.zpowers u = Subgroup.zpowers v := hzeq huo hvo hgy
  have hDyu : D = Subgroup.zpowers y ⊔ Subgroup.zpowers u := by rw [hDyv, huv]
  have huD : u ∈ D := hDyu ▸ (le_sup_right : Subgroup.zpowers u ≤ _) (Subgroup.mem_zpowers u)
  have hcommD : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hDE.1.is_comm.comm (⟨a, ha⟩ : ↥D) ⟨b, hb⟩)
  have hyu : Commute y u := hcommD y hyD u huD
  have hlines := fun e (he : e ∈ D) (he1 : e ≠ 1) =>
    zpowers_eq_of_mem_sup_of_orderOf_five hyo huo hyu (hDyu ▸ he) he1
  have hyu' : y ∉ Subgroup.zpowers u := by
    intro h
    have hle : D ≤ Subgroup.zpowers u := by
      rw [hDyu]
      exact sup_le (Subgroup.zpowers_le.mpr h) le_rfl
    have := Subgroup.card_le_of_le hle
    rw [hDcard, hcard_zp u huo] at this
    norm_num at this
  have hgu : g * u * g⁻¹ = y := by
    have h := Subgroup.mem_centralizer_singleton_iff.mp (hDle hyD)
    calc g * u * g⁻¹ = g * (g * y * g⁻¹) * g⁻¹ := by rw [hu_def]
      _ = g ^ 2 * y * (g ^ 2)⁻¹ := by rw [pow_two]; group
      _ = y := by rw [← h, mul_inv_cancel_right]
  set F : Subgroup G := D ⊓ Subgroup.centralizer ({g} : Set G) with hF_def
  have hmemF : ∀ e ∈ D, g * e * g⁻¹ = e → e ∈ F := fun e he h => Subgroup.mem_inf.mpr ⟨he, by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc e * g = g * e * g⁻¹ * g := by rw [h]
      _ = g * e := inv_mul_cancel_right _ _⟩
  have hyuF : y * u ∈ F := by
    refine hmemF _ (D.mul_mem hyD huD) ?_
    calc g * (y * u) * g⁻¹ = (g * y * g⁻¹) * (g * u * g⁻¹) := by group
      _ = u * y := by rw [← hu_def, hgu]
      _ = y * u := (hyu.eq).symm
  have hyF : y ∉ F := by
    intro h
    have h1 := Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp h).2
    have h2 : u = y := by rw [hu_def, ← h1, mul_inv_cancel_right]
    exact hyu' (h2 ▸ Subgroup.mem_zpowers u)
  have hyuo : orderOf (y * u) = 5 := by
    refine orderOf_eq_prime ?_ ?_
    · rw [hyu.mul_pow, hy5, hu5, one_mul]
    · intro h
      apply hyu'
      rw [eq_inv_of_mul_eq_one_left h]
      exact Subgroup.inv_mem _ (Subgroup.mem_zpowers u)
  have hFD : F ≤ D := inf_le_left
  have hFdvd : Nat.card F ∣ 5 ^ 2 := hDcard ▸ Subgroup.card_dvd_of_le hFD
  obtain ⟨m, hm, hmF⟩ := (Nat.dvd_prime_pow Nat.prime_five).mp hFdvd
  have hF5 : Nat.card F = 5 := by
    interval_cases m
    · exfalso
      have hbot := Subgroup.eq_bot_of_card_eq F (by rw [hmF]; norm_num)
      have h : y * u ∈ (⊥ : Subgroup G) := hbot ▸ hyuF
      rw [Subgroup.mem_bot] at h
      rw [h, orderOf_one] at hyuo
      norm_num at hyuo
    · rw [hmF]; norm_num
    · exfalso
      have hFeq : F = D := Subgroup.eq_of_le_of_card_ge hFD (by rw [hDcard, hmF])
      exact hyF (hFeq ▸ hyD)
  have hFyu : Subgroup.zpowers (y * u) = F :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hyuF) (by rw [hF5, hcard_zp _ hyuo])
  have hxF : x ∈ F := hmemF x hxD hgx
  have hx1 : x ≠ 1 := fun h => hxy (h ▸ Subgroup.one_mem _)
  have hxo : orderOf x = 5 := orderOf_eq_prime (hDE.2 x hxD) hx1
  have hxline : Subgroup.zpowers x = Subgroup.zpowers (y * u) := hzeq hxo hyuo (hFyu ▸ hxF)
  have htu : t * u * t⁻¹ = u⁻¹ := by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hgy
    rw [← hk, ← MulAut.conj_apply, map_zpow, MulAut.conj_apply, htv, inv_zpow]
  have hu4 : u ^ 4 = u⁻¹ := by
    rw [eq_inv_iff_mul_eq_one, ← pow_succ]
    exact hu5
  have hmap : ∀ w e : G, Subgroup.zpowers (w * e * w⁻¹) =
      (Subgroup.zpowers e).map (MulAut.conj w).toMonoidHom := fun w e => by
    rw [MonoidHom.map_zpowers]
    rfl
  have htx : Subgroup.zpowers (t * x * t⁻¹) = Subgroup.zpowers (y * u ^ 4) := by
    rw [hmap, hxline, ← hmap, hu4]
    congr 1
    calc t * (y * u) * t⁻¹ = (t * y * t⁻¹) * (t * u * t⁻¹) := by group
      _ = y * u⁻¹ := by rw [hty, htu]
  exact ⟨t, htK, htN, htJ, hty, hlines, hxline, htx⟩

theorem ggF4N2_mixed_ggG0_eq_sup
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {y : G} {K : Subgroup G} {Rd Ra : Prop} (hR : GGSecFiveRestGen 5 B Bs x L D J Rd Ra)
    (hNbr : GGNbr 5 B x D J y K) (hL : GGCentralImage .POmegaMinus 4 2 L)
    (hK : GGCentralImage .PSL 6 2 K)
    (hF4 : GGWeylOfType 5 CoxeterMatrix.F₄ (ggAutomizer L Bs ⊔ ggAutomizer K Bs))
    {g : G} (hgL : g ∈ L) (hgN : g ∈ Subgroup.normalizer (Bs : Set G))
    (hginv : ∀ b ∈ Bs ⊓ L, g * b * g⁻¹ = b⁻¹) (hgx : g * x * g⁻¹ = x)
    (hbad : ∀ (y' : G) (K' : Subgroup G), GGNbr 5 B x D J y' K' →
      Subgroup.zpowers y' ≠ Subgroup.zpowers (y * (g * y * g⁻¹) ^ 2) ∧
        Subgroup.zpowers y' ≠ Subgroup.zpowers (y * (g * y * g⁻¹) ^ 3)) :
    ggG0 5 B x L D J = L ⊔ K := by
  obtain ⟨t, htK, -, htJ, -, hlines, hxline, htx⟩ :=
    ggF4N2_mixed_lines hR hNbr hL hK hF4 hgL hgN hginv hgx
  obtain ⟨-, -, -, -, -, -, -, hgJ⟩ := ggF4N2L_swap_normalizes hR hL hgL hginv hgx
  have hJK : J ≤ K := ggF4N2J_le_psl6_neighbor hR hNbr hL hK
  have htNJ : t ∈ Subgroup.normalizer (J : Set G) := Subgroup.centralizer_le_normalizer _ htJ
  have h1 : (1 : G) ∈ (L ⊔ K) ⊓ Subgroup.normalizer (J : Set G) := Subgroup.one_mem _
  refine ggG0_eq_sup_of_lineCover hR.1.1 hR.1.2.2 hNbr hJK ?_
  intro y' K' h'
  obtain ⟨-, -, hy'o, hD'cl, -, -⟩ := ggF4N2_x_data hR h'
  have hy'D : y' ∈ D := hD'cl ▸ Subgroup.subset_closure (by simp)
  have hy'1 : y' ≠ 1 := fun h => by
    rw [h, orderOf_one] at hy'o
    norm_num at hy'o
  rcases hlines y' hy'D hy'1 with h | ⟨k, hk, h⟩
  · exact ⟨g, ⟨(le_sup_left : L ≤ L ⊔ K) hgL, hgJ⟩, Or.inl h⟩
  · interval_cases k
    · exact ⟨1, h1, Or.inl (by rw [h]; simp)⟩
    · exact ⟨1, h1, Or.inr (by rw [h, pow_one, ← hxline]; simp)⟩
    · exact absurd h (hbad y' K' h').1
    · exact absurd h (hbad y' K' h').2
    · exact ⟨t, ⟨(le_sup_right : K ≤ L ⊔ K) htK, htNJ⟩, Or.inr (by rw [h, ← htx])⟩

open CFSG.LieType.Universal CFSG.LieType.Universal.Spin in
theorem card_centralImage_POmegaMinus_four_two {G : Type} [Group G] {L : Subgroup G}
    (hL : GGCentralImage .POmegaMinus 4 2 L) :
    Nat.card L = 4 ^ 12 * (4 ^ 4 + 1) * (4 ^ 2 - 1) * (4 ^ 4 - 1) * (4 ^ 6 - 1) := by
  obtain ⟨ψ, -, hker, hrange⟩ := hL
  let K := GaloisField 2 2
  let b := (minusCoeffs 2 2).1
  let c := (minusCoeffs 2 2).2
  have hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0 := minusCoeffs_irr 2 2
  have hZ : Subgroup.center (spinGroup (Spin.quadMinus 4 K b c)) = ⊥ :=
    PsiDiag.SpinM.center_eq_bot hirr (by norm_num)
  have hcard : Nat.card (spinGroup (Spin.quadMinus 4 K b c)) =
      Nat.card (spinGroup (Spin.quadMinus 4 K b c) ⧸
        Subgroup.center (spinGroup (Spin.quadMinus 4 K b c))) := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup
      (Subgroup.center (spinGroup (Spin.quadMinus 4 K b c))), hZ, Subgroup.card_bot, mul_one]
  have hquot : Nat.card (spinGroup (Spin.quadMinus 4 K b c) ⧸
        Subgroup.center (spinGroup (Spin.quadMinus 4 K b c))) =
      Nat.card (CFSG.Open.StatedProj (CFSG.Open.StatedOmega
        (CFSG.Open.StatedQuadMinus 4 K b c))) :=
    Nat.card_congr (spinQuotientCenterEquivQuadMinus (K := K) (n := 4) (b := b) (c := c)
      (by norm_num) hirr).toEquiv
  have hform := CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedOmega_quadMinus
    (K := K) (n := 4) (b := b) (c := c) (by norm_num) hirr
  have hK : Nat.card K = 4 := by
    simpa using GaloisField.card 2 2 (by norm_num)
  rw [hK] at hform
  have hform' : (Nat.card (CFSG.Open.StatedProj (CFSG.Open.StatedOmega
        (CFSG.Open.StatedQuadMinus 4 K b c))) : ℤ) =
      (4:ℤ)^12 * ((4:ℤ)^4+1) * ∏ i ∈ Finset.Icc 1 3, ((4:ℤ)^(2*i)-1) := by
    simpa using hform
  have hprod : (∏ i ∈ Finset.Icc 1 3, ((4:ℤ)^(2*i)-1)) =
      (4^2-1)*(4^4-1)*(4^6-1) := by
    norm_num [Finset.prod_Icc_succ_top]
  rw [hprod] at hform'
  have hP : Nat.card (CFSG.Open.StatedProj (CFSG.Open.StatedOmega
        (CFSG.Open.StatedQuadMinus 4 K b c))) =
      4 ^ 12 * (4 ^ 4 + 1) * (4 ^ 2 - 1) * (4 ^ 4 - 1) * (4 ^ 6 - 1) := by
    have h := hform'
    norm_num at h
    exact_mod_cast h
  have hinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    refine hker.trans ?_
    change Subgroup.center (spinGroup (Spin.quadMinus 4 K b c)) ≤ ⊥
    rw [hZ]
  have hLcard : Nat.card L = Nat.card (spinGroup (Spin.quadMinus 4 K b c)) := by
    rw [← hrange]
    exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  rw [hLcard, hcard, hquot, hP]

theorem dvd_card_of_centralImage_POmegaMinus_four_two {G : Type} [Group G] {L : Subgroup G}
    (hL : GGCentralImage .POmegaMinus 4 2 L) : 257 ∣ Nat.card L := by
  rw [card_centralImage_POmegaMinus_four_two hL]
  norm_num

theorem ggF4N2_mixed_not_axis_to_x
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {y : G} {K : Subgroup G} {Rd Ra : Prop} (hR : GGSecFiveRestGen 5 B Bs x L D J Rd Ra)
    (hNbr : GGNbr 5 B x D J y K) (hL : GGCentralImage .POmegaMinus 4 2 L)
    (hK : GGCentralImage .PSL 6 2 K) {γ : G} (hγJ : γ ∈ Subgroup.normalizer (J : Set G))
    (hγ : Subgroup.zpowers (γ * y * γ⁻¹) = Subgroup.zpowers x) : False := by
  have hI := hR.1.1
  have hDJ := hR.1.2.2
  have hKc : CFSG.Assembly.IsComponentOf K (Subgroup.centralizer ({y} : Set G)) :=
    (isComponentOf_of_isNeighborOf hI.2.2.2.2.2.2.2 (isNeighborOf_of_ggNbr hDJ hNbr)).1
  have hLc : CFSG.Assembly.IsComponentOf L (Subgroup.centralizer ({x} : Set G)) :=
    hI.2.2.2.2.2.2.1.2.2.2.1
  have hKγ : CFSG.Assembly.IsComponentOf (K.map (MulAut.conj γ).toMonoidHom)
      (Subgroup.centralizer ({x} : Set G)) := by
    rw [← centralizer_singleton_eq_of_zpowers_eq hγ]
    exact isComponentOf_centralizer_map_conj hKc γ
  have hJK : J ≤ K := ggF4N2J_le_psl6_neighbor hR hNbr hL hK
  have hJKγ : J ≤ K.map (MulAut.conj γ).toMonoidHom :=
    (map_conj_eq_of_mem_normalizer hγJ).symm.le.trans (Subgroup.map_mono hJK)
  have hJL : J ≤ L := fun j hj => (hR.1.2.2.1.2.2.2.2.2.1.1 hj).1
  obtain ⟨t₁, -, j₁, -, -, -, -, -, hj₁J, -, -, ht₁, -, ht₁o, -, h₁₁, -, -, -, -, -⟩ :=
    ggF4N2K_block_inverters hR hNbr hL hK
  rcases isComponentOf_le_or_commutator_eq_bot hLc hKγ.2.1 with hle | hcomm
  · obtain ⟨ψ, -, hψK, -⟩ := ggF4N2K_chart_blockSL hR hNbr hL hK
    have h1 : Nat.card L ∣ Nat.card (K.map (MulAut.conj γ).toMonoidHom) :=
      Subgroup.card_dvd_of_le hle
    have h2 : Nat.card (K.map (MulAut.conj γ).toMonoidHom) = Nat.card K :=
      Subgroup.card_map_of_injective (MulAut.conj γ).injective
    have h3 : Nat.card K ∣ Nat.card (Matrix.SpecialLinearGroup (Fin 6) (GaloisField 2 2)) := by
      rw [← hψK]
      exact Subgroup.card_range_dvd ψ
    have h4 := (dvd_card_of_centralImage_POmegaMinus_four_two hL).trans (h1.trans (h2 ▸ h3))
    rw [card_SL_six_four] at h4
    norm_num at h4
  · have hc : t₁ * j₁ = j₁ * t₁ :=
      Subgroup.mem_centralizer_iff.mp
        ((Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm) (hJL hj₁J)) t₁ (hJKγ ht₁.2)
    have hfix : t₁⁻¹ = t₁ := by rw [← h₁₁, ← hc, mul_inv_cancel_right]
    have h2 : t₁ ^ 2 = 1 := by
      rw [pow_two]
      nth_rewrite 1 [← hfix]
      exact inv_mul_cancel t₁
    have hdvd := orderOf_dvd_of_pow_eq_one h2
    rw [ht₁o] at hdvd
    norm_num at hdvd

theorem ggF4N2_mixed_type_obstruction
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {y : G} {K : Subgroup G} {Rd Ra : Prop} (hR : GGSecFiveRestGen 5 B Bs x L D J Rd Ra)
    (hNbr : GGNbr 5 B x D J y K) (hL : GGCentralImage .POmegaMinus 4 2 L)
    (hK : GGCentralImage .PSL 6 2 K)
    (hF4 : GGWeylOfType 5 CoxeterMatrix.F₄ (ggAutomizer L Bs ⊔ ggAutomizer K Bs))
    {g : G} (hgL : g ∈ L) (hgN : g ∈ Subgroup.normalizer (Bs : Set G))
    (hginv : ∀ b ∈ Bs ⊓ L, g * b * g⁻¹ = b⁻¹) (hgx : g * x * g⁻¹ = x) :
    ∀ γ ∈ Subgroup.normalizer (J : Set G), ∀ e ∈ ({y, g * y * g⁻¹} : Set G),
      ∀ f ∈ ({y * (g * y * g⁻¹), y * (g * y * g⁻¹) ^ 4} : Set G),
        Subgroup.zpowers (γ * e * γ⁻¹) ≠ Subgroup.zpowers f := by
  obtain ⟨t, -, -, htJ, -, -, hxline, htx⟩ :=
    ggF4N2_mixed_lines hR hNbr hL hK hF4 hgL hgN hginv hgx
  obtain ⟨-, -, -, -, -, -, -, hgJ⟩ := ggF4N2L_swap_normalizes hR hL hgL hginv hgx
  have htNJ : t⁻¹ ∈ Subgroup.normalizer (J : Set G) :=
    Subgroup.inv_mem _ (Subgroup.centralizer_le_normalizer _ htJ)
  have hmap : ∀ w e : G, Subgroup.zpowers (w * e * w⁻¹) =
      (Subgroup.zpowers e).map (MulAut.conj w).toMonoidHom := fun w e => by
    rw [MonoidHom.map_zpowers]
    rfl
  have hx_of : ∀ γ' : G, γ' ∈ Subgroup.normalizer (J : Set G) →
      Subgroup.zpowers (γ' * y * γ'⁻¹) ≠ Subgroup.zpowers x := fun γ' hγ' h =>
    ggF4N2_mixed_not_axis_to_x hR hNbr hL hK hγ' h
  have htx' : ∀ γ' : G, Subgroup.zpowers (γ' * y * γ'⁻¹) = Subgroup.zpowers (t * x * t⁻¹) →
      Subgroup.zpowers ((t⁻¹ * γ') * y * (t⁻¹ * γ')⁻¹) = Subgroup.zpowers x := by
    intro γ' h
    rw [show (t⁻¹ * γ') * y * (t⁻¹ * γ')⁻¹ = t⁻¹ * (γ' * y * γ'⁻¹) * t⁻¹⁻¹ by group, hmap, h,
      ← hmap]
    congr 1
    group
  have hu : ∀ γ : G, γ * (g * y * g⁻¹) * γ⁻¹ = (γ * g) * y * (γ * g)⁻¹ := fun γ => by group
  intro γ hγ e he f hf h
  rcases he with rfl | rfl <;> rcases hf with rfl | rfl
  · exact hx_of γ hγ (h.trans hxline.symm)
  · exact hx_of _ (Subgroup.mul_mem _ htNJ hγ) (htx' γ (h.trans htx.symm))
  · rw [hu] at h
    exact hx_of _ (Subgroup.mul_mem _ hγ hgJ) (h.trans hxline.symm)
  · rw [hu] at h
    exact hx_of _ (Subgroup.mul_mem _ htNJ (Subgroup.mul_mem _ hγ hgJ))
      (htx' (γ * g) (h.trans htx.symm))

end Range

end CFSG.StandardType

end
