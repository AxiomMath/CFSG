module
public import CFSG.LocalAnalysis.WeakClosure81.OddCentral.Frame
public import CFSG.LocalAnalysis.WeakClosure81.OddCentral.OddTranspositions
public import CFSG.LocalAnalysis.WeakClosure81.SevenKGen
public import CFSG.Walter.PSL2Facts.Even
public import CFSG.CGT.Timmesfeld75.ListWCL2
public import CFSG.RankThree.S4Free.Stellmacher24Sz
public import CFSG.LocalAnalysis.SolvableSignalizer.CoprimeAction
public import CFSG.CGT.Timmesfeld75.Core214Proof
public import CFSG.RankThree.PartTwo.Sec21.FF79Sec3Tools

public section
namespace CFSG.LocalAnalysis.WeakClosure81.OddCentral

open Subgroup
open scoped commutatorElement

@[expose] def BorelData (L : Type) [Group L] (q : ℕ) : Prop :=
  ∃ Z : Subgroup L, (∀ z ∈ Z, z ^ 2 = 1) ∧ Nat.card Z = q ∧
    (∀ x : L, orderOf x = 2 → ∃ g : L, g * x * g⁻¹ ∈ Z) ∧
    ∃ h ∈ normalizer (Z : Set L), Odd (orderOf h) ∧ (∀ z ∈ Z, h * z * h⁻¹ = z → z = 1) ∧
      ∀ z ∈ Z, z ≠ 1 → ∀ w ∈ Z, w ≠ 1 → ∃ k : ℕ, h ^ k * z * (h ^ k)⁻¹ = w

theorem BorelData.of_mulEquiv {L M : Type} [Group L] [Group M] (e : L ≃* M) {q : ℕ}
    (hM : BorelData M q) : BorelData L q := by
  obtain ⟨Z, hZ2, hZc, hinv, h, hhN, hodd, hfix, htr⟩ := hM
  refine ⟨Z.comap e.toMonoidHom, fun z hz => ?_, ?_, fun x hx => ?_, e.symm h, ?_, ?_,
    fun z hz hzh => ?_, fun z hz hz1 w hw hw1 => ?_⟩
  · apply e.injective
    simpa using hZ2 _ hz
  · rw [← hZc]
    exact Nat.card_congr ((e.subgroupMap (Z.comap e.toMonoidHom)).toEquiv.trans
      (Equiv.subtypeEquivRight (fun m => by
        simp only [mem_map, mem_comap, MulEquiv.coe_toMonoidHom]
        constructor
        · rintro ⟨y, hy, rfl⟩; exact hy
        · intro hm; exact ⟨e.symm m, by simpa using hm, by simp⟩)))
  · obtain ⟨g, hg⟩ := hinv (e x) (by rw [MulEquiv.orderOf_eq]; exact hx)
    exact ⟨e.symm g, by simpa [mem_comap] using hg⟩
  · rw [mem_normalizer_iff] at hhN ⊢
    intro n
    simp only [mem_comap, MulEquiv.coe_toMonoidHom, map_mul, map_inv,
      MulEquiv.apply_symm_apply]
    exact hhN (e n)
  · rwa [MulEquiv.orderOf_eq]
  · apply e.injective
    rw [map_one]
    refine hfix (e z) hz ?_
    have := congrArg e hzh
    simpa using this
  · obtain ⟨k, hk⟩ := htr (e z) hz (by simpa using hz1) (e w) hw (by simpa using hw1)
    refine ⟨k, e.injective ?_⟩
    simpa using hk

private theorem odd_two_pow_sub_one {n : ℕ} (hn : 1 ≤ n) : Odd (2 ^ n - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [pow_succ]
  have : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  exact ⟨2 ^ m - 1, by omega⟩

private theorem pow_of_mem_zpowers {G : Type*} [Group G] [Finite G] {h d : G}
    (hd : d ∈ zpowers h) : ∃ k : ℕ, h ^ k = d := by
  rw [← mem_powers_iff_mem_zpowers] at hd
  exact hd

private theorem exists_ne_of_card {G : Type*} [Group G] [Finite G] {Z : Subgroup G}
    (hZ : 2 < Nat.card Z) {u : G} (hu : u ∈ Z) (hu2 : u ^ 2 = 1) :
    ∃ w ∈ Z, w ≠ 1 ∧ w ≠ u := by
  by_contra hcon
  push Not at hcon
  have hle : Z ≤ zpowers u := fun w hw => by
    by_cases h1 : w = 1
    · rw [h1]; exact one_mem _
    · rw [hcon w hw h1]; exact mem_zpowers u
  have hc := Subgroup.card_le_of_le hle
  rw [Nat.card_zpowers] at hc
  have := orderOf_le_of_pow_eq_one (by norm_num) hu2
  omega

private theorem fix_of_transitive {G : Type*} [Group G] [Finite G] {Z : Subgroup G} {h : G}
    (hZ : 2 < Nat.card Z) (hZ2 : ∀ z ∈ Z, z ^ 2 = 1)
    (htr : ∀ z ∈ Z, z ≠ 1 → ∀ w ∈ Z, w ≠ 1 → ∃ k : ℕ, h ^ k * z * (h ^ k)⁻¹ = w) :
    ∀ z ∈ Z, h * z * h⁻¹ = z → z = 1 := by
  intro z hz hzh
  by_contra hz1
  have hcomm : ∀ k : ℕ, h ^ k * z * (h ^ k)⁻¹ = z := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      calc h ^ (k + 1) * z * (h ^ (k + 1))⁻¹ = h * (h ^ k * z * (h ^ k)⁻¹) * h⁻¹ := by
            rw [pow_succ']; group
        _ = z := by rw [ih, hzh]
  obtain ⟨w, hw, hw1, hwz⟩ := exists_ne_of_card hZ hz (hZ2 z hz)
  obtain ⟨k, hk⟩ := htr z hz hz1 w hw hw1
  rw [hcomm k] at hk
  exact hwz hk.symm

theorem borelData_psl2 {n : ℕ} (hn : 2 ≤ n) :
    BorelData (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 n)) (2 ^ n) := by
  classical
  set P := Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 n)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain U : Sylow 2 P := default
  obtain ⟨hUel, hUc⟩ := CFSG.Walter.psl2_even_sylow_two hn U
  have hU2 : ∀ z ∈ (U : Subgroup P), z ^ 2 = 1 := fun z hz =>
    CFSG.elemPow_eq_one_of_isElementaryAbelian z hz
  have hq : 2 < 2 ^ n := by
    calc 2 < 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  obtain ⟨D, hDcyc, hDc, -, hsup, huniq⟩ := CFSG.Walter.psl2_even_normalizer_sylow_two hn U
  obtain ⟨g, hg⟩ := hDcyc.exists_generator
  have htr : ∀ z ∈ (U : Subgroup P), z ≠ 1 → ∀ w ∈ (U : Subgroup P), w ≠ 1 →
      ∃ k : ℕ, (g : P) ^ k * z * ((g : P) ^ k)⁻¹ = w := by
    intro z hz hz1 w hw hw1
    obtain ⟨d, hd, -⟩ := huniq z hz hz1 w hw hw1
    obtain ⟨k, hk⟩ := pow_of_mem_zpowers (hg d)
    exact ⟨k, by rw [← hd, ← hk]; simp⟩
  refine ⟨U, hU2, hUc, fun x hx => ?_, g, ?_, ?_, fix_of_transitive (hUc ▸ hq) hU2 htr, htr⟩
  ·
    have hU1 : (U : Subgroup P) ≠ ⊥ := by
      intro hbot
      rw [hbot, Subgroup.card_bot] at hUc
      omega
    obtain ⟨v, hv⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hU1
    have huU : (v : P) ∈ (U : Subgroup P) := v.2
    have hu1 : (v : P) ≠ 1 := fun h => hv (Subtype.ext h)
    set u : P := (v : P)
    have hu : orderOf (u : P) = 2 := orderOf_eq_prime (hU2 _ huU) hu1
    obtain ⟨c, hc⟩ := isConj_iff.mp (CFSG.Walter.psl2_even_isConj_of_orderOf_eq_two hn hu hx)
    refine ⟨c⁻¹, ?_⟩
    rw [← hc]
    simpa [mul_assoc] using huU
  · have hle : D ≤ normalizer ((U : Subgroup P) : Set P) := hsup ▸ le_sup_right
    exact hle g.2
  · rw [Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hg, hDc]
    exact odd_two_pow_sub_one (by omega)

private theorem conj_mem_inf_centralizer {G : Type*} [Group G] {S : Subgroup G} {g : G}
    (hg : g ∈ normalizer (S : Set G)) {z : G} (hz : z ∈ S ⊓ centralizer (S : Set G)) :
    g * z * g⁻¹ ∈ S ⊓ centralizer (S : Set G) := by
  rw [mem_normalizer_iff] at hg
  refine Subgroup.mem_inf.mpr ⟨(hg z).mp hz.1, mem_centralizer_iff.mpr fun s hs => ?_⟩
  have hs' : g⁻¹ * s * g ∈ S := by
    have := (hg (g⁻¹ * s * g)).mpr
    apply this
    simpa [mul_assoc] using hs
  have hc := (mem_centralizer_iff.mp hz.2) _ hs'
  calc s * (g * z * g⁻¹) = g * ((g⁻¹ * s * g) * z) * g⁻¹ := by group
    _ = g * (z * (g⁻¹ * s * g)) * g⁻¹ := by rw [hc]
    _ = g * z * g⁻¹ * s := by group

theorem borelData_sz {a : ℕ} (ha : 1 ≤ a) {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1)) {X : Type} [Group X] [Finite X]
    (e : X ≃* CFSG.Blueprint.suzukiGroup a K) : BorelData X (2 ^ (2 * a + 1)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain S : Sylow 2 X := default
  set Z : Subgroup X := (S : Subgroup X) ⊓ centralizer ((S : Subgroup X) : Set X) with hZdef
  obtain ⟨-, hZc, -, -⟩ := CFSG.RankThree.S4Free.Suzuki.card_sylow_and_center ha hK e S
  obtain ⟨T, hTcyc, hTc, -, hsup, htrT⟩ :=
    CFSG.RankThree.S4Free.Suzuki.exists_cyclic_complement ha hK e S
  obtain ⟨g, hg⟩ := hTcyc.exists_generator
  have hq : 2 < 2 ^ (2 * a + 1) := by
    calc 2 < 2 ^ 3 := by norm_num
      _ ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have htr : ∀ z ∈ Z, z ≠ 1 → ∀ w ∈ Z, w ≠ 1 → ∃ k : ℕ, (g : X) ^ k * z * ((g : X) ^ k)⁻¹ = w := by
    intro z hz hz1 w hw hw1
    obtain ⟨t, ht, htw⟩ := htrT z hz w hw hz1 hw1
    obtain ⟨k, hk⟩ := pow_of_mem_zpowers (hg ⟨t, ht⟩)
    exact ⟨k, by rw [← htw, ← show ((g : X) ^ k) = t from by simpa using congrArg Subtype.val hk]⟩
  have hZ2 : ∀ z ∈ Z, z ^ 2 = 1 := by
    obtain ⟨⟨u, huZ⟩, hu⟩ := exists_prime_orderOf_dvd_card' (G := Z) 2
      (by rw [hZc]; exact dvd_pow_self 2 (by omega))
    rw [Subgroup.orderOf_mk] at hu
    intro z hz
    by_cases hz1 : z = 1
    · rw [hz1, one_pow]
    have hu1 : u ≠ 1 := by rintro rfl; simp at hu
    obtain ⟨k, hk⟩ := htr u huZ hu1 z hz hz1
    rw [← hk, conj_pow, ← hu, pow_orderOf_eq_one, mul_one, mul_inv_cancel]
  have hgN : (g : X) ∈ normalizer ((S : Subgroup X) : Set X) := by
    rw [← hsup]; exact mem_sup_right g.2
  refine ⟨Z, hZ2, hZc, fun x hx => ?_, g, ?_, ?_, fix_of_transitive (hZc ▸ hq) hZ2 htr, htr⟩
  ·
    have hxp : IsPGroup 2 (zpowers x) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx, pow_one])
    obtain ⟨S', hS'⟩ := hxp.exists_le_sylow
    obtain ⟨c, hc⟩ := MulAction.exists_smul_eq X S' S
    have hxS : c * x * c⁻¹ ∈ (S : Subgroup X) := by
      rw [← hc, Sylow.coe_subgroup_smul]
      exact Subgroup.smul_mem_pointwise_smul _ (MulAut.conj c) _ (hS' (mem_zpowers x))
    refine ⟨c, hxS, ?_⟩
    refine CFSG.RankThree.S4Free.Suzuki.mem_centralizer_of_sq_eq_one hK e S hxS ?_
    rw [conj_pow, ← hx, pow_orderOf_eq_one, mul_one, mul_inv_cancel]
  · rw [mem_normalizer_iff]
    intro n
    constructor
    · exact conj_mem_inf_centralizer hgN
    · intro hn
      have := conj_mem_inf_centralizer (inv_mem hgN) hn
      rwa [show (g : X)⁻¹ * ((g : X) * n * (g : X)⁻¹) * (g : X)⁻¹⁻¹ = n by group] at this
  · rw [Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hg, hTc]
    exact odd_two_pow_sub_one (by omega)

theorem borelData_of_isL2OrSz {L : Type} [Group L] [Finite L]
    {n : ℕ} (hn : 1 < n) (hL : CFSG.LocalAnalysis.WeakClosure81.SevenK.IsL2OrSz L n) :
    BorelData L (2 ^ n) := by
  rcases hL with hP | ⟨-, a, ha, K, _, _, rfl, hK, ⟨e⟩⟩
  · obtain ⟨hf, ⟨e⟩⟩ := CFSG.CGT.Timmesfeld75.exists_psl2_galois_of_statedClassicalModel hP
    exact (borelData_psl2 hf).of_mulEquiv e
  · exact borelData_sz ha hK e

open CFSG.Open Subgroup
open CFSG.Timmesfeld.Bridge.Asc72

theorem le_center_of_hyperplane_count {Y : Type} [Group Y] [Finite Y] {D : Set Y}
    (hD : IsOddTransp D) (hDc : ∀ x ∈ D, ∀ g : Y, g * x * g⁻¹ ∈ D) (hgen : closure D = ⊤)
    {T : Subgroup Y} (hT2 : ∀ x ∈ T, x ^ 2 = 1) (hTgen : closure (D ∩ (T : Set Y)) = T)
    (hconj : ∀ d ∈ D, ∃ g : Y, g * d * g⁻¹ ∈ T)
    (hcount : ∀ B : Subgroup T, B.index = 2 → ∀ d ∈ D, ∀ hdT : d ∈ T, (⟨d, hdT⟩ : T) ∉ B →
      ∃ e ∈ D, ∃ heT : e ∈ T, (⟨e, heT⟩ : T) ∉ B ∧ e ≠ d) :
    fusionOddCore Y ≤ center Y := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set R := fusionOddCore Y with hRdef
  have hRodd : Odd (Nat.card R) := CFSG.CGT.Timmesfeld75.odd_card_fusionOddCore Y
  have hTcomm : ∀ x ∈ T, ∀ y ∈ T, x * y = y * x := by
    intro x hx y hy
    have h1 := hT2 x hx
    have h2 := hT2 y hy
    have h3 := hT2 (x * y) (T.mul_mem hx hy)
    rw [sq] at h1 h2 h3
    have ix : x⁻¹ = x := inv_eq_of_mul_eq_one_right h1
    have iy : y⁻¹ = y := inv_eq_of_mul_eq_one_right h2
    have ixy : (x * y)⁻¹ = x * y := inv_eq_of_mul_eq_one_right h3
    rw [← ixy, mul_inv_rev, ix, iy]
  by_cases hTn : Nontrivial T
  swap
  ·
    rw [not_nontrivial_iff_subsingleton] at hTn
    have hDe : D = ∅ := by
      ext d
      simp only [Set.mem_empty_iff_false, iff_false]
      intro hd
      obtain ⟨g, hg⟩ := hconj d hd
      have h1 : g * d * g⁻¹ = 1 := congrArg Subtype.val (Subsingleton.elim (⟨_, hg⟩ : T) 1)
      have hd1 : d = 1 := by
        have : d = g⁻¹ * (g * d * g⁻¹) * g := by group
        rw [this, h1]; group
      have := hD.1 d hd
      rw [hd1, orderOf_one] at this
      norm_num at this
    intro r _
    rw [hDe, Subgroup.closure_empty] at hgen
    rw [mem_center_iff]
    intro g
    have hg : g ∈ (⊥ : Subgroup Y) := hgen ▸ mem_top g
    have hr : r ∈ (⊥ : Subgroup Y) := hgen ▸ mem_top r
    rw [mem_bot] at hg hr
    rw [hg, hr]
  letI iC : CommGroup T :=
    { (inferInstance : Group T) with mul_comm := fun a b => Subtype.ext (hTcomm a a.2 b b.2) }
  haveI : IsElementaryAbelian 2 T :=
    { toIsMulCommutative := ⟨⟨fun a b => Subtype.ext (hTcomm a a.2 b b.2)⟩⟩
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun g =>
        Subtype.ext (by simpa using hT2 g g.2) }
  let α : T →* MulAut R := (MulAut.conjNormal (H := R)).comp T.subtype
  have hα : ∀ (b : T) (x : R), ((α b x : R) : Y) = (b : Y) * x * (b : Y)⁻¹ := by
    intro b x
    simp [α, MulAut.conjNormal_apply]
  have hgenR := CFSG.SolvableSignalizer.iSup_fixedBySubgroup_index_eq_top 2 Nat.prime_two α
    (by rw [← even_iff_two_dvd, Nat.not_even_iff_odd]; exact hRodd)
  have hDT : ∀ d ∈ D, d ∈ T → ∀ r ∈ R, Commute r d := by
    intro d hd hdT
    let Cd : Subgroup R := (centralizer ({d} : Set Y)).comap R.subtype
    have hle : (⊤ : Subgroup R) ≤ Cd := by
      rw [← hgenR]
      refine iSup₂_le fun B hB x hx => ?_
      rw [CFSG.SolvableSignalizer.mem_fixedBySubgroup] at hx
      have hfix : ∀ b ∈ B, (b : Y) * x * (b : Y)⁻¹ = x := fun b hb => by
        rw [← hα]; exact congrArg Subtype.val (hx b hb)
      show (x : Y) ∈ centralizer ({d} : Set Y)
      rw [mem_centralizer_singleton_iff]
      by_cases hdB : (⟨d, hdT⟩ : T) ∈ B
      · have := hfix _ hdB
        simp only at this
        calc (x : Y) * d = d * x * d⁻¹ * d := by rw [this]
          _ = d * x := by group
      · obtain ⟨e, he, heT, heB, hed⟩ := hcount B hB d hd hdT hdB
        have hdeB : (⟨d, hdT⟩ : T) * ⟨e, heT⟩ ∈ B :=
          (Subgroup.mul_mem_iff_of_index_two hB).mpr (iff_of_false hdB heB)
        have hfde := hfix _ hdeB
        simp only [Subgroup.coe_mul] at hfde
        have hqc : Commute (x : Y) (d * e) := by
          show (x : Y) * (d * e) = d * e * x
          calc (x : Y) * (d * e) = d * e * x * (d * e)⁻¹ * (d * e) := by rw [hfde]
            _ = d * e * x := by group
        have hc : Commute d e := hTcomm d hdT e heT
        have := commute_of_commute_mul hD hDc hd he (Ne.symm hed) hc
          (P := R) hRodd (fun y hy => (inferInstance : R.Normal).conj_mem y hy d) x.2 hqc
        exact this.eq
    intro r hr
    have := hle (mem_top ⟨r, hr⟩)
    have h' : r ∈ centralizer ({d} : Set Y) := this
    rw [mem_centralizer_singleton_iff] at h'
    exact h'
  have hD' : ∀ d ∈ D, ∀ r ∈ R, Commute r d := by
    intro d hd r hr
    obtain ⟨g, hg⟩ := hconj d hd
    have hc := hDT _ (hDc d hd g) hg (g * r * g⁻¹) ((inferInstance : R.Normal).conj_mem r hr g)
    have : g * (r * d) * g⁻¹ = g * (d * r) * g⁻¹ := by
      calc g * (r * d) * g⁻¹ = (g * r * g⁻¹) * (g * d * g⁻¹) := by group
        _ = (g * d * g⁻¹) * (g * r * g⁻¹) := hc.eq
        _ = g * (d * r) * g⁻¹ := by group
    exact mul_left_cancel (mul_right_cancel this)
  intro r hr
  rw [mem_center_iff]
  intro g
  have hg : g ∈ closure D := hgen ▸ mem_top g
  have hcl : closure D ≤ centralizer ({r} : Set Y) := by
    rw [closure_le]
    intro d hd
    rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
    exact ((hD' d hd r hr).eq).symm
  have := hcl hg
  rw [mem_centralizer_singleton_iff] at this
  exact this

open CFSG.Open Subgroup

private theorem card_le_four {Y : Type} [Group Y] [Finite Y] {S : Subgroup Y} {a b c e : Y}
    (h : ∀ x ∈ S, x = a ∨ x = b ∨ x = c ∨ x = e) : Nat.card S ≤ 4 := by
  classical
  have hsub : (S : Set Y) ⊆ ({a, b, c, e} : Set Y) := fun x hx => by
    rcases h x hx with h | h | h | h <;> simp [h]
  calc Nat.card S = (S : Set Y).ncard := (Nat.card_coe_set_eq _)
    _ ≤ ({a, b, c, e} : Set Y).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
    _ ≤ 4 := by
      refine (Set.ncard_insert_le _ _).trans ?_
      refine (Nat.succ_le_succ (Set.ncard_insert_le _ _)).trans ?_
      refine (Nat.succ_le_succ (Nat.succ_le_succ (Set.ncard_insert_le _ _))).trans ?_
      simp

private theorem card_le_two {Y : Type} [Group Y] [Finite Y] {S : Subgroup Y} {a b : Y}
    (h : ∀ x ∈ S, x = a ∨ x = b) : Nat.card S ≤ 2 := by
  classical
  have hsub : (S : Set Y) ⊆ ({a, b} : Set Y) := fun x hx => by
    rcases h x hx with h | h <;> simp [h]
  calc Nat.card S = (S : Set Y).ncard := (Nat.card_coe_set_eq _)
    _ ≤ ({a, b} : Set Y).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
    _ ≤ 2 := (Set.ncard_insert_le _ _).trans (by simp)

private theorem pow_conj_mem {Y : Type} [Group Y] {S : Set Y} {t : Y}
    (hS : ∀ x ∈ S, t * x * t⁻¹ ∈ S) (k : ℕ) : ∀ x ∈ S, t ^ k * x * (t ^ k)⁻¹ ∈ S := by
  induction k with
  | zero => intro x hx; simpa using hx
  | succ k ih =>
    intro x hx
    have := hS _ (ih x hx)
    rwa [show t * (t ^ k * x * (t ^ k)⁻¹) * t⁻¹ = t ^ (k + 1) * x * (t ^ (k + 1))⁻¹ by
      rw [pow_succ']; group] at this

private theorem pow_conj_fix {Y : Type} [Group Y] {t c : Y} (h : t * c * t⁻¹ = c) (k : ℕ) :
    t ^ k * c * (t ^ k)⁻¹ = c := by
  induction k with
  | zero => simp
  | succ k ih =>
    calc t ^ (k + 1) * c * (t ^ (k + 1))⁻¹ = t * (t ^ k * c * (t ^ k)⁻¹) * t⁻¹ := by
          rw [pow_succ']; group
      _ = c := by rw [ih, h]

theorem residual_of_one_outside {Y : Type} [Group Y] [Finite Y] {T C T₁ H : Subgroup Y}
    {Δ : Set Y} {t : Y} {n : ℕ} (hT2 : ∀ x ∈ T, x ^ 2 = 1) (hCT₁ : C ⊓ T₁ = ⊥)
    (hdec : ∀ x ∈ T, ∃ c ∈ C, ∃ u ∈ T₁, x = c * u)
    (htC : ∀ c ∈ C, t * c * t⁻¹ = c) (htT₁ : ∀ u ∈ T₁, t * u * t⁻¹ ∈ T₁)
    (htr : ∀ u ∈ T₁, u ≠ 1 → ∀ v ∈ T₁, v ≠ 1 → ∃ k : ℕ, t ^ k * u * (t ^ k)⁻¹ = v)
    (hn : 2 ≤ n) (hcard : Nat.card T₁ = 2 ^ n) (hΔT : Δ ⊆ T) (hΔC : ∀ d ∈ Δ, d ∉ C)
    (hΔt : ∀ d ∈ Δ, t * d * t⁻¹ ∈ Δ) {d : Y} (hd : d ∈ Δ) (hdH : d ∉ H)
    (hone : ∀ e ∈ Δ, e ∉ H → e = d) :
    n = 2 ∧ ∃ c ∈ C, ∃ u ∈ T₁, u ≠ 1 ∧ d = c * u ∧ (∀ v ∈ T₁, v ≠ 1 → c * v ∈ Δ) ∧
      ∀ e ∈ Δ, ∃ v ∈ T₁, v ≠ 1 ∧ e = c * v := by
  classical
  have huniq : ∀ c ∈ C, ∀ c' ∈ C, ∀ u ∈ T₁, ∀ u' ∈ T₁, c * u = c' * u' → c = c' ∧ u = u' := by
    intro c hc c' hc' u hu u' hu' h
    have h1 : c'⁻¹ * c = u' * u⁻¹ := by
      calc c'⁻¹ * c = c'⁻¹ * (c * u) * u⁻¹ := by group
        _ = c'⁻¹ * (c' * u') * u⁻¹ := by rw [h]
        _ = u' * u⁻¹ := by group
    have hmem : c'⁻¹ * c ∈ C ⊓ T₁ :=
      ⟨C.mul_mem (C.inv_mem hc') hc, h1 ▸ T₁.mul_mem hu' (T₁.inv_mem hu)⟩
    rw [hCT₁, mem_bot] at hmem
    have hcc : c = c' := by
      calc c = c' * (c'⁻¹ * c) := by group
        _ = c' := by rw [hmem, mul_one]
    refine ⟨hcc, ?_⟩
    rw [hcc] at h
    exact mul_left_cancel h
  obtain ⟨c, hc, u, hu, rfl⟩ := hdec _ (hΔT hd)
  have hu1 : u ≠ 1 := by
    rintro rfl
    exact hΔC _ hd (by simpa using hc)
  have horb : ∀ c' ∈ C, ∀ u' ∈ T₁, u' ≠ 1 → c' * u' ∈ Δ → ∀ v ∈ T₁, v ≠ 1 → c' * v ∈ Δ := by
    intro c' hc' u' hu' hu'1 hΔ' v hv hv1
    obtain ⟨k, hk⟩ := htr u' hu' hu'1 v hv hv1
    have := pow_conj_mem hΔt k _ hΔ'
    rwa [show t ^ k * (c' * u') * (t ^ k)⁻¹ = (t ^ k * c' * (t ^ k)⁻¹) * (t ^ k * u' * (t ^ k)⁻¹)
      by group, pow_conj_fix (htC c' hc') k, hk] at this
  have hcvH : ∀ v ∈ T₁, v ≠ 1 → v ≠ u → c * v ∈ H := by
    intro v hv hv1 hvu
    by_contra hvH
    have := hone _ (horb c hc u hu hu1 hd v hv hv1) hvH
    exact hvu (huniq c hc c hc v hv u hu this).2
  have hyH' : ∀ y ∈ T₁, ∀ v ∈ T₁, v ≠ 1 → v ≠ u → v * y ≠ 1 → v * y ≠ u → y ∈ H := by
    intro y hy v hv hv1 hvu hvy1 hvyu
    have h1 := hcvH v hv hv1 hvu
    have h2 := hcvH (v * y) (T₁.mul_mem hv hy) hvy1 hvyu
    have := H.mul_mem (H.inv_mem h1) h2
    rwa [show (c * v)⁻¹ * (c * (v * y)) = y by group] at this
  have h4le : 4 ≤ Nat.card T₁ := by
    rw [hcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hother : ∃ v ∈ T₁, v ≠ 1 ∧ v ≠ u := by
    by_contra hcon
    push Not at hcon
    have : Nat.card T₁ ≤ 2 := card_le_two (a := 1) (b := u) fun v hv => by
      by_cases h1 : v = 1
      · exact Or.inl h1
      · exact Or.inr (hcon v hv h1)
    omega
  obtain ⟨v₀, hv₀, hv₀1, hv₀u⟩ := hother
  have hT₁H : T₁ ≤ H → False := by
    intro hle
    have hcH : c ∈ H := by
      have := H.mul_mem (hcvH v₀ hv₀ hv₀1 hv₀u) (H.inv_mem (hle hv₀))
      rwa [mul_inv_cancel_right] at this
    exact hdH (H.mul_mem hcH (hle hu))
  have hn2 : n = 2 := by
    by_contra hne
    have h8 : 8 ≤ Nat.card T₁ := by
      rw [hcard]
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
    apply hT₁H
    intro y hy
    by_contra hyH
    have hcon : ∀ v ∈ T₁, v ≠ 1 → v ≠ u → v * y = 1 ∨ v * y = u := by
      intro v hv hv1 hvu
      by_contra h
      push Not at h
      exact hyH (hyH' y hy v hv hv1 hvu h.1 h.2)
    have : Nat.card T₁ ≤ 4 := card_le_four (a := 1) (b := u) (c := y⁻¹) (e := u * y⁻¹)
      fun v hv => by
        by_cases h1 : v = 1
        · exact Or.inl h1
        by_cases h2 : v = u
        · exact Or.inr (Or.inl h2)
        rcases hcon v hv h1 h2 with h3 | h3
        · exact Or.inr (Or.inr (Or.inl (eq_inv_of_mul_eq_one_left h3)))
        · exact Or.inr (Or.inr (Or.inr (by
            calc v = v * y * y⁻¹ := by group
              _ = u * y⁻¹ := by rw [h3])))
    omega
  refine ⟨hn2, c, hc, u, hu, hu1, rfl, fun v hv hv1 => horb c hc u hu hu1 hd v hv hv1,
    fun e he => ?_⟩
  obtain ⟨c', hc', v, hv, rfl⟩ := hdec e (hΔT he)
  have hv1 : v ≠ 1 := by
    rintro rfl
    exact hΔC _ he (by simpa using hc')
  by_cases hcc : c' = c
  · exact ⟨v, hv, hv1, by rw [hcc]⟩
  exfalso
  have hc'H : ∀ w ∈ T₁, w ≠ 1 → c' * w ∈ H := by
    intro w hw hw1
    by_contra hwH
    have := hone _ (horb c' hc' v hv hv1 he w hw hw1) hwH
    exact hcc (huniq c' hc' c hc w hw u hu this).1
  apply hT₁H
  intro y hy
  by_cases hy1 : y = 1
  · rw [hy1]; exact one_mem _
  obtain ⟨w, hw, hw1, hwy⟩ : ∃ w ∈ T₁, w ≠ 1 ∧ w * y ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have : Nat.card T₁ ≤ 2 := card_le_two (a := 1) (b := y⁻¹) fun w hw => by
      by_cases h1 : w = 1
      · exact Or.inl h1
      · exact Or.inr (eq_inv_of_mul_eq_one_left (hcon w hw h1))
    omega
  have := H.mul_mem (H.inv_mem (hc'H w hw hw1)) (hc'H (w * y) (T₁.mul_mem hw hy) hwy)
  rwa [show (c' * w)⁻¹ * (c' * (w * y)) = y by group] at this

private theorem mem_four_of_card {Y : Type} [Group Y] [Finite Y] {S : Subgroup Y}
    (hS : Nat.card S = 4) {a b c e : Y} (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S) (he : e ∈ S)
    (hab : a ≠ b) (hac : a ≠ c) (hae : a ≠ e) (hbc : b ≠ c) (hbe : b ≠ e) (hce : c ≠ e) :
    ∀ x ∈ S, x = a ∨ x = b ∨ x = c ∨ x = e := by
  classical
  intro x hx
  by_contra hcon
  push Not at hcon
  obtain ⟨h1, h2, h3, h4⟩ := hcon
  have hsub : ({x, a, b, c, e} : Set Y) ⊆ (S : Set Y) := by
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl <;> assumption
  have h5 : ({x, a, b, c, e} : Set Y).ncard = 5 := by
    rw [Set.ncard_insert_of_notMem (by simp [h1, h2, h3, h4]),
      Set.ncard_insert_of_notMem (by simp [hab, hac, hae]),
      Set.ncard_insert_of_notMem (by simp [hbc, hbe]),
      Set.ncard_insert_of_notMem (by simp [hce]), Set.ncard_singleton]
  have := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [h5, ← Nat.card_coe_set_eq] at this
  change 5 ≤ Nat.card S at this
  omega

theorem exists_isFrame_of_residual {Y : Type} [Group Y] [Finite Y] {T₁ : Subgroup Y}
    {t s c u : Y} (hT₁2 : ∀ x ∈ T₁, x ^ 2 = 1) (hcard : Nat.card T₁ = 4) (hc2 : c ^ 2 = 1)
    (hcT₁ : ∀ v ∈ T₁, c * v = v * c) (htc : t * c * t⁻¹ = c)
    (htT₁ : ∀ v ∈ T₁, t * v * t⁻¹ ∈ T₁) (hfpf : ∀ v ∈ T₁, t * v * t⁻¹ = v → v = 1)
    (hu : u ∈ T₁) (hu1 : u ≠ 1) (hcZ : c ∈ fusionZStar Y)
    (hT₁Z : ∀ v ∈ T₁, v ∈ fusionZStar Y → v = 1)
    (hconj : ∀ v ∈ T₁, v ≠ 1 → IsConj s (c * v)) :
    ∃ d₁ d₂ d₃ : Y, CFSG.LocalAnalysis.WeakClosure81.OddCentral.IsFrame s d₁ d₂ d₃ t := by
  classical
  have hcomm : ∀ x ∈ T₁, ∀ y ∈ T₁, x * y = y * x := by
    intro x hx y hy
    have h1 := hT₁2 x hx
    have h2 := hT₁2 y hy
    have h3 := hT₁2 (x * y) (T₁.mul_mem hx hy)
    rw [sq] at h1 h2 h3
    have ix : x⁻¹ = x := inv_eq_of_mul_eq_one_right h1
    have iy : y⁻¹ = y := inv_eq_of_mul_eq_one_right h2
    have ixy : (x * y)⁻¹ = x * y := inv_eq_of_mul_eq_one_right h3
    rw [← ixy, mul_inv_rev, ix, iy]
  have hsq : ∀ x ∈ T₁, x * x = 1 := fun x hx => by rw [← sq]; exact hT₁2 x hx
  set u' := t * u * t⁻¹ with hu'def
  have hu' : u' ∈ T₁ := htT₁ u hu
  have hu'1 : u' ≠ 1 := by
    intro h
    apply hu1
    calc u = t⁻¹ * u' * t := by rw [hu'def]; group
      _ = 1 := by rw [h]; group
  have hu'u : u' ≠ u := fun h => hu1 (hfpf u hu h)
  set w := u * u' with hwdef
  have hw : w ∈ T₁ := T₁.mul_mem hu hu'
  have hw1 : w ≠ 1 := by
    intro h
    apply hu'u
    calc u' = u * (u * u') := by rw [← mul_assoc, hsq u hu, one_mul]
      _ = u := by rw [← hwdef, h, mul_one]
  have hwu : w ≠ u := by
    intro h
    apply hu'1
    calc u' = u⁻¹ * (u * u') := by group
      _ = 1 := by rw [← hwdef, h, inv_mul_cancel]
  have hwu' : w ≠ u' := by
    intro h
    apply hu1
    calc u = u * u' * u'⁻¹ := by group
      _ = 1 := by rw [← hwdef, h, mul_inv_cancel]
  have hT₁eq := mem_four_of_card hcard (one_mem _) hu hu' hw (Ne.symm hu1) (Ne.symm hu'1)
    (Ne.symm hw1) (Ne.symm hu'u) (Ne.symm hwu) (Ne.symm hwu')
  set u'' := t * u' * t⁻¹ with hu''def
  have hu'' : u'' ∈ T₁ := htT₁ u' hu'
  have hconjmul : ∀ a b : Y, t * (a * b) * t⁻¹ = (t * a * t⁻¹) * (t * b * t⁻¹) := fun a b => by
    group
  have hu''w : u'' = w := by
    rcases hT₁eq u'' hu'' with h | h | h | h
    · exfalso; apply hu'1
      calc u' = t⁻¹ * u'' * t := by rw [hu''def]; group
        _ = 1 := by rw [h]; group
    ·
      exfalso
      apply hw1
      apply hfpf w hw
      rw [hwdef, hconjmul, ← hu'def, ← hu''def, h, hcomm u' hu' u hu]
    · exfalso; exact hu'1 (hfpf u' hu' h)
    · exact h
  have htw : t * w * t⁻¹ = u := by
    rw [hwdef, hconjmul, ← hu'def, ← hu''def, hu''w, hwdef, ← mul_assoc,
      hcomm u' hu' u hu, mul_assoc, hsq u' hu', mul_one]
  have htcv : ∀ v : Y, t * (c * v) * t⁻¹ = c * (t * v * t⁻¹) := fun v => by
    rw [hconjmul, htc]
  have hcc : c * c = 1 := by rw [← sq]; exact hc2
  have hcomm' : ∀ x ∈ T₁, ∀ y ∈ T₁, Commute (c * x) (c * y) := by
    intro x hx y hy
    show c * x * (c * y) = c * y * (c * x)
    rw [mul_assoc, ← mul_assoc x c y, ← hcT₁ x hx, mul_assoc c x y, hcomm x hx y hy,
      mul_assoc, ← mul_assoc y c x, ← hcT₁ y hy, mul_assoc c y x]
  refine ⟨c * u, c * u', c * w, hconj u hu hu1, hconj u' hu' hu'1, hconj w hw hw1,
    hcomm' u hu u' hu', hcomm' u' hu' w hw, hcomm' u hu w hw, ?_, ?_, ?_, ?_, ?_⟩
  ·
    have huu' : u * u' ∈ T₁ := T₁.mul_mem hu hu'
    have : c * u * (c * u') * (c * w) = c := by
      rw [hwdef]
      calc c * u * (c * u') * (c * (u * u')) = c * (u * c) * u' * (c * (u * u')) := by group
        _ = c * (c * u) * u' * (c * (u * u')) := by rw [← hcT₁ u hu]
        _ = (c * c) * (u * u') * (c * (u * u')) := by group
        _ = (u * u') * ((u * u') * c) := by rw [hcc, one_mul, hcT₁ _ huu']
        _ = ((u * u') * (u * u')) * c := by group
        _ = c := by rw [hsq _ huu', one_mul]
    rw [this]; exact hcZ
  ·
    have : c * u * (c * u') = w := by
      rw [mul_assoc c u, ← mul_assoc u c u', ← hcT₁ u hu, mul_assoc c u u', ← hwdef,
        ← mul_assoc, hcc, one_mul]
    rw [this]
    exact fun h => hw1 (hT₁Z w hw h)
  · exact htcv u
  · rw [htcv, ← hu''def, hu''w]
  · rw [htcv, htw]

open CFSG.Open Subgroup
open CFSG.Timmesfeld.Bridge.Asc72

private theorem isConj_conj {Y : Type} [Group Y] {s x : Y} (h : IsConj s x) (g : Y) :
    IsConj s (g * x * g⁻¹) :=
  h.trans (isConj_iff.mpr ⟨g, rfl⟩)

private theorem comm_of_sq {Y : Type} [Group Y] {T : Subgroup Y} (hT2 : ∀ x ∈ T, x ^ 2 = 1) :
    ∀ x ∈ T, ∀ y ∈ T, x * y = y * x := by
  intro x hx y hy
  have h1 := hT2 x hx
  have h2 := hT2 y hy
  have h3 := hT2 (x * y) (T.mul_mem hx hy)
  rw [sq] at h1 h2 h3
  have ix : x⁻¹ = x := inv_eq_of_mul_eq_one_right h1
  have iy : y⁻¹ = y := inv_eq_of_mul_eq_one_right h2
  have ixy : (x * y)⁻¹ = x * y := inv_eq_of_mul_eq_one_right h3
  rw [← ixy, mul_inv_rev, ix, iy]

private theorem pow_conj_fix' {Y : Type*} [Group Y] {t c : Y} (h : t * c * t⁻¹ = c) (k : ℕ) :
    t ^ k * c * (t ^ k)⁻¹ = c := by
  induction k with
  | zero => simp
  | succ k ih =>
    calc t ^ (k + 1) * c * (t ^ (k + 1))⁻¹ = t * (t ^ k * c * (t ^ k)⁻¹) * t⁻¹ := by
          rw [pow_succ']; group
      _ = c := by rw [ih, h]

private theorem fpf_of_transitive {G : Type*} [Group G] [Finite G] {Z : Subgroup G} {h : G}
    (hZ : 2 < Nat.card Z) (hZ2 : ∀ z ∈ Z, z ^ 2 = 1)
    (htr : ∀ z ∈ Z, z ≠ 1 → ∀ w ∈ Z, w ≠ 1 → ∃ k : ℕ, h ^ k * z * (h ^ k)⁻¹ = w) :
    ∀ z ∈ Z, h * z * h⁻¹ = z → z = 1 := by
  intro z hz hzh
  by_contra hz1
  obtain ⟨w, hw, hw1, hwz⟩ : ∃ w ∈ Z, w ≠ 1 ∧ w ≠ z := by
    by_contra hcon
    push Not at hcon
    have hle : Z ≤ zpowers z := fun w hw => by
      by_cases h1 : w = 1
      · rw [h1]; exact one_mem _
      · rw [hcon w hw h1]; exact mem_zpowers z
    have hc := Subgroup.card_le_of_le hle
    rw [Nat.card_zpowers] at hc
    have := orderOf_le_of_pow_eq_one (by norm_num) (hZ2 z hz)
    omega
  obtain ⟨k, hk⟩ := htr z hz hz1 w hw hw1
  rw [pow_conj_fix' hzh k] at hk
  exact hwz hk.symm

theorem le_center_or_frame_of_torus {Y : Type} [Group Y] [Finite Y] {s : Y}
    (hD : IsOddTransp {x : Y | IsConj s x}) (hs : normalClosure ({s} : Set Y) = ⊤)
    (hZ : fusionZStar Y ≠ ⊤) {n : ℕ} (hn : 2 ≤ n) {T C T₁ : Subgroup Y} {t : Y}
    (hT2 : ∀ x ∈ T, x ^ 2 = 1) (hTgen : closure ({x | IsConj s x} ∩ (T : Set Y)) = T)
    (hconj : ∀ d : Y, IsConj s d → ∃ g : Y, g * d * g⁻¹ ∈ T)
    (hCT : C ≤ T) (hT₁T : T₁ ≤ T) (hCT₁ : C ⊓ T₁ = ⊥)
    (hdec : ∀ x ∈ T, ∃ c ∈ C, ∃ u ∈ T₁, x = c * u)
    (hCZ : C ≤ fusionZStar Y) (hT₁Z : T₁ ⊓ fusionZStar Y = ⊥)
    (htC : ∀ c ∈ C, t * c * t⁻¹ = c) (htT₁ : ∀ u ∈ T₁, t * u * t⁻¹ ∈ T₁)
    (htr : ∀ u ∈ T₁, u ≠ 1 → ∀ v ∈ T₁, v ≠ 1 → ∃ k : ℕ, t ^ k * u * (t ^ k)⁻¹ = v)
    (hcard : Nat.card T₁ = 2 ^ n) :
    fusionOddCore Y ≤ center Y ∨
      (n = 2 ∧ ∃ d₁ d₂ d₃ t' : Y, CFSG.LocalAnalysis.WeakClosure81.OddCentral.IsFrame s d₁ d₂ d₃ t') := by
  classical
  set D : Set Y := {x : Y | IsConj s x} with hDdef
  have hDc : ∀ x ∈ D, ∀ g : Y, g * x * g⁻¹ ∈ D := fun x hx g => isConj_conj hx g
  have hgen : closure D = ⊤ := by
    rw [← hs, normalClosure]
    congr 1
    ext x
    simp [D, Group.mem_conjugatesOfSet_iff]
  have hTcomm := comm_of_sq hT2
  have hDZ : ∀ x ∈ D, x ∉ fusionZStar Y := by
    intro x hx
    obtain ⟨g, rfl⟩ := isConj_iff.mp hx
    exact conj_not_mem_fusionZStar hs hZ g
  have hT₁Z' : ∀ v ∈ T₁, v ∈ fusionZStar Y → v = 1 := fun v hv hvZ => by
    have : v ∈ T₁ ⊓ fusionZStar Y := ⟨hv, hvZ⟩
    rwa [hT₁Z, mem_bot] at this
  have hT₁2 : ∀ x ∈ T₁, x ^ 2 = 1 := fun x hx => hT2 x (hT₁T hx)
  have h4 : 2 < Nat.card T₁ := by
    rw [hcard]
    calc 2 < 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hfpf := fpf_of_transitive h4 hT₁2 htr
  have htT : ∀ x ∈ T, t * x * t⁻¹ ∈ T := by
    intro x hx
    obtain ⟨c, hc, u, hu, rfl⟩ := hdec x hx
    rw [show t * (c * u) * t⁻¹ = (t * c * t⁻¹) * (t * u * t⁻¹) by group, htC c hc]
    exact T.mul_mem (hCT hc) (hT₁T (htT₁ u hu))
  by_cases hcount : ∀ B : Subgroup T, B.index = 2 → ∀ d ∈ D, ∀ hdT : d ∈ T,
      (⟨d, hdT⟩ : T) ∉ B → ∃ e ∈ D, ∃ heT : e ∈ T, (⟨e, heT⟩ : T) ∉ B ∧ e ≠ d
  · exact Or.inl (le_center_of_hyperplane_count hD hDc hgen hT2 hTgen hconj hcount)
  right
  push Not at hcount
  obtain ⟨B, -, d, hd, hdT, hdB, hone⟩ := hcount
  set H : Subgroup Y := B.map T.subtype
  have hdH : d ∉ H := by
    rintro ⟨x, hx, hxd⟩
    apply hdB
    have : x = ⟨d, hdT⟩ := Subtype.ext hxd
    rwa [← this]
  have hone' : ∀ e ∈ D ∩ (T : Set Y), e ∉ H → e = d := by
    rintro e ⟨he, heT⟩ heH
    refine hone e he heT fun heB => heH ⟨⟨e, heT⟩, heB, rfl⟩
  obtain ⟨hn2, c, hc, u, hu, hu1, rfl, horb, -⟩ :=
    residual_of_one_outside (Δ := D ∩ (T : Set Y)) (H := H) hT2 hCT₁ hdec htC htT₁ htr hn
      hcard (fun x hx => hx.2) (fun x hx hxC => hDZ x hx.1 (hCZ hxC))
      (fun x hx => ⟨hDc x hx.1 t, htT x hx.2⟩) ⟨hd, hdT⟩ hdH hone'
  subst hn2
  refine ⟨rfl, ?_⟩
  obtain ⟨d₁, d₂, d₃, hF⟩ := exists_isFrame_of_residual (T₁ := T₁) (t := t) (s := s) (c := c)
    (u := u) hT₁2 (by rw [hcard]; norm_num) (hT2 c (hCT hc))
    (fun v hv => hTcomm c (hCT hc) v (hT₁T hv)) (htC c hc) htT₁ hfpf hu hu1 (hCZ hc) hT₁Z'
    (fun v hv hv1 => (horb v hv hv1).1)
  exact ⟨d₁, d₂, d₃, t, hF⟩

open CFSG.Open Subgroup
open CFSG.Timmesfeld.Bridge.Asc72

theorem commute_of_oddTransp_of_isPGroup {Y : Type} [Group Y] [Finite Y] {D : Set Y}
    (hD : IsOddTransp D) {P : Subgroup Y} (hP : IsPGroup 2 P) {d e : Y} (hd : d ∈ D)
    (he : e ∈ D) (hdP : d ∈ P) (heP : e ∈ P) : Commute d e := by
  have hde : d * e ∈ P := P.mul_mem hdP heP
  obtain ⟨k, hk⟩ := hP ⟨d * e, hde⟩
  have hord : orderOf (d * e) ∣ 2 ^ k := by
    rw [orderOf_dvd_iff_pow_eq_one]
    simpa using congrArg Subtype.val hk
  have hd1 : d * d = 1 := by rw [← sq, ← hD.1 d hd, pow_orderOf_eq_one]
  have he1 : e * e = 1 := by rw [← sq, ← hD.1 e he, pow_orderOf_eq_one]
  have hsq : (d * e) * (d * e) = 1 := by
    rcases hD.2 d hd e he with h | h
    · rw [← sq, ← orderOf_dvd_iff_pow_eq_one]; exact h
    · obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hord
      have h1 : orderOf (d * e) = 1 := by
        have hj0 : j = 0 := by
          by_contra hj0
          exact h.not_two_dvd_nat (hj ▸ dvd_pow_self 2 hj0)
        rw [hj, hj0, pow_zero]
      rw [orderOf_eq_one_iff] at h1
      rw [h1, one_mul]
  have id : d⁻¹ = d := inv_eq_of_mul_eq_one_right hd1
  have ie : e⁻¹ = e := inv_eq_of_mul_eq_one_right he1
  have ide : (d * e)⁻¹ = d * e := inv_eq_of_mul_eq_one_right hsq
  show d * e = e * d
  rw [← ide, mul_inv_rev, id, ie]

theorem sq_eq_one_of_mem_closure {Y : Type} [Group Y] {S : Set Y}
    (hS2 : ∀ x ∈ S, x ^ 2 = 1) (hSc : ∀ x ∈ S, ∀ y ∈ S, Commute x y) :
    ∀ x ∈ closure S, x ^ 2 = 1 := by
  have hc1 : ∀ x ∈ closure S, ∀ y ∈ S, Commute x y := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx => exact fun y hy => hSc x hx y hy
    | one => exact fun y _ => Commute.one_left y
    | mul a b _ _ ha hb => exact fun y hy => (ha y hy).mul_left (hb y hy)
    | inv a _ ha => exact fun y hy => (ha y hy).inv_left
  have hc : ∀ x ∈ closure S, ∀ y ∈ closure S, Commute x y := by
    intro x hx y hy
    induction hy using Subgroup.closure_induction with
    | mem y hy => exact hc1 x hx y hy
    | one => exact Commute.one_right x
    | mul a b _ _ ha hb => exact ha.mul_right hb
    | inv a _ ha => exact ha.inv_right
  intro x hx
  induction hx using Subgroup.closure_induction with
  | mem x hx => exact hS2 x hx
  | one => exact one_pow 2
  | mul a b ha hb iha ihb => rw [(hc a ha b hb).mul_pow, iha, ihb, one_mul]
  | inv a _ iha => rw [inv_pow, iha, inv_one]

private theorem commT {Y : Type} [Group Y] {T : Subgroup Y} (hT2 : ∀ x ∈ T, x ^ 2 = 1) :
    ∀ x ∈ T, ∀ y ∈ T, x * y = y * x := by
  intro x hx y hy
  have h1 := hT2 x hx
  have h2 := hT2 y hy
  have h3 := hT2 (x * y) (T.mul_mem hx hy)
  rw [sq] at h1 h2 h3
  have ix : x⁻¹ = x := inv_eq_of_mul_eq_one_right h1
  have iy : y⁻¹ = y := inv_eq_of_mul_eq_one_right h2
  have ixy : (x * y)⁻¹ = x * y := inv_eq_of_mul_eq_one_right h3
  rw [← ixy, mul_inv_rev, ix, iy]

private theorem pow_conj_mem' {Y : Type} [Group Y] {T : Subgroup Y} {t : Y}
    (htT : ∀ x ∈ T, t * x * t⁻¹ ∈ T) (k : ℕ) : ∀ x ∈ T, t ^ k * x * (t ^ k)⁻¹ ∈ T := by
  induction k with
  | zero => intro x hx; simpa using hx
  | succ k ih =>
    intro x hx
    have := htT _ (ih x hx)
    rwa [show t * (t ^ k * x * (t ^ k)⁻¹) * t⁻¹ = t ^ (k + 1) * x * (t ^ (k + 1))⁻¹ by
      rw [pow_succ']; group] at this

private theorem pow_conj_fix'' {Y : Type} [Group Y] {t c : Y} (h : t * c * t⁻¹ = c) (k : ℕ) :
    t ^ k * c * (t ^ k)⁻¹ = c := by
  induction k with
  | zero => simp
  | succ k ih =>
    calc t ^ (k + 1) * c * (t ^ (k + 1))⁻¹ = t * (t ^ k * c * (t ^ k)⁻¹) * t⁻¹ := by
          rw [pow_succ']; group
      _ = c := by rw [ih, h]

theorem exists_t_complement {Y : Type} [Group Y] [Finite Y] {T C : Subgroup Y} {t : Y}
    (hT2 : ∀ x ∈ T, x ^ 2 = 1) (hCT : C ≤ T) (htT : ∀ x ∈ T, t * x * t⁻¹ ∈ T)
    (htC : ∀ c ∈ C, t * c * t⁻¹ = c) (hodd : Odd (orderOf t))
    (hfixC : ∀ y ∈ T, t * y * t⁻¹ = y → y ∈ C) :
    ∃ T₁ : Subgroup Y, T₁ ≤ T ∧ C ⊓ T₁ = ⊥ ∧ (∀ x ∈ T, ∃ c ∈ C, ∃ u ∈ T₁, x = c * u) ∧
      ∀ u ∈ T₁, t * u * t⁻¹ ∈ T₁ := by
  classical
  have hcomm := commT hT2
  letI : CommGroup T :=
    { (inferInstance : Group T) with mul_comm := fun a b => Subtype.ext (hcomm a a.2 b b.2) }
  have htkT := pow_conj_mem' htT
  set b := orderOf t with hb
  let g : T → ℕ → T := fun x k => ⟨t ^ k * x * (t ^ k)⁻¹, htkT k x x.2⟩
  let f : T → T := fun x => ∏ k ∈ Finset.range b, g x k
  have hfmul : ∀ x y : T, f (x * y) = f x * f y := by
    intro x y
    simp only [f]
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => Subtype.ext ?_
    simp only [g, Subgroup.coe_mul]
    group
  let N : T →* T := MonoidHom.mk' f hfmul
  let τ : T →* T :=
    { toFun := fun x => ⟨t * x * t⁻¹, htT x x.2⟩
      map_one' := by ext; simp
      map_mul' := by intro x y; ext; simp only [Subgroup.coe_mul]; group }
  have hτg : ∀ x k, τ (g x k) = g x (k + 1) := by
    intro x k
    ext
    show t * (t ^ k * x * (t ^ k)⁻¹) * t⁻¹ = t ^ (k + 1) * x * (t ^ (k + 1))⁻¹
    rw [pow_succ']; group
  have hgτ : ∀ x k, g (τ x) k = τ (g x k) := by
    intro x k
    ext
    show t ^ k * (t * x * t⁻¹) * (t ^ k)⁻¹ = t * (t ^ k * x * (t ^ k)⁻¹) * t⁻¹
    rw [show t ^ k * (t * x * t⁻¹) * (t ^ k)⁻¹ = t ^ (k + 1) * x * (t ^ (k + 1))⁻¹ by
        rw [pow_succ]; group,
      show t * (t ^ k * x * (t ^ k)⁻¹) * t⁻¹ = t ^ (k + 1) * x * (t ^ (k + 1))⁻¹ by
        rw [pow_succ']; group]
  have hgb : ∀ x, g x b = g x 0 := by
    intro x
    ext
    simp [g, hb, pow_orderOf_eq_one]
  have hτN : ∀ x, τ (N x) = N x := by
    intro x
    show τ (f x) = f x
    simp only [f]
    rw [map_prod]
    simp only [hτg]
    have h1 := Finset.prod_range_succ' (g x) b
    have h2 := Finset.prod_range_succ (g x) b
    rw [hgb x] at h2
    exact mul_right_cancel (h1.symm.trans h2)
  have hNτ : ∀ x, N (τ x) = τ (N x) := by
    intro x
    show f (τ x) = τ (f x)
    simp only [f]
    rw [map_prod]
    exact Finset.prod_congr rfl fun k _ => hgτ x k
  have hNC : ∀ x : T, ((N x : T) : Y) ∈ C := fun x =>
    hfixC _ (N x).2 (congrArg Subtype.val (hτN x))
  have hNid : ∀ x : T, (x : Y) ∈ C → N x = x := by
    intro x hx
    show f x = x
    have hgx : ∀ k, g x k = x := fun k => Subtype.ext (pow_conj_fix'' (htC x hx) k)
    simp only [f, hgx, Finset.prod_const, Finset.card_range]
    obtain ⟨m, hm⟩ := hodd
    rw [hm, pow_succ, pow_mul, show x ^ 2 = 1 from Subtype.ext (by simpa using hT2 x x.2),
      one_pow, one_mul]
  refine ⟨N.ker.map T.subtype, map_subtype_le _, ?_, ?_, ?_⟩
  · rw [eq_bot_iff]
    rintro y ⟨hyC, ⟨x, hx, rfl⟩⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker] at hx
    rw [mem_bot]
    have := hNid x hyC
    rw [hx] at this
    simp [← this]
  · intro x hx
    set c : T := N ⟨x, hx⟩
    refine ⟨c, hNC _, ((c⁻¹ * ⟨x, hx⟩ : T) : Y), ⟨c⁻¹ * ⟨x, hx⟩, ?_, rfl⟩, ?_⟩
    · rw [SetLike.mem_coe, MonoidHom.mem_ker, map_mul, map_inv, hNid c (hNC _), inv_mul_cancel]
    · simp
  · rintro _ ⟨x, hx, rfl⟩
    refine ⟨τ x, ?_, rfl⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker] at hx ⊢
    rw [hNτ, hx, map_one]

private theorem fpf_of_transitive' {G : Type*} [Group G] [Finite G] {Z : Subgroup G} {h : G}
    (hZ : 2 < Nat.card Z) (hZ2 : ∀ z ∈ Z, z ^ 2 = 1)
    (htr : ∀ z ∈ Z, z ≠ 1 → ∀ w ∈ Z, w ≠ 1 → ∃ k : ℕ, h ^ k * z * (h ^ k)⁻¹ = w) :
    ∀ z ∈ Z, h * z * h⁻¹ = z → z = 1 := by
  intro z hz hzh
  by_contra hz1
  obtain ⟨w, hw, hw1, hwz⟩ : ∃ w ∈ Z, w ≠ 1 ∧ w ≠ z := by
    by_contra hcon
    push Not at hcon
    have hle : Z ≤ zpowers z := fun w hw => by
      by_cases h1 : w = 1
      · rw [h1]; exact one_mem _
      · rw [hcon w hw h1]; exact mem_zpowers z
    have hc := Subgroup.card_le_of_le hle
    rw [Nat.card_zpowers] at hc
    have := orderOf_le_of_pow_eq_one (by norm_num) (hZ2 z hz)
    omega
  obtain ⟨k, hk⟩ := htr z hz hz1 w hw hw1
  have hfix : ∀ k : ℕ, h ^ k * z * (h ^ k)⁻¹ = z := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      calc h ^ (k + 1) * z * (h ^ (k + 1))⁻¹ = h * (h ^ k * z * (h ^ k)⁻¹) * h⁻¹ := by
            rw [pow_succ']; group
        _ = z := by rw [ih, hzh]
  rw [hfix k] at hk
  exact hwz hk.symm

private theorem conj_mul_conj {G : Type*} [Group G] (a b v : G) :
    a * b * v * (a * b)⁻¹ = a * (b * v * b⁻¹) * a⁻¹ := by group

theorem exists_torus {Y : Type} [Group Y] [Finite Y] {s : Y}
    (hD : IsOddTransp {x : Y | IsConj s x}) (hs : normalClosure ({s} : Set Y) = ⊤)
    {n : ℕ} (hn : 2 ≤ n) (hB : BorelData (Y ⧸ fusionZStar Y) (2 ^ n)) :
    fusionZStar Y ≠ ⊤ ∧ ∃ (T C T₁ : Subgroup Y) (t : Y),
      (∀ x ∈ T, x ^ 2 = 1) ∧ closure ({x | IsConj s x} ∩ (T : Set Y)) = T ∧
      (∀ d : Y, IsConj s d → ∃ g : Y, g * d * g⁻¹ ∈ T) ∧
      C ≤ T ∧ T₁ ≤ T ∧ C ⊓ T₁ = ⊥ ∧ (∀ x ∈ T, ∃ c ∈ C, ∃ u ∈ T₁, x = c * u) ∧
      C ≤ fusionZStar Y ∧ T₁ ⊓ fusionZStar Y = ⊥ ∧
      (∀ c ∈ C, t * c * t⁻¹ = c) ∧ (∀ u ∈ T₁, t * u * t⁻¹ ∈ T₁) ∧
      (∀ u ∈ T₁, u ≠ 1 → ∀ v ∈ T₁, v ≠ 1 → ∃ k : ℕ, t ^ k * u * (t ^ k)⁻¹ = v) ∧
      Nat.card T₁ = 2 ^ n := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Z := fusionZStar Y with hZdef
  set π : Y →* Y ⧸ Z := QuotientGroup.mk' Z with hπdef
  set D : Set Y := {x : Y | IsConj s x} with hDdef
  have hπ1 : ∀ y : Y, π y = 1 ↔ y ∈ Z := fun y => QuotientGroup.eq_one_iff y
  obtain ⟨Zh, hZh2, hZhc, hinv, hh, hhhN, hhhodd, -, hhhtr⟩ := hB
  have hq : 4 ≤ 2 ^ n := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hZh3 : 2 < Nat.card Zh := by omega
  have hZhcomm := commT hZh2
  have hDc : ∀ x ∈ D, ∀ g : Y, g * x * g⁻¹ ∈ D := fun x hx g =>
    (show IsConj s x from hx).trans (isConj_iff.mpr ⟨g, rfl⟩)
  have hZne : Z ≠ ⊤ := by
    intro hZt
    have hle : Zh ≤ ⊥ := by
      intro yh _
      obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective Z yh
      rw [mem_bot]
      exact (hπ1 y).mpr (hZt ▸ mem_top y)
    have := Subgroup.card_le_of_le hle
    rw [Subgroup.card_bot] at this
    omega
  refine ⟨hZne, ?_⟩
  have hDZ : ∀ x ∈ D, x ∉ Z := by
    intro x hx
    obtain ⟨g, rfl⟩ := isConj_iff.mp hx
    exact conj_not_mem_fusionZStar hs hZne g
  have hD2 : ∀ x ∈ D, x ^ 2 = 1 := fun x hx => by rw [← hD.1 x hx, pow_orderOf_eq_one]
  have hDinv : ∀ x ∈ D, orderOf (π x) = 2 := fun x hx =>
    orderOf_eq_prime (by rw [← map_pow, hD2 x hx, map_one])
      (fun h => hDZ x hx ((hπ1 x).mp h))
  have hπconj : ∀ g x : Y, π (g * x * g⁻¹) = π g * π x * (π g)⁻¹ := fun g x => by
    simp only [map_mul, map_inv]
  set RR := Zh.comap π with hRRdef
  obtain ⟨P₂, hP₂⟩ := CFSG.RankThree.PartTwo.Sec21.FF79.L41.exists_sylowOf_p (p := 2) RR
  have hP₂2 : IsPGroup 2 P₂ := hP₂.2.1
  have hP₂RR : P₂ ≤ RR := hP₂.1
  have hK2 : ∀ zh ∈ Zh, zh ≠ 1 → ∀ d ∈ D, ∃ g : Y, g * d * g⁻¹ ∈ P₂ ∧ π (g * d * g⁻¹) = zh := by
    intro zh hzh hzh1 d hd
    obtain ⟨gh, hgh⟩ := hinv (π d) (hDinv d hd)
    obtain ⟨g₁, rfl⟩ := QuotientGroup.mk'_surjective Z gh
    have hw : π (g₁ * d * g₁⁻¹) ∈ Zh := by rw [hπconj]; exact hgh
    have hw1 : π (g₁ * d * g₁⁻¹) ≠ 1 := fun h => hDZ _ (hDc d hd g₁) ((hπ1 _).mp h)
    obtain ⟨k, hk⟩ := hhhtr _ hw hw1 zh hzh hzh1
    obtain ⟨h₀, hh₀'⟩ := QuotientGroup.mk'_surjective Z hh
    have eh : π h₀ = hh := hh₀'
    set e₀ := (h₀ ^ k * g₁) * d * (h₀ ^ k * g₁)⁻¹ with he₀def
    have he₀ : π e₀ = zh := by
      rw [← hk, he₀def, hπconj, map_mul, map_pow, hπconj, eh]
      simp only [mul_inv_rev, mul_assoc]
    have he₀D : e₀ ∈ D := hDc d hd _
    have he₀R : e₀ ∈ RR := by
      show π e₀ ∈ Zh
      rw [he₀]; exact hzh
    have hQ : IsPGroup 2 (zpowers e₀) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hD.1 _ he₀D, pow_one])
    obtain ⟨k', hk'R, hk'⟩ := CFSG.RankThree.PartTwo.Sec21.FF79.L41.exists_conj_le_sylowOf_p hP₂
      (zpowers_le.mpr he₀R) hQ
    refine ⟨k' * (h₀ ^ k * g₁), ?_, ?_⟩
    · have := hk' e₀ (mem_zpowers e₀)
      rwa [he₀def, show k' * ((h₀ ^ k * g₁) * d * (h₀ ^ k * g₁)⁻¹) * k'⁻¹ =
        k' * (h₀ ^ k * g₁) * d * (k' * (h₀ ^ k * g₁))⁻¹ by group] at this
    · rw [show k' * (h₀ ^ k * g₁) * d * (k' * (h₀ ^ k * g₁))⁻¹ = k' * e₀ * k'⁻¹ by
        rw [he₀def]; group, hπconj, he₀]
      have hk'Z : π k' ∈ Zh := hk'R
      rw [hZhcomm _ hk'Z _ hzh, mul_assoc, mul_inv_cancel, mul_one]
  set T := closure (D ∩ (P₂ : Set Y)) with hTdef
  have hTP : T ≤ P₂ := (closure_le _).mpr fun x hx => hx.2
  have hT2 : ∀ x ∈ T, x ^ 2 = 1 := sq_eq_one_of_mem_closure (fun x hx => hD2 x hx.1)
    (fun x hx y hy => commute_of_oddTransp_of_isPGroup hD hP₂2 hx.1 hy.1 hx.2 hy.2)
  have hTgen : closure (D ∩ (T : Set Y)) = T :=
    le_antisymm ((closure_le _).mpr fun x hx => hx.2)
      (closure_mono fun x hx => ⟨hx.1, subset_closure hx⟩)
  obtain ⟨zh₀, hzh₀, hzh₀1⟩ : ∃ zh ∈ Zh, zh ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have : Zh ≤ ⊥ := fun x hx => (mem_bot).mpr (hcon x hx)
    have := Subgroup.card_le_of_le this
    rw [Subgroup.card_bot] at this
    omega
  have hconj : ∀ d : Y, IsConj s d → ∃ g : Y, g * d * g⁻¹ ∈ T := fun d hd => by
    obtain ⟨g, hg, -⟩ := hK2 zh₀ hzh₀ hzh₀1 d hd
    exact ⟨g, subset_closure ⟨hDc d hd g, hg⟩⟩
  have hTZh : ∀ x ∈ T, π x ∈ Zh := fun x hx => hP₂RR (hTP hx)
  have hTsurj : ∀ zh ∈ Zh, ∃ x ∈ T, π x = zh := by
    intro zh hzh
    by_cases hzh1 : zh = 1
    · exact ⟨1, one_mem _, by rw [map_one, hzh1]⟩
    obtain ⟨g, hg, hgz⟩ := hK2 zh hzh hzh1 s (IsConj.refl s)
    exact ⟨_, subset_closure ⟨hDc s (IsConj.refl s) g, hg⟩, hgz⟩
  have hTR : ∀ x ∈ T, x ∈ fusionOddCore Y → x = 1 := by
    intro x hx hxR
    have h1 : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one (hT2 x hx)
    have h2 : orderOf x ∣ Nat.card (fusionOddCore Y) := by
      have := Subgroup.orderOf_dvd_natCard (fusionOddCore Y) hxR
      exact this
    have hodd := CFSG.CGT.Timmesfeld75.odd_card_fusionOddCore Y
    have h3 : Odd (orderOf x) := Odd.of_dvd_nat hodd h2
    rcases (Nat.dvd_prime Nat.prime_two).mp h1 with h | h
    · exact orderOf_eq_one_iff.mp h
    · rw [h] at h3; exact absurd h3 (by decide)
  obtain ⟨h₀, hh₀⟩ := QuotientGroup.mk'_surjective Z hh
  have hhhpow : ∀ j : ℕ, ∀ v ∈ Zh, hh ^ j * v * (hh ^ j)⁻¹ ∈ Zh := fun j v hv =>
    (mem_normalizer_iff.mp (pow_mem hhhN j) v).mp hv
  have hh₀N : h₀ ∈ CFSG.RankThree.PartTwo.Sec21.FF79.Nor RR :=
    CFSG.RankThree.PartTwo.Sec21.FF79.L41.mem_nor_of_forall fun y hy => by
      show π (h₀ * y * h₀⁻¹) ∈ Zh
      rw [hπconj]
      have : π h₀ = hh := hh₀
      rw [this]
      simpa using hhhpow 1 _ hy
  obtain ⟨k₀, hk₀R, hm⟩ := CFSG.RankThree.PartTwo.Sec21.FF79.S3.exists_frattini hP₂ hh₀N
  set m := k₀ * h₀ with hmdef
  have hπm : ∀ v ∈ Zh, π m * v * (π m)⁻¹ = hh * v * hh⁻¹ := by
    intro v hv
    have hk₀Z : π k₀ ∈ Zh := hk₀R
    have h1 : hh * v * hh⁻¹ ∈ Zh := by simpa using hhhpow 1 v hv
    rw [hmdef, map_mul, show π h₀ = hh from hh₀,
      conj_mul_conj (π k₀) hh v,
      hZhcomm _ hk₀Z _ h1, mul_assoc, mul_inv_cancel, mul_one]
  have hpowact : ∀ j : ℕ, ∀ v ∈ Zh, (π m) ^ j * v * ((π m) ^ j)⁻¹ = hh ^ j * v * (hh ^ j)⁻¹ := by
    intro j
    induction j with
    | zero => intro v _; simp
    | succ j ih =>
      intro v hv
      rw [pow_succ', pow_succ', show π m * (π m) ^ j * v * (π m * (π m) ^ j)⁻¹ =
          π m * ((π m) ^ j * v * ((π m) ^ j)⁻¹) * (π m)⁻¹ from conj_mul_conj _ _ _, ih v hv,
        hπm _ (hhhpow j v hv)]
      exact (conj_mul_conj hh (hh ^ j) v).symm
  obtain ⟨a, b, hbodd, hab⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos m).ne'
  set t := m ^ (2 ^ a) with htdef
  have htord : orderOf t = b := by
    rw [htdef, orderOf_pow_of_dvd (pow_ne_zero _ two_ne_zero) ⟨b, hab⟩, hab,
      Nat.mul_div_cancel_left _ (pow_pos two_pos a)]
  have htodd : Odd (orderOf t) := htord ▸ hbodd
  have htN : t ∈ normalizer ((P₂ : Subgroup Y) : Set Y) := pow_mem hm _
  obtain ⟨jj, hjj⟩ : ∃ jj : ℕ, hh ^ (2 ^ a * jj) = hh := by
    by_cases ho : orderOf hh = 1
    · exact ⟨0, by rw [orderOf_eq_one_iff.mp ho, one_pow]⟩
    have hcop : Nat.Coprime (2 ^ a) (orderOf hh) :=
      Nat.Coprime.pow_left a (Nat.coprime_two_left.mpr hhhodd)
    obtain ⟨jj, -, hjj⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop
      (lt_of_le_of_ne (orderOf_pos hh) (Ne.symm ho))
    exact ⟨jj, by rw [← pow_mod_orderOf, hjj, pow_one]⟩
  have hπt : ∀ K : ℕ, π (t ^ K) = (π m) ^ (2 ^ a * K) := fun K => by
    rw [htdef, ← pow_mul, map_pow]
  have htrπ : ∀ u ∈ Zh, u ≠ 1 → ∀ v ∈ Zh, v ≠ 1 →
      ∃ K : ℕ, π (t ^ K) * u * (π (t ^ K))⁻¹ = v := by
    intro u hu hu1 v hv hv1
    obtain ⟨k, hk⟩ := hhhtr u hu hu1 v hv hv1
    refine ⟨jj * k, ?_⟩
    rw [hπt, hpowact _ u hu, ← mul_assoc, pow_mul, hjj]
    exact hk
  have hfpfπ : ∀ v ∈ Zh, π t * v * (π t)⁻¹ = v → v = 1 := by
    have := fpf_of_transitive' (h := π t) hZh3 hZh2 (fun u hu hu1 v hv hv1 => by
      obtain ⟨K, hK⟩ := htrπ u hu hu1 v hv hv1
      exact ⟨K, by rw [← map_pow]; exact hK⟩)
    exact this
  have htT : ∀ x ∈ T, t * x * t⁻¹ ∈ T := by
    have hle : T ≤ T.comap (MulAut.conj t).toMonoidHom := by
      rw [hTdef, closure_le]
      intro x hx
      show t * x * t⁻¹ ∈ T
      exact subset_closure ⟨hDc x hx.1 t, (mem_normalizer_iff.mp htN x).mp hx.2⟩
    intro x hx
    have := hle hx
    simpa [MulAut.conj_apply] using this
  set C := T ⊓ Z with hCdef
  have htC : ∀ c ∈ C, t * c * t⁻¹ = c := by
    intro c hc
    have hcZ : QuotientGroup.mk' (fusionOddCore Y) c ∈ center (Y ⧸ fusionOddCore Y) := hc.2
    have hcomR : t * c * t⁻¹ * c⁻¹ ∈ fusionOddCore Y := by
      rw [← QuotientGroup.eq_one_iff]
      have h := (mem_center_iff.mp hcZ) (QuotientGroup.mk' (fusionOddCore Y) t)
      simp only [QuotientGroup.mk'_apply] at h
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
        QuotientGroup.mk_inv, QuotientGroup.mk_inv, h]
      group
    have hcomT : t * c * t⁻¹ * c⁻¹ ∈ T := T.mul_mem (htT c hc.1) (T.inv_mem hc.1)
    have := hTR _ hcomT hcomR
    calc t * c * t⁻¹ = t * c * t⁻¹ * c⁻¹ * c := by group
      _ = c := by rw [this, one_mul]
  have hfixC : ∀ y ∈ T, t * y * t⁻¹ = y → y ∈ C := by
    intro y hy hty
    refine ⟨hy, (hπ1 y).mp (hfpfπ _ (hTZh y hy) ?_)⟩
    rw [← hπconj, hty]
  obtain ⟨T₁, hT₁T, hCT₁, hdec, htT₁⟩ :=
    exists_t_complement hT2 inf_le_left htT htC htodd hfixC
  have hT₁Z : T₁ ⊓ Z = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hx1, hxZ⟩
    have : x ∈ C ⊓ T₁ := ⟨⟨hT₁T hx1, hxZ⟩, hx1⟩
    rwa [hCT₁] at this
  have hinjT₁ : ∀ x ∈ T₁, ∀ y ∈ T₁, π x = π y → x = y := by
    intro x hx y hy hxy
    have hm1 : x * y⁻¹ ∈ T₁ ⊓ Z := ⟨T₁.mul_mem hx (T₁.inv_mem hy),
      (hπ1 _).mp (by rw [map_mul, map_inv, hxy, mul_inv_cancel])⟩
    rw [hT₁Z, mem_bot] at hm1
    exact mul_inv_eq_one.mp hm1
  have htkT₁ := pow_conj_mem' htT₁
  refine ⟨T, C, T₁, t, hT2, hTgen, hconj, inf_le_left, hT₁T, hCT₁, hdec, inf_le_right, hT₁Z,
    htC, htT₁, ?_, ?_⟩
  · intro u hu hu1 v hv hv1
    have hπu : π u ≠ 1 := fun h => hu1 (by
      have : u ∈ T₁ ⊓ Z := ⟨hu, (hπ1 u).mp h⟩
      rwa [hT₁Z, mem_bot] at this)
    have hπv : π v ≠ 1 := fun h => hv1 (by
      have : v ∈ T₁ ⊓ Z := ⟨hv, (hπ1 v).mp h⟩
      rwa [hT₁Z, mem_bot] at this)
    obtain ⟨K, hK⟩ := htrπ _ (hTZh u (hT₁T hu)) hπu _ (hTZh v (hT₁T hv)) hπv
    refine ⟨K, hinjT₁ _ (htkT₁ K u hu) _ hv ?_⟩
    rw [hπconj]; exact hK
  · rw [← hZhc]
    refine Nat.card_eq_of_bijective (fun u : T₁ => (⟨π u, hTZh u (hT₁T u.2)⟩ : Zh))
      ⟨fun x y hxy => Subtype.ext (hinjT₁ x x.2 y y.2 (congrArg Subtype.val hxy)), ?_⟩
    rintro ⟨zh, hzh⟩
    obtain ⟨x, hx, rfl⟩ := hTsurj zh hzh
    obtain ⟨c, hc, u, hu, rfl⟩ := hdec x hx
    refine ⟨⟨u, hu⟩, Subtype.ext ?_⟩
    show π u = π (c * u)
    rw [map_mul, (hπ1 c).mpr hc.2, one_mul]

open CFSG.Open Subgroup
open CFSG.Timmesfeld.Bridge.Asc72

theorem le_center_or_frame {Y : Type} [Group Y] [Finite Y] {s : Y}
    (hD : IsOddTransp {x : Y | IsConj s x}) (hs : normalClosure ({s} : Set Y) = ⊤) {n : ℕ}
    (hn : 1 < n) (hL : CFSG.LocalAnalysis.WeakClosure81.SevenK.IsL2OrSz (Y ⧸ fusionZStar Y) n) :
    fusionOddCore Y ≤ center Y ∨
      (n = 2 ∧ ∃ d₁ d₂ d₃ t : Y, CFSG.LocalAnalysis.WeakClosure81.OddCentral.IsFrame s d₁ d₂ d₃ t) := by
  haveI : Finite (Y ⧸ fusionZStar Y) := Finite.of_surjective _ (QuotientGroup.mk'_surjective (fusionZStar Y))
  have hB := borelData_of_isL2OrSz hn hL
  obtain ⟨hZ, T, C, T₁, t, hT2, hTgen, hconj, hCT, hT₁T, hCT₁, hdec, hCZ, hT₁Z, htC, htT₁, htr,
    hcard⟩ := exists_torus hD hs (by omega) hB
  exact le_center_or_frame_of_torus hD hs hZ (by omega) hT2 hTgen hconj hCT hT₁T hCT₁ hdec hCZ
    hT₁Z htC htT₁ htr hcard

end CFSG.LocalAnalysis.WeakClosure81.OddCentral

