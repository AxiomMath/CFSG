module

public import CFSG.Timmesfeld.Transvection.Sp4Root
public import CFSG.Timmesfeld.Transvection.TriangleApex
public import CFSG.Timmesfeld.Transvection.CoprimeSplit

public section

namespace CFSG.Timmesfeld.Transvection

open CFSG.Timmesfeld.ARS CFSG.Timmesfeld.ARS.NaturalModule CFSG.Timmesfeld.RankOne

variable {G : Type*} [Group G] {Δ : Set (Subgroup G)}

namespace SL2Coords

variable {A E : Subgroup G} {k : ℕ} (φ : SL2Coords A E k)

theorem mat_pow {x : G} (hx : x ∈ A ⊔ E) (n : ℕ) : φ.mat (x ^ n) = φ.mat x ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, φ.mat_one]
  | succ n ih => rw [pow_succ, φ.mat_mul (Subgroup.pow_mem _ hx n) hx, ih, pow_succ]

theorem conjSub_eq_of_mat_eq_diagElt [Finite G] {h : G} (hX : h ∈ A ⊔ E) {μ : (GaloisField 2 k)ˣ}
    (hh : φ.mat h = diagElt μ) : conjSub A h = A ∧ conjSub E h = E := by
  have key : ∀ {P : Subgroup G}, P ≤ A ⊔ E →
      ∀ {U : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 k))},
      (∀ {x : G}, x ∈ A ⊔ E → (x ∈ P ↔ φ.mat x ∈ U)) →
      diagElt μ ∈ Subgroup.normalizer (U : Set _) → conjSub P h = P := by
    intro P hP U hU hnorm
    have hle : conjSub P h ≤ P := by
      rintro _ ⟨a, ha, rfl⟩
      show h * a * h⁻¹ ∈ P
      have haX : a ∈ A ⊔ E := hP ha
      have hX' : h * a ∈ A ⊔ E := Subgroup.mul_mem _ hX haX
      rw [hU (Subgroup.mul_mem _ hX' (Subgroup.inv_mem _ hX)), φ.mat_mul hX'
        (Subgroup.inv_mem _ hX), φ.mat_mul hX haX, φ.mat_inv hX, hh]
      exact (Subgroup.mem_normalizer_iff.1 hnorm _).1 ((hU haX).1 ha)
    exact Subgroup.eq_of_le_of_card_ge hle
      (Subgroup.card_map_of_injective (MulAut.conj h).injective).ge
  exact ⟨key le_sup_left (fun hx => φ.mem_A_iff hx) (diagElt_mem_normalizer_lowerUnipotent μ),
    key le_sup_right (fun hx => φ.mem_E_iff hx) (diagElt_mem_normalizer_upperUnipotent μ)⟩

theorem eq_one_of_commute_of_mat_eq_diagElt {h : G} (hX : h ∈ A ⊔ E) {μ : (GaloisField 2 k)ˣ}
    (hh : φ.mat h = diagElt μ) (hμ1 : μ ≠ 1) {a : G} (ha : a ∈ A) (hc : Commute a h) :
    a = 1 := by
  have haX : a ∈ A ⊔ E := Subgroup.mem_sup_left ha
  obtain ⟨c, hcA⟩ := (mem_lowerUnipotent_iff (GaloisField 2 k)).1 ((φ.mem_A_iff haX).1 ha)
  have h1 : φ.mat (h * a) = φ.mat (a * h) := by rw [hc.eq]
  rw [φ.mat_mul hX haX, φ.mat_mul haX hX, hh, hcA, diagElt_mul_lowerElt] at h1
  have h2 := mul_right_cancel h1
  have h3 := lowerElt_injective (GaloisField 2 k) h2
  have hμ2 : ((μ⁻¹ : (GaloisField 2 k)ˣ) : GaloisField 2 k) ^ 2 ≠ 1 := by
    intro h4
    apply hμ1
    have h5 : ((μ⁻¹ : (GaloisField 2 k)ˣ) : GaloisField 2 k) = 1 := by
      apply frobenius_inj (GaloisField 2 k) 2
      rw [frobenius_def, frobenius_def, h4, one_pow]
    have := Units.val_eq_one.1 h5
    rwa [inv_eq_one] at this
  have hc0 : c = 0 := by
    have h8 : (((μ⁻¹ : (GaloisField 2 k)ˣ) : GaloisField 2 k) ^ 2 - 1) * c = 0 := by
      rw [sub_mul, one_mul, h3, sub_self]
    exact (mul_eq_zero.1 h8).resolve_left (sub_ne_zero.2 hμ2)
  rw [hc0, lowerElt_zero] at hcA
  exact φ.mat_inj haX hcA

theorem odd_orderOf_of_mat_eq_diagElt [Finite G] (hk0 : k ≠ 0) {h : G} (hX : h ∈ A ⊔ E)
    {μ : (GaloisField 2 k)ˣ} (hh : φ.mat h = diagElt μ) : Odd (orderOf h) := by
  have hcard : Nat.card (GaloisField 2 k) = 2 ^ k := GaloisField.card 2 k hk0
  let _ : Fintype (GaloisField 2 k) := Fintype.ofFinite _
  have hμq : μ ^ (2 ^ k - 1) = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one]
    have := FiniteField.pow_card_sub_one_eq_one (μ : GaloisField 2 k) μ.ne_zero
    rwa [← Nat.card_eq_fintype_card, hcard] at this
  have h1 : h ^ (2 ^ k - 1) = 1 := by
    refine φ.mat_inj (Subgroup.pow_mem _ hX _) ?_
    rw [φ.mat_pow hX, hh, diagElt_pow, hμq, diagElt_one]
  have hodd : Odd (2 ^ k - 1) := by
    have : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk0
    refine ⟨2 ^ j - 1, ?_⟩
    have : 1 ≤ 2 ^ j := Nat.one_le_two_pow
    rw [pow_succ]
    omega
  exact hodd.of_dvd_nat (orderOf_dvd_of_pow_eq_one h1)

end SL2Coords

theorem exists_card_eq_two_pow_of_opposite [Finite G] (hR : IsRootClass Δ) {A E : Subgroup G}
    (hA : A ∈ Δ) (hE : E ∈ Δ) (hEA : Opposite E A) : ∃ k : ℕ, Nat.card A = 2 ^ k := by
  obtain ⟨n, -, hcard, -⟩ := ARS.Opposite.exists_mulEquiv_SL2' hR hE hEA
  exact ⟨n, (hR.card_eq hA hE).trans hcard⟩

theorem exists_unit_ne_one_of_card {A : Subgroup G} {k : ℕ} (hk : Nat.card A = 2 ^ k)
    (hq : 4 ≤ Nat.card A) : ∃ μ : (GaloisField 2 k)ˣ, μ ≠ 1 := by
  classical
  by_contra hno
  push Not at hno
  have hk0 : k ≠ 0 := by
    intro h0
    rw [h0, pow_zero] at hk
    omega
  let _ : Fintype (GaloisField 2 k) := Fintype.ofFinite _
  have h2 : Fintype.card (GaloisField 2 k)ˣ = 1 := Fintype.card_eq_one_iff.2 ⟨1, hno⟩
  rw [Fintype.card_units] at h2
  have h3 : Fintype.card (GaloisField 2 k) = Nat.card A := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card 2 k hk0, hk]
  omega

theorem commute_of_mem_sup_left {A E D : Subgroup G} (hAD : Commuting A D) (hED : Commuting E D)
    {x : G} (hx : x ∈ A ⊔ E) {d : G} (hd : d ∈ D) : Commute d x :=
  commute_of_mem_sup_of_commute (fun a ha => (hAD a ha d hd).symm)
    (fun e he => (hED e he d hd).symm) hx

namespace TriangleSetting

variable {A E B : Subgroup G} {t : G}

theorem centralizer_corrN_spec [Finite G] (S : TriangleSetting Δ A E B t) (htY : t ∈ A ⊔ E ⊔ B)
    (hq : 4 ≤ Nat.card A) (hpts : PointsDetermined Δ) (c : S.Coords) {h : G} (hh : h ∈ A ⊔ E)
    {μ : (GaloisField 2 c.k)ˣ} (hμ : c.mat h = diagElt μ) (hμ1 : μ ≠ 1) :
    (∀ m ∈ corrN A E t ⊓ Subgroup.centralizer (A : Set G), (Commute m h ↔
      m ∈ corrN A E t ⊓ Subgroup.centralizer ((A ⊔ E : Subgroup G) : Set G))) ∧
    corrN A E t ⊓ Subgroup.centralizer (A : Set G) =
      (corrN A E t ⊓ Subgroup.centralizer ((A ⊔ E : Subgroup G) : Set G)) ⊔
        commSub (corrN A E t ⊓ Subgroup.centralizer (A : Set G)) h ∧
    (corrN A E t ⊓ Subgroup.centralizer ((A ⊔ E : Subgroup G) : Set G)) ⊓
      commSub (corrN A E t ⊓ Subgroup.centralizer (A : Set G)) h = ⊥ ∧
    Nat.card (commSub (corrN A E t ⊓ Subgroup.centralizer (A : Set G)) h) = Nat.card A := by
  classical
  obtain ⟨hhA, -⟩ := c.conjSub_eq_of_mat_eq_diagElt hh hμ
  set N := corrN A E t with hN
  set C := N ⊓ Subgroup.centralizer (A : Set G) with hC
  set Z := N ⊓ Subgroup.centralizer ((A ⊔ E : Subgroup G) : Set G) with hZ
  have hCab : ∀ x ∈ C, ∀ y ∈ C, Commute x y := fun x hx y hy =>
    S.commute_of_mem_corrN' htY hq hx.1 hy.1
  have hhinvA : conjSub A h⁻¹ = A := conjSub_inv_eq hhA
  have hCh : ∀ x ∈ C, h * x * h⁻¹ ∈ C := by
    intro x hx
    refine ⟨conj_mem_corrN hh hx.1, Subgroup.mem_centralizer_iff.2 fun a ha => ?_⟩
    have ha' : h⁻¹ * a * h ∈ A := by
      have := conj_mem_conjSub h⁻¹ ha
      rwa [hhinvA, inv_inv] at this
    have hc := Subgroup.mem_centralizer_iff.1 hx.2 _ ha'
    calc a * (h * x * h⁻¹) = h * ((h⁻¹ * a * h) * x) * h⁻¹ := by group
      _ = h * (x * (h⁻¹ * a * h)) * h⁻¹ := by rw [hc]
      _ = h * x * h⁻¹ * a := by group
  have hvecC : ∀ {m : G}, m ∈ C → c.vec m 0 = 0 := fun hm =>
    (c.commute_A_iff hm.1).1 fun a ha => (Subgroup.mem_centralizer_iff.1 hm.2 a ha).symm
  have hvecm : ∀ {m : G}, m ∈ C → c.vec (m * h * m⁻¹ * h⁻¹) 1 =
      (1 - ((μ⁻¹ : (GaloisField 2 c.k)ˣ) : GaloisField 2 c.k)) * c.vec m 1 := by
    intro m hm
    have hm' : h * m⁻¹ * h⁻¹ ∈ N := conj_mem_corrN hh (Subgroup.inv_mem _ hm.1)
    rw [show m * h * m⁻¹ * h⁻¹ = m * (h * m⁻¹ * h⁻¹) by group, c.vec_mul hm.1 hm',
      c.vec_conj_diagElt hh hμ (Subgroup.inv_mem _ hm.1), c.vec_inv hm.1]
    simp only [Pi.add_apply, Pi.neg_apply, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    ring
  have hμ1' : ((μ⁻¹ : (GaloisField 2 c.k)ˣ) : GaloisField 2 c.k) ≠ 1 := by
    intro h1
    apply hμ1
    have := Units.val_eq_one.1 h1
    rwa [inv_eq_one] at this
  have hsub : (1 : GaloisField 2 c.k) - ((μ⁻¹ : (GaloisField 2 c.k)ˣ) : GaloisField 2 c.k) ≠ 0 :=
    sub_ne_zero.2 (Ne.symm hμ1')
  have hkey : ∀ {m : G}, m ∈ C → c.vec (m * h * m⁻¹ * h⁻¹) = 0 → m ∈ Z := by
    intro m hm h0
    have h1 : c.vec m 1 = 0 := by
      have := congrFun h0 1
      simp only [Pi.zero_apply] at this
      rw [hvecm hm] at this
      exact (mul_eq_zero.1 this).resolve_left hsub
    have h2 : c.vec m = 0 := by
      funext i
      fin_cases i
      · exact hvecC hm
      · exact h1
    exact ⟨hm.1, (c.vec_eq_zero_iff hm.1).1 h2⟩
  have hZY : ∀ {z : G}, z ∈ Z → ∀ {y : G}, y ∈ A ⊔ E ⊔ B → Commute z y := fun hz _ hy =>
    S.commute_of_mem_corrN_inf_centralizer htY hq hz hy
  have hZh : ∀ {z : G}, z ∈ Z → Commute z h := fun hz => hZY hz (Subgroup.mem_sup_left hh)
  have hZC : Z ≤ C := fun z hz => ⟨hz.1, Subgroup.mem_centralizer_iff.2 fun a ha =>
    Subgroup.mem_centralizer_iff.1 hz.2 a (Subgroup.mem_sup_left ha)⟩
  have hFC : graph A t ≤ C := fun f hf => ⟨corrM_le_corrN (graph_le_corrM hf),
    Subgroup.mem_centralizer_iff.2 fun a ha => (S.commute_graph_left hf ha).symm.eq⟩
  have hCFZ : C = graph A t ⊔ Z := le_antisymm (fun m hm => S.mem_graph_sup_of_commute htY hq
    hm.1 fun a ha => (Subgroup.mem_centralizer_iff.1 hm.2 a ha).symm) (sup_le hFC hZC)
  have hcardZ : Nat.card Z = Nat.card A := S.card_corrN_inf_centralizer_eq htY hq hpts
  have hcardC : Nat.card C = Nat.card A * Nat.card A := by
    have hFZ : graph A t ⊓ Z = ⊥ := by
      refine (Subgroup.eq_bot_iff_forall _).2 fun x hx => ?_
      have hx' : x ∈ Z ⊓ (A ⊔ B) := ⟨hx.2, S.graph_le_sup_right hx.1⟩
      rwa [S.corrN_inf_centralizer_inf_sup_eq_bot, Subgroup.mem_bot] at hx'
    have hFZc : Commuting (graph A t) Z := fun f hf z hz => (hZY hz (S.graph_le_sup hf)).symm
    rw [hCFZ, le_antisymm (card_sup_le_of_commuting hFZc) (card_mul_card_le_card_sup hFZ),
      S.card_graph, hcardZ]
  have hiff : ∀ m ∈ C, (Commute m h ↔ m ∈ Z) := fun m hm =>
    ⟨fun hmh => hkey hm (by
      rw [show m * h * m⁻¹ * h⁻¹ = 1 by rw [hmh.eq]; group, c.vec_one]), fun hmZ => hZh hmZ⟩
  have hker : (commMap hCab hCh).ker = Z.subgroupOf C := by
    ext m
    rw [mem_ker_commMap_iff, Subgroup.mem_subgroupOf]
    exact hiff m m.2
  have hcardX : Nat.card (commSub C h) = Nat.card A := by
    have h1 := card_range_commMap_mul hCab hCh
    rw [hker, card_subgroupOf_of_le hZC, hcardZ, hcardC] at h1
    rw [card_commSub hCab hCh]
    exact Nat.eq_of_mul_eq_mul_right (by omega) h1
  have hXC := commSub_le hCab hCh
  have hZX : Z ⊓ commSub C h = ⊥ := by
    refine (Subgroup.eq_bot_iff_forall _).2 fun x hx => ?_
    obtain ⟨m, hm, rfl⟩ := (mem_commSub_iff hCab hCh).1 hx.2
    have hmZ := hkey hm ((c.vec_eq_zero_iff hx.1.1).2 hx.1.2)
    rw [(hZh hmZ).eq]
    group
  have hZXc : Commuting Z (commSub C h) := fun z hz x hx => hCab z (hZC hz) x (hXC hx)
  have hCZX : C = Z ⊔ commSub C h := by
    refine (Subgroup.eq_of_le_of_card_ge (sup_le hZC hXC) ?_).symm
    rw [le_antisymm (card_sup_le_of_commuting hZXc) (card_mul_card_le_card_sup hZX), hcardZ,
      hcardX, hcardC]
  exact ⟨hiff, hCZX, hZX, hcardX⟩

theorem le_sup_inf_centralizer (S : TriangleSetting Δ A E B t) :
    B ≤ A ⊔ (corrN A E t ⊓ Subgroup.centralizer (A : Set G)) := by
  intro b hb
  have ha : t⁻¹ * b * t ∈ A := by
    rw [← S.conjA] at hb
    obtain ⟨a, ha, rfl⟩ := mem_conjSub_iff.1 hb
    rwa [show t⁻¹ * (t * a * t⁻¹) * t = a by group]
  have hf : t⁻¹ * b * t * (t * (t⁻¹ * b * t) * t⁻¹) ∈ graph A t :=
    (mem_graph_iff S.commuting_conjSub).2 ⟨_, ha, rfl⟩
  have hb' : b = (t⁻¹ * b * t)⁻¹ * (t⁻¹ * b * t * (t * (t⁻¹ * b * t) * t⁻¹)) := by group
  rw [hb']
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (A.inv_mem ha)) (Subgroup.mem_sup_right
    ⟨corrM_le_corrN (graph_le_corrM hf), Subgroup.mem_centralizer_iff.2 fun a' ha' =>
      (S.commute_graph_left hf ha').symm.eq⟩)

theorem inf_centralizer_le_corrL [Finite G] (S : TriangleSetting Δ A E B t)
    (htY : t ∈ A ⊔ E ⊔ B) (hq : 4 ≤ Nat.card A) (hpts : PointsDetermined Δ) :
    corrN A E t ⊓ Subgroup.centralizer (A : Set G) ≤ corrL A E t := by
  intro x hx
  rw [← S.sup_corrN_inf_centralizer_eq htY hq hpts]
  exact (sup_le (S.graph_le_sup_right.trans (sup_le (le_sup_left.trans le_sup_left)
    (le_sup_right.trans le_sup_left))) le_sup_right) (S.mem_graph_sup_of_commute htY hq hx.1
      fun a ha => (Subgroup.mem_centralizer_iff.1 hx.2 a ha).symm)

theorem corrL_le_lineGroup [Finite G] (S : TriangleSetting Δ A E B t) (htY : t ∈ A ⊔ E ⊔ B)
    (hq : 4 ≤ Nat.card A) (hpts : PointsDetermined Δ) {D : Subgroup G}
    (hD : D ∈ lineOf Δ A B) (hDE : Commuting D E) : corrL A E t ≤ lineGroup Δ A B := by
  have hDA : D ≠ A := by
    rintro rfl
    exact ModelRank.not_commuting_of_opposite S.tri.oppA hDE.symm
  have hDB : D ≠ B := by
    rintro rfl
    exact ModelRank.not_commuting_of_opposite S.tri.oppB hDE.symm
  rw [← S.sup_sup_eq_corrL htY hq hpts S.tri.memA S.tri.memB hD.1 Transvection.le_corrL
    S.le_corrL_right (S.le_corrL_of_mem_lineOf htY hq hpts hD hDE) S.tri.ne (Ne.symm hDA)
    (Ne.symm hDB)]
  exact sup_le (sup_le (le_lineGroup (left_mem_lineOf S.tri.memA))
    (le_lineGroup (right_mem_lineOf S.tri.memB))) (le_lineGroup hD)

end TriangleSetting

theorem commSub_mono {C C' : Subgroup G} (hCC' : C ≤ C') (h : G) : commSub C h ≤ commSub C' h :=
  Subgroup.closure_mono fun _ ⟨m, hm, hx⟩ => ⟨m, hCC' hm, hx⟩

theorem lineGroup_eq_of_mem_of_ne [Finite G] (hΔ : IsTransvectionClass Δ)
    (hpts : PointsDetermined Δ) {A B B' : Subgroup G} (hA : A ∈ Δ) (hB : B ∈ Δ) (hAB : A ≠ B)
    (hcAB : Commuting A B) (hB' : B' ∈ lineOf Δ A B) (hB'A : B' ≠ A) :
    lineGroup Δ A B' = lineGroup Δ A B := by
  rw [lineGroup, lineGroup, lineOf_eq_of_mem_of_ne hΔ hpts hA hB hAB hcAB hB' hB'A]

theorem Sp4Frame.corrL_le_lineGroup [Finite G] {A E D E' B : Subgroup G}
    (F : Sp4Frame Δ A E D E' B) (hpts : PointsDetermined Δ) {t : G}
    (S : TriangleSetting Δ A E B t) (htY : t ∈ A ⊔ E ⊔ B) (hq : 4 ≤ Nat.card A) :
    corrL A E t ≤ lineGroup Δ A D := by
  rw [F.corrL_eq_sup S.cls hpts S htY hq]
  exact sup_le (sup_le (le_lineGroup (left_mem_lineOf F.memA))
    (le_lineGroup (right_mem_lineOf F.memD))) (le_lineGroup F.memB)

theorem isTriangle_of_mem_lineOf [Finite G] (hΔ : IsTransvectionClass Δ) (hpts : PointsDetermined Δ)
    {A E D : Subgroup G} (hA : A ∈ Δ) (hE : E ∈ Δ) (hEA : Opposite E A) (hAD : Commuting A D)
    (hED : Commuting E D) (hD : D ∈ Δ) (hDA : D ≠ A) {B : Subgroup G}
    (hB : B ∈ lineOf Δ A D) (hBA : B ≠ A) (hBD : B ≠ D) :
    IsTriangle Δ A E B ∧ D ∈ lineOf Δ A B := by
  have hlD : lineOf Δ A B = lineOf Δ A D :=
    lineOf_eq_of_mem_of_ne hΔ hpts hA hD (Ne.symm hDA) hAD hB hBA
  have hAB : Commuting A B := (commuting_of_mem_lineOf' hΔ hA hD hAD hB).1
  have hEne : E ≠ ⊥ := hΔ.root.ne_bot E hE
  refine ⟨⟨hA, hE, hB.1, Ne.symm hBA, hAB, hEA, ?_⟩, hlD ▸ right_mem_lineOf hD⟩
  have hEB : E ≠ B := by
    rintro rfl
    exact hEA.not_commuting hEne hAB.symm
  rcases hΔ.commuting_or_opposite hE hB.1 hEB with h | h
  · exact absurd (commuting_of_commuting_of_mem_lineOf hΔ hpts hA hD (Ne.symm hDA) hAD hB
      (right_mem_lineOf hD) hBD (left_mem_lineOf hA) hE h hED) (hEA.not_commuting hEne)
  · exact h

section LineTorus

variable {A E D : Subgroup G} {k : ℕ} (φ : SL2Coords A E k) {h : G} (hh : h ∈ A ⊔ E)
  {μ : (GaloisField 2 k)ˣ} (hμ : φ.mat h = diagElt μ)
include hh hμ

theorem conjSub_lineGroup_torus [Finite G] (hR : IsRootClass Δ) (hAD : Commuting A D)
    (hED : Commuting E D) : conjSub (lineGroup Δ A D) h = lineGroup Δ A D := by
  obtain ⟨hhA, -⟩ := φ.conjSub_eq_of_mat_eq_diagElt hh hμ
  have hhD : conjSub D h = D := conjSub_of_forall_commute fun d hd =>
    (commute_of_mem_sup_left hAD hED hh hd).symm
  rw [← lineGroup_conjSub hR, hhA, hhD]

theorem le_commSub_lineGroup [Finite G] (hR : IsRootClass Δ) (hA : A ∈ Δ) (hμ1 : μ ≠ 1) :
    A ≤ commSub (lineGroup Δ A D) h := by
  have hAab : ∀ x ∈ A, ∀ y ∈ A, Commute x y := fun x hx y hy => hR.commute hA hx hy
  obtain ⟨hhA, -⟩ := φ.conjSub_eq_of_mat_eq_diagElt hh hμ
  have hAh : ∀ x ∈ A, h * x * h⁻¹ ∈ A := fun x hx => by
    have := conj_mem_conjSub h hx
    rwa [hhA] at this
  have hker : (commMap hAab hAh).ker = ⊥ := by
    refine (Subgroup.eq_bot_iff_forall _).2 fun a ha => ?_
    exact Subtype.ext (φ.eq_one_of_commute_of_mat_eq_diagElt hh hμ hμ1 a.2
      ((mem_ker_commMap_iff hAab hAh a).1 ha))
  have hcard : Nat.card (commSub A h) = Nat.card A := by
    have h1 := card_range_commMap_mul hAab hAh
    rw [hker, Subgroup.card_bot, mul_one] at h1
    rw [card_commSub hAab hAh, h1]
  have hAA : commSub A h = A :=
    Subgroup.eq_of_le_of_card_ge (commSub_le hAab hAh) hcard.ge
  exact hAA.ge.trans (Subgroup.closure_mono fun x ⟨m, hm, hx⟩ =>
    ⟨m, le_lineGroup (left_mem_lineOf hA) hm, hx⟩)

variable [Finite G] (hΔ : IsTransvectionClass Δ) (hiso : NoIsolated Δ) (hpts : PointsDetermined Δ)
  (hA : A ∈ Δ) (hE : E ∈ Δ) (hD : D ∈ Δ) (hEA : Opposite E A) (hAD : Commuting A D)
  (hED : Commuting E D) (hDA : D ≠ A) (hq : 4 ≤ Nat.card A) (hμ1 : μ ≠ 1)
include hΔ hiso hpts hA hE hD hEA hAD hED hDA hq hμ1

theorem lineGroup_eq_sup_commSub : lineGroup Δ A D = D ⊔ commSub (lineGroup Δ A D) h := by
  have hUab : ∀ x ∈ lineGroup Δ A D, ∀ y ∈ lineGroup Δ A D, Commute x y := fun x hx y hy =>
    commute_of_mem_lineGroup hΔ hA hD hAD hx hy
  have hUh : ∀ x ∈ lineGroup Δ A D, h * x * h⁻¹ ∈ lineGroup Δ A D := fun x hx => by
    have := conj_mem_conjSub h hx
    rwa [conjSub_lineGroup_torus φ hh hμ hΔ.root hAD hED] at this
  have hAU := le_commSub_lineGroup (D := D) φ hh hμ hΔ.root hA hμ1
  refine le_antisymm (iSup₂_le fun P hP => ?_)
    (sup_le (le_lineGroup (right_mem_lineOf hD)) (commSub_le hUab hUh))
  by_cases hPA : P = A
  · rw [hPA]
    exact hAU.trans le_sup_right
  by_cases hPD : P = D
  · rw [hPD]
    exact le_sup_left
  obtain ⟨hT, hDl⟩ := isTriangle_of_mem_lineOf hΔ hpts hA hE hEA hAD hED hD hDA hP hPA hPD
  obtain ⟨t, htY, S⟩ := exists_triangleSetting hΔ hiso hT
  obtain ⟨-, hCZ, -, -⟩ := S.centralizer_corrN_spec htY hq hpts (S.coordsOf htY hq φ) hh hμ hμ1
  rw [← S.eq_corrN_inf_centralizer htY hq hpts hDl hED.symm] at hCZ
  have hLU : corrL A E t ≤ lineGroup Δ A D := by
    have := S.corrL_le_lineGroup htY hq hpts hDl hED.symm
    rwa [← lineGroup_eq_of_mem_of_ne hΔ hpts hA hP.1 (Ne.symm hPA) hT.comm hDl hDA] at this
  have hmono := commSub_mono ((S.inf_centralizer_le_corrL htY hq hpts).trans hLU) h
  calc P ≤ A ⊔ (corrN A E t ⊓ Subgroup.centralizer (A : Set G)) := S.le_sup_inf_centralizer
    _ ≤ D ⊔ commSub (lineGroup Δ A D) h := by
      refine sup_le (hAU.trans le_sup_right) ?_
      rw [hCZ]
      exact sup_le le_sup_left (hmono.trans le_sup_right)

theorem commute_lineGroup_iff {u : G} (hu : u ∈ lineGroup Δ A D) : Commute u h ↔ u ∈ D := by
  have hUab : ∀ x ∈ lineGroup Δ A D, ∀ y ∈ lineGroup Δ A D, Commute x y := fun x hx y hy =>
    commute_of_mem_lineGroup hΔ hA hD hAD hx hy
  have hUh : ∀ x ∈ lineGroup Δ A D, h * x * h⁻¹ ∈ lineGroup Δ A D := fun x hx => by
    have := conj_mem_conjSub h hx
    rwa [conjSub_lineGroup_torus φ hh hμ hΔ.root hAD hED] at this
  have hDU : D ≤ lineGroup Δ A D := le_lineGroup (right_mem_lineOf hD)
  have hDker : D.subgroupOf (lineGroup Δ A D) ≤ (commMap hUab hUh).ker := fun d hd =>
    (mem_ker_commMap_iff hUab hUh d).2
      (commute_of_mem_sup_left hAD hED hh (Subgroup.mem_subgroupOf.1 hd))
  have h1 := card_range_commMap_mul hUab hUh
  have h2 : Nat.card ↥(lineGroup Δ A D) ≤ Nat.card D * Nat.card (commMap hUab hUh).range := by
    have hc : Commuting D (commSub (lineGroup Δ A D) h) := fun x hx y hy =>
      hUab x (hDU hx) y (commSub_le hUab hUh hy)
    calc Nat.card ↥(lineGroup Δ A D) =
          Nat.card ↥(D ⊔ commSub (lineGroup Δ A D) h) := by
          rw [← lineGroup_eq_sup_commSub φ hh hμ hΔ hiso hpts hA hE hD hEA hAD hED hDA hq hμ1]
      _ ≤ Nat.card D * Nat.card (commSub (lineGroup Δ A D) h) := card_sup_le_of_commuting hc
      _ = Nat.card D * Nat.card (commMap hUab hUh).range := by rw [card_commSub hUab hUh]
  have hpos : 0 < Nat.card (commMap hUab hUh).range := Nat.card_pos
  have h3 : Nat.card (commMap hUab hUh).ker ≤ Nat.card (D.subgroupOf (lineGroup Δ A D)) := by
    rw [card_subgroupOf_of_le hDU]
    refine Nat.le_of_mul_le_mul_right ?_ hpos
    rw [mul_comm, h1]
    exact h2
  have hkerD : (commMap hUab hUh).ker = D.subgroupOf (lineGroup Δ A D) :=
    (Subgroup.eq_of_le_of_card_ge hDker h3).symm
  have := mem_ker_commMap_iff hUab hUh ⟨u, hu⟩
  rw [hkerD, Subgroup.mem_subgroupOf] at this
  exact this.symm

omit hiso hpts hE hEA hDA hq hμ1 in
theorem inf_commSub_lineGroup : D ⊓ commSub (lineGroup Δ A D) h = ⊥ := by
  have hUab : ∀ x ∈ lineGroup Δ A D, ∀ y ∈ lineGroup Δ A D, Commute x y := fun x hx y hy =>
    commute_of_mem_lineGroup hΔ hA hD hAD hx hy
  have hUh : ∀ x ∈ lineGroup Δ A D, h * x * h⁻¹ ∈ lineGroup Δ A D := fun x hx => by
    have := conj_mem_conjSub h hx
    rwa [conjSub_lineGroup_torus φ hh hμ hΔ.root hAD hED] at this
  have hk0 : k ≠ 0 := by
    intro h0
    have := φ.card_eq
    rw [h0, pow_zero] at this
    have hAne : A ≠ ⊥ := hΔ.root.ne_bot A hA
    exact hAne (Subgroup.eq_bot_of_card_eq A this)
  have hodd := φ.odd_orderOf_of_mat_eq_diagElt hk0 hh hμ
  have hfit := inf_ker_range_commMap hUab hUh
    (fun x hx => mul_self_of_mem_lineGroup hΔ hA hD hAD hx) hodd
  refine (Subgroup.eq_bot_iff_forall _).2 fun x hx => ?_
  have hx2 := hx.2
  rw [commSub_eq_map hUab hUh] at hx2
  obtain ⟨⟨r, hrU⟩, hr, rfl⟩ := hx2
  have hrk : (⟨r, hrU⟩ : ↥(lineGroup Δ A D)) ∈ (commMap hUab hUh).ker :=
    (mem_ker_commMap_iff hUab hUh _).2 (commute_of_mem_sup_left hAD hED hh hx.1)
  have h1 : (⟨r, hrU⟩ : ↥(lineGroup Δ A D)) ∈
      (commMap hUab hUh).ker ⊓ (commMap hUab hUh).range := ⟨hrk, hr⟩
  rw [hfit, Subgroup.mem_bot] at h1
  exact congrArg Subtype.val h1

end LineTorus

theorem eq_one_of_mem_lineStab (hΔ : IsTransvectionClass Δ) {A E D : Subgroup G} (hA : A ∈ Δ)
    (hE : E ∈ Δ) (hD : D ∈ Δ) (hEA : Opposite E A) (hED : Commuting E D) {a : G} (ha : a ∈ A)
    (haS : a ∈ lineStab Δ E D) : a = 1 := by
  have hEa : conjSub E a ∈ lineOf Δ E D := (mem_lineStab_iff.1 haS E).2 (left_mem_lineOf hE)
  by_cases hne : conjSub E a = E
  · exact hEA.symm.eq_one_of_conjSub_eq ha hne
  · exact absurd (commuting_of_mem_lineOf_of_mem_lineOf hΔ hE hD hED (left_mem_lineOf hE) hEa)
      (ModelRank.not_commuting_of_opposite
        (opposite_conjSub_of_ne hΔ hA hEA.symm (Subgroup.mem_sup_right ha) hne))

theorem exists_sl2Coords_torus [Finite G] (hR : IsRootClass Δ) {A E : Subgroup G} (hA : A ∈ Δ)
    (hE : E ∈ Δ) (hEA : Opposite E A) (hq : 4 ≤ Nat.card A) :
    ∃ (k : ℕ) (φ : SL2Coords A E k) (h : G) (μ : (GaloisField 2 k)ˣ),
      h ∈ A ⊔ E ∧ φ.mat h = diagElt μ ∧ μ ≠ 1 := by
  obtain ⟨k, hk⟩ := exists_card_eq_two_pow_of_opposite hR hA hE hEA
  obtain ⟨φ⟩ := nonempty_sl2Coords hR hA hE hEA hk
  obtain ⟨μ, hμ1⟩ := exists_unit_ne_one_of_card hk hq
  obtain ⟨h, hh, hμ⟩ := φ.mat_surj (diagElt μ)
  exact ⟨k, φ, h, μ, hh, hμ, hμ1⟩

namespace PairFrame

variable {A E D E' : Subgroup G}

theorem shortRootGroup_inf_sup_eq_bot (P : PairFrame Δ A E D E') (hΔ : IsTransvectionClass Δ) :
    shortRootGroup Δ A E D E' ⊓ (A ⊔ D) = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).2 fun x hx => ?_
  obtain ⟨a, ha, d, hd, rfl⟩ := mem_sup_of_commuting P.commuting_AD hx.2
  have hdS : d ∈ lineStab Δ E D := mem_lineStab_of_commute hΔ.root
    (fun e he => (P.commuting_ED e he d hd).symm) (fun d' hd' => hΔ.root.commute P.memD hd hd')
  have haS : a ∈ lineStab Δ E D := by
    have := (lineStab Δ E D).mul_mem hx.1.1.2 ((lineStab Δ E D).inv_mem hdS)
    rwa [mul_inv_cancel_right] at this
  obtain rfl := eq_one_of_mem_lineStab hΔ P.memA P.memE P.memD P.oppA P.commuting_ED ha haS
  rw [one_mul] at hx ⊢
  have hdS' : d ∈ lineStab Δ E' A := by
    rw [← lineStab_comm]
    exact hx.1.2
  exact eq_one_of_mem_lineStab hΔ P.memD P.memE' P.memA P.oppD P.commuting_AE'.symm hd hdS'

theorem inf_corrN_le_shortRootGroup [Finite G] (P : PairFrame Δ A E D E')
    (hpts : PointsDetermined Δ) (hlines : MeetsLines Δ) {B : Subgroup G}
    (hB : B ∈ lineOf Δ A D) (hBA : B ≠ A) (hBD : B ≠ D) {t t' : G}
    (S : TriangleSetting Δ A E B t) (htY : t ∈ A ⊔ E ⊔ B) (S' : TriangleSetting Δ D E' B t')
    (htY' : t' ∈ D ⊔ E' ⊔ B) (hq : 4 ≤ Nat.card A) :
    corrN A E t ⊓ corrN D E' t' ≤ shortRootGroup Δ A E D E' := by
  have F := P.toSp4Frame hB hBA hBD
  have hΔ := S.cls
  have hqD : 4 ≤ Nat.card D := by rwa [hΔ.root.card_eq P.memD P.memA]
  have hXL : corrN A E t ⊓ corrN D E' t' ≤ corrL A E t := by
    rw [← F.sup_inf_corrN_eq_corrL hpts S htY S' htY' hq]
    exact le_sup_right
  intro x hx
  refine ⟨⟨F.corrL_le_lineGroup hpts S htY hq (hXL hx), mem_lineStab_of_mapsTo fun C hC =>
    S.conjSub_mem_lineOf_E htY hq hpts hlines (F.mem_lineOf hΔ hpts) P.commuting_ED.symm hx.1
      hC⟩, ?_⟩
  rw [lineStab_comm]
  exact mem_lineStab_of_mapsTo fun C hC => S'.conjSub_mem_lineOf_E htY' hqD hpts hlines
    (F.swap.mem_lineOf hΔ hpts) P.commuting_AE' hx.2 hC

theorem lineGroup_le_sup [Finite G] (P : PairFrame Δ A E D E') (hΔ : IsTransvectionClass Δ)
    (hiso : NoIsolated Δ) (hpts : PointsDetermined Δ) (hq : 4 ≤ Nat.card A) {W : Subgroup G}
    (hW : ∀ B ∈ lineOf Δ A D, B ≠ A → B ≠ D → ∀ t t' : G, t ∈ A ⊔ E ⊔ B →
      TriangleSetting Δ A E B t → t' ∈ D ⊔ E' ⊔ B → TriangleSetting Δ D E' B t' →
      corrN A E t ⊓ corrN D E' t' ≤ W) :
    lineGroup Δ A D ≤ A ⊔ D ⊔ W := by
  refine iSup₂_le fun B hB => ?_
  by_cases hBA : B = A
  · rw [hBA]
    exact le_sup_left.trans le_sup_left
  by_cases hBD : B = D
  · rw [hBD]
    exact le_sup_right.trans le_sup_left
  have F := P.toSp4Frame hB hBA hBD
  obtain ⟨t, htY, S⟩ := exists_triangleSetting hΔ hiso (F.isTriangle hΔ hpts)
  obtain ⟨t', htY', S'⟩ := exists_triangleSetting hΔ hiso (F.swap.isTriangle hΔ hpts)
  calc B ≤ corrL A E t := S.le_corrL_right
    _ = A ⊔ D ⊔ (corrN A E t ⊓ corrN D E' t') :=
        (F.sup_inf_corrN_eq_corrL hpts S htY S' htY' hq).symm
    _ ≤ A ⊔ D ⊔ W := sup_le_sup_left (hW B hB hBA hBD t t' htY S htY' S') _

theorem shortRootGroup_spec [Finite G] (P : PairFrame Δ A E D E') (hΔ : IsTransvectionClass Δ)
    (hiso : NoIsolated Δ) (hpts : PointsDetermined Δ) (hlines : MeetsLines Δ)
    (hq : 4 ≤ Nat.card A) {k₀ : ℕ} (φ₀ : SL2Coords A E k₀) {h₀ : G} (hh₀ : h₀ ∈ A ⊔ E)
    {μ : (GaloisField 2 k₀)ˣ} (hμ : φ₀.mat h₀ = diagElt μ) (hμ1 : μ ≠ 1) {k₁ : ℕ}
    (φ₁ : SL2Coords D E' k₁) {h₁ : G} (hh₁ : h₁ ∈ D ⊔ E') {ν : (GaloisField 2 k₁)ˣ}
    (hν : φ₁.mat h₁ = diagElt ν) (hν1 : ν ≠ 1) :
    shortRootGroup Δ A E D E' =
        commSub (lineGroup Δ A D) h₀ ⊓ commSub (lineGroup Δ A D) h₁ ∧
      A ⊔ shortRootGroup Δ A E D E' ⊔ D = lineGroup Δ A D ∧
      Nat.card ↥(lineGroup Δ A D) = Nat.card A ^ 2 * Nat.card ↥(shortRootGroup Δ A E D E') := by
  have hR := hΔ.root
  have hqD : 4 ≤ Nat.card D := by rwa [hR.card_eq P.memD P.memA]
  have hUc : lineGroup Δ D A = lineGroup Δ A D := lineGroup_comm D A
  have hUD := lineGroup_eq_sup_commSub φ₀ hh₀ hμ hΔ hiso hpts P.memA P.memE P.memD P.oppA
    P.commuting_AD P.commuting_ED P.ne_AD.symm hq hμ1
  have hDY₀ := inf_commSub_lineGroup φ₀ hh₀ hμ hΔ P.memA P.memD P.commuting_AD P.commuting_ED
  have hAY₀ := le_commSub_lineGroup (D := D) φ₀ hh₀ hμ hR P.memA hμ1
  have hUA := lineGroup_eq_sup_commSub φ₁ hh₁ hν hΔ hiso hpts P.memD P.memE' P.memA P.oppD
    P.commuting_AD.symm P.commuting_AE'.symm P.ne_AD hqD hν1
  have hAY₁ := inf_commSub_lineGroup φ₁ hh₁ hν hΔ P.memD P.memA P.commuting_AD.symm
    P.commuting_AE'.symm
  rw [hUc] at hUA hAY₁
  set U := lineGroup Δ A D with hU
  set Y₀ := commSub U h₀ with hY₀
  set Y₁ := commSub U h₁ with hY₁
  set X := shortRootGroup Δ A E D E' with hX
  have hAU : A ≤ U := le_lineGroup (left_mem_lineOf P.memA)
  have hDU : D ≤ U := le_lineGroup (right_mem_lineOf P.memD)
  have hY₀U : Y₀ ≤ U := le_sup_right.trans hUD.ge
  have hY₁U : Y₁ ≤ U := le_sup_right.trans hUA.ge
  have hXU : X ≤ U := fun x hx => hx.1.1
  have hUc' : ∀ {H K : Subgroup G}, H ≤ U → K ≤ U → Commuting H K := fun hH hK x hx y hy =>
    commute_of_mem_lineGroup hΔ P.memA P.memD P.commuting_AD (hH hx) (hK hy)
  obtain ⟨X', hX'⟩ : ∃ X' : Subgroup G, X' = Y₀ ⊓ Y₁ := ⟨_, rfl⟩
  have hX'U : X' ≤ U := hX' ▸ inf_le_left.trans hY₀U
  have hY₀eq : Y₀ = A ⊔ X' := by
    refine le_antisymm (fun y hy => ?_) (sup_le hAY₀ (hX' ▸ inf_le_left))
    have hyU : y ∈ A ⊔ Y₁ := by
      rw [← hUA]
      exact hY₀U hy
    obtain ⟨a, ha, v, hv, rfl⟩ := mem_sup_of_commuting (hUc' hAU hY₁U) hyU
    have hv0 : v ∈ Y₀ := by
      have := Y₀.mul_mem (Y₀.inv_mem (hAY₀ ha)) hy
      rwa [inv_mul_cancel_left] at this
    exact Subgroup.mul_mem_sup ha (hX' ▸ ⟨hv0, hv⟩)
  have hAX' : A ⊓ X' = ⊥ := by
    refine (Subgroup.eq_bot_iff_forall _).2 fun x hx => ?_
    have : x ∈ A ⊓ Y₁ := ⟨hx.1, (hX' ▸ hx.2 : x ∈ Y₀ ⊓ Y₁).2⟩
    rwa [hAY₁, Subgroup.mem_bot] at this
  have hX'AD : X' ⊓ (A ⊔ D) = ⊥ := by
    refine (Subgroup.eq_bot_iff_forall _).2 fun x hx => ?_
    obtain ⟨a, ha, d, hd, rfl⟩ := mem_sup_of_commuting P.commuting_AD hx.2
    have hx' : a * d ∈ Y₀ ⊓ Y₁ := hX' ▸ hx.1
    have hd0 : d ∈ Y₀ := by
      have := Y₀.mul_mem (Y₀.inv_mem (hAY₀ ha)) hx'.1
      rwa [inv_mul_cancel_left] at this
    have hd1 : d = 1 := by
      have : d ∈ D ⊓ Y₀ := ⟨hd, hd0⟩
      rwa [hDY₀, Subgroup.mem_bot] at this
    subst hd1
    rw [mul_one] at hx' ⊢
    have : a ∈ A ⊓ Y₁ := ⟨ha, hx'.2⟩
    rwa [hAY₁, Subgroup.mem_bot] at this
  have hXAD : X ⊓ (A ⊔ D) = ⊥ := P.shortRootGroup_inf_sup_eq_bot hΔ
  have hW : ∀ B ∈ lineOf Δ A D, B ≠ A → B ≠ D → ∀ t t' : G, t ∈ A ⊔ E ⊔ B →
      TriangleSetting Δ A E B t → t' ∈ D ⊔ E' ⊔ B → TriangleSetting Δ D E' B t' →
      corrN A E t ⊓ corrN D E' t' ≤ X ⊓ X' := by
    intro B hB hBA hBD t t' htY S htY' S'
    have F := P.toSp4Frame hB hBA hBD
    refine le_inf (P.inf_corrN_le_shortRootGroup hpts hlines hB hBA hBD S htY S' htY' hq) ?_
    rw [hX']
    refine le_inf ?_ ?_
    · rw [← F.commSub_eq_inf hpts S htY S' htY' hq (S.coordsOf htY hq φ₀) hh₀ hμ hμ1]
      exact commSub_mono ((S.inf_centralizer_le_corrL htY hq hpts).trans
        (F.corrL_le_lineGroup hpts S htY hq)) h₀
    · rw [← F.commSub_eq_inf_swap hpts S htY S' htY' hq (S'.coordsOf htY' hqD φ₁) hh₁ hν hν1]
      exact commSub_mono ((S'.inf_centralizer_le_corrL htY' hqD hpts).trans
        ((F.swap.corrL_le_lineGroup hpts S' htY' hqD).trans hUc.le)) h₁
  have hUW := P.lineGroup_le_sup hΔ hiso hpts hq hW
  have key : ∀ {Z : Subgroup G}, Z ≤ U → X ⊓ X' ≤ Z → Z ⊓ (A ⊔ D) = ⊥ → Z ≤ X ⊓ X' := by
    intro Z hZU hZ hZAD x hx
    obtain ⟨y, hy, r, hr, hyr⟩ := mem_sup_of_commuting
      (hUc' (sup_le hAU hDU) (inf_le_left.trans hXU)) (hUW (hZU hx))
    have hyZ : y ∈ Z := by
      have := Z.mul_mem hx (Z.inv_mem (hZ hr))
      rwa [← hyr, mul_inv_cancel_right] at this
    have hy1 : y = 1 := by
      have : y ∈ Z ⊓ (A ⊔ D) := ⟨hyZ, hy⟩
      rwa [hZAD, Subgroup.mem_bot] at this
    rw [← hyr, hy1, one_mul]
    exact hr
  have hXX' : X = X' := le_antisymm ((key hXU inf_le_left hXAD).trans inf_le_right)
    ((key hX'U inf_le_right hX'AD).trans inf_le_left)
  refine ⟨hXX'.trans hX', ?_, ?_⟩
  · calc A ⊔ X ⊔ D = D ⊔ (A ⊔ X') := by rw [hXX', sup_comm]
      _ = U := by rw [← hY₀eq, ← hUD]
  · have hc1 : Nat.card ↥(D ⊔ Y₀) = Nat.card D * Nat.card Y₀ :=
      le_antisymm (card_sup_le_of_commuting (hUc' hDU hY₀U)) (card_mul_card_le_card_sup hDY₀)
    have hc2 : Nat.card ↥(A ⊔ X') = Nat.card A * Nat.card X' :=
      le_antisymm (card_sup_le_of_commuting (hUc' hAU hX'U)) (card_mul_card_le_card_sup hAX')
    calc Nat.card ↥U = Nat.card ↥(D ⊔ Y₀) := by rw [← hUD]
      _ = Nat.card A * (Nat.card A * Nat.card X') := by
          rw [hc1, hR.card_eq P.memD P.memA, hY₀eq, hc2]
      _ = Nat.card A ^ 2 * Nat.card X := by rw [hXX']; ring

theorem shortRootGroup_eq_inf [Finite G] (P : PairFrame Δ A E D E') (hΔ : IsTransvectionClass Δ)
    (hiso : NoIsolated Δ) (hpts : PointsDetermined Δ) (hlines : MeetsLines Δ)
    (hq : 4 ≤ Nat.card A) {k₀ : ℕ} (φ₀ : SL2Coords A E k₀) {h₀ : G} (hh₀ : h₀ ∈ A ⊔ E)
    {μ : (GaloisField 2 k₀)ˣ} (hμ : φ₀.mat h₀ = diagElt μ) (hμ1 : μ ≠ 1) {k₁ : ℕ}
    (φ₁ : SL2Coords D E' k₁) {h₁ : G} (hh₁ : h₁ ∈ D ⊔ E') {ν : (GaloisField 2 k₁)ˣ}
    (hν : φ₁.mat h₁ = diagElt ν) (hν1 : ν ≠ 1) :
    shortRootGroup Δ A E D E' =
      commSub (lineGroup Δ A D) h₀ ⊓ commSub (lineGroup Δ A D) h₁ :=
  (P.shortRootGroup_spec hΔ hiso hpts hlines hq φ₀ hh₀ hμ hμ1 φ₁ hh₁ hν hν1).1

theorem sup_shortRootGroup [Finite G] (P : PairFrame Δ A E D E') (hΔ : IsTransvectionClass Δ)
    (hiso : NoIsolated Δ) (hpts : PointsDetermined Δ) (hlines : MeetsLines Δ)
    (hq : 4 ≤ Nat.card A) : A ⊔ shortRootGroup Δ A E D E' ⊔ D = lineGroup Δ A D := by
  have hqD : 4 ≤ Nat.card D := by rwa [hΔ.root.card_eq P.memD P.memA]
  obtain ⟨k₀, φ₀, h₀, μ, hh₀, hμ, hμ1⟩ := exists_sl2Coords_torus hΔ.root P.memA P.memE P.oppA hq
  obtain ⟨k₁, φ₁, h₁, ν, hh₁, hν, hν1⟩ := exists_sl2Coords_torus hΔ.root P.memD P.memE' P.oppD hqD
  exact (P.shortRootGroup_spec hΔ hiso hpts hlines hq φ₀ hh₀ hμ hμ1 φ₁ hh₁ hν hν1).2.1

theorem lineGroup_inf_lineStab [Finite G] (P : PairFrame Δ A E D E')
    (hΔ : IsTransvectionClass Δ) (hiso : NoIsolated Δ) (hpts : PointsDetermined Δ)
    (hlines : MeetsLines Δ) (hq : 4 ≤ Nat.card A) :
    lineGroup Δ A D ⊓ lineStab Δ E D = shortRootGroup Δ A E D E' ⊔ D := by
  have hR := hΔ.root
  have hDS : D ≤ lineStab Δ E D := fun d hd => mem_lineStab_of_commute hR
    (fun e he => (P.commuting_ED e he d hd).symm) (fun d' hd' => hR.commute P.memD hd hd')
  have hXS : shortRootGroup Δ A E D E' ≤ lineStab Δ E D := fun x hx => hx.1.2
  have hXU : shortRootGroup Δ A E D E' ≤ lineGroup Δ A D := fun x hx => hx.1.1
  have hDU : D ≤ lineGroup Δ A D := le_lineGroup (right_mem_lineOf P.memD)
  have hAU : A ≤ lineGroup Δ A D := le_lineGroup (left_mem_lineOf P.memA)
  refine le_antisymm (fun u hu => ?_) (sup_le (le_inf hXU hXS) (le_inf hDU hDS))
  have hu' : u ∈ A ⊔ (shortRootGroup Δ A E D E' ⊔ D) := by
    rw [← sup_assoc, P.sup_shortRootGroup hΔ hiso hpts hlines hq]
    exact hu.1
  have hc : Commuting A (shortRootGroup Δ A E D E' ⊔ D) := fun a ha w hw =>
    commute_of_mem_lineGroup hΔ P.memA P.memD P.commuting_AD (hAU ha) (sup_le hXU hDU hw)
  obtain ⟨a, ha, w, hw, rfl⟩ := mem_sup_of_commuting hc hu'
  have hwS : w ∈ lineStab Δ E D := sup_le hXS hDS hw
  have haS : a ∈ lineStab Δ E D := by
    have := (lineStab Δ E D).mul_mem hu.2 ((lineStab Δ E D).inv_mem hwS)
    rwa [mul_inv_cancel_right] at this
  obtain rfl := eq_one_of_mem_lineStab hΔ P.memA P.memE P.memD P.oppA P.commuting_ED ha haS
  rwa [one_mul]

theorem commute_shortRootGroup_iff [Finite G] (P : PairFrame Δ A E D E')
    (hΔ : IsTransvectionClass Δ) (hiso : NoIsolated Δ) (hpts : PointsDetermined Δ)
    (hq : 4 ≤ Nat.card A) {k : ℕ} (φ : SL2Coords A E k) {h : G} (hh : h ∈ A ⊔ E)
    {μ : (GaloisField 2 k)ˣ} (hμ : φ.mat h = diagElt μ) (hμ1 : μ ≠ 1) {x : G}
    (hx : x ∈ shortRootGroup Δ A E D E') : Commute x h ↔ x = 1 := by
  refine ⟨fun hxh => ?_, fun h1 => h1 ▸ Commute.one_left h⟩
  have hxD := (commute_lineGroup_iff φ hh hμ hΔ hiso hpts P.memA P.memE P.memD P.oppA
    P.commuting_AD P.commuting_ED P.ne_AD.symm hq hμ1 hx.1.1).1 hxh
  have : x ∈ shortRootGroup Δ A E D E' ⊓ (A ⊔ D) := ⟨hx, Subgroup.mem_sup_right hxD⟩
  rwa [P.shortRootGroup_inf_sup_eq_bot hΔ, Subgroup.mem_bot] at this

theorem commute_shortRootGroup_iff_swap [Finite G] (P : PairFrame Δ A E D E')
    (hΔ : IsTransvectionClass Δ) (hiso : NoIsolated Δ) (hpts : PointsDetermined Δ)
    (hq : 4 ≤ Nat.card A) {k : ℕ} (φ : SL2Coords D E' k) {h : G} (hh : h ∈ D ⊔ E')
    {ν : (GaloisField 2 k)ˣ} (hν : φ.mat h = diagElt ν) (hν1 : ν ≠ 1) {x : G}
    (hx : x ∈ shortRootGroup Δ A E D E') : Commute x h ↔ x = 1 := by
  have hqD : 4 ≤ Nat.card D := by rwa [hΔ.root.card_eq P.memD P.memA]
  refine ⟨fun hxh => ?_, fun h1 => h1 ▸ Commute.one_left h⟩
  have hxU : x ∈ lineGroup Δ D A := by
    rw [lineGroup_comm]
    exact hx.1.1
  have hxA := (commute_lineGroup_iff φ hh hν hΔ hiso hpts P.memD P.memE' P.memA P.oppD
    P.commuting_AD.symm P.commuting_AE'.symm P.ne_AD hqD hν1 hxU).1 hxh
  have : x ∈ shortRootGroup Δ A E D E' ⊓ (A ⊔ D) := ⟨hx, Subgroup.mem_sup_left hxA⟩
  rwa [P.shortRootGroup_inf_sup_eq_bot hΔ, Subgroup.mem_bot] at this

end PairFrame

end CFSG.Timmesfeld.Transvection
