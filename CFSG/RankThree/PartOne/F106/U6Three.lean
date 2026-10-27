module

public import CFSG.RankThree.PartOne.F106.ThreeRankGen
public import CFSG.RankThree.PartOne.F106.U6Mono
public import CFSG.Timmesfeld.Orders.Classical
public import Certificates.Certificate271061

set_option linter.unusedSectionVars false

public section

namespace CFSG.RankThree.PartOne.F106

open CFSG.Assembly.LowTwoRank

structure U6SylowCert.Facts (c : U6SylowCert) : Prop where
  len : c.paths.length = 729
  zero : c.paths.getD 0 [] = []
  path : ∀ p ∈ c.paths, ∀ k ∈ p, k < 6
  nodup : ((List.range 729).map c.tab).Nodup
  rt : ∀ i < 729, ∀ g < 6, c.rtv i g < 729 ∧
    (c.tab i).mul (U6Mon.gen g) = c.tab (c.rtv i g)
  inv : ∀ i < 729, c.invv i < 729 ∧ (c.tab i).mul (c.tab (c.invv i)) = U6Mon.one
  zl : c.zl.length < 243
  wit : ∀ i < 729, c.witOK i (c.wit.getD i .exc) = true

theorem U6SylowCert.facts_of_check (c : U6SylowCert) (hc : c.check = true) : c.Facts := by
  simp only [U6SylowCert.check, Bool.and_eq_true, List.all_eq_true, List.mem_range,
    decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := hc
  exact ⟨h1, h2, fun p hp k hk => by simpa using h3 p hp k hk, h4, h5, h6, h7, h8⟩

theorem exists_cube {K : Type} [Field K] [Finite K] (hK : Nat.card K = 4) :
    Nonempty (Cube K) := by
  classical
  have := Fintype.ofFinite K
  have h3 : 3 ∣ Nat.card Kˣ := by
    rw [Nat.card_eq_fintype_card, Fintype.card_units, ← Nat.card_eq_fintype_card, hK]
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) 3 h3
  refine ⟨⟨(x : K), ?_, ?_⟩⟩
  · have h := pow_orderOf_eq_one x
    rw [hx] at h
    simpa using congrArg Units.val h
  · intro h
    have h1 : x = 1 := Units.ext h
    rw [h1, orderOf_one] at hx
    exact absurd hx (by norm_num)

section Sel

variable {K : Type} [Field K] [CharP K 2] (ω : Cube K) (hK : Nat.card K = (2 ^ 1) ^ 2)
  (c : U6SylowCert)

@[expose] noncomputable def U6SylowCert.sel (i : ℕ) : StatedProj (StatedSU 6 (2 ^ 1) K) :=
  ω.mu hK (c.tab i)

@[expose] noncomputable def Cube.genMu (k : ℕ) : StatedProj (StatedSU 6 (2 ^ 1) K) :=
  ω.mu hK (U6Mon.gen k)

variable {c}

theorem U6SylowCert.ok_tab (i : ℕ) : (c.tab i).Ok := U6Mon.ok_evalWord _

theorem U6SylowCert.tab_inj (hf : c.Facts) {i j : ℕ} (hi : i < 729) (hj : j < 729)
    (h : c.tab i = c.tab j) : i = j :=
  List.inj_on_of_nodup_map hf.nodup (List.mem_range.2 hi) (List.mem_range.2 hj) h

theorem U6SylowCert.sel_inj (hf : c.Facts) {i j : ℕ} (hi : i < 729) (hj : j < 729)
    (h : c.sel ω hK i = c.sel ω hK j) : i = j :=
  tab_inj hf hi hj (ω.mu_injective hK (ok_tab i) (ok_tab j) h)

theorem U6SylowCert.sel_zero (hf : c.Facts) : c.sel ω hK 0 = 1 := by
  show ω.mu hK (U6Mon.evalWord (c.paths.getD 0 [])) = 1
  rw [hf.zero]
  exact ω.mu_one hK

theorem U6SylowCert.sel_rt (hf : c.Facts) {i g : ℕ} (hi : i < 729) (hg : g < 6) :
    c.sel ω hK i * ω.genMu hK g = c.sel ω hK (c.rtv i g) := by
  rw [U6SylowCert.sel, Cube.genMu, U6SylowCert.sel,
    ω.mu_mul hK (ok_tab i) (U6Mon.ok_gen g), (hf.rt i hi g hg).2]

theorem U6SylowCert.sel_inv (hf : c.Facts) {i : ℕ} (hi : i < 729) :
    c.sel ω hK (c.invv i) = (c.sel ω hK i)⁻¹ := by
  apply eq_inv_of_mul_eq_one_right
  rw [U6SylowCert.sel, U6SylowCert.sel, ω.mu_mul hK (ok_tab i) (ok_tab _), (hf.inv i hi).2,
    ω.mu_one hK]

theorem U6SylowCert.sel_mem_closure (hf : c.Facts) {i : ℕ} (hi : i < 729) :
    c.sel ω hK i ∈
      Subgroup.closure (Set.range fun k : Fin 6 => ω.genMu hK (k : ℕ)) := by
  have hi' : i < c.paths.length := hf.len ▸ hi
  have hmem : c.paths.getD i [] ∈ c.paths := by
    rw [List.getD_eq_getElem _ _ hi']
    exact List.getElem_mem hi'
  rw [U6SylowCert.sel, U6SylowCert.tab, ω.mu_evalWord hK]
  refine Subgroup.list_prod_mem _ (fun x hx => ?_)
  obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hx
  exact Subgroup.subset_closure ⟨⟨k, hf.path _ hmem k hk⟩, rfl⟩

theorem U6SylowCert.sel_comm {i j : ℕ} :
    (c.tab i).mul (c.tab j) = (c.tab j).mul (c.tab i) ↔
      c.sel ω hK i * c.sel ω hK j = c.sel ω hK j * c.sel ω hK i := by
  rw [U6SylowCert.sel, U6SylowCert.sel, ω.mu_mul hK (ok_tab i) (ok_tab j),
    ω.mu_mul hK (ok_tab j) (ok_tab i)]
  exact ⟨fun h => by rw [h], fun h => ω.mu_injective hK (U6Mon.ok_mul (ok_tab i) (ok_tab j))
    (U6Mon.ok_mul (ok_tab j) (ok_tab i)) h⟩

theorem U6SylowCert.sel_conj_ne (hf : c.Facts) {i u v : ℕ} (hu : u < 729) (hv : v < 729)
    (h : c.conjC i u ≠ c.conjC i v) :
    c.sel ω hK u * c.sel ω hK i * (c.sel ω hK u)⁻¹ ≠
      c.sel ω hK v * c.sel ω hK i * (c.sel ω hK v)⁻¹ := by
  have key : ∀ {w : ℕ}, w < 729 → c.sel ω hK w * c.sel ω hK i * (c.sel ω hK w)⁻¹ =
      ω.mu hK (c.conjC i w) := by
    intro w hw
    rw [← sel_inv ω hK hf hw, U6SylowCert.sel, U6SylowCert.sel, U6SylowCert.sel,
      ω.mu_mul hK (ok_tab w) (ok_tab i), ω.mu_mul hK (U6Mon.ok_mul (ok_tab w) (ok_tab i))
        (ok_tab _)]
    rfl
  rw [key hu, key hv]
  exact fun heq => h (ω.mu_injective hK (U6Mon.ok_mul (U6Mon.ok_mul (ok_tab u) (ok_tab i))
    (ok_tab _)) (U6Mon.ok_mul (U6Mon.ok_mul (ok_tab v) (ok_tab i)) (ok_tab _)) heq)

theorem U6SylowCert.tableWitness (hf : c.Facts) {i : ℕ} (hi : i < 729) :
    i ∈ c.zl ∨ TableWitness (c.sel ω hK) i := by
  have hw := hf.wit i hi
  have comm : ∀ {j : ℕ}, j < 729 → c.commB j i = true →
      c.sel ω hK j * c.sel ω hK i = c.sel ω hK i * c.sel ω hK j := fun _ hb =>
    (sel_comm ω hK).1 (of_decide_eq_true hb)
  have ncomm : ∀ {j : ℕ}, j < 729 → c.commB j i = false →
      c.sel ω hK j * c.sel ω hK i ≠ c.sel ω hK i * c.sel ω hK j := by
    intro j hj hb h
    have h2 := (sel_comm ω hK).2 h
    simp [U6SylowCert.commB, h2] at hb
  generalize c.wit.getD i .exc = w at hw
  cases w with
  | exc =>
    left
    simpa only [U6SylowCert.witOK, decide_eq_true_eq] using hw
  | conj4 u₀ u₁ u₂ u₃ =>
    right
    simp only [U6SylowCert.witOK, Bool.and_eq_true, decide_eq_true_eq] at hw
    obtain ⟨⟨h0, h1, h2, h3⟩, hnd⟩ := hw
    simp only [List.map_cons, List.map_nil, List.nodup_cons, List.mem_cons,
      List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true, not_false_eq_true] at hnd
    obtain ⟨⟨n01, n02, n03⟩, ⟨n12, n13⟩, n23⟩ := hnd
    have key : ∀ {u v : ℕ}, u < 729 → v < 729 → c.conjC i u ≠ c.conjC i v →
        c.sel ω hK u * c.sel ω hK i * (c.sel ω hK u)⁻¹ ≠
          c.sel ω hK v * c.sel ω hK i * (c.sel ω hK v)⁻¹ :=
      fun hu hv hne => sel_conj_ne ω hK hf hu hv hne
    refine Or.inl ⟨![u₀, u₁, u₂, u₃], ?_, ?_⟩
    · intro k
      fin_cases k <;> simpa
    · exact fin4_injective (key h0 h1 n01) (key h0 h2 n02) (key h0 h3 n03) (key h1 h2 n12)
        (key h1 h3 n13) (key h2 h3 n23)
  | pair z x y =>
    right
    simp only [U6SylowCert.witOK, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hw
    obtain ⟨⟨⟨⟨⟨hz, hx, hy⟩, nz⟩, cx⟩, cy⟩, nxy⟩ := hw
    refine Or.inr ⟨⟨z, hz, ncomm hz nz⟩, Or.inl ⟨x, y, hx, hy, comm hx cx, comm hy cy, ?_⟩⟩
    intro h
    have h2 := (sel_comm ω hK).2 h
    simp [U6SylowCert.commB, h2] at nxy
  | cube z x =>
    right
    simp only [U6SylowCert.witOK, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hw
    obtain ⟨⟨⟨⟨hz, hx⟩, nz⟩, cx⟩, hcube⟩ := hw
    refine Or.inr ⟨⟨z, hz, ncomm hz nz⟩, Or.inr ⟨x, hx, comm hx cx, fun h3 => hcube ?_⟩⟩
    have h3' : c.sel ω hK x * c.sel ω hK x * c.sel ω hK x = 1 :=
      (pow_three' (c.sel ω hK x)).symm.trans h3
    rw [U6SylowCert.sel, ω.mu_mul hK (ok_tab x) (ok_tab x),
      ω.mu_mul hK (U6Mon.ok_mul (ok_tab x) (ok_tab x)) (ok_tab x), ← ω.mu_one hK] at h3'
    exact ω.mu_injective hK (U6Mon.ok_mul (U6Mon.ok_mul (ok_tab x) (ok_tab x)) (ok_tab x))
      U6Mon.ok_one h3'

end Sel

theorem u6_no_elemAbelian_five
    {T : Type} [Group T] (hmod : StatedClassicalModel T .PSU 6 2 1) (D : Subgroup T)
    (hcomm : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a) (hcube : ∀ a ∈ D, a ^ 3 = 1)
    (hcard : Nat.card D = 3 ^ 5) : False := by
  classical
  have hord : Nat.card T = CFSG.Open.ordTwistedA (6 - 1) (2 ^ 1) :=
    (CFSG.Timmesfeld.card_statedClassicalModel_two hmod).2.1 rfl
  obtain ⟨-, K, _, hfin, hK, ⟨e⟩⟩ := hmod
  have : CharP K 2 := by
    have := Fintype.ofFinite K
    exact charP_of_card_eq_prime_pow (f := 2) (by rw [← Nat.card_eq_fintype_card, hK]; norm_num)
  obtain ⟨ω⟩ := exists_cube (K := K) (by rw [hK]; norm_num)
  have hf : u6ThreeCert.Facts :=
    U6SylowCert.facts_of_check _ (Certificates.certificate271061 : U6ThreeRankCheck)
  have hG : Nat.card (StatedProj (StatedSU 6 (2 ^ 1) K)) = 9196830720 := by
    rw [← Nat.card_congr e.toEquiv, hord]
    unfold CFSG.Open.ordTwistedA
    decide +kernel
  have : Finite (StatedProj (StatedSU 6 (2 ^ 1) K)) :=
    Nat.finite_of_card_ne_zero (by rw [hG]; norm_num)
  refine no_elemAbelian_five_of_table (fun k : Fin 6 => ω.genMu hK (k : ℕ))
    (u6ThreeCert.sel ω hK) (U6SylowCert.sel_zero ω hK hf)
    (fun i hi j hj h => U6SylowCert.sel_inj ω hK hf hi hj h)
    (fun i hi => U6SylowCert.sel_mem_closure ω hK hf hi)
    (fun i hi k =>
      ⟨u6ThreeCert.rtv i k, (hf.rt i hi k k.2).1, U6SylowCert.sel_rt ω hK hf hi k.2⟩)
    u6ThreeCert.zl.toFinset ?_ (fun i hi => ?_) ?_ (D.map e.toMonoidHom) ?_ ?_ ?_
  · exact lt_of_le_of_lt (List.toFinset_card_le _) (lt_of_lt_of_le hf.zl (by norm_num))
  · rcases U6SylowCert.tableWitness ω hK hf hi with hz | hw
    · exact Or.inl (List.mem_toFinset.2 hz)
    · exact Or.inr hw
  · rw [hG]
    norm_num
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, hcomm a ha b hb]
  · rintro _ ⟨a, ha, rfl⟩
    rw [← map_pow, hcube a ha, map_one]
  · rw [Subgroup.card_map_of_injective e.injective, hcard]

end CFSG.RankThree.PartOne.F106
