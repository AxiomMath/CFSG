module

public import CFSG.RankThree.PartOne.F106.ThreeRankGen
public import CFSG.Timmesfeld.Orders.ExceptionalUntwisted
public import CFSG.LieType.Chevalley.ExceptionalG2F4ModelSchreier
public import Certificates.Certificate271060

set_option linter.unusedSectionVars false

public section

namespace CFSG.RankThree.PartOne.F106

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.Simplicity.TitsBits TauCeti CFSG.RankThree.PartOne.SEITZX

section Table

variable {X : Type} [Field X] [CharP X 2] (c : F4SylowCert)

@[expose] noncomputable def F4SylowCert.gen (k : ℕ) : adjointGroup ReeTag.F4.tag X :=
  evalG X (wordOfCodes (c.gens.getD k []))

@[expose] noncomputable def F4SylowCert.sel (i : ℕ) : adjointGroup ReeTag.F4.tag X :=
  ((c.paths.getD i []).map (c.gen (X := X))).prod

@[expose] def F4SylowCert.tab : List ℕ := c.tabList c.gbList

theorem hasBits_gen (k : ℕ) : HasBits X (c.gen (X := X) k) (c.genBits k) :=
  hasBits_evalG (wordOfCodes (c.gens.getD k []))

theorem gbList_getD {k : ℕ} (hk : k < 6) : c.gbList.getD k 0 = c.genBits k := by
  simp [F4SylowCert.gbList, List.getD_eq_getElem?_getD, hk]

theorem hasBits_path {p : List ℕ} (hp : ∀ k ∈ p, k < 6) :
    HasBits X ((p.map (c.gen (X := X))).prod) (pathBits c.gbList p) := by
  induction p with
  | nil => exact hasBits_one
  | cons k p ih =>
    have hk : k < 6 := hp k (List.mem_cons_self ..)
    have h1 := (hasBits_gen (X := X) c k).mul (ih fun j hj => hp j (List.mem_cons_of_mem _ hj))
    have e : pathBits c.gbList (k :: p) = mul (c.genBits k) (pathBits c.gbList p) := by
      show mul (c.gbList.getD k 0) (pathBits c.gbList p) = _
      rw [gbList_getD c hk]
    rw [e, List.map_cons, List.prod_cons]
    exact h1

structure F4SylowCert.Facts : Prop where
  len : c.paths.length = 729
  zero : c.paths.getD 0 [] = []
  path : ∀ p ∈ c.paths, ∀ k ∈ p, k < 6
  nodup : (c.tab.map (· % 2 ^ 2704)).Nodup
  rt : ∀ i < 729, ∀ g < 6, c.rtv i g < 729 ∧
    mul (c.tab.getD i 0) (c.genBits g) % 2 ^ 2704 = c.tab.getD (c.rtv i g) 0 % 2 ^ 2704
  inv : ∀ i < 729, c.invv i < 729 ∧
    mul (c.tab.getD i 0) (c.tab.getD (c.invv i) 0) % 2 ^ 2704 = oneBits % 2 ^ 2704
  zl : c.zl.length < 243
  wit : ∀ i < 729, c.witOK c.tab i (c.wit.getD i .exc) = true

theorem F4SylowCert.facts_of_check (hc : c.check = true) : c.Facts := by
  simp only [F4SylowCert.check, F4SylowCert.checkWith, Bool.and_eq_true, List.all_eq_true,
    List.mem_range, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := hc
  refine ⟨h1, h2, fun p hp k hk => ?_, h4, fun i hi g hg => ?_, h6, h7, h8⟩
  · simpa using h3 p hp k hk
  · have := h5 i hi g hg
    rwa [gbList_getD c hg] at this

variable {c}

theorem tab_getD (hf : c.Facts) {i : ℕ} (hi : i < 729) :
    c.tab.getD i 0 = pathBits c.gbList (c.paths.getD i []) := by
  have hi' : i < c.paths.length := hf.len ▸ hi
  simp [F4SylowCert.tab, F4SylowCert.tabList, List.getD_eq_getElem?_getD, hi']

theorem path_mem (hf : c.Facts) {i : ℕ} (hi : i < 729) : c.paths.getD i [] ∈ c.paths := by
  have hi' : i < c.paths.length := hf.len ▸ hi
  rw [List.getD_eq_getElem _ _ hi']
  exact List.getElem_mem hi'

theorem hasBits_sel (hf : c.Facts) {i : ℕ} (hi : i < 729) :
    HasBits X (c.sel (X := X) i) (c.tab.getD i 0) := by
  rw [tab_getD hf hi]
  exact hasBits_path c (fun k hk => hf.path _ (path_mem hf hi) k hk)

theorem sel_zero (hf : c.Facts) : c.sel (X := X) 0 = 1 := by
  show ((c.paths.getD 0 []).map (c.gen (X := X))).prod = 1
  rw [hf.zero]
  rfl

theorem sel_mul (hf : c.Facts) {i j k : ℕ} (hi : i < 729) (hj : j < 729) (hk : k < 729) :
    c.sel (X := X) i * c.sel j = c.sel k ↔
      mul (c.tab.getD i 0) (c.tab.getD j 0) % 2 ^ 2704 = c.tab.getD k 0 % 2 ^ 2704 :=
  ((hasBits_sel hf hi).mul (hasBits_sel hf hj)).eq_iff (hasBits_sel hf hk)

theorem sel_inv (hf : c.Facts) {i : ℕ} (hi : i < 729) :
    c.sel (X := X) (c.invv i) = (c.sel i)⁻¹ := by
  obtain ⟨hlt, heq⟩ := hf.inv i hi
  have h0 : c.tab.getD 0 0 % 2 ^ 2704 = oneBits % 2 ^ 2704 := by
    have h : pathBits c.gbList [] = oneBits := rfl
    rw [tab_getD hf (by norm_num), hf.zero, h]
  have : c.sel (X := X) i * c.sel (c.invv i) = 1 := by
    rw [← sel_zero (X := X) hf, sel_mul hf hi hlt (by norm_num), heq, h0]
  exact eq_inv_of_mul_eq_one_right this

theorem sel_rt (hf : c.Facts) {i g : ℕ} (hi : i < 729) (hg : g < 6) :
    c.sel (X := X) i * c.gen g = c.sel (c.rtv i g) := by
  obtain ⟨hlt, heq⟩ := hf.rt i hi g hg
  exact (((hasBits_sel hf hi).mul (hasBits_gen c g)).eq_iff (hasBits_sel hf hlt)).2 heq

theorem sel_inj (hf : c.Facts) {i j : ℕ} (hi : i < 729) (hj : j < 729)
    (h : c.sel (X := X) i = c.sel j) : i = j := by
  have h1 := ((hasBits_sel hf hi).eq_iff (hasBits_sel hf hj)).1 h
  have hT : c.tab.length = 729 := by simp [F4SylowCert.tab, F4SylowCert.tabList, hf.len]
  have hl : (c.tab.map (· % 2 ^ 2704)).length = 729 := by rw [List.length_map]; exact hT
  refine (hf.nodup.getElem_inj_iff (hi := hl ▸ hi) (hj := hl ▸ hj)).1 ?_
  simp only [List.getElem_map]
  rw [← List.getD_eq_getElem _ 0 (hT ▸ hi), ← List.getD_eq_getElem _ 0 (hT ▸ hj)]
  exact h1

theorem gen_mem_closure {k : ℕ} (hk : k < 6) :
    c.gen (X := X) k ∈ Subgroup.closure (Set.range fun k : Fin 6 => c.gen (X := X) k) :=
  Subgroup.subset_closure ⟨⟨k, hk⟩, rfl⟩

theorem sel_mem_closure (hf : c.Facts) {i : ℕ} (hi : i < 729) :
    c.sel (X := X) i ∈ Subgroup.closure (Set.range fun k : Fin 6 => c.gen (X := X) k) := by
  refine Subgroup.list_prod_mem _ (fun x hx => ?_)
  obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hx
  exact gen_mem_closure (hf.path _ (path_mem hf hi) k hk)

theorem commB_iff (hf : c.Facts) {i j : ℕ} (hi : i < 729) (hj : j < 729) :
    F4SylowCert.commB c.tab i j = true ↔ c.sel (X := X) i * c.sel j = c.sel j * c.sel i := by
  rw [F4SylowCert.commB, decide_eq_true_eq]
  exact (((hasBits_sel (X := X) hf hi).mul (hasBits_sel hf hj)).eq_iff
    ((hasBits_sel hf hj).mul (hasBits_sel hf hi))).symm

theorem conj_ne (hf : c.Facts) {i u v : ℕ} (hi : i < 729) (hu : u < 729) (hv : v < 729)
    (h : c.conjBits c.tab i u ≠ c.conjBits c.tab i v) :
    c.sel (X := X) u * c.sel i * (c.sel u)⁻¹ ≠ c.sel v * c.sel i * (c.sel v)⁻¹ := by
  have bu := ((hasBits_sel (X := X) hf hu).mul (hasBits_sel hf hi)).mul
    (hasBits_sel hf (hf.inv u hu).1)
  have bv := ((hasBits_sel (X := X) hf hv).mul (hasBits_sel hf hi)).mul
    (hasBits_sel hf (hf.inv v hv).1)
  rw [sel_inv hf hu] at bu
  rw [sel_inv hf hv] at bv
  exact fun heq => h ((bu.eq_iff bv).1 heq)

theorem tableWitness (hf : c.Facts) {i : ℕ} (hi : i < 729) :
    i ∈ c.zl ∨ TableWitness (c.sel (X := X)) i := by
  have hw := hf.wit i hi
  have comm : ∀ {j : ℕ}, j < 729 → F4SylowCert.commB c.tab j i = true →
      c.sel (X := X) j * c.sel i = c.sel i * c.sel j :=
    fun hj hb => (commB_iff (X := X) hf hj hi).1 hb
  have ncomm : ∀ {j : ℕ}, j < 729 → F4SylowCert.commB c.tab j i = false →
      c.sel (X := X) j * c.sel i ≠ c.sel i * c.sel j := by
    intro j hj hb h
    have h2 := (commB_iff (X := X) hf hj hi).2 h
    simp [h2] at hb
  generalize c.wit.getD i .exc = w at hw
  cases w with
  | exc =>
    left
    simpa only [F4SylowCert.witOK, decide_eq_true_eq] using hw
  | conj4 u₀ u₁ u₂ u₃ =>
    right
    simp only [F4SylowCert.witOK, Bool.and_eq_true, decide_eq_true_eq] at hw
    obtain ⟨⟨h0, h1, h2, h3⟩, hnd⟩ := hw
    simp only [List.map_cons, List.map_nil, List.nodup_cons, List.mem_cons,
      List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true, not_false_eq_true] at hnd
    obtain ⟨⟨n01, n02, n03⟩, ⟨n12, n13⟩, n23⟩ := hnd
    have key : ∀ {u v : ℕ}, u < 729 → v < 729 →
        c.conjBits c.tab i u ≠ c.conjBits c.tab i v →
        c.sel (X := X) u * c.sel i * (c.sel u)⁻¹ ≠ c.sel v * c.sel i * (c.sel v)⁻¹ :=
      fun hu hv hne => conj_ne hf hi hu hv hne
    refine Or.inl ⟨![u₀, u₁, u₂, u₃], ?_, ?_⟩
    · intro k
      fin_cases k <;> simpa
    · exact fin4_injective (key h0 h1 n01) (key h0 h2 n02) (key h0 h3 n03) (key h1 h2 n12)
        (key h1 h3 n13) (key h2 h3 n23)
  | pair z x y =>
    right
    simp only [F4SylowCert.witOK, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hw
    obtain ⟨⟨⟨⟨⟨hz, hx, hy⟩, nz⟩, cx⟩, cy⟩, nxy⟩ := hw
    refine Or.inr ⟨⟨z, hz, ncomm hz nz⟩, Or.inl ⟨x, y, hx, hy, comm hx cx, comm hy cy, ?_⟩⟩
    intro h
    have h2 := (commB_iff (X := X) hf hx hy).2 h
    simp [h2] at nxy
  | cube z x =>
    right
    simp only [F4SylowCert.witOK, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hw
    obtain ⟨⟨⟨⟨hz, hx⟩, nz⟩, cx⟩, hcube⟩ := hw
    refine Or.inr ⟨⟨z, hz, ncomm hz nz⟩, Or.inr ⟨x, hx, comm hx cx, fun h3 => hcube ?_⟩⟩
    have b3 := ((hasBits_sel (X := X) hf hx).mul (hasBits_sel hf hx)).mul (hasBits_sel hf hx)
    have hone : c.sel (X := X) x * c.sel x * c.sel x = 1 := by
      rw [← h3, pow_succ, sq]
    exact (b3.eq_iff hasBits_one).1 hone

open CFSG.LocalAnalysis.ComponentInitial in
theorem f4_no_elemAbelian_five
    {T : Type} [Group T] (hT : UntwistedChevalleyModel T .F4 2) (D : Subgroup T)
    (hcomm : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a) (hcube : ∀ a ∈ D, a ^ 3 = 1)
    (hcard : Nat.card D = 3 ^ 5) : False := by
  classical
  obtain ⟨X, _, _, hX, ⟨e₀⟩⟩ := nonempty_mulEquiv_adjointGroup .F4 hT
  obtain ⟨e⟩ : Nonempty (T ≃* adjointGroup ReeTag.F4.tag X) := ⟨e₀⟩
  have : CharP X 2 := finite_field_prime_power_characteristic Nat.prime_two (k := 1)
    (le_refl 1) (by simpa using hX)
  have hf : f4ThreeCert.Facts :=
    F4SylowCert.facts_of_check _ (Certificates.certificate271060 : F4ThreeRankCheck)
  have hG : Nat.card (adjointGroup ReeTag.F4.tag X) = 3311126603366400 := by
    have h := CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_F4 (K := X)
    rw [hX] at h
    exact h.trans (by norm_num [CFSG.Open.ordF4])
  have : Finite (adjointGroup ReeTag.F4.tag X) :=
    Nat.finite_of_card_ne_zero (by rw [hG]; norm_num)
  refine no_elemAbelian_five_of_table (fun k : Fin 6 => f4ThreeCert.gen (X := X) k)
    (f4ThreeCert.sel (X := X)) (sel_zero hf) (fun i hi j hj h => sel_inj hf hi hj h)
    (fun i hi => sel_mem_closure hf hi)
    (fun i hi k => ⟨f4ThreeCert.rtv i k, (hf.rt i hi k k.2).1, sel_rt hf hi k.2⟩)
    f4ThreeCert.zl.toFinset ?_ (fun i hi => ?_) ?_ (D.map e.toMonoidHom) ?_ ?_ ?_
  · exact lt_of_le_of_lt (List.toFinset_card_le _) (lt_of_lt_of_le hf.zl (by norm_num))
  · rcases tableWitness (X := X) hf hi with hz | hw
    · exact Or.inl (List.mem_toFinset.2 hz)
    · exact Or.inr hw
  · rw [hG]
    norm_num
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, hcomm a ha b hb]
  · rintro _ ⟨a, ha, rfl⟩
    rw [← map_pow, hcube a ha, map_one]
  · rw [Subgroup.card_map_of_injective e.injective, hcard]

end Table

end CFSG.RankThree.PartOne.F106
