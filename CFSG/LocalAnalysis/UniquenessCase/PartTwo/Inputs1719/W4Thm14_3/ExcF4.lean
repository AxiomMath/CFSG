module

public import CFSG.RankThree.GF2n.Stroth80.Sec83Additive
public import CFSG.RankThree.PartTwo.Sec19.SeitzTrialityPairUnitary

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_3

section F4

variable {F : Type} [Field F] [Fintype F] [CharP F 2]

private lemma exists_omega_of_card_sixtyfour (hF : Fintype.card F = 2 ^ 6) :
    ∃ ω : F, ω ^ 2 = ω + 1 ∧ ω ^ 3 = 1 ∧ ω ≠ 0 ∧ ω ≠ 1 := by
  have hcard : Nat.card F = 64 := by rw [Nat.card_eq_fintype_card, hF]; norm_num
  have h3 : 3 ∣ Nat.card F - 1 := by rw [hcard]; norm_num
  obtain ⟨ω, hω⟩ := CFSG.RankThree.PartTwo.Sec19.NF5Pair.exists_omega (F := F) h3
  have hsq : ω ^ 2 = ω + 1 := by
    linear_combination hω - (ω + 1) * CharTwo.two_eq_zero (R := F)
  have hcube : ω ^ 3 = 1 := by linear_combination (ω - 1) * hω
  have hne0 : ω ≠ 0 := by
    intro h
    rw [h] at hω
    norm_num at hω
  have hne1 : ω ≠ 1 := by
    intro h
    rw [h] at hω
    have h3' : (1 : F) + 1 + 1 = 0 := by simpa using hω
    have h4 : (1 : F) = 0 := by linear_combination h3' - CharTwo.two_eq_zero (R := F)
    exact one_ne_zero h4
  exact ⟨ω, hsq, hcube, hne0, hne1⟩

private lemma pow_four_eq_self_iff {ω : F} (hω2 : ω ^ 2 = ω + 1) (hω3 : ω ^ 3 = 1)
    (l : F) : l ^ 4 = l ↔ l = 0 ∨ l = 1 ∨ l = ω ∨ l = ω ^ 2 := by
  constructor
  · intro h
    by_cases hl : l = 0
    · exact Or.inl hl
    · have hl3 : l ^ 3 = 1 := by
        have h1 : l * l ^ 3 = l * 1 := by
          calc l * l ^ 3 = l ^ 4 := by ring
            _ = l := h
            _ = l * 1 := by ring
        exact mul_left_cancel₀ hl h1
      have hfac : (l - 1) * (l ^ 2 + l + 1) = 0 := by
        have h1 : (l - 1) * (l ^ 2 + l + 1) = l ^ 3 - 1 := by ring
        rw [h1, hl3]
        ring
      rcases mul_eq_zero.mp hfac with h1 | h2
      · exact Or.inr (Or.inl (sub_eq_zero.mp h1))
      · have hfac2 : (l - ω) * (l - ω ^ 2) = 0 := by
          have hsum : ω + ω ^ 2 = 1 := by
            rw [hω2, ← add_assoc, CharTwo.add_self_eq_zero, zero_add]
          have h1 : (l - ω) * (l - ω ^ 2) = l ^ 2 - (ω + ω ^ 2) * l + ω ^ 3 := by ring
          rw [h1, hsum, hω3]
          have h2' : l ^ 2 - 1 * l + 1 = l ^ 2 + l + 1 := by
            rw [one_mul, CharTwo.sub_eq_add]
          rw [h2']
          exact h2
        rcases mul_eq_zero.mp hfac2 with h3 | h4
        · exact Or.inr (Or.inr (Or.inl (sub_eq_zero.mp h3)))
        · exact Or.inr (Or.inr (Or.inr (sub_eq_zero.mp h4)))
  · intro h
    rcases h with h | h | h | h
    · rw [h]; ring
    · rw [h]; ring
    · rw [h]
      calc ω ^ 4 = ω ^ 3 * ω := by ring
        _ = 1 * ω := by rw [hω3]
        _ = ω := by ring
    · rw [h]
      calc (ω ^ 2) ^ 4 = (ω ^ 3) ^ 2 * ω ^ 2 := by ring
        _ = 1 * ω ^ 2 := by rw [hω3, one_pow, one_mul]
        _ = ω ^ 2 := by ring

private def f4Sub : AddSubgroup F where
  carrier := {l : F | l ^ 4 = l}
  zero_mem' := by norm_num
  add_mem' := by
    intro a b ha hb
    show (a + b) ^ 4 = a + b
    have h4 : (a + b) ^ 4 = a ^ 4 + b ^ 4 := by
      simpa using add_pow_char_pow (R := F) a b 2 2
    rw [h4, ha, hb]
  neg_mem' := by
    intro a ha
    show (-a) ^ 4 = -a
    have h4 : (-a) ^ 4 = a ^ 4 := by
      rw [show -a = (-1 : F) * a by ring, mul_pow]
      norm_num
    rw [h4, ha, CharTwo.neg_eq]

private lemma card_f4Sub {ω : F} (hω2 : ω ^ 2 = ω + 1) (hω3 : ω ^ 3 = 1) (hω0 : ω ≠ 0)
    (hω1 : ω ≠ 1) : Nat.card ↥(f4Sub (F := F)) = 4 := by
  classical
  have h0w : (0 : F) ≠ ω := hω0.symm
  have h0w2 : (0 : F) ≠ ω ^ 2 := by
    intro h
    have h1 : ω + 1 = 0 := by rw [← hω2, h]
    have h2 : -ω = 1 := by rw [neg_eq_iff_add_eq_zero]; exact h1
    rw [CharTwo.neg_eq] at h2
    exact hω1 h2
  have h1w : (1 : F) ≠ ω := hω1.symm
  have h1w2 : (1 : F) ≠ ω ^ 2 := by
    intro h
    have h1 : ω + 1 = 1 := by rw [← hω2, h]
    have h2 : ω + 1 = (0 : F) + 1 := by rw [zero_add]; exact h1
    exact hω0 (add_right_cancel h2)
  have hww2 : ω ≠ ω ^ 2 := by
    intro h
    have h1 : ω + 1 = ω := by
      calc ω + 1 = ω ^ 2 := hω2.symm
        _ = ω := h.symm
    have h2 : ω + 1 = ω + 0 := by rw [add_zero]; exact h1
    have h3 : (1 : F) = 0 := add_left_cancel h2
    exact one_ne_zero h3
  have hcard : ({0, 1, ω, ω ^ 2} : Finset F).card = 4 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
      Finset.card_insert_of_notMem, Finset.card_singleton]
    all_goals simp [h0w, h0w2, h1w, h1w2, hww2]
  have hmem : ∀ x : F, x ∈ ({0, 1, ω, ω ^ 2} : Finset F) ↔ x ∈ f4Sub (F := F) := by
    intro x
    rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton]
    show (x = 0 ∨ x = 1 ∨ x = ω ∨ x = ω ^ 2) ↔ x ^ 4 = x
    exact (pow_four_eq_self_iff hω2 hω3 x).symm
  let f : ↥(f4Sub (F := F)) → {x // x ∈ ({0, 1, ω, ω ^ 2} : Finset F)} :=
    fun x => ⟨(x : F), (hmem (x : F)).mpr x.2⟩
  have hbij : Function.Bijective f := by
    constructor
    · intro a b hab
      exact Subtype.ext (congrArg (fun z : {x // x ∈ ({0, 1, ω, ω ^ 2} : Finset F)} => (z : F)) hab)
    · intro b
      exact ⟨⟨(b : F), (hmem (b : F)).mp b.2⟩, Subtype.ext rfl⟩
  have h1 := Nat.card_eq_of_bijective f hbij
  rw [h1, Nat.card_eq_fintype_card, Fintype.card_coe]
  exact hcard

private def f4Line (x : F) : AddSubgroup F := (f4Sub (F := F)).map (AddMonoidHom.mulRight x)

private lemma mem_f4Line (x t : F) :
    t ∈ f4Line x ↔ ∃ l : F, l ^ 4 = l ∧ l * x = t := by
  rw [f4Line, AddSubgroup.mem_map]
  constructor
  · rintro ⟨l, hl, hlt⟩
    exact ⟨l, hl, hlt⟩
  · rintro ⟨l, hl, hlt⟩
    exact ⟨l, hl, hlt⟩

private lemma card_map_f4Sub_eq_four {ω : F} (hω2 : ω ^ 2 = ω + 1) (hω3 : ω ^ 3 = 1) (hω0 : ω ≠ 0)
    (hω1 : ω ≠ 1) {x : F} (hx : x ≠ 0) : Nat.card ↥(f4Line x) = 4 := by
  rw [f4Line, AddSubgroup.card_map_of_injective]
  · exact card_f4Sub hω2 hω3 hω0 hω1
  · intro a b h
    exact mul_right_cancel₀ hx h

private lemma f4Line_le_of_mem {ω : F} (hω2 : ω ^ 2 = ω + 1) (hω3 : ω ^ 3 = 1)
    {A₀ : AddSubgroup F} {x : F} (hx : x ∈ A₀) (hωx : ω * x ∈ A₀) :
    f4Line x ≤ A₀ := by
  intro t ht
  rw [mem_f4Line] at ht
  obtain ⟨l, hl, rfl⟩ := ht
  rcases (pow_four_eq_self_iff hω2 hω3 l).mp hl with h0 | h1 | h2 | h3
  · rw [h0]; simpa using AddSubgroup.zero_mem (A₀ : AddSubgroup F)
  · rw [h1]; simpa using hx
  · rw [h2]; exact hωx
  · rw [h3]
    have h4 : ω ^ 2 * x = ω * x + x := by rw [hω2]; ring
    rw [h4]
    exact AddSubgroup.add_mem _ hωx hx

private lemma mem_f4Line_of_mul_pow_four_eq {x y : F} (hx : x ≠ 0)
    (h : x * y ^ 4 = y * x ^ 4) : y ∈ f4Line x := by
  rw [mem_f4Line]
  have hy4 : y ^ 4 = y * x ^ 3 := by
    have h' : y ^ 4 * x = (y * x ^ 3) * x := by
      calc y ^ 4 * x = x * y ^ 4 := by ring
        _ = y * x ^ 4 := h
        _ = (y * x ^ 3) * x := by ring
    exact mul_right_cancel₀ hx h'
  refine ⟨y / x, ?_, ?_⟩
  · rw [div_pow, hy4]
    field_simp
  · rw [div_mul_cancel₀ _ hx]

private lemma mul_pow_four_ne_of_notMem {x y : F} (hx : x ≠ 0) (hy : y ∉ f4Line x) :
    x * y ^ 4 ≠ y * x ^ 4 :=
  fun h => hy (mem_f4Line_of_mul_pow_four_eq hx h)

private lemma omega_mul_mem_inf {A₀ : AddSubgroup F} {ω z : F} (hω2 : ω ^ 2 = ω + 1)
    (hz : z ∈ A₀ ⊓ A₀.map (AddMonoidHom.mulLeft ω)) :
    ω * z ∈ A₀ ⊓ A₀.map (AddMonoidHom.mulLeft ω) := by
  obtain ⟨hzA, hzK⟩ := AddSubgroup.mem_inf.mp hz
  obtain ⟨a, ha, haz⟩ := AddSubgroup.mem_map.mp hzK
  have hz' : z = ω * a := haz.symm
  constructor
  · have h1 : ω * z = z + a := by
      rw [hz']
      calc ω * (ω * a) = ω ^ 2 * a := by ring
        _ = (ω + 1) * a := by rw [hω2]
        _ = ω * a + a := by ring
    rw [h1]
    exact AddSubgroup.add_mem _ hzA ha
  · exact AddSubgroup.mem_map.mpr ⟨z, hzA, rfl⟩

private lemma card_mul_le_of_map {A₀ : AddSubgroup F} {ω : F} (hω0 : ω ≠ 0)
    (hF64 : Nat.card F = 64) :
    Nat.card ↥A₀ * Nat.card ↥A₀ ≤
      64 * Nat.card ↥(A₀ ⊓ A₀.map (AddMonoidHom.mulLeft ω)) := by
  classical
  have hprod := CFSG.RankThree.GF2n.Stroth80.card_sup_mul_card_inf_addSubgroup A₀
    (A₀.map (AddMonoidHom.mulLeft ω))
  have hmap : Nat.card ↥(A₀.map (AddMonoidHom.mulLeft ω)) = Nat.card ↥A₀ :=
    AddSubgroup.card_map_of_injective (fun a b h => mul_left_cancel₀ hω0 h)
  rw [hmap] at hprod
  have hsup : Nat.card ↥(A₀ ⊔ A₀.map (AddMonoidHom.mulLeft ω)) ≤ 64 := by
    have h := Nat.card_le_card_of_injective
      (fun x : ↥(A₀ ⊔ A₀.map (AddMonoidHom.mulLeft ω)) => (x : F)) Subtype.val_injective
    rwa [hF64] at h
  rw [← hprod]
  exact Nat.mul_le_mul_right _ hsup

theorem exists_pair_of_eight_le (hF : Fintype.card F = 2 ^ 6) (A₀ : AddSubgroup F)
    (hA : 8 ≤ Nat.card A₀) : ∃ x ∈ A₀, ∃ y ∈ A₀, x ≠ 0 ∧ x * y ^ 4 ≠ y * x ^ 4 := by
  classical
  obtain ⟨ω, hω2, hω3, hω0, hω1⟩ := exists_omega_of_card_sixtyfour hF
  by_contra h
  push Not at h
  have h1 : 1 < Nat.card A₀ := by omega
  have hcardA : 1 < Fintype.card ↥A₀ := by rw [← Nat.card_eq_fintype_card]; exact h1
  obtain ⟨x, hx0⟩ := Fintype.exists_ne_of_one_lt_card hcardA (0 : ↥A₀)
  have hxmem : (x : F) ∈ A₀ := x.2
  have hxne : (x : F) ≠ 0 := by
    intro hh
    exact hx0 (Subtype.ext hh)
  have hle : A₀ ≤ f4Line (x : F) := by
    intro y hy
    exact mem_f4Line_of_mul_pow_four_eq hxne (h (x : F) hxmem y hy hxne)
  have hlecard : Nat.card A₀ ≤ Nat.card ↥(f4Line (x : F)) :=
    Nat.card_le_card_of_injective
      (fun z : ↥A₀ => (⟨(z : F), hle z.2⟩ : ↥(f4Line (x : F))))
      (fun a b hab => Subtype.ext
        (congrArg (fun z : ↥(f4Line (x : F)) => (z : F)) hab))
  rw [card_map_f4Sub_eq_four hω2 hω3 hω0 hω1 hxne] at hlecard
  omega

theorem exists_line_of_sixteen_le (hF : Fintype.card F = 2 ^ 6) (A₀ : AddSubgroup F)
    (hA : 16 ≤ Nat.card A₀) :
    ∃ (x : F) (K : AddSubgroup F), x ≠ 0 ∧ K ≤ A₀ ∧ Nat.card K = 4 ∧
      ∀ t ∈ K, ∃ l : F, l ^ 4 = l ∧ t = l * x := by
  classical
  obtain ⟨ω, hω2, hω3, hω0, hω1⟩ := exists_omega_of_card_sixtyfour hF
  have hF64 : Nat.card F = 64 := by rw [Nat.card_eq_fintype_card, hF]; norm_num
  let K1 : AddSubgroup F := A₀.map (AddMonoidHom.mulLeft ω)
  have hineq := card_mul_le_of_map (A₀ := A₀) (ω := ω) hω0 hF64
  have h4 : 4 ≤ Nat.card ↥(A₀ ⊓ K1) := by
    have h256 : 256 ≤ Nat.card ↥A₀ * Nat.card ↥A₀ := by
      calc 256 = 16 * 16 := by norm_num
        _ ≤ Nat.card ↥A₀ * Nat.card ↥A₀ := Nat.mul_le_mul hA hA
    have h64 : 64 * 4 ≤ 64 * Nat.card ↥(A₀ ⊓ K1) := by
      calc 64 * 4 = 256 := by norm_num
        _ ≤ Nat.card ↥A₀ * Nat.card ↥A₀ := h256
        _ ≤ 64 * Nat.card ↥(A₀ ⊓ K1) := hineq
    exact Nat.le_of_mul_le_mul_left h64 (by norm_num)
  have hcardB : 1 < Fintype.card ↥(A₀ ⊓ K1) := by
    rw [← Nat.card_eq_fintype_card]; omega
  obtain ⟨x, hx0⟩ := Fintype.exists_ne_of_one_lt_card hcardB (0 : ↥(A₀ ⊓ K1))
  have hxmem : (x : F) ∈ A₀ := x.2.1
  have hxinf : (x : F) ∈ A₀ ⊓ K1 := x.2
  have hxne : (x : F) ≠ 0 := by
    intro hh
    exact hx0 (Subtype.ext hh)
  have hωx : ω * (x : F) ∈ A₀ := (AddSubgroup.mem_inf.mp (omega_mul_mem_inf hω2 hxinf)).1
  refine ⟨(x : F), f4Line (x : F), hxne, ?_, card_map_f4Sub_eq_four hω2 hω3 hω0 hω1 hxne, ?_⟩
  · exact f4Line_le_of_mem hω2 hω3 hxmem hωx
  · intro t ht
    obtain ⟨l, hl, hlt⟩ := (mem_f4Line (x : F) t).mp ht
    exact ⟨l, hl, hlt.symm⟩

theorem exists_plane_of_thirtytwo_le (hF : Fintype.card F = 2 ^ 6) (A₀ : AddSubgroup F)
    (hA : 32 ≤ Nat.card A₀) :
    ∃ (x y : F) (K : AddSubgroup F), x ≠ 0 ∧ x * y ^ 4 ≠ y * x ^ 4 ∧ K ≤ A₀ ∧
      Nat.card K = 16 ∧ ∀ t ∈ K, ∃ l l' : F, l ^ 4 = l ∧ l' ^ 4 = l' ∧ t = l * x + l' * y := by
  classical
  obtain ⟨ω, hω2, hω3, hω0, hω1⟩ := exists_omega_of_card_sixtyfour hF
  have hF64 : Nat.card F = 64 := by rw [Nat.card_eq_fintype_card, hF]; norm_num
  let K1 : AddSubgroup F := A₀.map (AddMonoidHom.mulLeft ω)
  have hineq := card_mul_le_of_map (A₀ := A₀) (ω := ω) hω0 hF64
  have h16 : 16 ≤ Nat.card ↥(A₀ ⊓ K1) := by
    have h1024 : 1024 ≤ Nat.card ↥A₀ * Nat.card ↥A₀ := by
      calc 1024 = 32 * 32 := by norm_num
        _ ≤ Nat.card ↥A₀ * Nat.card ↥A₀ := Nat.mul_le_mul hA hA
    have h64 : 64 * 16 ≤ 64 * Nat.card ↥(A₀ ⊓ K1) := by
      calc 64 * 16 = 1024 := by norm_num
        _ ≤ Nat.card ↥A₀ * Nat.card ↥A₀ := h1024
        _ ≤ 64 * Nat.card ↥(A₀ ⊓ K1) := hineq
    exact Nat.le_of_mul_le_mul_left h64 (by norm_num)
  have hcardB : 1 < Fintype.card ↥(A₀ ⊓ K1) := by
    rw [← Nat.card_eq_fintype_card]; omega
  obtain ⟨x, hx0⟩ := Fintype.exists_ne_of_one_lt_card hcardB (0 : ↥(A₀ ⊓ K1))
  have hxmem : (x : F) ∈ A₀ := x.2.1
  have hxinf : (x : F) ∈ A₀ ⊓ K1 := x.2
  have hxne : (x : F) ≠ 0 := by
    intro hh
    exact hx0 (Subtype.ext hh)
  have hωx : ω * (x : F) ∈ A₀ := (AddSubgroup.mem_inf.mp (omega_mul_mem_inf hω2 hxinf)).1
  have hyex : ∃ y : ↥(A₀ ⊓ K1), ((y : F)) ∉ f4Line (x : F) := by
    by_contra h
    push Not at h
    have hsub : A₀ ⊓ K1 ≤ f4Line (x : F) := fun z hz => h ⟨z, hz⟩
    have hlecard : Nat.card ↥(A₀ ⊓ K1) ≤ Nat.card ↥(f4Line (x : F)) :=
      Nat.card_le_card_of_injective
        (fun z : ↥(A₀ ⊓ K1) => (⟨(z : F), hsub z.2⟩ : ↥(f4Line (x : F))))
        (fun a b hab => Subtype.ext
          (congrArg (fun z : ↥(f4Line (x : F)) => (z : F)) hab))
    rw [card_map_f4Sub_eq_four hω2 hω3 hω0 hω1 hxne] at hlecard
    omega
  obtain ⟨y, hy⟩ := hyex
  have hymem : (y : F) ∈ A₀ := y.2.1
  have hyinf : (y : F) ∈ A₀ ⊓ K1 := y.2
  have hωy : ω * (y : F) ∈ A₀ := (AddSubgroup.mem_inf.mp (omega_mul_mem_inf hω2 hyinf)).1
  have hyne : (y : F) ≠ 0 := by
    intro hh
    apply hy
    rw [mem_f4Line]
    exact ⟨0, by norm_num, by rw [hh]; ring⟩
  have hdisj : f4Line (x : F) ⊓ f4Line (y : F) = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    rw [AddSubgroup.mem_bot]
    rw [AddSubgroup.mem_inf, mem_f4Line, mem_f4Line] at hz
    obtain ⟨⟨l, hl, hlz⟩, ⟨l', hl', hl'z⟩⟩ := hz
    by_cases hl'0 : l' = 0
    · rw [hl'0, zero_mul] at hl'z
      exact hl'z.symm
    · exfalso
      apply hy
      rw [mem_f4Line]
      refine ⟨l / l', ?_, ?_⟩
      · rw [div_pow, hl, hl']
      · have heq : l * x = l' * y := hlz.trans hl'z.symm
        rw [div_mul_eq_mul_div, div_eq_iff hl'0, heq]
        ring
  have hcard16 : Nat.card ↥(f4Line (x : F) ⊔ f4Line (y : F)) = 16 := by
    let f : ↥(f4Line (x : F)) × ↥(f4Line (y : F)) → ↥(f4Line (x : F) ⊔ f4Line (y : F)) :=
      fun p => ⟨(p.1 : F) + (p.2 : F), AddSubgroup.add_mem_sup p.1.2 p.2.2⟩
    have hbij : Function.Bijective f := by
      constructor
      · intro p q hpq
        have hp : (p.1 : F) + (p.2 : F) = (q.1 : F) + (q.2 : F) :=
          congrArg (fun z : ↥(f4Line (x : F) ⊔ f4Line (y : F)) => (z : F)) hpq
        have hmem : (p.1 : F) - (q.1 : F) = (q.2 : F) - (p.2 : F) := by
          linear_combination hp
        have h1 : (p.1 : F) - (q.1 : F) ∈ f4Line (x : F) :=
          AddSubgroup.sub_mem _ p.1.2 q.1.2
        have h2 : (p.1 : F) - (q.1 : F) ∈ f4Line (y : F) := by
          rw [hmem]; exact AddSubgroup.sub_mem _ q.2.2 p.2.2
        have h0 : (p.1 : F) - (q.1 : F) = 0 := by
          have hz : (p.1 : F) - (q.1 : F) ∈ (⊥ : AddSubgroup F) := by
            rw [← hdisj]
            exact AddSubgroup.mem_inf.mpr ⟨h1, h2⟩
          simpa using hz
        have hp1 : p.1 = q.1 := Subtype.ext (sub_eq_zero.mp h0)
        have hp2 : p.2 = q.2 := by
          apply Subtype.ext
          have h := hp
          rw [hp1] at h
          exact add_left_cancel h
        exact Prod.ext hp1 hp2
      · rintro ⟨z, hz⟩
        rw [AddSubgroup.mem_sup] at hz
        obtain ⟨a, ha, b, hb, hab⟩ := hz
        exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), Subtype.ext hab⟩
    have h1 := Nat.card_eq_of_bijective f hbij
    rw [← h1, Nat.card_prod, card_map_f4Sub_eq_four hω2 hω3 hω0 hω1 hxne,
      card_map_f4Sub_eq_four hω2 hω3 hω0 hω1 hyne]
  refine ⟨(x : F), (y : F), f4Line (x : F) ⊔ f4Line (y : F), hxne, ?_, ?_, hcard16, ?_⟩
  · exact mul_pow_four_ne_of_notMem hxne hy
  · exact sup_le (f4Line_le_of_mem hω2 hω3 hxmem hωx)
      (f4Line_le_of_mem hω2 hω3 hymem hωy)
  · intro t ht
    rw [AddSubgroup.mem_sup] at ht
    obtain ⟨a, ha, b, hb, hab⟩ := ht
    obtain ⟨l, hl, hla⟩ := (mem_f4Line (x : F) a).mp ha
    obtain ⟨l', hl', hlb⟩ := (mem_f4Line (y : F) b).mp hb
    refine ⟨l, l', hl, hl', ?_⟩
    rw [← hab, ← hla, ← hlb]

end F4

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_3
