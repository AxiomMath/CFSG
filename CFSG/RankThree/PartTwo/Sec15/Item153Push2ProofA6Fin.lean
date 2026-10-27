module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_21FinA6
public import CFSG.RankThree.PartTwo.Sec15.Item153Push2ProofPerm
import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltHypIISix
import CFSG.ClassicalInvolution.Q3.TL4E3C269G9A

public section

namespace CFSG.RankThree.PartTwo.Sec15.Push153B.A6

open CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts

@[expose] def conjC (r u : List ℕ) : List ℕ := Core.cmul (Core.cmul r u) (Core.cmul r r)

@[expose] def commC (u v : List ℕ) : Bool := Core.cmul u v == Core.cmul v u

@[expose] def cubeC (u : List ℕ) : List ℕ := Core.cmul (Core.cmul u u) u

@[expose] def wC (r u : List ℕ) : List ℕ :=
  Core.cmul (Core.cmul u (conjC r u)) (conjC (Core.cmul r r) u)

@[expose] def wSet (r : List ℕ) : List (List ℕ) :=
  Core.p0Lit.filter fun u => Core.p0Lit.contains (conjC r u) &&
    Core.p0Lit.contains (conjC (Core.cmul r r) u)

@[expose] def vlSet (r : List ℕ) : List (List ℕ) :=
  (wSet r).filter fun u => !(u == Core.cid) && !(commC u r && !Out21.A6.inM10C u) &&
    !(commC (wC r u) r && !Out21.A6.inM10C (wC r u))

@[expose] def repsC : List (List ℕ) :=
  [[0, 2, 9, 8, 6, 4, 5, 3, 7, 1], [0, 3, 8, 4, 1, 9, 2, 5, 6, 7], [0, 5, 4, 9, 7, 8, 3, 2, 1, 6],
    [1, 9, 2, 8, 3, 7, 5, 6, 4, 0]]

@[expose] def repConjC : List (List ℕ) :=
  [[9, 0, 1, 5, 7, 6, 8, 4, 3, 2], [9, 0, 4, 1, 2, 7, 3, 6, 5, 8], [9, 0, 3, 8, 4, 1, 7, 5, 2, 6],
    [0, 1, 9, 4, 3, 8, 7, 6, 5, 2]]

@[expose] def tAddC : List ℕ := [1, 2, 0, 4, 5, 3, 7, 8, 6, 9]

@[expose] def tIC : List ℕ := [3, 4, 5, 6, 7, 8, 0, 1, 2, 9]

@[expose] def t9c : List (List ℕ) :=
  [[0, 1, 2, 3, 4, 5, 6, 7, 8, 9], [1, 2, 0, 4, 5, 3, 7, 8, 6, 9], [2, 0, 1, 5, 3, 4, 8, 6, 7, 9],
    [3, 4, 5, 6, 7, 8, 0, 1, 2, 9], [4, 5, 3, 7, 8, 6, 1, 2, 0, 9], [5, 3, 4, 8, 6, 7, 2, 0, 1, 9],
    [6, 7, 8, 0, 1, 2, 3, 4, 5, 9], [7, 8, 6, 1, 2, 0, 4, 5, 3, 9], [8, 6, 7, 2, 0, 1, 5, 3, 4, 9]]

theorem orb_check : Core.pslLit.all (fun x => !(cubeC x == Core.cid) || x == Core.cid ||
    Core.p0Lit.any fun p => repsC.any fun r => Core.cmul p x == Core.cmul r p) = true := by
  decide +kernel

theorem repConj_check : repsC.all (fun r => repConjC.any fun g =>
    Core.cmul g r == Core.cmul tAddC g) = true := by
  decide +kernel

theorem repConj_aut : repConjC.all (fun g => Core.autL.contains g) = true := by
  decide +kernel

theorem reps_psl : repsC.all (fun r => Core.pslLit.contains r) = true := by
  decide +kernel

theorem lat_check : repsC.all (fun r => (vlSet r).all fun a => (vlSet r).all fun b =>
    b == a || b == conjC r a || b == conjC (Core.cmul r r) a) = true := by
  decide +kernel

theorem cent_check : repsC.all (fun r => (vlSet r).isEmpty || Core.pslLit.all fun k =>
    !(cubeC k == Core.cid) || k == Core.cid || (vlSet r).any fun v => !commC k v) = true := by
  decide +kernel

theorem f6_check : Core.autL.all (fun u => !(commC u tAddC && !Out21.A6.inM10C u) ||
    t9c.any fun w => !(w == Core.cid) && !(w == tAddC) && !(w == Core.cmul tAddC tAddC) &&
      Core.cmul u w == Core.cmul (Core.cmul w w) u) = true := by
  decide +kernel

theorem ordT9_check : Core.autL.all (fun u => !(commC u tAddC && cubeC u == Core.cid) ||
    t9c.contains u) = true := by
  decide +kernel

theorem t9_check : t9c.all (fun w => Core.pslLit.contains w && cubeC w == Core.cid &&
    commC w tAddC && decide (w.Perm (List.range 10))) = true := by
  decide +kernel

theorem t9_gen_check : t9c.all (fun w => w == Core.cid || w == tAddC ||
    w == Core.cmul tAddC tAddC || [0, 1, 2].any fun i => [0, 1, 2].any fun j =>
      Core.cmul (Core.cpow tAddC i) (Core.cpow w j) == tIC) = true := by
  decide +kernel

theorem t9_span_check : t9c.all (fun t => [0, 1, 2].any fun i => [0, 1, 2].any fun j =>
    Core.cmul (Core.cpow tAddC i) (Core.cpow tIC j) == t) = true := by
  decide +kernel

theorem p0_perm_check : Core.p0Lit.all (fun c => decide (c.Perm (List.range 10))) = true := by
  decide +kernel

theorem t9c_one : List.range 10 ∈ t9c := by decide +kernel

theorem t9c_mul : ∀ a ∈ t9c, ∀ b ∈ t9c, cmul a b ∈ t9c := by decide +kernel

theorem t9c_three : ∀ a ∈ t9c, cmul (csq a) a = List.range 10 := by decide +kernel

theorem code_tAdd : code A6Models.tAdd = tAddC := by decide +kernel

theorem ncC_check : Core.pslLit.contains [0, 2, 9, 8, 6, 4, 5, 3, 7, 1] = true ∧
    cubeC [0, 2, 9, 8, 6, 4, 5, 3, 7, 1] = Core.cid ∧
    commC tAddC [0, 2, 9, 8, 6, 4, 5, 3, 7, 1] = false := by
  decide +kernel

theorem code_eq_pcode (u : P10) : code u = pcode u := rfl

theorem code_conjC (r u : P10) : conjC (code r) (code u) = code (r * u * (r * r)) := by
  rw [conjC, code_mul, code_mul, code_mul]

theorem code_cubeC (u : P10) : cubeC (code u) = code (u ^ 3) := by
  rw [cubeC, show u ^ 3 = u * u * u by rw [pow_succ, pow_two], code_mul, code_mul]

theorem commC_iff (u v : P10) : commC (code u) (code v) = true ↔ u * v = v * u := by
  rw [commC, beq_iff_eq, ← code_mul, ← code_mul]
  exact code_injective.eq_iff

theorem code_wC (r u : P10) :
    wC (code r) (code u) = code (u * (r * u * (r * r)) * ((r * r) * u * ((r * r) * (r * r)))) := by
  simp only [wC, conjC, code_mul]

theorem cubeC_eq_cid_iff (u : P10) : cubeC (code u) = Core.cid ↔ u ^ 3 = 1 := by
  rw [code_cubeC, ← code_one]
  exact code_injective.eq_iff

theorem code_eq_cid_iff (u : P10) : code u = Core.cid ↔ u = 1 := by
  rw [← code_one]
  exact code_injective.eq_iff

theorem contains_iff {l : List (List ℕ)} {c : List ℕ} : l.contains c = true ↔ c ∈ l := by
  simp

theorem exists_P0_of_code {c : List ℕ} (hc : c ∈ Core.p0Lit) : ∃ p ∈ P0, code p = c := by
  have h := List.all_eq_true.mp p0_perm_check c hc
  obtain ⟨σ, hσ⟩ := exists_pcode_eq (n := 10) (of_decide_eq_true h)
  exact ⟨σ, (mem_P0_iff σ).mpr (by rw [code_eq_pcode, hσ]; exact hc), hσ⟩

theorem inv_eq_sq {x : P10} (hx3 : x ^ 3 = 1) : x⁻¹ = x * x := by
  rw [inv_eq_iff_mul_eq_one, ← pow_two, ← pow_succ']
  exact hx3

theorem m10_conj_mem {g m : P10} (hg : g ∈ A6Models.autA6) (hm : m ∈ A6Models.m10) :
    g * m * g⁻¹ ∈ A6Models.m10 := by
  have hle : A6Models.m10 ≤ A6Models.autA6 :=
    CFSG.ClassicalInvolution.Q3.TL4.E3C269G9.m10_le_autA6
  have hidx : (A6Models.m10.subgroupOf A6Models.autA6).index = 2 := by
    have h := Subgroup.card_mul_index (A6Models.m10.subgroupOf A6Models.autA6)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv, Out21.A6.card_m10,
      card_autA6] at h
    omega
  have hN := Subgroup.normal_of_index_eq_two hidx
  have := hN.conj_mem ⟨m, hle hm⟩ (Subgroup.mem_subgroupOf.mpr hm) ⟨g, hg⟩
  simpa using Subgroup.mem_subgroupOf.mp this

theorem exists_conj_rep {x : P10} (hx : x ∈ A6Models.psl29) (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1) :
    ∃ p ∈ P0, ∃ r : P10, code r ∈ repsC ∧ p * x * p⁻¹ = r := by
  have h := List.all_eq_true.mp orb_check (code x) ((mem_psl29_iff x).mp hx)
  have h3 : (cubeC (code x) == Core.cid) = true := by
    rw [beq_iff_eq, cubeC_eq_cid_iff]; exact hx3
  have h1 : (code x == Core.cid) = false := by
    rw [beq_eq_false_iff_ne, Ne, code_eq_cid_iff]; exact hx1
  rw [h3, h1] at h
  simp only [Bool.not_true, Bool.false_or, List.any_eq_true, beq_iff_eq] at h
  obtain ⟨pc, hpc, rc, hrc, he⟩ := h
  obtain ⟨p, hp, rfl⟩ := exists_P0_of_code hpc
  obtain ⟨r, -, rfl⟩ := exists_psl29_of_code
    (List.all_eq_true.mp reps_psl rc hrc |> contains_iff.mp)
  refine ⟨p, hp, r, hrc, ?_⟩
  have : p * x = r * p := by
    apply code_injective
    rw [code_mul, code_mul]
    exact he
  rw [this, mul_inv_cancel_right]

theorem exists_conj_tAdd {x : P10} (hx : x ∈ A6Models.psl29) (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1) :
    ∃ g ∈ A6Models.autA6, g * x * g⁻¹ = A6Models.tAdd := by
  obtain ⟨p, hp, r, hr, hpr⟩ := exists_conj_rep hx hx3 hx1
  have h := List.all_eq_true.mp repConj_check (code r) hr
  simp only [List.any_eq_true, beq_iff_eq] at h
  obtain ⟨gc, hgc, hge⟩ := h
  obtain ⟨g, hg, rfl⟩ := CFSG.ComponentClassification.RankTwoAlt.Six.exists_autA6_of_code
    (contains_iff.mp (List.all_eq_true.mp repConj_aut gc hgc))
  refine ⟨g * p, A6Models.autA6.mul_mem hg (P0_le_autA6 hp), ?_⟩
  have hgr : g * r = A6Models.tAdd * g := by
    apply code_injective
    rw [code_mul, code_mul, code_tAdd]
    exact hge
  calc g * p * x * (g * p)⁻¹ = g * (p * x * p⁻¹) * g⁻¹ := by group
    _ = A6Models.tAdd := by rw [hpr, hgr, mul_inv_cancel_right]

theorem exists_conj_le_P0 {Q : Subgroup P10} (hQA : Q ≤ A6Models.autA6) (hQ : IsPGroup 2 Q) :
    ∃ g ∈ A6Models.autA6, Q.map (MulAut.conj g).toMonoidHom ≤ P0 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P0' : Subgroup ↥A6Models.autA6 := P0.subgroupOf A6Models.autA6 with hP0'
  have hP0card : Nat.card P0' = 32 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe P0_le_autA6).toEquiv, card_P0]
  have hidx : P0'.index = 45 := by
    have h := Subgroup.card_mul_index P0'
    rw [hP0card, card_autA6] at h
    omega
  let PS : Sylow 2 ↥A6Models.autA6 :=
    (show IsPGroup 2 P0' from IsPGroup.of_card (n := 5) (by rw [hP0card]; norm_num)).toSylow
      (by rw [hidx]; decide)
  have hPS : (PS : Subgroup ↥A6Models.autA6) = P0' := rfl
  set Q' : Subgroup ↥A6Models.autA6 := Q.subgroupOf A6Models.autA6 with hQ'
  have hQ'2 : IsPGroup 2 Q' := hQ.comap_of_injective _ A6Models.autA6.subtype_injective
  have : Finite (Sylow 2 ↥A6Models.autA6) := Sylow.finite_of_finiteIndex PS
  obtain ⟨R, hR⟩ := hQ'2.exists_le_sylow
  obtain ⟨a, ha⟩ := MulAction.exists_smul_eq ↥A6Models.autA6 R PS
  refine ⟨a, a.2, ?_⟩
  rintro _ ⟨q, hq, rfl⟩
  have hqR : (⟨q, hQA hq⟩ : ↥A6Models.autA6) ∈ (R : Subgroup ↥A6Models.autA6) :=
    hR (Subgroup.mem_subgroupOf.mpr hq)
  have h1 : (a * ⟨q, hQA hq⟩ * a⁻¹ : ↥A6Models.autA6) ∈
      ((a • R : Sylow 2 ↥A6Models.autA6) : Subgroup ↥A6Models.autA6) := ⟨_, hqR, rfl⟩
  rw [ha, hPS] at h1
  exact Subgroup.mem_subgroupOf.mp h1

theorem conj_mem_of_mem_normalizer {R : Subgroup P10} {r : P10} (hr3 : r ^ 3 = 1)
    (hrR : r ∈ Subgroup.normalizer (R : Set P10)) {v : P10} (hv : v ∈ R) :
    r * v * (r * r) ∈ R ∧ (r * r) * v * ((r * r) * (r * r)) ∈ R := by
  have hinv := inv_eq_sq hr3
  have h1 : r * v * r⁻¹ ∈ R := (Subgroup.mem_normalizer_iff.mp hrR v).mp hv
  have h2 : r⁻¹ * v * r⁻¹⁻¹ ∈ R := (Subgroup.mem_normalizer_iff.mp (inv_mem hrR) v).mp hv
  rw [← hinv]
  refine ⟨h1, ?_⟩
  have e : r⁻¹ * r⁻¹ = r := by
    rw [hinv]
    calc r * r * (r * r) = r ^ 3 * r := by rw [pow_three]; group
      _ = r := by rw [hr3, one_mul]
  rw [e]
  simpa using h2

theorem lattice_a6 {x : P10} (hx : x ∈ A6Models.psl29) (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1)
    {Q₁ Q₂ : Subgroup P10} (hQA : Q₂ ≤ A6Models.autA6) (h2 : IsPGroup 2 Q₂) (hle : Q₁ ≤ Q₂)
    {t₀ : P10} (ht₀ : t₀ ∈ Q₁) (ht₀1 : t₀ ≠ 1) (hn1 : x ∈ Subgroup.normalizer (Q₁ : Set P10))
    (hn2 : x ∈ Subgroup.normalizer (Q₂ : Set P10))
    (hexcl : ∀ u ∈ Q₂, u * x = x * u → u ∈ A6Models.m10) :
    (∀ v ∈ Q₂, v ≠ 1 → v = t₀ ∨ v = x * t₀ * (x * x) ∨
      v = (x * x) * t₀ * ((x * x) * (x * x))) ∧
    Q₂ ≤ Q₁ ∧ ∀ k ∈ A6Models.psl29, k ^ 3 = 1 → k ≠ 1 → ∃ v ∈ Q₂, k * v ≠ v * k := by
  obtain ⟨g, hg, hgQ⟩ := exists_conj_le_P0 hQA h2
  have hx' : g * x * g⁻¹ ∈ A6Models.psl29 := psl29_normal g hg x hx
  have hx'3 : (g * x * g⁻¹) ^ 3 = 1 := by rw [conj_pow, hx3, mul_one, mul_inv_cancel]
  have hx'1 : g * x * g⁻¹ ≠ 1 := by
    intro h
    apply hx1
    have := congrArg (fun y => g⁻¹ * y * g) h
    simpa [mul_assoc] using this
  obtain ⟨p, hp, r, hr, hpr⟩ := exists_conj_rep hx' hx'3 hx'1
  set h := p * g with hhdef
  have hh : h ∈ A6Models.autA6 := A6Models.autA6.mul_mem (P0_le_autA6 hp) hg
  have hhx : h * x * h⁻¹ = r := by rw [← hpr, hhdef]; group
  have hr3 : r ^ 3 = 1 := by rw [← hhx, conj_pow, hx3, mul_one, mul_inv_cancel]
  set c := (MulAut.conj h).toMonoidHom with hc
  have hcinj : Function.Injective c := (MulAut.conj h).injective
  have hcapp : ∀ y, c y = h * y * h⁻¹ := fun y => rfl
  have hRn : ∀ {Q : Subgroup P10}, x ∈ Subgroup.normalizer (Q : Set P10) →
      r ∈ Subgroup.normalizer ((Q.map c : Subgroup P10) : Set P10) := by
    intro Q hQ
    rw [← hhx]
    exact Subgroup.le_normalizer_map c ⟨x, hQ, rfl⟩
  have hR₂P0 : Q₂.map c ≤ P0 := by
    rintro _ ⟨q, hq, rfl⟩
    rw [hcapp]
    have hgq : g * q * g⁻¹ ∈ P0 := hgQ ⟨q, hq, rfl⟩
    have e : h * q * h⁻¹ = p * (g * q * g⁻¹) * p⁻¹ := by rw [hhdef]; group
    rw [e]
    exact P0.mul_mem (P0.mul_mem hp hgq) (P0.inv_mem hp)
  have hR₂ : r ∈ Subgroup.normalizer ((Q₂.map c : Subgroup P10) : Set P10) := hRn hn2
  have hR₁ : r ∈ Subgroup.normalizer ((Q₁.map c : Subgroup P10) : Set P10) := hRn hn1
  have hexcl' : ∀ v ∈ Q₂.map c, v * r = r * v → v ∈ A6Models.m10 := by
    rintro _ ⟨u, hu, rfl⟩ hvr
    rw [hcapp] at hvr ⊢
    have hux : u * x = x * u := by
      rw [← hhx] at hvr
      have := congrArg (fun y => h⁻¹ * y * h) hvr
      simpa [mul_assoc] using this
    exact m10_conj_mem hh (hexcl u hu hux)
  have hvl : ∀ v ∈ Q₂.map c, v ≠ 1 → code v ∈ vlSet (code r) := by
    intro v hv hv1
    obtain ⟨h1, h2'⟩ := conj_mem_of_mem_normalizer hr3 hR₂ hv
    have hw : v * (r * v * (r * r)) * ((r * r) * v * ((r * r) * (r * r))) ∈ Q₂.map c :=
      (Q₂.map c).mul_mem ((Q₂.map c).mul_mem hv h1) h2'
    rw [vlSet, List.mem_filter, wSet, List.mem_filter]
    refine ⟨⟨(mem_P0_iff v).mp (hR₂P0 hv), ?_⟩, ?_⟩
    · rw [Bool.and_eq_true, contains_iff, contains_iff, ← code_mul, code_conjC, code_conjC]
      exact ⟨(mem_P0_iff _).mp (hR₂P0 h1), (mem_P0_iff _).mp (hR₂P0 h2')⟩
    · have e1 : (code v == Core.cid) = false := by
        rw [beq_eq_false_iff_ne, Ne, code_eq_cid_iff]; exact hv1
      have e2 : (commC (code v) (code r) && !Out21.A6.inM10C (code v)) = false := by
        by_cases hcomm : v * r = r * v
        · rw [(Out21.A6.mem_m10_iff_code v).mp (hexcl' v hv hcomm)]
          simp
        · have : commC (code v) (code r) = false := by
            rw [← Bool.not_eq_true, commC_iff]; exact hcomm
          rw [this]
          simp
      have e3 : (commC (wC (code r) (code v)) (code r) &&
          !Out21.A6.inM10C (wC (code r) (code v))) = false := by
        rw [code_wC]
        by_cases hcomm : (v * (r * v * (r * r)) * ((r * r) * v * ((r * r) * (r * r)))) * r =
            r * (v * (r * v * (r * r)) * ((r * r) * v * ((r * r) * (r * r))))
        · rw [(Out21.A6.mem_m10_iff_code _).mp (hexcl' _ hw hcomm)]
          simp
        · have : commC (code (v * (r * v * (r * r)) * ((r * r) * v * ((r * r) * (r * r)))))
              (code r) = false := by
            rw [← Bool.not_eq_true, commC_iff]; exact hcomm
          rw [this]
          simp
      simp only [e1, e2, e3, Bool.not_false, Bool.and_self]
  set t := c t₀ with ht
  have htQ₁ : t ∈ Q₁.map c := ⟨t₀, ht₀, rfl⟩
  have ht1 : t ≠ 1 := fun h0 => ht₀1 (hcinj (h0.trans (map_one c).symm))
  have htvl := hvl t (Subgroup.map_mono hle htQ₁) ht1
  have horb : ∀ b ∈ vlSet (code r), b = code t ∨ b = code (r * t * (r * r)) ∨
      b = code ((r * r) * t * ((r * r) * (r * r))) := by
    intro b hb
    have h := List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp lat_check
      (code r) hr) (code t) htvl) b hb
    simp only [Bool.or_eq_true, beq_iff_eq] at h
    rw [code_conjC, ← code_mul, code_conjC] at h
    rcases h with (h | h) | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  have hmemQ₁ : ∀ b ∈ vlSet (code r), ∃ v ∈ Q₁.map c, code v = b := by
    intro b hb
    obtain ⟨h1, h2'⟩ := conj_mem_of_mem_normalizer hr3 hR₁ htQ₁
    rcases horb b hb with rfl | rfl | rfl
    · exact ⟨t, htQ₁, rfl⟩
    · exact ⟨_, h1, rfl⟩
    · exact ⟨_, h2', rfl⟩
  have hQ₂Q₁ : Q₂.map c ≤ Q₁.map c := by
    intro v hv
    by_cases hv1 : v = 1
    · rw [hv1]; exact (Q₁.map c).one_mem
    · obtain ⟨v', hv', he⟩ := hmemQ₁ _ (hvl v hv hv1)
      rw [← code_injective he]
      exact hv'
  have hcx : c x = r := hhx
  have horb' : ∀ v ∈ Q₂, v ≠ 1 → v = t₀ ∨ v = x * t₀ * (x * x) ∨
      v = (x * x) * t₀ * ((x * x) * (x * x)) := by
    intro v hv hv1
    have hv' : c v ∈ Q₂.map c := ⟨v, hv, rfl⟩
    have hcv1 : c v ≠ 1 := fun h0 => hv1 (hcinj (h0.trans (map_one c).symm))
    rcases horb _ (hvl _ hv' hcv1) with h | h | h
    · exact Or.inl (hcinj (code_injective h))
    · right; left
      apply hcinj
      rw [code_injective h, map_mul, map_mul, map_mul, hcx]
    · right; right
      apply hcinj
      rw [code_injective h]
      simp only [map_mul, hcx]
      rfl
  refine ⟨horb', (Subgroup.map_le_map_iff_of_injective hcinj).mp hQ₂Q₁, fun k hk hk3 hk1 => ?_⟩
  have hk' : h * k * h⁻¹ ∈ A6Models.psl29 := psl29_normal h hh k hk
  have hk'3 : (h * k * h⁻¹) ^ 3 = 1 := by rw [conj_pow, hk3, mul_one, mul_inv_cancel]
  have hk'1 : h * k * h⁻¹ ≠ 1 := by
    intro h0
    apply hk1
    have := congrArg (fun y => h⁻¹ * y * h) h0
    simpa [mul_assoc] using this
  have hc := List.all_eq_true.mp cent_check (code r) hr
  have hne' : (vlSet (code r)).isEmpty = false := by
    rw [List.isEmpty_eq_false_iff_exists_mem]
    exact ⟨_, htvl⟩
  rw [hne', Bool.false_or] at hc
  have hc' := List.all_eq_true.mp hc (code (h * k * h⁻¹)) ((mem_psl29_iff _).mp hk')
  have h3 : (cubeC (code (h * k * h⁻¹)) == Core.cid) = true := by
    rw [beq_iff_eq, cubeC_eq_cid_iff]; exact hk'3
  have h1 : (code (h * k * h⁻¹) == Core.cid) = false := by
    rw [beq_eq_false_iff_ne, Ne, code_eq_cid_iff]; exact hk'1
  rw [h3, h1] at hc'
  simp only [Bool.not_true, Bool.false_or, List.any_eq_true, Bool.not_eq_true'] at hc'
  obtain ⟨b, hb, hbc⟩ := hc'
  obtain ⟨v, hv, rfl⟩ := hmemQ₁ b hb
  obtain ⟨v₀, hv₀, rfl⟩ := hv
  refine ⟨v₀, hle hv₀, fun hkv => ?_⟩
  have : (h * k * h⁻¹) * c v₀ = c v₀ * (h * k * h⁻¹) := by
    rw [hcapp]
    calc h * k * h⁻¹ * (h * v₀ * h⁻¹) = h * (k * v₀) * h⁻¹ := by group
      _ = h * (v₀ * k) * h⁻¹ := by rw [hkv]
      _ = h * v₀ * h⁻¹ * (h * k * h⁻¹) := by group
  rw [← commC_iff] at this
  rw [this] at hbc
  simp at hbc

theorem le_of_lattice_a6 {x : P10} (hx : x ∈ A6Models.psl29) (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1)
    {Q₁ Q₂ : Subgroup P10} (hQA : Q₂ ≤ A6Models.autA6) (h2 : IsPGroup 2 Q₂) (hle : Q₁ ≤ Q₂)
    (hne : Q₁ ≠ ⊥) (hn1 : x ∈ Subgroup.normalizer (Q₁ : Set P10))
    (hn2 : x ∈ Subgroup.normalizer (Q₂ : Set P10))
    (hexcl : ∀ u ∈ Q₂, u * x = x * u → u ∈ A6Models.m10) :
    Q₂ ≤ Q₁ ∧ ∀ k ∈ A6Models.psl29, k ^ 3 = 1 → k ≠ 1 → ∃ v ∈ Q₂, k * v ≠ v * k := by
  obtain ⟨⟨t₀, ht₀⟩, ht₁⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hne
  have ht₀1 : t₀ ≠ 1 := fun h0 => ht₁ (Subtype.ext h0)
  obtain ⟨-, h1, h2'⟩ := lattice_a6 hx hx3 hx1 hQA h2 hle ht₀ ht₀1 hn1 hn2 hexcl
  exact ⟨h1, h2'⟩

theorem mem_zpowers_of_pow_three {y z : P10} (hy3 : y ^ 3 = 1) (hz : z ∈ Subgroup.zpowers y) :
    z = 1 ∨ z = y ∨ z = y * y := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
  have hk : y ^ k = y ^ (k % 3) := by
    conv_lhs => rw [← Int.emod_add_mul_ediv k 3]
    rw [zpow_add, zpow_mul, show (y ^ (3 : ℤ)) = 1 by exact_mod_cast hy3, one_zpow, mul_one]
  have h0 : 0 ≤ k % 3 := Int.emod_nonneg k (by norm_num)
  have h3 : k % 3 < 3 := Int.emod_lt_of_pos k (by norm_num)
  rw [hk]
  interval_cases (k % 3)
  · left; simp
  · right; left; simp
  · right; right; rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) by norm_num, zpow_natCast, pow_two]

theorem not_mem_zpowers_conj {g x w : P10} (hw : w ∉ Subgroup.zpowers x) :
    g * w * g⁻¹ ∉ Subgroup.zpowers (g * x * g⁻¹) := by
  intro h
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h
  apply hw
  refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
  have h1 : (g * x * g⁻¹) ^ k = g * x ^ k * g⁻¹ := by
    rw [← MulAut.conj_apply, ← map_zpow, MulAut.conj_apply]
  rw [h1] at hk
  have := congrArg (fun y => g⁻¹ * y * g) hk
  simpa [mul_assoc] using this

theorem exists_inv_of_not_mem_m10 {x : P10} (hx : x ∈ A6Models.psl29) (hx3 : x ^ 3 = 1)
    (hx1 : x ≠ 1) {u : P10} (hu : u ∈ A6Models.autA6) (hux : u * x = x * u)
    (hum : u ∉ A6Models.m10) :
    ∃ w ∈ A6Models.psl29, w ^ 3 = 1 ∧ w * x = x * w ∧ w ∉ Subgroup.zpowers x ∧
      u * w * u⁻¹ = w⁻¹ := by
  obtain ⟨g, hg, hgx⟩ := exists_conj_tAdd hx hx3 hx1
  set u' := g * u * g⁻¹ with hu'def
  have hu' : u' ∈ A6Models.autA6 :=
    A6Models.autA6.mul_mem (A6Models.autA6.mul_mem hg hu) (A6Models.autA6.inv_mem hg)
  have hu'x : u' * A6Models.tAdd = A6Models.tAdd * u' := by
    rw [← hgx, hu'def]
    calc g * u * g⁻¹ * (g * x * g⁻¹) = g * (u * x) * g⁻¹ := by group
      _ = g * (x * u) * g⁻¹ := by rw [hux]
      _ = g * x * g⁻¹ * (g * u * g⁻¹) := by group
  have hu'm : u' ∉ A6Models.m10 := by
    intro h
    apply hum
    have := m10_conj_mem (A6Models.autA6.inv_mem hg) h
    simpa [hu'def, mul_assoc] using this
  have hf := List.all_eq_true.mp f6_check (code u') (code_mem_autL hu')
  have hc : (commC (code u') tAddC && !Out21.A6.inM10C (code u')) = true := by
    rw [← code_tAdd, Bool.and_eq_true, commC_iff, Bool.not_eq_true',
      ← Bool.not_eq_true, ← Out21.A6.mem_m10_iff_code]
    exact ⟨hu'x, hu'm⟩
  rw [hc] at hf
  simp only [Bool.not_true, Bool.false_or, List.any_eq_true, Bool.and_eq_true,
    Bool.not_eq_true', beq_eq_false_iff_ne, beq_iff_eq] at hf
  obtain ⟨wc, hwc, ⟨⟨⟨hw1, hw2⟩, hw3⟩, hwu⟩⟩ := hf
  have ht9 := List.all_eq_true.mp t9_check wc hwc
  simp only [Bool.and_eq_true, beq_iff_eq] at ht9
  obtain ⟨⟨⟨hwpsl, hwcube⟩, hwcomm⟩, -⟩ := ht9
  obtain ⟨w', hw'psl, rfl⟩ := exists_psl29_of_code (contains_iff.mp hwpsl)
  have hw'3 : w' ^ 3 = 1 := (cubeC_eq_cid_iff w').mp hwcube
  have hw'x : w' * A6Models.tAdd = A6Models.tAdd * w' := by
    rw [← commC_iff, code_tAdd]; exact hwcomm
  have hw'n : w' ∉ Subgroup.zpowers A6Models.tAdd := by
    intro h
    rcases mem_zpowers_of_pow_three (by
        rw [← cubeC_eq_cid_iff, code_tAdd]; decide +kernel) h with h' | h' | h'
    · exact hw1 (by rw [h', code_one])
    · exact hw2 (by rw [h', code_tAdd])
    · exact hw3 (by rw [h', code_mul, code_tAdd])
  have hu'w' : u' * w' = w' * w' * u' := by
    apply code_injective
    rw [code_mul u' w', code_mul (w' * w') u', code_mul w' w']
    exact hwu
  refine ⟨g⁻¹ * w' * g, ?_, ?_, ?_, ?_, ?_⟩
  · have := psl29_normal _ (A6Models.autA6.inv_mem hg) _ hw'psl
    simpa using this
  · rw [show (g⁻¹ * w' * g) ^ 3 = g⁻¹ * w' ^ 3 * g by
      rw [show g⁻¹ * w' * g = g⁻¹ * w' * g⁻¹⁻¹ by rw [inv_inv], conj_pow, inv_inv], hw'3]
    group
  · have hx' : x = g⁻¹ * A6Models.tAdd * g := by rw [← hgx]; group
    rw [hx']
    calc g⁻¹ * w' * g * (g⁻¹ * A6Models.tAdd * g) = g⁻¹ * (w' * A6Models.tAdd) * g := by group
      _ = g⁻¹ * (A6Models.tAdd * w') * g := by rw [hw'x]
      _ = g⁻¹ * A6Models.tAdd * g * (g⁻¹ * w' * g) := by group
  · intro h
    apply hw'n
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h
    refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
    rw [← hgx, show (g * x * g⁻¹) ^ k = g * x ^ k * g⁻¹ by
      rw [← MulAut.conj_apply, ← map_zpow, MulAut.conj_apply], hk]
    group
  · have hw'inv : w'⁻¹ = w' * w' := inv_eq_sq hw'3
    have hu'eq : u = g⁻¹ * u' * g := by rw [hu'def]; group
    rw [hu'eq]
    have e : u' * w' * u'⁻¹ = w'⁻¹ := by
      rw [hu'w', hw'inv]; group
    calc g⁻¹ * u' * g * (g⁻¹ * w' * g) * (g⁻¹ * u' * g)⁻¹ = g⁻¹ * (u' * w' * u'⁻¹) * g := by
          group
      _ = (g⁻¹ * w' * g)⁻¹ := by rw [e]; group

@[expose] def T9 : Subgroup P10 := ofCodes t9c t9c_one t9c_mul t9c_three

theorem card_T9 : Nat.card ↥T9 = 9 :=
  card_ofCodes (by decide +kernel) (fun a ha => by
    have h := List.all_eq_true.mp t9_check a ha
    simp only [Bool.and_eq_true] at h
    exact List.mem_permutations'.mpr (of_decide_eq_true h.2))

theorem card_closure_pair {x w : P10} (hx : x ∈ A6Models.psl29) (hx3 : x ^ 3 = 1)
    (hx1 : x ≠ 1) (hw : w ∈ A6Models.psl29) (hw3 : w ^ 3 = 1) (hwx : w * x = x * w)
    (hwn : w ∉ Subgroup.zpowers x) : Nat.card (Subgroup.closure ({x, w} : Set P10)) = 9 := by
  obtain ⟨g, hg, hgx⟩ := exists_conj_tAdd hx hx3 hx1
  set w' := g * w * g⁻¹ with hw'def
  have hw' : w' ∈ A6Models.autA6 :=
    A6Models.autA6.mul_mem (A6Models.autA6.mul_mem hg (psl29_le_autA6 hw))
      (A6Models.autA6.inv_mem hg)
  have hw'3 : w' ^ 3 = 1 := by rw [hw'def, conj_pow, hw3, mul_one, mul_inv_cancel]
  have hw'x : w' * A6Models.tAdd = A6Models.tAdd * w' := by
    rw [← hgx, hw'def]
    calc g * w * g⁻¹ * (g * x * g⁻¹) = g * (w * x) * g⁻¹ := by group
      _ = g * (x * w) * g⁻¹ := by rw [hwx]
      _ = g * x * g⁻¹ * (g * w * g⁻¹) := by group
  have hw'n : w' ∉ Subgroup.zpowers A6Models.tAdd := by
    rw [← hgx]; exact not_mem_zpowers_conj hwn
  have hw'T : code w' ∈ t9c := by
    have h := List.all_eq_true.mp ordT9_check (code w') (code_mem_autL hw')
    have hc : (commC (code w') tAddC && cubeC (code w') == Core.cid) = true := by
      rw [Bool.and_eq_true, ← code_tAdd, commC_iff, beq_iff_eq, cubeC_eq_cid_iff]
      exact ⟨hw'x, hw'3⟩
    rw [hc] at h
    simpa using h
  have hgen := List.all_eq_true.mp t9_gen_check (code w') hw'T
  have hw1 : (code w' == Core.cid) = false := by
    rw [beq_eq_false_iff_ne, Ne, code_eq_cid_iff]
    exact fun h => hw'n (h ▸ Subgroup.one_mem _)
  have hw2 : (code w' == tAddC) = false := by
    rw [beq_eq_false_iff_ne, Ne, ← code_tAdd]
    exact fun h => hw'n (code_injective h ▸ Subgroup.mem_zpowers _)
  have hw3' : (code w' == Core.cmul tAddC tAddC) = false := by
    rw [beq_eq_false_iff_ne, Ne, ← code_tAdd, ← code_mul]
    intro h
    apply hw'n
    rw [code_injective h, ← pow_two]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) 2
  rw [hw1, hw2, hw3'] at hgen
  simp only [Bool.false_or, List.any_eq_true, beq_iff_eq, List.mem_cons, List.not_mem_nil,
    or_false] at hgen
  have hcl : Subgroup.closure ({A6Models.tAdd, w'} : Set P10) = T9 := by
    apply le_antisymm
    · rw [Subgroup.closure_le]
      rintro y (rfl | rfl)
      · show pcode A6Models.tAdd ∈ t9c
        rw [← code_eq_pcode, code_tAdd]
        decide +kernel
      · exact hw'T
    · intro t ht
      have ht' : code t ∈ t9c := ht
      have hs := List.all_eq_true.mp t9_span_check (code t) ht'
      simp only [List.any_eq_true, beq_iff_eq, List.mem_cons, List.not_mem_nil,
        or_false] at hs
      obtain ⟨i, -, j, -, hij⟩ := hs
      obtain ⟨i', -, j', -, hij'⟩ := hgen
      obtain ⟨tI, -, htI⟩ : ∃ y ∈ T9, code y = tIC := by
        have h := exists_mem_ofCodes (l := t9c) (h1 := t9c_one) (hmul := t9c_mul)
          (h3 := t9c_three) (fun a ha => by
            have h := List.all_eq_true.mp t9_check a ha
            simp only [Bool.and_eq_true] at h
            exact List.mem_permutations'.mpr (of_decide_eq_true h.2))
          (show tIC ∈ t9c by decide +kernel)
        exact h
      have htI' : tI = A6Models.tAdd ^ i' * w' ^ j' := by
        apply code_injective
        rw [code_mul, code_pow, code_pow, code_tAdd, htI]
        exact hij'.symm
      have ht'' : t = A6Models.tAdd ^ i * tI ^ j := by
        apply code_injective
        rw [code_mul, code_pow, code_pow, code_tAdd, htI]
        exact hij.symm
      have hmem1 : A6Models.tAdd ∈ Subgroup.closure ({A6Models.tAdd, w'} : Set P10) :=
        Subgroup.subset_closure (Set.mem_insert _ _)
      have hmem2 : w' ∈ Subgroup.closure ({A6Models.tAdd, w'} : Set P10) :=
        Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
      rw [ht'', htI']
      exact Subgroup.mul_mem _ (Subgroup.pow_mem _ hmem1 _) (Subgroup.pow_mem _
        (Subgroup.mul_mem _ (Subgroup.pow_mem _ hmem1 _) (Subgroup.pow_mem _ hmem2 _)) _)
  have hmap : (Subgroup.closure ({x, w} : Set P10)).map (MulAut.conj g).toMonoidHom =
      Subgroup.closure ({A6Models.tAdd, w'} : Set P10) := by
    rw [MonoidHom.map_closure, Set.image_pair, ← hgx]
    rfl
  rw [← Subgroup.card_map_of_injective (f := (MulAut.conj g).toMonoidHom)
    (MulAut.conj g).injective, hmap, hcl, card_T9]

theorem exists_noncomm_three : ∃ x ∈ A6Models.psl29, ∃ y ∈ A6Models.psl29,
    x ^ 3 = 1 ∧ y ^ 3 = 1 ∧ x * y ≠ y * x := by
  obtain ⟨h1, h2, h3⟩ := ncC_check
  obtain ⟨y, hy, hyc⟩ := exists_psl29_of_code (contains_iff.mp h1)
  refine ⟨A6Models.tAdd, Out21.A6.tAdd_mem_psl29, y, hy, ?_, ?_, ?_⟩
  · rw [← cubeC_eq_cid_iff, code_tAdd]; decide +kernel
  · rw [← cubeC_eq_cid_iff, hyc]; exact h2
  · intro h
    have := (commC_iff _ _).mpr h
    rw [code_tAdd, hyc, h3] at this
    exact Bool.false_ne_true this

end CFSG.RankThree.PartTwo.Sec15.Push153B.A6
