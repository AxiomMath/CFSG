module

public import CFSG.Sporadic.Schreier.RuWitReps
public import Certificates.Certificate7350

public section

namespace CFSG.Sporadic.RuSchreier.J49

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native

@[expose] noncomputable def gel (k : ℕ) : Equiv.Perm (Fin 4060) :=
  evalSigned [ruA0, ruA1] ((wordList ()).getD k [])

@[expose] noncomputable def Ex.evalG : Ex → Equiv.Perm (Fin 4060)
  | .el k => gel k
  | .one => 1
  | .mul a b => a.evalG * b.evalG
  | .pow a n => a.evalG ^ n

@[expose] def At.holds : At → Prop
  | .eq a b => a.evalG = b.evalG
  | .ne a b => a.evalG ≠ b.evalG
  | .eqAny a cs => ∃ c ∈ cs, a.evalG = c.evalG
  | .imp h c => h.holds → c.holds

theorem tabOf_tabs (k : ℕ) :
    tabOf (tabs ()) k = ruSeedWordA ((wordList ()).getD k []) := by
  unfold tabOf tabs
  by_cases hk : k < (wordList ()).length
  · have hs : k < (((wordList ()).map ruSeedWordA).toArray).size := by simpa using hk
    rw [if_pos hs]
    simp [getElem!_pos, hk, List.getD_eq_getElem?_getD]
  · have hs : ¬ k < (((wordList ()).map ruSeedWordA).toArray).size := by simpa using hk
    rw [if_neg hs]
    have : (wordList ()).getD k [] = [] := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : (wordList ()).length ≤ k)]
    rw [this]
    rfl

theorem rep_tabOf (hw : ∀ w ∈ wordList (), lettersOK 2 w = true)
    (k : ℕ) : Rep 4060 (tabOf (tabs ()) k) (gel k) := by
  rw [tabOf_tabs]
  have hl : lettersOK 2 ((wordList ()).getD k []) = true := by
    by_cases hk : k < (wordList ()).length
    · have : (wordList ()).getD k [] ∈ wordList () := by
        simp [List.getD_eq_getElem?_getD, hk]
      exact hw _ this
    · have : (wordList ()).getD k [] = [] := by
        simp [List.getD_eq_getElem?_getD,
          List.getElem?_eq_none (by omega : (wordList ()).length ≤ k)]
      rw [this]
      rfl
  exact rep_ruSeedWordA hl

theorem rep_evalA (hw : ∀ w ∈ wordList (), lettersOK 2 w = true) :
    ∀ e : Ex, Rep 4060 (e.evalA (tabs ())) e.evalG
  | .el k => rep_tabOf hw k
  | .one => rep_idA
  | .mul a b => rep_compA (rep_evalA hw a) (rep_evalA hw b)
  | .pow a n => rep_powA (rep_evalA hw a) n

theorem checkA_iff (hw : ∀ w ∈ wordList (), lettersOK 2 w = true) :
    ∀ a : At, a.checkA (tabs ()) = true ↔ a.holds
  | .eq a b => eqA_iff (rep_evalA hw a) (rep_evalA hw b)
  | .ne a b => by
    unfold At.checkA At.holds
    rw [Bool.not_eq_true', ← Bool.not_eq_true, eqA_iff (rep_evalA hw a) (rep_evalA hw b)]
  | .eqAny a cs => by
    unfold At.checkA At.holds
    rw [List.any_eq_true]
    refine exists_congr fun c => ?_
    refine and_congr_right fun hc => ?_
    exact eqA_iff (rep_evalA hw a) (rep_evalA hw c)
  | .imp h c => by
    unfold At.checkA At.holds
    have h1 := checkA_iff hw h
    have h2 := checkA_iff hw c
    rw [Bool.or_eq_true, Bool.not_eq_true']
    constructor
    · rintro (h0 | h0) hh
      · exact absurd (h1.2 hh) (by simp [h0])
      · exact h2.1 h0
    · intro H
      by_cases hh : h.checkA (tabs ()) = true
      · exact Or.inr (h2.2 (H (h1.1 hh)))
      · exact Or.inl (by simpa using hh)

theorem check_sound (h : check () = true) :
    (wordList ()).length = 19 ∧ (∀ w ∈ wordList (), lettersOK 2 w = true) ∧
      ∀ a ∈ atoms (), a.holds := by
  unfold check at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  have hw : ∀ w ∈ wordList (), lettersOK 2 w = true := h2
  exact ⟨h1, hw, fun a ha => (checkA_iff hw a).1 (h3 a ha)⟩


@[expose] def labG {K : Type*} [Group K] (z u : K) (k : ℕ) : K :=
  if k % 3 = 0 then z else if k % 3 = 1 then u else u * z

structure Cfg {K : Type*} [Group K] (x : ℕ → K) (z y u i1 i2 r s : K) : Prop where
  z_sq : z * z = 1
  z_ne : z ≠ 1
  u_sq : u * u = 1
  u_ne : u ≠ 1
  u_ne_z : u ≠ z
  comm : u * z = z * u
  y_cube : y ^ 3 = 1
  y_ne : y ≠ 1
  y_comm : y * z = z * y
  x_pow : ∀ k < 12, x k ^ 5 = 1
  x_ne : ∀ k < 12, x k ≠ 1
  x_cent : ∀ k < 12, labG z u k * x k = x k * labG z u k
  x_inv1 : ∀ k < 12, labG z u (k + 1) * x k * labG z u (k + 1) = x k ^ 4
  x_inv2 : ∀ k < 12, labG z u (k + 2) * x k * labG z u (k + 2) = x k ^ 4
  x_adj : ∀ k < 12, x k * x ((k + 1) % 12) = x ((k + 1) % 12) * x k
  x_nadj : ∀ k < 12, x k * x ((k + 2) % 12) ≠ x ((k + 2) % 12) * x k
  x_dist : ∀ i < 12, ∀ j < 12, i < j → ∀ m < 4, x j ≠ x i ^ (m + 1)
  i1_pow : i1 ^ 4 = 1
  i2_pow : i2 ^ 4 = 1
  i_comm : i1 * i2 = i2 * i1
  z_mem : ∃ p < 4, ∃ q < 4, z = i1 ^ p * i2 ^ q
  u_mem : ∃ p < 4, ∃ q < 4, u = i1 ^ p * i2 ^ q
  i_cz : ∀ p < 4, ∀ q < 4, (i1 ^ p * i2 ^ q) * z = z * (i1 ^ p * i2 ^ q)
  i_nx : ∀ p < 4, ∀ q < 4, ∀ k < 12, ∃ m < 4,
    (i1 ^ p * i2 ^ q) * x k = x k ^ (m + 1) * (i1 ^ p * i2 ^ q)
  i_inv : ∀ p < 4, ∀ q < 4, (i1 ^ p * i2 ^ q) * (i1 ^ p * i2 ^ q) = 1 →
    i1 ^ p * i2 ^ q = 1 ∨ i1 ^ p * i2 ^ q = z ∨ i1 ^ p * i2 ^ q = u ∨ i1 ^ p * i2 ^ q = u * z
  i_dist : ∀ p < 4, ∀ q < 4, ∀ p' < 4, ∀ q' < 4, p * 4 + q < p' * 4 + q' →
    i1 ^ p * i2 ^ q ≠ i1 ^ p' * i2 ^ q'
  r_b : ∃ m < 4, x 0 * r = r * x 0 ^ (m + 1)
  r_u : u * r = r * (u * z)
  r_z : z * r = r * z
  r_i1 : ∃ p < 4, ∃ q < 4, i1 * r = r * (i1 ^ p * i2 ^ q)
  r_i2 : ∃ p < 4, ∃ q < 4, i2 * r = r * (i1 ^ p * i2 ^ q)
  s_i1 : ∃ p < 4, ∃ q < 4, i1 * s = s * (i1 ^ p * i2 ^ q)
  s_i2 : ∃ p < 4, ∃ q < 4, i2 * s = s * (i1 ^ p * i2 ^ q)
  r_x : ∀ k < 12, ∃ m < 4, x k * r = r * x ((12 - k) % 12) ^ (m + 1)
  s_x : ∀ k < 12, ∃ m < 4, x k * s = s * x ((13 - k) % 12) ^ (m + 1)


theorem evalG_labE (k : ℕ) : (labE k).evalG = labG (gel 12) (gel 16) k := by
  unfold labE labG
  split_ifs <;> simp [Ex.evalG, zE, uE, uzE]

theorem evalG_ieE (p q : ℕ) : (ieE p q).evalG = gel 14 ^ p * gel 15 ^ q := by
  simp [ieE, Ex.evalG, i1E, i2E]

theorem mem_ieAll {p q : ℕ} (hp : p < 4) (hq : q < 4) : ieE p q ∈ ieAll := by
  simp only [ieAll, List.mem_flatMap, List.mem_range, List.mem_map]
  exact ⟨p, hp, q, hq, rfl⟩

theorem mem_ieAll_iff {c : Ex} : c ∈ ieAll ↔ ∃ p < 4, ∃ q < 4, c = ieE p q := by
  simp only [ieAll, List.mem_flatMap, List.mem_range, List.mem_map]
  constructor
  · rintro ⟨p, hp, q, hq, rfl⟩
    exact ⟨p, hp, q, hq, rfl⟩
  · rintro ⟨p, hp, q, hq, rfl⟩
    exact ⟨p, hp, q, hq, rfl⟩

theorem mem_pows_iff {a c : Ex} : c ∈ pows a ↔ ∃ m < 4, c = .pow a (m + 1) := by
  simp only [pows, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨m, hm, rfl⟩
    exact ⟨m, hm, rfl⟩
  · rintro ⟨m, hm, rfl⟩
    exact ⟨m, hm, rfl⟩

theorem holds_cn {g x : Ex} {cs : List Ex} (h : (cn g x cs).holds) :
    ∃ c ∈ cs, x.evalG * g.evalG = g.evalG * c.evalG := by
  unfold cn At.holds at h
  obtain ⟨c', hc', hc⟩ := h
  simp only [List.mem_map] at hc'
  obtain ⟨c, hcs, rfl⟩ := hc'
  exact ⟨c, hcs, by simpa [Ex.evalG] using hc⟩

theorem mem_atoms_basic {a : At} (ha : a ∈ atomsBasic) : a ∈ atoms () := by
  simp only [atoms, List.mem_append]
  tauto

theorem mem_atoms_X {k : ℕ} (hk : k < 12) {a : At} (ha : a ∈ atomsXk k) : a ∈ atoms () := by
  have : a ∈ atomsX () := by
    simp only [atomsX, List.mem_flatMap, List.mem_range]
    exact ⟨k, hk, ha⟩
  simp only [atoms, List.mem_append]
  tauto

theorem mem_atoms_dist {a : At} (ha : a ∈ atomsDist ()) : a ∈ atoms () := by
  simp only [atoms, List.mem_append]
  tauto

theorem mem_atoms_I0 {a : At} (ha : a ∈ atomsI0) : a ∈ atoms () := by
  simp only [atoms, List.mem_append]
  tauto

theorem mem_atoms_Ipq {p q : ℕ} (hp : p < 4) (hq : q < 4) {a : At} (ha : a ∈ atomsIpq p q) :
    a ∈ atoms () := by
  have : a ∈ atomsI () := by
    simp only [atomsI, List.mem_flatMap, List.mem_range]
    exact ⟨p, hp, q, hq, ha⟩
  simp only [atoms, List.mem_append]
  tauto

theorem mem_atoms_Idist {a : At} (ha : a ∈ atomsIdist ()) : a ∈ atoms () := by
  simp only [atoms, List.mem_append]
  tauto

theorem mem_atoms_RS0 {a : At} (ha : a ∈ atomsRS0) : a ∈ atoms () := by
  simp only [atoms, List.mem_append]
  tauto

theorem mem_atoms_RSk {k : ℕ} (hk : k < 12) {a : At} (ha : a ∈ atomsRSk k) : a ∈ atoms () := by
  simp only [atoms, List.mem_append, List.mem_flatMap, List.mem_range]
  exact Or.inr ⟨k, hk, ha⟩


theorem cfg_gel :
    Cfg (fun k => gel k) (gel 12) (gel 13) (gel 16) (gel 14) (gel 15) (gel 17) (gel 18) := by
  have hall := (check_sound Certificates.certificate7350).2.2
  have hB : ∀ a ∈ atomsBasic, a.holds := fun a ha => hall a (mem_atoms_basic ha)
  have hX : ∀ k < 12, ∀ a ∈ atomsXk k, a.holds := fun k hk a ha => hall a (mem_atoms_X hk ha)
  have hD : ∀ a ∈ atomsDist (), a.holds := fun a ha => hall a (mem_atoms_dist ha)
  have hI0 : ∀ a ∈ atomsI0, a.holds := fun a ha => hall a (mem_atoms_I0 ha)
  have hI : ∀ p < 4, ∀ q < 4, ∀ a ∈ atomsIpq p q, a.holds :=
    fun p hp q hq a ha => hall a (mem_atoms_Ipq hp hq ha)
  have hId : ∀ a ∈ atomsIdist (), a.holds := fun a ha => hall a (mem_atoms_Idist ha)
  have hR0 : ∀ a ∈ atomsRS0, a.holds := fun a ha => hall a (mem_atoms_RS0 ha)
  have hRk : ∀ k < 12, ∀ a ∈ atomsRSk k, a.holds :=
    fun k hk a ha => hall a (mem_atoms_RSk hk ha)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [At.holds, Ex.evalG, zE] using hB (.eq (.mul zE zE) .one) (by simp [atomsBasic])
  · simpa [At.holds, Ex.evalG, zE] using hB (.ne zE .one) (by simp [atomsBasic])
  · simpa [At.holds, Ex.evalG, uE] using hB (.eq (.mul uE uE) .one) (by simp [atomsBasic])
  · simpa [At.holds, Ex.evalG, uE] using hB (.ne uE .one) (by simp [atomsBasic])
  · simpa [At.holds, Ex.evalG, uE, zE] using hB (.ne uE zE) (by simp [atomsBasic])
  · simpa [At.holds, Ex.evalG, uE, zE] using
      hB (.eq (.mul uE zE) (.mul zE uE)) (by simp [atomsBasic])
  · simpa [At.holds, Ex.evalG, yE] using hB (.eq (.pow yE 3) .one) (by simp [atomsBasic])
  · simpa [At.holds, Ex.evalG, yE] using hB (.ne yE .one) (by simp [atomsBasic])
  · simpa [At.holds, Ex.evalG, yE, zE] using
      hB (.eq (.mul yE zE) (.mul zE yE)) (by simp [atomsBasic])
  · intro k hk
    simpa [At.holds, Ex.evalG, X] using hX k hk (.eq (.pow (X k) 5) .one) (by simp [atomsXk])
  · intro k hk
    simpa [At.holds, Ex.evalG, X] using hX k hk (.ne (X k) .one) (by simp [atomsXk])
  · intro k hk
    simpa [At.holds, Ex.evalG, X, evalG_labE] using
      hX k hk (.eq (.mul (labE k) (X k)) (.mul (X k) (labE k))) (by simp [atomsXk])
  · intro k hk
    simpa [At.holds, Ex.evalG, X, evalG_labE] using
      hX k hk (.eq (.mul (.mul (labE (k + 1)) (X k)) (labE (k + 1))) (.pow (X k) 4))
        (by simp [atomsXk])
  · intro k hk
    simpa [At.holds, Ex.evalG, X, evalG_labE] using
      hX k hk (.eq (.mul (.mul (labE (k + 2)) (X k)) (labE (k + 2))) (.pow (X k) 4))
        (by simp [atomsXk])
  · intro k hk
    simpa [At.holds, Ex.evalG, X] using
      hX k hk (.eq (.mul (X k) (X ((k + 1) % 12))) (.mul (X ((k + 1) % 12)) (X k)))
        (by simp [atomsXk])
  · intro k hk
    simpa [At.holds, Ex.evalG, X] using
      hX k hk (.ne (.mul (X k) (X ((k + 2) % 12))) (.mul (X ((k + 2) % 12)) (X k)))
        (by simp [atomsXk])
  · intro i hi j hj hij m hm
    have := hD (.ne (X j) (.pow (X i) (m + 1))) (by
      simp only [atomsDist, List.mem_flatMap, List.mem_range, List.mem_map]
      exact ⟨i, hi, j, hj, by rw [if_pos hij]; exact List.mem_map.2 ⟨m, List.mem_range.2 hm, rfl⟩⟩)
    simpa [At.holds, Ex.evalG, X] using this
  · simpa [At.holds, Ex.evalG, i1E] using hI0 (.eq (.pow i1E 4) .one) (by simp [atomsI0])
  · simpa [At.holds, Ex.evalG, i2E] using hI0 (.eq (.pow i2E 4) .one) (by simp [atomsI0])
  · simpa [At.holds, Ex.evalG, i1E, i2E] using
      hI0 (.eq (.mul i1E i2E) (.mul i2E i1E)) (by simp [atomsI0])
  · obtain ⟨c, hc, he⟩ := (hI0 (.eqAny zE ieAll) (by simp [atomsI0]) : (At.eqAny zE ieAll).holds)
    obtain ⟨p, hp, q, hq, rfl⟩ := mem_ieAll_iff.1 hc
    exact ⟨p, hp, q, hq, by simpa [Ex.evalG, zE, evalG_ieE] using he⟩
  · obtain ⟨c, hc, he⟩ := (hI0 (.eqAny uE ieAll) (by simp [atomsI0]) : (At.eqAny uE ieAll).holds)
    obtain ⟨p, hp, q, hq, rfl⟩ := mem_ieAll_iff.1 hc
    exact ⟨p, hp, q, hq, by simpa [Ex.evalG, uE, evalG_ieE] using he⟩
  · intro p hp q hq
    simpa [At.holds, Ex.evalG, zE, evalG_ieE] using
      hI p hp q hq (.eq (.mul (ieE p q) zE) (.mul zE (ieE p q))) (by simp [atomsIpq])
  · intro p hp q hq k hk
    obtain ⟨c, hc, he⟩ := (hI p hp q hq (.eqAny (.mul (ieE p q) (X k))
      ((pows (X k)).map fun c => .mul c (ieE p q))) (by
        simp only [atomsIpq, List.mem_append, List.mem_map, List.mem_range]
        exact Or.inr ⟨k, hk, rfl⟩) :
      (At.eqAny (.mul (ieE p q) (X k)) ((pows (X k)).map fun c => .mul c (ieE p q))).holds)
    simp only [List.mem_map] at hc
    obtain ⟨c0, hc0, rfl⟩ := hc
    obtain ⟨m, hm, rfl⟩ := mem_pows_iff.1 hc0
    exact ⟨m, hm, by simpa [Ex.evalG, X, evalG_ieE] using he⟩
  · intro p hp q hq hsq
    have := hI p hp q hq (.imp (.eq (.mul (ieE p q) (ieE p q)) .one)
      (.eqAny (ieE p q) [.one, zE, uE, uzE])) (by simp [atomsIpq])
    have h2 := this (by simpa [At.holds, Ex.evalG, evalG_ieE] using hsq)
    obtain ⟨c, hc, he⟩ := h2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl
    · exact Or.inl (by simpa [Ex.evalG, evalG_ieE] using he)
    · exact Or.inr (Or.inl (by simpa [Ex.evalG, evalG_ieE, zE] using he))
    · exact Or.inr (Or.inr (Or.inl (by simpa [Ex.evalG, evalG_ieE, uE] using he)))
    · exact Or.inr (Or.inr (Or.inr (by simpa [Ex.evalG, evalG_ieE, uzE, uE, zE] using he)))
  · intro p hp q hq p' hp' q' hq' hlt
    have := hId (.ne (ieE p q) (ieE p' q')) (by
      simp only [atomsIdist, List.mem_flatMap, List.mem_range]
      exact ⟨p, hp, q, hq, p', hp', q', hq', by rw [if_pos hlt]; simp⟩)
    simpa [At.holds, evalG_ieE] using this
  · obtain ⟨c, hc, he⟩ := holds_cn (hR0 (cn rE (X 0) (pows (X 0))) (by simp [atomsRS0]))
    obtain ⟨m, hm, rfl⟩ := mem_pows_iff.1 hc
    exact ⟨m, hm, by simpa [Ex.evalG, X, rE] using he⟩
  · obtain ⟨c, hc, he⟩ := holds_cn (hR0 (cn rE uE [uzE]) (by simp [atomsRS0]))
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    subst hc
    simpa [Ex.evalG, uE, rE, uzE, zE] using he
  · obtain ⟨c, hc, he⟩ := holds_cn (hR0 (cn rE zE [zE]) (by simp [atomsRS0]))
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    subst hc
    simpa [Ex.evalG, zE, rE] using he
  · obtain ⟨c, hc, he⟩ := holds_cn (hR0 (cn rE i1E ieAll) (by simp [atomsRS0]))
    obtain ⟨p, hp, q, hq, rfl⟩ := mem_ieAll_iff.1 hc
    exact ⟨p, hp, q, hq, by simpa [Ex.evalG, i1E, rE, evalG_ieE] using he⟩
  · obtain ⟨c, hc, he⟩ := holds_cn (hR0 (cn rE i2E ieAll) (by simp [atomsRS0]))
    obtain ⟨p, hp, q, hq, rfl⟩ := mem_ieAll_iff.1 hc
    exact ⟨p, hp, q, hq, by simpa [Ex.evalG, i2E, rE, evalG_ieE] using he⟩
  · obtain ⟨c, hc, he⟩ := holds_cn (hR0 (cn sE i1E ieAll) (by simp [atomsRS0]))
    obtain ⟨p, hp, q, hq, rfl⟩ := mem_ieAll_iff.1 hc
    exact ⟨p, hp, q, hq, by simpa [Ex.evalG, i1E, sE, evalG_ieE] using he⟩
  · obtain ⟨c, hc, he⟩ := holds_cn (hR0 (cn sE i2E ieAll) (by simp [atomsRS0]))
    obtain ⟨p, hp, q, hq, rfl⟩ := mem_ieAll_iff.1 hc
    exact ⟨p, hp, q, hq, by simpa [Ex.evalG, i2E, sE, evalG_ieE] using he⟩
  · intro k hk
    obtain ⟨c, hc, he⟩ := holds_cn (hRk k hk (cn rE (X k) (pows (X ((12 - k) % 12))))
      (by simp [atomsRSk]))
    obtain ⟨m, hm, rfl⟩ := mem_pows_iff.1 hc
    exact ⟨m, hm, by simpa [Ex.evalG, X, rE] using he⟩
  · intro k hk
    obtain ⟨c, hc, he⟩ := holds_cn (hRk k hk (cn sE (X k) (pows (X ((13 - k) % 12))))
      (by simp [atomsRSk]))
    obtain ⟨m, hm, rfl⟩ := mem_pows_iff.1 hc
    exact ⟨m, hm, by simpa [Ex.evalG, X, sE] using he⟩


theorem map_labG {H K : Type*} [Group H] [Group K] (f : H →* K) (z u : H) (k : ℕ) :
    f (labG z u k) = labG (f z) (f u) k := by
  unfold labG
  split_ifs <;> simp [map_mul]

theorem Cfg.of_inj {H K : Type*} [Group H] [Group K] (f : H →* K) (hf : Function.Injective f)
    {x : ℕ → H} {z y u i1 i2 r s : H}
    (h : Cfg (fun k => f (x k)) (f z) (f y) (f u) (f i1) (f i2) (f r) (f s)) :
    Cfg x z y u i1 i2 r s := by
  have hmul : ∀ a b c d : H, f a * f b = f c * f d → a * b = c * d := fun a b c d e =>
    hf (by simpa [map_mul] using e)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hf (by simpa using h.z_sq)
  · exact fun e => h.z_ne (by simp [e])
  · exact hf (by simpa using h.u_sq)
  · exact fun e => h.u_ne (by simp [e])
  · exact fun e => h.u_ne_z (by simp [e])
  · exact hmul _ _ _ _ h.comm
  · exact hf (by simpa using h.y_cube)
  · exact fun e => h.y_ne (by simp [e])
  · exact hmul _ _ _ _ h.y_comm
  · intro k hk
    exact hf (by simpa using h.x_pow k hk)
  · intro k hk
    exact fun e => h.x_ne k hk (by simp [e])
  · intro k hk
    have := h.x_cent k hk
    rw [← map_labG] at this
    exact hmul _ _ _ _ this
  · intro k hk
    have := h.x_inv1 k hk
    rw [← map_labG] at this
    exact hf (by simpa [map_mul] using this)
  · intro k hk
    have := h.x_inv2 k hk
    rw [← map_labG] at this
    exact hf (by simpa [map_mul] using this)
  · intro k hk
    exact hmul _ _ _ _ (h.x_adj k hk)
  · intro k hk e
    exact h.x_nadj k hk (by simpa [map_mul] using congrArg f e)
  · intro i hi j hj hij m hm e
    exact h.x_dist i hi j hj hij m hm (by simpa [map_pow] using congrArg f e)
  · exact hf (by simpa using h.i1_pow)
  · exact hf (by simpa using h.i2_pow)
  · exact hmul _ _ _ _ h.i_comm
  · obtain ⟨p, hp, q, hq, e⟩ := h.z_mem
    exact ⟨p, hp, q, hq, hf (by simpa [map_mul, map_pow] using e)⟩
  · obtain ⟨p, hp, q, hq, e⟩ := h.u_mem
    exact ⟨p, hp, q, hq, hf (by simpa [map_mul, map_pow] using e)⟩
  · intro p hp q hq
    exact hf (by simpa [map_mul, map_pow] using h.i_cz p hp q hq)
  · intro p hp q hq k hk
    obtain ⟨m, hm, e⟩ := h.i_nx p hp q hq k hk
    exact ⟨m, hm, hf (by simpa [map_mul, map_pow] using e)⟩
  · intro p hp q hq hsq
    have := h.i_inv p hp q hq (by simpa [map_mul, map_pow] using congrArg f hsq)
    rcases this with e | e | e | e
    · exact Or.inl (hf (by simpa [map_mul, map_pow] using e))
    · exact Or.inr (Or.inl (hf (by simpa [map_mul, map_pow] using e)))
    · exact Or.inr (Or.inr (Or.inl (hf (by simpa [map_mul, map_pow] using e))))
    · exact Or.inr (Or.inr (Or.inr (hf (by simpa [map_mul, map_pow] using e))))
  · intro p hp q hq p' hp' q' hq' hlt e
    exact h.i_dist p hp q hq p' hp' q' hq' hlt (by simpa [map_mul, map_pow] using congrArg f e)
  · obtain ⟨m, hm, e⟩ := h.r_b
    exact ⟨m, hm, hf (by simpa [map_mul, map_pow] using e)⟩
  · exact hf (by simpa [map_mul] using h.r_u)
  · exact hf (by simpa [map_mul] using h.r_z)
  · obtain ⟨p, hp, q, hq, e⟩ := h.r_i1
    exact ⟨p, hp, q, hq, hf (by simpa [map_mul, map_pow] using e)⟩
  · obtain ⟨p, hp, q, hq, e⟩ := h.r_i2
    exact ⟨p, hp, q, hq, hf (by simpa [map_mul, map_pow] using e)⟩
  · obtain ⟨p, hp, q, hq, e⟩ := h.s_i1
    exact ⟨p, hp, q, hq, hf (by simpa [map_mul, map_pow] using e)⟩
  · obtain ⟨p, hp, q, hq, e⟩ := h.s_i2
    exact ⟨p, hp, q, hq, hf (by simpa [map_mul, map_pow] using e)⟩
  · intro k hk
    obtain ⟨m, hm, e⟩ := h.r_x k hk
    exact ⟨m, hm, hf (by simpa [map_mul, map_pow] using e)⟩
  · intro k hk
    obtain ⟨m, hm, e⟩ := h.s_x k hk
    exact ⟨m, hm, hf (by simpa [map_mul, map_pow] using e)⟩

end CFSG.Sporadic.RuSchreier.J49
