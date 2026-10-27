module

public import CFSG.RankThree.Native.PermEnumeration

public section

namespace CFSG.Quasithin.H13.Ch4.HatChk

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer CFSG.RankThree.Native

variable {n : ℕ}

@[expose] def fpfA (n : ℕ) (x : Array ℕ) : Bool := allLt n fun i => x[i]! != i

@[expose] def cmA (n : ℕ) (p x : Array ℕ) : Bool := eqA n (compA n p x) (compA n x p)

@[expose] def centralA (n : ℕ) (gs : Array (Array ℕ)) (x : Array ℕ) : Bool :=
  allLt gs.size fun k => cmA n gs[k]! x

@[expose] def memA (n : ℕ) (ps : List ℕ) (c : ArrCert) (ks : Array ℕ) (t : Array ℕ) : Bool :=
  let k := keyA n ps t
  !(allLt c.pts.size fun j => !(ks[j]! == k && eqA n t c.pts[j]!))

@[expose] def keysOf (n : ℕ) (ps : List ℕ) (c : ArrCert) : Array ℕ := c.pts.map (keyA n ps)

@[expose] def coverOK (n m : ℕ) (ps : List ℕ) (c₁ c₂ : ArrCert) (cls : Array ℕ) : Bool :=
  let ks := keysOf n ps c₂
  let mem := c₁.pts.map fun t => memA n ps c₂ ks t
  let idx := (List.range c₁.pts.size).filter fun i => mem[i]!
  idx.all (fun i => decide (cls[i]! < m)) &&
    idx.all fun i => idx.all fun j =>
      i == j || cls[i]! != cls[j]! || !cmA n c₁.pts[i]! c₁.pts[j]!

@[expose] def greedyCover (n : ℕ) (ps : List ℕ) (c₁ c₂ : ArrCert) : Array ℕ := Id.run do
  let ks := keysOf n ps c₂
  let mut cls : Array ℕ := Array.replicate c₁.pts.size 0
  let mut classes : Array (Array ℕ) := #[]
  for i in [0:c₁.pts.size] do
    if memA n ps c₂ ks c₁.pts[i]! then
      let mut placed := false
      for k in [0:classes.size] do
        if !placed && (classes[k]!).all (fun j => !cmA n c₁.pts[i]! c₁.pts[j]!) then
          classes := classes.set! k ((classes[k]!).push i)
          cls := cls.set! i k
          placed := true
      if !placed then
        cls := cls.set! i classes.size
        classes := classes.push #[i]
  return cls

@[expose] def fpfPairOK (n : ℕ) (gs : Array (Array ℕ)) (c : ArrCert) (r : Array ℕ) : Bool :=
  allLt c.pts.size fun j =>
    !(centralA n gs c.pts[j]! && fpfA n c.pts[j]! && !eqA n c.pts[j]! r) ||
      !fpfA n (compA n r c.pts[j]!)

theorem fpfA_iff {t : Array ℕ} {g : Equiv.Perm (Fin n)} (ht : Rep n t g) :
    fpfA n t = true ↔ ∀ i : Fin n, g i ≠ i := by
  rw [fpfA, allLt_iff]
  constructor
  · intro h i hi
    have h1 := h i i.2
    rw [bne_iff_ne, ht.apply i.2] at h1
    exact h1 (congrArg Fin.val hi)
  · intro h i hi
    rw [bne_iff_ne, ht.apply hi]
    intro h1
    exact h ⟨i, hi⟩ (Fin.ext h1)

theorem cmA_iff {t u : Array ℕ} {g h : Equiv.Perm (Fin n)} (ht : Rep n t g) (hu : Rep n u h) :
    cmA n t u = true ↔ g * h = h * g :=
  eqA_iff (rep_compA ht hu) (rep_compA hu ht)

theorem centralA_iff {gs : Array (Array ℕ)} (hgs : ∀ k < gs.size, validA n gs[k]! = true)
    {t : Array ℕ} {g : Equiv.Perm (Fin n)} (ht : Rep n t g) :
    centralA n gs t = true ↔ ∀ k < gs.size, permOfArr n gs[k]! * g = g * permOfArr n gs[k]! := by
  rw [centralA, allLt_iff]
  exact forall₂_congr fun k hk => cmA_iff (rep_of_validA (hgs k hk)) ht

theorem map_getElem! {α β : Type} [Inhabited α] [Inhabited β] (f : α → β) (a : Array α) {j : ℕ}
    (hj : j < a.size) : (a.map f)[j]! = f a[j]! := by
  rw [getElem!_pos (a.map f) j (by simpa using hj), Array.getElem_map, getElem!_pos a j hj]

theorem memA_iff {ps : List ℕ} {c : ArrCert} {ks t : Array ℕ} :
    memA n ps c ks t = true ↔
      ∃ j < c.pts.size, ks[j]! = keyA n ps t ∧ eqA n t c.pts[j]! = true := by
  unfold memA
  rw [Bool.not_eq_true', ← Bool.not_eq_true, allLt_iff]
  constructor
  · intro h
    by_contra hne
    push Not at hne
    apply h
    intro j hj
    by_cases hk : ks[j]! = keyA n ps t
    · have h1 := hne j hj hk
      simp [hk, h1]
    · simp [hk]
  · rintro ⟨j, hj, hk, he⟩ hall
    have h1 := hall j hj
    simp [hk, he] at h1

theorem memA_of_mem {gs : Array (Array ℕ)} {ps : List ℕ} {c : ArrCert} (hps : ∀ p ∈ ps, p < n)
    (h : enumOK n gs ps c = true) {t : Array ℕ} {g : Equiv.Perm (Fin n)} (ht : Rep n t g)
    (hvt : validA n t = true) (hg : g ∈ Subgroup.closure (permsA n gs)) :
    memA n ps c (keysOf n ps c) t = true := by
  obtain ⟨hmem, -, hval⟩ := enumOK_spec hps h
  obtain ⟨j, hj, hgj⟩ := (hmem g).1 hg
  have hrj := rep_of_validA (hval j hj)
  rw [hgj] at hrj
  refine memA_iff.2 ⟨j, hj, ?_, (eqA_iff ht hrj).2 rfl⟩
  rw [keysOf, map_getElem! _ _ hj]
  exact keyA_eq hps (hval j hj) hvt (by rw [hgj, permOfArr_eq_of_rep ht])

theorem mem_of_memA {gs : Array (Array ℕ)} {ps : List ℕ} {c : ArrCert} (hps : ∀ p ∈ ps, p < n)
    (h : enumOK n gs ps c = true) {ks : Array ℕ} {t : Array ℕ} {g : Equiv.Perm (Fin n)}
    (ht : Rep n t g) (hm : memA n ps c ks t = true) : g ∈ Subgroup.closure (permsA n gs) := by
  obtain ⟨j, hj, -, hjt⟩ := memA_iff.1 hm
  obtain ⟨hmem, -, hval⟩ := enumOK_spec hps h
  have hrj := rep_of_validA (hval j hj)
  have hgj : g = permOfArr n c.pts[j]! := (eqA_iff ht hrj).1 hjt
  exact (hmem g).2 ⟨j, hj, hgj.symm⟩

theorem card_le_of_coverOK {gs₁ gs₂ : Array (Array ℕ)} {ps : List ℕ} {c₁ c₂ : ArrCert}
    {m : ℕ} {cls : Array ℕ} (hps : ∀ p ∈ ps, p < n) (h₁ : enumOK n gs₁ ps c₁ = true)
    (h₂ : enumOK n gs₂ ps c₂ = true) (hc : coverOK n m ps c₁ c₂ cls = true)
    {A : Subgroup (Equiv.Perm (Fin n))} (hA₁ : A ≤ Subgroup.closure (permsA n gs₁))
    (hA₂ : A ≤ Subgroup.closure (permsA n gs₂)) (hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) :
    Nat.card A ≤ m := by
  obtain ⟨hmem₁, -, hval₁⟩ := enumOK_spec hps h₁
  rw [coverOK, Bool.and_eq_true, List.all_eq_true, List.all_eq_true] at hc
  obtain ⟨hlt, hpair⟩ := hc
  have hidx : ∀ a : ↥A, ∃ i < c₁.pts.size, permOfArr n c₁.pts[i]! = a := fun a =>
    (hmem₁ a).1 (hA₁ a.2)
  choose ι hι hιa using hidx
  have hin : ∀ a : ↥A, ι a ∈ (List.range c₁.pts.size).filter fun i =>
      (c₁.pts.map fun t => memA n ps c₂ (keysOf n ps c₂) t)[i]! := by
    intro a
    rw [List.mem_filter, List.mem_range, map_getElem! _ _ (hι a)]
    refine ⟨hι a, ?_⟩
    have hr := rep_of_validA (hval₁ (ι a) (hι a))
    rw [hιa] at hr
    exact memA_of_mem hps h₂ hr (hval₁ (ι a) (hι a)) (hA₂ a.2)
  let f : ↥A → Fin m := fun a => ⟨cls[ι a]!, of_decide_eq_true (hlt _ (hin a))⟩
  have hf : Function.Injective f := by
    intro a b hab
    have hcls : cls[ι a]! = cls[ι b]! := congrArg Fin.val hab
    by_contra hne
    have hij : ι a ≠ ι b := fun h => hne (Subtype.ext (by rw [← hιa a, ← hιa b, h]))
    have h1 := hpair _ (hin a)
    rw [List.all_eq_true] at h1
    have h2 := h1 _ (hin b)
    simp only [Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq, Bool.not_eq_true'] at h2
    rcases h2 with (h2 | h2) | h2
    · exact hij h2
    · exact h2 hcls
    · have hra := rep_of_validA (hval₁ (ι a) (hι a))
      have hrb := rep_of_validA (hval₁ (ι b) (hι b))
      rw [hιa] at hra
      rw [hιa] at hrb
      have hcm := (cmA_iff hra hrb).2 (hAc a a.2 b b.2)
      rw [h2] at hcm
      exact Bool.noConfusion hcm
  have h3 := Nat.card_le_card_of_injective f hf
  rwa [Nat.card_eq_fintype_card (α := Fin m), Fintype.card_fin] at h3

theorem exists_fixed_of_fpfPairOK {gs : Array (Array ℕ)} {ps : List ℕ} {c : ArrCert}
    (hps : ∀ p ∈ ps, p < n) (h : enumOK n gs ps c = true) {r : Array ℕ}
    {ρ : Equiv.Perm (Fin n)} (hr : Rep n r ρ) (hchk : fpfPairOK n gs c r = true)
    {b : Equiv.Perm (Fin n)} (hb : b ∈ Subgroup.closure (permsA n gs))
    (hbc : ∀ k < gs.size, permOfArr n gs[k]! * b = b * permOfArr n gs[k]!)
    (hbf : ∀ i : Fin n, b i ≠ i) (hbr : b ≠ ρ) : ∃ i : Fin n, (ρ * b) i = i := by
  obtain ⟨hmem, -, hval⟩ := enumOK_spec hps h
  have hgs : ∀ k < gs.size, validA n gs[k]! = true := fun k hk => enumOK_gens_valid h hk
  obtain ⟨j, hj, hbj⟩ := (hmem b).1 hb
  have hrj := rep_of_validA (hval j hj)
  rw [hbj] at hrj
  have h1 := allLt_spec hchk hj
  simp only [Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff] at h1
  by_contra hfix
  push Not at hfix
  rcases h1 with ((h1 | h1) | h1) | h1
  · rw [(centralA_iff hgs hrj).2 hbc] at h1
    exact Bool.noConfusion h1
  · rw [(fpfA_iff hrj).2 hbf] at h1
    exact Bool.noConfusion h1
  · simp only [Bool.not_eq_false'] at h1
    exact hbr ((eqA_iff hrj hr).1 h1)
  · rw [(fpfA_iff (rep_compA hr hrj)).2 hfix] at h1
    exact Bool.noConfusion h1

end CFSG.Quasithin.H13.Ch4.HatChk
