module

public import CFSG.LocalAnalysis.StandardType.GGSignedCoordBlocks

public section

namespace CFSG.StandardType

private def AlignRoot {p N : ℕ} (v : Fin N → ZMod p) : Prop :=
  (∃ k, ∃ c : ZMod p, c ≠ 0 ∧ v = Pi.single k c) ∨
    ∃ k l, k ≠ l ∧ ∃ c : ZMod p, c ≠ 0 ∧ ∃ σ : ZMod p, (σ = 1 ∨ σ = -1) ∧
      v = Pi.single k c + Pi.single l (σ * c)

private theorem align_single_same {p N : ℕ} {k : Fin N} (c : ZMod p) :
    (Pi.single (M := fun _ => ZMod p) k c : Fin N → ZMod p) k = c :=
  Pi.single_eq_same (M := fun _ => ZMod p) k c

private theorem align_single_zero {p N : ℕ} {k j : Fin N} (h : j ≠ k) (c : ZMod p) :
    (Pi.single (M := fun _ => ZMod p) k c : Fin N → ZMod p) j = 0 :=
  Pi.single_eq_of_ne (M := fun _ => ZMod p) h c

private theorem alignRoot_eq_of_ne {p N : ℕ} {v : Fin N → ZMod p} {k : Fin N} {c : ZMod p}
    (hv : v = Pi.single k c) {j : Fin N} (hj : v j ≠ 0) : j = k := by
  by_contra h
  exact hj (by rw [hv, align_single_zero h c])

private theorem alignRoot_mem_of_ne {p N : ℕ} {v : Fin N → ZMod p} {k l : Fin N}
    {c d : ZMod p} (hv : v = Pi.single k c + Pi.single l d) {j : Fin N}
    (hj : v j ≠ 0) : j = k ∨ j = l := by
  by_contra h
  rw [not_or] at h
  exact hj (by rw [hv, Pi.add_apply, align_single_zero h.1 c, align_single_zero h.2 d,
    add_zero])

private theorem alignRoot_not_three_nonzero {p N : ℕ} {v : Fin N → ZMod p}
    (hv : AlignRoot v) {k₁ k₂ k₃ : Fin N}
    (h₁₂ : k₁ ≠ k₂) (h₁₃ : k₁ ≠ k₃) (h₂₃ : k₂ ≠ k₃) :
    ¬ (v k₁ ≠ 0 ∧ v k₂ ≠ 0 ∧ v k₃ ≠ 0) := by
  rintro ⟨h1, h2, h3⟩
  rcases hv with ⟨k, c, -, hv'⟩ | ⟨k, l, hkl, c, -, σ, -, hv'⟩
  · have h1k := alignRoot_eq_of_ne hv' h1
    have h2k := alignRoot_eq_of_ne hv' h2
    exact h₁₂ (h1k.trans h2k.symm)
  · have h1' := alignRoot_mem_of_ne hv' h1
    have h2' := alignRoot_mem_of_ne hv' h2
    have h3' := alignRoot_mem_of_ne hv' h3
    rcases h1' with h1k | h1l
    · have h2l : k₂ = l := by
        rcases h2' with h2k | h2l
        · exact absurd (h1k.trans h2k.symm) h₁₂
        · exact h2l
      have h3l : k₃ = l := by
        rcases h3' with h3k | h3l
        · exact absurd (h1k.trans h3k.symm) h₁₃
        · exact h3l
      exact h₂₃ (h2l.trans h3l.symm)
    · have h2k : k₂ = k := by
        rcases h2' with h2k | h2l
        · exact h2k
        · exact absurd (h1l.trans h2l.symm) h₁₂
      have h3k : k₃ = k := by
        rcases h3' with h3k | h3l
        · exact h3k
        · exact absurd (h1l.trans h3l.symm) h₁₃
      exact h₂₃ (h2k.trans h3k.symm)

private theorem align_signedPerm_single {p N : ℕ} (π : Equiv.Perm (Fin N))
    (ε : Fin N → ZMod p) (i : Fin N) :
    (fun k => ε (π.symm k) * (Pi.single i (1 : ZMod p) : Fin N → ZMod p) (π.symm k)) =
      Pi.single (π i) (ε i) := by
  funext k
  have hiff : π.symm k = i ↔ k = π i := Equiv.symm_apply_eq π
  rw [Pi.single_apply, Pi.single_apply]
  by_cases h : k = π i
  · rw [if_pos h, if_pos (hiff.2 h)]
    rw [hiff.2 h, mul_one]
  · rw [if_neg h, if_neg (fun hh => h (hiff.1 hh)), mul_zero]

private theorem align_two_ne_zero_zmod {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    (2 : ZMod p) ≠ 0 := by
  intro h
  have hdvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h
  have hp2le : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hple : p ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
  omega

private theorem align_one_ne_zero_zmod {p : ℕ} [Fact p.Prime] : (1 : ZMod p) ≠ 0 := by
  intro h
  have hp1 : p = 1 := (ZMod.one_eq_zero_iff).mp h
  have hp2le : 2 ≤ p := (Fact.out : p.Prime).two_le
  omega

private theorem align_neg_two_eq_zmod {p : ℕ} [Fact p.Prime] :
    (-2 : ZMod p) = -1 + -1 := by
  have h2 : (2 : ZMod p) = 1 + 1 := by norm_num
  calc (-2 : ZMod p) = -(1 + 1) := congrArg Neg.neg h2
    _ = -1 + -1 := neg_add_rev 1 1

private theorem align_neg_mul_neg_eq {p : ℕ} (ε t : ZMod p) :
    (-ε) * (-t⁻¹) = t⁻¹ * ε := by
  calc (-ε) * (-t⁻¹) = ε * t⁻¹ := neg_mul_neg ε t⁻¹
    _ = t⁻¹ * ε := mul_comm _ _

private theorem align_eq_smul_inv {p N : ℕ} [Fact p.Prime] {v d : Fin N → ZMod p} {t : ZMod p}
    (ht : d = t • v) (htne : t ≠ 0) : v = t⁻¹ • d := by
  rw [ht]
  rw [smul_smul, inv_mul_cancel₀ htne, one_smul]

private theorem align_exists_ne_ne {N : ℕ} (hN : 3 ≤ N) (k l : Fin N) :
    ∃ m : Fin N, m ≠ k ∧ m ≠ l := by
  have hcard : ({k, l} : Finset (Fin N)).card < Fintype.card (Fin N) := by
    have hle : ({k, l} : Finset (Fin N)).card ≤ 2 := by
      simpa using Finset.card_insert_le (a := k) (s := ({l} : Finset (Fin N)))
    rw [Fintype.card_fin]
    omega
  obtain ⟨m, -, hm⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  exact ⟨m, fun h => hm (by rw [h]; simp), fun h => hm (by rw [h]; simp)⟩

private theorem align_t_inv_sub_eq_single {p N : ℕ} (π : Equiv.Perm (Fin N))
    (ε : Fin N → ZMod p) (i : Fin N) (t : ZMod p) :
    t⁻¹ • (Pi.single (M := fun _ => ZMod p) (π i) (ε i) -
        Pi.single (M := fun _ => ZMod p) i (1 : ZMod p)) =
      Pi.single (M := fun _ => ZMod p) i (-t⁻¹) +
        Pi.single (M := fun _ => ZMod p) (π i) (t⁻¹ * ε i) := by
  rw [smul_sub, ← Pi.single_smul (f := fun _ => ZMod p), ← Pi.single_smul (f := fun _ => ZMod p),
    smul_eq_mul, smul_eq_mul, mul_one]
  rw [sub_eq_add_neg, Pi.single_neg, add_comm]

private theorem alignRoot_two_roots_no_three {p N : ℕ} {r r' : Fin N → ZMod p}
    (hr : AlignRoot r) (hr' : AlignRoot r') {i j m : Fin N}
    (hij : i ≠ j) (him : i ≠ m) (hjm : j ≠ m)
    (hri : r i ≠ 0) (hrj_add : r j + r' j ≠ 0)
    (hrm : r m ≠ 0) (hr'i : r' i ≠ 0) (hr'm : r' m ≠ 0) : False := by
  by_cases hrj : r j = 0
  · have hr'j : r' j ≠ 0 := by simpa [hrj] using hrj_add
    exact alignRoot_not_three_nonzero hr' hij him hjm ⟨hr'i, hr'j, hr'm⟩
  · exact alignRoot_not_three_nonzero hr hij him hjm ⟨hri, hrj, hrm⟩

private theorem align_eq_neg_of_mul_eq_neg {p : ℕ} {σ c b : ZMod p}
    (h : σ * c = -b) : b = -(σ * c) := by
  rw [h, neg_neg]

private theorem alignShort_long_both_zero {p N : ℕ} [Fact p.Prime]
    {va vb : Fin N → ZMod p} {k l m : Fin N} {c σ : ZMod p}
    (hkl : k ≠ l) (hmk : m ≠ k) (hml : m ≠ l) (hc : c ≠ 0) (hσne : σ ≠ 0)
    (hvak : va k = c) (hval : va l = σ * c) (hsm : (va + vb) m ≠ 0)
    (hbk : vb k = 0) (hbl : vb l = 0) (hroot : AlignRoot (va + vb)) : False := by
  have hsk : (va + vb) k ≠ 0 := by
    rw [Pi.add_apply, hvak, hbk, add_zero]; exact hc
  have hsl : (va + vb) l ≠ 0 := by
    rw [Pi.add_apply, hval, hbl, add_zero]
    exact mul_ne_zero hσne hc
  exact alignRoot_not_three_nonzero hroot hkl hmk.symm hml.symm ⟨hsk, hsl, hsm⟩

private theorem alignShort_long_left_zero {p N : ℕ} [Fact p.Prime]
    {va vb : Fin N → ZMod p} {k l m : Fin N} {c σ : ZMod p}
    (hkl : k ≠ l) (hmk : m ≠ k) (hml : m ≠ l) (hc : c ≠ 0) (hσne : σ ≠ 0)
    (h2ne : (2 : ZMod p) ≠ 0)
    (hvak : va k = c) (hval : va l = σ * c)
    (hsm : (va + vb) m ≠ 0) (hdm : (va - vb) m ≠ 0)
    (hbk : vb k = 0)
    (hsr : AlignRoot (va + vb)) (hdr : AlignRoot (va - vb)) : False := by
  have hsk : (va + vb) k ≠ 0 := by
    rw [Pi.add_apply, hvak, hbk, add_zero]; exact hc
  have hdk : (va - vb) k ≠ 0 := by
    have hkval : (va - vb) k = c := by
      rw [Pi.sub_apply, hvak, hbk]
      exact sub_zero c
    rw [hkval]; exact hc
  have hsuml : (va + vb) l + (va - vb) l ≠ 0 := by
    have h2σc : (2 : ZMod p) * (σ * c) ≠ 0 :=
      mul_ne_zero h2ne (mul_ne_zero hσne hc)
    have hsum : (va + vb) l + (va - vb) l = 2 * (σ * c) := by
      rw [Pi.add_apply, Pi.sub_apply, hval]; ring
    rw [hsum]; exact h2σc
  exact alignRoot_two_roots_no_three hsr hdr hkl hmk.symm hml.symm hsk hsuml hsm hdk hdm

private theorem alignShort_long_right_zero {p N : ℕ} [Fact p.Prime]
    {va vb : Fin N → ZMod p} {k l m : Fin N} {c σ : ZMod p}
    (hkl : k ≠ l) (hmk : m ≠ k) (hml : m ≠ l) (hc : c ≠ 0) (hσne : σ ≠ 0)
    (h2ne : (2 : ZMod p) ≠ 0)
    (hvak : va k = c) (hval : va l = σ * c)
    (hsm : (va + vb) m ≠ 0) (hdm : (va - vb) m ≠ 0)
    (hbl : vb l = 0)
    (hsr : AlignRoot (va + vb)) (hdr : AlignRoot (va - vb)) : False := by
  have hsl : (va + vb) l ≠ 0 := by
    rw [Pi.add_apply, hval, hbl, add_zero]
    exact mul_ne_zero hσne hc
  have hdl : (va - vb) l ≠ 0 := by
    have hlval : (va - vb) l = σ * c := by
      rw [Pi.sub_apply, hval, hbl]
      exact sub_zero (σ * c)
    rw [hlval]; exact mul_ne_zero hσne hc
  have hsumk : (va + vb) k + (va - vb) k ≠ 0 := by
    have h2c : (2 : ZMod p) * c ≠ 0 := mul_ne_zero h2ne hc
    have hsum : (va + vb) k + (va - vb) k = 2 * c := by
      rw [Pi.add_apply, Pi.sub_apply, hvak]; ring
    rw [hsum]; exact h2c
  exact alignRoot_two_roots_no_three hsr hdr hkl.symm hml.symm hmk.symm hsl hsumk hsm hdl hdm

private theorem alignShort_long_false {p N M : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hN : 3 ≤ N)
    (v : Fin M → Fin N → ZMod p) (hroot : ∀ a, AlignRoot (v a))
    (hadd : ∀ a b, a ≠ b → AlignRoot (v a + v b))
    (hsub : ∀ a b, a ≠ b → AlignRoot (v a - v b))
    (hspan : ∀ m, ∃ a, v a m ≠ 0) (a : Fin M) {k l : Fin N} (hkl : k ≠ l)
    {c σ : ZMod p} (hc : c ≠ 0) (hσ : σ = 1 ∨ σ = -1)
    (hva : v a = Pi.single k c + Pi.single l (σ * c)) : False := by
  obtain ⟨m, hmk, hml⟩ := align_exists_ne_ne hN k l
  obtain ⟨b, hbm⟩ := hspan m
  have hvam : v a m = 0 := by
    rw [hva, Pi.add_apply, Pi.single_eq_of_ne hmk, Pi.single_eq_of_ne hml, zero_add]
  have hba : b ≠ a := by
    intro h
    rw [h] at hbm
    exact hbm hvam
  have hab : a ≠ b := hba.symm
  have hbroot : AlignRoot (v b) := hroot b
  have hbkl : v b k = 0 ∨ v b l = 0 := by
    by_cases h1 : v b k = 0
    · exact Or.inl h1
    · refine Or.inr ?_
      by_contra h2
      exact alignRoot_not_three_nonzero hbroot hkl hmk.symm hml.symm ⟨h1, h2, hbm⟩
  have hvak : v a k = c := by
    rw [hva, Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne hkl, add_zero]
  have hval : v a l = σ * c := by
    rw [hva, Pi.add_apply, Pi.single_eq_of_ne hkl.symm, Pi.single_eq_same, zero_add]
  have hsm : (v a + v b) m ≠ 0 := by rw [Pi.add_apply, hvam, zero_add]; exact hbm
  have hdm : (v a - v b) m ≠ 0 := by
    rw [Pi.sub_apply, hvam, zero_sub]
    exact neg_ne_zero.mpr hbm
  have hσne : σ ≠ 0 := by
    rcases hσ with h | h
    · rw [h]; exact align_one_ne_zero_zmod
    · rw [h]; exact neg_ne_zero.mpr align_one_ne_zero_zmod
  have h2ne : (2 : ZMod p) ≠ 0 := align_two_ne_zero_zmod hp2
  have hsr := hadd a b hab
  have hdr := hsub a b hab
  by_cases hboth : v b k = 0 ∧ v b l = 0
  · exact alignShort_long_both_zero hkl hmk hml hc hσne hvak hval hsm hboth.1 hboth.2 hsr
  · rcases hbkl with hbk | hbl
    · exact alignShort_long_left_zero hkl hmk hml hc hσne h2ne hvak hval hsm hdm hbk hsr hdr
    · exact alignShort_long_right_zero hkl hmk hml hc hσne h2ne hvak hval hsm hdm hbl hsr hdr

private theorem alignRoot_of_signedPerm_fixed {p N : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (π : Equiv.Perm (Fin N)) (ε : Fin N → ZMod p) (hε : ∀ i, ε i = 1 ∨ ε i = -1)
    (v : Fin N → ZMod p)
    (hW : ∀ y : Fin N → ZMod p, ∃ t : ZMod p,
      (fun k => ε (π.symm k) * y (π.symm k)) - y = t • v)
    (hne : ∃ y : Fin N → ZMod p, (fun k => ε (π.symm k) * y (π.symm k)) ≠ y)
    (hfix : ∀ i, π i = i) : AlignRoot v := by
  have h2ne : (2 : ZMod p) ≠ 0 := align_two_ne_zero_zmod hp2
  have hneg2 : (-2 : ZMod p) ≠ 0 := neg_ne_zero.mpr h2ne
  have hεne : ∃ k, ε k ≠ 1 := by
    by_contra h
    rw [not_exists] at h
    obtain ⟨y, hy⟩ := hne
    apply hy
    funext k
    have hk1 : ε k = 1 := by
      by_contra hk
      exact h k hk
    have hk' : π.symm k = k := (Equiv.symm_apply_eq π).2 (hfix k).symm
    rw [hk', hk1, one_mul]
  obtain ⟨k, hk⟩ := hεne
  have hεk : ε k = -1 := (hε k).resolve_left hk
  obtain ⟨t, ht⟩ := hW (Pi.single k 1)
  have hWy : (fun j => ε (π.symm j) * (Pi.single k 1 : Fin N → ZMod p) (π.symm j)) =
      Pi.single k (ε k) := by
    have h := align_signedPerm_single π ε k
    rw [hfix k] at h
    exact h
  have hd : (Pi.single k (-2 : ZMod p) : Fin N → ZMod p) = t • v := by
    rw [← ht, hWy, hεk, ← Pi.single_sub]
    congr 1
    rw [sub_eq_add_neg]
    exact align_neg_two_eq_zmod
  have htne : t ≠ 0 := by
    intro h0
    have hzero : (Pi.single k (-2 : ZMod p) : Fin N → ZMod p) = 0 := by
      rw [hd, h0, zero_smul]
    have hk2 : (-2 : ZMod p) = 0 := by simpa using congrFun hzero k
    exact hneg2 hk2
  have hv : v = Pi.single k (t⁻¹ * (-2 : ZMod p)) := by
    rw [align_eq_smul_inv hd htne]
    rw [← Pi.single_smul (f := fun _ => ZMod p), smul_eq_mul]
  exact Or.inl ⟨k, t⁻¹ * (-2 : ZMod p), mul_ne_zero (inv_ne_zero htne) hneg2, hv⟩

private theorem alignRoot_of_signedPerm_moved {p N : ℕ} [Fact p.Prime]
    (π : Equiv.Perm (Fin N)) (ε : Fin N → ZMod p) (hε : ∀ i, ε i = 1 ∨ ε i = -1)
    (v : Fin N → ZMod p)
    (hW : ∀ y : Fin N → ZMod p, ∃ t : ZMod p,
      (fun k => ε (π.symm k) * y (π.symm k)) - y = t • v)
    (hπ : ∃ i, π i ≠ i) : AlignRoot v := by
  obtain ⟨i, hπi⟩ := hπ
  obtain ⟨t, ht⟩ := hW (Pi.single i 1)
  have hWy : (fun j => ε (π.symm j) * (Pi.single i 1 : Fin N → ZMod p) (π.symm j)) =
      Pi.single (π i) (ε i) := align_signedPerm_single π ε i
  have hd : (((Pi.single (π i) (ε i) : Fin N → ZMod p) -
      (Pi.single i (1 : ZMod p) : Fin N → ZMod p))) = t • v := by
    rw [← ht, hWy]
  have hdi : (((Pi.single (π i) (ε i) : Fin N → ZMod p) -
      (Pi.single i (1 : ZMod p) : Fin N → ZMod p)) i) = -1 := by
    rw [Pi.sub_apply, align_single_zero (Ne.symm hπi) (ε i), align_single_same (1 : ZMod p)]
    exact zero_sub (1 : ZMod p)
  have hd0 : (((Pi.single (π i) (ε i) : Fin N → ZMod p) -
      (Pi.single i (1 : ZMod p) : Fin N → ZMod p))) ≠ 0 := by
    intro h
    have h' := congrFun h i
    rw [hdi] at h'
    exact align_one_ne_zero_zmod (neg_eq_zero.mp h')
  have htne : t ≠ 0 := by
    intro h0
    exact hd0 (by rw [hd, h0, zero_smul])
  have hv : v = Pi.single i (-t⁻¹) + Pi.single (π i) (t⁻¹ * ε i) := by
    calc v = t⁻¹ • (t • v) := by rw [smul_smul, inv_mul_cancel₀ htne, one_smul]
      _ = t⁻¹ • (((Pi.single (π i) (ε i) : Fin N → ZMod p) -
          (Pi.single i (1 : ZMod p) : Fin N → ZMod p))) := by
          rw [← hd]
      _ = Pi.single i (-t⁻¹) + Pi.single (π i) (t⁻¹ * ε i) :=
          align_t_inv_sub_eq_single π ε i t
  refine Or.inr ⟨i, π i, Ne.symm hπi, -t⁻¹, neg_ne_zero.mpr (inv_ne_zero htne), -ε i, ?_, ?_⟩
  · rcases hε i with h | h
    · right; rw [h]; rfl
    · left; rw [h]; exact neg_neg 1
  · rw [hv]
    have h : t⁻¹ * ε i = (-ε i) * (-t⁻¹) :=
      (align_neg_mul_neg_eq (ε i) t).symm
    rw [h]

private theorem alignRoot_of_signedPerm {p N : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (π : Equiv.Perm (Fin N)) (ε : Fin N → ZMod p) (hε : ∀ i, ε i = 1 ∨ ε i = -1)
    (v : Fin N → ZMod p)
    (hW : ∀ y : Fin N → ZMod p, ∃ t : ZMod p,
      (fun k => ε (π.symm k) * y (π.symm k)) - y = t • v)
    (hne : ∃ y : Fin N → ZMod p, (fun k => ε (π.symm k) * y (π.symm k)) ≠ y) :
    AlignRoot v := by
  by_cases hfix : ∀ i, π i = i
  · exact alignRoot_of_signedPerm_fixed hp2 π ε hε v hW hne hfix
  · rw [not_forall] at hfix
    exact alignRoot_of_signedPerm_moved π ε hε v hW hfix

private theorem alignShort_of_roots {p N M : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hN : 3 ≤ N)
    (v : Fin M → Fin N → ZMod p) (hroot : ∀ a, AlignRoot (v a))
    (hadd : ∀ a b, a ≠ b → AlignRoot (v a + v b))
    (hsub : ∀ a b, a ≠ b → AlignRoot (v a - v b))
    (hspan : ∀ m, ∃ a, v a m ≠ 0) :
    ∀ a, ∃ k, ∃ c : ZMod p, c ≠ 0 ∧ v a = Pi.single k c := by
  intro a
  rcases hroot a with ⟨k, c, hc, hv⟩ | ⟨k, l, hkl, c, hc, σ, hσ, hv⟩
  · exact ⟨k, c, hc, hv⟩
  · exact (alignShort_long_false hp2 hN v hroot hadd hsub hspan a hkl hc hσ hv).elim

private theorem alignMonomial_short_false {p N : ℕ} {u : Fin N → ZMod p}
    {k : Fin N → Fin N} {a b : Fin N} (hkab : k a ≠ k b)
    {k' : Fin N} {c' : ZMod p} (hu' : u = Pi.single k' c')
    (hua0 : u (k a) ≠ 0) (hub0 : u (k b) ≠ 0) : False := by
  have h1 : k a = k' := alignRoot_eq_of_ne hu' hua0
  have h2 : k b = k' := alignRoot_eq_of_ne hu' hub0
  exact absurd (h1.trans h2.symm) hkab

private theorem alignMonomial_long_left {p : ℕ} {c c' b σ : ZMod p}
    (hσ : σ = 1 ∨ σ = -1) (hka : c' = c) (hkb : σ * c' = -b) :
    b = c ∨ b = -c := by
  rw [hka] at hkb
  have hcb : b = -(σ * c) := align_eq_neg_of_mul_eq_neg hkb
  rcases hσ with h | h
  · right
    have h' : b = -((1 : ZMod p) * c) := by rw [h] at hcb; exact hcb
    calc b = -((1 : ZMod p) * c) := h'
      _ = -c := congrArg Neg.neg (one_mul c)
  · left
    have h' : b = -((-1 : ZMod p) * c) := by rw [h] at hcb; exact hcb
    calc b = -((-1 : ZMod p) * c) := h'
      _ = -(-c) := congrArg Neg.neg (neg_one_mul c)
      _ = c := neg_neg c

private theorem alignMonomial_long_right {p : ℕ} {c c' b σ : ZMod p}
    (hσ : σ = 1 ∨ σ = -1) (hka : σ * c' = c) (hkb : c' = -b) :
    b = c ∨ b = -c := by
  have hσ2 : σ * σ = 1 := by rcases hσ with h | h <;> simp [h]
  have hkb' : σ * (σ * c') = -b := by
    rw [← mul_assoc, hσ2, one_mul, hkb]
  exact alignMonomial_long_left hσ hka hkb'

private theorem alignMonomial_long_case {p N : ℕ} {k : Fin N → Fin N} {c : Fin N → ZMod p}
    {a b : Fin N} (hkab : k a ≠ k b) (u : Fin N → ZMod p)
    (hua : u (k a) = c a) (hub : u (k b) = -c b)
    (hua0 : u (k a) ≠ 0) (hub0 : u (k b) ≠ 0)
    {k' l' : Fin N} (hkl' : k' ≠ l') {c' σ : ZMod p}
    (hσ : σ = 1 ∨ σ = -1)
    (hu' : u = Pi.single k' c' + Pi.single l' (σ * c')) :
    c b = c a ∨ c b = -c a := by
  have h1 : k a = k' ∨ k a = l' := alignRoot_mem_of_ne hu' hua0
  have h2 : k b = k' ∨ k b = l' := alignRoot_mem_of_ne hu' hub0
  have hval_ka : (Pi.single (M := fun _ => ZMod p) k' c' +
      Pi.single (M := fun _ => ZMod p) l' (σ * c')) (k a) = c a := by
    rw [← hu']; exact hua
  have hval_kb : (Pi.single (M := fun _ => ZMod p) k' c' +
      Pi.single (M := fun _ => ZMod p) l' (σ * c')) (k b) = -c b := by
    rw [← hu']; exact hub
  rcases h1 with h1 | h1
  · have h2' : k b = l' := by
      rcases h2 with h2 | h2
      · exact absurd (h1.trans h2.symm) hkab
      · exact h2
    rw [Pi.add_apply, h1, Pi.single_eq_same, Pi.single_eq_of_ne hkl', add_zero] at hval_ka
    rw [Pi.add_apply, h2', Pi.single_eq_of_ne hkl'.symm, Pi.single_eq_same, zero_add] at hval_kb
    exact alignMonomial_long_left hσ hval_ka hval_kb
  · have h2' : k b = k' := by
      rcases h2 with h2 | h2
      · exact h2
      · exact absurd (h1.trans h2.symm) hkab
    rw [Pi.add_apply, h1, Pi.single_eq_of_ne hkl'.symm, Pi.single_eq_same, zero_add] at hval_ka
    rw [Pi.add_apply, h2', Pi.single_eq_same, Pi.single_eq_of_ne hkl', add_zero] at hval_kb
    exact alignMonomial_long_right hσ hval_ka hval_kb

private theorem alignMonomial_root_case {p N : ℕ} {k : Fin N → Fin N} {c : Fin N → ZMod p}
    {a b : Fin N} (hkab : k a ≠ k b) (u : Fin N → ZMod p)
    (hua : u (k a) = c a) (hub : u (k b) = -c b)
    (hua0 : u (k a) ≠ 0) (hub0 : u (k b) ≠ 0) (hu : AlignRoot u) :
    c b = c a ∨ c b = -c a := by
  rcases hu with ⟨k', c', hc', hu'⟩ | ⟨k', l', hkl', c', hc', σ, hσ, hu'⟩
  · exact (alignMonomial_short_false hkab hu' hua0 hub0).elim
  · exact alignMonomial_long_case hkab u hua hub hua0 hub0 hkl' hσ hu'

private theorem alignMonomial_of_short {p N : ℕ} (k : Fin N → Fin N) (c : Fin N → ZMod p)
    (hc : ∀ a, c a ≠ 0) (hk : Function.Surjective k)
    (hsub : ∀ a b, a ≠ b →
      AlignRoot (Pi.single (k a) (c a) - Pi.single (k b) (c b) : Fin N → ZMod p)) :
    Function.Bijective k ∧ ∀ a b, c b = c a ∨ c b = -c a := by
  have hbij : Function.Bijective k := Function.Surjective.bijective_of_finite hk
  refine ⟨hbij, ?_⟩
  intro a b
  by_cases hab : a = b
  · subst hab
    exact Or.inl rfl
  have hkab : k a ≠ k b := fun h => hab (hbij.injective h)
  let u : Fin N → ZMod p := Pi.single (k a) (c a) - Pi.single (k b) (c b)
  have hua : u (k a) = c a := by
    dsimp [u]
    rw [align_single_same (c a), align_single_zero hkab (c b)]
    exact sub_zero (c a)
  have hub : u (k b) = -c b := by
    dsimp [u]
    rw [align_single_zero hkab.symm (c a), align_single_same (c b)]
    exact zero_sub (c b)
  have hua0 : u (k a) ≠ 0 := by rw [hua]; exact hc a
  have hub0 : u (k b) ≠ 0 := by rw [hub]; exact neg_ne_zero.mpr (hc b)
  have hu : AlignRoot u := by simpa [u] using hsub a b hab
  exact alignMonomial_root_case hkab u hua hub hua0 hub0 hu

section AssemblyHelpers

open Multiplicative

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem toAdd_T_sum {p r : ℕ} [Fact p.Prime]
    (T : (Fin (r + 2) → Multiplicative (ZMod p)) →* (Fin (r + 1) → Multiplicative (ZMod p)))
    (x : Fin (r + 2) → Multiplicative (ZMod p)) (k : Fin (r + 1)) :
    Multiplicative.toAdd (T x k) =
      ∑ j : Fin (r + 2), Multiplicative.toAdd (x j) *
        Multiplicative.toAdd (T (Pi.mulSingle (M := fun _ : Fin (r + 2) => Multiplicative (ZMod p))
          j (Multiplicative.ofAdd (1 : ZMod p))) k) := by
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hx : x = ∏ j, Pi.mulSingle (M := fun _ : Fin (r + 2) => Multiplicative (ZMod p)) j (x j) :=
    (Finset.univ_prod_mulSingle x).symm
  conv_lhs => rw [hx]
  rw [map_prod, Finset.prod_apply, toAdd_prod]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h1 : Pi.mulSingle (M := fun _ : Fin (r + 2) => Multiplicative (ZMod p)) j (x j) =
      Pi.mulSingle (M := fun _ : Fin (r + 2) => Multiplicative (ZMod p)) j
        (Multiplicative.ofAdd (1 : ZMod p)) ^ (Multiplicative.toAdd (x j)).val := by
    conv_lhs => rw [← ofAdd_toAdd (x j), SpCoord.mulSingle_ofAdd_eq_pow]
  rw [h1, map_pow, SpCoord.toAdd_pow_apply, ZMod.natCast_zmod_val]

private theorem ker_eq_axis {p r : ℕ} [Fact p.Prime] {i0 : Fin (r + 2)}
    (T : (Fin (r + 2) → Multiplicative (ZMod p)) →* (Fin (r + 1) → Multiplicative (ZMod p)))
    (hTs : Function.Surjective T)
    (hker : ∀ x, T x = 1 → ∀ j, j ≠ i0 → x j = 1) :
    T (Pi.mulSingle i0 (Multiplicative.ofAdd (1 : ZMod p))) = 1 := by
  let f : Multiplicative (ZMod p) →* (Fin (r + 2) → Multiplicative (ZMod p)) :=
    MonoidHom.mulSingle (fun _ : Fin (r + 2) => Multiplicative (ZMod p)) i0
  have hf : Function.Injective f := by
    simpa [f] using Pi.mulSingle_injective (M := fun _ : Fin (r + 2) => Multiplicative (ZMod p)) i0
  have hcard_axis : Nat.card ↥f.range = p := by
    have hEquiv : ↥f.range ≃ ↑(Set.range f) :=
      Equiv.subtypeEquivRight fun x => by
        rw [MonoidHom.mem_range, Set.mem_range]
    calc Nat.card ↥f.range = Nat.card ↑(Set.range f) := Nat.card_congr hEquiv
      _ = Nat.card (Multiplicative (ZMod p)) := (Nat.card_congr (Equiv.ofInjective f hf)).symm
      _ = p := by rw [Nat.card_congr (Multiplicative.toAdd (α := ZMod p)), Nat.card_zmod]
  have hcard_ker : Nat.card ↥T.ker = p := by
    have hsrc : Nat.card (Fin (r + 2) → Multiplicative (ZMod p)) = p ^ (r + 2) := by
      rw [Nat.card_fun, Nat.card_congr (Multiplicative.toAdd (α := ZMod p)), Nat.card_zmod,
        Nat.card_fin]
    have htgt : Nat.card (Fin (r + 1) → Multiplicative (ZMod p)) = p ^ (r + 1) := by
      rw [Nat.card_fun, Nat.card_congr (Multiplicative.toAdd (α := ZMod p)), Nat.card_zmod,
        Nat.card_fin]
    have hrange : Nat.card ↥(T.range) = p ^ (r + 1) := by
      rw [MonoidHom.range_eq_top.2 hTs, Subgroup.card_top, htgt]
    have hcard := Subgroup.card_ker_mul_card_range T
    rw [hrange, hsrc] at hcard
    rw [Nat.pow_succ p (r + 1)] at hcard
    rw [Nat.mul_comm (Nat.card ↥T.ker) (p ^ (r + 1))] at hcard
    exact Nat.mul_left_cancel (Nat.pow_pos (Fact.out : p.Prime).pos) hcard
  have hle : T.ker ≤ f.range := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    rw [MonoidHom.mem_range]
    refine ⟨x i0, ?_⟩
    funext j
    by_cases hj : j = i0
    · subst hj; simp [f]
    · change f (x i0) j = x j
      rw [MonoidHom.mulSingle_apply, Pi.mulSingle_eq_of_ne hj]
      exact (hker x hx j hj).symm
  have heq : T.ker = f.range := by
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [hcard_axis, hcard_ker]
  have hmem : Pi.mulSingle i0 (Multiplicative.ofAdd (1 : ZMod p)) ∈ T.ker := by
    rw [heq]
    rw [MonoidHom.mem_range]
    exact ⟨Multiplicative.ofAdd (1 : ZMod p), rfl⟩
  exact MonoidHom.mem_ker.mp hmem

private theorem v_j_ne_zero {p r : ℕ} [Fact p.Prime] {i0 : Fin (r + 2)}
    (T : (Fin (r + 2) → Multiplicative (ZMod p)) →* (Fin (r + 1) → Multiplicative (ZMod p)))
    (hker : ∀ x, T x = 1 → ∀ j, j ≠ i0 → x j = 1)
    (j : Fin (r + 2)) (hj : j ≠ i0) :
    (fun k : Fin (r + 1) =>
      Multiplicative.toAdd (T (Pi.mulSingle j (Multiplicative.ofAdd (1 : ZMod p))) k)) ≠ 0 := by
  intro h
  have hT : T (Pi.mulSingle j (Multiplicative.ofAdd (1 : ZMod p))) = 1 := by
    funext k
    have hk := congrFun h k
    have hk0 :
        Multiplicative.toAdd (T (Pi.mulSingle j (Multiplicative.ofAdd (1 : ZMod p))) k) = 0 := hk
    have : Multiplicative.toAdd (T (Pi.mulSingle j (Multiplicative.ofAdd (1 : ZMod p))) k) =
        Multiplicative.toAdd (1 : Multiplicative (ZMod p)) := by
      rw [hk0, toAdd_one]
    exact Multiplicative.toAdd.injective this
  have hx := hker (Pi.mulSingle j (Multiplicative.ofAdd (1 : ZMod p))) hT j hj
  rw [Pi.mulSingle_eq_same] at hx
  have h1 : (1 : ZMod p) = 0 := by
    have := congrArg Multiplicative.toAdd hx
    rwa [toAdd_ofAdd, toAdd_one] at this
  exact (SpCoord.coord_zero_ne_one (Fact.out : p.Prime)) h1.symm

private theorem v_pair_linearIndependent {p r : ℕ} [Fact p.Prime] {i0 : Fin (r + 2)}
    (T : (Fin (r + 2) → Multiplicative (ZMod p)) →* (Fin (r + 1) → Multiplicative (ZMod p)))
    (hker : ∀ x, T x = 1 → ∀ j, j ≠ i0 → x j = 1)
    (a b : Fin (r + 2)) (ha : a ≠ i0) (hb : b ≠ i0) (hab : a ≠ b) :
    ∀ c d : ZMod p,
      (fun k : Fin (r + 1) =>
        c * Multiplicative.toAdd (T (Pi.mulSingle a (Multiplicative.ofAdd (1 : ZMod p))) k) +
        d * Multiplicative.toAdd (T (Pi.mulSingle b (Multiplicative.ofAdd (1 : ZMod p))) k)) = 0 →
      c = 0 ∧ d = 0 := by
  intro c d h
  let x : Fin (r + 2) → Multiplicative (ZMod p) :=
    Pi.mulSingle a (Multiplicative.ofAdd c) * Pi.mulSingle b (Multiplicative.ofAdd d)
  have hx_a : x a = Multiplicative.ofAdd c := by
    simp [x, Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne hab]
  have hx_b : x b = Multiplicative.ofAdd d := by
    simp [x, Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne (Ne.symm hab)]
  have hx_eq : x = (Pi.mulSingle a (Multiplicative.ofAdd (1 : ZMod p))) ^ c.val *
      (Pi.mulSingle b (Multiplicative.ofAdd (1 : ZMod p))) ^ d.val := by
    dsimp [x]
    rw [SpCoord.mulSingle_ofAdd_eq_pow a c, SpCoord.mulSingle_ofAdd_eq_pow b d]
  have hT : T x = 1 := by
    funext k
    have hk := congrFun h k
    have hTx : Multiplicative.toAdd (T x k) =
        c * Multiplicative.toAdd (T (Pi.mulSingle a (Multiplicative.ofAdd (1 : ZMod p))) k) +
        d * Multiplicative.toAdd (T (Pi.mulSingle b (Multiplicative.ofAdd (1 : ZMod p))) k) := by
      rw [hx_eq, map_mul, SpCoord.toAdd_mul_apply, map_pow, map_pow,
        SpCoord.toAdd_pow_apply, SpCoord.toAdd_pow_apply,
        ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
    apply Multiplicative.toAdd.injective
    rw [hTx, hk]
    simp [toAdd_one]
  have hxa := hker x hT a ha
  have hxb := hker x hT b hb
  rw [hx_a] at hxa
  rw [hx_b] at hxb
  have hc : c = 0 := by
    have := congrArg Multiplicative.toAdd hxa
    rwa [toAdd_ofAdd, toAdd_one] at this
  have hd : d = 0 := by
    have := congrArg Multiplicative.toAdd hxb
    rwa [toAdd_ofAdd, toAdd_one] at this
  exact ⟨hc, hd⟩

private theorem alignRoot_of_generator {p r : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {i0 : Fin (r + 2)}
    (T : (Fin (r + 2) → Multiplicative (ZMod p)) →* (Fin (r + 1) → Multiplicative (ZMod p)))
    (hTs : Function.Surjective T)
    (hW : ∀ w ∈ bCoordinateBlock (r + 2) p i0, ∃ (π : Equiv.Perm (Fin (r + 1)))
      (ε : Fin (r + 1) → ZMod p), (∀ i, ε i = 1 ∨ ε i = -1) ∧
      ∀ x i, Multiplicative.toAdd (T (w x) (π i)) = ε i * Multiplicative.toAdd (T x i))
    (w : MulAut (Fin (r + 2) → Multiplicative (ZMod p)))
    (hw : w ∈ bCoordinateBlock (r + 2) p i0)
    (u : Fin (r + 1) → ZMod p) (hu : u ≠ 0)
    (s : (Fin (r + 2) → Multiplicative (ZMod p)) → ZMod p)
    (hs : ∀ x, (fun k => Multiplicative.toAdd (T (w x) k)) -
      (fun k => Multiplicative.toAdd (T x k)) = s x • u)
    (hne : ∃ x₀, s x₀ ≠ 0) :
    AlignRoot u := by
  obtain ⟨π, ε, hε, hWπ⟩ := hW w hw
  refine alignRoot_of_signedPerm hp2 π ε hε u ?_ ?_
  · intro y
    obtain ⟨x, hx⟩ := hTs (fun k => Multiplicative.ofAdd (y k))
    refine ⟨s x, ?_⟩
    have h1 : (fun k => ε (π.symm k) * y (π.symm k)) =
        fun k => Multiplicative.toAdd (T (w x) k) := by
      funext k
      have h2 := hWπ x (π.symm k)
      rw [Equiv.apply_symm_apply] at h2
      rw [h2, congrFun hx (π.symm k)]
      simp
    have h2 : (fun k => Multiplicative.toAdd (T x k)) = y := by
      funext k
      rw [congrFun hx k]
      simp
    rw [h1, ← h2]
    exact hs x
  · obtain ⟨x₀, hx₀⟩ := hne
    refine ⟨fun k => Multiplicative.toAdd (T x₀ k), ?_⟩
    intro h
    have h1 : (fun k => ε (π.symm k) * Multiplicative.toAdd (T x₀ (π.symm k))) =
        fun k => Multiplicative.toAdd (T (w x₀) k) := by
      funext k
      have h2 := hWπ x₀ (π.symm k)
      rw [Equiv.apply_symm_apply] at h2
      rw [h2]
    have h2 : (fun k => Multiplicative.toAdd (T (w x₀) k)) -
        (fun k => Multiplicative.toAdd (T x₀ k)) = 0 := by
      rw [← h1, h, sub_self]
    rw [hs x₀] at h2
    exact smul_ne_zero hx₀ hu h2

private theorem toAdd_diff_sgnAut {p r : ℕ} [Fact p.Prime]
    (T : (Fin (r + 2) → Multiplicative (ZMod p)) →* (Fin (r + 1) → Multiplicative (ZMod p)))
    (j : Fin (r + 2)) (x : Fin (r + 2) → Multiplicative (ZMod p)) :
    (fun k : Fin (r + 1) => Multiplicative.toAdd (T (SpCoord.sgnAut j x) k)) -
      (fun k => Multiplicative.toAdd (T x k)) =
    (-2 * Multiplicative.toAdd (x j)) •
      (fun k => toAdd (T (Pi.mulSingle j (ofAdd (1 : ZMod p))) k)) := by
  funext k
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [toAdd_T_sum T (SpCoord.sgnAut j x) k, toAdd_T_sum T x k]
  have hsum : ∑ i : Fin (r + 2),
      (Multiplicative.toAdd ((SpCoord.sgnAut j) x i) *
          Multiplicative.toAdd (T (Pi.mulSingle i (Multiplicative.ofAdd (1 : ZMod p))) k) -
        Multiplicative.toAdd (x i) *
          Multiplicative.toAdd (T (Pi.mulSingle i (Multiplicative.ofAdd (1 : ZMod p))) k)) =
      (∑ i : Fin (r + 2), Multiplicative.toAdd ((SpCoord.sgnAut j) x i) *
          Multiplicative.toAdd (T (Pi.mulSingle i (Multiplicative.ofAdd (1 : ZMod p))) k)) -
        (∑ i : Fin (r + 2), Multiplicative.toAdd (x i) *
          Multiplicative.toAdd (T (Pi.mulSingle i (Multiplicative.ofAdd (1 : ZMod p))) k)) :=
    Finset.sum_sub_distrib _ _
  rw [← hsum]
  rw [Finset.sum_eq_single j]
  · rw [SpCoord.sgnAut_apply, Function.update_self, toAdd_inv]
    ring
  · intro i _ hi
    rw [SpCoord.sgnAut_apply, Function.update_of_ne hi, sub_self]
  · intro h
    exact absurd (Finset.mem_univ j) h

private theorem toAdd_diff_permAut_swap {p r : ℕ} [Fact p.Prime]
    (T : (Fin (r + 2) → Multiplicative (ZMod p)) →* (Fin (r + 1) → Multiplicative (ZMod p)))
    (a b : Fin (r + 2)) (hab : a ≠ b) (x : Fin (r + 2) → Multiplicative (ZMod p)) :
    (fun k : Fin (r + 1) => Multiplicative.toAdd (T (SpCoord.permAut (Equiv.swap a b) x) k)) -
      (fun k => Multiplicative.toAdd (T x k)) =
    (-(Multiplicative.toAdd (x a) - Multiplicative.toAdd (x b))) •
      ((fun k => toAdd (T (Pi.mulSingle a (ofAdd (1 : ZMod p))) k)) -
        (fun k => toAdd (T (Pi.mulSingle b (ofAdd (1 : ZMod p))) k))) := by
  funext k
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [toAdd_T_sum T (SpCoord.permAut (Equiv.swap a b) x) k, toAdd_T_sum T x k]
  have hsum : ∑ i : Fin (r + 2),
      (Multiplicative.toAdd ((SpCoord.permAut (Equiv.swap a b)) x i) *
          Multiplicative.toAdd (T (Pi.mulSingle i (Multiplicative.ofAdd (1 : ZMod p))) k) -
        Multiplicative.toAdd (x i) *
          Multiplicative.toAdd (T (Pi.mulSingle i (Multiplicative.ofAdd (1 : ZMod p))) k)) =
      (∑ i : Fin (r + 2), Multiplicative.toAdd ((SpCoord.permAut (Equiv.swap a b)) x i) *
          Multiplicative.toAdd (T (Pi.mulSingle i (Multiplicative.ofAdd (1 : ZMod p))) k)) -
        (∑ i : Fin (r + 2), Multiplicative.toAdd (x i) *
          Multiplicative.toAdd (T (Pi.mulSingle i (Multiplicative.ofAdd (1 : ZMod p))) k)) :=
    Finset.sum_sub_distrib _ _
  rw [← hsum]
  rw [Finset.sum_eq_add a b hab]
  · rw [SpCoord.permAut_apply, Function.comp_apply, Equiv.swap_inv, Equiv.swap_apply_left,
      Function.comp_apply, Equiv.swap_apply_right]
    ring
  · intro c _ hc
    rw [SpCoord.permAut_apply, Function.comp_apply, Equiv.swap_inv,
      Equiv.swap_apply_of_ne_of_ne hc.1 hc.2, sub_self]
  · intro h
    exact absurd (Finset.mem_univ a) h
  · intro h
    exact absurd (Finset.mem_univ b) h

private theorem sgnAut_permAut_swap_sgnAut_apply {p n : ℕ} {a b : Fin n} (hab : a ≠ b)
    (x : Fin n → Multiplicative (ZMod p)) :
    SpCoord.sgnAut a (SpCoord.permAut (Equiv.swap a b) (SpCoord.sgnAut a x)) a = (x b)⁻¹ ∧
      SpCoord.sgnAut a (SpCoord.permAut (Equiv.swap a b) (SpCoord.sgnAut a x)) b = (x a)⁻¹ ∧
      ∀ c, c ≠ a → c ≠ b →
        SpCoord.sgnAut a (SpCoord.permAut (Equiv.swap a b) (SpCoord.sgnAut a x)) c = x c := by
  refine ⟨?_, ?_, fun c hca hcb => ?_⟩
  · simp only [SpCoord.sgnAut_apply, SpCoord.permAut_apply, Function.comp_apply, Equiv.swap_inv,
      Function.update_self, Equiv.swap_apply_left, Function.update_of_ne (Ne.symm hab)]
  · simp only [SpCoord.sgnAut_apply, SpCoord.permAut_apply, Function.comp_apply, Equiv.swap_inv,
      Function.update_self, Equiv.swap_apply_right, Function.update_of_ne (Ne.symm hab)]
  · simp only [SpCoord.sgnAut_apply, SpCoord.permAut_apply, Function.comp_apply, Equiv.swap_inv,
      Function.update_of_ne hca, Equiv.swap_apply_of_ne_of_ne hca hcb]

private theorem toAdd_diff_negSwap {p r : ℕ} [Fact p.Prime]
    (T : (Fin (r + 2) → Multiplicative (ZMod p)) →* (Fin (r + 1) → Multiplicative (ZMod p)))
    (a b : Fin (r + 2)) (hab : a ≠ b) (x y : Fin (r + 2) → Multiplicative (ZMod p))
    (hya : y a = (x b)⁻¹) (hyb : y b = (x a)⁻¹) (hyc : ∀ c, c ≠ a → c ≠ b → y c = x c) :
    (fun k : Fin (r + 1) => toAdd (T y k)) - (fun k => toAdd (T x k)) =
    (-(toAdd (x a) + toAdd (x b))) •
      ((fun k => toAdd (T (Pi.mulSingle a (ofAdd (1 : ZMod p))) k)) +
        (fun k => toAdd (T (Pi.mulSingle b (ofAdd (1 : ZMod p))) k))) := by
  funext k
  simp only [Pi.sub_apply, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
  rw [toAdd_T_sum T y k, toAdd_T_sum T x k]
  have hsum : ∑ i : Fin (r + 2),
      (toAdd (y i) * toAdd (T (Pi.mulSingle i (ofAdd (1 : ZMod p))) k) -
        toAdd (x i) * toAdd (T (Pi.mulSingle i (ofAdd (1 : ZMod p))) k)) =
      (∑ i : Fin (r + 2), toAdd (y i) * toAdd (T (Pi.mulSingle i (ofAdd (1 : ZMod p))) k)) -
        (∑ i : Fin (r + 2), toAdd (x i) * toAdd (T (Pi.mulSingle i (ofAdd (1 : ZMod p))) k)) :=
    Finset.sum_sub_distrib _ _
  rw [← hsum, Finset.sum_eq_add a b hab]
  · rw [hya, hyb, toAdd_inv, toAdd_inv]
    ring
  · intro c _ hc
    rw [hyc c hc.1 hc.2, sub_self]
  · intro h
    exact absurd (Finset.mem_univ a) h
  · intro h
    exact absurd (Finset.mem_univ b) h

private theorem exists_align_aux {p r : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hr : 2 ≤ r)
    {i0 : Fin (r + 2)}
    (T : (Fin (r + 2) → Multiplicative (ZMod p)) →* (Fin (r + 1) → Multiplicative (ZMod p)))
    (hTs : Function.Surjective T) (hker : ∀ x, T x = 1 → ∀ j, j ≠ i0 → x j = 1)
    (hW : ∀ w ∈ bCoordinateBlock (r + 2) p i0, ∃ (π : Equiv.Perm (Fin (r + 1)))
      (ε : Fin (r + 1) → ZMod p), (∀ i, ε i = 1 ∨ ε i = -1) ∧
      ∀ x i, toAdd (T (w x) (π i)) = ε i * toAdd (T x i)) :
    ∃ π' : Fin (r + 2) ≃ Fin (r + 2), π' 0 = i0 ∧ ∃ c : ZMod p, c ≠ 0 ∧
      ∃ ε : Fin (r + 1) → ZMod p, (∀ k, ε k = 1 ∨ ε k = -1) ∧
        ∀ x k, toAdd (T x k) = ε k * c * toAdd (x (π' k.succ)) := by
  have h2 : (2 : ZMod p) ≠ 0 := SpCoord.coord_two_ne_zero Fact.out hp2
  let v : Fin (r + 2) → Fin (r + 1) → ZMod p := fun j l =>
    toAdd (T (Pi.mulSingle j (ofAdd (1 : ZMod p))) l)
  have hsg : ∀ j, j ≠ i0 → SpCoord.sgnAut j ∈ bCoordinateBlock (r + 2) p i0 := fun j hj =>
    Subgroup.subset_closure (Or.inl ⟨j, hj, rfl⟩)
  have hsw : ∀ a b, a ≠ b → a ≠ i0 → b ≠ i0 →
      SpCoord.permAut (Equiv.swap a b) ∈ bCoordinateBlock (r + 2) p i0 :=
    fun a b hab ha hb => Subgroup.subset_closure (Or.inr ⟨a, b, hab, ha, hb, rfl⟩)
  have hroot : ∀ j, j ≠ i0 → AlignRoot (v j) := by
    intro j hj
    refine alignRoot_of_generator hp2 T hTs hW _ (hsg j hj) (v j) (v_j_ne_zero T hker j hj)
      (fun x => -2 * toAdd (x j)) (toAdd_diff_sgnAut T j) ⟨Pi.mulSingle j (ofAdd 1), ?_⟩
    simp only [Pi.mulSingle_eq_same, toAdd_ofAdd, mul_one]
    exact neg_ne_zero.2 h2
  have hdiff : ∀ a b, a ≠ b → a ≠ i0 → b ≠ i0 → AlignRoot (v a - v b) := by
    intro a b hab ha hb
    refine alignRoot_of_generator hp2 T hTs hW _ (hsw a b hab ha hb) (v a - v b) ?_
      (fun x => -(toAdd (x a) - toAdd (x b))) (toAdd_diff_permAut_swap T a b hab)
      ⟨Pi.mulSingle a (ofAdd 1), ?_⟩
    · intro h
      refine one_ne_zero (v_pair_linearIndependent T hker a b ha hb hab 1 (-1) ?_).1
      funext l
      have hl := congrFun h l
      simp only [Pi.sub_apply, Pi.zero_apply] at hl
      simp only [one_mul, neg_one_mul, Pi.zero_apply, ← sub_eq_add_neg]
      exact hl
    · simp only [Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne (Ne.symm hab), toAdd_ofAdd,
        toAdd_one, sub_zero]
      exact neg_ne_zero.2 one_ne_zero
  have hsum : ∀ a b, a ≠ b → a ≠ i0 → b ≠ i0 → AlignRoot (v a + v b) := by
    intro a b hab ha hb
    have hmem : (SpCoord.sgnAut a * SpCoord.permAut (Equiv.swap a b) * SpCoord.sgnAut a :
        MulAut (Fin (r + 2) → Multiplicative (ZMod p))) ∈ bCoordinateBlock (r + 2) p i0 :=
      mul_mem (mul_mem (hsg a ha) (hsw a b hab ha hb)) (hsg a ha)
    refine alignRoot_of_generator hp2 T hTs hW _ hmem (v a + v b) ?_
      (fun x => -(toAdd (x a) + toAdd (x b)))
      (fun x => toAdd_diff_negSwap T a b hab x
        (SpCoord.sgnAut a (SpCoord.permAut (Equiv.swap a b) (SpCoord.sgnAut a x)))
        (sgnAut_permAut_swap_sgnAut_apply hab x).1 (sgnAut_permAut_swap_sgnAut_apply hab x).2.1
        (sgnAut_permAut_swap_sgnAut_apply hab x).2.2)
      ⟨Pi.mulSingle a (ofAdd 1), ?_⟩
    · intro h
      refine one_ne_zero (v_pair_linearIndependent T hker a b ha hb hab 1 1 ?_).1
      funext l
      have hl := congrFun h l
      simp only [Pi.add_apply, Pi.zero_apply] at hl
      simp only [one_mul, Pi.zero_apply]
      exact hl
    · simp only [Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne (Ne.symm hab), toAdd_ofAdd,
        toAdd_one, add_zero]
      exact neg_ne_zero.2 one_ne_zero
  have hspan : ∀ m : Fin (r + 1), ∃ a : Fin (r + 1), v (i0.succAbove a) m ≠ 0 := by
    intro m
    by_contra hcon
    simp only [not_exists, ne_eq, not_not] at hcon
    obtain ⟨x, hx⟩ := hTs (Pi.mulSingle m (ofAdd (1 : ZMod p)))
    have h1 := toAdd_T_sum T x m
    rw [hx, Pi.mulSingle_eq_same, toAdd_ofAdd] at h1
    refine one_ne_zero (h1.trans (Finset.sum_eq_zero fun j _ => ?_))
    rcases Fin.eq_self_or_eq_succAbove i0 j with hj | ⟨a, hja⟩
    · rw [hj, ker_eq_axis T hTs hker, Pi.one_apply, toAdd_one, mul_zero]
    · rw [hja, show toAdd (T (Pi.mulSingle (i0.succAbove a) (ofAdd (1 : ZMod p))) m) = 0 from
        hcon a, mul_zero]
  have hshort := alignShort_of_roots hp2 (by omega : 3 ≤ r + 1) (fun a => v (i0.succAbove a))
    (fun a => hroot _ (Fin.succAbove_ne i0 a))
    (fun a b hab => hsum _ _ (Fin.succAbove_right_injective.ne hab) (Fin.succAbove_ne i0 a)
      (Fin.succAbove_ne i0 b))
    (fun a b hab => hdiff _ _ (Fin.succAbove_right_injective.ne hab) (Fin.succAbove_ne i0 a)
      (Fin.succAbove_ne i0 b))
    hspan
  choose κ γ hγ hvκ using hshort
  have hκs : Function.Surjective κ := by
    intro m
    obtain ⟨a, ha⟩ := hspan m
    refine ⟨a, ?_⟩
    by_contra hne
    apply ha
    have h := congrFun (hvκ a) m
    rw [Pi.single_eq_of_ne' hne] at h
    exact h
  obtain ⟨hκb, hγpm⟩ := alignMonomial_of_short κ γ hγ hκs fun a b hab => by
    have h := hdiff _ _ (Fin.succAbove_right_injective.ne hab) (Fin.succAbove_ne i0 a)
      (Fin.succAbove_ne i0 b)
    rw [show v (i0.succAbove a) = Pi.single (κ a) (γ a) from hvκ a,
      show v (i0.succAbove b) = Pi.single (κ b) (γ b) from hvκ b] at h
    exact h
  obtain ⟨κe, hκe⟩ : ∃ κe : Fin (r + 1) ≃ Fin (r + 1), ∀ a, κe a = κ a :=
    ⟨Equiv.ofBijective κ hκb, fun _ => rfl⟩
  obtain ⟨π', hπ0, hπs⟩ : ∃ π' : Fin (r + 2) ≃ Fin (r + 2), π' 0 = i0 ∧
      ∀ k : Fin (r + 1), π' k.succ = i0.succAbove (κe.symm k) :=
    ⟨(finSuccEquiv (r + 1)).trans ((Equiv.optionCongr κe.symm).trans (finSuccEquiv' i0).symm),
      by
        rw [Equiv.trans_apply, Equiv.trans_apply, finSuccEquiv_zero, Equiv.optionCongr_apply]
        exact finSuccEquiv'_symm_none i0,
      fun k => by
        rw [Equiv.trans_apply, Equiv.trans_apply, finSuccEquiv_succ, Equiv.optionCongr_apply]
        exact finSuccEquiv'_symm_some i0 (κe.symm k)⟩
  have hcol : ∀ k, toAdd (T (Pi.mulSingle (i0.succAbove (κe.symm k)) (ofAdd (1 : ZMod p))) k) =
      γ (κe.symm k) := by
    intro k
    have h := congrFun (hvκ (κe.symm k)) k
    rw [show κ (κe.symm k) = k from (hκe _).symm.trans (κe.apply_symm_apply k),
      Pi.single_eq_same] at h
    exact h
  have hcoef : ∀ k, γ (κe.symm k) = (if γ (κe.symm k) = γ 0 then 1 else -1) * γ 0 := by
    intro k
    by_cases h : γ (κe.symm k) = γ 0
    · rw [if_pos h, one_mul]
      exact h
    · rw [if_neg h, neg_one_mul]
      exact (hγpm 0 (κe.symm k)).resolve_left h
  refine ⟨π', hπ0, γ 0, hγ 0, fun k => if γ (κe.symm k) = γ 0 then 1 else -1, fun k => ?_,
    fun x k => ?_⟩
  · by_cases h : γ (κe.symm k) = γ 0
    · exact Or.inl (if_pos h)
    · exact Or.inr (if_neg h)
  · show toAdd (T x k) = (if γ (κe.symm k) = γ 0 then 1 else -1) * γ 0 * toAdd (x (π' k.succ))
    rw [← hcoef k, toAdd_T_sum T x k, Finset.sum_eq_single (π' k.succ)]
    · rw [hπs k, hcol k, mul_comm]
    · intro j _ hj
      rcases Fin.eq_self_or_eq_succAbove i0 j with hj0 | ⟨m, hjm⟩
      · rw [hj0, ker_eq_axis T hTs hker, Pi.one_apply, toAdd_one, mul_zero]
      · have hmk : κ m ≠ k := by
          intro hmk
          apply hj
          rw [hjm, hπs k, ← hmk, ← hκe m, Equiv.symm_apply_apply]
        have h1 : toAdd (T (Pi.mulSingle (i0.succAbove m) (ofAdd (1 : ZMod p))) k) = 0 := by
          have h := congrFun (hvκ m) k
          rw [Pi.single_eq_of_ne' hmk] at h
          exact h
        rw [hjm, h1, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ _) h

end AssemblyHelpers

theorem ggSecFiveBPermSpK_exists_align {p r : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hr : 2 ≤ r)
    {i0 : Fin (r + 2)}
    (T : (Fin (r + 2) → Multiplicative (ZMod p)) →* (Fin (r + 1) → Multiplicative (ZMod p)))
    (hTs : Function.Surjective T) (hker : ∀ x, T x = 1 → ∀ j, j ≠ i0 → x j = 1)
    (hW : ∀ w ∈ bCoordinateBlock (r + 2) p i0, ∃ (π : Equiv.Perm (Fin (r + 1)))
      (ε : Fin (r + 1) → ZMod p), (∀ i, ε i = 1 ∨ ε i = -1) ∧
      ∀ x i, Multiplicative.toAdd (T (w x) (π i)) = ε i * Multiplicative.toAdd (T x i)) :
    ∃ π' : Fin (r + 2) ≃ Fin (r + 2), π' 0 = i0 ∧ ∃ c : ZMod p, c ≠ 0 ∧
      ∃ ε : Fin (r + 1) → ZMod p, (∀ k, ε k = 1 ∨ ε k = -1) ∧
        ∀ x k, Multiplicative.toAdd (T x k) =
          ε k * c * Multiplicative.toAdd (x (π' k.succ)) := by
  exact exists_align_aux hp2 hr T hTs hker hW

end CFSG.StandardType

end
