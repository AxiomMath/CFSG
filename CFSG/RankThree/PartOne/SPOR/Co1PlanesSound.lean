module

public import CFSG.RankThree.PartOne.SPOR.PlanesGeneric
public import CFSG.RankThree.PartOne.SPOR.Co1PlanesData
import CFSG.Sporadic.Co1.Module.InvSpec

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

public section

namespace CFSG.RankThree.PartOne.SPOR

open CFSG.Sporadic.Co1Schreier CFSG.Sporadic.Co1.InvNative Subgroup

section Rows

theorem validRows_one' :
    validRows CFSG.Sporadic.Co1Schreier.Native.one = true := by
  show validRows (CFSG.Sporadic.SmallF2.Native.idRows 24) = true
  simp only [validRows, Bool.and_eq_true, beq_iff_eq,
    Array.all_eq_true, decide_eq_true_eq]
  refine ⟨by simp [CFSG.Sporadic.SmallF2.Native.idRows], fun i hi => ?_⟩
  simp only [CFSG.Sporadic.SmallF2.Native.idRows, Array.getElem_ofFn]
  rw [Nat.one_shiftLeft]
  have : (i : ℕ) < 24 := by simpa [CFSG.Sporadic.SmallF2.Native.idRows] using hi
  calc 2 ^ i < 2 ^ 24 := Nat.pow_lt_pow_right (by norm_num) this
    _ = 16777216 := by norm_num

theorem ne_one_of_rows {X : Native.Rows} {g : GL24} (hX : MRep X g) (hv : validRows X = true)
    (hne : X ≠ Native.one) : g ≠ 1 := by
  intro h
  rw [h] at hX
  exact hne (CFSG.Sporadic.Co1.Module.rowsMatrix_injective_of_valid hv validRows_one'
    (hX.trans MRep.one.symm))

theorem ne_of_rows {X Y : Native.Rows} {g h : GL24} (hX : MRep X g) (hY : MRep Y h)
    (hvX : validRows X = true) (hvY : validRows Y = true) (hne : X ≠ Y) : g ≠ h := by
  intro e
  rw [e] at hX
  exact hne (CFSG.Sporadic.Co1.Module.rowsMatrix_injective_of_valid hvX hvY (hX.trans hY.symm))

theorem rep_comm {X Y : Native.Rows} {g h : GL24} (hX : MRep X g) (hY : MRep Y h)
    (e : Native.mul X Y = Native.mul Y X) : g * h = h * g :=
  (hX.mul hY).eq (e ▸ hY.mul hX)

end Rows

section Sound

variable {A : Type} [Group A] (ι : A →* GL24) {R : List Native.Rows} {gs : List GL24}

theorem exists_of_getD (hsurj : ∀ g ∈ gs, ∃ a : A, ι a = g) (k : ℕ) :
    ∃ a : A, ι a = gs.getD k 1 := by
  rw [List.getD_eq_getElem?_getD]
  cases hk : gs[k]? with
  | none => exact ⟨1, map_one ι⟩
  | some g => exact hsurj g (List.mem_of_getElem? hk)

noncomputable def eltA (hsurj : ∀ g ∈ gs, ∃ a : A, ι a = g) (k : ℕ) : A :=
  Classical.choose (exists_of_getD ι hsurj (k - 1))

theorem eltA_spec (hsurj : ∀ g ∈ gs, ∃ a : A, ι a = g) (k : ℕ) :
    ι (eltA ι hsurj k) = gs.getD (k - 1) 1 :=
  Classical.choose_spec (exists_of_getD ι hsurj (k - 1))

theorem rep_eltA (hR : List.Forall₂ MRep R gs) (hsurj : ∀ g ∈ gs, ∃ a : A, ι a = g) (k : ℕ) :
    MRep (R.getD (k - 1) Native.one) (ι (eltA ι hsurj k)) := by
  rw [eltA_spec]
  exact getD_rep hR MRep.one (k - 1)

theorem rep_conjProd (hR : List.Forall₂ MRep R gs) (hsurj : ∀ g ∈ gs, ∃ a : A, ι a = g)
    {tR : Native.Rows} {tA : A} (ht : MRep tR (ι tA)) :
    ∀ ws : List ℕ, (∀ k ∈ ws, Native.mul (R.getD (k - 1) Native.one)
        (Native.inv (R.getD (k - 1) Native.one)) = Native.one) →
      MRep (co1ConjProd R tR ws)
        (ι ((ws.map fun k => eltA ι hsurj k * tA * (eltA ι hsurj k)⁻¹).prod))
  | [], _ => by simpa [co1ConjProd] using MRep.one
  | k :: ws, hws => by
    have hk := hws k (by simp)
    have h1 := rep_eltA ι hR hsurj k
    have h2 := h1.inv hk
    have ih := rep_conjProd hR hsurj ht ws (fun j hj => hws j (by simp [hj]))
    simp only [co1ConjProd, List.foldr_cons, List.map_cons, List.prod_cons, map_mul, map_inv]
    exact ((h1.mul ht).mul h2).mul ih

theorem co1LineOK_sound (hR : List.Forall₂ MRep R gs) (hsurj : ∀ g ∈ gs, ∃ a : A, ι a = g)
    {tR : Native.Rows} {tA : A} (ht : MRep tR (ι tA)) (hι : Function.Injective ι) {p : ℕ}
    (hp : p.Prime) {x : Native.Rows} {gx : A} (hx : MRep x (ι gx)) {ws : List ℕ} {e : ℕ}
    (h : co1LineOK R tR p x ws e = true) :
    ∃ l : List A, (∀ g ∈ l, g * gx = gx * g) ∧
      p ∣ orderOf ((l.map fun g => g * tA * g⁻¹).prod) := by
  simp only [co1LineOK, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, beq_iff_eq,
    bne_iff_ne, ne_eq] at h
  obtain ⟨⟨⟨hws, hv⟩, hne⟩, hpe⟩ := h
  have hinv : ∀ k ∈ ws, Native.mul (R.getD (k - 1) Native.one)
      (Native.inv (R.getD (k - 1) Native.one)) = Native.one := fun k hk => (hws k hk).1.2
  have : Fact p.Prime := ⟨hp⟩
  refine ⟨ws.map (eltA ι hsurj), ?_, ?_⟩
  · intro g hg
    obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hg
    apply hι
    rw [map_mul, map_mul]
    exact rep_comm (rep_eltA ι hR hsurj k) hx (hws k hk).2
  · set z : A := (ws.map fun k => eltA ι hsurj k * tA * (eltA ι hsurj k)⁻¹).prod with hz
    have hrep := rep_conjProd ι hR hsurj ht ws hinv
    have hmap : (ws.map (eltA ι hsurj)).map (fun g => g * tA * g⁻¹) =
        ws.map fun k => eltA ι hsurj k * tA * (eltA ι hsurj k)⁻¹ := by
      rw [List.map_map]; rfl
    rw [hmap]
    have hpow := hrep.pow e
    have hne' : (ι z) ^ e ≠ 1 := ne_one_of_rows hpow hv hne
    have hpp : ((ι z) ^ e) ^ p = 1 := by
      have := (hpow.pow p)
      rw [hpe] at this
      exact this.eq MRep.one
    have hord : orderOf ((ι z) ^ e) = p := orderOf_eq_prime hpp hne'
    have hdvd : orderOf (ι z ^ e) ∣ orderOf z := by
      rw [← map_pow]
      exact (orderOf_injective ι hι (z ^ e)).symm ▸ orderOf_pow_dvd e
    rw [← hord]
    exact hdvd

theorem co1Block1_cover [Finite A] (hR : List.Forall₂ MRep R gs)
    (hsurj : ∀ g ∈ gs, ∃ a : A, ι a = g) {tR : Native.Rows} {tA : A} (ht : MRep tR (ι tA))
    (hι : Function.Injective ι) (hc : ∀ a : A, (∀ b : A, a * b = b * a) → a = 1)
    {b : Co1PlaneBlock1} (hp : b.p.Prime) (hb : co1Block1OK R tR b = true) {N m : ℕ}
    (hN : Nat.card (Subgroup.centralizer ({tA} : Set A)) = N) (hNm : N = b.p ^ 1 * m)
    (hm : ¬ b.p ∣ m) :
    ∀ y : A, y * tA = tA * y → orderOf y = b.p →
      ∃ l : List A, (∀ g ∈ l, g * y = y * g) ∧
        b.p ∣ orderOf ((l.map fun g => g * tA * g⁻¹).prod) := by
  simp only [co1Block1OK, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, bne_iff_ne,
    ne_eq] at hb
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, hv⟩, hcomm⟩, hpow⟩, hne⟩, hline⟩ := hb
  have : Fact b.p.Prime := ⟨hp⟩
  have hY := rep_eltA ι hR hsurj b.y
  have hcom : eltA ι hsurj b.y * tA = tA * eltA ι hsurj b.y := by
    apply hι
    rw [map_mul, map_mul]
    exact rep_comm hY ht hcomm
  have hord : orderOf (eltA ι hsurj b.y) = b.p := by
    have hp1 : (ι (eltA ι hsurj b.y)) ^ b.p = 1 := by
      have := hY.pow b.p
      rw [hpow] at this
      exact this.eq MRep.one
    have hne' : ι (eltA ι hsurj b.y) ≠ 1 := ne_one_of_rows hY hv hne
    exact orderOf_eq_prime (hι (by rw [map_pow, map_one]; exact hp1))
      (fun h => hne' (by rw [h, map_one]))
  exact cover_of_line_inner hp hc tA hN hNm hm hcom hord
    (co1LineOK_sound ι hR hsurj ht hι hp hY hline)

theorem co1Block2_cover [Finite A] (hR : List.Forall₂ MRep R gs)
    (hsurj : ∀ g ∈ gs, ∃ a : A, ι a = g) {tR : Native.Rows} {tA : A} (ht : MRep tR (ι tA))
    (hι : Function.Injective ι) (hc : ∀ a : A, (∀ b : A, a * b = b * a) → a = 1)
    {b : Co1PlaneBlock2} (hp : b.p.Prime) (hb : co1Block2OK R tR b = true) {N m : ℕ}
    (hN : Nat.card (Subgroup.centralizer ({tA} : Set A)) = N) (hNm : N = b.p ^ 2 * m)
    (hm : ¬ b.p ∣ m) :
    ∀ y : A, y * tA = tA * y → orderOf y = b.p →
      ∃ l : List A, (∀ g ∈ l, g * y = y * g) ∧
        b.p ∣ orderOf ((l.map fun g => g * tA * g⁻¹).prod) := by
  simp only [co1Block2OK, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, bne_iff_ne, ne_eq,
    List.all_eq_true, List.mem_range, Bool.or_eq_true] at hb
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, -⟩, hv1⟩, hv2⟩, hc1⟩, hc2⟩, hp1⟩, hp2⟩, hc12⟩, hinj⟩, hlen1⟩,
    hlen2⟩, hl0⟩, hl⟩ := hb
  have : Fact b.p.Prime := ⟨hp⟩
  have hY1 := rep_eltA ι hR hsurj b.y1
  have hY2 := rep_eltA ι hR hsurj b.y2
  set y₁ := eltA ι hsurj b.y1 with hy₁
  set y₂ := eltA ι hsurj b.y2 with hy₂
  have hcm1 : y₁ * tA = tA * y₁ := by
    apply hι
    rw [map_mul, map_mul]
    exact rep_comm hY1 ht hc1
  have hcm2 : y₂ * tA = tA * y₂ := by
    apply hι
    rw [map_mul, map_mul]
    exact rep_comm hY2 ht hc2
  have hcm12 : y₁ * y₂ = y₂ * y₁ := by
    apply hι
    rw [map_mul, map_mul]
    exact rep_comm hY1 hY2 hc12
  have hpw1 : y₁ ^ b.p = 1 := by
    apply hι
    rw [map_pow, map_one]
    have := hY1.pow b.p
    rw [hp1] at this
    exact this.eq MRep.one
  have hpw2 : y₂ ^ b.p = 1 := by
    apply hι
    rw [map_pow, map_one]
    have := hY2.pow b.p
    rw [hp2] at this
    exact this.eq MRep.one
  have hind : ∀ a c a' c' : ℕ, a < b.p → c < b.p → a' < b.p → c' < b.p →
      y₁ ^ a * y₂ ^ c = y₁ ^ a' * y₂ ^ c' → a = a' ∧ c = c' := by
    intro a c a' c' ha hc' ha' hc'' heq
    rcases hinj a ha c hc' a' ha' c' hc'' with h | ⟨⟨hva, hvb⟩, hne⟩
    · exact h
    · exfalso
      have hX := (hY1.pow a).mul (hY2.pow c)
      have hX' := (hY1.pow a').mul (hY2.pow c')
      have := ne_of_rows hX hX' hva hvb hne
      apply this
      rw [← map_pow, ← map_pow, ← map_pow, ← map_pow, ← map_mul, ← map_mul, heq]
  have hline0 := co1LineOK_sound ι hR hsurj ht hι hp hY2 hl0
  have hlinec : ∀ c : ℕ, c < b.p → ∃ l : List A,
      (∀ g ∈ l, g * (y₁ * y₂ ^ c) = (y₁ * y₂ ^ c) * g) ∧
        b.p ∣ orderOf ((l.map fun g => g * tA * g⁻¹).prod) := fun c hc'' => by
    have hx : MRep (Native.mul (R.getD (b.y1 - 1) Native.one)
        (Native.pow (R.getD (b.y2 - 1) Native.one) c)) (ι (y₁ * y₂ ^ c)) := by
      rw [map_mul, map_pow]
      exact hY1.mul (hY2.pow c)
    exact co1LineOK_sound ι hR hsurj ht hι hp hx (hl c hc'')
  exact cover_of_plane_inner hp hc tA hN hNm hm hcm1 hcm2 hcm12 hpw1 hpw2 hind hline0 hlinec

theorem getD_dagG_of_lt (derivs : List (List ℤ)) :
    ∀ (baseG : List GL24) {k : ℕ}, k < baseG.length →
      (dagG baseG derivs).getD k 1 = baseG.getD k 1 := by
  induction derivs with
  | nil => intro baseG k _; rfl
  | cons w ws ih =>
    intro baseG k hk
    have h1 : dagG baseG (w :: ws) = dagG (baseG ++ [wordG baseG w]) ws := rfl
    rw [h1, ih (baseG ++ [wordG baseG w]) (by simp; omega)]
    rw [List.getD_append _ _ _ _ hk]

theorem co1Class_cover [Finite A] {baseG : List GL24}
    (hbase : List.Forall₂ MRep co1PlaneBase baseG) (hmem : ∀ g ∈ baseG, ∃ a : A, ι a = g)
    (hι : Function.Injective ι) (hc : ∀ a : A, (∀ b : A, a * b = b * a) → a = 1)
    {c : Co1PlaneClass} (hcl : co1ClassOK c = true) :
    ∃ tA : A, ι tA = baseG.getD (c.t - 1) 1 ∧
      (∀ b ∈ c.b1, b.p.Prime → ∀ {N m : ℕ},
        Nat.card (Subgroup.centralizer ({tA} : Set A)) = N → N = b.p ^ 1 * m → ¬ b.p ∣ m →
        ∀ y : A, y * tA = tA * y → orderOf y = b.p →
          ∃ l : List A, (∀ g ∈ l, g * y = y * g) ∧
            b.p ∣ orderOf ((l.map fun g => g * tA * g⁻¹).prod)) ∧
      (∀ b ∈ c.b2, b.p.Prime → ∀ {N m : ℕ},
        Nat.card (Subgroup.centralizer ({tA} : Set A)) = N → N = b.p ^ 2 * m → ¬ b.p ∣ m →
        ∀ y : A, y * tA = tA * y → orderOf y = b.p →
          ∃ l : List A, (∀ g ∈ l, g * y = y * g) ∧
            b.p ∣ orderOf ((l.map fun g => g * tA * g⁻¹).prod)) := by
  simp only [co1ClassOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hcl
  obtain ⟨⟨⟨⟨hflag, ht1⟩, ht2⟩, hb1⟩, hb2⟩ := hcl
  have hR := dag_rep hbase c.derivs hflag
  have hsurj : ∀ g ∈ dagG baseG c.derivs, ∃ a : A, ι a = g := fun g hg => by
    have := dagG_mem (H := ι.range) (fun g hg => by
      obtain ⟨a, ha⟩ := hmem g hg
      exact ⟨a, ha⟩) c.derivs g hg
    exact this
  have hlen : co1PlaneBase.length = baseG.length := hbase.length_eq
  have htlt : c.t - 1 < baseG.length := by omega
  refine ⟨eltA ι hsurj c.t, ?_, ?_, ?_⟩
  · rw [eltA_spec, getD_dagG_of_lt _ _ htlt]
  · intro b hb hp N m hN hNm hm
    exact co1Block1_cover ι hR hsurj (rep_eltA ι hR hsurj c.t) hι hc hp (hb1 b hb) hN hNm hm
  · intro b hb hp N m hN hNm hm
    exact co1Block2_cover ι hR hsurj (rep_eltA ι hR hsurj c.t) hι hc hp (hb2 b hb) hN hNm hm

end Sound

end CFSG.RankThree.PartOne.SPOR
