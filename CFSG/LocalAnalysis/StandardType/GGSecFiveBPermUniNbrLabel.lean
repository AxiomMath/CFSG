module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermUniDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBNbrType
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBLabelDefs
public import CFSG.LocalAnalysis.StandardType.GGTBXPlumb
public import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrRowDefs
public import CFSG.LocalAnalysis.StandardType.GGMultTableCl
public import CFSG.LocalAnalysis.StandardType.GGKacK1
public import CFSG.LocalAnalysis.StandardType.GGFieldNbr
public import CFSG.LocalAnalysis.StandardType.GGNbrBalance
public import CFSG.LocalAnalysis.StandardType.GGSecFiveNonWeylKnownDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeakNbr
public import CFSG.LocalAnalysis.StandardType.GGSignedCoordBlocks
import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBLabelCore
import CFSG.LocalAnalysis.StandardType.GGTwE6BadWeyl
import CFSG.LocalAnalysis.StandardType.GGNbrReflGenTwE6Three
import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoAux
import CFSG.LocalAnalysis.StandardType.GGPZNbrResRest
import CFSG.LocalAnalysis.StandardType.GGNSJoinBaseLabel
import CFSG.LocalAnalysis.StandardType.GGK1ScMain
import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBRes
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermSpKCent
import CFSG.LocalAnalysis.StandardType.GGResNonsingularBase
import CFSG.LocalAnalysis.StandardType.GGResNonsingF4Three
import CFSG.LocalAnalysis.StandardType.GGSecFiveRowMemberAux
import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrRowNCells
import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordDExclReal
import CFSG.LocalAnalysis.StandardType.GGNbrLabelJOfTcjK
import CFSG.LocalAnalysis.StandardType.GGNbrHalfSplitArith
import CFSG.LocalAnalysis.StandardType.GGSecFiveNonWeylOfKnown
import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerUnitaryHyperbolic
import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel
import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBSparseLinLabel
import CFSG.LocalAnalysis.StandardType.GGSignedCoordReflGroup

public section

namespace CFSG.StandardType

open CFSG.Assembly

@[expose] def GGSecFiveBPermUniNbrLabel (n f : ℕ) (lab : LargeEvenLabel) : Prop :=
  lab.n = f ∧ (((lab.tag = .B ∨ lab.tag = .C) ∧ lab.rank = n - 1) ∨
    (lab.tag = .D ∧ lab.rank = n ∧ Odd n) ∨ (lab.tag = .twD ∧ lab.rank = n ∧ Even n))


theorem card_bstar_inf_centralizer_le_of_fixedPoints {G : Type} [Group G] {p n : ℕ}
    {Bs X : Subgroup G} [Finite ↥Bs] (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p)))
    {H : Subgroup (MulAut (Fin n → Multiplicative (ZMod p)))}
    (hH : H ≤ (ggAutomizer X Bs).map (MulAut.congr eta).toMonoidHom)
    (hfix : Nat.card {v : Fin n → Multiplicative (ZMod p) // ∀ h ∈ H, h v = v} ≤ p) :
    Nat.card ↥(Bs ⊓ Subgroup.centralizer (X : Set G)) ≤ p := by
  classical
  have _ : Finite (Fin n → Multiplicative (ZMod p)) := Finite.of_equiv ↥Bs eta.toEquiv
  let f : ↥(Bs ⊓ Subgroup.centralizer (X : Set G)) →
      {v : Fin n → Multiplicative (ZMod p) // ∀ h ∈ H, h v = v} :=
    fun z => ⟨eta ⟨z.1, z.2.1⟩, fun h hh => by
      obtain ⟨φ, hφA, hφ⟩ := Subgroup.mem_map.mp (hH hh)
      have hzφ : φ ⟨z.1, z.2.1⟩ = ⟨z.1, z.2.1⟩ := by
        obtain ⟨g, hgX, -, hφg⟩ := mem_ggAutomizer_iff.mp hφA
        apply Subtype.ext
        rw [hφg]
        have hgz : g * z.1 = z.1 * g :=
          Subgroup.mem_centralizer_iff.mp z.2.2 g hgX
        rw [hgz]
        group
      rw [← hφ]
      change (MulAut.congr eta φ) (eta ⟨z.1, z.2.1⟩) = eta ⟨z.1, z.2.1⟩
      rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply,
        MulEquiv.trans_apply]
      exact congrArg eta hzφ⟩
  have hf : Function.Injective f := by
    intro z1 z2 h
    have hv : eta ⟨z1.1, z1.2.1⟩ = eta ⟨z2.1, z2.2.1⟩ := congrArg Subtype.val h
    have hb : (⟨z1.1, z1.2.1⟩ : ↥Bs) = ⟨z2.1, z2.2.1⟩ := eta.injective hv
    exact Subtype.ext (congrArg (Subtype.val : ↥Bs → G) hb)
  exact (Nat.card_le_card_of_injective f hf).trans hfix

theorem card_bstar_inf_center_le_of_fixedPoints {G : Type} [Group G] {p n : ℕ}
    {Bs X : Subgroup G} [Finite ↥Bs] (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p)))
    {H : Subgroup (MulAut (Fin n → Multiplicative (ZMod p)))}
    (hH : H ≤ (ggAutomizer X Bs).map (MulAut.congr eta).toMonoidHom)
    (hfix : Nat.card {v : Fin n → Multiplicative (ZMod p) // ∀ h ∈ H, h v = v} ≤ p) :
    Nat.card ↥(Bs ⊓ X ⊓ Subgroup.centralizer (X : Set G)) ≤ p := by
  haveI : Finite ↥(Bs ⊓ Subgroup.centralizer (X : Set G)) :=
    Finite.of_injective (Subgroup.inclusion inf_le_left) (Subgroup.inclusion_injective _)
  exact (Nat.card_le_card_of_injective
    (Subgroup.inclusion (le_inf (inf_le_left.trans inf_le_left) inf_le_right))
    (Subgroup.inclusion_injective _)).trans
    (card_bstar_inf_centralizer_le_of_fixedPoints eta hH hfix)


theorem ggHalfSplit_not_tbTorCov_cases {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp7 : p ≠ 7)
    {lab : LargeEvenLabel} {c : Prop} (hlab : LargeEvenInLambda2 lab)
    (hS : LargeEvenHalfSplit p lab c) (hnd : ¬ p ∣ 2 ^ lab.n - 1) (hnc : ¬ GGTBTorCov p lab) :
    (p = 3 ∧ ((lab.tag = .A ∧ 6 ≤ lab.rank ∧ lab.n = 1) ∨ (lab.tag = .E6 ∧ lab.n = 1) ∨
      (lab.tag = .F4 ∧ 3 ∣ 2 ^ lab.n + 1) ∨ (lab.tag = .twE6 ∧ 3 ∣ 2 ^ lab.n + 1) ∨
      (lab.tag = .twA ∧ lab.rank = 5 ∧ 3 ∣ 2 ^ lab.n + 1))) ∨ ggRowP_Small p lab ∨
    (((lab.tag = .A ∧ (lab.rank = 3 ∨ lab.rank = 4)) ∨ (lab.tag = .D ∧ lab.rank = 3)) ∧
      p ∣ 2 ^ lab.n + 1) := by
  have htor : ∀ {r m N : ℕ} {C : Matrix (Fin N) (Fin N) ℤ} {M : CoxeterMatrix (Fin N)},
      GGTBTorRowAt p lab r m N C M → False :=
    fun hrow => hnc ⟨_, _, _, _, _, hrow⟩
  unfold LargeEvenHalfSplit at hS
  rcases hS with hsplit | ⟨htag, hdiv⟩ | ⟨htw, hsub⟩ | ⟨htA, hrA, hnA, -, hp5⟩ |
    ⟨htA8, -, hnA8, hp7A⟩ | ⟨htE6, -, hp7E⟩
  · rcases ggSplit_not_tbTorCov_cases hp hp2 hlab hsplit hnc with hres | hsm | hsp
    · unfold GGSecFiveBCoordBResLabel at hres
      obtain ⟨hp3, h⟩ := hres
      refine Or.inl ⟨hp3, ?_⟩
      rcases h with h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · obtain ⟨ht, hn⟩ := h
        exact Or.inr (Or.inr (Or.inl ⟨ht, by rw [hn]; norm_num⟩))
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
    · exact Or.inr (Or.inl hsm)
    · exact Or.inr (Or.inr hsp)
  · rcases htag with ht | ht | ht | ht | ht
    · exact (htor (GGTBTorRowAt.c (Or.inl ht) (dvd_mul_of_dvd_right hdiv _))).elim
    · by_cases hEven : Even lab.rank
      · exact (htor (GGTBTorRowAt.d (Or.inl ⟨ht, Or.inr ⟨hdiv, hEven⟩⟩))).elim
      · exact (htor (GGTBTorRowAt.relD
          (Or.inl ⟨ht, hdiv, Nat.not_even_iff_odd.mp hEven⟩))).elim
    · by_cases hp3 : p = 3
      · exact Or.inl ⟨hp3, Or.inr (Or.inr (Or.inl ⟨ht, by rw [← hp3]; exact hdiv⟩))⟩
      · exact (htor (GGTBTorRowAt.f4 ht (dvd_mul_of_dvd_right hdiv _)
          (by rintro ⟨h3, -⟩; exact hp3 h3))).elim
    · exact (htor (GGTBTorRowAt.e7 ht (dvd_mul_of_dvd_right hdiv _))).elim
    · by_cases hp3 : p = 3
      · exact (htor (GGTBTorRowAt.e8Three ht hp3)).elim
      · exact (htor (GGTBTorRowAt.e8Ind hp3 ht (dvd_mul_of_dvd_right hdiv _))).elim
  · exact (hnd hsub).elim
  · have hdvd : p ∣ 2 ^ lab.n + 1 := by rw [hp5, hnA]; norm_num
    exact (htor (GGTBTorRowAt.relA5 hrA (Or.inl ⟨htA, hdvd⟩))).elim
  · exact (hp7 hp7A).elim
  · exact (hp7 hp7E).elim

theorem ggMultTableCl_ord_ne_zero {T : GGKacTypeCl} {tw : Bool} {p n : ℕ}
    {D : GGKacDatum} (hD : D ∈ ggMultTableCl T tw p n) : ggMultOrd p n ≠ 0 := by
  intro h
  cases T <;> simp [ggMultTableCl, h] at hD

theorem ggMultBlockA_n (r nf d : ℕ) : (ggMultBlockA r nf d).lab.n = nf := by
  unfold ggMultBlockA
  split_ifs <;> rfl

private theorem ggMultBlockA_one_notTwisted (r nf : ℕ) :
    ¬ ((ggMultBlockA r nf 1).lab.tag = .twA ∨ (ggMultBlockA r nf 1).lab.tag = .twD) := by
  unfold ggMultBlockA
  simp

private theorem twn_append {l₁ l₂ : List GGKacOrbit} {nf : ℕ}
    (h₁ : ∀ o ∈ l₁, (o.lab.tag = .twA ∨ o.lab.tag = .twD) → o.lab.n = nf)
    (h₂ : ∀ o ∈ l₂, (o.lab.tag = .twA ∨ o.lab.tag = .twD) → o.lab.n = nf) :
    ∀ o ∈ l₁ ++ l₂, (o.lab.tag = .twA ∨ o.lab.tag = .twD) → o.lab.n = nf := by
  intro o ho htw
  rw [List.mem_append] at ho
  exact ho.elim (fun h => h₁ o h htw) (fun h => h₂ o h htw)

private theorem twn_map {α : Type*} {l : List α} {f : α → GGKacOrbit} {nf : ℕ}
    (h : ∀ x, (f x).lab.tag = .twA ∨ (f x).lab.tag = .twD → (f x).lab.n = nf) :
    ∀ o ∈ l.map f, (o.lab.tag = .twA ∨ o.lab.tag = .twD) → o.lab.n = nf := by
  intro o ho htw
  rw [List.mem_map] at ho
  obtain ⟨x, -, rfl⟩ := ho
  exact h x htw

private theorem twn_map_A {α : Type*} {l : List α} {g : α → ℕ} {nf : ℕ} :
    ∀ o ∈ l.map (fun x => (⟨⟨.A, g x, 2 * nf⟩, true⟩ : GGKacOrbit)),
      (o.lab.tag = .twA ∨ o.lab.tag = .twD) → o.lab.n = nf := by
  apply twn_map
  intro x htw
  simp at htw

private theorem twn_singleton {o : GGKacOrbit} {nf : ℕ}
    (h : (o.lab.tag = .twA ∨ o.lab.tag = .twD) → o.lab.n = nf) :
    ∀ x ∈ [o], (x.lab.tag = .twA ∨ x.lab.tag = .twD) → x.lab.n = nf := by
  intro x hx htw
  rw [List.mem_singleton] at hx
  subst hx
  exact h htw

private theorem twn_cons {o : GGKacOrbit} {l : List GGKacOrbit} {nf : ℕ}
    (h : (o.lab.tag = .twA ∨ o.lab.tag = .twD) → o.lab.n = nf)
    (hl : ∀ x ∈ l, (x.lab.tag = .twA ∨ x.lab.tag = .twD) → x.lab.n = nf) :
    ∀ x ∈ o :: l, (x.lab.tag = .twA ∨ x.lab.tag = .twD) → x.lab.n = nf := by
  intro x hx htw
  rw [List.mem_cons] at hx
  rcases hx with rfl | hx
  · exact h htw
  · exact hl x hx htw

private theorem twn_nil {nf : ℕ} :
    ∀ o ∈ ([] : List GGKacOrbit), (o.lab.tag = .twA ∨ o.lab.tag = .twD) → o.lab.n = nf := by
  intro o ho
  simp at ho

private theorem twn_of_tag_ne {o : GGKacOrbit} {nf : ℕ}
    (h1 : o.lab.tag ≠ .twA) (h2 : o.lab.tag ≠ .twD) :
    (o.lab.tag = .twA ∨ o.lab.tag = .twD) → o.lab.n = nf := by
  rintro (h | h)
  · exact absurd h h1
  · exact absurd h h2

private theorem ntwn_append {l₁ l₂ : List GGKacOrbit}
    (h₁ : ∀ o ∈ l₁, ¬ (o.lab.tag = .twA ∨ o.lab.tag = .twD))
    (h₂ : ∀ o ∈ l₂, ¬ (o.lab.tag = .twA ∨ o.lab.tag = .twD)) :
    ∀ o ∈ l₁ ++ l₂, ¬ (o.lab.tag = .twA ∨ o.lab.tag = .twD) := by
  intro o ho
  rw [List.mem_append] at ho
  exact ho.elim (h₁ o) (h₂ o)

private theorem ntwn_map {α : Type*} {l : List α} {f : α → GGKacOrbit}
    (h : ∀ x, ¬ ((f x).lab.tag = .twA ∨ (f x).lab.tag = .twD)) :
    ∀ o ∈ l.map f, ¬ (o.lab.tag = .twA ∨ o.lab.tag = .twD) := by
  intro o ho
  rw [List.mem_map] at ho
  obtain ⟨x, -, rfl⟩ := ho
  exact h x

private theorem ntwn_singleton {o : GGKacOrbit}
    (h : ¬ (o.lab.tag = .twA ∨ o.lab.tag = .twD)) :
    ∀ x ∈ [o], ¬ (x.lab.tag = .twA ∨ x.lab.tag = .twD) := by
  intro x hx
  rw [List.mem_singleton] at hx
  subst hx
  exact h

private theorem ggMultV0_twn {m0 nf : ℕ} {plus : Bool} :
    ∀ o ∈ ggMultV0 m0 plus nf,
      (o.lab.tag = .twA ∨ o.lab.tag = .twD) → o.lab.n = nf := by
  unfold ggMultV0
  by_cases h1 : m0 ≤ 1
  · simp [h1]
  by_cases h2 : m0 = 2
  · by_cases hp : plus <;> simp [h2, hp]
  by_cases h3 : m0 = 3
  · by_cases hp : plus <;> simp [h3, hp]
  · by_cases hp : plus <;> simp [h1, h2, h3, hp]

private theorem ggMultDatumC_twn {p nf d : ℕ} (mm : List ℕ) :
    ∀ o ∈ (ggMultDatumC p nf d mm).orbits,
      (o.lab.tag = .twA ∨ o.lab.tag = .twD) → o.lab.n = nf := by
  unfold ggMultDatumC
  dsimp only
  by_cases h0 : mm.headD 0 = 1
  · rw [if_pos h0]
    exact twn_append (twn_singleton (twn_of_tag_ne (by simp) (by simp)))
      (twn_map (fun x _ => ggMultBlockA_n (mm.getD x 0 - 1) nf d))
  by_cases h1 : mm.headD 0 = 2 ∧ nf = 1
  · rw [if_neg h0, if_pos h1]
    exact twn_append (twn_singleton (twn_of_tag_ne (by simp) (by simp)))
      (twn_map (fun x _ => ggMultBlockA_n (mm.getD x 0 - 1) nf d))
  by_cases h2 : 2 ≤ mm.headD 0
  · rw [if_neg h0, if_neg h1, if_pos h2]
    exact twn_append (twn_singleton (twn_of_tag_ne (by simp) (by simp)))
      (twn_map (fun x _ => ggMultBlockA_n (mm.getD x 0 - 1) nf d))
  · rw [if_neg h0, if_neg h1, if_neg h2]
    exact twn_append (by simp)
      (twn_map (fun x _ => ggMultBlockA_n (mm.getD x 0 - 1) nf d))

private theorem ggMultDatumD_twn {p nf d : ℕ} (tw : Bool) (mm : List ℕ) :
    ∀ o ∈ (ggMultDatumD p nf d tw mm).orbits,
      (o.lab.tag = .twA ∨ o.lab.tag = .twD) → o.lab.n = nf := by
  unfold ggMultDatumD
  dsimp only
  exact twn_append ggMultV0_twn
    (twn_map (fun x _ => ggMultBlockA_n (mm.getD x 0 - 1) nf d))

private theorem ggMultDatumA_twisted_n {p nf d : ℕ} {tw : Bool} (mm : List ℕ) (htw : tw = true) :
    ∀ o ∈ (ggMultDatumA p nf d tw mm).orbits,
      (o.lab.tag = .twA ∨ o.lab.tag = .twD) → o.lab.n = nf := by
  unfold ggMultDatumA
  dsimp only
  by_cases htriv : (tw = false ∧ d = 1) ∨ (tw = true ∧ d = 2)
  · rw [if_pos htriv]
    exact twn_map (fun x _ => ggMultBlockA_n (mm.getD x 0 - 1) nf d)
  · rw [if_neg htriv]
    by_cases h2 : 2 ≤ mm.headD 0
    · rw [if_pos h2]
      dsimp only
      have htwf : ¬ (tw = false) := by rw [htw]; decide
      rw [if_neg htwf]
      exact twn_append (twn_cons (fun _ => ggMultBlockA_n (mm.headD 0 - 1) nf 2) twn_nil)
        twn_map_A
    · rw [if_neg h2]
      exact twn_append twn_nil twn_map_A

private theorem ggMultDatumA_notTwisted {p nf d : ℕ} {tw : Bool} (mm : List ℕ) (htw : tw = false) :
    ∀ o ∈ (ggMultDatumA p nf d tw mm).orbits,
      ¬ (o.lab.tag = .twA ∨ o.lab.tag = .twD) := by
  unfold ggMultDatumA
  dsimp only
  by_cases htriv : (tw = false ∧ d = 1) ∨ (tw = true ∧ d = 2)
  · rw [if_pos htriv]
    have hd1 : d = 1 := by
      rcases htriv with ⟨-, h⟩ | ⟨h, -⟩
      · exact h
      · rw [htw] at h; exact absurd h (by decide)
    subst hd1
    exact ntwn_map (fun x => ggMultBlockA_one_notTwisted (mm.getD x 0 - 1) nf)
  · rw [if_neg htriv]
    by_cases h2 : 2 ≤ mm.headD 0
    · rw [if_pos h2]
      dsimp only
      rw [if_pos htw]
      exact ntwn_append (ntwn_singleton (by simp)) (ntwn_map (fun _ => by simp))
    · rw [if_neg h2]
      exact ntwn_append (by simp) (ntwn_map (fun _ => by simp))

theorem ggMultValidCl_twisted_orbit {lab : LargeEvenLabel} {p : ℕ} {D : GGKacDatum}
    (hV : GGMultValidCl lab p D) (hd : p ∣ 2 ^ lab.n + 1) (hnd : ¬ p ∣ 2 ^ lab.n - 1)
    {o : GGKacOrbit} (ho : o ∈ D.orbits) (htw : o.lab.tag = .twA ∨ o.lab.tag = .twD) :
    o.lab.n = lab.n ∧ lab.tag ≠ .A := by
  obtain ⟨T, tw, m, hlab, hDmem⟩ := hV
  have hord : ggMultOrd p m ≠ 0 := ggMultTableCl_ord_ne_zero hDmem
  rcases lab with ⟨t, r, e⟩
  cases t with
  | A =>
    simp only [ggKacTypeClOfLabel, Option.some.injEq, Prod.mk.injEq] at hlab
    obtain ⟨rfl, rfl, rfl⟩ := hlab
    obtain ⟨mm, -, -, -, hDeq⟩ :=
      (mem_ggMultTableCl_A (r := r) (p := p) (n := e) (tw := false) (D := D) hord).mp hDmem
    rw [hDeq] at ho
    exact absurd htw (ggMultDatumA_notTwisted mm rfl o ho)
  | twA =>
    simp only [ggKacTypeClOfLabel, Option.some.injEq, Prod.mk.injEq] at hlab
    obtain ⟨rfl, rfl, rfl⟩ := hlab
    obtain ⟨mm, -, -, -, hDeq⟩ :=
      (mem_ggMultTableCl_A (r := r) (p := p) (n := e) (tw := true) (D := D) hord).mp hDmem
    rw [hDeq] at ho
    exact ⟨ggMultDatumA_twisted_n mm rfl o ho htw, by simp⟩
  | B =>
    simp only [ggKacTypeClOfLabel] at hlab
    by_cases h2r : 2 ≤ r
    · rw [if_pos h2r] at hlab
      simp only [Option.some.injEq, Prod.mk.injEq] at hlab
      obtain ⟨rfl, rfl, rfl⟩ := hlab
      obtain ⟨mm, -, -, hDeq⟩ :=
        (mem_ggMultTableCl_C (r := r) (p := p) (n := e) (D := D) hord).mp hDmem
      rw [hDeq] at ho
      exact ⟨ggMultDatumC_twn mm o ho htw, by simp⟩
    · rw [if_neg h2r] at hlab
      simp at hlab
  | C =>
    simp only [ggKacTypeClOfLabel] at hlab
    by_cases h2r : 2 ≤ r
    · rw [if_pos h2r] at hlab
      simp only [Option.some.injEq, Prod.mk.injEq] at hlab
      obtain ⟨rfl, rfl, rfl⟩ := hlab
      obtain ⟨mm, -, -, hDeq⟩ :=
        (mem_ggMultTableCl_C (r := r) (p := p) (n := e) (D := D) hord).mp hDmem
      rw [hDeq] at ho
      exact ⟨ggMultDatumC_twn mm o ho htw, by simp⟩
    · rw [if_neg h2r] at hlab
      simp at hlab
  | D =>
    simp only [ggKacTypeClOfLabel] at hlab
    by_cases h4r : 4 ≤ r
    · rw [if_pos h4r] at hlab
      simp only [Option.some.injEq, Prod.mk.injEq] at hlab
      obtain ⟨rfl, rfl, rfl⟩ := hlab
      obtain ⟨mm, -, -, -, hDeq⟩ :=
        (mem_ggMultTableCl_D (r := r) (p := p) (n := e) (tw := false) (D := D) hord).mp hDmem
      rw [hDeq] at ho
      exact ⟨ggMultDatumD_twn false mm o ho htw, by simp⟩
    · rw [if_neg h4r] at hlab
      by_cases hr3 : r = 3
      · rw [if_pos hr3] at hlab
        simp only [Option.some.injEq, Prod.mk.injEq] at hlab
        obtain ⟨rfl, rfl, rfl⟩ := hlab
        obtain ⟨mm, -, -, -, hDeq⟩ :=
          (mem_ggMultTableCl_A (r := 3) (p := p) (n := e) (tw := false) (D := D) hord).mp hDmem
        rw [hDeq] at ho
        exact absurd htw (ggMultDatumA_notTwisted mm rfl o ho)
      · rw [if_neg hr3] at hlab
        simp at hlab
  | twD =>
    simp only [ggKacTypeClOfLabel] at hlab
    by_cases h4r : 4 ≤ r
    · rw [if_pos h4r] at hlab
      simp only [Option.some.injEq, Prod.mk.injEq] at hlab
      obtain ⟨rfl, rfl, rfl⟩ := hlab
      obtain ⟨mm, -, -, -, hDeq⟩ :=
        (mem_ggMultTableCl_D (r := r) (p := p) (n := e) (tw := true) (D := D) hord).mp hDmem
      rw [hDeq] at ho
      exact ⟨ggMultDatumD_twn true mm o ho htw, by simp⟩
    · rw [if_neg h4r] at hlab
      by_cases hr3 : r = 3
      · rw [if_pos hr3] at hlab
        simp only [Option.some.injEq, Prod.mk.injEq] at hlab
        obtain ⟨rfl, rfl, rfl⟩ := hlab
        obtain ⟨mm, -, -, -, hDeq⟩ :=
          (mem_ggMultTableCl_A (r := 3) (p := p) (n := e) (tw := true) (D := D) hord).mp hDmem
        rw [hDeq] at ho
        exact ⟨ggMultDatumA_twisted_n mm rfl o ho htw, by simp⟩
      · rw [if_neg hr3] at hlab
        by_cases hr2 : r = 2
        · rw [if_pos hr2] at hlab
          simp only [Option.some.injEq, Prod.mk.injEq] at hlab
          obtain ⟨rfl, rfl, rfl⟩ := hlab
          obtain ⟨mm, -, -, -, hDeq⟩ :=
            (mem_ggMultTableCl_A (r := 1) (p := p) (n := 2 * e) (tw := false) (D := D)
              hord).mp hDmem
          rw [hDeq] at ho
          exact absurd htw (ggMultDatumA_notTwisted mm rfl o ho)
        · rw [if_neg hr2] at hlab
          simp at hlab
  | E6 => simp [ggKacTypeClOfLabel] at hlab
  | E7 => simp [ggKacTypeClOfLabel] at hlab
  | E8 => simp [ggKacTypeClOfLabel] at hlab
  | F4 => simp [ggKacTypeClOfLabel] at hlab
  | twE6 => simp [ggKacTypeClOfLabel] at hlab
  | triD4 => simp [ggKacTypeClOfLabel] at hlab
  | G2 => simp [ggKacTypeClOfLabel] at hlab
  | twB2 => simp [ggKacTypeClOfLabel] at hlab
  | twF4 => simp [ggKacTypeClOfLabel] at hlab
  | B2der => simp [ggKacTypeClOfLabel] at hlab
  | G2der => simp [ggKacTypeClOfLabel] at hlab
  | twF4der => simp [ggKacTypeClOfLabel] at hlab

theorem ggNbrK_J_le_K {G : Type} [Group G] [Finite G] (hI3 : GGNbrSubcomponentInput)
    {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J) {y : G} {K : Subgroup G} (hnb : GGNbr p B x D J y K) :
    J ≤ K :=
  hI3 G p B x L D J hcfg.1 hcfg.2.2 y K hnb

theorem ggNbrK_not_dvd_sub_one {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hd : p ∣ 2 ^ n + 1) : ¬ p ∣ 2 ^ n - 1 := by
  intro h
  have h2 : p ∣ (2 ^ n + 1) - (2 ^ n - 1) := Nat.dvd_sub hd h
  have h3 : (2 ^ n + 1) - (2 ^ n - 1) = 2 := by
    have := Nat.one_le_two_pow (n := n)
    omega
  rw [h3] at h2
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2)

theorem ggNbrK_datum_of_label {G : Type} [Group G] {Bs K : Subgroup G}
    (hRig : GGLabelRigidInput) (hInnK : GGInnerDiagOn Bs K) {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (hhas : GGHasLabel lab (↥K ⧸ Subgroup.center ↥K))
    {P : LargeEvenRawCont} (hP : LargeEvenLabelAll lab P) :
    ∃ (R : Type) (_ : Group R) (θ : ↥K ⧸ Subgroup.center ↥K ≃* R) (I F : Set (MulAut R)),
      (Bs ≤ Subgroup.normalizer (K : Set G)) ∧
      (∀ b ∈ Bs, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ) ∧
      P R I F := by
  have hmark := ggInnerDiagOn_relabel hRig hInnK hlab hhas
  have hmark' := largeEvenMarking_and_labelAll (S := fun lab' => lab' = lab) (P' := P)
    (fun lab' _ h' => by rw [h']; exact hP)
    (fun lab' R _ I F θ hPmark => hPmark.1) hmark
  obtain ⟨-, lab', hlab', hraw'⟩ := hmark'
  obtain ⟨R, _, I, F, -, -, θ, hPθ⟩ := largeEvenRawDatum_exists hraw'
  obtain ⟨⟨-, hN', hind⟩, hPR⟩ := hPθ
  exact ⟨R, ‹Group R›, θ, I, F, hN', hind, hPR⟩

private theorem ggLabelIso_twA_field {lab : LargeEvenLabel} {m f : ℕ}
    (hiso : GGLabelIso lab ⟨.twA, m, f⟩) :
    (lab.tag = .twA ∨ lab.tag = .twD) ∧ lab.n = f := by
  rcases hiso with h | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ |
    ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · subst h
    exact ⟨Or.inl rfl, rfl⟩
  · rcases h2 with h2 | h2
    · simp at h2
    · simp at h2
  · have htag : LargeEvenLieTag.twA = LargeEvenLieTag.A := by
      simpa using congrArg LargeEvenLabel.tag h2
    exact absurd htag (by decide)
  · have htag : LargeEvenLieTag.twA = LargeEvenLieTag.D := by
      simpa using congrArg LargeEvenLabel.tag h2
    exact absurd htag (by decide)
  · refine ⟨Or.inr ?_, ?_⟩
    · have htag : lab.tag = LargeEvenLieTag.twD := by
        simpa using congrArg LargeEvenLabel.tag h1
      exact htag
    · have hn : f = lab.n := by simpa using congrArg LargeEvenLabel.n h2
      omega
  · have htag : LargeEvenLieTag.twA = LargeEvenLieTag.twD := by
      simpa using congrArg LargeEvenLabel.tag h2
    exact absurd htag (by decide)
  · have htag : LargeEvenLieTag.twA = LargeEvenLieTag.A := by
      simpa using congrArg LargeEvenLabel.tag h2
    exact absurd htag (by decide)
  · have htag : LargeEvenLieTag.twA = LargeEvenLieTag.twD := by
      simpa using congrArg LargeEvenLabel.tag h1
    exact absurd htag (by decide)

theorem ggNbrK_field_of_k0
    (hI3 : GGNbrSubcomponentInput) (hRig : GGLabelRigidInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J) {y : G} {K : Subgroup G} (hnb : GGNbr p B x D J y K)
    (hInnK : GGInnerDiagOn Bs K) {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (hhas : GGHasLabel lab (↥K ⧸ Subgroup.center ↥K)) (hgen : GGKacGenericCl lab p)
    (hd : p ∣ 2 ^ lab.n + 1) {m f : ℕ} (hm : 2 ≤ m) (hf : 1 ≤ f) (hmf : m = 2 → 2 ≤ f)
    (hJ : GGHasLabel ⟨.twA, m, f⟩ (↥J ⧸ Subgroup.center ↥J)) :
    lab.n = f ∧ lab.tag ≠ .A := by
  have hp : p.Prime := hgen.1
  have hp2 : p ≠ 2 := hgen.2.1
  have hnd : ¬ p ∣ 2 ^ lab.n - 1 := ggNbrK_not_dvd_sub_one hp hp2 hd
  have hT : GGThmIHyp p B x L := hcfg.1
  have hSS : LargeEvenSStar p B x L := hT.2.2.2.2.2.2.1
  have hBel : IsElemAbelian p B := hSS.1.1
  have hx : x ∈ B := hSS.2.1
  have hxBs : x ∈ Bs := hcfg.2.1.1 hx
  have hDJ : LargeEvenStdSub p B x L D J := hcfg.2.2
  have hJK : J ≤ K := ggNbrK_J_le_K hI3 hcfg hnb
  have hcomp : IsComponentOf J (K ⊓ Subgroup.centralizer ({x} : Set G)) :=
    isComponentOf_inf_centralizer_of_ggNbr hSS hDJ hnb hJK
  obtain ⟨R, hR, θ, I, F, hN, hind, hPk⟩ :=
    ggNbrK_datum_of_label hRig hInnK hlab hhas (ggK0Main_cl p lab hlab hgen)
  let : Group R := hR
  have hxN : x ∈ Subgroup.normalizer (K : Set G) := hN hxBs
  let ψ : ↥K →* R :=
    (θ : ↥K ⧸ Subgroup.center ↥K →* R).comp (QuotientGroup.mk' (Subgroup.center ↥K))
  have hψsurj : Function.Surjective ψ := by
    intro r
    obtain ⟨q, rfl⟩ := θ.surjective r
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective q
    exact ⟨l, rfl⟩
  have hψker : ψ.ker ≤ Subgroup.center ↥K := by
    intro l hl
    have h0 : θ (QuotientGroup.mk l) = 1 := hl
    have h1 : (QuotientGroup.mk l : ↥K ⧸ Subgroup.center ↥K) = 1 := by
      simpa using θ.injective (h0.trans (map_one θ).symm)
    exact (QuotientGroup.eq_one_iff l).mp h1
  let e : MulAut ↥K := K.normalizerMonoidHom ⟨x, hxN⟩
  have hx1 : x ^ p = 1 := hBel.2 x hx
  have hep : e ^ p = 1 := by
    dsimp only [e]
    rw [← map_pow]
    have h1 : (⟨x, hxN⟩ : ↥(Subgroup.normalizer (K : Set G))) ^ p = 1 :=
      Subtype.ext (by simpa using hx1)
    rw [h1, map_one]
  obtain ⟨φ, hφI, hφ⟩ := hind x⁻¹ (Bs.inv_mem hxBs)
  have hine : ∃ φ ∈ I, ∀ l : ↥K, φ (ψ l) = ψ (e l) := by
    refine ⟨φ, hφI, fun l => hφ l (e l) ?_⟩
    show ((e l : ↥K) : G) = x⁻¹⁻¹ * (l : G) * x⁻¹
    dsimp only [e]
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe, inv_inv]
  have hJcomp : IsComponentOf (J.subgroupOf K) (ggFixSub e) :=
    ggIsComponentOf_ggFixSub_normalizerMonoidHom hxN hcomp
  obtain ⟨D, hValid, hcompA, -, -, -⟩ :=
    hPk ↥K ψ hψsurj hψker hInnK.1 e hep hine
  obtain ⟨o, ho, hqs, hndvd, hΛo, hhasO⟩ := hcompA (J.subgroupOf K) hJcomp
  have hhasO' : GGHasLabel o.lab (↥J ⧸ Subgroup.center ↥J) :=
    ggHasLabel_of_mulEquiv (QuotientGroup.congr _ _ (Subgroup.subgroupOfEquivOfLe hJK)
      (Subgroup.map_center_eq _)) hhasO
  have hΛtwA : LargeEvenInLambda2 ⟨.twA, m, f⟩ := by
    unfold LargeEvenInLambda2
    dsimp only
    exact ⟨hf, hm, hmf⟩
  have hiso : GGLabelIso o.lab ⟨.twA, m, f⟩ :=
    hRig o.lab ⟨.twA, m, f⟩ (↥J ⧸ Subgroup.center ↥J) hΛo hΛtwA hhasO' hJ
  obtain ⟨htwO, hnO⟩ := ggLabelIso_twA_field hiso
  obtain ⟨hnLab, htagLab⟩ := ggMultValidCl_twisted_orbit hValid hd hnd ho htwO
  exact ⟨hnLab.symm.trans hnO, htagLab⟩

theorem card_ggAutomizer_of_twA5Three_nbr
    (hRig : GGLabelRigidInput)
    (hLB : GGLBalanceInput) (hPJ : GGStdSubPrimeInput) {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hcfg : GGConfig 3 B Bs x L D J) (hnb : GGNbr 3 B x D J y K) (hInn : GGInnerDiagOn Bs K)
    {labX : LargeEvenLabel} (hΛ : LargeEvenInLambda2 labX)
    (hl : GGHasLabel labX (↥K ⧸ Subgroup.center ↥K))
    (htag : labX.tag = .twA ∧ labX.rank = 5 ∧ 3 ∣ 2 ^ labX.n + 1) :
    Nat.card ↥(ggAutomizer K Bs) = 720 := by
  obtain ⟨f, hN, hf, hpq, hTor⟩ :=
    ggTwA5Three_torDataNbr hRig hLB hPJ hcfg hnb hInn hΛ hl htag
  have hodd : Odd (2 ^ f + 1) := by
    obtain ⟨g, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : f ≠ 0)
    rw [pow_succ]
    exact ⟨2 ^ g, by omega⟩
  have hW := NSJoin.weylOfType_of_torData (p := 3) (by norm_num : (3 : ℕ) ≠ 2) hodd hpq
    (ggIntCartan_A 5) hcfg.2.1.2.1 hcfg.2.1.2.2.2 hN hTor
  obtain ⟨e, -⟩ := hW
  rw [← Nat.card_congr e.toEquiv, l05nK3a_card_coxeterA 5]
  norm_num [Nat.factorial]


private theorem ggLabelIso_n_eq_of_not_small {p : ℕ} {lab lab' : LargeEvenLabel}
    (h : GGLabelIso lab lab') (hns : ¬ ggRowP_Small p lab) : lab.n = lab'.n := by
  rcases h with rfl | hBC | hD3 | hA3 | htwD3 | htwA3 | htwD2 | hA1D2
  · rfl
  · exact hBC.2.2.2
  · rw [hD3.2]
  · rw [hA3.2]
  · rw [htwD3.2]
  · rw [htwA3.2]
  · exact absurd (show ggRowP_Small p lab from by rw [htwD2.1]; simp [ggRowP_Small]) hns
  · exact absurd (show ggRowP_Small p lab from by rw [hA1D2.2]; simp [ggRowP_Small]) hns

section Label


theorem GGSecFiveRouteCfg.uniNbr_label_of_bBlockOn (hT : GGTBTorAll) (hLift : GGTBTorLiftRows)
    (hTCJ : GGTCJKnown) (hI3 : GGNbrSubcomponentInput) (hRig : GGLabelRigidInput)
    (hraw : GGRawInnFieldInput) (hiso : GGRawInndiagIsoInput) (hLB : GGLBalanceInput)
    (hPJ : GGStdSubPrimeInput) (hTE6R : GGTwE6ThreeNbrRankInput)
    {G : Type} [Group G] [Finite G] {p n f : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)} (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))) {K : Subgroup G} (hK𝒦 : K ∈ 𝒦)
    {I : Finset (Fin n)} (hI : 3 ≤ I.card)
    (hAut : (ggAutomizer K Bs).map (MulAut.congr eta).toMonoidHom = bBlockOn n p I)
    (hZ : Nat.card ↥(Bs ⊓ K ⊓ Subgroup.centralizer (K : Set G)) ≤ p)
    (hf : 1 ≤ f) (hIf : I.card = 3 → 2 ≤ f) (hpf : p ∣ 2 ^ f + 1)
    (hJ : GGHasLabel ⟨.twA, I.card - 1, f⟩ (↥J ⧸ Subgroup.center ↥J)) :
    GGInnerDiagOnLabel (fun _ lab => GGSecFiveBPermUniNbrLabel (I.card + 1) f lab) p Bs K := by
  obtain ⟨hp, hp2⟩ := ggRouteCfg_prime hR
  have : Fact p.Prime := ⟨hp⟩
  have hNoTr : GGNoTransvection p Bs := hR.1.2.2.2.1
  have hweak : GGSecFiveWeakNbr p B Bs x L D J 𝒦 K := GGSecFiveWeakNbr.of_mem hR hK𝒦
  obtain ⟨y, hnb⟩ := hR.2.2.2.1.2 K hK𝒦
  have hInnK : GGInnerDiagOn Bs K := hR.1.2.2.1.2 y K hnb
  have hH : GGResHyp p B Bs x L D J y K :=
    ⟨hR.1.1, hR.1.2.1, hR.1.2.2.1, hNoTr, hnb, hR.2.1 y K hnb, Or.inr hR.2.1⟩
  have hcardK : Nat.card ↥(ggAutomizer K Bs) = 2 ^ I.card * I.card.factorial :=
    card_ggAutomizer_of_bBlockOn hp hp2 eta I hAut
  have hp7 : p ≠ 7 := by
    intro h7
    subst h7
    exact ggA8Nbr_not_seven_dvd_two_pow_add_one f hpf
  obtain ⟨lab, hlab, hHS, hfin⟩ :=
    ggNbr_exists_halfSplit_innerDiagLabel hRig hraw hiso hR.1.1 hnb hInnK
  have hhas : GGHasLabel lab (↥K ⧸ Subgroup.center ↥K) := by
    obtain ⟨lab', -, hhas', R, _, I, F, θ, hlab', -⟩ :=
      largeEvenMarking_exists_hasLabel (hfin (fun _ l => l = lab) rfl)
    rw [hlab'] at hhas'
    exact hhas'
  by_cases hsm : ggRowP_Small p lab
  · exact (ggX_absurd_of_small_halfSplit hR (Or.inr hweak) (hfin _ ⟨hsm, hHS⟩)).elim
  obtain ⟨lab1, labJ, hl1, hhas1, hlJ, hdvd, hhasJ⟩ :=
    ggNbrK_label_J_of_tcj hTCJ hI3 hR.1.1 hR.1.2.2.1 hnb
  have hlabJ : LargeEvenInLambda2 ⟨.twA, I.card - 1, f⟩ := by
    refine ⟨?_, ?_, ?_⟩
    · show 1 ≤ f
      omega
    · show 2 ≤ I.card - 1
      omega
    · show I.card - 1 = 2 → 2 ≤ f
      intro h
      exact hIf (by omega)
  have hisoJ : GGLabelIso ⟨.twA, I.card - 1, f⟩ labJ :=
    hRig _ _ _ hlabJ hlJ hJ hhasJ
  have hlabJn : labJ.n = f := by
    have h := NSJoin.ggLabelIso_n_eq hisoJ (lab := ⟨.twA, I.card - 1, f⟩) (lab' := labJ)
      (by simp) (by simp)
    exact h.symm
  have hiso1 : GGLabelIso lab lab1 := hRig lab lab1 _ hlab hl1 hhas hhas1
  have hlab1n : lab.n = lab1.n := ggLabelIso_n_eq_of_not_small hiso1 hsm
  have hdvdnf : lab.n ∣ f := by
    rw [hlab1n]
    simpa [hlabJn] using hdvd
  have hnd : ¬ p ∣ 2 ^ lab.n - 1 := by
    intro hsub
    have hsubf : p ∣ 2 ^ f - 1 :=
      hsub.trans (Nat.pow_sub_one_dvd_pow_sub_one 2 hdvdnf)
    exact not_dvd_two_pow_add_one_of_dvd_sub_one hp hp2 hsubf hpf
  have hd : p ∣ 2 ^ lab.n + 1 := by
    rcases largeEvenHalfSplit_dvd hlab hHS with h | ⟨h7, -⟩
    · have hsq : (2 ^ lab.n) ^ 2 - 1 = (2 ^ lab.n - 1) * (2 ^ lab.n + 1) := by
        rw [pow_two, mul_self_tsub_one, mul_comm]
      rw [hsq] at h
      rcases (hp.dvd_mul.mp h) with h' | h'
      · exact absurd h' hnd
      · exact h'
    · exact absurd h7 hp7
  by_cases hcov : GGTBTorCov p lab
  ·
    obtain ⟨r, m, N, C, M, hrow⟩ := hcov
    have hL : GGInnerDiagOnLabel (fun p lab' => ∃ (r m N : ℕ) (C : Matrix (Fin N) (Fin N) ℤ)
        (M : CoxeterMatrix (Fin N)), GGTBTorRowAt p lab' r m N C M ∧
          GGTBTorRowAt p lab r m N C M) p Bs K :=
      hfin _ ⟨r, m, N, C, M, hrow, hrow⟩
    obtain ⟨r', m', N', C', M', hrow', hcardM⟩ := hH.exists_row_card_automizer_K hT hLift hL
    have hk : 3 ≤ I.card := hI
    have hmatch := ggTBTorRowAt_coordB_of_card hlab hrow' hk (hcardM ▸ hcardK)
    have hclass : (lab.tag = .A ∨ lab.tag = .twA ∨ lab.tag = .B ∨ lab.tag = .C ∨
        lab.tag = .D ∨ lab.tag = .twD) ∧ (lab.tag = .twA → ¬ p ∣ lab.rank + 1) := by
      rcases hmatch with ⟨hBC, -⟩ | ⟨⟨hD, -, -⟩ | ⟨htwD, -⟩, -⟩ |
        ⟨-, ⟨hA, -⟩ | ⟨htwA, hsub⟩, -⟩
      · rcases hBC with hB | hC
        · exact ⟨Or.inr (Or.inr (Or.inl hB)), by rw [hB]; simp⟩
        · exact ⟨Or.inr (Or.inr (Or.inr (Or.inl hC))), by rw [hC]; simp⟩
      · exact ⟨Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hD)))), by rw [hD]; simp⟩
      · exact ⟨Or.inr (Or.inr (Or.inr (Or.inr (Or.inr htwD)))), by rw [htwD]; simp⟩
      · exact ⟨Or.inl hA, by rw [hA]; simp⟩
      · exact (hnd hsub).elim
    have hgen : GGKacGenericCl lab p :=
      ⟨hp, hp2, Or.inr hd, hclass.1, by rintro ⟨-, -, h⟩; exact hnd h,
        by rintro ⟨h, hdiv, -⟩; exact hclass.2 h hdiv⟩
    obtain ⟨hfield, hnA⟩ :=
      ggNbrK_field_of_k0 hI3 hRig hR.1.1 hnb hInnK hlab hhas hgen hd
        (m := I.card - 1) (by omega) hf (fun h => hIf (by omega)) hJ
    refine hfin _ ⟨hfield, ?_⟩
    rcases hmatch with ⟨hBC, hrank⟩ | ⟨hDcase, hrank⟩ | ⟨hrank5, hA5, hk3⟩
    · exact Or.inl ⟨hBC, hrank⟩
    · have hn_eq : lab.rank = I.card + 1 := by omega
      rcases hDcase with ⟨hD, -, hodd⟩ | ⟨htwD, hcase⟩
      · exact Or.inr (Or.inl ⟨hD, hn_eq, by simpa [hn_eq] using hodd⟩)
      · have heven : Even lab.rank := by
          rcases hcase with hsub | ⟨-, he⟩
          · exact (hnd hsub).elim
          · exact he
        exact Or.inr (Or.inr ⟨htwD, hn_eq, by simpa [hn_eq] using heven⟩)
    · rcases hA5 with ⟨hA, -⟩ | ⟨htwA, hsub⟩
      · exact absurd hA hnA
      · exact (hnd hsub).elim
  ·
    rcases ggHalfSplit_not_tbTorCov_cases hp hp2 hp7 hlab hHS hnd hcov with
      ⟨hp3, hcat⟩ | hsm' | hsp
    · obtain rfl := hp3
      rcases hcat with ⟨htag, hr6, hn1⟩ | ⟨htag, hn1⟩ | ⟨htag, h3dvd⟩ | ⟨htag, h3dvd⟩ |
        ⟨htag, hr5, h3dvd⟩
      · have hgen : GGKacGenericCl lab 3 :=
          ⟨Nat.prime_three, by norm_num, Or.inr hd, Or.inl htag,
            by rintro ⟨-, -, h⟩; exact hnd h,
            by rintro ⟨h, -, -⟩; exact absurd h (by rw [htag]; simp)⟩
        obtain ⟨-, hnA⟩ :=
          ggNbrK_field_of_k0 hI3 hRig hR.1.1 hnb hInnK hlab hhas hgen hd
            (m := I.card - 1) (by omega) hf (fun h => hIf (by omega)) hJ
        exact absurd htag hnA
      · have h1152 :=
          card_ggAutomizer_of_e6Two_nbr hR.1.1 hNoTr hnb (hfin _ ⟨htag, hn1⟩) hZ
        rw [hcardK] at h1152
        exact (two_pow_mul_factorial_ne_1152 (I.card) h1152).elim
      · have h1152 :=
          card_ggAutomizer_of_f4Three hR.1.1 hNoTr (hfin _ ⟨htag, rfl, h3dvd⟩) hZ
        rw [hcardK] at h1152
        exact (two_pow_mul_factorial_ne_1152 (I.card) h1152).elim
      · have h51840 :=
          card_ggAutomizer_of_twE6Bad_nbr hRig hTE6R hR.1.1 hNoTr hnb hInnK
            (hfin _ ⟨htag, rfl, h3dvd⟩) hZ
        rw [hcardK] at h51840
        exact (two_pow_mul_factorial_ne_51840 (I.card) h51840).elim
      · have h720 :=
          card_ggAutomizer_of_twA5Three_nbr hRig hLB hPJ hR.1.1 hnb hInnK hlab hhas
            ⟨htag, hr5, h3dvd⟩
        rw [hcardK] at h720
        exact (two_pow_mul_factorial_ne_720 (I.card) h720).elim
    · exact (ggX_absurd_of_small_halfSplit hR (Or.inr hweak) (hfin _ ⟨hsm', hHS⟩)).elim
    · exact (ggX_row_absurd_of_pRank ggRowPRankLeTwo_smallPlus hR (Or.inr hweak)
        (hfin _ hsp)).elim

theorem GGSecFiveRouteCfg.uniNbr_label (hT : GGTBTorAll) (hLift : GGTBTorLiftRows)
    (hTCJ : GGTCJKnown) (hI3 : GGNbrSubcomponentInput) (hRig : GGLabelRigidInput)
    (hraw : GGRawInnFieldInput) (hiso : GGRawInndiagIsoInput) (hLB : GGLBalanceInput)
    (hPJ : GGStdSubPrimeInput) (hTE6R : GGTwE6ThreeNbrRankInput)
    {G : Type} [Group G] [Finite G] {p n f : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)} (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    (hn : 4 ≤ n) (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))) {K : Subgroup G}
    (hK𝒦 : K ∈ 𝒦) (i0 : Fin n)
    (hAut : (ggAutomizer K Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock n p i0)
    (hf : 1 ≤ f) (hnf : n = 4 → 2 ≤ f) (hpf : p ∣ 2 ^ f + 1)
    (hJ : GGHasLabel ⟨.twA, n - 2, f⟩ (↥J ⧸ Subgroup.center ↥J)) :
    GGInnerDiagOnLabel (fun _ lab => GGSecFiveBPermUniNbrLabel n f lab) p Bs K := by
  obtain ⟨hp, hp2⟩ := ggRouteCfg_prime hR
  have hI : (Finset.univ.erase i0).card = n - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ i0), Finset.card_univ, Fintype.card_fin]
  have hAutI : (ggAutomizer K Bs).map (MulAut.congr eta).toMonoidHom =
      bBlockOn n p (Finset.univ.erase i0) := by
    rw [bBlockOn_univ_erase]
    exact hAut
  have hJI : GGHasLabel ⟨.twA, (Finset.univ.erase i0).card - 1, f⟩
      (↥J ⧸ Subgroup.center ↥J) := by
    rw [show (Finset.univ.erase i0).card - 1 = n - 2 by omega]
    exact hJ
  have h := hR.uniNbr_label_of_bBlockOn hT hLift hTCJ hI3 hRig hraw hiso hLB hPJ hTE6R eta hK𝒦
    (by omega) hAutI (card_bstar_inf_center_le_of_bCoordinateBlock hp hp2 eta i0 hAut) hf
    (fun h => hnf (by omega)) hpf hJI
  rwa [show (Finset.univ.erase i0).card + 1 = n by omega] at h

end Label

end CFSG.StandardType

end
