module

public import CFSG.Certificates.NativeSchreierEnum

public section

namespace CFSG.Sporadic.Schreier.Tits

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Certificates.ChainArrays

variable {n : ℕ}

theorem exists_levT_prod {Q : RawSchreierDatum n} {O S : Array (Array ℕ)} {base : Array ℕ}
    {W : Array (List ℤ)} {chunks : ℕ} (hA : ChainArrays Q O S base W) (hc : 0 < chunks)
    (h : rawChainOK n O S base W chunks = true) {g : Equiv.Perm (Fin n)}
    (hg : g ∈ Q.originalSubgroup) :
    ∃ c : Fin Q.baseCount → ℕ, (∀ i, c i < (lev n S base i).pts.size) ∧
      (List.ofFn fun i => levT n S base i (c i)).prod = g := by
  have hF := chainCheckFacts h
  have hQ := (validSchreier_of_chainOK hA hc h).1
  obtain ⟨-, Φ, hΦ, hbij, -⟩ := Q.schreier_transversal_product_bijection hQ
  obtain ⟨y, hy⟩ := hbij.2 ⟨g, hg⟩
  refine ⟨fun i => (lev n S base i).pos[((y i : Fin n) : ℕ)]!,
    fun i => (hA.orbitPoints_spec hF i.2 (y i).2).1, ?_⟩
  have hT : ∀ i : Fin Q.baseCount, Q.orbitTransversal i (y i) =
      levT n S base i (lev n S base i).pos[((y i : Fin n) : ℕ)]! :=
    fun i => (hA.orbitPoints_spec hF i.2 (y i).2).2.2
  have hgy : (Φ y : Equiv.Perm (Fin n)) = g := congrArg Subtype.val hy
  rw [← hgy, hΦ y]
  exact congrArg List.prod (congrArg List.ofFn (funext fun i => (hT i).symm))

theorem prod_ofFn_five {M : Type*} [Monoid M] {k : ℕ} (hk : k = 5) (f : Fin k → M) :
    (List.ofFn f).prod = f ⟨0, by omega⟩ * f ⟨1, by omega⟩ * f ⟨2, by omega⟩ * f ⟨3, by omega⟩ *
      f ⟨4, by omega⟩ := by
  subst hk
  simp [List.ofFn_succ, mul_assoc]

@[expose] def prod5 (n : ℕ) (L : Array Level) (a b c d e : ℕ) : Array ℕ :=
  compA n (compA n (compA n (compA n L[0]!.tr[a]! L[1]!.tr[b]!) L[2]!.tr[c]!) L[3]!.tr[d]!)
    L[4]!.tr[e]!

@[expose] def all5 (n : ℕ) (L : Array Level) (p : Array ℕ → Bool) : Bool :=
  allLt L[0]!.pts.size fun a => allLt L[1]!.pts.size fun b => allLt L[2]!.pts.size fun c =>
    allLt L[3]!.pts.size fun d => allLt L[4]!.pts.size fun e => p (prod5 n L a b c d e)

@[expose] def survivors5 (n : ℕ) (L : Array Level) (p : Array ℕ → Bool) : List (Array ℕ) :=
  (List.range L[0]!.pts.size).flatMap fun a => (List.range L[1]!.pts.size).flatMap fun b =>
    (List.range L[2]!.pts.size).flatMap fun c => (List.range L[3]!.pts.size).flatMap fun d =>
      ((List.range L[4]!.pts.size).map fun e => prod5 n L a b c d e).filter p

@[expose] def commutesAll (n : ℕ) (a : Array ℕ) (gens : Array (Array ℕ)) : Bool :=
  allLt gens.size fun i => eqA n (compA n a gens[i]!) (compA n gens[i]! a)

theorem commutesAll_iff {a : Array ℕ} {g : Equiv.Perm (Fin n)} (ha : Rep n a g)
    {gens : Array (Array ℕ)} {gs : ℕ → Equiv.Perm (Fin n)}
    (hgs : ∀ i < gens.size, Rep n gens[i]! (gs i)) :
    commutesAll n a gens = true ↔ ∀ i < gens.size, g * gs i = gs i * g := by
  rw [commutesAll, allLt_iff]
  exact forall_congr' fun i => imp_congr_right fun hi =>
    eqA_iff (rep_compA ha (hgs i hi)) (rep_compA (hgs i hi) ha)

theorem all5_spec {Q : RawSchreierDatum n} {O S : Array (Array ℕ)} {base : Array ℕ}
    {W : Array (List ℤ)} {chunks : ℕ} (hA : ChainArrays Q O S base W) (hc : 0 < chunks)
    (h : rawChainOK n O S base W chunks = true) (h5 : Q.baseCount = 5) {p : Array ℕ → Bool}
    (hp : all5 n (rawLevels n S base) p = true) {g : Equiv.Perm (Fin n)}
    (hg : g ∈ Q.originalSubgroup) : ∃ a, Rep n a g ∧ p a = true := by
  have hF := chainCheckFacts h
  obtain ⟨c, hc', hprod⟩ := exists_levT_prod hA hc h hg
  have hrep : ∀ i (hi : i < Q.baseCount), Rep n (lev n S base i).tr[c ⟨i, hi⟩]!
      (levT n S base i (c ⟨i, hi⟩)) := fun i hi => hA.rep_levT hF hi (hc' ⟨i, hi⟩)
  have hlev : ∀ i, lev n S base i = (rawLevels n S base)[i]! := fun i => rfl
  refine ⟨prod5 n (rawLevels n S base) (c ⟨0, by omega⟩) (c ⟨1, by omega⟩) (c ⟨2, by omega⟩)
    (c ⟨3, by omega⟩) (c ⟨4, by omega⟩), ?_, ?_⟩
  · rw [← hprod, prod_ofFn_five h5]
    exact rep_compA (rep_compA (rep_compA (rep_compA (hrep 0 (by omega)) (hrep 1 (by omega)))
      (hrep 2 (by omega))) (hrep 3 (by omega))) (hrep 4 (by omega))
  · have := allLt_spec (allLt_spec (allLt_spec (allLt_spec (allLt_spec hp
      (hc' ⟨0, by omega⟩)) (hc' ⟨1, by omega⟩)) (hc' ⟨2, by omega⟩)) (hc' ⟨3, by omega⟩))
      (hc' ⟨4, by omega⟩)
    exact this

end CFSG.Sporadic.Schreier.Tits
