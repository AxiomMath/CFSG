module

public import CFSG.Quasithin.Recognition.CertPermSimple
public import CFSG.Assembly.Defs

public section

namespace CFSG.Quasithin

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native

theorem mem_closure_iff_siftA {n : ℕ} (hn : 1 ≤ n) {O S : Array (Array ℕ)} {W : Array (List ℤ)}
    {base : List (Fin n)} (hb : base.Nodup) {chunks : ℕ} (hc : 0 < chunks)
    (hOS : O.size ≤ S.size) (hSO : ∀ i < O.size, S[i]! = O[i]!)
    (h : rawChainOK n (S.extract 0 O.size) S (base.map Fin.val).toArray W chunks = true)
    {g : Array ℕ} {G : Equiv.Perm (Fin n)} (hG : Rep n g G) :
    siftA n (rawLevels n S (base.map Fin.val).toArray) (base.map Fin.val).toArray 0 g = true ↔
      G ∈ Subgroup.closure {x | ∃ k < O.size, permOfArr n O[k]! = x} := by
  have hF := chainCheckFacts h
  have hA := chainArrays_ofArrays (hn := hn) (k := O.size) (hk := hOS) (hb := hb) (W := W)
    hF.strong_inv
  have hQ : (RawSchreierDatum.ofArrays n hn S O.size hOS base hb W).originalSubgroup =
      Subgroup.closure {g | ∃ k < O.size, permOfArr n O[k]! = g} := by
    unfold RawSchreierDatum.originalSubgroup
    congr 1
    ext g
    rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, RawSchreierDatum.mem_ofArrays_original]
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact ⟨i, hi, by rw [hSO i hi]⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨i, hi, by rw [hSO i hi]⟩
  rw [← hQ]
  exact siftA_iff_mem_originalSubgroup hA hc h hG

theorem centralizer_eq_one_of_primCheck {n k : ℕ} {S : Array (Array ℕ)}
    {J : Subgroup (Equiv.Perm (Fin n))} {x : ℕ} {labels roots : Array ℕ} {tw hw : Array (List ℤ)}
    (hSinvA : ∀ j < S.size, isInvA n S[j]! (rawInvs n S)[j]! = true)
    (hSJ : ∀ j < S.size, permOfArr n S[j]! ∈ J)
    (h : primCheck n S x labels roots k tw hw = true)
    (hnt : ∀ p < n, p ≠ x → ∃ q < n, q ≠ p ∧ labels[q]! = labels[p]!)
    (c : Equiv.Perm (Fin n)) (hc : ∀ g ∈ J, c * g = g * c) : c = 1 := by
  obtain ⟨hx, htrans, hlab⟩ := primCheck_spec hSinvA hSJ h
  have hcomm : ∀ g ∈ J, ∀ y : Fin n, c (g y) = g (c y) := fun g hg y =>
    congrArg (fun f : Equiv.Perm (Fin n) => f y) (hc g hg)
  have hcx : c ⟨x, hx⟩ = ⟨x, hx⟩ := by
    by_contra hne
    set q := c ⟨x, hx⟩ with hq
    have hfix : ∀ g ∈ J ⊓ MulAction.stabilizer (Equiv.Perm (Fin n)) (⟨x, hx⟩ : Fin n),
        g q = q := by
      intro g hg
      have hgx : g ⟨x, hx⟩ = ⟨x, hx⟩ := MulAction.mem_stabilizer_iff.1 hg.2
      rw [hq, ← hcomm g hg.1, hgx]
    have hqx : (q : ℕ) ≠ x := fun h' => hne (Fin.ext h')
    obtain ⟨q', hq'n, hq'ne, hq'lab⟩ := hnt q q.2 hqx
    obtain ⟨-, r, hr, g, hg, hgr⟩ := hlab q
    obtain ⟨-, r', hr', g', hg', hgr'⟩ := hlab ⟨q', hq'n⟩
    have hrr : r' = r := Fin.ext (by rw [hr', hr]; simp only [hq'lab])
    have hrq : r = q := by
      have h1 := hfix g hg
      have : g r = g q := hgr.trans h1.symm
      exact g.injective this
    rw [hrr, hrq] at hgr'
    have h2 := hfix g' hg'
    apply hq'ne
    have : (⟨q', hq'n⟩ : Fin n) = q := hgr'.symm.trans h2
    exact congrArg Fin.val this
  refine Equiv.ext fun p => ?_
  obtain ⟨g, hg, hgp⟩ := htrans p
  rw [← hgp, hcomm g hg, hcx]
  rfl

theorem exists_outer_of_conj {n : ℕ} {J : Subgroup (Equiv.Perm (Fin n))}
    (π : Equiv.Perm (Fin n)) (hπ : π ∉ J) (hconj : ∀ x ∈ J, π * x * π⁻¹ ∈ J)
    (hcent : ∀ c : Equiv.Perm (Fin n), (∀ g ∈ J, c * g = g * c) → c = 1) :
    ∃ φ : MulAut ↥J, φ ∉ (MulAut.conj : ↥J →* MulAut ↥J).range := by
  let f : ↥J →* ↥J :=
    { toFun := fun x => ⟨π * x * π⁻¹, hconj x x.2⟩
      map_one' := by apply Subtype.ext; simp
      map_mul' := fun x y => by apply Subtype.ext; simp [mul_assoc] }
  have hinj : Function.Injective f := by
    intro x y hxy
    have := congrArg Subtype.val hxy
    simp only [f, MonoidHom.coe_mk, OneHom.coe_mk, mul_left_inj, mul_right_inj] at this
    exact Subtype.ext this
  refine ⟨MulEquiv.ofBijective f (Finite.injective_iff_bijective.1 hinj), ?_⟩
  rintro ⟨g, hg⟩
  have key : ∀ x : ↥J, π * (x : Equiv.Perm (Fin n)) * π⁻¹ =
      (g : Equiv.Perm (Fin n)) * x * (g : Equiv.Perm (Fin n))⁻¹ := by
    intro x
    have h := congrArg (fun φ : MulAut ↥J => ((φ x : ↥J) : Equiv.Perm (Fin n))) hg
    simpa [MulAut.conj_apply, f] using h.symm
  have hc : (g : Equiv.Perm (Fin n))⁻¹ * π = 1 := by
    refine hcent _ fun x hx => ?_
    have h : π * x * π⁻¹ = (g : Equiv.Perm (Fin n)) * x * (g : Equiv.Perm (Fin n))⁻¹ :=
      key ⟨x, hx⟩
    calc (g : Equiv.Perm (Fin n))⁻¹ * π * x
        = (g : Equiv.Perm (Fin n))⁻¹ * (π * x * π⁻¹) * π := by group
      _ = x * ((g : Equiv.Perm (Fin n))⁻¹ * π) := by rw [h]; group
  have hP : π = (g : Equiv.Perm (Fin n)) := by
    have := congrArg ((g : Equiv.Perm (Fin n)) * ·) hc
    simpa using this
  exact hπ (by rw [hP]; exact g.2)

theorem conj_mem_closure_of_gen {G : Type*} [Group G] (π : G) {T : Set G}
    (h : ∀ t ∈ T, π * t * π⁻¹ ∈ Subgroup.closure T) :
    ∀ x ∈ Subgroup.closure T, π * x * π⁻¹ ∈ Subgroup.closure T := by
  intro x hx
  have : (Subgroup.closure T).map (MulAut.conj π).toMonoidHom ≤ Subgroup.closure T := by
    rw [MonoidHom.map_closure]
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨t, ht, rfl⟩
    exact h t ht
  exact this ⟨x, hx, by simp [MulAut.conj_apply]⟩

end CFSG.Quasithin
