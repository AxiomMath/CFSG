module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.PStability
public import CFSG.LocalAnalysis.SectionRank.Ccomm.ElementaryAut

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Walter

open CFSG.SectionRank.Ccomm

variable {p : ℕ} [hp : Fact p.Prime]

theorem isPGroup_closure_pair_of_le_GL_two (hp2 : p ≠ 2) {X : Subgroup (GL (Fin 2) (ZMod p))}
    (hX : BenderSuzuki.HasAbelianSylow 2 X) {x y : GL (Fin 2) (ZMod p)} (hx : x ∈ X)
    (hy : y ∈ X) (hxp : IsPElement p x) (hyp : IsPElement p y) :
    IsPGroup p (Subgroup.closure ({x, y} : Set (GL (Fin 2) (ZMod p)))) := by
  classical
  set C : Subgroup (GL (Fin 2) (ZMod p)) := Subgroup.closure {x, y} with hCdef
  have hCX : C ≤ X := by
    rw [hCdef, Subgroup.closure_le]
    intro z hz
    rcases hz with rfl | rfl
    · exact hx
    · exact hy
  have hxC : x ∈ C := Subgroup.subset_closure (Set.mem_insert x _)
  have hyC : y ∈ C := Subgroup.subset_closure (Set.mem_insert_of_mem x rfl)
  let ρ : Representation (ZMod p) C (Fin 2 → ZMod p) :=
    (Units.coeHom _).comp ((Matrix.GeneralLinearGroup.toLin).toMonoidHom.comp C.subtype)
  have hρ : Function.Injective ρ := by
    intro a b hab
    apply Subtype.ext
    apply Matrix.GeneralLinearGroup.toLin.injective
    exact Units.ext hab
  have hdim : Module.finrank (ZMod p) (Fin 2 → ZMod p) = 2 := Module.finrank_fin_fun _
  have hgen : Subgroup.closure ({⟨x, hxC⟩, ⟨y, hyC⟩} : Set C) = ⊤ := by
    have h := Subgroup.closure_closure_coe_preimage (k := ({x, y} : Set (GL (Fin 2) (ZMod p))))
    convert h using 2
    ext z
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_preimage]
    constructor
    · rintro (rfl | rfl) <;> simp
    · rintro (h | h)
      · exact Or.inl (Subtype.ext h)
      · exact Or.inr (Subtype.ext h)
  have hpodd : Odd p := hp.out.odd_of_ne_two hp2
  have hxp' : IsPElement p (⟨x, hxC⟩ : C) := by
    obtain ⟨n, hn⟩ := hxp
    exact ⟨n, by rw [Subgroup.orderOf_mk, hn]⟩
  have hyp' : IsPElement p (⟨y, hyC⟩ : C) := by
    obtain ⟨n, hn⟩ := hyp
    exact ⟨n, by rw [Subgroup.orderOf_mk, hn]⟩
  have hCsyl : BenderSuzuki.HasAbelianSylow 2 C :=
    (hX.subgroup (C.subgroupOf X)).of_mulEquiv (Subgroup.subgroupOfEquivOfLe hCX)
  exact BenderSuzuki.two_dimensional_generated_pElements_isPGroup_of_abelianSylowTwo ρ hρ hdim
    _ _ hgen hpodd hxp' hyp' hCsyl

theorem eq_one_of_isPElement_mulAut_of_card_le {W : Type*} [Group W] [Finite W]
    (hcomm : ∀ a b : W, a * b = b * a) (hpow : ∀ a : W, a ^ p = 1) {d : ℕ}
    (hcard : Nat.card W = p ^ d) (hd : d ≤ 1) {x : MulAut W} (hxp : IsPElement p x) : x = 1 := by
  obtain ⟨e⟩ := nonempty_mulEquiv_of_elementary hcomm hpow hcard
  obtain ⟨n, hn⟩ := hxp
  have hdvd : orderOf x ∣ Nat.card (MulAut W) := orderOf_dvd_natCard x
  rw [card_mulAut_eq_card_GL e, card_GL_zmod, hn] at hdvd
  have hp1 := hp.out.one_lt
  have hn0 : n = 0 := by
    by_contra hn0
    have hpdvd : p ∣ ∏ i : Fin d, (p ^ d - p ^ (i : ℕ)) :=
      (dvd_pow_self p hn0).trans hdvd
    interval_cases d
    · simp at hpdvd
      omega
    · simp only [Finset.univ_unique, Fin.default_eq_zero, Fin.val_zero, pow_zero, pow_one,
        Finset.prod_singleton] at hpdvd
      have h1 : p ∣ p - 1 + 1 := by
        rw [Nat.sub_add_cancel hp1.le]
      have h2 : p ∣ 1 := (Nat.dvd_add_right hpdvd).1 h1
      exact hp.out.one_lt.ne' (Nat.dvd_one.1 h2)
  rw [hn0, pow_zero] at hn
  exact orderOf_eq_one_iff.mp hn

theorem isPElement_mul_of_le_mulAut (hp2 : p ≠ 2) {W : Type*} [Group W] [Finite W]
    (hcomm : ∀ a b : W, a * b = b * a) (hpow : ∀ a : W, a ^ p = 1) (hcard : Nat.card W ≤ p ^ 2)
    {X : Subgroup (MulAut W)} (hX : BenderSuzuki.HasAbelianSylow 2 X) {x y : MulAut W}
    (hx : x ∈ X) (hy : y ∈ X) (hxp : IsPElement p x) (hyp : IsPElement p y) :
    IsPElement p (x * y) := by
  have hWp : IsPGroup p W := fun w => ⟨1, by rw [pow_one, hpow]⟩
  obtain ⟨d, hd⟩ := hWp.exists_card_eq
  have hd2 : d ≤ 2 := by
    rw [hd] at hcard
    exact (Nat.pow_le_pow_iff_right hp.out.one_lt).1 hcard
  rcases Nat.lt_or_ge d 2 with hlt | hge
  · rw [eq_one_of_isPElement_mulAut_of_card_le hcomm hpow hd (by omega) hxp,
      eq_one_of_isPElement_mulAut_of_card_le hcomm hpow hd (by omega) hyp, mul_one]
    exact ⟨0, by simp⟩
  · have hd2' : d = 2 := le_antisymm hd2 hge
    subst hd2'
    obtain ⟨e⟩ := nonempty_mulEquiv_of_elementary hcomm hpow hd
    set φ := elemAutEquivGL e
    set X' : Subgroup (GL (Fin 2) (ZMod p)) := X.map φ.toMonoidHom
    have hX' : BenderSuzuki.HasAbelianSylow 2 X' :=
      hX.of_mulEquiv (X.equivMapOfInjective φ.toMonoidHom φ.injective)
    have hxp' : IsPElement p (φ x) := by
      obtain ⟨n, hn⟩ := hxp
      exact ⟨n, by rw [MulEquiv.orderOf_eq, hn]⟩
    have hyp' : IsPElement p (φ y) := by
      obtain ⟨n, hn⟩ := hyp
      exact ⟨n, by rw [MulEquiv.orderOf_eq, hn]⟩
    have hC := isPGroup_closure_pair_of_le_GL_two hp2 hX' (Subgroup.mem_map_of_mem _ hx)
      (Subgroup.mem_map_of_mem _ hy) hxp' hyp'
    have hmem : φ (x * y) ∈ Subgroup.closure ({φ x, φ y} : Set (GL (Fin 2) (ZMod p))) := by
      rw [map_mul]
      exact Subgroup.mul_mem _ (Subgroup.subset_closure (Set.mem_insert _ _))
        (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl))
    obtain ⟨k, hk⟩ := hC ⟨φ (x * y), hmem⟩
    have hdvd : orderOf (x * y) ∣ p ^ k := by
      rw [← MulEquiv.orderOf_eq φ, ← Subgroup.orderOf_mk (φ (x * y)) hmem]
      exact orderOf_dvd_of_pow_eq_one hk
    obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow hp.out).1 hdvd
    exact ⟨m, hm⟩

end CFSG.Walter
