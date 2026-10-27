module

public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.GroupAction.MultipleTransitivity

public section

namespace CFSG

namespace FiveTransitive.OyamaPairCriterion

open MulAction

private theorem invariant_pair_parity
    {G X:Type*} [Group G] [MulAction G X] [Finite X]
    (hG:IsPGroup 2 G) (O:SubMulAction G X) (a b:X)
    (hfix:fixedPoints G X={a,b}) (ha:a∉O) :
    (b∈O → Nat.card O ≡ 1 [MOD 2]) ∧
      (b∉O → Nat.card O ≡ 0 [MOD 2]) := by
  classical
  have hmod := hG.card_modEq_card_fixedPoints O
  have hamb (x:fixedPoints G O):x.val.val∈fixedPoints G X := by
    rw [mem_fixedPoints]
    intro g
    exact congrArg Subtype.val (mem_fixedPoints.mp x.property g)
  constructor
  · intro hb
    let y:O := ⟨b,hb⟩
    have hy:y∈fixedPoints G O := by
      rw [mem_fixedPoints]
      intro g
      apply Subtype.ext
      exact mem_fixedPoints.mp (by rw [hfix]; exact Set.mem_insert_of_mem _ rfl) g
    let : Unique (fixedPoints G O) := {
      default := ⟨y,hy⟩
      uniq := by
        intro x
        apply Subtype.ext
        apply Subtype.ext
        have hx := hamb x
        rw [hfix,Set.mem_insert_iff,Set.mem_singleton_iff] at hx
        rcases hx with hx|hx
        · exact False.elim (ha (hx ▸ x.val.property))
        · exact hx }
    simpa only [Nat.card_unique] using hmod
  · intro hb
    let : IsEmpty (fixedPoints G O) := ⟨by
      intro x
      have hx := hamb x
      rw [hfix,Set.mem_insert_iff,Set.mem_singleton_iff] at hx
      rcases hx with hx|hx
      · exact ha (hx ▸ x.val.property)
      · exact hb (hx ▸ x.val.property)⟩
    simpa only [Nat.card_of_isEmpty] using hmod

private def orbitAction {G X:Type*} [Group G] [MulAction G X]
    (H Q:Subgroup G) (hQ:Q≤H) (b:X) : SubMulAction Q X where
  carrier := orbit H b
  smul_mem' q _ hx := mem_orbit_of_mem_orbit (⟨q.val,hQ q.property⟩:H) hx

private theorem orbit_pair_parity
    {G X:Type*} [Group G] [MulAction G X] [Finite X]
    (H Q:Subgroup G) (hQ:Q≤H) (hP:IsPGroup 2 Q) (a b c:X)
    (hfix:fixedPoints Q X={a,c}) (ha:a∉orbit H b) :
    (c∈orbit H b → Nat.card (orbit H b) ≡ 1 [MOD 2]) ∧
      (c∉orbit H b → Nat.card (orbit H b) ≡ 0 [MOD 2]) :=
  invariant_pair_parity hP (orbitAction H Q hQ b) a c hfix ha

private theorem stabilizer_transitive_complement
    {G X:Type*} [Group G] [MulAction G X] [Finite X]
    (hpair:∀a b:X,a≠b → ∃Q:Subgroup G,IsPGroup 2 Q ∧ fixedPoints Q X={a,b})
    (a b c:X) (hb:b≠a) (hc:c≠a) :
    ∃g:stabilizer G a,g • b=c := by
  have ha:a∉orbit (stabilizer G a) b := by
    rintro ⟨g,hg⟩
    apply hb
    apply MulAction.injective g
    exact hg.trans g.property.symm
  have hle (Q:Subgroup G) (d:X) (hfix:fixedPoints Q X={a,d}) :
      Q≤stabilizer G a := by
    intro q hq
    have hafix:a∈fixedPoints Q X := by rw [hfix]; exact Set.mem_insert _ _
    exact mem_fixedPoints.mp hafix (⟨q,hq⟩:Q)
  by_contra hn
  have hcO:c∉orbit (stabilizer G a) b := hn
  obtain ⟨Q,hQ,hQfix⟩ := hpair a b hb.symm
  have hodd := (orbit_pair_parity (stabilizer G a) Q (hle Q b hQfix)
    hQ a b b hQfix ha).1 (mem_orbit_self b)
  obtain ⟨R,hR,hRfix⟩ := hpair a c hc.symm
  have heven := (orbit_pair_parity (stabilizer G a) R (hle R c hRfix)
    hR a b c hRfix ha).2 hcO
  have hbad : (1:ℕ) ≡ 0 [MOD 2] := hodd.symm.trans heven
  norm_num [Nat.ModEq] at hbad

theorem two_transitive_of_pair_fixed_sets
    {G X:Type*} [Group G] [MulAction G X] [Finite X]
    (hcard:3≤Nat.card X)
    (hpair:∀a b:X,a≠b → ∃Q:Subgroup G,IsPGroup 2 Q ∧ fixedPoints Q X={a,b}) :
    IsMultiplyPretransitive G X 2 := by
  classical
  have htrans (x y:X):∃g:G,g • x=y := by
    let E := Finite.equivFin X
    obtain ⟨z,hzx,hzy⟩ := Fin.exists_ne_and_ne_of_two_lt (E x) (E y) (by omega)
    have hx:x≠E.symm z := by
      intro he
      apply hzx
      rw [he,E.apply_symm_apply]
    have hy:y≠E.symm z := by
      intro he
      apply hzy
      rw [he,E.apply_symm_apply]
    obtain ⟨g,hg⟩ := stabilizer_transitive_complement hpair (E.symm z) x y hx hy
    exact ⟨g.val,hg⟩
  apply is_two_pretransitive_iff.mpr
  intro a b c d hab hcd
  obtain ⟨g,hg⟩ := htrans a c
  have hb:g • b≠c := by
    intro he
    exact hab (MulAction.injective g (hg.trans he.symm))
  obtain ⟨h,hh⟩ := stabilizer_transitive_complement hpair c (g • b) d hb hcd.symm
  refine ⟨h.val*g,?_,?_⟩
  · rw [mul_smul,hg]
    exact h.property
  · rw [mul_smul]
    exact hh

end FiveTransitive.OyamaPairCriterion

end CFSG
