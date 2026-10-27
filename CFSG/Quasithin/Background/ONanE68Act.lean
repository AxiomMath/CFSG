module

public import CFSG.Quasithin.Background.ONanE68Setting
public import CFSG.Quasithin.Background.E6EightSmall
public import CFSG.Quasithin.H13.KGFact68Base

public section

namespace CFSG.Quasithin

namespace E6

namespace E68Proof

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.H13.KG68

section Sandwich

variable {G : Type} [Group G] [Finite G] {T M V U L : Subgroup G}

omit [Finite G] in
theorem twoPrimeResidual_le_self (X : Subgroup G) : twoPrimeResidual X ≤ X :=
  iInf₂_le X ⟨le_rfl, Subgroup.le_normalizer, by rw [Subgroup.relIndex_self]; norm_num⟩

theorem sandwich (h : HypE61 T M V) (hU : U ∈ gammaE64 V M)
    (hL : IsComponentIn L (Subgroup.centralizer (U : Set G))) :
    L ⊓ Subgroup.centralizer (V : Set G) ≤ L ⊓ M ∧
      twoPrimeResidual (L ⊓ M) ≤ L ⊓ Subgroup.centralizer (V : Set G) ∧
      L ⊓ M ≤ Subgroup.normalizer (V : Set G) := by
  refine ⟨inf_le_inf_left L h.centralizer_le, ?_, fun x hx =>
    (e6_5_three h hU).2 ⟨hL.1 hx.1, hx.2⟩⟩
  have h1 : twoPrimeResidual (L ⊓ M) ≤ twoPrimeResidual (M ⊓ Subgroup.centralizer (U : Set G)) :=
    twoPrimeResidual_mono (le_inf inf_le_right (inf_le_left.trans hL.1))
  have h2 := h1.trans hU.2.2.2
  exact le_inf ((twoPrimeResidual_le_self _).trans inf_le_left) (h2.trans inf_le_right)

theorem baseHyp (h : HypE61 T M V) (hU : U ∈ gammaE64 V M)
    (hL : IsComponentIn L (Subgroup.centralizer (U : Set G))) :
    E6.E68BaseHyp L V
      ((T ⊓ Subgroup.centralizer (V : Set G)) ⊓ Subgroup.normalizer (L : Set G)) where
  quasisimple := BenderBranch.isQuasisimple_of_isComponentIn hL
  elemAbelian := h.isElemAbelian
  isPGroup := h.isPGroup_Q.to_le inf_le_left
  le := le_inf h.le_inf_centralizer (le_normalizer_of_component h hU hL)
  centralizer := inf_le_left.trans inf_le_right
  normalizer := inf_le_right
  sylow := by
    have hS : IsSylowTwoOf ((T ⊓ Subgroup.centralizer (V : Set G)) ⊓ L) L :=
      RankOneRecog.isSylowTwoOf_inf_of_subnormal (e6_5_one h hU) hL.1 hL.2.2
    rwa [inf_assoc, inf_eq_right.2 (Subgroup.le_normalizer : L ≤ _)]

end Sandwich

section Base

variable {Y : Type} [Group Y] [Finite Y] {L A R : Subgroup Y}

omit [Finite Y] in
theorem leN_base (h : E6.E68BaseHyp L A R) : A ≤ Subgroup.normalizer (L : Set Y) :=
  h.le.trans h.normalizer

@[expose] noncomputable def sylowInB (h : E6.E68BaseHyp L A R) : Sylow 2 ↥L :=
  A4.toSylow h.sylow

omit [Finite Y] in
theorem conjOn_fix_base (h : E6.E68BaseHyp L A R) {a : Y} (ha : a ∈ A) {x : ↥L}
    (hx : x ∈ ((sylowInB h : Sylow 2 ↥L) : Subgroup ↥L)) :
    conjOn L a (leN_base h ha) x = x := by
  apply Subtype.ext
  rw [conjOn_coe]
  have hxR : (x : Y) ∈ R := (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hx)).1
  have hc := Subgroup.mem_centralizer_iff.mp (h.centralizer hxR) a ha
  rw [hc]
  group

omit [Finite Y] in
theorem conjOn_sq_base (h : E6.E68BaseHyp L A R) {a : Y} (ha : a ∈ A) :
    conjOn L a (leN_base h ha) * conjOn L a (leN_base h ha) = 1 := by
  rw [← conjOn_mul, conjOn_eq_one_iff]
  have h2 : a * a = 1 := by
    have := h.elemAbelian.2 a ha
    rwa [pow_two] at this
  rw [h2]
  exact Subgroup.one_mem _

theorem mem_omega_of_conj_base (h : E6.E68BaseHyp L A R) (hZ : Subgroup.center ↥L = ⊥) {a : Y}
    (ha : a ∈ A) {g : ↥L} (hg : conjOn L a (leN_base h ha) = MulAut.conj g) :
    g ∈ ((sylowInB h : Sylow 2 ↥L) : Subgroup ↥L) ∧
      (∀ x ∈ ((sylowInB h : Sylow 2 ↥L) : Subgroup ↥L), g * x = x * g) ∧ g * g = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P := ((sylowInB h : Sylow 2 ↥L) : Subgroup ↥L) with hPdef
  have hgP : ∀ x ∈ P, g * x = x * g := by
    intro x hx
    have h1 := conjOn_fix_base h ha hx
    rw [hg, MulAut.conj_apply] at h1
    calc g * x = (g * x * g⁻¹) * g := by group
      _ = x * g := by rw [h1]
  have hg2 : g * g = 1 := by
    have h1 := conjOn_sq_base h ha
    rw [hg, ← map_mul] at h1
    have h2 : g * g ∈ Subgroup.center ↥L := by
      rw [Subgroup.mem_center_iff]
      intro y
      have h3 := congrArg (fun φ : MulAut ↥L => φ y) h1
      simp only [MulAut.conj_apply, MulAut.one_apply] at h3
      calc y * (g * g) = (g * g * y * (g * g)⁻¹) * (g * g) := by rw [h3]
        _ = g * g * y := by group
    rw [hZ, Subgroup.mem_bot] at h2
    exact h2
  have hgS : g ∈ P := by
    by_cases hg1 : g = 1
    · rw [hg1]
      exact P.one_mem
    have hz2 : IsPGroup 2 (Subgroup.zpowers g) := by
      refine IsPGroup.of_card (n := 1) ?_
      rw [Nat.card_zpowers, orderOf_eq_prime (by rw [sq]; exact hg2) hg1, pow_one]
    have hzN : Subgroup.zpowers g ≤ Subgroup.normalizer (P : Set ↥L) := by
      rw [Subgroup.zpowers_le]
      refine A4.mem_normalizer_of_conj_mem fun x hx => ?_
      have h1 : g * x * g⁻¹ = x := by rw [hgP x hx]; group
      rw [h1]
      exact hx
    have hsup := IsPGroup.to_sup_of_normal_right' hz2 (sylowInB h).isPGroup' hzN
    have heq := (sylowInB h).is_maximal' hsup le_sup_right
    have hmem : g ∈ Subgroup.zpowers g ⊔ P := Subgroup.mem_sup_left (Subgroup.mem_zpowers g)
    rw [heq] at hmem
    exact hmem
  exact ⟨hgS, hgP, hg2⟩

theorem relIndex_le_of_inner_base (h : E6.E68BaseHyp L A R) (hZ : Subgroup.center ↥L = ⊥)
    (hinn : ∀ a (ha : a ∈ A), ∃ g : ↥L, conjOn L a (leN_base h ha) = MulAut.conj g) :
    (A ⊓ Subgroup.centralizer (L : Set Y)).relIndex A ≤
      Nat.card (omegaZ ((sylowInB h : Sylow 2 ↥L) : Subgroup ↥L)) := by
  classical
  rw [relIndex_eq_card_range L A (leN_base h)]
  have key : ∀ φ : ↥(actHom L A (leN_base h)).range,
      ∃ g : omegaZ ((sylowInB h : Sylow 2 ↥L) : Subgroup ↥L),
        (φ : MulAut ↥L) = MulAut.conj (g : ↥L) := by
    rintro ⟨φ, a, rfl⟩
    obtain ⟨g, hg⟩ := hinn a a.2
    exact ⟨⟨g, mem_omega_of_conj_base h hZ a.2 hg⟩, hg⟩
  choose f hf using key
  refine Nat.card_le_card_of_injective f fun φ ψ hφψ => Subtype.ext ?_
  rw [hf φ, hf ψ, hφψ]

end Base

end E68Proof

end E6

end CFSG.Quasithin
