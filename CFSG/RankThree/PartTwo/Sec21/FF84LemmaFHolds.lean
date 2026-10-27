module

public import CFSG.RankThree.PartTwo.Sec21.FF84S3Inputs
public import CFSG.RankThree.PartTwo.Sec21.FF84LemmaFCore

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84

open CFSG CFSG.RankThree.PartTwo.Sec21

theorem exists_normal_elemAbelian_of_pGroup {Γ : Type} [Group Γ] [Finite Γ] (Q : Subgroup Γ)
    [hQn : Q.Normal] (hQ : IsPGroup 2 Q) (hQ1 : Q ≠ ⊥) :
    ∃ E : Subgroup Γ, E.Normal ∧ E ≠ ⊥ ∧ E ≤ Q ∧ (∀ e ∈ E, e * e = 1) ∧
      ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let E : Subgroup Γ :=
    { carrier := {γ | γ ∈ Q ∧ γ * γ = 1 ∧ ∀ q ∈ Q, γ * q = q * γ}
      mul_mem' := by
        rintro a b ⟨haQ, ha2, haC⟩ ⟨hbQ, hb2, hbC⟩
        refine ⟨mul_mem haQ hbQ, ?_, ?_⟩
        · have hab : a * b = b * a := haC b hbQ
          calc a * b * (a * b) = a * (b * a) * b := by group
            _ = a * (a * b) * b := by rw [← hab]
            _ = (a * a) * (b * b) := by group
            _ = 1 := by rw [ha2, hb2, one_mul]
        · intro q hq
          calc a * b * q = a * (b * q) := by group
            _ = a * (q * b) := by rw [hbC q hq]
            _ = (a * q) * b := by group
            _ = (q * a) * b := by rw [haC q hq]
            _ = q * (a * b) := by group
      one_mem' := ⟨one_mem Q, mul_one 1, fun q _ => by simp⟩
      inv_mem' := by
        rintro a ⟨haQ, ha2, haC⟩
        refine ⟨inv_mem haQ, ?_, fun q hq => (Commute.inv_left (haC q hq))⟩
        rw [← mul_inv_rev, ha2, inv_one] }
  have hEmem : ∀ γ : Γ, γ ∈ E ↔ γ ∈ Q ∧ γ * γ = 1 ∧ ∀ q ∈ Q, γ * q = q * γ := fun γ => Iff.rfl
  refine ⟨E, ⟨fun n hn g => ?_⟩, ?_, fun e he => ((hEmem e).1 he).1, fun e he => ((hEmem e).1 he).2.1,
    fun a ha b hb => ((hEmem a).1 ha).2.2 b ((hEmem b).1 hb).1⟩
  · obtain ⟨hnQ, hn2, hnC⟩ := (hEmem n).1 hn
    refine (hEmem _).2 ⟨hQn.conj_mem n hnQ g, ?_, ?_⟩
    · calc g * n * g⁻¹ * (g * n * g⁻¹) = g * (n * n) * g⁻¹ := by group
        _ = 1 := by rw [hn2]; group
    · intro q hq
      have hq' : g⁻¹ * q * g ∈ Q := by
        simpa using hQn.conj_mem q hq g⁻¹
      have := hnC _ hq'
      calc g * n * g⁻¹ * q = g * (n * (g⁻¹ * q * g)) * g⁻¹ := by group
        _ = g * ((g⁻¹ * q * g) * n) * g⁻¹ := by rw [this]
        _ = q * (g * n * g⁻¹) := by group
  ·
    intro hE
    haveI : Nontrivial Q := by
      rw [Subgroup.nontrivial_iff_ne_bot]; exact hQ1
    haveI : Nontrivial (Subgroup.center Q) := hQ.center_nontrivial
    have hcen : IsPGroup 2 (Subgroup.center Q) :=
      hQ.of_injective (Subgroup.center Q).subtype Subtype.val_injective
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hcen
    have hn0 : n ≠ 0 := by
      rintro rfl
      have : Nat.card (Subgroup.center Q) = 1 := by simpa using hn
      exact (Finite.one_lt_card (α := Subgroup.center Q)).ne' this
    obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center Q) 2
      (by rw [hn]; exact dvd_pow_self 2 hn0)
    have hu2 : (u : Q) * u = 1 := by
      have := pow_orderOf_eq_one u
      rw [hu, pow_two] at this
      exact_mod_cast this
    have hu1 : (u : Q) ≠ 1 := by
      intro h1
      have : u = 1 := Subtype.ext h1
      rw [this, orderOf_one] at hu
      omega
    have huE : ((u : Q) : Γ) ∈ E := by
      refine (hEmem _).2 ⟨(u : Q).2, ?_, ?_⟩
      · exact_mod_cast congrArg Subtype.val hu2
      · intro q hq
        have := Subgroup.mem_center_iff.1 u.2 ⟨q, hq⟩
        exact congrArg Subtype.val this.symm
    rw [hE] at huE
    exact hu1 (Subtype.ext (by simpa using huE))

theorem lemmaF_holds : LemmaF := by
  intro G _ _ J Z X N _ y hZJ hZ2 hsimple hcard hyJ hord hX2 hNX hNnorm hJX hJN hfpf
  by_contra hXN
  rw [SetLike.le_def] at hXN
  push Not at hXN
  obtain ⟨x0, hx0X, hx0N⟩ := hXN
  set W : Subgroup G := Nor X ⊓ Nor N with hW
  have hJW : J ≤ W := le_inf hJX hJN
  have hXNor : X ≤ Nor N := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro n
    constructor
    · intro hn
      have := hNnorm.conj_mem ⟨n, hNX hn⟩ hn ⟨x, hx⟩
      exact this
    · intro hn
      have := hNnorm.conj_mem ⟨x * n * x⁻¹, hNX hn⟩ hn ⟨x⁻¹, inv_mem hx⟩
      have h2 : x⁻¹ * (x * n * x⁻¹) * x⁻¹⁻¹ = n := by group
      rw [← h2]
      exact this
  have hXW : X ≤ W := le_inf Subgroup.le_normalizer hXNor
  have hN1 : (N.subgroupOf W).Normal := by
    refine ⟨fun n hn w => ?_⟩
    have hw : (w : G) ∈ Nor N := w.2.2
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact (Subgroup.mem_normalizer_iff.1 hw n).1 hn
  have hX1 : (X.subgroupOf W).Normal := by
    refine ⟨fun n hn w => ?_⟩
    have hw : (w : G) ∈ Nor X := w.2.1
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact (Subgroup.mem_normalizer_iff.1 hw n).1 hn
  let π : ↥W →* ↥W ⧸ N.subgroupOf W := QuotientGroup.mk' (N.subgroupOf W)
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hπker : ∀ w : ↥W, π w = 1 ↔ (w : G) ∈ N := fun w => by
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  set Q : Subgroup (↥W ⧸ N.subgroupOf W) := (X.subgroupOf W).map π with hQdef
  haveI hQn : Q.Normal := Subgroup.Normal.map hX1 π hπ
  have hQ2 : IsPGroup 2 Q := by
    have h1 : IsPGroup 2 (X.subgroupOf W) :=
      hX2.of_equiv (Subgroup.subgroupOfEquivOfLe hXW).symm
    exact h1.of_surjective (π.subgroupMap (X.subgroupOf W))
      (MonoidHom.subgroupMap_surjective _ _)
  have hQ1 : Q ≠ ⊥ := by
    intro hQ
    have hx0W : x0 ∈ W := hXW hx0X
    have hmem : π ⟨x0, hx0W⟩ ∈ Q := Subgroup.mem_map_of_mem _ (by
      rw [Subgroup.mem_subgroupOf]; exact hx0X)
    rw [hQ, Subgroup.mem_bot, hπker] at hmem
    exact hx0N hmem
  obtain ⟨E, hEn, hE1, hEQ, hE2, hEc⟩ := exists_normal_elemAbelian_of_pGroup Q hQ2 hQ1
  letI : CommGroup ↥E :=
    { (inferInstance : Group ↥E) with mul_comm := fun a b => Subtype.ext (hEc a a.2 b b.2) }
  let φ : ↥J →* MulAut ↥E := MulAut.conjNormal.comp (π.comp (Subgroup.inclusion hJW))
  letI : MulDistribMulAction ↥J ↥E := MulDistribMulAction.compHom ↥E φ
  have hsm : ∀ (j : ↥J) (e : ↥E), ((j • e : ↥E) : ↥W ⧸ N.subgroupOf W) =
      π (Subgroup.inclusion hJW j) * e * (π (Subgroup.inclusion hJW j))⁻¹ := by
    intro j e
    have h0 : (j • e : ↥E) = MulAut.conjNormal (π (Subgroup.inclusion hJW j)) e := rfl
    rw [h0, MulAut.conjNormal_apply]
  have hy3' : y ^ 3 = 1 := hord ▸ pow_orderOf_eq_one y
  have hZ : IsPGroup 2 (Z.subgroupOf J) :=
    hZ2.of_equiv (Subgroup.subgroupOfEquivOfLe hZJ).symm
  haveI := hsimple
  have hall : ∀ e : ↥E, e = 1 :=
    eq_one_of_simple168_quotient (J := ↥J) (Z.subgroupOf J) hZ hcard (E := ↥E)
      (fun e => Subtype.ext (hE2 e e.2)) (y := ⟨y, hyJ⟩)
      (Subtype.ext (by simpa using hy3')) (fun e he => by
        have he' := congrArg Subtype.val he
        rw [hsm] at he'
        obtain ⟨w, hwX, hwe⟩ := Subgroup.mem_map.1 (hEQ e.2)
        have h3 : π w = π (Subgroup.inclusion hJW ⟨y, hyJ⟩ * w *
            (Subgroup.inclusion hJW ⟨y, hyJ⟩)⁻¹) := by
          rw [map_mul, map_mul, map_inv, hwe]
          exact he'.symm
        have hn := QuotientGroup.eq.1 h3
        rw [Subgroup.mem_subgroupOf] at hn hwX
        have hwN : (w : G) ∈ N := by
          refine hfpf (w : G) hwX ⟨(w : G)⁻¹ * (y * (w : G) * y⁻¹), ?_, by group⟩
          simpa using hn
        apply Subtype.ext
        rw [← hwe]
        exact (hπker w).2 hwN)
  obtain ⟨e, he1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hE1
  exact he1 (hall e)

end CFSG.RankThree.PartTwo.Sec21.FF84
