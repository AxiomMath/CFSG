module

public import CFSG.OddTranspositions.PartThree.Twelve.FiveDefs
public import CFSG.OddTranspositions.PartFour.Fourteen.FiveEichler
import CFSG.OddTranspositions.PartThree.Twelve.FiveChartBasic
import CFSG.OddTranspositions.PartThree.CommSetConj
public import CFSG.RankThree.GF2n.Tim79aSec2

public section

namespace CFSG.OddTranspositions.PartThree

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open CFSG.Timmesfeld.Bridge CFSG.OddTranspositions.PartFour
  PartFour.TableE1Five PartFour.FiveEichler

variable {G : Type} [Group G] {D : Set G}

namespace FiveChart

variable {hC : HypothesisC D} {n : ℕ}

@[expose] def ActsAsEich (c : FiveChart hC n) (e β : Fin n → ZMod 5) (g : G) : Prop :=
  ∀ y ∈ commSet D hC.d,
    c.vec (g * y * g⁻¹) = eich c.b e β (c.vec y) ∨ c.vec (g * y * g⁻¹) = -eich c.b e β (c.vec y)

private theorem vec_mul_conj_eq_act (c : FiveChart hC n) {x x' y : G}
    (hx : x ∈ commSet D hC.d) (hx' : x' ∈ commSet D hC.d) (hy : y ∈ commSet D hC.d) :
    c.vec ((x * x') * y * (x * x')⁻¹) =
        act (refl c.b (c.vec x)) (act (refl c.b (c.vec x')) (c.vec y)) ∨
      c.vec ((x * x') * y * (x * x')⁻¹) =
        -act (refl c.b (c.vec x)) (act (refl c.b (c.vec x')) (c.vec y)) := by
  have hz : x' * y * x'⁻¹ ∈ commSet D hC.d :=
    conj_mem_commSet_of_commute hC.setup.normal hx'.2.1 hy
  have hgroup : (x * x') * y * (x * x')⁻¹ = x * (x' * y * x'⁻¹) * x⁻¹ := by group
  rw [hgroup]
  rcases c.vec_conj_eq_act hx' hy with h2 | h2
  · rcases c.vec_conj_eq_act hx hz with h1 | h1
    · left
      rw [h1, h2]
    · right
      rw [h1, h2]
  · rcases c.vec_conj_eq_act hx hz with h1 | h1
    · right
      rw [h1, h2, act_neg]
    · left
      rw [h1, h2, act_neg, neg_neg]

private theorem mem_inter_commSet_of_vec (c : FiveChart hC n) {w v₀ : G}
    (hwd : ¬ Commute w hC.d) (hv₀ : v₀ ∈ commSet D hC.d ∩ commSet D w)
    {e q : Fin n → ZMod 5} (hqe : c.b q e = 0)
    (hqv₀ : c.b q (c.vec v₀) = 0)
    (hP : ∀ x ∈ commSet D hC.d ∩ commSet D v₀, (Commute x w ↔ c.b (c.vec x) e = 0))
    {x : G} (hx : x ∈ commSet D hC.d) (hxv : c.vec x = q ∨ c.vec x = -q) :
    x ∈ commSet D hC.d ∩ commSet D w := by
  have hxv₀ : c.b (c.vec x) (c.vec v₀) = 0 := by
    rcases hxv with h | h
    · rw [h, hqv₀]
    · rw [h, LinearMap.BilinForm.neg_left, hqv₀, neg_zero]
  have hxe : c.b (c.vec x) e = 0 := by
    rcases hxv with h | h
    · rw [h, hqe]
    · rw [h, LinearMap.BilinForm.neg_left, hqe, neg_zero]
  have hxne : x ≠ v₀ := by
    intro h
    have h1 : c.b (c.vec x) (c.vec v₀) = 1 := by rw [h, c.norm_vec v₀ hv₀.1]
    rw [h1] at hxv₀
    exact (by decide : (1 : ZMod 5) ≠ 0) hxv₀
  have hxv₀mem : x ∈ commSet D v₀ :=
    ⟨hx.1, (c.commute_iff x hx v₀ hv₀.1 hxne).2 hxv₀, hxne⟩
  have hcw : Commute x w := (hP x ⟨hx, hxv₀mem⟩).2 hxe
  have hxw : x ≠ w := by
    intro h
    exact hwd (h ▸ hx.2.1)
  exact ⟨hx, ⟨hx.1, hcw, hxw⟩⟩

private theorem exists_signed_vec_of_vec_eq_pm (c : FiveChart hC n) {e q v : Fin n → ZMod 5}
    {s : ZMod 5} {x : G} (hxq : c.vec x = q ∨ c.vec x = -q) (hq : c.b q q = 1)
    (hqe : c.b q e = 0) (hqv : c.b q v = 0) :
    ∃ sx : ZMod 5, ∃ qx : Fin n → ZMod 5,
      c.vec x = qx ∧ sx • qx = s • q ∧ c.b qx qx = 1 ∧ c.b qx e = 0 ∧
        c.b qx v = 0 := by
  rcases hxq with h | h
  · exact ⟨s, q, h, rfl, hq, hqe, hqv⟩
  · refine ⟨-s, -q, h, ?_, ?_, ?_, ?_⟩
    · rw [neg_smul, smul_neg, neg_neg]
    · rw [LinearMap.BilinForm.neg_left, LinearMap.BilinForm.neg_right, hq, neg_neg]
    · rw [LinearMap.BilinForm.neg_left, hqe, neg_zero]
    · rw [LinearMap.BilinForm.neg_left, hqv, neg_zero]

private theorem actsAsEich_mul_of_vec_eq_pm (c : FiveChart hC n) {e p : Fin n → ZMod 5}
    {x x' : G} (hx : x ∈ commSet D hC.d) (hx' : x' ∈ commSet D hC.d)
    (hxp : c.vec x = p) (hpe : c.b p e = 0) (hpp : c.b p p = 1) (he : c.b e e = 0)
    {t : ZMod 5} (hx'v : c.vec x' = p + t • e ∨ c.vec x' = -(p + t • e)) :
    c.ActsAsEich e ((2 * t) • p) (x * x') := by
  intro y hy
  have hvec := vec_mul_conj_eq_act c hx hx' hy
  have hrefl : refl c.b (c.vec x') = refl c.b (p + t • e) := by
    rcases hx'v with h | h
    · rw [h]
    · rw [h, refl_neg]
  have hcomp : act (refl c.b p) (act (refl c.b (c.vec x')) (c.vec y)) =
      eich c.b e ((2 * t) • p) (c.vec y) := by
    rw [hrefl, act_refl_act_refl c.hsym hpp hpe he t]
  rw [hxp] at hvec
  rcases hvec with h | h
  · left
    rw [h, hcomp]
  · right
    rw [h, hcomp]

private theorem exists_actsAsEich_smul_of_norm_one (c : FiveChart hC n) {w v₀ : G}
    (hwd : ¬ Commute w hC.d) {e : Fin n → ZMod 5}
    (hv₀ : v₀ ∈ commSet D hC.d ∩ commSet D w)
    (he : c.b e e = 0) (hev₀ : c.b e (c.vec v₀) = 0)
    (hP : ∀ x ∈ commSet D hC.d ∩ commSet D v₀, (Commute x w ↔ c.b (c.vec x) e = 0))
    {q : Fin n → ZMod 5} (hq : c.b q q = 1) (hqv₀ : c.b q (c.vec v₀) = 0)
    (hqe : c.b q e = 0) (s : ZMod 5) :
    ∃ g ∈ Subgroup.closure (commSet D hC.d ∩ commSet D w), c.ActsAsEich e (s • q) g := by
  have h23 : (2 * 3 : ZMod 5) = 1 := by decide
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨x, hx, hxq⟩ := c.exists_vec q hq
  obtain ⟨sx, qx, hxqx, hsxq, hqxnorm, hqxe, hqxv₀⟩ :=
    exists_signed_vec_of_vec_eq_pm c (v := c.vec v₀) hxq hq hqe hqv₀
  set t : ZMod 5 := 3 * sx with htdef
  have ht2' : (2 : ZMod 5) * t = sx := by
    rw [htdef, ← mul_assoc, h23, one_mul]
  have hnorm : c.b (qx + t • e) (qx + t • e) = 1 := by
    calc c.b (qx + t • e) (qx + t • e)
        = c.b qx qx + t * c.b qx e + t * c.b e qx + t * t * c.b e e := by
          rw [LinearMap.BilinForm.add_left, LinearMap.BilinForm.add_right,
            LinearMap.BilinForm.add_right, LinearMap.BilinForm.smul_left,
            LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right,
            LinearMap.BilinForm.smul_right]
          ring
      _ = 1 := by
          rw [c.hsym e qx, hqxe, hqxnorm, he]
          ring
  obtain ⟨x', hx', hx'v⟩ := c.exists_vec (qx + t • e) hnorm
  have hqe' : c.b (qx + t • e) e = 0 := by
    rw [LinearMap.BilinForm.add_left, LinearMap.BilinForm.smul_left, hqxe, he]
    ring
  have hqv₀' : c.b (qx + t • e) (c.vec v₀) = 0 := by
    rw [LinearMap.BilinForm.add_left, LinearMap.BilinForm.smul_left, hqxv₀, hev₀]
    ring
  have hxS : x ∈ commSet D hC.d ∩ commSet D w :=
    mem_inter_commSet_of_vec c hwd hv₀ hqxe hqxv₀ hP hx (Or.inl hxqx)
  have hx'S : x' ∈ commSet D hC.d ∩ commSet D w := by
    rcases hx'v with h | h
    · exact mem_inter_commSet_of_vec c hwd hv₀ hqe' hqv₀' hP hx' (Or.inl h)
    · exact mem_inter_commSet_of_vec c hwd hv₀ hqe' hqv₀' hP hx' (Or.inr h)
  refine ⟨x * x', Subgroup.mul_mem _ (Subgroup.subset_closure hxS)
    (Subgroup.subset_closure hx'S), ?_⟩
  have harg : (2 * t) • qx = s • q := by
    rw [ht2', hsxq]
  simpa [harg] using actsAsEich_mul_of_vec_eq_pm c hx hx' hxqx hqxe hqxnorm he hx'v

theorem actsAsEich_one (c : FiveChart hC n) (e : Fin n → ZMod 5) : c.ActsAsEich e 0 1 := by
  intro y _
  left
  rw [one_mul, inv_one, mul_one, eich_zero]

theorem ActsAsEich.mul {c : FiveChart hC n} {e β β' : Fin n → ZMod 5} {g g' : G}
    (hg : c.ActsAsEich e β g) (hg' : c.ActsAsEich e β' g') (hg'd : Commute g' hC.d)
    (he : c.b e e = 0) (hβ : c.b β e = 0) (hβ' : c.b β' e = 0) :
    c.ActsAsEich e (β + β') (g * g') := by
  intro y hy
  have hy' : g' * y * g'⁻¹ ∈ commSet D hC.d :=
    conj_mem_commSet_of_commute hC.setup.normal hg'd hy
  have h1 := hg (g' * y * g'⁻¹) hy'
  have hgroup : (g * g') * y * (g * g')⁻¹ = g * (g' * y * g'⁻¹) * g⁻¹ := by group
  rw [hgroup]
  rcases hg' y hy with h2 | h2
  · have hcomb : eich c.b e β (c.vec (g' * y * g'⁻¹)) =
        eich c.b e (β + β') (c.vec y) := by
      rw [h2, eich_eich c.hsym he hβ hβ']
    rcases h1 with h1 | h1
    · left
      rw [h1, hcomb]
    · right
      rw [h1, hcomb]
  · have hcomb : eich c.b e β (c.vec (g' * y * g'⁻¹)) =
        -eich c.b e (β + β') (c.vec y) := by
      rw [h2, eich_neg, eich_eich c.hsym he hβ hβ']
    rcases h1 with h1 | h1
    · right
      rw [h1, hcomb]
    · left
      rw [h1, hcomb, neg_neg]

theorem ActsAsEich.inv {c : FiveChart hC n} {e β : Fin n → ZMod 5} {g : G}
    (hg : c.ActsAsEich e β g) (hgd : Commute g hC.d) (he : c.b e e = 0) (hβ : c.b β e = 0) :
    c.ActsAsEich e (-β) g⁻¹ := by
  intro y hy
  simp only [inv_inv]
  have hz : g⁻¹ * y * g ∈ commSet D hC.d := by
    simpa using conj_mem_commSet_of_commute hC.setup.normal (g := g⁻¹) hgd.inv_left hy
  have h := hg (g⁻¹ * y * g) hz
  have hzy : g * (g⁻¹ * y * g) * g⁻¹ = y := by group
  rw [hzy] at h
  have hnegβ : c.b (-β) e = 0 := by
    rw [LinearMap.BilinForm.neg_left, hβ, neg_zero]
  rcases h with h | h
  · left
    rw [h, eich_eich c.hsym he hnegβ hβ, show -β + β = 0 by abel, eich_zero]
  · right
    rw [h, eich_neg, eich_eich c.hsym he hnegβ hβ, show -β + β = 0 by abel, eich_zero, neg_neg]

theorem ActsAsEich.pow {c : FiveChart hC n} {e β : Fin n → ZMod 5} {g : G}
    (hg : c.ActsAsEich e β g) (hgd : Commute g hC.d) (he : c.b e e = 0) (hβ : c.b β e = 0)
    (m : ℕ) : c.ActsAsEich e (m • β) (g ^ m) := by
  induction m with
  | zero => simpa using actsAsEich_one c e
  | succ m ih =>
      have hβm : c.b (m • β) e = 0 := by
        rw [← Nat.cast_smul_eq_nsmul (R := ZMod 5) m β]
        rw [LinearMap.BilinForm.smul_left, hβ, mul_zero]
      have hmul := ActsAsEich.mul (c := c) (e := e) (β := m • β) (β' := β) (g := g ^ m)
        (g' := g) ih hg hgd he hβm hβ
      rw [pow_succ]
      simpa [succ_nsmul, add_mul, one_mul] using hmul

theorem ActsAsEich.conj_eq_of_zero {c : FiveChart hC n} {e : Fin n → ZMod 5} {g : G}
    (hg : c.ActsAsEich e 0 g) (hgd : Commute g hC.d) {y : G} (hy : y ∈ commSet D hC.d) :
    g * y * g⁻¹ = y := by
  have hmem : g * y * g⁻¹ ∈ commSet D hC.d :=
    conj_mem_commSet_of_commute hC.setup.normal hgd hy
  have h := hg y hy
  rw [eich_zero] at h
  exact c.eq_of_vec y hy (g * y * g⁻¹) hmem h

theorem exists_actsAsEich_of_local (c : FiveChart hC n) (hn : 5 ≤ n) {w v₀ : G}
    (hwd : ¬ Commute w hC.d) {e : Fin n → ZMod 5} (hv₀ : v₀ ∈ commSet D hC.d ∩ commSet D w)
    (he : c.b e e = 0) (he0 : e ≠ 0) (hev₀ : c.b e (c.vec v₀) = 0)
    (hP : ∀ x ∈ commSet D hC.d ∩ commSet D v₀, (Commute x w ↔ c.b (c.vec x) e = 0))
    {β : Fin n → ZMod 5} (hβv₀ : c.b β (c.vec v₀) = 0) (hβe : c.b β e = 0) :
    ∃ g ∈ Subgroup.closure (commSet D hC.d ∩ commSet D w), c.ActsAsEich e β g := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hv₀norm : c.b (c.vec v₀) (c.vec v₀) = 1 := c.norm_vec v₀ hv₀.1
  obtain ⟨p, hpv₀, hpe, hpp⟩ :=
    exists_norm_perp_of_singular c.hsym c.hnd hn hv₀norm he he0 hev₀ 1
  obtain ⟨s, t, ht, hnorm⟩ := exists_add_smul_norm_sq c.hsym hpp β
  set q : Fin n → ZMod 5 := t⁻¹ • (β + s • p) with hqdef
  have hqnorm : c.b q q = 1 := by
    rw [hqdef, LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right, hnorm]
    rw [show t⁻¹ * (t⁻¹ * (t * t)) = (t⁻¹ * t) * (t⁻¹ * t) by ring,
      inv_mul_cancel₀ ht, one_mul]
  have hqv₀ : c.b q (c.vec v₀) = 0 := by
    rw [hqdef, LinearMap.BilinForm.smul_left, LinearMap.BilinForm.add_left,
      LinearMap.BilinForm.smul_left, hβv₀, hpv₀]
    ring
  have hqe : c.b q e = 0 := by
    rw [hqdef, LinearMap.BilinForm.smul_left, LinearMap.BilinForm.add_left,
      LinearMap.BilinForm.smul_left, hβe, hpe]
    ring
  obtain ⟨g₁, hg₁L, hg₁⟩ :=
    exists_actsAsEich_smul_of_norm_one c hwd hv₀ he hev₀ hP hpp hpv₀ hpe (-s)
  obtain ⟨g₂, hg₂L, hg₂⟩ :=
    exists_actsAsEich_smul_of_norm_one c hwd hv₀ he hev₀ hP hqnorm hqv₀ hqe t
  refine ⟨g₁ * g₂, Subgroup.mul_mem _ hg₁L hg₂L, ?_⟩
  have hg₂d : Commute g₂ hC.d :=
    OddLocal.commute_of_mem_closure_commSet (Subgroup.closure_mono Set.inter_subset_left hg₂L)
  have hβ₁ : c.b ((-s) • p) e = 0 := by
    rw [LinearMap.BilinForm.smul_left, hpe, mul_zero]
  have hβ₂ : c.b (t • q) e = 0 := by
    rw [LinearMap.BilinForm.smul_left, hqe, mul_zero]
  have hg₁' : c.ActsAsEich e (-(s • p)) g₁ := by
    simpa [neg_smul] using hg₁
  have hβ₁' : c.b (-(s • p)) e = 0 := by
    simpa [neg_smul] using hβ₁
  have htq : t • q = β + s • p := by
    rw [hqdef, smul_smul, mul_inv_cancel₀ ht, one_smul]
  have hβeq : -(s • p) + t • q = β := by
    have h1 : -(s • p) + s • p = 0 := by rw [neg_add_cancel]
    calc -(s • p) + t • q = -(s • p) + (β + s • p) := by rw [htq]
      _ = (-(s • p) + s • p) + β := by abel
      _ = β := by rw [h1, zero_add]
  have hmul := ActsAsEich.mul (c := c) (e := e) (β := -(s • p)) (β' := t • q) (g := g₁)
    (g' := g₂) hg₁' hg₂ hg₂d he hβ₁' hβ₂
  simpa [hβeq] using hmul

theorem exists_actsAsEich (c : FiveChart hC n) (hn : 5 ≤ n) {w v₀ : G}
    (hwd : ¬ Commute w hC.d) {e : Fin n → ZMod 5} (hv₀ : v₀ ∈ commSet D hC.d ∩ commSet D w)
    (he : c.b e e = 0) (he0 : e ≠ 0) (hev₀ : c.b e (c.vec v₀) = 0)
    (hP : ∀ u ∈ commSet D hC.d ∩ commSet D w,
      ∀ x ∈ commSet D hC.d ∩ commSet D u, (Commute x w ↔ c.b (c.vec x) e = 0))
    {β : Fin n → ZMod 5} (hβe : c.b β e = 0) :
    ∃ g ∈ Subgroup.closure (commSet D hC.d ∩ commSet D w), c.ActsAsEich e β g := by
  have hv₀norm : c.b (c.vec v₀) (c.vec v₀) = 1 := c.norm_vec v₀ hv₀.1
  have hβv₀sym : c.b (c.vec v₀) e = 0 := by
    rw [c.hsym]
    exact hev₀
  set s : ZMod 5 := c.b β (c.vec v₀) with hsdef
  set β' : Fin n → ZMod 5 := β - s • c.vec v₀ with hβ'def
  have hβ'v₀ : c.b β' (c.vec v₀) = 0 := by
    rw [hβ'def, LinearMap.BilinForm.sub_left, LinearMap.BilinForm.smul_left, hv₀norm, hsdef]
    ring
  have hβ'e : c.b β' e = 0 := by
    rw [hβ'def, LinearMap.BilinForm.sub_left, LinearMap.BilinForm.smul_left, hβv₀sym, hβe]
    ring
  obtain ⟨g', hg'L, hg'⟩ :=
    exists_actsAsEich_of_local c hn hwd hv₀ he he0 hev₀ (hP v₀ hv₀) hβ'v₀ hβ'e
  obtain ⟨p, hpv₀, hpe, hpp⟩ :=
    exists_norm_perp_of_singular c.hsym c.hnd hn hv₀norm he he0 hev₀ 1
  obtain ⟨u, hu, huq⟩ := c.exists_vec p hpp
  have huS : u ∈ commSet D hC.d ∩ commSet D w := by
    rcases huq with h | h
    · exact mem_inter_commSet_of_vec c hwd hv₀ hpe hpv₀ (hP v₀ hv₀) hu (Or.inl h)
    · exact mem_inter_commSet_of_vec c hwd hv₀ hpe hpv₀ (hP v₀ hv₀) hu (Or.inr h)
  have heu : c.b e (c.vec u) = 0 := by
    rcases huq with h | h
    · rw [h, c.hsym e p, hpe]
    · rw [h, LinearMap.BilinForm.neg_right, c.hsym e p, hpe, neg_zero]
  have hβ₁ : c.b (s • c.vec v₀) (c.vec u) = 0 := by
    have h : c.b (c.vec v₀) (c.vec u) = 0 := by
      rcases huq with h | h
      · rw [h, c.hsym (c.vec v₀) p, hpv₀]
      · rw [h, LinearMap.BilinForm.neg_right, c.hsym (c.vec v₀) p, hpv₀, neg_zero]
    rw [LinearMap.BilinForm.smul_left, h, mul_zero]
  have hβ₂ : c.b (s • c.vec v₀) e = 0 := by
    rw [LinearMap.BilinForm.smul_left, hβv₀sym, mul_zero]
  obtain ⟨g'', hg''L, hg''⟩ :=
    exists_actsAsEich_of_local c hn hwd huS he he0 heu (hP u huS) hβ₁ hβ₂
  have hg''d : Commute g'' hC.d :=
    OddLocal.commute_of_mem_closure_commSet (Subgroup.closure_mono Set.inter_subset_left hg''L)
  have hsum : β' + s • c.vec v₀ = β := by
    rw [hβ'def, sub_add_cancel]
  refine ⟨g' * g'', Subgroup.mul_mem _ hg'L hg''L, ?_⟩
  have hmul := ActsAsEich.mul (c := c) (e := e) (β := β') (β' := s • c.vec v₀) (g := g')
    (g' := g'') hg' hg'' hg''d he hβ'e hβ₂
  simpa [hsum] using hmul

end FiveChart

end CFSG.OddTranspositions.PartThree
