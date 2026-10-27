module

public import CFSG.Quasithin.EmptyFaithful.S151XA
public import CFSG.Quasithin.Background.FLcP0Main
public import CFSG.Quasithin.Background.FLcP0Ker
public import CFSG.LieType.Simplicity.Classical

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem FLc.le_normalizer_conjClosure {Z H X : Subgroup G}
    (hZ : X ≤ Subgroup.normalizer (Z : Set G)) (hH : X ≤ Subgroup.normalizer (H : Set G)) :
    X ≤ Subgroup.normalizer (conjClosure Z H : Set G) := by
  have key : ∀ x ∈ X, ∀ y ∈ conjClosure Z H, x * y * x⁻¹ ∈ conjClosure Z H := by
    intro x hx y hy
    induction hy using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨h, hh, z, hz, rfl⟩ := hy
      have h1 : x * h * x⁻¹ ∈ H := (Subgroup.mem_normalizer_iff.mp (hH hx) h).mp hh
      have h2 : x * z * x⁻¹ ∈ Z := (Subgroup.mem_normalizer_iff.mp (hZ hx) z).mp hz
      have := mem_conjClosure h1 h2
      simpa [mul_assoc] using this
    | one => simp
    | mul y y' _ _ ihy ihy' => simpa [mul_assoc] using (conjClosure Z H).mul_mem ihy ihy'
    | inv y _ ih => simpa [mul_assoc] using (conjClosure Z H).inv_mem ih
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · exact key x hx y
  · intro hy
    have := key x⁻¹ (X.inv_mem hx) _ hy
    simpa [mul_assoc] using this

omit [Finite G] in
theorem FLc.le_normalizer_commutator {A B X : Subgroup G}
    (hA : X ≤ Subgroup.normalizer (A : Set G)) (hB : X ≤ Subgroup.normalizer (B : Set G)) :
    X ≤ Subgroup.normalizer ((⁅A, B⁆ : Subgroup G) : Set G) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  have hA' := Subgroup.mem_normalizer_iff_map_conj_eq.mp (hA hx)
  have hB' := Subgroup.mem_normalizer_iff_map_conj_eq.mp (hB hx)
  rw [Subgroup.map_commutator, hA', hB']

theorem nonempty_p0Setup15129 {T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G} {n : ℕ} {W : ℕ → Subgroup G}
    (hc : Ctx15129 T Mc M Z₁ Z₂ V₁ V₂ L) (hF : FlagData15129 T Mc M Z₁ Z₂ V₂ L n W) :
    Nonempty (FLc.P0Setup L (s1516 T Z₁) (uLOf1527 Z₂ L) n W) := by
  have hq := hc.base.ctx.qtfe
  have hM := hc.base.ctx.mf
  have hS := hc.base.ctx.setting
  have hfour := hF.four
  have h7 : ¬ Ce15Seven T Mc M := not_seven_of_four_or_six (Or.inl hfour)
  have hL1520 : IsL1520 T Mc Z₁ L :=
    hc.base.hL.isL1520 hc.base.h18.four (hS.pCore_g1_ne_bot hq hM)
  have hSylL : IsSylowTwoOf (s1516 T Z₁ ⊓ L) L := lemma_15_1_20_sylow hc.base.h18.four hL1520
  have hSN : s1516 T Z₁ ≤ Subgroup.normalizer (L : Set G) := hF.normalizes
  have hdiag := (hS.diagonal (Or.inl hfour) h7).2
  have hSZ2 : s1516 T Z₁ ≤ Subgroup.normalizer (Z₂ : Set G) := by
    intro x hx
    have hx' : x ∈ T ⊓ Subgroup.centralizer (Z₂ : Set G) := by rw [← hdiag]; exact hx
    exact Subgroup.centralizer_le_normalizer _ hx'.2
  have hSU : s1516 T Z₁ ≤ Subgroup.normalizer (uOf1527 Z₂ L : Set G) :=
    FLc.le_normalizer_conjClosure hSZ2 hSN
  have hSUL : s1516 T Z₁ ≤ Subgroup.normalizer (uLOf1527 Z₂ L : Set G) :=
    FLc.le_normalizer_commutator hSU hSN
  obtain ⟨n', hn', hsec⟩ := hc.h28.1
  obtain ⟨α₀, β₀, hLU, hαs, hαk, hβs, hβk, hrel⟩ := FLc.isNaturalSection_data hsec
  have hβi : Function.Injective β₀ := by
    rw [← MonoidHom.ker_eq_bot_iff, hβk, Subgroup.bot_subgroupOf]
  have hcard' : Nat.card ↥(uLOf1527 Z₂ L) = 2 ^ n' := FLc.card_eq_of_bijective hβi hβs
  have hnn : n' = n := Nat.pow_right_injective (le_refl 2) (hcard'.symm.trans hF.flag.1)
  subst hnn
  have hn1 : 1 ≤ n' := by rcases hF.n_eq with h | h <;> omega
  have hn3 : 3 ≤ n' := by rcases hF.n_eq with h | h <;> omega
  obtain ⟨α, β, hαs', hαk', hnorm, hrel'⟩ :=
    FLc.exists_normalized hn1 hSylL α₀ (MulEquiv.ofBijective β₀ ⟨hβi, hβs⟩) hαs hrel
  have hkerα : ∀ a : ↥L, α a = 1 ↔ (a : G) ∈ Subgroup.centralizer (uLOf1527 Z₂ L : Set G) := by
    intro a
    rw [hαk' a, ← MonoidHom.mem_ker, hαk, Subgroup.mem_subgroupOf]
    exact ⟨fun h => h.2, fun h => ⟨a.2, h⟩⟩
  have hsimple : IsSimpleGroup (↥L ⧸ CFSG.pCore 2 ↥L) := by
    rcases hc.base.h26.2 with h | h
    · exact (CFSG.LieType.Simplicity.fam_PSL_simplicity _ 4 2 1 h).2
    · exact (CFSG.LieType.Simplicity.fam_PSL_simplicity _ 5 2 1 h).2
  have hK2 := FLc.kernel_isPGroup (by omega : 2 ≤ n') α hαs' hkerα hsimple
  have hSyl2 : IsSylowTwoOf (s1516 T Z₁) (L ⊔ s1516 T Z₁) :=
    A4.isSylowTwoOf_mono hc.base.h18.four le_sup_right
      (sup_le (le_of_mem_cComp hc.base.hL.comp) (s1516_le_g1 T Z₁))
  exact ⟨⟨α, β, hn3, hαs', (fun a ha => (hkerα a).1 ha), hnorm, hrel', hLU, hSUL,
    (fun s hs l hl => (Subgroup.mem_normalizer_iff.1 (hSN hs) l).1 hl),
    hc.base.h18.four.2.1, hK2, hSyl2,
    (fun k h1 h2 => (hF.flag.2 k h1 h2).1),
    (fun k h1 h2 => (hF.flag.2 k h1 h2).2.1),
    (fun k h1 h2 => (hF.flag.2 k h1 h2).2.2.1)⟩⟩

theorem input15129P0_holds : Input15129P0 := by
  intro G _ _ T Mc M Z₁ Z₂ V₁ V₂ L n W hc hF
  obtain ⟨D⟩ := nonempty_p0Setup15129 hc hF
  have h := D.concl
  rw [hF.w2] at h
  exact h

end CFSG.Quasithin
