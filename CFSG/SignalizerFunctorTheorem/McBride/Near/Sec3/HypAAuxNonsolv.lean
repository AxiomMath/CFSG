module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec3.Invariance
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec3.HypAAuxQuot
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.AChief.Simple
public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.SemisimpleCommutator

public section

open CFSG.Open
open CFSG.SignalizerFunctorTheorem.McBride.Nonsolv
open CFSG.SignalizerFunctorTheorem.Nonsolvable (simpleComponents IsASimple)
open scoped Pointwise

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Near.HypAAux

variable {Γ : Type u} [Group Γ]

theorem exists_minimal_admits [Finite Γ] {Q Z : Subgroup Γ} (hZ : Z ≠ ⊥) (hZQ : Admits Q Z) :
    ∃ M ≤ Z, M ≠ ⊥ ∧ Admits Q M ∧ ∀ M' ≤ M, Admits Q M' → M' = ⊥ ∨ M' = M := by
  obtain ⟨M, ⟨hMZ, hM0, hMQ⟩, hmin⟩ := (Set.toFinite {M : Subgroup Γ | M ≤ Z ∧ M ≠ ⊥ ∧
    Admits Q M}).exists_minimal ⟨Z, le_rfl, hZ, hZQ⟩
  refine ⟨M, hMZ, hM0, hMQ, fun M' hM'M hM'Q => ?_⟩
  by_cases h : M' = ⊥
  · exact Or.inl h
  · exact Or.inr (le_antisymm hM'M (hmin ⟨hM'M.trans hMZ, h, hM'Q⟩ hM'M))

theorem forall_mul_comm_of_solvable_minimal {Q N : Subgroup Γ} (hN : Admits Q N) (hN0 : N ≠ ⊥)
    (hmin : ∀ M : Subgroup Γ, M ≤ N → Admits Q M → M = ⊥ ∨ M = N)
    (hsol : Group.IsSolvable ↥N) : ∀ x ∈ N, ∀ y ∈ N, x * y = y * x := by
  have : Nontrivial ↥N := (Subgroup.nontrivial_iff_ne_bot N).mpr hN0
  have hlt : ⁅N, N⁆ < N := CFSG.commutator_lt_self_of_isSolvable N
  have hadm : Admits Q ⁅N, N⁆ := by
    rw [admits_iff_map]
    intro g hg
    rw [Subgroup.map_commutator, admits_iff_map.mp hN g hg]
  have hbot : ⁅N, N⁆ = ⊥ := by
    rcases hmin _ hlt.le hadm with h | h
    · exact h
    · exact absurd h hlt.ne
  have hle : N ≤ Subgroup.centralizer (N : Set Γ) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot
  intro x hx y hy
  exact (Subgroup.mem_centralizer_iff.mp (hle hx) y hy).symm

theorem exists_component_le [Finite Γ] {K Z : Subgroup Γ} (hK : IsSemisimple K) (hZK : Z ≤ K)
    (hZ : K ≤ Subgroup.normalizer (Z : Set Γ)) (hZ0 : Z ≠ ⊥) :
    ∃ T ∈ simpleComponents K, T ≤ Z := by
  have hZn : (Z.subgroupOf K).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hZK]
    intro z k hz hk
    exact (Subgroup.mem_normalizer_iff.mp (hZ hk) z).mp hz
  by_contra hcon
  push Not at hcon
  have hcent : ∀ J ∈ lcal K, J ≤ Subgroup.centralizer (Z : Set Γ) := by
    intro J hJ
    by_contra hJc
    have hJsup : J ≤ ⁅K, Z⁆ := by
      rw [commutator_eq_sSup_not_centralized hK (hZK.trans Subgroup.le_normalizer)]
      exact le_sSup ⟨hJ, hJc⟩
    have hcomm : ⁅K, Z⁆ ≤ Z := by
      refine Subgroup.commutator_le.mpr fun k hk z hz => ?_
      have h1 : k * z * k⁻¹ ∈ Z := (Subgroup.mem_normalizer_iff.mp (hZ hk) z).mp hz
      rw [commutatorElement_def]
      exact mul_mem h1 (inv_mem hz)
    rw [hK.lcal_eq] at hJ
    exact hcon J hJ (hJsup.trans hcomm)
  have hKc : K ≤ Subgroup.centralizer (Z : Set Γ) := by
    rw [← (hK.isDirectProduct_lcal).sSup_eq]
    exact sSup_le hcent
  obtain ⟨-, hinf, -⟩ := hK.isDirectPair_of_normal hZK hZn
  have : Z ≤ K ⊓ Subgroup.centralizer (Z : Set Γ) := le_inf hZK (hZK.trans hKc)
  exact hZ0 (le_bot_iff.mp ((le_inf le_rfl this).trans hinf.le))

theorem not_isSolvable_of_normal [Finite Γ] {K Z : Subgroup Γ} (hK : IsSemisimple K)
    (hZK : Z ≤ K) (hZ : K ≤ Subgroup.normalizer (Z : Set Γ)) (hZ0 : Z ≠ ⊥) :
    ¬ Group.IsSolvable ↥Z := by
  intro hsol
  obtain ⟨T, hT, hTZ⟩ := exists_component_le hK hZK hZ hZ0
  have hTsol : Group.IsSolvable ↥T :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hTZ)
  obtain ⟨-, -, hTs, x, hx, y, hy, hxy⟩ := hT
  have := hTs
  exact hxy (congrArg Subtype.val ((IsSimpleGroup.comm_iff_isSolvable (G := ↥T)).mpr hTsol
    ⟨x, hx⟩ ⟨y, hy⟩))

theorem normalizer_le_normalizer_centralizer (F : Subgroup Γ) :
    Subgroup.normalizer (F : Set Γ) ≤
      Subgroup.normalizer ((Subgroup.centralizer (F : Set Γ) : Subgroup Γ) : Set Γ) := by
  have key : ∀ {g : Γ}, g ∈ Subgroup.normalizer (F : Set Γ) → ∀ {x : Γ},
      x ∈ Subgroup.centralizer (F : Set Γ) → g * x * g⁻¹ ∈ Subgroup.centralizer (F : Set Γ) := by
    intro g hg x hx
    rw [Subgroup.mem_centralizer_iff]
    intro f hf
    have hf' : g⁻¹ * f * g ∈ F := (Subgroup.mem_normalizer_iff''.mp hg f).mp hf
    have h1 := Subgroup.mem_centralizer_iff.mp hx _ hf'
    calc f * (g * x * g⁻¹) = g * ((g⁻¹ * f * g) * x) * g⁻¹ := by group
      _ = g * (x * (g⁻¹ * f * g)) * g⁻¹ := by rw [h1]
      _ = (g * x * g⁻¹) * f := by group
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  exact ⟨fun hx => key hg hx, fun hx => by simpa [mul_assoc] using key (inv_mem hg) hx⟩

theorem inf_le_of_nonsolvable_minimal_normal [Finite Γ] {p : ℕ} {H A D D₂ N : Subgroup Γ}
    (hp : p.Prime) (hA : IsElemAbelian p A) (hcop : Nat.Coprime p (Nat.card H))
    (hD : D = H ⊓ Subgroup.centralizer (A : Set Γ))
    (h5 : ∀ X₁ X₂ : Subgroup Γ, X₁ ≤ H → X₂ ≤ H → Admits (D ⊔ A) X₁ → Admits (D ⊔ A) X₂ →
      IsChiefFactorOf (X₁ ⊔ D ⊔ A) X₁ X₂ → ¬ IsSolvableSection X₁ X₂ → X₂ ⊓ D ≤ D₂ →
        X₁ ⊓ D ≤ D₂)
    (hNH : N ≤ H) (hN : Admits (H ⊔ A) N)
    (hmin : ∀ M : Subgroup Γ, M ≤ N → Admits (H ⊔ A) M → M = ⊥ ∨ M = N)
    (hns : ¬ Group.IsSolvable ↥N) : N ⊓ D ≤ D₂ := by
  have hDH : D ≤ H := hD ▸ inf_le_left
  have hDC : D ≤ Subgroup.centralizer (A : Set Γ) := hD ▸ inf_le_right
  have hDmem : ∀ y ∈ H, y ∈ Subgroup.centralizer (A : Set Γ) → y ∈ D := fun y hy hyC =>
    hD ▸ Subgroup.mem_inf.mpr ⟨hy, hyC⟩
  have hnc : ∃ x ∈ N, ∃ y ∈ N, x * y ≠ y * x := by
    by_contra hcon
    push Not at hcon
    exact hns (Group.isSolvable_of_comm fun a b => Subtype.ext (hcon a a.2 b b.2))
  have hss : IsSemisimple N :=
    AChief.isDirectProduct_simpleComponents ⟨hN, hnc, fun M hMN _ hM => hmin M hMN hM⟩
  have hNQ : N ≤ N ⊔ D ⊔ A := le_sup_left.trans le_sup_left
  have hDQ : D ≤ N ⊔ D ⊔ A := le_sup_right.trans le_sup_left
  have hAQ : A ≤ N ⊔ D ⊔ A := le_sup_right
  have hQG : N ⊔ D ⊔ A ≤ H ⊔ A :=
    sup_le (sup_le (hNH.trans le_sup_left) (hDH.trans le_sup_left)) le_sup_right
  have key : ∀ Z : Subgroup Γ, Z ≤ N → Admits (N ⊔ D ⊔ A) Z → Z ⊓ D ≤ D₂ := by
    intro Z
    induction Z using WellFoundedLT.induction with
    | _ Z ih =>
      intro hZN hZQ
      by_cases hZ0 : Z = ⊥
      · rw [hZ0, bot_inf_eq]
        exact bot_le
      obtain ⟨Z₁, hZ₁Z, hZ₁0, hZ₁Q, hZ₁min⟩ := exists_minimal_admits hZ0 hZQ
      have hZ₁N : Z₁ ≤ N := hZ₁Z.trans hZN
      have hZ₁H : Z₁ ≤ H := hZ₁N.trans hNH
      have hNZ₁ : N ≤ Subgroup.normalizer (Z₁ : Set Γ) := hNQ.trans hZ₁Q
      obtain ⟨hcomm, hinf, hsup⟩ := hss.isDirectPair_of_normal hZ₁N
        (by
          rw [Subgroup.normal_subgroupOf_iff hZ₁N]
          intro z k hz hk
          exact (Subgroup.mem_normalizer_iff.mp (hNZ₁ hk) z).mp hz)
      set C : Subgroup Γ := N ⊓ Subgroup.centralizer (Z₁ : Set Γ) with hC
      have hCZ : C ≤ Subgroup.centralizer (Z₁ : Set Γ) := inf_le_right
      have hZ₁ns : ¬ Group.IsSolvable ↥Z₁ := not_isSolvable_of_normal hss hZ₁N hNZ₁ hZ₁0
      have hDZ₁ : Admits (D ⊔ A) Z₁ := (sup_le hDQ hAQ).trans hZ₁Q
      have hbot : ∀ g : Γ, g ∈ Subgroup.normalizer ((⊥ : Subgroup Γ) : Set Γ) := fun g => by
        rw [Subgroup.mem_normalizer_iff]
        intro x
        simp
      have hchief : IsChiefFactorOf (Z₁ ⊔ D ⊔ A) Z₁ ⊥ := by
        refine ⟨⟨bot_le, fun g _ => hbot g⟩, ⟨le_sup_left.trans le_sup_left, ?_⟩,
          bot_lt_iff_ne_bot.mpr hZ₁0, fun K hK _ hKZ => ?_⟩
        · exact sup_le (sup_le Subgroup.le_normalizer (hDQ.trans hZ₁Q)) (hAQ.trans hZ₁Q)
        · have hKQ : Admits (N ⊔ D ⊔ A) K := by
            refine sup_le (sup_le ?_ ?_) ?_
            · rw [← hsup]
              refine sup_le ((le_sup_left.trans le_sup_left).trans hK.2) ?_
              exact (hCZ.trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hKZ))).trans
                (Subgroup.centralizer_le_normalizer _)
            · exact (le_sup_right.trans le_sup_left).trans hK.2
            · exact le_sup_right.trans hK.2
          exact hZ₁min K hKZ hKQ
      have hZ₁A : Z₁ ⊓ D ≤ D₂ := h5 Z₁ ⊥ hZ₁H bot_le hDZ₁ (fun g _ => hbot g) hchief
        (fun hsol => hZ₁ns (isSolvableSection_bot_iff.mp hsol)) (by simp)
      set Z₂ : Subgroup Γ := Z ⊓ Subgroup.centralizer (Z₁ : Set Γ) with hZ₂
      have hCadm : Admits (N ⊔ D ⊔ A) (Subgroup.centralizer (Z₁ : Set Γ)) :=
        hZ₁Q.trans (normalizer_le_normalizer_centralizer Z₁)
      have hZ₂adm : Admits (N ⊔ D ⊔ A) Z₂ := fun g hg =>
        Subgroup.inf_normalizer_le_normalizer_inf ⟨hZQ hg, hCadm hg⟩
      have hZ₂lt : Z₂ < Z := by
        refine lt_of_le_of_ne inf_le_left fun heq => ?_
        have hZC : Z ≤ Subgroup.centralizer (Z₁ : Set Γ) := heq ▸ inf_le_right
        have : Z₁ ≤ Z₁ ⊓ C := le_inf le_rfl (le_inf hZ₁N (hZ₁Z.trans hZC))
        exact hZ₁0 (le_bot_iff.mp (this.trans hinf.le))
      have hZ₂D : Z₂ ⊓ D ≤ D₂ := ih Z₂ hZ₂lt (inf_le_left.trans hZN) hZ₂adm
      have hZ₁C : Z₁ ≤ Subgroup.normalizer (C : Set Γ) :=
        (Subgroup.le_centralizer_iff.mp hCZ).trans (Subgroup.centralizer_le_normalizer _)
      have hZsub : Z ≤ Z₁ ⊔ Z₂ := by
        intro z hz
        have hzN : z ∈ (Z₁ : Set Γ) * (C : Set Γ) := by
          rw [← Subgroup.coe_mul_of_left_le_normalizer_right Z₁ C hZ₁C, hsup]
          exact hZN hz
        obtain ⟨a, ha, c, hc, rfl⟩ := hzN
        have ha' : a ∈ Z₁ := ha
        have hc' : c ∈ C := hc
        have hcZ : c ∈ Z := by
          have := mul_mem (inv_mem (hZ₁Z ha')) hz
          simpa using this
        exact mul_mem (Subgroup.mem_sup_left ha')
          (Subgroup.mem_sup_right (Subgroup.mem_inf.mpr ⟨hcZ, hCZ hc'⟩))
      have hZ₁Z₂ : Z₁ ≤ Subgroup.normalizer (Z₂ : Set Γ) := fun a ha =>
        Subgroup.inf_normalizer_le_normalizer_inf
          ⟨hZQ ((hZ₁N.trans hNQ) ha), normalizer_le_normalizer_centralizer Z₁
            (Subgroup.le_normalizer ha)⟩
      intro x hx
      obtain ⟨a, ha, b, hb, rfl⟩ := HypAAux.exists_mul_of_mem_sup_of_centralizer hp hA
        (hcop.coprime_dvd_right (Subgroup.card_dvd_of_le hZ₁H)) (hAQ.trans hZ₁Q)
        (hAQ.trans hZ₂adm) hZ₁Z₂ (hZsub hx.1) (hDC hx.2)
      have haD : a ∈ D := hDmem a (hZ₁H ha.1) ha.2
      have hbD : b ∈ D := hDmem b ((inf_le_left.trans hZN |>.trans hNH) hb.1) hb.2
      exact mul_mem (hZ₁A (Subgroup.mem_inf.mpr ⟨ha.1, haD⟩))
        (hZ₂D (Subgroup.mem_inf.mpr ⟨hb.1, hbD⟩))
  have hNadm : Admits (N ⊔ D ⊔ A) N := sup_le (sup_le Subgroup.le_normalizer
    ((hDH.trans le_sup_left).trans hN)) (le_sup_right.trans hN)
  exact key N le_rfl hNadm

end CFSG.SignalizerFunctorTheorem.McBride.Near.HypAAux
