module

public import CFSG.Quasithin.Recognition.F112Crit.OddFiveTorusGraph
public import CFSG.Quasithin.Recognition.F112Crit.OddFiveTorusTwins
public import CFSG.Quasithin.Recognition.F112Crit.OddFiveTorusTwo
public import CFSG.Quasithin.Recognition.F112Crit.OddFiveTorusLoc
public import CFSG.Quasithin.Recognition.F112Crit.APrime.S3Gamma1
public import CFSG.Quasithin.Recognition.F112Crit.APrime.S3Transport
public import CFSG.Quasithin.Recognition.F112Crit.APrime.ConcreteA
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3RLab

public section

namespace CFSG.Quasithin.F112Crit

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7

variable {G : Type} [Group G] [Finite G]

open CosetGeom (graph stab ballStab nbrs vtype γ₀ γ₁)

theorem Setting.torusGraph {L₁ L₂ S Z : Subgroup G} (hs : Setting L₁ L₂ S Z)
    {q i : ℕ} (hK : IsBenderQuot (oTwoQuot ↥L₂) q i) (hC : IsCartanQuot (oTwoQuot ↥L₂))
    (hS3 : VS3 L₁) {μ δ : CosetGeom (L₁ ⊔ L₂ ⊔ S) (P₂ L₁ L₂ S) (P₁ L₁ L₂ S)}
    (hμ : vtype μ = false) (hδ : δ ∈ nbrs μ) {X : Subgroup G} (hX : IsEdgeHall μ δ X) :
    TorusGraph X δ := by
  have hG : L₁ ⊔ L₂ ⊔ S = P₂ L₁ L₂ S ⊔ P₁ L₁ L₂ S := hs.toCritAmalgam.amalgam.gen
  have hμδ : (graph _ _ _).Adj μ δ := hδ
  have hXμ : X ≤ stab μ := hX.1.trans inf_le_left
  have hXδ : X ≤ stab δ := hX.1.trans inf_le_right
  have hA := APrime.amalgamS3_of_setting hs.hyp hS3 hs.S_le
  have hLoc := APrime.LocalS3.of_s3Point_γ₁ hA.hyp hA.s3Point_γ₁
  have h3 : ∀ y, vtype y = true → (nbrs y).ncard = 3 := fun y hy => (hLoc.point y hy).ncard_nbrs
  have hXΔ : ∀ v ∈ torusComp X δ, X ≤ stab v := fun v hv => le_stab_of_mem_torusComp hXδ hv
  have hnbrΔ : ∀ y ∈ torusComp X δ, ∃ ν ∈ torusComp X δ, ν ∈ nbrs y := by
    intro y hy
    by_cases hyδ : y = δ
    · subst hyδ
      exact ⟨μ, mem_torusComp_of_adj hXδ (mem_torusComp_self X y) hμδ.symm hXμ, hμδ.symm⟩
    · obtain ⟨u, hu, hadj⟩ := exists_adj_of_mem_torusComp hy hyδ
      exact ⟨u, hu, hadj.symm⟩
  have hsmall : ∀ y ∈ torusComp X δ, vtype y = true → X ≤ ballStab 1 y := by
    intro y hy hyt
    obtain ⟨ν, hν, hνy⟩ := hnbrΔ y hy
    exact le_ballStab_one_of_ncard_nbrs_eq_three hG hX.2.1 (h3 y hyt) hνy (hXΔ y hy) (hXΔ ν hν)
  have hnbr : ∀ y ∈ torusComp X δ, vtype y = true → ∀ e ∈ nbrs y, X ≤ stab e :=
    fun y hy hyt _ he => (hsmall y hy hyt).trans
      (CosetGeom.ballStab_le_stab_of_dist_le (CosetGeom.dist_eq_one_iff_adj.mpr he).le)
  have hHall : ∀ ν, vtype ν = false → ∀ y ∈ nbrs ν, X ≤ stab ν → X ≤ stab y →
      IsEdgeHall ν y X :=
    fun _ hν _ hy hXν hXy => hX.of_le hμ hδ hν hy hXν hXy
  have hpair : ∀ e ∈ torusComp X δ, vtype e = false → ∃ u ∈ nbrs e, ∃ u' ∈ nbrs e, u' ≠ u ∧
      ∀ ε ∈ nbrs e, X ≤ stab ε ↔ ε = u ∨ ε = u' := by
    intro e he het
    obtain ⟨u, hu, hue⟩ := hnbrΔ e he
    obtain ⟨u', hu', hne, hiff⟩ :=
      hs.exists_fixed_nbrs_eq_pair hK hC het hue (hHall e het u hue (hXΔ e he) (hXΔ u hu))
    exact ⟨u, hue, u', hu', hne, hiff⟩
  have hswap : ∀ e ∈ torusComp X δ, vtype e = false → ∀ u ∈ nbrs e, ∀ w ∈ nbrs e, u ≠ w →
      X ≤ stab u → X ≤ stab w →
      ∃ n : ↥(L₁ ⊔ L₂ ⊔ S), (n : G) ∈ Subgroup.normalizer (X : Set G) ∧ n • u = w := by
    intro e he het u hu w hw hne hXu hXw
    obtain ⟨L, hB⟩ := hs.exists_benderLocal hK het
    obtain ⟨T, hTH, hHT, hT, hodd⟩ := hs.exists_normal_two_edge het hu
    obtain ⟨n, hn, -, hnu, -⟩ := hB.exists_normalizer_swap hu hw hne hTH hHT hT hodd
      (hHall e het u hu (hXΔ e he) hXu) hXw
    exact ⟨n, hn, hnu⟩
  have hloc : ∀ y ∈ torusComp X δ, vtype y = true → ∀ e ∈ nbrs y, ∀ e' ∈ nbrs y,
      ∃ n : ↥(L₁ ⊔ L₂ ⊔ S), (n : G) ∈ Subgroup.normalizer (X : Set G) ∧ n • y = y ∧
        n • e = e' := by
    intro y hy hyt e he e' he'
    have hye : (graph _ _ _).Adj e y := (show (graph _ _ _).Adj y e from he).symm
    have het : vtype e = false := CosetGeom.vtype_eq_false_of_adj he hyt
    obtain ⟨T, hTH, hHT, hT, hodd⟩ := hs.exists_normal_two_edge het hye
    exact exists_normalizer_smul_nbrs hye hTH hHT hT hodd
      (hHall e het y hye (hnbr y hy hyt e he) (hXΔ y hy)) (hsmall y hy hyt) he he'
  refine
    { small_le := hsmall
      subdiv := ?_
      trans := fun y hy hyt y' hy' hy't => torusComp_trans_of_swap hXδ hswap hy hyt hy' hy't
      loc := fun y hy hyt e e' he he' => hloc y hy hyt e he e' he' }
  refine
    { bip := ?_
      card_nbrs := ?_
      nbr_mem := fun y hy hyt v hv => mem_torusComp_of_adj hXδ hy hv (hnbr y hy hyt v hv)
      two := ?_
      simple := ?_
      conn := fun u hu v hv => torusComp_reflTransGen hu hv }
  · intro u v huv
    have h := CosetGeom.vtype_ne_of_adj huv
    revert h
    generalize vtype u = a
    generalize vtype v = b
    cases a <;> cases b <;> decide
  · intro y _ hyt
    show Nat.card (nbrs y) = 3
    rw [Nat.card_coe_set_eq]
    exact h3 y hyt
  · intro e he het
    obtain ⟨u, hu, u', hu', hne, hiff⟩ := hpair e he (by simpa using het)
    refine ⟨u, u', hne.symm, fun v => ⟨fun ⟨hvΔ, hev⟩ => (hiff v hev).mp (hXΔ v hvΔ), ?_⟩⟩
    rintro (rfl | rfl)
    · exact ⟨mem_torusComp_of_adj hXδ he hu ((hiff _ hu).mpr (Or.inl rfl)), hu⟩
    · exact ⟨mem_torusComp_of_adj hXδ he hu' ((hiff _ hu').mpr (Or.inr rfl)), hu'⟩
  · intro y hy hyt e₁ e₂ y' h₁ h₂ hy' hne h₁' h₂'
    refine torusComp_simple_of_loc hXδ h3 (fun a b ha hb hab => hs.eq_of_nbrs_eq hK ha hb hab)
      hnbr ?_ hloc hy hyt h₁ h₂ hy' hne h₁' h₂'
    intro e he het u hu w hw w' hw' hXu hXw hXw'
    obtain ⟨a, -, a', -, -, hiff⟩ := hpair e he het
    rcases (hiff u hu).mp hXu with rfl | rfl <;> rcases (hiff w hw).mp hXw with rfl | rfl <;>
      rcases (hiff w' hw').mp hXw' with rfl | rfl <;> simp

end CFSG.Quasithin.F112Crit

end
