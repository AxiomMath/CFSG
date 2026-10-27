module

public import CFSG.RankThree.GF2n.Stroth80.Sec4Bar
public import CFSG.GroupTheory.Fitting.LayerTopBot

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

section

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem normal_of_unique_sl2 {Γ : Type} [Group Γ] [Finite Γ] {q : ℕ} {Y : Subgroup Γ}
    (hYc : IsComponent Y) (hYSL : IsSLModel 2 q ↥Y)
    (hYu : ∀ C : Subgroup Γ, IsComponent C → IsSLModel 2 q ↥C → C = Y) (s : Γ) :
    conjSubgroup s Y = Y := by
  refine hYu _ (isComponent_conjSubgroup s hYc) ?_
  obtain ⟨K, hF, hFin, hK, ⟨e⟩⟩ := hYSL
  exact ⟨K, hF, hFin, hK, ⟨(Subgroup.equivMapOfInjective Y (MulAut.conj s).toMonoidHom
    (MulAut.conj s).injective).symm.trans e⟩⟩

theorem stroth43_of_310 (h34 : Stroth34Statement) (h310 : Stroth310Statement)
    (h44 : Stroth44Statement) (hCQ : ClassicalQuasisimpleStatement) : Stroth43Statement := by
  intro G _ _ M Q Z B hN hc n hw hn hno hgen hY hnE
  classical
  obtain ⟨Y, ⟨hYc, hYSL⟩, hYu⟩ := hY
  have hYu' : ∀ C : Subgroup (Mbar M Q), IsComponent C → IsSLModel 2 (Nat.card Z) ↥C → C = Y :=
    fun C hC hCS => hYu C ⟨hC, hCS⟩
  have hq4 : 4 ≤ Nat.card Z := hc.hyp.q4
  obtain ⟨jj, kk, hZ2, -⟩ := hc.hyp.cp
  have hSL2 : ∀ (K : Type) [Field K] [Finite K], Nat.card K = Nat.card Z →
      CFSG.IsQuasisimple ↥(StatedSL 2 K) := by
    intro K _ _ hK
    haveI : CharP K 2 := charP_two_of_card_eq_two_pow (hK.trans hZ2)
    exact (hCQ K (by rw [hK]; exact hq4)).1 2 le_rfl
  have hcs := hc.compSimple h34 h44 hw hn hno hgen
  have hΛ := hc.swapHyp hw hn hno
  have hYne : Y ≠ ⊥ := ne_bot_of_isComponent hYc
  have hYn : ∀ s : Mbar M Q, conjSubgroup s Y = Y := normal_of_unique_sl2 hYc hYSL hYu'
  have hYnormal : Y.Normal := ⟨fun x hx g => by
    have := (mul_mem_conjSubgroup_iff (g := g) (T := Y)).mpr hx
    rwa [hYn g] at this⟩
  have hΛY : bar M Q (LB M Q B) ≤ Subgroup.normalizer (Y : Set (Mbar M Q)) :=
    fun s _ => conjSubgroup_eq_self_iff.mp (hYn s)
  have hne0 : bar M Q (LB M Q B) ⊓ Y ≠ ⊥ :=
    hc.inter_bar_LB_ne_bot h34 hw hn hno hgen hYc.1 hΛY
  obtain ⟨tb, htb1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne0
  have htbΛ : (tb : Mbar M Q) ∈ bar M Q (LB M Q B) := tb.2.1
  have htbY : (tb : Mbar M Q) ∈ Y := tb.2.2
  have htbne : (tb : Mbar M Q) ≠ 1 := fun h => htb1 (Subtype.ext h)
  obtain ⟨t', ht'LB, ht'mk⟩ := Subgroup.mem_map.mp htbΛ
  have htLB : (t' : G) ∈ LB M Q B := ht'LB
  have htQ : (t' : G) ∉ Q := by
    intro hq
    apply htbne
    rw [← ht'mk]
    exact (QuotientGroup.eq_one_iff t').mpr (Subgroup.mem_subgroupOf.mpr hq)
  have hmk : (QuotientGroup.mk t' : Mbar M Q) = tb := ht'mk
  set 𝒮 : Set (Subgroup (Mbar M Q)) := {C | IsComponent C ∧ C ≠ Y} with h𝒮
  set X : Subgroup (Mbar M Q) := sSup 𝒮 with hX
  obtain ⟨hXcent0, hEX0⟩ := CFSG.WholeGroup.layer_eq_sup_others hYc
  have hXcent : X ≤ Subgroup.centralizer (Y : Set (Mbar M Q)) := hXcent0
  have hEX : layer (Mbar M Q) = Y ⊔ X := hEX0
  have hXY : X ⊓ Y = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxX, hxY⟩
    exact Subgroup.mem_bot.mpr (hcs.eq_one_of_commutes hYc hxY fun y hy =>
      Subgroup.mem_centralizer_iff.mp (hXcent hxX) y hy)
  have hXR : ∀ C ∈ 𝒮, C ≤ bar M Q (Rt M (LB M Q B) (t' : G)) := by
    intro C hC
    refine hc.component_le_bar_Rt h34 hw hn hno hgen hcs hC.1 htLB fun x hx => ?_
    rw [hmk]
    exact comm_of_ne_component hC.1 hYc hC.2 x hx tb htbY
  have hXle : X ≤ bar M Q (Rt M (LB M Q B) (t' : G)) := sSup_le hXR
  have hXne : X ≠ ⊥ := by
    intro h
    apply hnE
    have hE : layer (Mbar M Q) = Y := by rw [hEX, h, sup_bot_eq]
    obtain ⟨K, hF, hFin, hK, ⟨e⟩⟩ := hYSL
    exact ⟨K, hF, hFin, hK, ⟨(MulEquiv.subgroupCongr hE).trans e⟩⟩
  obtain ⟨C₀, hC₀⟩ : 𝒮.Nonempty := by
    rcases Set.eq_empty_or_nonempty 𝒮 with h | h
    · exact absurd (by rw [hX, h, sSup_empty]) hXne
    · exact h
  have hRne : Rt M (LB M Q B) (t' : G) ≠ LB M Q B := by
    intro hRL
    obtain ⟨a, b, hab⟩ := exists_noncomm_of_isComponent hC₀.1
    have hCΛ : C₀ ≤ bar M Q (LB M Q B) := by
      have := hXR C₀ hC₀
      rwa [hRL] at this
    exact hab (Subtype.ext (hΛ.comm _ (hCΛ a.2) _ (hCΛ b.2)))
  obtain ⟨K, hF, hFin, hK2, Gc, hGc, π, hK, hπs, hπk, hcl⟩ :=
    hc.classical_quotient h310 hw hn hno hgen htLB htQ hRne
  have hshape := hcl.shape hCQ (by rw [hK]; exact hq4)
  have hXnorm : ∀ (g : Mbar M Q), ∀ x ∈ X, g * x * g⁻¹ ∈ X := by
    intro g x hx
    have hmap : ∀ C ∈ 𝒮, conjSubgroup g C ∈ 𝒮 := by
      intro C hC
      refine ⟨isComponent_conjSubgroup g hC.1, fun h => hC.2 ?_⟩
      have h1 : conjSubgroup g⁻¹ (conjSubgroup g C) = C := by
        rw [← conjSubgroup_mul_sec4, inv_mul_cancel, conjSubgroup_one_sec4]
      rw [← h1, h, hYn]
    have hle : X ≤ X.comap (MulAut.conj g).toMonoidHom := by
      refine sSup_le fun C hC => ?_
      exact Subgroup.map_le_iff_le_comap.mp (le_sSup (hmap C hC))
    exact hle hx
  have hXnormal : X.Normal := ⟨fun x hx g => hXnorm g x hx⟩
  have hinj : ∀ x : ↥X, π ⟨(x : Mbar M Q), hXle x.2⟩ = 1 → x = 1 := by
    intro x hx
    have h1 := (hπk ⟨(x : Mbar M Q), hXle x.2⟩).mp hx
    have h2 : (x : Mbar M Q) ∈ X ⊓ bar M Q (hc.CN (t' : G)) := ⟨x.2, h1⟩
    rw [hc.sSup_inf_CN_eq_bot h34 hw hn hno hgen hcs htLB 𝒮
      (fun C hC => ⟨hC.1, hXR C hC⟩), Subgroup.mem_bot] at h2
    exact Subtype.ext h2
  have hns : ¬ Group.IsSolvable ↥X := by
    intro hs
    have hC₀X : C₀ ≤ X := le_sSup hC₀
    haveI := hs
    exact not_isSolvable_of_isQuasisimple hC₀.1.1
      (solvable_of_solvable_injective (f := Subgroup.inclusion hC₀X)
        (Subgroup.inclusion_injective hC₀X))
  have hq2 : ∃ k : ℕ, Nat.card Z = 2 ^ k := ⟨jj, hZ2⟩
  have hU := not_sl2_of_normal_of_unique hq2 hSL2 hYu' hYne hXnormal hXY
  haveI : CharP K 2 := hK2
  rcases normal_embedding_cases (hSL2 K hK) (R := bar M Q (Rt M (LB M Q B) (t' : G))) (X := X)
    π hπs hshape hXle (fun r hr x hx => hXnorm r x hx) hinj hns with
    ⟨hq, ⟨e⟩⟩ | he | he
  · refine ⟨X, Y, by rw [sup_comm]; exact hEX.symm, hXY, fun x hx y hy => ?_,
      isQuasisimple_of_mulEquiv' e.symm hq, hYSL⟩
    exact (Subgroup.mem_centralizer_iff.mp (hXcent hx) y hy).symm
  · exact (hU.1 ⟨K, hF, hFin, hK, he⟩).elim
  · exact (hU.2 K hK he).elim

end

end CFSG.RankThree.GF2n.Stroth80
