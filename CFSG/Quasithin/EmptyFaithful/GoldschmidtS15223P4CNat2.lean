module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223P4CNat1
public import CFSG.Quasithin.EmptyFaithful.A38c10Mat
public import CFSG.Quasithin.Background.FLc2Rho

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin

open CFSG.Open hiding StatedSL StatedClassicalModel StatedProj StatedLieTag StatedLieAdmissible
open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.FLc
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.LieType.BorelTits
open scoped Pointwise commutatorElement

namespace S15223P4

namespace C

variable {G : Type} [Group G] [Finite G]

theorem relIndex_Theta {L S UL : Subgroup G} {n : ℕ} {W : ℕ → Subgroup G}
    (D : P0Setup L S UL n W) {H : Subgroup G} (hHX : H ≤ L ⊔ S) :
    (Ut n).relIndex (D.Theta H) = S.relIndex H := by
  have hker : D.rho.ker ≤ S.subgroupOf (L ⊔ S) := fun x hx =>
    D.ker_le_S ((MonoidHom.mem_ker).1 hx)
  have hcomap : (D.Theta S).comap D.rho = S.subgroupOf (L ⊔ S) := by
    unfold P0Setup.Theta
    exact Subgroup.comap_map_eq_self hker
  have h1 := Subgroup.relIndex_comap (D.Theta S) D.rho (H.subgroupOf (L ⊔ S))
  rw [hcomap, Subgroup.relIndex_subgroupOf hHX, D.Theta_S] at h1
  exact h1.symm

theorem nodesNe_eq (n a : ℕ) : NodesNe n a = nodeSet n \ {a} := by
  ext x
  simp only [NodesNe, nodeSet, IsNode, Set.mem_ofPred_eq, Set.mem_sdiff, Set.mem_singleton_iff]
  tauto

variable {T Mc M H : Subgroup G} {B₀ : Subgroup (MulAut (V154 T Mc M))} {I X : Subgroup G}

namespace CData

variable (d : CData T Mc M H B₀ I X)

include d

theorem S_le_normalizer_K : sOf152 T Mc M B₀ ≤ Subgroup.normalizer (oTwoUpper H : Set G) :=
  S_le_T152.trans (d.c.sylowH.1.trans (le_normalizer_oTwoUpper H))

theorem K_inf_S : oTwoUpper H ⊓ sOf152 T Mc M B₀ = pCoreOf 2 (oTwoUpper H) := by
  rw [← d.c.K_inf_A d.f.K_le]
  ext x
  exact ⟨fun hx => ⟨hx.1, hx.2, d.f.K_le hx.1⟩, fun hx => ⟨hx.1, hx.2.1⟩⟩

theorem relIndex_K_sup_S : (sOf152 T Mc M B₀).relIndex (oTwoUpper H ⊔ sOf152 T Mc M B₀) = 9 := by
  have hcard := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer
    d.S_le_normalizer_K
  rw [d.K_inf_S] at hcard
  have hK9 : Nat.card ↥(oTwoUpper H) = Nat.card ↥(pCoreOf 2 (oTwoUpper H)) * 9 := by
    rw [card_eq_card_pCoreOf_mul_relIndex (oTwoUpper H), d.c.relIndex_K]
  have hpos : 0 < Nat.card ↥(pCoreOf 2 (oTwoUpper H)) := Nat.card_pos
  have h1 := Subgroup.relIndex_mul_card (sOf152 T Mc M B₀) (oTwoUpper H ⊔ sOf152 T Mc M B₀)
  rw [inf_of_le_left (le_sup_right : sOf152 T Mc M B₀ ≤ oTwoUpper H ⊔ sOf152 T Mc M B₀)] at h1
  have hposS : 0 < Nat.card ↥(sOf152 T Mc M B₀) := Nat.card_pos
  have h2 : ((sOf152 T Mc M B₀).relIndex (oTwoUpper H ⊔ sOf152 T Mc M B₀) *
      Nat.card ↥(sOf152 T Mc M B₀)) * Nat.card ↥(pCoreOf 2 (oTwoUpper H)) =
      (9 * Nat.card ↥(sOf152 T Mc M B₀)) * Nat.card ↥(pCoreOf 2 (oTwoUpper H)) := by
    rw [h1, hcard, hK9]
    ring
  exact Nat.eq_of_mul_eq_mul_right hposS (Nat.eq_of_mul_eq_mul_right hpos h2)

theorem sup_le_normalizer_W1 (hF : ¬ X ≤ Mc) {n : ℕ} {W : ℕ → Subgroup G}
    (D : P0Setup X (sOf152 T Mc M B₀) (uLOf1527 (zSOf T Mc M B₀) X) n W) (hn : 1 < n)
    (hZW : zUOf1528 (zSOf T Mc M B₀) X = W 1) :
    oTwoUpper H ⊔ sOf152 T Mc M B₀ ≤ Subgroup.normalizer (W 1 : Set G) := by
  have hF' := d.facts15128 hF
  refine sup_le (fun k hk => ?_) (fun s hs => D.W_norm 1 le_rfl hn hs)
  have h := (FLc.centralizer_zU_eq hF'.decomp hF'.ZU hF'.ULU k (d.f.K_le hk)).1
    (d.c.K_le_centralizer hk)
  have h' : k ∈ Subgroup.centralizer (W 1 : Set G) := by rw [← hZW]; exact h
  exact Subgroup.centralizer_le_normalizer _ h'

theorem false_of_four (hF : ¬ X ≤ Mc) {W : ℕ → Subgroup G}
    (D : P0Setup X (sOf152 T Mc M B₀) (uLOf1527 (zSOf T Mc M B₀) X) 4 W)
    (hZW : zUOf1528 (zSOf T Mc M B₀) X = W 1) : False := by
  set H₀ := oTwoUpper H ⊔ sOf152 T Mc M B₀ with hH₀
  have hSH : sOf152 T Mc M B₀ ≤ H₀ := le_sup_right
  have hHX : H₀ ≤ X ⊔ sOf152 T Mc M B₀ := sup_le (d.f.K_le.trans le_sup_left) le_sup_right
  have h9 : (Ut 4).relIndex (D.Theta H₀) = 9 := by
    rw [relIndex_Theta D hHX]
    exact d.relIndex_K_sup_S
  have hN := d.sup_le_normalizer_W1 hF D (by norm_num) hZW
  have hle : D.Theta H₀ ≤ QI 4 {1} := by
    rintro _ ⟨x, hx, rfl⟩
    rw [mem_flagStabilizer]
    intro j hj
    rw [Set.mem_singleton_iff] at hj
    subst hj
    exact (D.mem_normalizer_W_iff le_rfl (by norm_num) x).1 (hN hx)
  have hU : Ut 4 ≤ D.Theta H₀ := D.Ut_le_Theta hSH
  have h21 : (Ut 4).relIndex (QI 4 {1}) = 21 := by
    have hUt : Nat.card ↥(Ut 4) = 64 := by
      have := CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_unitriangular (K := ZMod 2) 4
      rw [Nat.card_zmod] at this
      simpa using this
    have h1 := Subgroup.relIndex_mul_card (Ut 4) (QI 4 {1})
    rw [inf_of_le_left (Ut_le_QI 4 {1}), hUt, A38c10.card_QI_end 1 (Or.inl rfl)] at h1
    omega
  have := Subgroup.relIndex_mul_relIndex (Ut 4) (D.Theta H₀) (QI 4 {1}) hU hle
  rw [h9, h21] at this
  omega

theorem not_irred_of_natural {n : ℕ} {W : ℕ → Subgroup G}
    (D : P0Setup X (sOf152 T Mc M B₀) (uLOf1527 (zSOf T Mc M B₀) X) n W) :
    ¬ IsIrredOnSection (sOf152 T Mc M B₀) (oTwoUpper H) (pCoreOf 2 (oTwoUpper H)) := by
  intro hirr
  set S := sOf152 T Mc M B₀ with hS
  set K := oTwoUpper H with hK
  have hSK := d.S_le_normalizer_K
  have hSH : S ≤ K ⊔ S := le_sup_right
  have hHX : K ⊔ S ≤ X ⊔ S := sup_le (d.f.K_le.trans le_sup_left) le_sup_right
  have h9 : (Ut n).relIndex (D.Theta (K ⊔ S)) = 9 := by
    rw [relIndex_Theta D hHX]
    exact d.relIndex_K_sup_S
  have hUJ : Ut n ≤ D.Theta (K ⊔ S) := D.Ut_le_Theta hSH
  have hJU : D.Theta (K ⊔ S) ≠ Ut n := by
    intro h
    rw [h, Subgroup.relIndex_self] at h9
    omega
  have hJQ := eq_QI_cuts hUJ
  obtain ⟨a, ha, haJ⟩ : ∃ a, IsNode n a ∧ a ∉ cuts (D.Theta (K ⊔ S)) := by
    by_contra hall
    push Not at hall
    apply hJU
    rw [hJQ]
    have : cuts (D.Theta (K ⊔ S)) = {i | IsNode n i} :=
      Set.Subset.antisymm (fun i hi => isNode_of_mem_cuts hi) hall
    rw [this, ← Ut_eq_QI]
  have hPaJ : QI n (nodeSet n \ {a}) ≤ D.Theta (K ⊔ S) := by
    rw [hJQ]
    refine (QI_le_QI_iff (fun j hj => isNode_of_mem_cuts hj)).2 fun i hi =>
      ⟨isNode_of_mem_cuts hi, ?_⟩
    rw [Set.mem_singleton_iff]
    rintro rfl
    exact haJ hi
  have hidx := index_single ha
  have hUPa : Ut n ≤ QI n (nodeSet n \ {a}) := Ut_le_QI n _
  have hPaneJ : QI n (nodeSet n \ {a}) ≠ D.Theta (K ⊔ S) := by
    intro h
    rw [h, h9] at hidx
    omega
  have hPaneU : QI n (nodeSet n \ {a}) ≠ Ut n := by
    intro h
    rw [h, Subgroup.relIndex_self] at hidx
    omega
  obtain ⟨Ha, hSHa, hHaX, hΘ⟩ := D.exists_Theta_eq hUPa
  have hHaH : Ha ≤ K ⊔ S := D.le_of_Theta_le hSH hHaX (by rw [hΘ]; exact hPaJ)
  have hHaS : Ha ≠ S := fun h => hPaneU (by rw [← hΘ, h, D.Theta_S])
  have hHaH' : Ha ≠ K ⊔ S := fun h => hPaneJ (by rw [← hΘ, h])
  have hOS : pCoreOf 2 K ≤ S := d.K_inf_S.ge.trans inf_le_right
  have hO : pCoreOf 2 K ≤ K ⊓ Ha := le_inf (pCoreOf_le 2 K) (hOS.trans hSHa)
  have hSN : S ≤ Subgroup.normalizer ((K ⊓ Ha : Subgroup G) : Set G) := fun g hg =>
    mem_normalizer_inf_of' (hSK hg) (Subgroup.le_normalizer (hSHa hg))
  have hmul : ∀ h ∈ K ⊔ S, ∃ k ∈ K, ∃ s ∈ S, h = k * s := by
    intro h hh
    have : h ∈ (K : Set G) * (S : Set G) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left K S hSK]
      exact hh
    obtain ⟨k, hk, s, hs, e⟩ := this
    exact ⟨k, hk, s, hs, e.symm⟩
  rcases hirr.2.2.2 (K ⊓ Ha) hO inf_le_left hSN with h | h
  ·
    apply hHaS
    refine le_antisymm (fun x hx => ?_) hSHa
    obtain ⟨k, hk, s, hs, rfl⟩ := hmul x (hHaH hx)
    have hkHa : k ∈ Ha := by
      have : k = k * s * s⁻¹ := by group
      rw [this]
      exact Ha.mul_mem hx (Ha.inv_mem (hSHa hs))
    have hkO : k ∈ pCoreOf 2 K := h ▸ ⟨hk, hkHa⟩
    exact S.mul_mem (hOS hkO) hs
  ·
    apply hHaH'
    refine le_antisymm hHaH (sup_le (fun k hk => ?_) hSHa)
    have : k ∈ K ⊓ Ha := by rw [h]; exact hk
    exact this.2

end CData

end C

end S15223P4

end CFSG.Quasithin
