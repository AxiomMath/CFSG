module

public import CFSG.Quasithin.Vol2.Ch11SecB36K
public import CFSG.Quasithin.Vol2.Ch11SecB36Sym
public import CFSG.Quasithin.Vol2.Ch11SecBFacts36K

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Quasithin.Vol2.Ch11.SecA

variable {G : Type} [Group G] [Finite G] {n : ℕ}

theorem false_of_pair (hFL : FactsL2) (hn : 2 ≤ n) {VH K W : Subgroup G}
    (hVHel : IsElemAbelian 2 VH) {g : G}
    (hBN : conjSubgroup W g ≤ Subgroup.normalizer (VH : Set G))
    (hnat : BinaryNaturalSL (autI hVHel K) ⊤ (fixV (autI hVHel K)) 2 (2 * n))
    (hBS : QuasithinUnique.IsSylowTwoOf (autI hVHel (conjSubgroup W g)) (autI hVHel K))
    (hGm : ∃ (F' : Type) (_ : Field F') (_ : Finite F'), Nat.card F' = 2 ^ (2 * n) ∧
      Nonempty (↥(autI hVHel K) ≃* Matrix.SpecialLinearGroup (Fin 2) F'))
    (hcm : E3.mQuot ⁅W, conjSubgroup VH g⁻¹⁆ ⊥ = 4 * n) {a b : G} (haW : a ∈ W)
    (hbW : b ∈ W) (hab : a⁻¹ * b ∉ Subgroup.centralizer (conjSubgroup VH g⁻¹ : Set G))
    (habE : ⁅Subgroup.zpowers a, conjSubgroup VH g⁻¹⁆ =
      ⁅Subgroup.zpowers b, conjSubgroup VH g⁻¹⁆)
    (haE : ⁅Subgroup.zpowers a, conjSubgroup VH g⁻¹⁆ ≠ ⊥) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hEg : conjSubgroup (conjSubgroup VH g⁻¹) g = VH := E3.conjSubgroup_inv_conj VH g
  have ha'B : g⁻¹ * a * g ∈ conjSubgroup W g := by
    rw [mem_conjSubgroup_iff, show g * (g⁻¹ * a * g) * g⁻¹ = a by group]
    exact haW
  have hb'B : g⁻¹ * b * g ∈ conjSubgroup W g := by
    rw [mem_conjSubgroup_iff, show g * (g⁻¹ * b * g) * g⁻¹ = b by group]
    exact hbW
  have hca : ⁅Subgroup.zpowers (g⁻¹ * a * g), VH⁆ =
      conjSubgroup ⁅Subgroup.zpowers a, conjSubgroup VH g⁻¹⁆ g := by
    rw [E3.conjSubgroup_commutator, conjSubgroup_zpowers, hEg]
  have hcb : ⁅Subgroup.zpowers (g⁻¹ * b * g), VH⁆ =
      conjSubgroup ⁅Subgroup.zpowers b, conjSubgroup VH g⁻¹⁆ g := by
    rw [E3.conjSubgroup_commutator, conjSubgroup_zpowers, hEg]
  have hab' : ⁅Subgroup.zpowers (g⁻¹ * a * g), VH⁆ = ⁅Subgroup.zpowers (g⁻¹ * b * g), VH⁆ := by
    rw [hca, hcb, habE]
  have ha'ne : ⁅Subgroup.zpowers (g⁻¹ * a * g), VH⁆ ≠ ⊥ := by
    rw [hca]
    exact fun h => haE (conjSubgroup_eq_bot_iff.mp h)
  have hb'ne : ⁅Subgroup.zpowers (g⁻¹ * b * g), VH⁆ ≠ ⊥ := hab' ▸ ha'ne
  have hab'C : (g⁻¹ * a * g)⁻¹ * (g⁻¹ * b * g) ∉ Subgroup.centralizer (VH : Set G) := by
    intro h
    apply hab
    have h1 : a⁻¹ * b ∈ conjSubgroup (Subgroup.centralizer (VH : Set G)) g⁻¹ := by
      rw [E3.mem_conjSubgroup_inv_iff]
      convert h using 1
      group
    rwa [E3.conjSubgroup_centralizer] at h1
  have hBVH : ⁅conjSubgroup W g, VH⁆ ≤ VH :=
    Subgroup.le_normalizer_iff_commutator_le_right.mp hBN
  have hcm' : E3.mQuot ⁅conjSubgroup W g, VH⁆ ⊥ = 4 * n := by
    have := E3.mQuot_conjSubgroup ⁅W, conjSubgroup VH g⁻¹⁆ ⊥ g
    rw [E3.conjSubgroup_commutator, hEg, E3.conjSubgroup_bot, hcm] at this
    exact this
  have hcard : Nat.card ↥(commV (autI hVHel (conjSubgroup W g))) = 2 ^ (2 * (2 * n)) := by
    rw [card_commV_autI hVHel hBN, Subgroup.commutator_comm]
    have h2 : IsPGroup 2 ↥⁅conjSubgroup W g, VH⁆ :=
      (B2F.isPGroup_of_isElemAbelian hVHel).to_le hBVH
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp h2
    have h3 : E3.mQuot ⁅conjSubgroup W g, VH⁆ ⊥ = m := by
      unfold E3.mQuot
      rw [Subgroup.relIndex_bot_left, hm, padicValNat.prime_pow]
    rw [hm, ← h3, hcm']
    ring_nf
  have horth := hFL.orth (IntMod VH hVHel) IntMod.sq_eq_one (autI hVHel K)
    (autI hVHel (conjSubgroup W g)) (2 * n) (by omega) hGm hBS hnat hcard
  have ha'N : g⁻¹ * a * g ∈ Subgroup.normalizer (VH : Set G) := hBN ha'B
  have hb'N : g⁻¹ * b * g ∈ Subgroup.normalizer (VH : Set G) := hBN hb'B
  have hne1 : ∀ {x : G} (hx : x ∈ Subgroup.normalizer (VH : Set G)),
      ⁅Subgroup.zpowers x, VH⁆ ≠ ⊥ → convI hVHel ⟨x, hx⟩ ≠ 1 := by
    intro x hx hne h
    apply hne
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact Subgroup.zpowers_le.mpr ((convI_eq_one_iff hVHel _).mp h)
  have hneq : convI hVHel ⟨g⁻¹ * a * g, ha'N⟩ ≠ convI hVHel ⟨g⁻¹ * b * g, hb'N⟩ := by
    intro h
    apply hab'C
    have : convI hVHel (⟨g⁻¹ * a * g, ha'N⟩⁻¹ * ⟨g⁻¹ * b * g, hb'N⟩) = 1 := by
      rw [map_mul, map_inv, h, inv_mul_cancel]
    exact (convI_eq_one_iff hVHel _).mp this
  have h1 := horth _ (convI_mem_autI hVHel ha'B ha'N) _ (convI_mem_autI hVHel hb'B hb'N)
    (hne1 ha'N ha'ne) (hne1 hb'N hb'ne) hneq
  rw [← autI_zpowers hVHel ha'N, ← autI_zpowers hVHel hb'N] at h1
  have h2 := inf_commutator_eq_bot hVHel (Subgroup.zpowers_le.mpr ha'N)
    (Subgroup.zpowers_le.mpr hb'N) h1
  rw [Subgroup.commutator_comm VH, Subgroup.commutator_comm VH, ← hab', inf_idem] at h2
  exact ha'ne h2

end CFSG.Quasithin.Vol2.Ch11.SecB
