module

public import CFSG.Quasithin.Recognition.Kleidman.F204.T1IIBase
public import CFSG.Quasithin.Recognition.Kleidman.F204.W2FFCount

public section

namespace CFSG.Quasithin.Kleidman.F204

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.S152X
open CFSG.Quasithin.F7 CFSG.Quasithin.FA5
open CFSG.Quasithin.F53
open CFSG.Quasithin.CosetGeom

set_option linter.unusedSectionVars false

variable {G : Type} [Group G] [Finite G]

section Generic

variable {H M : Subgroup G}

@[expose] def NatA (x : Geo H M) : Prop :=
  Nat.card (Zv x) = 16 ∧
    (∀ δ ∈ nbrs x, Nat.card (Zv x ⊓ Subgroup.centralizer (Qv δ : Set G) : Subgroup G) = 4) ∧
    ∀ δ ∈ nbrs x, ∀ δ' ∈ nbrs x, δ ≠ δ' →
      (Zv x ⊓ Subgroup.centralizer (Qv δ : Set G)) ⊓
        (Zv x ⊓ Subgroup.centralizer (Qv δ' : Set G)) = ⊥

omit [Finite G] in
private theorem inf_centralizer_smul (g : ↥(H ⊔ M)) (x δ : Geo H M) :
    Zv (g • x) ⊓ Subgroup.centralizer (Qv (g • δ) : Set G) =
      conjSub (g : G) (Zv x ⊓ Subgroup.centralizer (Qv δ : Set G)) := by
  rw [Zv_smul, Qv_smul, conjSub_inf, conjSub_centralizer]

theorem NatA.smul (g : ↥(H ⊔ M)) {x : Geo H M} (h : NatA x) : NatA (g • x) := by
  obtain ⟨h1, h2, h3⟩ := h
  have hn : ∀ δ', δ' ∈ nbrs (g • x) → g⁻¹ • δ' ∈ nbrs x := by
    intro δ' hδ'
    have := (smul_adj g⁻¹).mpr (show (graph (H ⊔ M) H M).Adj (g • x) δ' from hδ')
    rwa [inv_smul_smul] at this
  refine ⟨?_, ?_, ?_⟩
  · rw [Zv_smul, CosetGeom.card_conjSub, h1]
  · intro δ' hδ'
    have e : δ' = g • (g⁻¹ • δ') := (smul_inv_smul g δ').symm
    rw [e, inf_centralizer_smul, CosetGeom.card_conjSub]
    exact h2 _ (hn δ' hδ')
  · intro δ₁ hδ₁ δ₂ hδ₂ hne
    have e1 : δ₁ = g • (g⁻¹ • δ₁) := (smul_inv_smul g δ₁).symm
    have e2 : δ₂ = g • (g⁻¹ • δ₂) := (smul_inv_smul g δ₂).symm
    have hne' : g⁻¹ • δ₁ ≠ g⁻¹ • δ₂ := fun h => hne (by rw [e1, e2, h])
    rw [e1, e2, inf_centralizer_smul, inf_centralizer_smul, ← conjSub_inf,
      h3 _ (hn _ hδ₁) _ (hn _ hδ₂) hne']
    exact (conjSub_eq_bot_iff _).mpr rfl

theorem NatA.of_vtype_eq {x y : Geo H M} (hv : vtype x = vtype y) (h : NatA x) : NatA y := by
  obtain ⟨g, rfl⟩ := exists_smul_of_vtype_eq hv
  exact h.smul g

end Generic

variable {L1 L2 S D X : Subgroup G}

theorem sylow_sup_Qv (F : Frame L1 L2 S D X) {x δ : Geo (P1 L1 L2 S) (P2 L1 L2 S)}
    (hx : vtype x = true) (hδ : δ ∈ nbrs x) :
    IsSylowTwoOf (Qv x ⊔ Qv δ) (stab δ) ∧ IsSylowTwoOf (Qv x ⊔ Qv δ) (stab x) ∧
      stab x ⊓ stab δ ≤ Subgroup.normalizer ((Qv x ⊔ Qv δ : Subgroup G) : Set G) := by
  have h₁ : P1 L1 L2 S ≤ P1 L1 L2 S ⊔ P2 L1 L2 S := le_sup_left
  have h₂ : P2 L1 L2 S ≤ P1 L1 L2 S ⊔ P2 L1 L2 S := le_sup_right
  have hQ0 : Qv (γ₀ (P1 L1 L2 S ⊔ P2 L1 L2 S) (P1 L1 L2 S) (P2 L1 L2 S)) = Q1 L1 L2 S := by
    unfold Qv; rw [stab_γ₀ h₁]
  have hQ1 : Qv (γ₁ (P1 L1 L2 S ⊔ P2 L1 L2 S) (P1 L1 L2 S) (P2 L1 L2 S)) = Q2 L1 L2 S := by
    unfold Qv; rw [stab_γ₁ h₂]
  obtain ⟨g, ⟨hg0, hg1⟩ | ⟨hg0, hg1⟩⟩ := exists_smul_edge (show (graph _ _ _).Adj x δ from hδ)
  · exfalso
    have := vtype_smul g (γ₀ (P1 L1 L2 S ⊔ P2 L1 L2 S) (P1 L1 L2 S) (P2 L1 L2 S))
    rw [hg0, hx, vtype_γ₀] at this
    exact Bool.noConfusion this
  · have hsup : Qv x ⊔ Qv δ = conjSub (g : G) S := by
      rw [← hg0, ← hg1, Qv_smul, Qv_smul, hQ0, hQ1, ← conjSub_sup,
        show Q2 L1 L2 S ⊔ Q1 L1 L2 S = S from by rw [sup_comm]; exact Q1_sup_Q2 F]
    have hsδ : stab δ = conjSub (g : G) (P1 L1 L2 S) := by rw [← hg0, stab_smul, stab_γ₀ h₁]
    have hsx : stab x = conjSub (g : G) (P2 L1 L2 S) := by rw [← hg1, stab_smul, stab_γ₁ h₂]
    refine ⟨?_, ?_, ?_⟩
    · rw [hsup, hsδ]; exact isSylowTwoOf_conj F.sylow_P1 _
    · rw [hsup, hsx]; exact isSylowTwoOf_conj F.sylow_P2 _
    · rw [hsup, hsx, hsδ, ← conjSub_inf,
        show P2 L1 L2 S ⊓ P1 L1 L2 S = bigB L1 L2 S from by rw [inf_comm]; exact F.P1_inf_P2,
        conjSub_normalizer]
      exact conjSub_mono _ F.B_le_normalizer_S

section T1

variable (F : Frame L1 L2 S D X) (hT1 : ConfigT1 L1 L2 S)
include F hT1

theorem Zv_eq_inf_centralizer {x δ : Geo (P1 L1 L2 S) (P2 L1 L2 S)} (hx : vtype x = true)
    (hδ : δ ∈ nbrs x) : Zv δ = Zv x ⊓ Subgroup.centralizer (Qv δ : Set G) := by
  have hA := Amal.of_frame F
  have hδf : vtype δ = false := by
    have := vtype_ne_of_adj (show (graph _ _ _).Adj x δ from hδ)
    rw [hx] at this
    cases h : vtype δ <;> simp_all
  have hcen : ZCentral δ := (hT1 δ).mpr hδf
  have hxδ : x ∈ nbrs δ := (show (graph _ _ _).Adj x δ from hδ).symm
  apply le_antisymm
  · refine le_inf (hA.Zv_le_Zv_of_ZCentral hxδ hcen) fun z hz => (hA.Zv_le_centerOf_Qv δ hz).2
  · rintro z ⟨hzx, hzc⟩
    obtain ⟨hT, -, -⟩ := sylow_sup_Qv F hx hδ
    rw [hcen _ hT]
    apply Subgroup.subset_closure
    have hzT : z ∈ Qv x ⊔ Qv δ := le_sup_left (a := Qv x) (hA.Zv_le_Qv x hzx)
    have hTC : Qv x ⊔ Qv δ ≤ Subgroup.centralizer {z} := by
      refine sup_le (fun q hq => ?_) (fun q hq => ?_)
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact (Subgroup.mem_centralizer_iff.mp (hA.Zv_le_centerOf_Qv x hzx).2 q hq)
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact (Subgroup.mem_centralizer_iff.mp hzc q hq)
    refine ⟨⟨hzT, Subgroup.mem_centralizer_iff.mpr fun t ht => ?_⟩, ?_⟩
    · exact (Subgroup.mem_centralizer_singleton_iff.mp (hTC ht))
    · exact (hA.isElemAbelian_Zv x).2 z hzx

theorem Zv_inf_Zv_eq_bot {x δ δ' : Geo (P1 L1 L2 S) (P2 L1 L2 S)} (hx : vtype x = true)
    (hN : NatA x) (hδ : δ ∈ nbrs x) (hδ' : δ' ∈ nbrs x) (hne : δ ≠ δ') : Zv δ ⊓ Zv δ' = ⊥ := by
  rw [Zv_eq_inf_centralizer F hT1 hx hδ, Zv_eq_inf_centralizer F hT1 hx hδ']
  exact hN.2.2 δ hδ δ' hδ' hne

theorem card_Zv_nbr {x δ : Geo (P1 L1 L2 S) (P2 L1 L2 S)} (hx : vtype x = true) (hN : NatA x)
    (hδ : δ ∈ nbrs x) : Nat.card (Zv δ) = 4 := by
  rw [Zv_eq_inf_centralizer F hT1 hx hδ]; exact hN.2.1 δ hδ

theorem Zv_sup_Zv_eq {x δ δ' : Geo (P1 L1 L2 S) (P2 L1 L2 S)} (hx : vtype x = true)
    (hN : NatA x) (hδ : δ ∈ nbrs x) (hδ' : δ' ∈ nbrs x) (hne : δ ≠ δ') :
    Zv δ ⊔ Zv δ' = Zv x := by
  have hA := Amal.of_frame F
  have hle : Zv δ ⊔ Zv δ' ≤ Zv x := by
    rw [Zv_eq_inf_centralizer F hT1 hx hδ, Zv_eq_inf_centralizer F hT1 hx hδ']
    exact sup_le inf_le_left inf_le_left
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  have h1 := card_mul_le_card_of_inf_eq_bot (V := Zv δ ⊔ Zv δ') le_sup_left le_sup_right
    (Zv_inf_Zv_eq_bot F hT1 hx hN hδ hδ' hne)
  rw [card_Zv_nbr F hT1 hx hN hδ, card_Zv_nbr F hT1 hx hN hδ'] at h1
  rw [hN.1]
  exact h1

theorem inf_centralizer_two_eq {x δ : Geo (P1 L1 L2 S) (P2 L1 L2 S)} (hx : vtype x = true)
    (hN : NatA x) (hδ : δ ∈ nbrs x) (hfaith : ¬ stab x ≤ Subgroup.centralizer (Zv x : Set G))
    {t : G} (htx : t ∈ stab x) (htδ : t ∈ stab δ) {k : ℕ} (htk : t ^ 2 ^ k = 1)
    (htQ : t ∉ Qv x) : Zv x ⊓ Subgroup.centralizer {t} = Zv δ := by
  have hA := Amal.of_frame F
  obtain ⟨hTδ, hTx, hTn⟩ := sylow_sup_Qv F hx hδ
  have hp : IsPGroup 2 (Subgroup.zpowers t) := by
    obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one htk)
    exact IsPGroup.of_card (n := m) (by rw [Nat.card_zpowers, hm])
  have hUK : Subgroup.zpowers t ≤ stab x ⊓ stab δ := Subgroup.zpowers_le.mpr ⟨htx, htδ⟩
  have hpT : IsPGroup 2 ↥(Qv x ⊔ Qv δ) := hTδ.2.1
  have hsup : IsPGroup 2 ↥(Subgroup.zpowers t ⊔ (Qv x ⊔ Qv δ)) :=
    IsPGroup.to_sup_of_normal_right' hp hpT (hUK.trans hTn)
  have hle : Subgroup.zpowers t ⊔ (Qv x ⊔ Qv δ) ≤ stab δ := sup_le (hUK.trans inf_le_right) hTδ.1
  have heq := F1.eq_of_isSylowTwoOf_le hTδ hle hsup le_sup_right
  have htT : t ∈ Qv x ⊔ Qv δ := by
    rw [heq]; exact le_sup_left (a := Subgroup.zpowers t) (Subgroup.mem_zpowers t)
  have hQn : Qv δ ≤ Subgroup.normalizer (Qv x : Set G) :=
    (hA.Qv_le_stab_of_mem_nbrs (show x ∈ nbrs δ from
      (show (graph _ _ _).Adj x δ from hδ).symm)).trans (le_normalizer_pCoreOf 2 (stab x))
  obtain ⟨a, ha, b, hb, rfl⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes hQn).mp htT
  have hle1 : Zv δ ≤ Zv x ⊓ Subgroup.centralizer {a * b} := by
    rw [Zv_eq_inf_centralizer F hT1 hx hδ]
    rintro z ⟨hzx, hzc⟩
    refine ⟨hzx, ?_⟩
    show z ∈ Subgroup.centralizer {a * b}
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 : a * z = z * a :=
      (Subgroup.mem_centralizer_iff.mp (hA.Zv_le_centerOf_Qv x hzx).2 a ha)
    have h2 : b * z = z * b := Subgroup.mem_centralizer_iff.mp hzc b hb
    calc z * (a * b) = (z * a) * b := (mul_assoc _ _ _).symm
      _ = (a * z) * b := by rw [h1]
      _ = a * (z * b) := mul_assoc _ _ _
      _ = a * (b * z) := by rw [h2]
      _ = (a * b) * z := (mul_assoc _ _ _).symm
  have hQC : Qv x ≤ Subgroup.centralizer (Zv x : Set G) := fun q hq =>
    Subgroup.mem_centralizer_iff.mpr fun y hy =>
      (Subgroup.mem_centralizer_iff.mp (hA.Zv_le_centerOf_Qv x hy).2 q hq).symm
  have htk' : (a * b) ^ 2 ^ k ∈ Qv x := by rw [htk]; exact one_mem _
  have h4 := four_le_relIndex_A F hx (hA.isElemAbelian_Zv x) (hA.stab_le_normalizer_Zv x) hQC
    hfaith htx htQ htk'
  have hc := card_eq_relIndex_mul (V := Zv x) (Z := Subgroup.centralizer {a * b})
  rw [hN.1] at hc
  have hcard : Nat.card (Zv x ⊓ Subgroup.centralizer {a * b} : Subgroup G) ≤ 4 := by
    by_contra hlt
    push Not at hlt
    have : 4 * 5 ≤ (Zv x ⊓ Subgroup.centralizer {a * b}).relIndex (Zv x) *
        Nat.card (Zv x ⊓ Subgroup.centralizer {a * b} : Subgroup G) := Nat.mul_le_mul h4 hlt
    omega
  exact (Subgroup.eq_of_le_of_card_ge hle1 (by rw [card_Zv_nbr F hT1 hx hN hδ]; exact hcard)).symm

end T1

end CFSG.Quasithin.Kleidman.F204
