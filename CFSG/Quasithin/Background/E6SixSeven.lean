module

public import CFSG.Quasithin.Vol2.Ch11StatementsInputsAS
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.Quasithin
namespace E6

open CFSG.Open CFSG.QuasithinUnique
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem as_E_6_6_four_proved : ASInputs.AS_E_6_6_four := by
  intro G _ _ T M V U h hU hUZ
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT : IsSylowTwoOf T ⊤ :=
    ⟨le_top, h.sylow.1, by rw [← Subgroup.relIndex, Subgroup.relIndex_top_right]; exact h.sylow.2⟩
  have hU2 : IsPGroup 2 U := h.isPGroup_V.to_le hU.2.1
  have hZ : U ⊓ (T ⊓ Subgroup.centralizer (T : Set G)) ≠ ⊥ := by
    refine fun h0 => hUZ (eq_bot_iff.2 ?_)
    rw [← h0]
    exact inf_le_inf_left _ (inf_le_inf_right _ h.le)
  have hN := CT.charTwo_normalizer_of_inf_center h.qtke.2.1 hT hU2 hZ
  have hC := CT.CharTwo.inf_centralizer hN Subgroup.le_normalizer hU2
  rwa [inf_eq_right.2 (Subgroup.centralizer_le_normalizer _)] at hC

omit [Finite G] in
theorem cgsIn_mono {K H Q : Subgroup G} (hKH : K ≤ H) : cgsIn K Q ≤ cgsIn H Q :=
  iSup_mono fun _ => iSup_mono fun _ => iSup_mono fun _ => iSup_mono fun _ =>
    inf_le_inf_right _ hKH

omit [Finite G] in
theorem coe_eq_mul_iSup {K M : Subgroup G} {r : ℕ} {Lb : Fin r → Subgroup G}
    (hLK : ∀ i, Lb i ≤ K)
    (hprod : ∀ h ∈ K, ∃ m ∈ K ⊓ M, ∃ x : Fin r → G, (∀ i, x i ∈ Lb i) ∧
      h = m * (List.ofFn x).prod) :
    (K : Set G) = ((K ⊓ M : Subgroup G) : Set G) * ((⨆ i, Lb i : Subgroup G) : Set G) := by
  ext h
  constructor
  · intro hh
    obtain ⟨m, hm, x, hx, rfl⟩ := hprod h hh
    refine ⟨m, hm, (List.ofFn x).prod, Subgroup.list_prod_mem (K := ⨆ i, Lb i) fun y hy => ?_, rfl⟩
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hy
    exact le_iSup Lb i (hx i)
  · rintro ⟨m, hm, l, hl, rfl⟩
    exact K.mul_mem hm.1 (iSup_le hLK hl)

end E6
end CFSG.Quasithin
