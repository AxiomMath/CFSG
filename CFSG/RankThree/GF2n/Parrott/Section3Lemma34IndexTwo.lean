module

public import CFSG.GH74.PartII.Lemma22E16Sym5
public import CFSG.GH74.PartII.SylowAhat8Transfer
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.RankThree.GF2n.Parrott.Section3Lemma34Local

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open

variable {Y : Type} [Group Y] [Finite Y] {M D : Subgroup Y}

theorem exists_normal_index_two_of_permFive (hDM : D ≤ M) (hD : IsElemAbelian 2 D)
    (hD16 : Nat.card D = 16)
    (hπ : ∃ π : ↥M →* Equiv.Perm (Fin 5), Function.Surjective π ∧ π.ker = D.subgroupOf M)
    (hTrans : ∀ a ∈ D, ∀ b ∈ D, a ≠ 1 → b ≠ 1 → ∃ g ∈ M, g * a * g⁻¹ = b)
    (hCent : ∀ d ∈ D, d ≠ 1 → Subgroup.centralizer ({d} : Set Y) ≤ M) (hodd : Odd M.index) :
    ∃ K : Subgroup Y, K.Normal ∧ K.index = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hM1920, -, -, hC128⟩ := local_data_of_permFive hDM hD16 hπ hTrans hCent
  obtain ⟨d₀, hd₀, hd₀1, -⟩ := exists_mem_ne_one_ne_of_two_lt_card (D := D) (by omega) 1
  obtain ⟨π, hs, hk⟩ := hπ
  have hkcard : Nat.card π.ker = 16 := (card_ker_eq_card_of_eq_subgroupOf hDM hk).trans hD16
  have htr := ker_transitive_of_eq_subgroupOf hk hTrans
  have hel : IsElemAbelian 2 π.ker := by
    rw [hk]
    exact hD.subgroupOf M
  obtain ⟨hP, hidx⟩ := isPGroup_and_not_two_dvd_index_of_card_eq hM1920 hodd (hC128 d₀ hd₀ hd₀1)
  let S : Sylow 2 Y := hP.toSylow hidx
  have hSeq : (S : Subgroup Y) = Subgroup.centralizer {d₀} := IsPGroup.toSylow_coe hP hidx
  have hSM : (S : Subgroup Y) ≤ M := by
    rw [hSeq]
    exact hCent d₀ hd₀ hd₀1
  obtain ⟨e₁⟩ := CFSG.GH74.PartII.nonempty_mulEquiv_sylAhat8_of_e16_sym5 hs hel hkcard htr
    (S.subtype hSM)
  let e₂ : ↥(S.subtype hSM) ≃* ↥(S : Subgroup Y) :=
    (MulEquiv.subgroupCongr (S.coe_subtype hSM)).trans (Subgroup.subgroupOfEquivOfLe hSM)
  exact CFSG.GH74.PartII.exists_normal_index_two_of_centralizer_eq_sylAhat8 S (e₁.symm.trans e₂)
    hd₀1 hSeq.symm

end CFSG.RankThree.GF2n.Parrott
