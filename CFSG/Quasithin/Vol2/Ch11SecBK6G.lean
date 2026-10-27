module

public import CFSG.Quasithin.Vol2.Ch11SecBK6F
public import CFSG.Quasithin.Vol2.Ch11SecBK6B

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Quasithin Matrix
open CFSG.Quasithin.Vol2.KGNat
open CFSG.Assembly.LowTwoRank (StatedSL)
open CFSG.ClassicalInvolution.ModelFacts.OddCover (uSL)
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (flagSpace)
open CFSG.Open (pCoreOf)
open scoped IsMulCommutative

namespace BK6

variable {G : Type} [Group G] [Finite G] {L V X T V₁ V₂ : Subgroup G} {n : ℕ}

theorem mQuot_le_of_relIndex_le {A B : Subgroup G} {k : ℕ} (h : B.relIndex A ≤ 2 ^ k) :
    E3.mQuot A B ≤ k := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  unfold E3.mQuot
  have h1 : 2 ^ padicValNat 2 (B.relIndex A) ≤ 2 ^ k :=
    (Nat.le_of_dvd (Nat.pos_of_ne_zero (E3.relIndex_ne_zero' A B)) pow_padicValNat_dvd).trans h
  exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h1

theorem r2Gen_sl3 (hfl : Flag24 L V X T V₁ V₂ n) (hk : KindSL3 L V n) {A : Subgroup G}
    (hAR : A ≤ pCoreOf 2 (LOf L V₂ ⊔ T)) :
    V ≤ ⨆ (B : Subgroup G) (_ : B ≤ A ∧ E3.mQuot A B ≤ 2 * n),
      V ⊓ Subgroup.centralizer (B : Set G) := by
  obtain ⟨_, K, _, _, _, hK, π, hπ⟩ := exists_real_sl3 hfl hk
  have hsq : ∀ w : ↥V, w ^ 2 = 1 := fun w => Subtype.ext (by simpa using hfl.elem.2 w w.2)
  have hn := hfl.two_le
  obtain ⟨f, hf⟩ := exists_isCoord (linModelNat _) hπ
  have hTL' : QuasithinUnique.IsSylowTwoOf (T ⊓ L) L :=
    B6.isSylowTwoOf_inf_normal hfl.sylow le_sup_left (sup_le Subgroup.le_normalizer hfl.T_le_L)
  obtain ⟨g, hg⟩ := exists_sylow_eq_conj_Usl hK (by omega) hf
    (SecA.isSylowTwoOf_autOn hfl.le_normalizer hTL')
  have hF₂ := isFlagW_of_flag24 hfl hfl.le₂ (hfl.cV_le.trans hfl.le₁₂) hfl.stable₂ hfl.index₂
    hfl.T_le_V₂
  have hU₂ := eq_U2_of_isFlagW hsq hf hg (by rw [hK]; exact hF₂)
  have hAV : A ≤ Subgroup.normalizer (V : Set G) := fun a ha => K7.r2_le_normalizer hfl (hAR ha)
  have hsub : (autOn A V : Set (MulAut ↥V)) ⊆ Set.range fun bc : K × K =>
      ((rho3 π (g * uSL 0 bc.1 bc.2 * g⁻¹) : ↥(autOn L V)) : MulAut ↥V) := by
    intro φ hφ
    obtain ⟨a, ha, haV, rfl⟩ := SecA.mem_autOn_iff.mp hφ
    obtain ⟨b, c, hbc⟩ := exists_rad2_of_mem_r2 hfl hK hf hU₂ (hAR ha)
    exact ⟨(b, c), hbc.symm⟩
  have hcard : Nat.card ↥(autOn A V) ≤ 2 ^ (2 * n) := by
    calc Nat.card ↥(autOn A V) ≤ Nat.card ↥(Set.range fun bc : K × K =>
          ((rho3 π (g * uSL 0 bc.1 bc.2 * g⁻¹) : ↥(autOn L V)) : MulAut ↥V)) :=
          Nat.card_mono (Set.toFinite _) hsub
      _ ≤ Nat.card (K × K) := Finite.card_range_le _
      _ = 2 ^ (2 * n) := by rw [Nat.card_prod, hK, ← pow_add, two_mul]
  have hm : E3.mQuot A (A ⊓ Subgroup.centralizer (V : Set G)) ≤ 2 * n :=
    mQuot_le_of_relIndex_le (by rw [← card_autOn_eq_relIndex hAV]; exact hcard)
  intro v hv
  have hmem : v ∈ V ⊓ Subgroup.centralizer
      ((A ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G) :=
    Subgroup.mem_inf.mpr ⟨hv, Subgroup.mem_centralizer_iff.mpr fun b hb =>
      (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hb).2 v hv).symm⟩
  exact (le_iSup₂ (f := fun (B : Subgroup G) (_ : B ≤ A ∧ E3.mQuot A B ≤ 2 * n) =>
    V ⊓ Subgroup.centralizer (B : Set G)) (A ⊓ Subgroup.centralizer (V : Set G))
    ⟨inf_le_left, hm⟩) hmem

end BK6

end CFSG.Quasithin.Vol2.Ch11.SecB
