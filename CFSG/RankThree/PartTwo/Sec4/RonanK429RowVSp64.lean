module

public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowVSp64Blk
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowVSp64Lin
public import CFSG.RankThree.PartTwo.Sec4.RonanK432RowSp64
public import CFSG.RankThree.PartTwo.Sec4.Item47Kinds
public import CFSG.RankThree.PartTwo.Sec5.Tools
public import CFSG.RankThree.PartTwo.Sec4.Item423Res2ProofHelpers
public import CFSG.Open.SplitBNPair
public import CFSG.Quasithin.Vol2.Ch10StatementsE
public import CFSG.Quasithin.Vol2.Ch10StatementsInputs
public import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS
public import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS2
public import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS3
public import CFSG.RankThree.PartTwo.Sec11.Inverter1118Proof
public import CFSG.RankThree.PartTwo.Sec11.Inverter1118ProofSteps
public import CFSG.RankThree.PartTwo.Sec11.Item1121Proof
public import CFSG.RankThree.PartTwo.Sec11.Item119K
public import CFSG.RankThree.PartTwo.Sec14.Item142ResProofPGL
public import CFSG.RankThree.PartTwo.Sec20.OneSteps
public import CFSG.RankThree.PartTwo.Sec21.Item211ProofListOf
public import Certificates.Certificate8166

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK429

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.KFacts
open CFSG.RankThree.PartTwo.Sec4.Item434Kit
open Matrix CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl CFSG.Open
open CFSG.RankThree.PartTwo.Sec4.RonanK432 (Sp6 wreathFacts_Sp6 card_wreathW_Sp6
  factorization_card_Sp6)
open CFSG.Assembly.RankThreeEven (projSp)

namespace RowV

local notation "spTorus" => CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.torusHom

theorem card_Sp6_eq : Nat.card Sp6 = 7 * 586579968000 := by
  rw [KFacts.KS21.Sp64.card_Sp_eq]
  norm_num

theorem vecElt_lam_eq (ω : (GaloisField 2 2)ˣ) (v : Fin 3 → ZMod 3) :
    vecElt (fun i => lam i (sl2Diag ω)) v =
      spTorus (fun i => ω ^ (v i).val) := by
  rw [vecElt, lam_sl2Diag, lam_sl2Diag, lam_sl2Diag, ← map_pow, ← map_pow, ← map_pow,
    ← map_mul, ← map_mul]
  congr 1
  funext j
  fin_cases j <;> simp [Pi.mulSingle_apply]

theorem centQuasi_Sp6 {E : Subgroup Sp6} (hE : CFSG.Assembly.IsElemAbelian 3 E)
    (hE27 : Nat.card E = 27) {s : Sp6} (hs : s ∈ E) (hs1 : s ≠ 1) :
    CentQuasi s 586579968000 60480 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hF4 : Nat.card (GaloisField 2 2) = 4 := by
    rw [GaloisField.card 2 2 (by norm_num)]; norm_num
  obtain ⟨ω, hord, hω3, -⟩ := KFacts.KS21.Sp64.exists_omega_data
  have hwz := wreathFacts_Sp6 hω3 hord
  obtain ⟨g, hg⟩ := Item434AltPerm.exists_le_map_conj_of_card
    (P₀ := wreathW (fun i => lam i (sl2Diag ω)) (leviSp KFacts.KS21.DFT.permGL3))
    (by rw [card_wreathW_Sp6 hω3 hord, factorization_card_Sp6]; norm_num)
    (CFSG.RankThree.PartTwo.Sec5.isPGroup_of_isElemAbelian hE)
  have hle := Item434AltPerm.map_conj_inv_le hg
  have hEq := eq_baseA_of_le_wreathW hwz (card_wreathW_Sp6 hω3 hord) hle
    (Res423Two.isElemAbelian_map' _ hE)
    (by rw [Subgroup.card_map_of_injective (f := (MulAut.conj g⁻¹).toMonoidHom)
        (MulAut.conj g⁻¹).injective, hE27])
  have hs' : MulAut.conj g⁻¹ s ∈ baseA (fun i => lam i (sl2Diag ω)) := hEq ▸ ⟨s, hs, rfl⟩
  obtain ⟨v, hv⟩ := (mem_baseA_iff hwz).mp hs'
  apply CentQuasi.of_mulEquiv (MulAut.conj g⁻¹)
  set s' := MulAut.conj g⁻¹ s with hs'def
  set a : Fin 3 → (GaloisField 2 2)ˣ := fun i => ω ^ (v i).val with hadef
  have hsa : s' = spTorus a := by rw [← hv, vecElt_lam_eq]
  have hs'1 : s' ≠ 1 :=
    fun h => hs1 ((MulAut.conj g⁻¹).injective (by rw [← hs'def, h, map_one]))
  have ha3 : ∀ i, a i ^ 3 = 1 := fun i => by
    rw [hadef, ← pow_mul, mul_comm, pow_mul, hω3, one_pow]
  have hane : ¬ ∀ i, a i = 1 := by
    intro h
    apply hs'1
    rw [hsa, show a = 1 from funext h, map_one]
  by_cases h7 : ∃ t ∈ Subgroup.centralizer ({s'} : Set Sp6), orderOf t = 7
  · obtain ⟨t, ht, ht7⟩ := h7
    set T := spMat t with hT
    have hTt : T ^ 7 = 1 := by
      have h := pow_orderOf_eq_one t
      rw [ht7] at h
      have h' := congrArg spMat h
      simpa [spMat, hT] using h'
    have hT1 : T ≠ 1 := by
      intro h
      have : t = 1 := statedSp_ext (by simpa [spMat, hT] using h)
      rw [this, orderOf_one] at ht7
      norm_num at ht7
    have hTsp : Tᵀ * fromBlocks 0 1 (-1) 0 * T = fromBlocks 0 1 (-1) 0 :=
      (mem_statedSp_iff (g := (t : GL (Fin 3 ⊕ Fin 3) (GaloisField 2 2)))).mp t.2
    have hcomm : diagonal (Sum.elim (fun i => (a i : GaloisField 2 2))
          fun i => ((a i)⁻¹ : (GaloisField 2 2)ˣ)) * T =
        T * diagonal (Sum.elim (fun i => (a i : GaloisField 2 2))
          fun i => ((a i)⁻¹ : (GaloisField 2 2)ˣ)) := by
      have h := Subgroup.mem_centralizer_singleton_iff.mp ht
      have h' := congrArg spMat h
      simp only [spMat, Subgroup.coe_mul, Units.val_mul] at h'
      rw [← CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.coe_torusHom, ← hsa, hT]
      exact h'.symm
    rcases sp_trivial_or_regular_of_commute_pow_seven' hF4 hTt hT1 hTsp ha3 hcomm with h | hreg
    · exact absurd h hane
    set c := a 0 with hc
    have hc1 : c ≠ 1 := hreg 0
    have hc3 : c ^ 3 = 1 := ha3 0
    have hval : ∀ i, a i = c ∨ a i = c⁻¹ := by
      intro i
      have hv0 : (v 0).val ≠ 0 := fun h => hc1 (by rw [hc, hadef]; simp only [h, pow_zero])
      have hvi : (v i).val ≠ 0 := fun h => hreg i (by rw [hadef]; simp only [h, pow_zero])
      have h0 := (v 0).val_lt
      have hi := (v i).val_lt
      rcases (by omega : (v i).val = (v 0).val ∨ (v i).val + (v 0).val = 3) with h | h
      · left
        rw [hc, hadef]
        simp only [h]
      · right
        rw [eq_inv_iff_mul_eq_one, hc, hadef]
        simp only
        rw [← pow_add, h, hω3]
    have hflip : ∀ (b : Fin 3 → (GaloisField 2 2)ˣ) (i : Fin 3), b i = c⁻¹ →
        ∃ w : Sp6, w * spTorus b * w⁻¹ = spTorus (Function.update b i c) := by
      intro b i hbi
      refine ⟨lam i sl2W, ?_⟩
      rw [flip_conj_torusHom, hbi, inv_inv]
    have hnorm : ∃ w : Sp6, w * spTorus a * w⁻¹ = spTorus (fun _ : Fin 3 => c) := by
      have step : ∀ (b : Fin 3 → (GaloisField 2 2)ˣ) (i : Fin 3), (b i = c ∨ b i = c⁻¹) →
          ∃ w : Sp6, w * spTorus b * w⁻¹ = spTorus (Function.update b i c) := by
        intro b i hbi
        rcases hbi with h | h
        · exact ⟨1, by rw [one_mul, inv_one, mul_one, Function.update_eq_self_iff.mpr h.symm]⟩
        · exact hflip b i h
      obtain ⟨w₀, hw₀⟩ := step a 0 (hval 0)
      obtain ⟨w₁, hw₁⟩ := step (Function.update a 0 c) 1 (by
        rw [Function.update_of_ne (by decide)]; exact hval 1)
      obtain ⟨w₂, hw₂⟩ := step (Function.update (Function.update a 0 c) 1 c) 2 (by
        rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide)]; exact hval 2)
      refine ⟨w₂ * w₁ * w₀, ?_⟩
      have hfin : Function.update (Function.update (Function.update a 0 c) 1 c) 2 c =
          fun _ : Fin 3 => c := by
        funext j
        fin_cases j <;> simp [Function.update_apply]
      rw [← hfin, ← hw₂, ← hw₁, ← hw₀]
      group
    obtain ⟨w, hw⟩ := hnorm
    have hwconj : MulAut.conj w s' = spTorus (fun _ : Fin 3 => c) := by
      rw [MulAut.conj_apply, hsa, hw]
    apply CentQuasi.of_mulEquiv (MulAut.conj w)
    rw [hwconj]
    exact centQuasi_torusHom_const hF4 hc1 hc3 586579968000
  · left
    push Not at h7
    have h7' : ¬ 7 ∣ Nat.card (Subgroup.centralizer ({s'} : Set Sp6)) := by
      intro hd
      have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
      obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' 7 hd
      exact h7 t t.2 (by rwa [Subgroup.orderOf_coe])
    have hd : Nat.card (Subgroup.centralizer ({s'} : Set Sp6)) ∣ 7 * 586579968000 :=
      card_Sp6_eq ▸ Subgroup.card_subgroup_dvd_card _
    exact (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).mpr h7')).dvd_of_dvd_mul_left
      hd

theorem noCfgS429_projSp_three_four {S : Type} [Group S] [Finite S] (hs : IsSimpleGroup S)
    (hna : ∃ a b : S, a * b ≠ b * a) (φ : S ≃* projSp 3 (GaloisField 2 2)) : NoCfgS429 S := by
  set ψ : S ≃* Sp6 := φ.trans KFacts.KS21.Sp64.equivSp with hψ
  refine noCfgS429_of_inner_quasi (N₁ := 586579968000) (N₂ := 60480) (B := 35)
    (center_eq_bot_of_simple hs hna) ?_ ?_ (by norm_num) (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro τ h3
    have h3' : MulAut.congr φ τ ^ 3 = 1 := by rw [← map_pow, h3, map_one]
    exact (isInnerAut_congr φ τ).mp
      (cubeInner_of_not_three_dvd_card_outer RonanK432.not_three_dvd_card_outer_projSp6 _ h3')
  · intro E hE hE27 s hsE hs1
    apply CentQuasi.of_mulEquiv ψ
    refine centQuasi_Sp6 (E := E.map ψ.toMonoidHom) (Res423Two.isElemAbelian_map' _ hE)
      (by rw [Subgroup.card_map_of_injective (f := ψ.toMonoidHom) ψ.injective, hE27]) ⟨s, hsE, rfl⟩ ?_
    intro h
    exact hs1 (ψ.injective (by rw [h, map_one]))

end RowV

end CFSG.RankThree.PartTwo.Sec4.RonanK429
