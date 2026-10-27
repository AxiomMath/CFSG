module

public import CFSG.Quasithin.Vol2.KGFact3312Base
public import CFSG.Quasithin.Background.E2TwoProofSporJ2
public import CFSG.Sporadic.Bridge.J2Native
public import CFSG.Sporadic.J2.Simple
import CFSG.Blueprint.NativeSporadic
public import CFSG.Quasithin.Background.A3Structure312Facts
public import CFSG.Quasithin.Background.B5Statement
public import CFSG.Quasithin.Vol2.Ch1Faithful
public import CFSG.Quasithin.Vol2.Ch3Sec3KGSylow
public import CFSG.Quasithin.Vol2.Ch3Sec3Setup
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CPrime
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.DihedralAut
public import Certificates.Certificate8026Base

public section

namespace CFSG.Quasithin.H13.KG3312

open CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1.SporLat CFSG.Quasithin.E2P.SporB
open scoped Pointwise

theorem j2_overgroup_1920
    (Z : Subgroup ↥CFSG.Sporadic.J2.J) (hZ : j2Ctx.S ≤ Z)
    (hc : Nat.card Z = 1920) : Z = j2Ctx.Y 3 := by
  have hL : j2Ctx.D.Om.map (fun o => o.lbl.size) = #[1, 3, 9, 15, 3] := j2_Om_size
  obtain ⟨j, hj, rfl⟩ := lat_all j2Ctx hL Z hZ
  have hk : j2Ctx.k = 7 := rfl
  have hsize : (#[1, 3, 9, 15, 3] : Array ℕ).size = 5 := rfl
  rw [hsize] at hj hc ⊢
  unfold memberOrTop at hc ⊢
  split_ifs at hc ⊢ with h5
  · have hcj := lat_card j2Ctx hL j (by rw [hsize]; exact h5)
    rw [hcj, hk] at hc
    interval_cases j <;> first | exact absurd hc (by decide) | rfl
  · rw [Subgroup.card_top, CFSG.Sporadic.J2.card_J] at hc
    norm_num at hc

theorem j2_sylow :
    IsSylowTwoOf j2Ctx.S ⊤ := by
  have hN : j2Ctx.D.O.lbl.size = 4725 := j2_O_size
  refine K1.isSylowTwoOf_top_iff.mpr ⟨j2Ctx.S_isPGroup, ?_⟩
  have h1 := Subgroup.card_mul_index j2Ctx.S
  rw [j2Ctx.S_card, j2Ctx.hΓ, hN] at h1
  have h2 : j2Ctx.S.index = 4725 := by
    have : j2Ctx.k = 7 := rfl
    rw [this] at h1
    omega
  rw [h2]
  norm_num

theorem card_of_isExt_extra2_alt5 {B : Type} [Group B]
    (hB : IsExt B (fun V _ => IsExtraspecial2 2 V) (fun Y _ => IsAlt 5 Y)) : Nat.card B = 1920 := by
  refine card_of_isExt (a := 32) (b := 60) (fun V _ h => by rw [h.2]; norm_num)
    (fun Y _ h => ?_) hB
  obtain ⟨f⟩ := h
  rw [Nat.card_congr f.toEquiv, Nat.card_eq_fintype_card]
  rfl

theorem mem_stabilizer_of_unique_overgroup {Q Γ : Type} [Group Q] [Finite Q] [Group Γ]
    [Finite Γ] (e : Q ≃* Γ) (hZ : Subgroup.center Q = ⊥) {S₀ Y₀ : Subgroup Γ}
    (hS₀ : IsSylowTwoOf S₀ ⊤) {n : ℕ} (huniq : ∀ Z : Subgroup Γ, S₀ ≤ Z → Nat.card Z = n → Z = Y₀)
    (hidx : ∀ C : Subgroup Q, Nat.card C = n → ¬ 2 ∣ C.index) {A S : Subgroup (MulAut Q)}
    (hA : (MulAut.conj : Q →* MulAut Q).range ≤ A) (hS : IsSylowTwoOf S A) {B : Subgroup Q}
    (hB : Nat.card B = n) (hSB : S ≤ MulAction.stabilizer (MulAut Q) B) {d : MulAut Q}
    (hd : d ∈ Subgroup.normalizer (S : Set (MulAut Q))) :
    d ∈ MulAction.stabilizer (MulAut Q) B := by
  have hT := isSylowTwoOf_comap_conj (conj_injective hZ) hA hS
  have hdB : Nat.card ↥(d • B) = n := by
    rw [← Nat.card_congr (Subgroup.equivSMul d B).toEquiv, hB]
  have hTB := le_of_le_normalizer_of_odd_index hT.2.1 (comap_conj_le_normalizer hSB) (hidx B hB)
  have hTdB := le_of_le_normalizer_of_odd_index hT.2.1
    (comap_conj_le_normalizer (le_stabilizer_smul hSB hd)) (hidx _ hdB)
  exact MulAction.mem_stabilizer_iff.mpr (eq_of_overgroups e hS₀ huniq hT hTdB hTB hdB hB)

theorem j2_facts
    {Q : Type} [Group Q] [Finite Q]
    (e : Q ≃* ↥CFSG.Sporadic.J2.J) : Nat.card Q = 604800 ∧ Subgroup.center Q = ⊥ := by
  have hcardQ : Nat.card Q = 604800 := by
    rw [Nat.card_congr e.toEquiv, CFSG.Sporadic.J2.card_J]
  have : IsSimpleGroup Q :=
    @MulEquiv.isSimpleGroup Q _ ↥CFSG.Sporadic.J2.J (Subgroup.toGroup _)
      CFSG.Sporadic.J2.isSimpleGroup_J e
  exact ⟨hcardQ, center_eq_bot_of_isSimpleGroup (by rw [hcardQ]; norm_num)⟩

theorem factJ2Norm3312_holds :
    FactJ2Norm3312 := by
  intro Q _ _ hQ A S B hA hS hB hSB d hd _
  obtain ⟨e₀⟩ := hQ
  have e : Q ≃* ↥CFSG.Sporadic.J2.J := e₀.trans CFSG.Sporadic.Bridge.J2.nativeEquiv
  obtain ⟨hcardQ, hZ⟩ := j2_facts e
  have hidx : ∀ C : Subgroup Q, Nat.card C = 1920 → ¬ 2 ∣ C.index := by
    intro C hC
    have h := Subgroup.card_mul_index C
    rw [hC, hcardQ] at h
    omega
  have hfin : Finite ↥CFSG.Sporadic.J2.J := inferInstance
  exact @mem_stabilizer_of_unique_overgroup Q ↥CFSG.Sporadic.J2.J _ _ (Subgroup.toGroup _) hfin e
    hZ _ _ j2_sylow 1920 j2_overgroup_1920 hidx A S hA hS B (card_of_isExt_extra2_alt5 hB) hSB d
    (Subgroup.mem_inf.mp hd).1

end CFSG.Quasithin.H13.KG3312
