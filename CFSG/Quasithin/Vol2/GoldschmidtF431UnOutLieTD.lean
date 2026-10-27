module

public import CFSG.Quasithin.Vol2.GoldschmidtF431UnOutLieTC
public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesBasic
public import CFSG.Quasithin.Vol2.GoldschmidtF431UnOutLieLev
public import CFSG.Quasithin.Vol2.GoldschmidtF431UnOutLieT

public noncomputable section

namespace CFSG.Quasithin.H13.F431.Un.OL

set_option linter.unusedSectionVars false

open Matrix Subgroup CFSG.LocalAnalysis CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.EvenBN.U4 CFSG.QuasithinUnique CFSG.Open CFSG.Quasithin

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K) [CharP K 2]

@[expose] def tfc_fix (B : Subgroup (Xg h)) : Subgroup (Xg h) := B ⊓ miyamotoFixBar h

theorem tfc_mem_fix {B : Subgroup (Xg h)} {x : Xg h} :
    x ∈ tfc_fix h B ↔ x ∈ B ∧ fbar h x = x := Iff.rfl

theorem tfc_fStab_fix {B : Subgroup (Xg h)} (hB : FStab h B) : FStab h (tfc_fix h B) := by
  intro φ x
  rw [tfc_mem_fix, tfc_mem_fix, hB φ x, fbar_fa_apply]
  exact and_congr_right fun _ => (fa h φ).injective.eq_iff

theorem tfc_centralizer_inf_Ssd {B : Subgroup (Xg h)} (hB : FStab h B) (F : Subgroup (K ≃+* K)) :
    Subgroup.centralizer ({fbar h} : Set (MulAut (Xg h))) ⊓ Ssd h B hB F =
      Ssd h (tfc_fix h B) (tfc_fStab_fix h hB) F := by
  ext α
  rw [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨hc, s, hs, φ, hφ, rfl⟩
    exact ⟨s, (tfc_mem_fix h).2 ⟨hs, (cj_fa_comm_fbar_iff h s φ).1 hc⟩, φ, hφ, rfl⟩
  · rintro ⟨s, hs, φ, hφ, rfl⟩
    exact ⟨(cj_fa_comm_fbar_iff h s φ).2 ((tfc_mem_fix h).1 hs).2,
      s, ((tfc_mem_fix h).1 hs).1, φ, hφ, rfl⟩

theorem tfc_Pfx_le_fix : Pfx h ≤ tfc_fix h (Pt h) := fun _ hx =>
  (tfc_mem_fix h).2 ⟨Psy_le_Pt h hx.1, hx.2⟩

theorem tfc_isPGroup_Pfx : IsPGroup 2 (Pfx h) :=
  IsPGroup.of_card (n := f * 4) (by rw [tfc_card_Pfx, pow_mul])

theorem tfc_twoPart_fix_Pt : twoPart (tfc_fix h (Pt h)) = (2 ^ f) ^ 4 := by
  apply le_antisymm
  · rw [← tfc_twoPart_FixBar h]
    exact twoPart_mono inf_le_right
  · rw [← tfc_card_Pfx h]
    exact card_le_twoPart (tfc_Pfx_le_fix h) (tfc_isPGroup_Pfx h)

theorem tfc_twoPart_card_mul {G₁ G₂ G₃ : Type*} [Group G₁] [Group G₂] [Group G₃]
    {X : Subgroup G₁} {Y : Subgroup G₂} {Z : Subgroup G₃} [Finite X] [Finite Y]
    (e : Nat.card Z = Nat.card X * Nat.card Y) : twoPart Z = twoPart X * twoPart Y := by
  unfold twoPart
  rw [e, Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne']
  simp [pow_add]

theorem Sylow_Tf (hf : 2 ≤ f) (F₂ Fk : Subgroup (K ≃+* K)) (hF : IsSylowTwoOf F₂ Fk) :
    IsSylowTwoOf (spTf (Ssd h (Psy h) (fStab_Psy h) F₂) (fbar h))
      (Subgroup.centralizer ({fbar h} : Set (MulAut (Xg h))) ⊓
        Ssd h (Pt h) (fStab_Pt h) Fk) := by
  have _ := hf
  have := finite_aut h
  rw [spTf_Ssd, tfc_centralizer_inf_Ssd h (fStab_Pt h) Fk]
  refine isSylowTwoOf_iff.2 ⟨Ssd_mono h (tfc_Pfx_le_fix h) hF.1, ?_, ?_⟩
  · obtain ⟨b, hb⟩ := IsPGroup.iff_card.1 hF.2.1
    refine IsPGroup.of_card (n := f * 4 + b) ?_
    rw [card_Ssd, tfc_card_Pfx, hb, pow_add, pow_mul]
  · rw [tfc_twoPart_card_mul (card_Ssd h (tfc_fix h (Pt h)) (tfc_fStab_fix h (fStab_Pt h)) Fk),
      tfc_twoPart_fix_Pt, ← hF.card_eq, card_Ssd, tfc_card_Pfx]

end CFSG.Quasithin.H13.F431.Un.OL
