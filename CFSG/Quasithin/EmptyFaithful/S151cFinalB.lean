module

public import CFSG.Quasithin.EmptyFaithful.S151cOm4b
public import CFSG.Quasithin.EmptyFaithful.S151cGlue

public section

open CFSG.QuasithinUnique (quasithinIsQTKECat)

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G] {T Mc M : Subgroup G}

@[expose] def DescAt (T M W : Subgroup G) : Prop :=
  W = conjClosure (quasithinOmegaOneCenter T ⊓ W) (preOn M W (JhatOn M W))

@[expose] def Lemma1517ConclAt (T M W : Subgroup G) : Prop :=
  Lemma1517Cases T M W (JhatOn M W) ∧ (W < VZ T M → Case1517Three M W (JhatOn M W))

@[expose] def Lemma1518ConclAt (M W : Subgroup G) : Prop :=
  (qhatOn M W = 2 ∧ qOn M W = 2) ∨
    (Case1517Three M W (JhatOn M W) ∧ qhatOn M W = ((3 / 2 : ℚ) : WithTop ℚ) ∧ qOn M W = 2)

theorem lemma1517Concl_iff (T Mc M : Subgroup G) :
    Lemma1517Concl T Mc M ↔ Lemma1517ConclAt T M (V154 T Mc M) := Iff.rfl

theorem lemma1518Concl_iff (T Mc M : Subgroup G) :
    Lemma1518Concl T Mc M ↔ Lemma1518ConclAt M (V154 T Mc M) := Iff.rfl

theorem facts_of_six (h : quasithinQTFE14Cat G T Mc) (hM : IsMf T Mc M)
    (hb : Case1512Six T Mc M) :
    DescAt T M (uJ154 T M) ∧ IsTwoNilpotentOn M (uJ154 T M) ∧
      Lemma1517ConclAt T M (uJ154 T M) ∧ Lemma1518ConclAt M (uJ154 T M) := by
  obtain ⟨hU, hΩ⟩ := hb.2.2.2.2.2.1
  have hcard16 : Nat.card (uJ154 T M) = 16 := hb.2.2.2.1
  have hΩ' : IsOmegaFourPlus (autI hU M) := hΩ
  have hJ : JhatOn M (uJ154 T M) = autOn M (uJ154 T M) := by
    rw [JhatOn_eq_Jhat_autI M hU]
    exact Jhat_eq_of_isOmegaFourPlus hΩ'
  have hC3 : Case1517Three M (uJ154 T M) (JhatOn M (uJ154 T M)) :=
    ⟨hcard16, hJ.symm, ⟨hU, hΩ⟩⟩
  have hNil : IsTwoNilpotentOn M (uJ154 T M) :=
    (isOmegaFourPlus_twoNilp hΩ' : TwoNilpAut (autI hU M))
  have h17 : Lemma1517ConclAt T M (uJ154 T M) :=
    ⟨Or.inr (Or.inr (Or.inl hC3)), fun _ => hC3⟩
  have h18 : Lemma1518ConclAt M (uJ154 T M) := by
    refine Or.inr ⟨hC3, ?_, ?_⟩
    · rw [qhatOn_eq hU]
      exact qhatOf_eq_of_isOmegaFourPlus (U := IntMod (uJ154 T M) hU) hΩ'
    · rw [qOn_eq hU]
      exact qOf_eq_of_isOmegaFourPlus (U := IntMod (uJ154 T M) hU) hΩ'
  refine ⟨?_, hNil, h17, h18⟩
  set W := uJ154 T M with hW
  have hMN : M ≤ Subgroup.normalizer (W : Set G) := le_normalizer_uJ154 T M
  have hVT : W ≤ T := (uJ154_le_VZ T M).trans (isTwoReducedIn_VZ h hM.1.1).2
  have hW0 : W ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hcard16
    omega
  obtain ⟨z, hzW, hz1, hzZ⟩ := exists_ne_one_mem_omegaOneCenter_of_normalized h.sylow.1 hVT hW0
    (hM.1.1.2.trans hMN)
  set K := preOn M W (JhatOn M W) with hK
  set C := conjClosure (quasithinOmegaOneCenter T ⊓ W) K with hC
  have hCW : C ≤ W := by
    refine conjClosure_le fun k hk z hz => ?_
    exact (Subgroup.mem_normalizer_iff.mp (hMN (preOn_le _ _ _ hk)) z).mp hz.2
  have hzC : z ∈ C := le_conjClosure _ _ ⟨hzZ, hzW⟩
  set B : Subgroup (IntMod W hU) := C.subgroupOf W with hB
  have hCinv : ∀ y ∈ autI hU M, ∀ b ∈ B, y b ∈ B := by
    intro y hy b hb'
    obtain ⟨m, hm, rfl⟩ := (mem_autI hU).1 hy
    have hmK : (m : G) ∈ K := by
      refine mem_preOn.mpr ⟨hm, m.2, ?_⟩
      rw [hJ]
      exact convI_mem_autI hU hm m.2
    have hbC : b.val ∈ C := hb'
    have : (m : G) * b.val * (m : G)⁻¹ ∈ C :=
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure _ _ hmK) b.val).mp hbC
    show (convI hU m b).val ∈ C
    rw [convI_apply_val]
    exact this
  have hBne : B ≠ ⊥ := by
    intro hbot
    have h1 := (Subgroup.eq_bot_iff_forall B).mp hbot (IntMod.mk hU ⟨z, hzW⟩) hzC
    exact hz1 (congrArg IntMod.val h1)
  have htop := isOmegaFourPlus_irreducible hΩ' hCinv hBne
  refine le_antisymm (fun w hw => ?_) hCW
  have : IntMod.mk hU ⟨w, hw⟩ ∈ B := by rw [htop]; trivial
  exact this

end CFSG.Quasithin
