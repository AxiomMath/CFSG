module

public import CFSG.Quasithin.Vol2.Ch3Sec2Lem328Sec
public import CFSG.Quasithin.Vol2.Ch3Sec2Lem328Vocab
public import CFSG.Quasithin.Vol2.Ch11SecA02Setup
public import CFSG.Quasithin.Vol2.Ch11SecA14Lines
public import CFSG.Quasithin.Vol2.Ch11SecSCartanT2
public import CFSG.Quasithin.Vol2.Ch11SecCB51Core
public import CFSG.Quasithin.Background.B2FactorizationOffender

public section

namespace CFSG.Quasithin.Vol2.Ch11.O10

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ}

omit [Finite G] in
theorem isPGroup_autOn_of {T V : Subgroup G} (hT : IsPGroup 2 ↥T) : IsPGroup 2 ↥(autOn T V) := by
  unfold autOn
  exact (hT.comap_of_injective _ (Subgroup.normalizer (V : Set G)).subtype_injective).map _

theorem fixed_autOn_eq_bot [IsMulCommutative ↥(fsuV T I)] (h : Hyp11 G T L I n)
    (hcV : fsuV T I ⊓ Subgroup.centralizer (L : Set G) = ⊥) :
    XMod.fixed ↥(autOn L (fsuV T I)) (⊤ : Subgroup ↥(fsuV T I)) = ⊥ := by
  have hLV := SecA.L_le_normalizer_fsuV h
  rw [eq_bot_iff]
  intro v hv
  have hv' : v ∈ fixV (autOn L (fsuV T I)) := by
    rw [mem_fixV]
    intro a ha
    exact hv.2 ⟨a, ha⟩
  rw [fixV_autOn hLV, Subgroup.mem_subgroupOf] at hv'
  have h1 : (v : G) ∈ fsuV T I ⊓ Subgroup.centralizer (L : Set G) := ⟨v.2, hv'⟩
  rw [hcV] at h1
  exact Subgroup.mem_bot.mpr (Subtype.ext (Subgroup.mem_bot.mp h1))

theorem exists_b4Hyp (h1102 : Stmt11_0_2) (h8 : Ch10.TmpL6_3_2_2_eight) (h : Hyp11 G T L I n)
    (hcV : fsuV T I ⊓ Subgroup.centralizer (L : Set G) = ⊥) [IsMulCommutative ↥(fsuV T I)] :
    ∃ S : Subgroup (MulAut ↥(fsuV T I)),
      QuasithinUnique.IsSylowTwoOf S
        (Subgroup.normalizer (autOn L (fsuV T I) : Set (MulAut ↥(fsuV T I)))) ∧
      autOn T (fsuV T I) ≤ S ∧ Sec328 (autOn L (fsuV T I)) S ∧
      B4Hyp (autOn L (fsuV T I) ⊔ S) (autOn L (fsuV T I)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLV := SecA.L_le_normalizer_fsuV h
  have hTV := SecA.T_le_normalizer_fsuV T I
  have hO2 := SecA.pCoreOf_autOn_eq_bot h8 h
  have hq := InternalSec.isQuasisimple_autOn hLV h.fsu.quasisimple hO2
    (SecA.not_le_centralizer_fsuV h)
  have hker : IsPGroup 2 ↥(L ⊓ Subgroup.centralizer (fsuV T I : Set G)) := by
    rw [SecA.centralizer_eq_pCoreOf h1102 h]
    exact CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L
  have hsqtk := InternalSec.sqtkGroup_autOn hLV (SecA.sqtkGroup_L h) hker
  obtain ⟨_, hirr, -⟩ := h1102 G T L I n h
  obtain ⟨htop, hIrr⟩ := top_mem_irrPlus_autOn hLV
    ⟨le_rfl, hirr.2.1, hirr.2.2.1, hirr.2.2.2.1, hirr.2.2.2.2.1, hirr.2.2.2.2.2⟩
  obtain ⟨S, hS, hTS⟩ := exists_isSylowTwoOf_ge (SecS.autOn_le_normalizer (V := fsuV T I) h.normal)
    (isPGroup_autOn_of h.fsu.sylow.1)
  have hsec : Sec328 (autOn L (fsuV T I)) S :=
    { sq := fun v => Subtype.ext (by simpa using (SecA.isElemAbelian_fsuV h).2 v v.2)
      quasi := hq
      sqtk := hsqtk
      irr := by rw [htop]; exact hIrr
      top := htop
      two := hS.2.1
      norm := hS.1 }
  refine ⟨S, hS, hTS, hsec, hsec.sqtk_sup, hsec.genFitting_eq.symm, hq, ?_⟩
  have h3 := hIrr.2.2.2
  rw [fixed_autOn_eq_bot h hcV] at h3
  exact h3

theorem isFFStarOffender_autOn [IsMulCommutative ↥(fsuV T I)] (h : Hyp11 G T L I n)
    {S : Subgroup (MulAut ↥(fsuV T I))} (hTS : autOn T (fsuV T I) ≤ S) {A : Subgroup G}
    (hA : IsMaxElemAbelian T A) (hAV : ¬ A ≤ Subgroup.centralizer (fsuV T I : Set G)) :
    IsFFStarOffender (autOn L (fsuV T I) ⊔ S) (autOn A (fsuV T I)) := by
  have hVe := SecA.isElemAbelian_fsuV h
  have h1 := offenderImages_isFFStarOffender hVe (SecA.fsuV_le_T h)
    (SecA.T_le_normalizer_fsuV T I) ⟨A, ⟨hA, hAV⟩, rfl⟩
  exact isFFStarOffender_mono (hTS.trans le_sup_right) h1

theorem le_ffJ_of_offender [IsMulCommutative ↥(fsuV T I)] (h : Hyp11 G T L I n)
    {S : Subgroup (MulAut ↥(fsuV T I))} (hTS : autOn T (fsuV T I) ≤ S)
    (hsec : Sec328 (autOn L (fsuV T I)) S) {A : Subgroup G} (hA : IsMaxElemAbelian T A)
    (hAV : ¬ A ≤ Subgroup.centralizer (fsuV T I : Set G)) :
    autOn L (fsuV T I) ≤ ffJ (autOn L (fsuV T I) ⊔ S) := by
  have hoff := isFFStarOffender_autOn h hTS hA hAV
  have hAN : autOn A (fsuV T I) ≤
      Subgroup.normalizer (autOn L (fsuV T I) : Set (MulAut ↥(fsuV T I))) :=
    (SecA.autOn_mono hA.1).trans (hTS.trans hsec.norm)
  rcases SecC.B51.commutator_eq_or_eq_bot hsec.quasi hAN with h1 | h1
  · exact B1Red.K_le_ffJ le_sup_left hoff h1
  · exfalso
    apply hoff.2.1
    rw [eq_bot_iff]
    intro x hx
    have hx2 : ∃ k : ℕ, x ^ 2 ^ k = 1 :=
      (isPGroup_autOn_of (h.fsu.sylow.1.to_le hA.1)) ⟨x, hx⟩ |>.imp fun k hk =>
        congrArg Subtype.val hk
    obtain ⟨k, hk⟩ := hx2
    refine Subgroup.mem_bot.mpr (hsec.eq_one (fun l hl => ?_) hk)
    have := (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h1) hl
    exact (Subgroup.mem_centralizer_iff.mp this x hx).symm

end CFSG.Quasithin.Vol2.Ch11.O10
