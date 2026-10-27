module

public import CFSG.Quasithin.H13.L32NLem14324r

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique

namespace L14324

variable {G : Type} [Group G] [Finite G]

namespace Ctx5

variable {T L V V₂ : Subgroup G} {g a : G} {D : HatModelU (fsuU T V)}
  (C : Ctx5 G T L V V₂ g a D)
include C

theorem card_dvd (M : S8Five.Model5 (D.img (l32nH T V))) {K : Subgroup G}
    (hK : K ∈ cComp (l32nH T V)) (hKimg : D.img K = M.A) :
    20160 ∣ Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKH : K ≤ l32nH T V := le_of_mem_cComp hK
  set f : ↥K →* (D.V ≃ₗ[ZMod 2] D.V) :=
    D.ρ.comp (Subgroup.inclusion (hKH.trans (H_N))) with hf
  have hker : CFSG.pCore 2 ↥K ≤ f.ker := by
    intro k hk
    have hkG : (k : G) ∈ pCoreOf 2 K := by
      exact ⟨k, hk, rfl⟩
    have hkH : (k : G) ∈ pCoreOf 2 (l32nH T V) :=
      A4.pCoreOf_le_of_subnormal 2 (subnormal_of_mem_cComp hK) hkG
    exact C.rho_eq_one_of_pCoreOf hkH _
  have hn : (CFSG.pCore 2 ↥K).Normal := CFSG.pCore_normal
  set fb := QuotientGroup.lift (CFSG.pCore 2 ↥K) f hker with hfb
  have hrange : fb.range = M.A := by
    rw [← hKimg]
    ext γ
    constructor
    · rintro ⟨q, rfl⟩
      obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥K) q
      exact L128A.HatU.rho_mem_img D k.2 _
    · intro hγ
      obtain ⟨k, hk, hkN, rfl⟩ := (L128A.HatU.mem_img D).mp hγ
      exact ⟨QuotientGroup.mk' (CFSG.pCore 2 ↥K) ⟨k, hk⟩, rfl⟩
  have h := Subgroup.card_range_dvd fb
  rw [hrange, M.card_A] at h
  exact h

theorem false_of_model5 (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4) (h36 : A36ForSQTK)
    (h37 : A37ForSQTK) (h39 : A39ForSQTK) (h1434 : Lemma1434One)
    (M : S8Five.Model5 (D.img (l32nH T V))) : False := by
  classical
  obtain ⟨K, hK, hKimg, hKn⟩ := C.exists_comp h37 h39 M
  have hZK := C.comm_zD_ne h1332 h1334 h36 M hK hKimg hKn
  set ZD := quasithinOmegaOneCenter T ⊓ centerOf (i128 T L V (fsuV1 T V)) with hZD
  have hsyl : IsSylowTwoOf T (l32nH T V) := isSylowTwoOf_of_isSylowTwo C.hyp.fsu.sylow C.T_le
  obtain ⟨S, hS⟩ := exists_sylow_coe_eq C.hyp.fsu.sylow
  have hInH : InH (S : Subgroup G) (l32nH T V) := ⟨hS ▸ C.T_le, C.pCoreOf_ne⟩
  have hF : l32nH T V ⊓ Subgroup.centralizer (pCoreOf 2 (l32nH T V) : Set G) ≤
      pCoreOf 2 (l32nH T V) := charTwo_of_inH' C.hyp.fsu.qtke C.hyp.fsu.sylow (hS ▸ hInH)
  have hR2 : IsTwoReducedIn (l32nH T V) (conjClosure ZD (l32nH T V)) :=
    isTwoReducedIn_conjClosure_of_sylowIn C.T_le C.hyp.fsu.sylow.1 hsyl.2.2 hF inf_le_left
  have hcomm : ⁅conjClosure ZD (l32nH T V), K⁆ ≠ ⊥ := fun h => hZK (le_bot_iff.mp
    (h ▸ Subgroup.commutator_mono (le_conjClosure ZD (l32nH T V)) le_rfl))
  have hTFAE := lemma_1_2_10_of_a36 C.hyp.fsu.qtke C.hyp.fsu.simple C.hyp.fsu.nonabelian h36 S
    hInH hK
  have hex : ∃ V' : Subgroup G, IsTwoReducedIn (l32nH T V) V' ∧ ⁅V', K⁆ ≠ ⊥ :=
    ⟨_, hR2, hcomm⟩
  have hKf : quasithinIsFaithfulLocal (S : Subgroup G) K := (hTFAE.out 2 1).mp hex
  rw [hS] at hKf
  have hdvd := C.card_dvd M hK hKimg
  rcases h1434 G T L C.hyp.hyp K hKf with h5 | h3
  · obtain ⟨e⟩ := h5
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
      Fintype.card_fin] at hdvd
    exact absurd hdvd (by decide)
  · obtain ⟨e⟩ := nonempty_equiv_SL32_of_lieModel h3
    rw [Nat.card_congr e.toEquiv, HSType.card_SL_three_two] at hdvd
    exact absurd hdvd (by decide)

end Ctx5

theorem false_of_concl5 (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4) (h1222 : Stmt12_2_2)
    (h12213 : Stmt12_2_13) (h12813 : Lemma12_8_13) (h14312 : Lemma14312One)
    (hFixS : G11.SzG11S.TheoremG112FixS) (h36 : A36ForSQTK) (h37 : A37ForSQTK)
    (h38 : A38ForSQTK) (h39 : A39ForSQTK) (h1434 : Lemma1434One)
    {T L V : Subgroup G} (h : Hyp14310One G T L V) (hlt : fsuV1 T V < centerOf (fsuU T V))
    {V₂ : Subgroup G} {g : G} (hV₂ : IsL32NPlane T V V₂) (hgP : g ∈ p128 T L V)
    (hgN : g ∉ l32nH T V) (D : HatModelU (fsuU T V))
    (h5 : G112Concl5 D.B (D.img (l32nH T V))) : False := by
  obtain ⟨a, C⟩ := exists_ctx5 h1332 h1334 h1222 h12213 h12813 h14312 hFixS h37 h38 h39 h hlt
    hV₂ hgP hgN D
  obtain ⟨M⟩ := S8Five.exists_model5 C.alt C.nd h5
  exact C.false_of_model5 h1332 h1334 h36 h37 h39 h1434 M

end L14324

end CFSG.Quasithin.H13
