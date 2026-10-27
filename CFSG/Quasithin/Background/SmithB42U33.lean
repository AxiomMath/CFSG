module

public import CFSG.Quasithin.Background.SmithB42U33SixProof
public import CFSG.Quasithin.Background.SmithB42U33Off
public import CFSG.Quasithin.Background.SmithB42HatA6
public import CFSG.GH74.SmallRanks.PSU3

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Quasithin.H13 CFSG.Quasithin.H13.Orbit

namespace B42U33

variable {V : Type} [CommGroup V] [Finite V]

theorem rank_le_two {L A : Subgroup (MulAut V)} (hP : B42TypeU33 ↥L) (hAL : A ≤ L)
    (hAe : IsElemAbelian2 A) {k : ℕ} (hk : Nat.card A = 2 ^ k) : k ≤ 2 := by
  have : Finite (MulAut V) := Finite.of_injective _ DFunLike.coe_injective
  let f : ↥A →* ↥L ⧸ Subgroup.center ↥L :=
    (QuotientGroup.mk' _).comp (Subgroup.inclusion hAL)
  have hf : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro a ha
    rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hP.1,
      Subgroup.mem_bot] at ha
    have h1 : (a : MulAut V) = 1 := congrArg Subtype.val ha
    exact Subtype.ext h1
  have h1 := CFSG.SectionRank.le_pRank_of_injective (p := 2) (H := ⊤) Nat.one_lt_two
    (fun a b => Subtype.ext (hAe.1 _ a.2 _ b.2)) (fun a => Subtype.ext (hAe.2 _ a.2)) hk f hf
    le_top
  exact h1.trans (CFSG.GH74.SmallRanks.twoRank_le_two_of_statedClassicalModel_PSU_three_three hP.2)

theorem card_range_g2QAct : Nat.card (g2QAct (ZMod 2)).range = 12096 := by
  rw [← card_g2Two]
  exact (Nat.card_congr (MonoidHom.ofInjective g2QAct_injective).toEquiv).symm

omit [Finite V] in
theorem exists_equiv_of_g2NaturalDerived {L : Subgroup (MulAut V)}
    (h : G2NaturalDerived L ⊤ ⊥ 1) :
    ∃ e : V ≃* ModQ, L.map (MulAut.congr e).toMonoidHom =
      (g2Derived (ZMod 2)).map (g2QAct (ZMod 2)) := by
  obtain ⟨K, _, _, hK, hR⟩ := h
  have hK2 : Nat.card K = 2 := by rw [hK, pow_one]
  have := charP_two_of_natCard_two hK2
  obtain ⟨π, β, hβ⟩ := (CFSG.Quasithin.H.Mathieu.realizes_iff _ L ⊤ ⊥).1 hR
  let e : V ≃* (FFModel.zornQ (quasithinG2 K)).Mod :=
    realizeEquiv (D := FFModel.zornQ ⁅quasithinG2 K, quasithinG2 K⁆) hβ
  have hLe : L.map (MulAut.congr e).toMonoidHom = (g2Derived K).map (g2QAct K) :=
    map_congr_eq_of_equivariant e π hβ.1 (g2QAct K)
      (fun γ => ⟨γ.1, Subgroup.commutator_le_self _ γ.2⟩) (realizeEquiv_zornQ hβ) _
      (mem_map_g2Derived_iff (g2QAct K))
  refine ⟨e.trans (modQEquivK hK2).symm, ?_⟩
  have hcongr : (MulAut.congr (e.trans (modQEquivK hK2).symm)).toMonoidHom =
      (MulAut.congr (modQEquivK hK2).symm).toMonoidHom.comp (MulAut.congr e).toMonoidHom :=
    MonoidHom.ext fun x => MulEquiv.ext fun _ => rfl
  rw [hcongr, ← Subgroup.map_map, hLe, Subgroup.map_map, ← map_g2Derived_conjF2Hom hK2,
    Subgroup.map_map]
  congr 1
  exact MonoidHom.ext fun g => congr_modQEquivK_symm hK2 g

end B42U33

open B42U33

theorem asB42U33_of_six
    (hsix : U33SixNatural) : AsB42U33 := by
  intro V _ _ hV G L hHyp hP A hA
  have hcard := card_V hV hHyp hP hA
  have hLG := HatA6.le_of_b4Hyp hHyp
  have hGN := HatA6.le_normalizer_of_b4Hyp hHyp
  obtain ⟨e, hLe⟩ := exists_equiv_of_g2NaturalDerived (hsix V hV hcard L hP)
  set φ := (MulAut.congr e).toMonoidHom with hφ
  have hφinj : Function.Injective φ := (MulAut.congr e).injective
  have hG : ∀ x ∈ G, MulAut.congr e x ∈ (g2QAct (ZMod 2)).range := by
    intro x hx
    refine normalizer_two_Q _ fun h => ?_
    obtain ⟨h', rfl⟩ := (MulAut.congr e).surjective h
    have hxN := Subgroup.mem_normalizer_iff.1 (hGN hx) h'
    rw [← hLe, ← map_inv, ← map_mul, ← map_mul]
    change φ h' ∈ L.map φ ↔ φ (x * h' * x⁻¹) ∈ L.map φ
    rw [Subgroup.mem_map_iff_mem hφinj, Subgroup.mem_map_iff_mem hφinj]
    exact hxN
  have hoff : ∀ B, IsFFStarOffender G B → Nat.card B = 8 ∧ Nat.card (fixV B) = 8 :=
    fun B hB => offender_facts_of_equiv e hG hB
  obtain ⟨hA8, -⟩ := hoff A hA
  have hAL : ¬ A ≤ L := fun h => by
    have := rank_le_two hP h hA.2.2.1 (k := 3) (by rw [hA8]; norm_num)
    omega
  have hL6048 : Nat.card L = 6048 := card_of_b42TypeU33 hP
  have : Finite ModQ := Nat.finite_of_card_ne_zero (by rw [card_ModQ]; norm_num)
  have : Finite (MulAut ModQ) := Finite.of_injective _ DFunLike.coe_injective
  set J := ffJ G with hJdef
  have hJG : J ≤ G := iSup₂_le fun B hB => hB.1
  have hLJ : L ≤ J :=
    CFSG.QuasithinUnique.Bridge.TypeList.le_ffJ_of_b4Hyp (KP := CFSG.SectionRank.IsKGroupCat)
      hV hHyp hA
  have hAJ : A ≤ J := le_iSup₂ (f := fun B (_ : IsFFStarOffender G B) => B) A hA
  have hLJlt : L < J := lt_of_le_of_ne hLJ fun h => hAL (h ▸ hAJ)
  have hJcard : Nat.card J = 12096 := by
    have h1 : Nat.card L ∣ Nat.card J := Subgroup.card_dvd_of_le hLJ
    have h2 : Nat.card L < Nat.card J := Subgroup.card_lt_of_lt hLJlt
    have h3 : Nat.card J ≤ 12096 := by
      rw [← card_range_g2QAct, ← Subgroup.card_map_of_injective hφinj]
      refine Subgroup.card_le_of_le ?_
      rintro _ ⟨x, hx, rfl⟩
      exact hG x (hJG hx)
    rw [hL6048] at h1 h2
    obtain ⟨c, hc⟩ := h1
    rw [hc] at h2 h3 ⊢
    have : c = 2 := by omega
    rw [this]
  have hJimg : J.map φ = (g2QAct (ZMod 2)).range := by
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro _ ⟨x, hx, rfl⟩
      exact hG x (hJG hx)
    · rw [card_range_g2QAct, Subgroup.card_map_of_injective hφinj, hJcard]
  have hnat : G2Natural J ⊤ ⊥ 1 := by
    refine ⟨ZMod 2, inferInstance, inferInstance, by rw [Nat.card_zmod, pow_one], ?_⟩
    let r : ↥J ≃* ↥(g2QAct (ZMod 2)).range :=
      (J.equivMapOfInjective φ hφinj).trans (MulEquiv.subgroupCongr hJimg)
    refine H.FFModel.realizes_of_equiv (fun _ _ _ _ => trivial)
      ((Subgroup.topEquiv : (⊤ : Subgroup V) ≃* V).trans e) r (fun h u => ?_)
      (FFModel.zornQ_isActionModel (quasithinG2 (ZMod 2)) le_rfl).realizesMod_range
    change MulAut.congr e (h : MulAut V) (e u) = e ((h : MulAut V) u)
    exact congr_apply_eq e _ _
  refine Or.inr (Or.inr (Or.inr (Or.inl ⟨⟨1, hnat, ?_, fun h => absurd h (lt_irrefl 1)⟩, ?_⟩)))
  ·
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    rw [rk, hA8, show (8 : ℕ) = 2 ^ 3 by norm_num, padicValNat.prime_pow]
  ·
    refine qOf_eq_of_offenders hV le_rfl (fun B hB => ?_) ⟨A, hA, B1_4_1 hV hA⟩
    obtain ⟨hB8, hB8'⟩ := hoff B hB
    refine HatA6.one_le_rAV_of_le_index hV hB.isA2 ?_
    have := (fixV B).card_mul_index
    rw [hB8', hcard] at this
    omega

theorem asB42U33_holds :
    AsB42U33 :=
  asB42U33_of_six u33SixNatural

end CFSG.Quasithin
