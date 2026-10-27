module

public import CFSG.Quasithin.Recognition.SzVBEvenMain
public import CFSG.Quasithin.Recognition.SzVBAssembly
public import CFSG.Quasithin.Recognition.SzVBGeo

public section


namespace CFSG.Quasithin.SzVB

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.CosetGeom

variable {G : Type} [Group G] [Finite G] {K1 L2 S Zs : Subgroup G}

theorem exists_kleinData_of_setting (hRO : RankOneListedFacts.{0}) (h : R1SettingLegacyBare K1 L2 S Zs) :
    ∃ z : G, KleinData (K1 ⊔ S) (conjClosure Zs L2) z := by
  have hyp := F112J2.amalgamHypV_of_setting hRO h
  have hZ : Zs ≠ ⊥ := by
    intro hZ
    have := h.card_Z
    rw [hZ, Subgroup.card_bot] at this
    omega
  obtain ⟨⟨z, hz⟩, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hZ
  have hz1' : z ≠ 1 := fun e => hz1 (Subtype.ext e)
  have hPc : K1 ⊔ S ≤ Subgroup.centralizer (Zs : Set G) :=
    sup_le h.K1_cent_Z (F112J2.S_le_centralizer_Z h)
  exact ⟨z,
    { V_le := h.V_le.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 _)
      elemAbelian := hyp.elemAbelian
      card_eq := h.V_card
      z_mem := le_conjClosure Zs L2 hz
      z_ne_one := hz1'
      z_cent := fun x hx => ((Subgroup.mem_centralizer_iff.mp (hPc hx)) z hz).symm }⟩

theorem exists_geoCtx_of_setting (hRO : RankOneListedFacts.{0}) (h : R1SettingLegacyBare K1 L2 S Zs) :
    ∃ z : G, GeoCtx (K1 ⊔ L2 ⊔ S) (L2 ⊔ S) (K1 ⊔ S) S (conjClosure Zs L2) z := by
  obtain ⟨z, hK⟩ := exists_kleinData_of_setting hRO h
  have hR := F112J2.hyp111R_of_setting hRO h
  exact ⟨z, F112J2.amalgamHypV_of_setting hRO h, F112J2.isNaturalS3_of_setting hRO h,
    F112J2.inf_L2S_K1S hR h.s3, F112J2.relIndex_L2S hR h.s3, hK⟩

theorem exists_evenCtx_of_setting (hRO : RankOneListedFacts.{0}) (h : R1SettingLegacyBare K1 L2 S Zs)
    {n : ℕ} (hn : 2 ≤ n) (hX : IsBenderQuot n (OTwoQuot K1))
    (hne : ¬ IsL2Quot 2 (OTwoQuot K1)) :
    ∃ z : G, EvenCtx (K1 ⊔ L2 ⊔ S) (L2 ⊔ S) (K1 ⊔ S) S (conjClosure Zs L2) z := by
  obtain ⟨z, hK⟩ := exists_kleinData_of_setting hRO h
  have hR := F112J2.hyp111R_of_setting hRO h
  exact ⟨z, ⟨⟨F112J2.amalgamHypV_of_setting hRO h, F112J2.isNaturalS3_of_setting hRO h,
    F112J2.inf_L2S_K1S hR h.s3, F112J2.relIndex_L2S hR h.s3, hK⟩,
    benderLocalFacts_of_setting hRO h hn hX hne⟩⟩

theorem even_critDist_false_of_setting (hRO : RankOneListedFacts.{0}) (h : R1SettingLegacyBare K1 L2 S Zs)
    {n : ℕ} (hn : 2 ≤ n) (hX : IsBenderQuot n (OTwoQuot K1))
    (hne : ¬ IsL2Quot 2 (OTwoQuot K1))
    (hab : ⁅vBeta K1 L2 S Zs, vBeta K1 L2 S Zs⁆ = ⊥) :
    ¬ Even (critDist (K1 ⊔ L2 ⊔ S) (L2 ⊔ S) (K1 ⊔ S) (conjClosure Zs L2)) := by
  intro hev
  obtain ⟨z, hC⟩ := exists_evenCtx_of_setting hRO h hn hX hne
  exact even_critDist_false hC hev (three_le_critDist_of_comm hRO h hab)

end CFSG.Quasithin.SzVB
