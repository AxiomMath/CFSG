module

public import CFSG.Quasithin.Background.Harris.R1.QbetaDAbel
public import CFSG.Quasithin.Background.Harris.R1.QbetaN2

public section

namespace CFSG.Quasithin.Background.Harris.R1

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.SzR1 CFSG.Quasithin.A5Model
  CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G] {K1 L2 S Zs : Subgroup G}

theorem dAbel_of_ZS_inst (hRO : RankOneListedFacts.{0}) (hset : R1SettingLegacyBare K1 L2 S Zs)
    (hZS : ∀ u ∈ S, u * u = 1 → (∀ s ∈ S, u * s = s * u) → u ∈ Zs)
    (hL24 : IsL2Quot 2 (OTwoQuot K1)) (hna : ⁅vBeta K1 L2 S Zs, vBeta K1 L2 S Zs⁆ ≠ ⊥) :
    ∀ a ∈ pCoreOf 2 (K1 ⊔ S) ⊓ Subgroup.centralizer (vBeta K1 L2 S Zs : Set G),
    ∀ b ∈ pCoreOf 2 (K1 ⊔ S) ⊓ Subgroup.centralizer (vBeta K1 L2 S Zs : Set G), a * b = b * a := by
  classical
  have hcen := f112R1aCenter_of_rankOne hRO G K1 L2 S Zs hset hL24 hna
  let C5 := F112J2.fiveCtxOfSetting hRO hset hL24 hna
  let C : FamCtx K1 L2 S Zs (Fin 5) := famCtxOfFive C5
  have hZS' : ∀ u ∈ S, (∀ s ∈ S, u * s = s * u) → u * u = 1 → u ∈ Zs :=
    fun u hu hc h2 => hZS u hu h2 hc
  have hW32 : Nat.card ↥(vBeta K1 L2 S Zs) = 32 := (C5.isQ8D8_vBeta hcen).1
  have hodd : Odd (Fintype.card (Fin 5)) := ⟨2, by simp⟩
  have hker := hker_of_five hL24 C5
  have h3 : ∃ k : ↥K1, C.D.act k = c3 := by
    obtain ⟨k, hk⟩ := C5.D.surj ⟨c3, Equiv.Perm.mem_alternatingGroup.mpr c3_sign⟩
    exact ⟨k, by
      show ((C5.D.θ k : A5) : Equiv.Perm (Fin 5)) = c3
      rw [hk]⟩
  have hOk : pCoreOf 2 (K1 ⊔ S) ≤ C.kerM := pCore_le_kerM C (by simp) hodd
  have hkS : C.kerM ≤ S := kerM_le_S C hker
  intro a ha b hb
  exact kerMD_abelian C rfl hcen hZS' hker hW32 h3 a
    (Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨hOk ha.1, hkS (hOk ha.1)⟩, ha.2⟩) b
    (Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨hOk hb.1, hkS (hOk hb.1)⟩, hb.2⟩)

theorem n2Loc_holds (hRO : RankOneListedFacts.{0}) :
    ∀ (G : Type) [Group G] [Finite G] (K1 L2 S Zs : Subgroup G), R1SettingLegacyBare K1 L2 S Zs →
      (∀ u ∈ S, u * u = 1 → (∀ s ∈ S, u * s = s * u) → u ∈ Zs) →
      IsL2Quot 2 (OTwoQuot K1) → ⁅vBeta K1 L2 S Zs, vBeta K1 L2 S Zs⁆ ≠ ⊥ →
      pCoreOf 2 (K1 ⊔ S) = pCoreOf 2 K1 :=
  fun _ _ _ _ _ _ _ hset hZS hL24 hna =>
    n2_of_dAbel_inst hRO hset hZS hL24 hna (dAbel_of_ZS_inst hRO hset hZS hL24 hna)

end CFSG.Quasithin.Background.Harris.R1
