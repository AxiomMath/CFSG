module

public import CFSG.Quasithin.H13.A6S1516d

public section

namespace CFSG.Quasithin.H13.A6

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits

variable {G : Type} [Group G]

theorem exists_surjective_quot_of_alt6 {K : Subgroup G}
    (φ : ↥K →* ↥(alternatingGroup (Fin 6))) (hφ : Function.Surjective φ) :
    ∃ φ₁ : (↥K ⧸ CFSG.pCore 2 ↥K) →* ↥(alternatingGroup (Fin 6)), Function.Surjective φ₁ := by
  classical
  have hO2 : CFSG.pCore 2 ↥K ≤ φ.ker := by
    have hP : IsPGroup 2 ((CFSG.pCore 2 ↥K).map φ) := CFSG.pCore_isPGroup.map φ
    have hsimp : IsSimpleGroup ↥(alternatingGroup (Fin 6)) :=
      alternatingGroup.isSimpleGroup (by simp)
    have hN : ((CFSG.pCore 2 ↥K).map φ).Normal := Subgroup.Normal.map CFSG.pCore_normal φ hφ
    rcases hsimp.eq_bot_or_eq_top_of_normal ((CFSG.pCore 2 ↥K).map φ) with h | h
    · rw [Subgroup.map_eq_bot_iff] at h
      exact h
    · exfalso
      rw [h] at hP
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hP
      rw [Subgroup.card_top, card_alt6] at hk
      have h3 : 3 ∣ 2 ^ k := hk ▸ (by norm_num : (3 : ℕ) ∣ 360)
      exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3) (by norm_num)
  refine ⟨QuotientGroup.lift (CFSG.pCore 2 ↥K) φ hO2, fun y => ?_⟩
  obtain ⟨x, rfl⟩ := hφ y
  exact ⟨(x : ↥K ⧸ CFSG.pCore 2 ↥K), rfl⟩

theorem a6CentralQuotient_of_isA6On (h1332 : Stmt13_3_2) (h13316 : Stmt13_3_16) [Finite G]
    {T L V : Subgroup G} (hH : QTH13 G T L) (hV : IsIrrPlusIn L (reducedAggregate (L ⊔ T)) T V)
    (hA6V : IsA6On L V) : A6CentralQuotient L := by
  obtain ⟨hfive, -, -, -⟩ := h1332 G T L hH L hH.faithful
  have hLN : L ≤ Subgroup.normalizer (V : Set G) := hV.2.2.1
  obtain ⟨e⟩ := hA6V
  obtain ⟨φ, hφ⟩ := exists_surjective_autOn hLN
  obtain ⟨φ₁, hφ₁⟩ := exists_surjective_quot_of_alt6 (e.toMonoidHom.comp φ) (e.surjective.comp hφ)
  have hle := Nat.card_le_card_of_surjective φ₁ hφ₁
  rw [card_alt6] at hle
  rcases hfive with hf | h32 | hf | hhat | hu
  · obtain ⟨f⟩ := hf
    rw [Nat.card_congr f.toEquiv, card_alt5] at hle
    omega
  · rw [card_of_statedClassicalModel_psl32 (statedClassicalModel_of_lieModel_psl32 h32)] at hle
    omega
  · obtain ⟨f⟩ := hf
    have hZ : Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) = ⊥ := by
      rw [eq_bot_iff]
      intro z hz
      have h1 : f z ∈ Subgroup.center ↥(alternatingGroup (Fin 6)) :=
        map_center_le_center f.toMonoidHom f.surjective ⟨z, hz, rfl⟩
      rw [alternatingGroup.center_eq_bot (by simp), Subgroup.mem_bot] at h1
      rw [Subgroup.mem_bot]
      exact f.injective (h1.trans (map_one f).symm)
    exact ⟨(QuotientGroup.quotientMulEquivOfEq hZ).trans (QuotientGroup.quotientBot.trans f)⟩
  · exact hhat.2.2
  · exact (h13316 G T L hH hu).elim

namespace Setting4

variable [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

theorem G1_mem_Hz_of (h : ¬ S.G1 ≤ Subgroup.normalizer (L : Set G)) : S.G1 ∈ S.Hz := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨⟨?_, fun h0 => ?_⟩, le_rfl, h⟩
  · show S.L1 ⊔ T ≤ Subgroup.centralizer ({S.z} : Set G)
    rw [← S.normalizer_V1]
    exact S.L1T_le_NV1
  · have hV1G : fsuV1 T V ≤ S.G1 := fun x hx => by
      rcases S.mem_V1_iff.1 hx with rfl | rfl
      · exact S.G1.one_mem
      · exact Subgroup.mem_centralizer_singleton_iff.2 rfl
    have hV1 : fsuV1 T V ≤ pCoreOf 2 S.G1 :=
      le_pCoreOf_of_le_normalizer 2 hV1G
        (S.G1_le_centralizer_V1.trans (Subgroup.centralizer_le_normalizer _))
        (IsPGroup.of_card (n := 1) (by rw [S.card_V1]; norm_num))
    rw [h0, le_bot_iff] at hV1
    have := S.card_V1
    rw [hV1] at this
    simp at this

theorem conjClosure_V1_L : conjClosure (fsuV1 T V) L = V := by
  have hV1V : fsuV1 T V ≤ V := (S.V1_le_V2.trans S.V2_le_V3).trans S.V3_le_V
  have hle : conjClosure (fsuV1 T V) L ≤ V :=
    conjClosure_le fun l hl v hv =>
      (Subgroup.mem_normalizer_iff.mp (S.frame.L_le hl) v).mp (hV1V hv)
  rcases S.irr.2.2.2.2.2.1 (conjClosure (fsuV1 T V) L) (by rw [S.zv]; exact bot_le) hle
      (le_normalizer_conjClosure _ _) with h | h
  · exfalso
    rw [S.zv] at h
    apply S.z_ne_one
    have : S.z ∈ conjClosure (fsuV1 T V) L := le_conjClosure _ _ (S.mem_V1_iff.2 (Or.inr rfl))
    rw [h] at this
    exact (Subgroup.mem_bot).1 this
  · exact h

theorem conj_mem_V_of_le_M (hle : S.G1 ≤ Subgroup.normalizer (L : Set G)) {g : G}
    (hg : g ∈ S.G1) {v : G} (hv : v ∈ V) : g * v * g⁻¹ ∈ V := by
  have hgV1 : g ∈ Subgroup.normalizer (fsuV1 T V : Set G) := by
    rw [S.normalizer_V1]
    exact hg
  have hgL : g ∈ Subgroup.normalizer (L : Set G) := hle hg
  have hc : conjClosure (fsuV1 T V) L ≤
      (conjClosure (fsuV1 T V) L).comap (MulAut.conj g).toMonoidHom := by
    refine conjClosure_le fun l hl w hw => ?_
    show g * (l * w * l⁻¹) * g⁻¹ ∈ conjClosure (fsuV1 T V) L
    have e : g * (l * w * l⁻¹) * g⁻¹ = (g * l * g⁻¹) * (g * w * g⁻¹) * (g * l * g⁻¹)⁻¹ := by
      group
    rw [e]
    exact mem_conjClosure ((Subgroup.mem_normalizer_iff.mp hgL l).mp hl)
      ((Subgroup.mem_normalizer_iff.mp hgV1 w).mp hw)
  have key : ∀ x ∈ conjClosure (fsuV1 T V) L, g * x * g⁻¹ ∈ conjClosure (fsuV1 T V) L :=
    fun x hx => hc hx
  have := key v (S.conjClosure_V1_L.symm ▸ hv)
  rwa [S.conjClosure_V1_L] at this

theorem G1_not_le_M (hna : ¬ IsElemAbelian 2 (conjClosure S.V3 S.G1)) :
    ¬ S.G1 ≤ Subgroup.normalizer (L : Set G) := fun hle => hna
  (F7.isElemAbelian_mono S.elemAbelian_V
    (conjClosure_le fun _ hg _ hv => S.conj_mem_V_of_le_M hle hg (S.V3_le_V hv)))

theorem G1_mem_Hz_of_nonabelian (hna : ¬ IsElemAbelian 2 (conjClosure S.V3 S.G1)) :
    S.G1 ∈ S.Hz :=
  S.G1_mem_Hz_of (S.G1_not_le_M hna)

end Setting4

@[expose] def Input13518Six : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (S : Setting4 G T L V),
    ¬ LieModel G .PSp 3 2 1 → ¬ IsHatA6 L → ¬ IsElemAbelian 2 (conjClosure S.V3 S.G1) →
    ∃ H ∈ S.Hz, ¬ IsElemAbelian 2 (conjClosure S.V3 H) ∧ H ≤ Subgroup.normalizer (S.L1 : Set G)

@[expose] def Input13521Four : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (S : Setting4 G T L V),
    ¬ LieModel G .PSp 3 2 1 → ¬ IsElemAbelian 2 (conjClosure S.V3 S.G1) → ¬ IsHatA6 L

theorem stmt13_5_12_six_of_inputs
    (h1332 : Stmt13_3_2) (h13316 : Stmt13_3_16)
    (h1341 : Stmt13_4_1) (h13315 : Stmt13_3_15) (h1356two : Input1356Two)
    (hobl : Obl13_5_14Six) (hctk : Input13515CTK) (hU43 : StmtU43Type)
    (h13521 : Input13521Four) (h13518 : Input13518Six) : Stmt13_5_12_six := by
  intro G _ _ T L V hH hV hA6V hNS hna
  have hZV : V ⊓ Subgroup.centralizer (L : Set G) = ⊥ := by
    by_contra h
    exact hNS (h1341 G T L V hH hV h)
  obtain ⟨S⟩ := exists_setting4 h1332 h13316 hH
    (a6CentralQuotient_of_isA6On h1332 h13316 hH hV hA6V) hV hZV
  have hg1 : g1 T V = S.G1 := S.normalizer_V1
  rw [S.v3_eq, hg1] at hna
  have hna' : ¬ IsElemAbelian 2 (conjClosure S.V3 S.G1) := fun h => hna h.1
  have hhat := h13521 G T L V S hNS hna'
  obtain ⟨H, hH', hnaH, hn⟩ := h13518 G T L V S hNS hhat hna'
  exact S.psu43 hNS h13315 h1356two hH' hhat hn hnaH hobl hctk hU43

end CFSG.Quasithin.H13.A6
