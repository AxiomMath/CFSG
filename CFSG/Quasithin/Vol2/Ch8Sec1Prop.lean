module

public import CFSG.Quasithin.Vol2.Ch8Sec1Hyp
public import CFSG.Quasithin.Vol2.Ch8Sec1
public import CFSG.Quasithin.Vol2.Ch8InputsB
public import CFSG.Quasithin.Vol2.Ch3Sec1Thm311
public import CFSG.Quasithin.Background.InternalSecTwo

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.H.Mathieu CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem normalizer_le_of_characteristic {Q C : Subgroup G} (hCQ : C ≤ Q)
    (hchar : (C.subgroupOf Q).Characteristic) :
    Subgroup.normalizer (Q : Set G) ≤ Subgroup.normalizer (C : Set G) := by
  have h := CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic (C.subgroupOf Q)
  rwa [Subgroup.map_subgroupOf_eq_of_le hCQ] at h

theorem normalizer_le_of_isUniqueM {Q C M : Subgroup G} (hQ : IsPGroup 2 Q)
    (huniq : IsUniqueM (Subgroup.normalizer (Q : Set G)) M) (hCQ : C ≤ Q) (hC : C ≠ ⊥)
    (hchar : (C.subgroupOf Q).Characteristic) : Subgroup.normalizer (C : Set G) ≤ M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hCO : C ≤ pCoreOf 2 (Subgroup.normalizer (C : Set G)) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 Subgroup.le_normalizer le_rfl
      (hQ.to_le hCQ)
  have hO : pCoreOf 2 (Subgroup.normalizer (C : Set G)) ≠ ⊥ := fun h =>
    hC (le_bot_iff.1 (h ▸ hCO))
  obtain ⟨M', hM'⟩ := exists_inM_of_pCoreOf_ne_bot hO
  have : M' = M :=
    huniq.2 M' ⟨hM'.1, (normalizer_le_of_characteristic hCQ hchar).trans hM'.2⟩
  rw [← this]
  exact hM'.2

theorem setting811_of (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (hmod : StmtFSUModule) (h711 : Stmt7_1_1_normal) (h325 : Stmt3_2_5) (hQ : Input8_3_Q)
    (huniq : Input7_0_2_unique) {T L I : Subgroup G} (hyp : Hyp7_0_2 G T L I)
    [IsMulCommutative ↥(fsuV T I)] (hrow : CocodeRow T L I) (hV : IsElemAbelian 2 (fsuV T I))
    (hcard : Nat.card ↥(fsuV T I) = 2 ^ 10 ∨ Nat.card ↥(fsuV T I) = 2 ^ 11) :
    Setting811 T L (fsuV T I) (fsuM T L) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hfsu := hyp.fsu
  have : IsSimpleGroup G := hfsu.simple
  obtain ⟨-, hN⟩ := hmod G T L I hfsu
  have hTL := le_normalizer_of_cocodeRow h711 hyp hrow
  have hL0 : fsuL0 T L = L := fsuL0_eq_of_le_normalizer hTL
  have hM : fsuM T L = Subgroup.normalizer (L : Set G) := by
    change Subgroup.normalizer (fsuL0 T L : Set G) = _
    rw [hL0]
  have hNM := normalizer_fsuV_le_fsuM h37 h38 h39 hfsu hV hN
  have hu := huniq G T L I hyp
  have hTsyl : IsSylowTwoOf T ⊤ := by
    refine ⟨le_top, hfsu.sylow.1, ?_⟩
    have h := hfsu.sylow.2
    rwa [← Subgroup.relIndex_top_right] at h
  have hTM : T ≤ fsuM T L := by rw [hM]; exact hTL
  have hMloc : pCoreOf 2 (fsuM T L) ≠ ⊥ := by
    obtain ⟨P, hP1, hP2, hPM⟩ := hu.1.1.1
    intro h
    apply hP1
    have hPO : P ≤ pCoreOf 2 (fsuM T L) := by
      rw [hPM]
      exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 Subgroup.le_normalizer le_rfl hP2
    exact le_bot_iff.1 (h ▸ hPO)
  have hQeq := hQ G T L I hyp
  rw [hL0] at hN hQeq
  exact
    { sylow := hTsyl
      elem := hV
      V_le_T := fsuV_le_T hfsu hV (by rw [hL0]; exact hN)
      LT_le_normalizer := hN
      normalizer_le := hNM
      LT_le := by rw [hM]; exact sup_le Subgroup.le_normalizer hTL
      le_normalizer_L := hM.le
      ti := isTISetUnder_of_cocodeRow h711 h325 hyp hrow
      q_eq := hQeq
      normalizer_char_le := fun C hC hC1 hchar =>
        normalizer_le_of_isUniqueM (hTsyl.2.1.to_le inf_le_left) hu hC hC1 hchar
      quasisimple := hfsu.quasisimple
      charTwo := charTwo_of_inH' hfsu.qtke hfsu.sylow ⟨hTM, hMloc⟩
      localSQTK := fun P hP => InternalSec.sqtkGroup_of_localSQTK
        (qtkeCore_of_cat hfsu.nonabelian hfsu.qtke).1 hP
      card := hcard }

theorem ne_one_of_isCocodeO2
    {V : Type*} [CommGroup V] {L : Subgroup (MulAut V)}
    (h : MathieuCocode22 L ⊤ ⊥ ∨ MathieuCocode23 L ⊤ ⊥ ∨ MathieuCocode24 L ⊤ ⊥) {v : V}
    (hv : IsCocodeO2 L v) : v ≠ 1 := by
  rintro rfl
  rcases h with h | h | h
  · obtain ⟨e, -, he⟩ := cocode22_o2_std h hv
    rw [map_one] at he
    exact absurd (toW_inj (by norm_num) (by norm_num) (he.symm.trans (toW_zero 10).symm))
      (by norm_num)
  · obtain ⟨e, -, he⟩ := cocode23_o2_std h hv
    rw [map_one] at he
    exact absurd (toW_inj (by norm_num) (by norm_num) (he.symm.trans (toW_zero 11).symm))
      (by norm_num)
  · obtain ⟨e, -, he⟩ := cocode24_o2_std h hv
    rw [map_one] at he
    exact absurd (toW_inj (by norm_num) (by norm_num) (he.symm.trans (toW_zero 11).symm))
      (by norm_num)

theorem stmt8_1_1_of
    (hC48 : ∀ (G : Type) [Group G] [Finite G], ASC48Statement G)
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK) (hmod : StmtFSUModule)
    (h711 : Stmt7_1_1_normal) (h325 : Stmt3_2_5) (hQ : Input8_3_Q)
    (huniq : Input7_0_2_unique) : Stmt8_1_1 := by
  intro G _ _ T L I hyp _ _ hrow hV x hx
  have hTL := le_normalizer_of_cocodeRow h711 hyp hrow
  have hL0 : fsuL0 T L = L := fsuL0_eq_of_le_normalizer hTL
  have hrow' : MathieuCocode22 (autI hV (fsuL0 T L)) ⊤ ⊥ ∨
      MathieuCocode23 (autI hV (fsuL0 T L)) ⊤ ⊥ ∨ MathieuCocode24 (autI hV (fsuL0 T L)) ⊤ ⊥ :=
    hrow
  have hx1 := ne_one_of_isCocodeO2 hrow' hx
  obtain ⟨N, hN, hd, hcard⟩ : ∃ N : ℕ, (N = 20160 ∨ N = 443520) ∧
      O2Data (autI hV (fsuL0 T L)) x N ∧
      (Nat.card ↥(fsuV T I) = 2 ^ 10 ∨ Nat.card ↥(fsuV T I) = 2 ^ 11) := by
    rcases hrow' with h | h | h
    · exact ⟨20160, Or.inl rfl, o2Data_of_cocode22 h hx,
        Or.inl (card_of_cocode22 (V := IntMod (fsuV T I) hV) h)⟩
    · exact ⟨443520, Or.inr rfl, o2Data_of_cocode23 h hx,
        Or.inr (card_of_cocode23 (V := IntMod (fsuV T I) hV) h).1⟩
    · exact ⟨443520, Or.inr rfl, o2Data_of_cocode24 h hx,
        Or.inr (card_of_cocode24 (V := IntMod (fsuV T I) hV) h).1⟩
  have S := setting811_of h37 h38 h39 hmod h711 h325 hQ huniq hyp hrow hV hcard
  rw [hL0] at hd
  exact S.centralizer_le (hC48 G) hN hd hx1

end CFSG.Quasithin.H13
