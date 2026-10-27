module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatHeCertificate

public import CFSG.Quasithin.Vol2.Ch12Sec5O2P
public import CFSG.Quasithin.Vol2.KGFactAutSylowM23
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.G3SporRows
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatHe
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatHS
import all CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatHS
import all CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatHe
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatRu
import all CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatRu

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin S125

namespace S125KG

variable {X : Type} [Group X] [Finite X]

theorem card_N_of_config63 {S N D : Subgroup X} (hS : QuasithinUnique.IsSylowTwoOf S ⊤)
    (hc : Config63 S N D) {a m : ℕ} (hm : ¬ 2 ∣ m) (hX : Nat.card X = 2 ^ a * m) :
    Nat.card N = 63 * 2 ^ a := by
  rw [hc.2.2.1, QuasithinUnique.A5.G3.card_eq_of_isSylowTwoOf hS hm hX]

theorem not_config63_of_index (hs : IsSimpleGroup X) {a : ℕ} (hX : Nat.card X = 2 ^ a * 315)
    {S N D : Subgroup X} (hS : QuasithinUnique.IsSylowTwoOf S ⊤) (hc : Config63 S N D) : False := by
  have hN := card_N_of_config63 hS hc (by norm_num) hX
  have hidx : N.index = 5 := by
    have h := Subgroup.card_mul_index N
    rw [hN, hX] at h
    have hpos : 0 < 2 ^ a := pow_pos (by norm_num) a
    have h2 : 2 ^ a * (63 * N.index) = 2 ^ a * 315 := by rw [← h]; ring
    have h3 := Nat.eq_of_mul_eq_mul_left hpos h2
    omega
  have hcore := Subgroup.index_normalCore_dvd_factorial_index N
  rw [hidx] at hcore
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N.normalCore with hb | ht
  · rw [hb, Subgroup.index_bot, hX] at hcore
    have h315 : 315 ∣ Nat.factorial 5 := (Dvd.intro_left _ rfl).trans hcore
    norm_num [Nat.factorial] at h315
  · have hNt : N = ⊤ := eq_top_iff.2 (ht.ge.trans (Subgroup.normalCore_le N))
    rw [hNt, Subgroup.index_top] at hidx
    omega

theorem not_config63_m23
    (e : X ≃* ↥NativeSporadic.M23) {S N D : Subgroup X}
    (hS : QuasithinUnique.IsSylowTwoOf S ⊤) (hc : Config63 S N D) : False := by
  have hX : Nat.card X = 2 ^ 7 * 79695 := by
    rw [Nat.card_congr e.toEquiv, CFSG.Sporadic.Schreier.m23_card]
    norm_num
  have hN := card_N_of_config63 hS hc (by norm_num) hX
  rcases KGSporLat.m23_overgroups ⟨e⟩ hS (hc.1.trans hc.2.1) with ht | ⟨m, hm, hord, -, -⟩
  · rw [ht, Subgroup.card_top, hX] at hN
    norm_num at hN
  · rw [hord] at hN
    simp only [KGSporLat.m23Mems, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl <;> norm_num at hN

theorem not_config63_hs
    (e : X ≃* NativeSporadic.HS) {S N D : Subgroup X}
    (hS : QuasithinUnique.IsSylowTwoOf S ⊤) (hc : Config63 S N D) : False := by
  have hX : Nat.card X = 2 ^ 9 * 86625 := by
    rw [Nat.card_congr e.toEquiv, CFSG.Sporadic.HS.card_HS]
    norm_num
  have hN := card_N_of_config63 hS hc (by norm_num) hX
  rcases QuasithinUnique.Ch1.SporLat.HS.hs_overgroups ⟨e⟩ hS (hc.1.trans hc.2.1) with
    ht | ⟨m, hm, hord, -, -⟩
  · rw [ht, Subgroup.card_top, hX] at hN
    norm_num at hN
  · rw [hord] at hN
    simp only [QuasithinUnique.Ch1.SporLat.HS.hsMems, List.mem_cons, List.not_mem_nil,
      or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl <;> norm_num at hN

theorem not_config63_he
    (e : X ≃* NativeSporadic.He) {S N D : Subgroup X}
    (hS : QuasithinUnique.IsSylowTwoOf S ⊤) (hc : Config63 S N D) : False := by
  have hX : Nat.card X = 2 ^ 10 * 3935925 := by
    rw [Nat.card_congr e.toEquiv, CFSG.Sporadic.He.card_He]
    norm_num
  have hN := card_N_of_config63 hS hc (by norm_num) hX
  rcases QuasithinUnique.Ch1.SporLat.He.he_overgroups ⟨e⟩ hS (hc.1.trans hc.2.1) with
    ht | ⟨m, hm, hord, -, -⟩
  · rw [ht, Subgroup.card_top, hX] at hN
    norm_num at hN
  · rw [hord] at hN
    simp only [QuasithinUnique.Ch1.SporLat.He.heMems, List.mem_cons, List.not_mem_nil,
      or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      norm_num at hN

theorem not_config63_ru
    (e : X ≃* NativeSporadic.Ru) {S N D : Subgroup X}
    (hS : QuasithinUnique.IsSylowTwoOf S ⊤) (hc : Config63 S N D) : False := by
  have hX : Nat.card X = 2 ^ 14 * 8906625 := by
    rw [Nat.card_congr e.toEquiv, CFSG.Sporadic.Ru.card_Ru]
    norm_num
  have hN := card_N_of_config63 hS hc (by norm_num) hX
  rcases QuasithinUnique.Ch1.SporLat.Ru.ru_overgroups ⟨e⟩ hS (hc.1.trans hc.2.1) with
    ht | ⟨m, hm, hord, -, -⟩
  · rw [ht, Subgroup.card_top, hX] at hN
    norm_num at hN
  · rw [hord] at hN
    simp only [QuasithinUnique.Ch1.SporLat.Ru.ruMems, List.mem_cons, List.not_mem_nil,
      or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl <;> norm_num at hN

end S125KG

namespace S125L3

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

theorem false_of_list3
    (hF : A318Facts) (h36 : A36ForSQTK) (h38 : A38ForSQTK) (h1222 : Stmt12_2_2)
    (F : Frame125 T L V) (hH : Hyp125 G T L V) {K₁ : Subgroup G}
    (hK : quasithinIsCComponent K₁ (Subgroup.normalizer (F.V1 : Set G)))
    (hK₁n : Subgroup.normalizer (F.V1 : Set G) ≤ Subgroup.normalizer (K₁ : Set G))
    (hLK : li L F.V1 ≤ K₁)
    (hl : Nonempty (↥K₁ ⧸ CFSG.pCore 2 ↥K₁ ≃* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) ∨
      Nonempty (↥K₁ ⧸ CFSG.pCore 2 ↥K₁ ≃* alternatingGroup (Fin 7)) ∨
      Nonempty (↥K₁ ⧸ CFSG.pCore 2 ↥K₁ ≃* NativeSporadic.M23) ∨
      Nonempty (↥K₁ ⧸ CFSG.pCore 2 ↥K₁ ≃* NativeSporadic.HS) ∨
      Nonempty (↥K₁ ⧸ CFSG.pCore 2 ↥K₁ ≃* NativeSporadic.He) ∨
      Nonempty (↥K₁ ⧸ CFSG.pCore 2 ↥K₁ ≃* NativeSporadic.Ru)) : False := by
  have hKG : K₁ ≤ Subgroup.normalizer (F.V1 : Set G) := le_of_mem_cComp hK
  have hPK := S125O2P.oTwoUpper_P_le_of_list3 hF h36 h38 h1222 F hH hK hl
  have hc := S125Cfg.config63 h1222 F hH hK₁n hKG hLK hPK
  have hS := S125Cfg.isSylow_img h1222 F hH hK₁n hKG
  rcases hl with h | h | h | h | h | h <;> obtain ⟨e⟩ := h
  · refine S125KG.not_config63_of_index (a := 6)
      (@MulEquiv.isSimpleGroup _ _ _ _ (isSimpleGroup_sl_zmod_two (m := 4) (by norm_num)).1 e)
      ?_ hS hc
    rw [Nat.card_congr e.toEquiv,
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (n := 4) (by norm_num),
      Nat.card_zmod]
    decide
  · refine S125KG.not_config63_of_index (a := 3)
      (@MulEquiv.isSimpleGroup _ _ _ _ (alternatingGroup.isSimpleGroup (by simp)) e) ?_ hS hc
    rw [Nat.card_congr e.toEquiv, card_alt_fin1515e 7 (by norm_num)]
    decide
  · exact S125KG.not_config63_m23 e hS hc
  · exact S125KG.not_config63_hs e hS hc
  · exact S125KG.not_config63_he e hS hc
  · exact S125KG.not_config63_ru e hS hc

end S125L3

end CFSG.Quasithin.H13
