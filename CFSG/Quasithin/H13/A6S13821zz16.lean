module

public import CFSG.Quasithin.H13.A6S13821zz15
public import CFSG.Quasithin.H13.A6S13821za
public import CFSG.Quasithin.H13.A6S13821zz
public import CFSG.Quasithin.H13.A6S13821zz10

public section

namespace CFSG.Quasithin.H13.A6

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits

attribute [local instance] commGroupOfFact

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

theorem false_of_l3_13820a
    (h36c : QuasithinUnique.Vol2Native.A36CoreForSQTKCat) (h37 : A37ForSQTK)
    (h38 : A38ForSQTK) (h139 : Stmt13_3_9) (h1334 : Stmt13_3_4) (h13 : Lem13813)
    (hD310 : D310) (hD391 : D391) (hI4 : Insp4) (hA21 : AsA21SQTKSection) (h42 : AsB42)
    (hB51 : AsB51) {H K : Subgroup G} {n : ℕ} (hC : S.Ctx13820 H K n)
    (ha : S.Case13820aHyp H K) (hnodd : Odd n)
    (hL3 : IsPSL 3 2 n (↥(S.KSt H K) ⧸ Subgroup.center ↥(S.KSt H K))) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hF, I, hV₁I, hIU, hirrT, hTI, m, hm, hnat, hq⟩ :=
    S.exists_ff_sl3_13820a h36c h37 h38 h139 h1334 h13 hD310 hD391 hI4 hA21 h42 hC ha hnodd hL3
  obtain ⟨hperf, hs, hcardQ⟩ := S.k_data_l3 hC hnodd hL3
  obtain ⟨hS, hH, hK, hKn, -, hn, hLie⟩ := hC
  obtain ⟨-, hXc, hHX, t, htH, htK, htX⟩ := ha
  obtain ⟨e₁⟩ := S.kst_equiv hS hH hK
  have hLieQ : LieF2n (↥K ⧸ CFSG.pCore 2 ↥K) n := lieF2n_congr e₁.symm hLie
  have hTH : T ≤ H := le_sup_right.trans hH.1.1
  have hKH : K ≤ H := le_of_mem_cComp hK
  have hK₀ : conjClosure K T = K :=
    le_antisymm (conjClosure_le fun t ht k hk =>
      (Subgroup.mem_normalizer_iff.mp (hKn (hTH ht)) k).mp hk) (le_conjClosure K T)
  have := factElem hF hIU
  have hSQ := S.sqtkGroup_of_mem_Hz hH
  have hirr := isIrrPlusTilde_of_module hF hV₁I hIU hirrT
  obtain ⟨c, hcX, hc3, hθ, hfpf, htri, hdich⟩ := S.exists_c_13820a' hS hH hHX
  have P := S.plusData_X13820
  have hL1H : S.L1 ≤ H := le_sup_left.trans hH.1.1
  have hcH : c ∈ H := hL1H (P.le_L1 hcX)
  have hXO : pCoreOf 2 S.X13820 ≤ pCoreOf 2 H := by
    have hchar : (CFSG.Open.pCore 2 ↥S.X13820).Characteristic := by
      infer_instance
    have hHO : H ≤ Subgroup.normalizer ((pCoreOf 2 S.X13820 : Subgroup G) : Set G) :=
      hHX.trans (normalizer_le_normalizer_map_of_characteristic (CFSG.Open.pCore 2 ↥S.X13820))
    exact le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 _).trans (P.le_L1.trans hL1H)) hHO
      (pCoreOf_isPGroup 2 _)
  obtain ⟨s₀, hs₀H, hs₀2, hs₀c, hs₀K⟩ := A6S20.exists_two_part (le_normalizer_pCoreOf 2 H)
    hKH htH hcH (hXO (htX c hcX)) htK
  have hTsyl : IsSylowTwoOf T H := hF.toHypF98.toHypF91.sylow_H
  obtain ⟨s, hsT, ⟨e₂, hs2⟩, hsc, hsK⟩ := A6S20.exists_two_part_mem (le_normalizer_pCoreOf 2 H)
    hKn hTsyl hcH hdich hs₀H hs₀2 hs₀c hs₀K
  have hcK : ∀ k ∈ K, c * k * c⁻¹ * k⁻¹ ∈ pCoreOf 2 H := hXc c hcX
  have hII := A6S20.inf_conj_le_centralizerMod hF hK₀ hV₁I hIU hirrT hTI hcH hc3 hθ hcK hsT
    hsK hsc hs2
  have hKI : K ≤ Subgroup.normalizer (I : Set G) := (le_conjClosure K T).trans hirr.1
  have hJN := (A6S20.sup_conj_le_normalizer hV₁I hIU hθ (F7.isSylowTwoOf_pCoreOf_le hTsyl) hTI
    hKI (le_normalizer_pCoreOf 2 H hcH) (hKn hcH)
    (fun t ht => (Subgroup.mem_normalizer_iff.mp (hHX (hTH ht)) c).mp hcX) htri).1
  have hRc : ∀ b ∈ pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T), c * b * c⁻¹ * b⁻¹ ∈ pCoreOf 2 H :=
    fun b hb => S.comm_c_of_mem_R hS hH hcX hc3 hfpf hdich hb
  have hn3 : 3 ≤ n := by
    obtain ⟨k, rfl⟩ := hnodd
    omega
  have hoddZ : Odd (Nat.card (Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K))) :=
    E1.ThinA5.odd_card_center_quot_pCore
  have hsyl := S.isSylowTwoOf_TK hH hKH hKn
  have hFU : Fact (IsElemAbelian 2 (tildeOf (fsuV1 T V) (conjClosure S.V3 H))) :=
    factElem hF (le_conjClosure S.V3 H)
  have hfix1 := A6S20.fixProp_sup_sl3 hF hK₀ hV₁I hIU hirr hperf hs hnat hm hcH hcK hII hsyl
  have hfix2 := A6S20.fixProp_layer2_sl3 hA21 hB51 hSQ hF hK₀ hV₁I hIU hirrT hTI hq hcH hII hJN
    hRc hperf hs hn3 hcardQ hoddZ hsyl
  have hW2 : ∀ w : ↥(tildeOf (fsuV1 T V) (conjClosure S.V3 H)), w ^ 2 = 1 := fun w => by
    apply Subtype.ext
    exact hFU.out.2 (w : SecQuot (Subgroup.normalizer ((fsuV1 T V : Subgroup G) : Set G))
      (fsuV1 T V)) w.2
  have hodd := A6S20.odd_index_of_sylow hsyl (le_inf hsyl.1 Subgroup.le_normalizer)
  have hbot : S1565.InvSub ((actH hF.H_le_normalizer_V₁ (le_normalizer_conjClosure S.V3 H)).comp
      (Subgroup.inclusion hKH)) (⊥ : Subgroup ↥(tildeOf (fsuV1 T V) (conjClosure S.V3 H))) :=
    fun x a ha => by
      rw [Subgroup.mem_bot] at ha ⊢
      rw [ha, map_one]
  have hfix := S1565.fixProp_compose _ hW2 _ hodd hbot bot_le hfix1 hfix2
  have hcV := S.not_mem_centralizer_of_fpf hS hH hfpf
  have hBM := S.borel_le_M h13 h1334 hS hH hKH hKn hn hLieQ
  exact A6S20.false_of_fixProp hF hK₀ hIU hirr (fun b hb =>
    S.borel_comm_V3_13820a hS hH hKH hKn hBM hcX hc3 hcV hfpf hcK htri hsT hsc hsK hb) hfix

end Setting4

end CFSG.Quasithin.H13.A6
