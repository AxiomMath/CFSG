module

public import CFSG.Quasithin.H13.NQS13410P
public import CFSG.Quasithin.Vol2.Ch12Sec2Action

public section

namespace CFSG.Quasithin.H13.NQS134

open Subgroup Equiv CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.H13.A6 CFSG.Quasithin.InternalSec
open scoped IsMulCommutative commutatorElement

theorem b56Case1_of_commV {V : Type} [CommGroup V] [Finite V] {J K : Subgroup (MulAut V)}
    (hKJ : K ≤ J) (hn : ∀ x ∈ J, ∀ k ∈ K, x * k * x⁻¹ ∈ K) (hK : CFSG.IsQuasisimple ↥K)
    (hcomm : commV K = ⊤)
    (hcases : B56Case1 J ∨ B56Case2 J ∨ B56Case3 J ∨ B56Case4 J ∨ B56Case5 J) :
    B56Case1 J := by
  have htop : ∀ {X : Subgroup (MulAut V)}, K ≤ X → commV X = ⊤ := fun h =>
    top_le_iff.1 (by rw [← hcomm]; exact commV_le_commV h)
  rcases hcases with h1 | ⟨⟨e⟩, -⟩ |
      ⟨G₁, G₂, hsup, -, hc, -, -, W₁, W₂, -, -, -, -, -, hWinf, hp₁, hp₂⟩ |
      ⟨G₁, G₂, t, hJt, -, hc, -, hc₂, -, -, ⟨-, hV12⟩, -, hcV₂, ht₁, ht₂, -⟩ |
      ⟨_, _, -, -, -, -, -, -, hidx, -⟩
  · exact h1
  · exact (not_le_perm_three hK hKJ e).elim
  · exfalso
    rcases le_or_le_of_sup_eq hsup hc hKJ hn hK with h | h
    · have hW₁ : W₁ = ⊤ := top_le_iff.1 ((htop h).symm.le.trans (commV_le_of_b56Piece hp₁))
      rw [hW₁, top_inf_eq] at hWinf
      rw [hWinf] at hp₂
      exact not_b56Piece_self hp₂
    · have hW₂ : W₂ = ⊤ := top_le_iff.1 ((htop h).symm.le.trans (commV_le_of_b56Piece hp₂))
      rw [hW₂, inf_top_eq] at hWinf
      rw [hWinf] at hp₁
      exact not_b56Piece_self hp₁
  · exfalso
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    rcases le_or_le_of_sup_zpowers hJt hc ht₁ ht₂ hKJ hn hK with h | h
    · rw [htop h, top_inf_eq] at hV12
      rw [hV12, Subgroup.card_bot] at hcV₂
      norm_num at hcV₂
    · exact not_le_of_card_prime hK h hc₂
  · exfalso
    rw [htop hKJ, top_sup_eq, Subgroup.index_top] at hidx
    exact absurd hidx (by norm_num)

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

theorem conjClosure_eq_of_a6 (hC137 : U3.C137StatementFiveZ)
    (h1332 : Stmt13_3_2) (h1228 : Stmt12_2_8) (h56 : AsB56) (S : A6.Setting134 G T L V)
    (he : Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* alternatingGroup (Fin 6))) {H K U : Subgroup G}
    (hTH : T ≤ H) (hL1H : L₁Of L (fsuV1 T V) ≤ H) (hO2H : pCoreOf 2 H ≠ ⊥) (hKH : K ≤ H)
    (hHK : H ≤ normalizer (K : Set G)) (hKf : quasithinIsFaithfulLocal T K)
    (hKM : ¬ K ≤ normalizer (L : Set G)) (hL1K : L₁Of L (fsuV1 T V) ≤ K)
    (hJ : ⁅K, thompsonJ T⁆ = K)
    (hK : LieModel (↥K ⧸ CFSG.pCore 2 ↥K) .PSL 3 2 1 ∨
      Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 6)))
    [IsMulCommutative ↥U] (hKU : K ≤ normalizer (U : Set G)) (hTU : T ≤ normalizer (U : Set G))
    (hUK : ⁅U, K⁆ = U) (hU1 : U ≠ ⊥)
    (hUcl : U ≤ conjClosure (quasithinOmegaOneCenter T ⊓ U) K)
    (ho2Z : A6.o2Z K = K ⊓ centralizer (U : Set G))
    (hnat : LieModel (↥K ⧸ CFSG.pCore 2 ↥K) .PSL 3 2 1 →
      BinaryNaturalSL (V := ↥U) (autOn K U) ⊤ ⊥ 3 1)
    (hZ : quasithinOmegaOneCenter T ≤ U ⊔ U3.cZ T K) :
    conjClosure (quasithinOmegaOneCenter T ⊓ U) H = U := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Z₀ := quasithinOmegaOneCenter T ⊓ U with hZ₀
  set W := conjClosure Z₀ H with hWdef
  have hTsylH : IsSylowTwoOf T H := A5.isSylowTwoOf_of_le S.h13.sylow hTH
  have hchar : CharTwo H := U3.s134_charTwo_of_inH S ⟨hTH, hO2H⟩
  have hred : IsTwoReducedIn H W :=
    isTwoReducedIn_conjClosure_of_sylowIn hTH hTsylH.2.1 hTsylH.2.2 hchar inf_le_left
  have hWe : IsElemAbelian 2 W := hred.2.2.1
  have : IsMulCommutative ↥W := hWe.1
  have hW2 : ∀ w ∈ W, w ^ 2 = 1 := hWe.2
  have hHW : H ≤ normalizer (W : Set G) := hred.2.1
  have hKW : K ≤ normalizer (W : Set G) := hKH.trans hHW
  have hUW : U ≤ W := hUcl.trans (conjClosure_mono le_rfl hKH)
  have hWZ := (conjClosure_le_centerOf_pCoreOf_of_sylowIn hTH hTsylH.2.1 hTsylH.2.2 hchar
    (inf_le_left : Z₀ ≤ quasithinOmegaOneCenter T)).1
  have hWO : W ≤ pCoreOf 2 H := hWZ.trans inf_le_left
  have hOW : pCoreOf 2 H ≤ centralizer (W : Set G) := by
    intro x hx
    rw [mem_centralizer_iff]
    intro w hw
    exact (mem_centralizer_iff.mp (hWZ hw).2 x hx).symm
  have hHN : H ≤ normalizer ((⁅W, K⁆ : Subgroup G) : Set G) := by
    intro h hh
    rw [mem_normalizer_iff_map_conj_eq, Subgroup.map_commutator,
      mem_normalizer_iff_map_conj_eq.mp (hHW hh), mem_normalizer_iff_map_conj_eq.mp (hHK hh)]
  have hWK : ⁅W, K⁆ = W := by
    refine le_antisymm ?_ (conjClosure_le fun h hh z hz => ?_)
    · rw [commutator_le]
      intro w hw k hk
      have h1 : k * w⁻¹ * k⁻¹ ∈ W := (mem_normalizer_iff.mp (hKW hk) _).mp (inv_mem hw)
      have e : ⁅w, k⁆ = w * (k * w⁻¹ * k⁻¹) := by
        rw [commutatorElement_def]
        group
      rw [e]
      exact mul_mem hw h1
    · have hzU : z ∈ ⁅W, K⁆ := by
        have : z ∈ ⁅U, K⁆ := hUK.symm ▸ (inf_le_right : Z₀ ≤ U) hz
        exact commutator_mono hUW le_rfl this
      exact (mem_normalizer_iff.mp (hHN hh) z).mp hzU
  have hZK : center (↥K ⧸ CFSG.pCore 2 ↥K) = ⊥ := by
    rcases hK with h3 | h6
    · exact center_eq_bot_of_simple_types (Or.inr (Or.inl h3))
    · exact center_eq_bot_of_simple_types (Or.inr (Or.inr h6))
  have hOK : pCoreOf 2 K ≤ pCoreOf 2 H :=
    LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 ((LieType.BorelTits.pCoreOf_le 2 K).trans hKH)
      (hHK.trans (LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K))
      (LieType.BorelTits.pCoreOf_isPGroup 2 K)
  have hOKW : pCoreOf 2 K ≤ centralizer (W : Set G) := hOK.trans hOW
  have hCKW : K ⊓ centralizer (W : Set G) ≤ pCoreOf 2 K := fun k hk => by
    have h1 : k ∈ A6.o2Z K := by
      rw [ho2Z]
      exact mem_inf.2 ⟨(mem_inf.1 hk).1, centralizer_le hUW (mem_inf.1 hk).2⟩
    exact o2Z_le_pCoreOf_of_center hZK h1
  have hCK2 : IsPGroup 2 ↥(K ⊓ centralizer (W : Set G)) :=
    (LieType.BorelTits.pCoreOf_isPGroup 2 K).to_le hCKW
  have hKWnt : ¬ K ≤ centralizer (W : Set G) := by
    intro h
    apply hU1
    rw [← hUK, eq_bot_iff, commutator_le]
    intro u hu k hk
    have h1 := mem_centralizer_iff.mp (h hk) u (hUW hu)
    rw [commutatorElement_def, mem_bot, h1]
    group
  have hcardK : Nat.card ↥(autOn K W) = Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) := by
    rw [card_autOn_eq_relIndex hKW]
    have e : K ⊓ centralizer (W : Set G) = pCoreOf 2 K :=
      le_antisymm hCKW (le_inf (LieType.BorelTits.pCoreOf_le 2 K) hOKW)
    rw [e]
    have heq : (pCoreOf 2 K).subgroupOf K = CFSG.pCore 2 ↥K := by
      ext x
      rw [mem_subgroupOf]
      exact U3.coe_mem_pCoreOf_iff
    rw [relIndex, heq, index_eq_card]
  have hcard360 : Nat.card ↥(autOn K W) = 168 ∨ Nat.card ↥(autOn K W) = 360 := by
    rw [hcardK]
    rcases hK with h3 | h6
    · left
      exact card_of_statedClassicalModel_psl32 (statedClassicalModel_of_lieModel_psl32 h3)
    · right
      obtain ⟨e6⟩ := h6
      rw [Nat.card_congr e6.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
        Fintype.card_fin]
      decide
  have hO2Y : pCoreOf 2 (autOn H W) = ⊥ := Setup.pCoreOf_autOn_eq_bot hred
  have hO2K : pCoreOf 2 (autOn K W) = ⊥ := by
    have hn : ((autOn K W).subgroupOf (autOn H W)).Normal := by
      refine ⟨fun k hk x => ?_⟩
      rw [mem_subgroupOf] at hk ⊢
      exact autOn_normal_of hHK _ x.2 _ hk
    have := CFSG.RankThreeEvenClassification.Helpers.pCoreOf_le_pCoreOf_of_normal 2 _ _
      (autOn_le_autOn_of_le hKH) hn
    rw [hO2Y] at this
    exact le_bot_iff.1 this
  have hq : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K) := by
    obtain ⟨-, -, ⟨⟨V₀, hV₀⟩, hK3⟩, -⟩ := h1332 G T L S.h13 K hKf
    exact (hK3 V₀ hV₀).2.2.1.quasisimple
  have hqA : CFSG.IsQuasisimple ↥(autOn K W) := isQuasisimple_autOn hKW hq hO2K hKWnt
  have hSH : SQTKGroup ↥H :=
    sqtkGroup_of_pCoreOf_ne_bot S.h13.qtke S.h13.simple S.h13.nonabelian hO2H
  obtain ⟨A₀, -, hA, hKA⟩ := U3.exists_offender_of hTsylH hKH hHK hred hqA hKWnt hJ.symm
  obtain ⟨hKJ, hn, -, -, hcases⟩ := b56Cases_ffJ_autOn h56 hW2 hHW hKH hHK hSH hO2Y hA hKA
  have hcommV : commV (autOn K W) = ⊤ := commV_autOn_eq_top hKW hWK
  have h1 := b56Case1_of_commV hKJ hn hqA hcommV hcases
  have hF := eq_of_le_quasisimple hKJ hn hqA h1.1
  have hB51 := h1.2.1
  rw [hF] at hB51
  obtain ⟨-, hi | hii | hiii | hiv⟩ := hB51.1
  ·
    have h2 := U3.eq_of_irrPlus hKW hi.1 hUW hKU hUK hU1
    rw [hWK] at h2
    exact h2
  ·
    exfalso
    have hc6048 : Nat.card ↥(autOn K W) ≤ 360 := by rcases hcard360 with h | h <;> omega
    rcases hK with h3 | h6
    · have h168 : Nat.card ↥(autOn K W) ≤ 168 := by
        rw [hcardK]
        exact (card_of_statedClassicalModel_psl32 (statedClassicalModel_of_lieModel_psl32 h3)).le
      obtain ⟨I₀, I₁, hI₀W, hI₁W, hKI₀, hKI₁, hinf, hsup, ⟨hc₀, hnat₀⟩, φ₀, hφ₀⟩ :=
        exists_two_copies hKW hii h168
      rw [hWK] at hsup
      have hnatU := hnat h3
      obtain ⟨C⟩ := exists_l3Coords hnatU
      have hU8 : Nat.card ↥U = 8 := card_eq_eight_of_l32 hnatU
      have hI8 : Nat.card ↥I₀ = 8 := card_eq_eight_of_l32 hnat₀
      obtain ⟨I, hIW, hKI, hUI, hUIW, φ, hφ⟩ :=
        exists_compl_copy C hUW hI₀W hI₁W hKU hKI₀ hKI₁ hinf hsup φ₀ hφ₀ hU8 hI8
      have hRH : pCoreOf 2 H ≤ pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T) :=
        LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
          (EscapingLocal.pCoreOf_le_of_isSylowTwoOf hTsylH |>.trans le_sup_right)
          ((sup_le hL1H hTH).trans (LieType.BorelTits.le_normalizer_pCoreOf 2 H))
          (LieType.BorelTits.pCoreOf_isPGroup 2 H)
      have hWR : U ⊔ I ≤ pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T) := by
        rw [hUIW]
        exact hWO.trans hRH
      have hUZ : A6.o2Z K = K ⊓ centralizer (U : Set G) := ho2Z
      exact not_two_copies_of_a6 hC137 h1332 h1228 S he hKf hKM hL1K h3 hnatU hKU hTU hUZ hUI
        (hUIW ▸ hWe) hKI φ hφ (hUIW ▸ (hTH.trans hHW)) hWR hZ
    ·
      obtain ⟨-, n', F, _, _, hF', I', π, -, -, hreal, -, -⟩ := hii
      have hinj := B5.realizesVia_injective (FFModel.nat_faithful _) (hreal 0)
      have hcard := Nat.card_congr (Equiv.ofBijective π ⟨hinj, (hreal 0).1⟩)
      rw [← Nat.card_congr (Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 F).toEquiv,
        Vol2.Ch11.SecC.B51.card_SL3_eq_pow hF'] at hcard
      have h360 : Nat.card ↥(autOn K W) = 360 := by
        rw [hcardK]
        obtain ⟨e6⟩ := h6
        rw [Nat.card_congr e6.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
          Fintype.card_fin]
        decide
      rw [h360] at hcard
      have h1 := Vol2.Ch11.SecC.B51.one_le_of_card_eq hF'
      rcases Nat.lt_or_ge n' 2 with hn2 | hn2
      · interval_cases n'
        norm_num at hcard
      · have h64 : 64 ≤ 2 ^ (3 * n') :=
          (show (64 : ℕ) = 2 ^ 6 by norm_num) ▸ Nat.pow_le_pow_right (by norm_num) (by omega)
        have h16 : 16 ≤ 2 ^ (2 * n') :=
          (show (16 : ℕ) = 2 ^ 4 by norm_num) ▸ Nat.pow_le_pow_right (by norm_num) (by omega)
        have h3 : 63 * 15 ≤ (2 ^ (3 * n') - 1) * (2 ^ (2 * n') - 1) :=
          Nat.mul_le_mul (by omega) (by omega)
        have h4 : 64 * (63 * 15) ≤ 2 ^ (3 * n') * ((2 ^ (3 * n') - 1) * (2 ^ (2 * n') - 1)) :=
          Nat.mul_le_mul h64 h3
        omega
  · exfalso
    exact (U3.not_case1iii_iv (by rcases hcard360 with h | h <;> omega)).1 hiii
  · exfalso
    exact (U3.not_case1iii_iv (by rcases hcard360 with h | h <;> omega)).2 hiv

end CFSG.Quasithin.H13.NQS134
