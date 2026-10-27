module

public import CFSG.Quasithin.Vol2.Ch9Sec3L24
public import CFSG.Quasithin.Vol2.Ch9Sec4End
public import CFSG.Quasithin.Vol2.Ch9Sec3L34Branch
public import CFSG.Quasithin.Vol2.Ch9Sec3L34Par
public import CFSG.Quasithin.Vol2.Ch9Sec3L34Res
public import CFSG.Quasithin.Vol2.Ch9Lem9310
public import CFSG.Quasithin.Vol2.Ch9Lem938
public import CFSG.Quasithin.H13.F112DSL2Slices
public import CFSG.Quasithin.Recognition.GoldschmidtF112RQ
public import CFSG.Quasithin.Background.F1VertexCore
public import CFSG.Quasithin.Vol2.Ch9Lem937
public import CFSG.Quasithin.Vol2.Ch9Sec3FactsF112
public import CFSG.Quasithin.Vol2.Ch9Sec3K1

public section

namespace CFSG.Quasithin.H13.Ch9

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H Matrix

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ}

namespace Setup

variable (S : Setup T L I n)
include S

theorem lem933'_slices (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (h37c : Vol2Native.A37ForSQTKCat) (h38c : Vol2Native.A38ForSQTKCat) (hDSA : DSAL2Statement)
    (hFI : F112FourLinkFactC) (h2 : n = 2) {K D : Subgroup G}
    (hD : Lin2.IsHallTwoPrimeOf D
      (fsuL0 T L ⊓ Subgroup.normalizer ((T ⊓ fsuL0 T L : Subgroup G) : Set G)))
    (hT₁K : T ⊓ Subgroup.normalizer (L : Set G) ≤ Subgroup.normalizer (K : Set G))
    (hDK : D ≤ Subgroup.normalizer (K : Set G))
    (hKV : K ≤ Subgroup.centralizer ((fsuV T I ⊓ Subgroup.centralizer
      ((T ⊓ fsuL0 T L : Subgroup G) : Set G) : Subgroup G) : Set G))
    (hTKs : IsSylowTwoOf (T ⊓ K) K)
    (hKA : Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 5)))
    (hKns : ¬ Group.IsSolvable ↥K)
    (hTKR : T ⊓ K ≤ (T ⊓ fsuL0 T L) ⊔ (T ⊓ Subgroup.centralizer (fsuV T I : Set G)))
    (hbor : K ⊓ Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G) ≤
      fsuM T L ⊓ Subgroup.normalizer (L : Set G))
    (hbL : L ⊓ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G) ≤
      Subgroup.normalizer (K : Set G)) :
    pCoreOf 2 (L ⊔ D ⊔ (T ⊓ Subgroup.normalizer (L : Set G)) ⊔ K) ≠ ⊥ := by
  intro hM₀
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hfsu := S.hyp.fsu
  obtain ⟨F, _, _, _, e, ψ, hc, hdiag⟩ := S.exists_isCoord_diag h37c h38c hD
  set V₁ := fsuV T I ⊓ Subgroup.centralizer ((T ⊓ fsuL0 T L : Subgroup G) : Set G) with hV₁
  set Q := T ⊓ Subgroup.centralizer (fsuV T I : Set G) with hQ
  set R₀ := (T ⊓ fsuL0 T L) ⊔ Q with hR₀
  set M := fsuM T L with hM
  have hTM : T ≤ M := Setup.T_le_fsuM
  have hDL0 : D ≤ fsuL0 T L := hD.1.trans inf_le_left
  have hDL : D ≤ Subgroup.normalizer (L : Set G) :=
    hDL0.trans (hc.L0_le_normalizer_L h37 h38 h37c h38c)
  have hDR₀ : D ≤ Subgroup.normalizer (R₀ : Set G) := hD.1.trans S.N0_le_normalizer_r0
  have hTR₀ : T ≤ Subgroup.normalizer (R₀ : Set G) := S.T_le_normalizer_r0
  have hQN : fsuL0 T L ⊔ T ≤ Subgroup.normalizer (Q : Set G) := S.L0T_le_normalizer_Q
  have hR₀T : R₀ ≤ T := r0_le_T
  have hR₀2 : IsPGroup 2 R₀ := S.isPGroup_r0
  have hR₀L : R₀ ≤ Subgroup.normalizer (L : Set G) := hc.r0_le_normalizer_L h37 h38 h37c h38c
  have hRK : R₀ ⊓ K = T ⊓ K :=
    le_antisymm (inf_le_inf_right K hR₀T) (le_inf hTKR inf_le_right)
  have hTLR : T ⊓ L ≤ R₀ := fun x hx => Subgroup.mem_sup_left ⟨hx.1, S.L_le_L0 hx.2⟩
  have hRL : R₀ ⊓ L = T ⊓ L :=
    le_antisymm (inf_le_inf_right L hR₀T) (le_inf hTLR inf_le_right)
  have hborLeq : borelOf L R₀ = L ⊓ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G) := by
    unfold borelOf
    rw [hRL]
  have hborKeq : borelOf K R₀ = K ⊓ Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G) := by
    unfold borelOf
    rw [hRK]
  have hborL : borelOf L R₀ ≤ D ⊔ T := hborLeq ▸ hc.borelOf_L_le h37c h38c hD
  have hborK : borelOf K R₀ ≤ M ⊓ Subgroup.normalizer (L : Set G) := hborKeq ▸ hbor
  have hMO : pCoreOf 2 M ≠ ⊥ := by
    intro h0
    have hVO : fsuV T I ≤ pCoreOf 2 M :=
      CFSG.QuasithinUnique.le_pCoreOf_of_le_normalizer (S.fsuV_le_T.trans hTM) S.hMN
        S.isPGroup_fsuV
    rw [h0] at hVO
    exact S.fsuV_ne_bot (le_bot_iff.mp hVO)
  have hMchar : CharTwo M := charTwo_of_inH' hfsu.qtke hfsu.sylow ⟨hTM, hMO⟩
  have hOMT : pCoreOf 2 M ≤ T :=
    F7.isSylowTwoOf_pCoreOf_le
      (CFSG.Quasithin.isSylowTwoOf_of_quasithinIsSylowTwo hfsu.sylow hTM)
  have hOMR : pCoreOf 2 M ≤ R₀ := by
    refine le_trans ?_ le_sup_right
    rw [hQ, ← S.hQ]
    exact CFSG.QuasithinUnique.le_pCoreOf_of_le_normalizer (hOMT.trans le_sup_right)
      (Setup.L0T_le_fsuM.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M)
  set HD := K ⊔ D ⊔ T with hHD
  have hTHD : T ≤ HD := le_sup_right
  have hDHD : D ≤ HD := le_sup_right.trans le_sup_left
  have hV₁HD : V₁ ≤ pCoreOf 2 HD := by
    refine CFSG.QuasithinUnique.le_pCoreOf_of_le_normalizer
      ((inf_le_left.trans S.fsuV_le_T).trans hTHD) ?_ (S.isPGroup_fsuV.to_le inf_le_left)
    refine sup_le (sup_le (fun k hk => Subgroup.centralizer_le_normalizer _ (hKV hk)) ?_)
      S.T_le_normalizer_V1
    exact fun d hd => S.mem_normalizer_V1_of_mem_N0 (hD.1 hd)
  have hHDO : pCoreOf 2 HD ≠ ⊥ := fun h0 =>
    hc.V1_ne_bot (le_bot_iff.mp (h0 ▸ hV₁HD))
  have hHDchar : CharTwo HD := charTwo_of_inH' hfsu.qtke hfsu.sylow ⟨hTHD, hHDO⟩
  have hOHD : pCoreOf 2 HD ≤ R₀ := hc.pCoreOf_le_r0 h37c h38c h2 hD hdiag hTHD hDHD
  obtain ⟨-, hKlist⟩ := oTwoQuot_facts_of_alt_five hKA
  have hLA := S.oTwoQuot_L_facts h37c h38c h2
  obtain ⟨-, hLlist⟩ := oTwoQuot_facts_of_alt_five hLA
  have hc1 : CharTwo (K ⊔ R₀ ⊔ borelOf L R₀) := by
    refine charTwo_of_pCore_centralizer_le hHDchar (sup_le (sup_le (le_sup_left.trans le_sup_left)
      (hR₀T.trans hTHD)) (hborL.trans (sup_le hDHD hTHD))) ?_
    exact inf_le_left.trans (hOHD.trans (le_sup_right.trans le_sup_left))
  have hc2 : CharTwo (L ⊔ R₀ ⊔ borelOf K R₀) := by
    refine charTwo_of_pCore_centralizer_le hMchar (sup_le (sup_le S.L_le_fsuM (hR₀T.trans hTM))
      (hborK.trans inf_le_left)) ?_
    exact inf_le_left.trans (hOMR.trans (le_sup_right.trans le_sup_left))
  set M₀ := L ⊔ D ⊔ (T ⊓ Subgroup.normalizer (L : Set G)) ⊔ K with hM₀def
  set Y := K ⊔ L ⊔ R₀ with hY
  have hYM₀ : Y ≤ M₀ := sup_le (sup_le le_sup_right (le_sup_left.trans (le_sup_left.trans
    le_sup_left))) ((le_inf hR₀T hR₀L).trans (le_sup_right.trans le_sup_left))
  have hYN : Y ≤ Subgroup.normalizer (Y : Set G) := Subgroup.le_normalizer
  have hM₀N : M₀ ≤ Subgroup.normalizer (Y : Set G) := by
    refine sup_le (sup_le (sup_le ((le_sup_right.trans le_sup_left).trans hYN) ?_) ?_)
      ((le_sup_left.trans le_sup_left).trans hYN)
    · exact le_normalizer_sup_of_le_of_le (le_normalizer_sup_of_le_of_le hDK hDL) hDR₀
    · exact le_normalizer_sup_of_le_of_le (le_normalizer_sup_of_le_of_le
        hT₁K inf_le_right) (inf_le_left.trans hTR₀)
  have hYO : pCoreOf 2 Y = ⊥ := by
    rw [eq_bot_iff, ← hM₀]
    exact CFSG.QuasithinUnique.le_pCoreOf_of_le_normalizer
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 Y).trans hYM₀)
      (hM₀N.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y)
  have hhyp : Hyp111 K L R₀ :=
    ⟨⟨inferInstance, hR₀2, (le_inf hR₀T hR₀L).trans hT₁K, hRK ▸ hTKs, hKlist,
        hborLeq ▸ hbL, hc1⟩,
      ⟨inferInstance, hR₀2, hR₀L, hRL ▸ hc.isSylowTwoOf_inf_L h37 h38 h37c h38c, hLlist,
        hborK.trans inf_le_right, hc2⟩, hYO⟩
  have hhyp' : Hyp111 L K R₀ := ⟨hhyp.h2, hhyp.h1, by rw [sup_comm L K]; exact hhyp.o2⟩
  have hqt : IsQuasithinSub (K ⊔ L ⊔ R₀) := isQuasithinSub_of_qtke hfsu.qtke _
  have hnorm : (R₀.subgroupOf (R₀ ⊔ borelOf L R₀)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
      (sup_le Subgroup.le_normalizer (hborL.trans (sup_le hDR₀ hTR₀)))
  have hLns : ¬ Group.IsSolvable ↥L := fun _ =>
    CFSG.LocalAnalysis.ComponentInitial.not_isSolvable_of_isQuasisimple hfsu.quasisimple
      inferInstance
  have hKq := isL2Quot_two_of_alt_five hKA
  have hLq := isL2Quot_two_of_alt_five hLA
  obtain ⟨L1', L2', hsw, -, hlist, -⟩ :=
    hDSA G K L R₀ hhyp hqt (Or.inr hnorm) hKns hLns (Or.inl ⟨2, hKq⟩)
  have hV₁ne : V₁ ≠ ⊥ := hc.V1_ne_bot
  have hV₁Z : V₁ ≤ centerOf R₀ := le_inf (fun v hv => Subgroup.mem_sup_right (S.fsuV_le_Q hv.1))
    fun v hv => Subgroup.mem_centralizer_iff.mpr fun r hr =>
      (Subgroup.mem_centralizer_iff.mp (r0_le_centralizer_V1 hr) v hv).symm
  have hV₁K : V₁ ≤ Subgroup.centralizer (K : Set G) := fun v hv =>
    Subgroup.mem_centralizer_iff.mpr fun k hk =>
      (Subgroup.mem_centralizer_iff.mp (hKV hk) v hv).symm
  have hO : pCoreOf 2 (L ⊔ R₀) = ⁅pCoreOf 2 (L ⊔ R₀), L⁆ := by
    rcases hsw with ⟨h1', h2'⟩ | ⟨h1', h2'⟩
    · rw [h1', h2'] at hlist
      exact hFI G K L R₀ hhyp hlist hKq hLq K L (Or.inl ⟨rfl, rfl⟩) V₁ hV₁ne hV₁Z hV₁K
    · rw [h1', h2'] at hlist
      exact hFI G L K R₀ hhyp' hlist hLq hKq K L (Or.inr ⟨rfl, rfl⟩) V₁ hV₁ne hV₁Z hV₁K
  have hOL : pCoreOf 2 (L ⊔ R₀) ≤ L := by
    rw [hO, Subgroup.commutator_le]
    intro x hx y hy
    have hxN : x ∈ Subgroup.normalizer (L : Set G) :=
      sup_le Subgroup.le_normalizer hR₀L (CFSG.LieType.BorelTits.pCoreOf_le 2 _ hx)
    rw [commutatorElement_def]
    exact L.mul_mem ((Subgroup.mem_normalizer_iff.mp hxN y).mp hy) (L.inv_mem hy)
  obtain ⟨u₀, hu₀, hu₀L, hu₀c⟩ := hc.exists_other_factor h37c h38c
  have hconj : ∀ x ∈ fsuL0 T L ⊔ T, x * u₀ * x⁻¹ * u₀⁻¹ ∈ Q →
      x ∈ Subgroup.normalizer ((Q ⊔ Subgroup.zpowers u₀ : Subgroup G) : Set G) := by
    intro x hx hxu
    refine mem_normalizer_sup_zpowers (hQN hx) ?_
    have e : x * u₀ * x⁻¹ = (x * u₀ * x⁻¹ * u₀⁻¹) * u₀ := by group
    rw [e]
    exact mul_mem (Subgroup.mem_sup_left hxu) (Subgroup.mem_sup_right (Subgroup.mem_zpowers u₀))
  have hW : Q ⊔ Subgroup.zpowers u₀ ≤ pCoreOf 2 (L ⊔ R₀) := by
    refine CFSG.QuasithinUnique.le_pCoreOf_of_le_normalizer (sup_le (le_sup_right.trans
      le_sup_right) (Subgroup.zpowers_le.mpr (Subgroup.mem_sup_right
        (Subgroup.mem_sup_left hu₀)))) (sup_le ?_ (sup_le ?_ ?_))
      (hfsu.sylow.1.to_le (sup_le inf_le_left (Subgroup.zpowers_le.mpr hu₀.1)))
    · exact fun l hl => hconj l (Subgroup.mem_sup_left (S.L_le_L0 hl)) (hu₀c l hl)
    · exact fun s hs => hconj s (Subgroup.mem_sup_right hs.1) (hc.comm_mem_Q h37c h38c hs hu₀)
    · intro q hq
      refine hconj q (Subgroup.mem_sup_right hq.1) ?_
      have h1 : u₀ * q⁻¹ * u₀⁻¹ ∈ Q :=
        (Subgroup.mem_normalizer_iff.mp (hQN (Subgroup.mem_sup_right hu₀.1)) q⁻¹).mp
          (Q.inv_mem hq)
      have e : q * u₀ * q⁻¹ * u₀⁻¹ = q * (u₀ * q⁻¹ * u₀⁻¹) := by group
      rw [e]
      exact Q.mul_mem hq h1
  exact hu₀L (hOL (hW (Subgroup.mem_sup_right (Subgroup.mem_zpowers u₀))))

theorem lem933_slices (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (h37c : Vol2Native.A37ForSQTKCat) (h38c : Vol2Native.A38ForSQTKCat) (hDSA : DSAL2Statement)
    (hFI : F112FourLinkFactC) (h2 : n = 2) {H K B D : Subgroup G}
    (hH : IsHStar T (fsuM T L) H) (hHK : H = K ⊔ T) (hKc : K ∈ cComp H)
    (hTK : T ≤ Subgroup.normalizer (K : Set G))
    (hKA : Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 5)))
    (hB : Lin2.IsHallTwoPrimeOf B (H ⊓ fsuM T L)) (hBK : B ≤ K)
    (hBTK : B ≤ Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G))
    (hD : Lin2.IsHallTwoPrimeOf D
      (fsuL0 T L ⊓ Subgroup.normalizer ((T ⊓ fsuL0 T L : Subgroup G) : Set G)))
    (hBD : B = D ⊓ Subgroup.centralizer ((fsuV T I ⊓ Subgroup.centralizer
      ((T ⊓ fsuL0 T L : Subgroup G) : Set G) : Subgroup G) : Set G))
    (hDK : D ≤ Subgroup.normalizer (K : Set G))
    (hKV : K ≤ Subgroup.centralizer ((fsuV T I ⊓ Subgroup.centralizer
      ((T ⊓ fsuL0 T L : Subgroup G) : Set G) : Subgroup G) : Set G)) :
    pCoreOf 2 (L ⊔ D ⊔ (T ⊓ Subgroup.normalizer (L : Set G)) ⊔ K) ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hfsu := S.hyp.fsu
  obtain ⟨F, _, _, _, e, ψ, hc, hdiag⟩ := S.exists_isCoord_diag h37c h38c hD
  set M := fsuM T L with hM
  have hTH : T ≤ H := hH.1.1
  have hKH : K ≤ H := le_of_mem_cComp hKc
  have hTM : T ≤ M := Setup.T_le_fsuM
  have hHKn : H ≤ Subgroup.normalizer (K : Set G) := by
    rw [hHK]
    exact sup_le Subgroup.le_normalizer hTK
  have hTHs : IsSylowTwoOf T H := CFSG.Quasithin.isSylowTwoOf_of_quasithinIsSylowTwo hfsu.sylow hTH
  have hTKs : IsSylowTwoOf (T ⊓ K) K := A4.isSylowTwoOf_inf_normal hTHs hKH hHKn
  have hDL0 : D ≤ fsuL0 T L := hD.1.trans inf_le_left
  have hBD' : B ≤ D := hBD ▸ inf_le_left
  have hDL : D ≤ Subgroup.normalizer (L : Set G) :=
    hDL0.trans (hc.L0_le_normalizer_L h37 h38 h37c h38c)
  have hTKR := hc.inf_le_r0 h37c h38c h2 hD hdiag hTK hDK hKV (hBD ▸ hBTK)
  have hBX : B ≤ K ⊓ (H ⊓ M) := le_inf hBK hB.1
  have hBh' : Lin2.IsHallTwoPrimeOf B (K ⊓ (H ⊓ M)) := by
    obtain ⟨-, hBodd, k, hk⟩ := hB
    refine ⟨hBX, hBodd, ?_⟩
    have h1 := Subgroup.relIndex_mul_relIndex B (K ⊓ (H ⊓ M)) (H ⊓ M) hBX inf_le_right
    have h3 : B.relIndex (K ⊓ (H ⊓ M)) ∣ 2 ^ k := by
      rw [← hk, ← h1]
      exact dvd_mul_right _ _
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h3
    exact ⟨j, hj⟩
  have hTKs' : IsSylowTwoOf (T ⊓ K) (K ⊓ (H ⊓ M)) :=
    Lin2.isSylowTwoOf_of_le_of_le hTKs
      (le_inf inf_le_right (le_inf (inf_le_left.trans hTH) (inf_le_left.trans hTM))) inf_le_left
  have hKHM : B ⊔ (T ⊓ K) = K ⊓ (H ⊓ M) := sup_eq_of_isHall_isSylow hBh' hTKs'
  have hbor : K ⊓ Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G) ≤
      M ⊓ Subgroup.normalizer (L : Set G) := by
    have h1 : K ⊓ Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G) ≤ B ⊔ (T ⊓ K) := by
      rw [hKHM]
      exact le_inf inf_le_left (S.inf_normalizer_le hH hHK hKc hTK hKA)
    refine h1.trans (sup_le (le_inf ((hBD'.trans hDL0).trans Setup.L0_le_fsuM) (hBD'.trans hDL))
      (le_inf (inf_le_left.trans hTM) ?_))
    exact hTKR.trans (hc.r0_le_normalizer_L h37 h38 h37c h38c)
  exact S.lem933'_slices h37 h38 h37c h38c hDSA hFI h2 hD (inf_le_left.trans hTK) hDK hKV hTKs hKA
    (not_isSolvable_of_mem_cComp hKc) hTKR hbor
    ((hc.borelOf_L_le h37c h38c hD).trans (sup_le hDK hTK))

end Setup

end CFSG.Quasithin.H13.Ch9

namespace CFSG.Quasithin.H13.Ch9

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H Matrix

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ}

namespace Setup

namespace IsCoord

variable {S : Setup T L I n} {F : Type} [Field F] [Fintype F] [CharP F 2]
  {e : ↥(fsuV T I) ≃* Om4.VM F}
  {ψ : ↥(fsuL0 T L) →* SpecialLinearGroup (Fin 2) F × SpecialLinearGroup (Fin 2) F}
  (hc : S.IsCoord e ψ)
include hc

theorem false_of_pCoreOf_eq_bot_slices (h37 : A37ForSQTK)
    (h38 : A38ForSQTK) (h37c : Vol2Native.A37ForSQTKCat) (h38c : Vol2Native.A38ForSQTKCat)
    (hDSB : CFSG.Quasithin.F112R.DSBStatementL2) (h2 : n = 2) {D : Subgroup G}
    (hD : Lin2.IsHallTwoPrimeOf D
      (fsuL0 T L ⊓ Subgroup.normalizer ((T ⊓ fsuL0 T L : Subgroup G) : Set G)))
    (hdiag : (D.subgroupOf (fsuL0 T L)).map ψ = (diagT F).prod (diagT F))
    {H K : Subgroup G} (hH : IsHStar T (fsuM T L) H) (hHK : H = K ⊔ T) (hKc : K ∈ cComp H)
    (hTK : T ≤ Subgroup.normalizer (K : Set G))
    (hKA : Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 5)))
    (hBh : Lin2.IsHallTwoPrimeOf (D ⊓ Subgroup.centralizer ((fsuV T I ⊓ Subgroup.centralizer
      ((T ⊓ fsuL0 T L : Subgroup G) : Set G) : Subgroup G) : Set G)) (H ⊓ fsuM T L))
    (hBK : D ⊓ Subgroup.centralizer ((fsuV T I ⊓ Subgroup.centralizer
      ((T ⊓ fsuL0 T L : Subgroup G) : Set G) : Subgroup G) : Set G) ≤ K)
    {t : G} (ht : t ∈ T) (htn : t ∉ Subgroup.normalizer (L : Set G))
    {A₀ B₀ : GL (Fin 2) F} {τ₀ : F ≃+* F} (hτ₀ : τ₀ ≠ 1)
    (hform₀ : bar e ⟨t, S.hMN (Setup.T_le_fsuM ht)⟩ = Om4.lr A₀ B₀ * Om4.frM τ₀ * Om4.trM)
    (hO : pCoreOf 2 (D ⊔ H) = ⊥) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hfsu := S.hyp.fsu
  set V₁ := fsuV T I ⊓ Subgroup.centralizer ((T ⊓ fsuL0 T L : Subgroup G) : Set G) with hV₁
  set B := D ⊓ Subgroup.centralizer (V₁ : Set G) with hB
  set M := fsuM T L with hM
  obtain ⟨Dσ, T₂, hDσD, -, hsym, hT₂T, -, -, hTL₂, hBL₂, hsyl, hidx, hnn, hS3, hVL₂, hL₂M⟩ :=
    hc.exists_vertex h37 h38 h37c h38c h2 hD hdiag ht htn hτ₀ hform₀
  set L₂ := Dσ ⊔ T₂ with hL₂
  have hT2 : IsPGroup 2 T := hfsu.sylow.1
  have hTH : T ≤ H := hH.1.1
  have hKH : K ≤ H := le_of_mem_cComp hKc
  have hHKn : H ≤ Subgroup.normalizer (K : Set G) := by
    rw [hHK]
    exact sup_le Subgroup.le_normalizer hTK
  have hTHs : IsSylowTwoOf T H := CFSG.Quasithin.isSylowTwoOf_of_quasithinIsSylowTwo hfsu.sylow hTH
  have hTM : T ≤ M := Setup.T_le_fsuM
  have hTL₂eq : T ⊓ L₂ = T₂ :=
    le_antisymm (KStar.le_of_isSylowTwoOf_of_le hsyl (hT2.to_le inf_le_left)
      (le_inf hT₂T le_sup_right) inf_le_right) (le_inf hT₂T le_sup_right)
  have hborL₂ : borelOf L₂ T = T₂ := by
    have h1 : borelOf L₂ T = borelOf L₂ T₂ := by
      unfold borelOf
      rw [hTL₂eq, inf_eq_left.mpr (le_sup_right : T₂ ≤ L₂)]
    rw [h1]
    exact borelOf_eq_of_relIndex_prime le_sup_right Nat.prime_three hidx hnn
  obtain ⟨P, hP⟩ := exists_sylow_coe_eq hfsu.sylow
  have hborK : borelOf K T ≤ H ⊓ M := by
    set Y₀ := H ⊓ Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G) with hY₀
    have hTY₀ : T ≤ Y₀ := le_inf hTH fun s hs => Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer hs, hTK hs⟩
    have hY₀M : Y₀ ≤ M := by
      by_contra hY₀M
      have hInH : InH T Y₀ := by
        rw [← hP] at hTY₀ ⊢
        exact inH_of_le P hTY₀ inf_le_left (hP ▸ hH.1)
      have hY₀H : Y₀ = H := hH.2.2 Y₀ hInH inf_le_left hY₀M
      have hKN : K ≤ Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G) := by
        intro k hk
        have : k ∈ Y₀ := by rw [hY₀H]; exact hKH hk
        exact this.2
      have hTKs : IsSylowTwoOf (T ⊓ K) K := A4.isSylowTwoOf_inf_normal hTHs hKH hHKn
      have hTKO : T ⊓ K ≤ pCoreOf 2 K :=
        CFSG.QuasithinUnique.le_pCoreOf_of_le_normalizer inf_le_right hKN hTKs.2.1
      have hodd : ¬ 2 ∣ (pCoreOf 2 K).relIndex K := by
        intro h2d
        apply hTKs.2.2
        show 2 ∣ (T ⊓ K).relIndex K
        rw [← Subgroup.relIndex_mul_relIndex (T ⊓ K) (pCoreOf 2 K) K hTKO
          (CFSG.LieType.BorelTits.pCoreOf_le 2 K)]
        exact h2d.mul_left _
      apply hodd
      have h60 := (oTwoQuot_facts_of_alt_five hKA).1
      have hidxK : (pCoreOf 2 K).relIndex K = Nat.card (oTwoQuot ↥K) := by
        rw [Subgroup.relIndex, ← Subgroup.index_eq_card]
        congr 1
        exact Subgroup.comap_map_eq_self_of_injective K.subtype_injective _
      rw [hidxK, h60]
      norm_num
    exact le_inf (inf_le_left.trans hKH) ((inf_le_inf_right _ hKH).trans
      (le_inf inf_le_left hY₀M) |>.trans inf_le_right)
  have hHMeq : B ⊔ T = H ⊓ M := sup_eq_of_isHall_isSylow hBh
    (CFSG.Quasithin.isSylowTwoOf_of_quasithinIsSylowTwo hfsu.sylow (le_inf hTH hTM))
  have hHML₂ : H ⊓ M ≤ Subgroup.normalizer (L₂ : Set G) := by
    rw [← hHMeq]
    exact sup_le hBL₂ hTL₂
  have hHO : pCoreOf 2 H ≠ ⊥ := hH.1.2
  have hMO : pCoreOf 2 M ≠ ⊥ := by
    intro h0
    have hVO : fsuV T I ≤ pCoreOf 2 M := by
      refine CFSG.QuasithinUnique.le_pCoreOf_of_le_normalizer
        (S.fsuV_le_T.trans hTM) S.hMN S.isPGroup_fsuV
    rw [h0] at hVO
    exact S.fsuV_ne_bot (le_bot_iff.mp hVO)
  have hHchar : CharTwo H := charTwo_of_inH' hfsu.qtke hfsu.sylow ⟨hTH, hHO⟩
  have hMchar : CharTwo M := charTwo_of_inH' hfsu.qtke hfsu.sylow ⟨hTM, hMO⟩
  have hOMT : pCoreOf 2 M ≤ T :=
    F7.isSylowTwoOf_pCoreOf_le
      (CFSG.Quasithin.isSylowTwoOf_of_quasithinIsSylowTwo hfsu.sylow hTM)
  obtain ⟨h60, hKlist⟩ := oTwoQuot_facts_of_alt_five hKA
  have hKTeq : K ⊔ T ⊔ borelOf L₂ T = H := by
    rw [hborL₂, hHK]
    exact le_antisymm (sup_le le_rfl (hT₂T.trans le_sup_right)) le_sup_left
  have hc2 : CharTwo (L₂ ⊔ T ⊔ borelOf K T) := by
    refine charTwo_of_pCore_centralizer_le hMchar
      (sup_le (sup_le hL₂M hTM) (hborK.trans inf_le_right)) ?_
    exact inf_le_left.trans (hOMT.trans (le_sup_right.trans le_sup_left))
  have hX : K ⊔ L₂ ⊔ T = D ⊔ H := by
    apply le_antisymm
    · refine sup_le (sup_le (hKH.trans le_sup_right) (sup_le (hDσD.trans le_sup_left)
        (hT₂T.trans (hTH.trans le_sup_right)))) (hTH.trans le_sup_right)
    · refine sup_le ?_ (by rw [hHK]; exact sup_le (le_sup_left.trans le_sup_left) le_sup_right)
      intro x hx
      obtain ⟨b, hb, d, hd, rfl⟩ := hsym x hx
      exact mul_mem (Subgroup.mem_sup_left (Subgroup.mem_sup_left (hBK hb)))
        (Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.mem_sup_left hd)))
  have hhyp : Hyp111 K L₂ T :=
    ⟨⟨inferInstance, hT2, hTK, A4.isSylowTwoOf_inf_normal hTHs hKH hHKn, hKlist,
        hborL₂ ▸ hT₂T.trans hTK, by rw [hKTeq]; exact hHchar⟩,
      ⟨inferInstance, hT2, hTL₂, hTL₂eq ▸ hsyl, isRankOneListed_perm_three hS3.some,
        hborK.trans hHML₂, hc2⟩,
      by rw [hX]; exact hO⟩
  have hqt : IsQuasithinSub (K ⊔ L₂ ⊔ T) := isQuasithinSub_of_qtke hfsu.qtke _
  have hnorm : (T.subgroupOf (T ⊔ borelOf L₂ T)).Normal := by
    rw [hborL₂, sup_eq_left.mpr hT₂T, Subgroup.subgroupOf_self]
    infer_instance
  have hKns : ¬ Group.IsSolvable ↥K := not_isSolvable_of_mem_cComp hKc
  have hKq := isL2Quot_two_of_alt_five hKA
  obtain ⟨L1', L2', hsw, -, hlistB, -⟩ :=
    hDSB G K L₂ T hhyp hqt (Or.inr hnorm) hKns ⟨2, hKq⟩ hS3
  have hS3c : Nat.card (oTwoQuot ↥L₂) = 6 := by
    obtain ⟨e3⟩ := hS3
    rw [Nat.card_congr e3.toEquiv, Nat.card_perm, Nat.card_fin]
    decide
  have hVc : Nat.card ↥(fsuV T I) = 2 ^ 8 := by
    obtain ⟨K₀, _, _, _, e₀, ψ₀, hc₀⟩ := S.exists_isCoord
    rw [Nat.card_congr e₀.toEquiv, card_vm, hc₀.card, h2]
    norm_num
  have hbig : 2 ^ 8 ≤ Nat.card ↥(pCoreOf 2 L₂) := hVc ▸ Subgroup.card_le_of_le hVL₂
  have hbigV' : 2 ^ 8 ≤ Nat.card ↥(pCoreOf 2 (L₂ ⊔ bigB L₂ K T)) :=
    hbig.trans (Subgroup.card_le_of_le hhyp.symm.pCoreOf_le_pCoreOf_vertex)
  have hbigV : 2 ^ 8 ≤ Nat.card ↥(pCoreOf 2 (L₂ ⊔ bigB K L₂ T)) := by
    rwa [bigB_comm K L₂ T] at hbigV'
  unfold F112ListB at hlistB
  rcases hlistB with ⟨-, h3, -, -, -⟩ | ⟨-, h1, hsp, -, h2', -, -, -⟩ |
      ⟨-, h2', -, h1, hcard⟩ | ⟨-, -, -, ⟨e3⟩, hcard⟩
  ·
    have h504 := h3.card (by norm_num)
    rcases hsw with ⟨hL1, -⟩ | ⟨hL1, -⟩ <;> rw [hL1] at h504
    · rw [h60] at h504
      norm_num at h504
    · rw [hS3c] at h504
      norm_num at h504
  ·
    rcases hsw with ⟨hL1, -⟩ | ⟨hL1, hL2⟩
    · rw [hL1] at h1
      have h6 := h1.card (by norm_num)
      rw [h60] at h6
      norm_num at h6
    · rw [hL1, hL2] at hsp
      have h32 := hsp.2.1
      rw [h32] at hbigV'
      norm_num at hbigV'
  ·
    rcases hsw with ⟨hL1, hL2⟩ | ⟨-, hL2⟩
    · rw [hL1, hL2] at hcard
      rw [hcard] at hbigV
      norm_num at hbigV
    · rw [hL2] at h1
      have h6 := h1.card (by norm_num)
      rw [h60] at h6
      norm_num at h6
  ·
    rcases hsw with ⟨hL1, hL2⟩ | ⟨-, hL2⟩
    · rw [hL1, hL2] at hcard
      rw [hcard] at hbigV
      norm_num at hbigV
    · have h6 : Nat.card (oTwoQuot ↥L2') = 6 := by
        rw [Nat.card_congr e3.toEquiv, Nat.card_perm, Nat.card_fin]
        decide
      rw [hL2, h60] at h6
      norm_num at h6

end IsCoord

end Setup

end CFSG.Quasithin.H13.Ch9

namespace CFSG.Quasithin.H13.Ch9

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H Matrix

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ}

namespace Setup

variable (S : Setup T L I n)
include S

theorem prop931_slices (h36 : A36ForSQTK) (h37 : A37ForSQTK)
    (h38 : A38ForSQTK) (h39 : A39ForSQTK) (h312 : A312ForSQTK) (h314 : A314Facts)
    (hA3 : A314ThreeNormFact) (hFB : A314FFFactE9) (hFC : A314InnerLieFact) (hFD : A7FFNoA5Fact)
    (h3108 : Stmt3_2_10_eight) (hDSB : CFSG.Quasithin.F112R.DSBStatementL2)
    (h37c : Vol2Native.A37ForSQTKCat)
    (h38c : Vol2Native.A38ForSQTKCat) (hC58 : TheoremC58) (h317 : AS317Sylow) (h2 : n = 2)
    (h1 : zQ T I = fsuV T I) {H K B D : Subgroup G} (hH : IsHStar T (fsuM T L) H)
    (hHK : H = K ⊔ T) (hKc : K ∈ cComp H) (hTK : T ≤ Subgroup.normalizer (K : Set G))
    (hJ : IsPGroup 2 (kerIn (H ⊓ fsuM T L) H))
    (hKL : IsPSL 2 2 2 ↥(E2.star (H ⊓ fsuM T L) H K))
    (hB : Lin2.IsHallTwoPrimeOf B (H ⊓ fsuM T L)) (hBK : B ≤ K) (hB3 : Nat.card B = 3)
    (hBTK : B ≤ Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G))
    (hD : Lin2.IsHallTwoPrimeOf D
      (fsuL0 T L ⊓ Subgroup.normalizer ((T ⊓ fsuL0 T L : Subgroup G) : Set G)))
    (hBD : B = D ⊓ Subgroup.centralizer ((fsuV T I ⊓ Subgroup.centralizer
      ((T ⊓ fsuL0 T L : Subgroup G) : Set G) : Subgroup G) : Set G)) :
    D ≤ Subgroup.normalizer (K : Set G) ∧
      K ≤ Subgroup.centralizer ((fsuV T I ⊓ Subgroup.centralizer
        ((T ⊓ fsuL0 T L : Subgroup G) : Set G) : Subgroup G) : Set G) := by
  set V₁ := fsuV T I ⊓ Subgroup.centralizer ((T ⊓ fsuL0 T L : Subgroup G) : Set G) with hV₁
  obtain ⟨F, _, _, _, e, ψ, hc, hdiag⟩ := S.exists_isCoord_diag h37c h38c hD
  have hDL : D ≤ fsuL0 T L := hD.1.trans inf_le_left
  have hKH : K ≤ H := le_of_mem_cComp hKc
  have hKA := KStar.nonempty_modO2_equiv_alt_five hKH hJ hKL
  have hZK : K ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) := by
    have hZ := S.le_centerOf h37c h38c hC58 h317 h1 hH
    intro k hk
    refine Subgroup.mem_centralizer_iff.mpr fun z hz => ?_
    exact (Subgroup.mem_centralizer_iff.mp (hZ hz).2 k (hKH hk)).symm
  have hBD' : B ≤ D := hBD ▸ inf_le_left
  have hBN : D ⊓ Subgroup.centralizer (V₁ : Set G) ≤ Subgroup.normalizer (K : Set G) :=
    hBD ▸ hBK.trans Subgroup.le_normalizer
  have hred : D ≤ Subgroup.normalizer (K : Set G) →
      D ≤ Subgroup.normalizer (K : Set G) ∧ K ≤ Subgroup.centralizer (V₁ : Set G) := fun hDK =>
    hc.first_red h2 h1 hdiag hDL hZK hBN (fun d hd _ _ => hDK hd)
  by_cases hDK : D ≤ Subgroup.normalizer (K : Set G)
  · exact hred hDK
  exfalso
  have hKl : K ∈ lFamily T := by
    show K ∈ cComp (K ⊔ T)
    rw [← hHK]
    exact hKc
  by_cases hKV : K ≤ Subgroup.normalizer (V₁ : Set G)
  · exact hDK (hc.le_normalizer_of_le_normalizer_V1 h36 h37 h38 h39 h312 h314 hA3 h37c h38c h2
      hD hdiag hKl hTK hKA hB3 hBD' hBK hBTK hKV)
  by_cases hTV : T ≤ Subgroup.centralizer (V₁ : Set G)
  · apply hKV
    have hV₁Z : V₁ ≤ quasithinOmegaOneCenter T := by
      rw [S.omegaOneCenter_T_eq h1]
      exact fun v hv => ⟨hv.1, Subgroup.mem_centralizer_iff.mpr fun t ht =>
        (Subgroup.mem_centralizer_iff.mp (hTV ht) v hv).symm⟩
    exact fun k hk => mem_normalizer_of_mem_centralizer (Subgroup.centralizer_le hV₁Z (hZK hk))
  obtain ⟨t, ht, htn, -, A₀, B₀, τ₀, hτ₀, hform₀⟩ :=
    hc.exists_swap_field h37 h38 h37c h38c hD hTV
  by_cases hO : pCoreOf 2 (D ⊔ H) = ⊥
  · exact hc.false_of_pCoreOf_eq_bot_slices h37 h38 h37c h38c hDSB h2 hD hdiag hH hHK hKc hTK hKA
      (hBD ▸ hB) (hBD ▸ hBK) ht htn hτ₀ hform₀ hO
  · exact hc.false_of_pCoreOf_ne_bot h36 h37 h38 h39 h312 h314 hA3 hFB hFC hFD h3108 h37c h38c
      h2 h1 hD hdiag hH hHK hKc hTK hKA hB3 hBD' hBK hBTK hZK hKV hDK hO

end Setup

end CFSG.Quasithin.H13.Ch9

namespace CFSG.Quasithin.H13.Ch9

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H Matrix

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ}

namespace Setup

variable (S : Setup T L I n)
include S

theorem false_of_L24_slices
    (h36 : A36ForSQTK) (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (h312 : A312ForSQTK) (h314 : A314Facts) (hA3 : A314ThreeNormFact) (hFB : A314FFFactE9)
    (hFC : A314InnerLieFact) (hFD : A7FFNoA5Fact) (hFI : F112FourLinkFactC)
    (hFE : SL3FourTorusFact) (hFH : Sp4BlockParabolicFact) (h3108 : Stmt3_2_10_eight)
    (hDSA : DSAL2Statement) (hDSB : CFSG.Quasithin.F112R.DSBStatementL2)
    (hC32 : ASInputs.AS_C_1_32)
    (h37c : Vol2Native.A37ForSQTKCat) (h38c : Vol2Native.A38ForSQTKCat) (hC58 : TheoremC58)
    (h317 : AS317Sylow) (h2 : n = 2) (h1 : zQ T I = fsuV T I) {H K B D : Subgroup G}
    (hH : IsHStar T (fsuM T L) H) (hHK : H = K ⊔ T) (hKc : K ∈ cComp H)
    (hTK : T ≤ Subgroup.normalizer (K : Set G)) (hJ : IsPGroup 2 (kerIn (H ⊓ fsuM T L) H))
    (hKL : IsPSL 2 2 2 ↥(E2.star (H ⊓ fsuM T L) H K))
    (hB : Lin2.IsHallTwoPrimeOf B (H ⊓ fsuM T L)) (hBK : B ≤ K) (hB3 : Nat.card B = 3)
    (hBTK : B ≤ Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G))
    (hD : Lin2.IsHallTwoPrimeOf D
      (fsuL0 T L ⊓ Subgroup.normalizer ((T ⊓ fsuL0 T L : Subgroup G) : Set G)))
    (hBD : B = D ⊓ Subgroup.centralizer ((fsuV T I ⊓ Subgroup.centralizer
      ((T ⊓ fsuL0 T L : Subgroup G) : Set G) : Subgroup G) : Set G)) : False := by
  obtain ⟨hDK, hKV⟩ := S.prop931_slices h36 h37 h38 h39 h312 h314 hA3 hFB hFC hFD h3108 hDSB
    h37c h38c
    hC58 h317 h2 h1 hH hHK hKc hTK hJ hKL hB hBK hB3 hBTK hD hBD
  have hKH : K ≤ H := le_of_mem_cComp hKc
  have hKA := KStar.nonempty_modO2_equiv_alt_five hKH hJ hKL
  have hBK' : D ⊓ Subgroup.centralizer ((fsuV T I ⊓ Subgroup.centralizer
      ((T ⊓ fsuL0 T L : Subgroup G) : Set G) : Subgroup G) : Set G) ≤ K := hBD ▸ hBK
  set T₁ := T ⊓ Subgroup.normalizer (L : Set G) with hT₁
  set M₀ := L ⊔ D ⊔ T₁ ⊔ K with hM₀
  have hKM : ¬ K ≤ fsuM T L := fun h => hH.2.1 (by rw [hHK]; exact sup_le h Setup.T_le_fsuM)
  have hM₀M : ¬ M₀ ≤ fsuM T L := fun h => hKM (le_sup_right.trans h)
  have hM₀O := S.lem933_slices h37 h38 h37c h38c hDSA hFI h2 hH hHK hKc hTK hKA hB hBK hBTK hD
    hBD hDK
    hKV
  have hsyl := S.lem934 h37 h38 h37c h38c h3108 (le_sup_left.trans (le_sup_left.trans le_sup_left))
    (le_sup_right.trans le_sup_left) hM₀O hM₀M
  have hKl : K ∈ lFamily T := by
    show K ∈ cComp (K ⊔ T)
    rw [← hHK]
    exact hKc
  obtain ⟨K₀, hK₀, hLK₀, hKK₀, hK₀n⟩ := S.exists_K0 h37 h38 h39 h37c h38c h2 hKl hD hBK' hM₀O hsyl
  obtain ⟨-, -, hchar⟩ := S.lem936 h37 h38 h37c h38c h3108 h2 h1 hD hBK' hM₀O hsyl hM₀M hK₀ hLK₀
    hKK₀
  have hKHM := S.sup_eq_inf_of_hall hH hHK hKc hTK hB hBK
  rw [hBD] at hKHM
  rcases S.lem937 h37 h38 h37c h38c hFB hFD h3108 h2 h1 hH hHK hKc hTK hKA hD hBK' hKHM
      (hBD ▸ hBTK) hKV hM₀O hsyl hchar hK₀ hLK₀ hKK₀ hK₀n with hSL | hSp | hG2
  · exact S.lem938 h37 h38 h37c h38c hFE h2 hH hHK hKc hTK hKA hBK hB3 hD hBD hDK hsyl hK₀ hLK₀
      hKK₀ hK₀n hSL
  · exact S.lem9310 h37 h38 h37c h38c hC32 hFH h3108 h2 hH hHK hKc hD hBK' h1 hM₀O hsyl hK₀ hLK₀
      hKK₀ hK₀n hSp
  · exact S.lem939 h37 h38 h37c h38c hC32 h3108 h2 hH hHK hKc hD hBK' h1 hM₀O hsyl hK₀ hLK₀ hKK₀
      hK₀n hG2

end Setup

end CFSG.Quasithin.H13.Ch9

namespace CFSG.Quasithin.H13.Ch9

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H Matrix

theorem stmt9_false_of_setup_slices
    (h36 : A36ForSQTK) (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (h37c : Vol2Native.A37ForSQTKCat) (h38c : Vol2Native.A38ForSQTKCat) (h312 : A312ForSQTK)
    (h314 : A314Facts) (h3104 : Stmt3_2_10_four) (h3108 : Stmt3_2_10_eight)
    (h3228 : Stmt3_2_2_eight) (h331 : Stmt3_3_1)
    (h316 : Theorem316Statement) (hB69 : B69One) (hC58 : TheoremC58) (h317 : AS317Sylow)
    (hE22 : E2.E22StatementC) (h4414 : Stmt4_4_14) (h122 : Vol2Native.Lemma122A)
    (hE610 : Ch6InE610Four) (h63 : ASInputs.AS_E_6_3) (h612 : ASInputs.AS_E_6_12)
    (hH11 : Ch9InH11Plus) (hF1 : FactBorelOddLarge) (hF2 : FactBenderCartanFrob)
    (hA3 : A314ThreeNormFact) (hFB : A314FFFactE9) (hFC : A314InnerLieFact) (hFD : A7FFNoA5Fact)
    (hFI : F112FourLinkFactC) (hFE : SL3FourTorusFact) (hFH : Sp4BlockParabolicFact)
    (hDSA : DSAL2Statement) (hDSB : CFSG.Quasithin.F112R.DSBStatementL2)
    (hC32 : ASInputs.AS_C_1_32)
    (hFa : A314QuasiRankFact) (hFb : A314FFCohomFact) (hL34 : Ch9L34Branch)
    {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ} (S : Setup T L I n) : False := by
  have := S.comm
  obtain ⟨H, hH⟩ := ((h331 G T S.hyp.fsu.simple S.hyp.fsu.nonabelian S.hyp.fsu.qtke
    S.hyp.fsu.sylow).2 L S.hyp.fsu.maximal S.hyp.fsu.quasisimple).2.2.1
  have h1 := S.zQ_eq h37c h38c hC58 h317 h316 hB69 ⟨H, hH⟩
  have h2 := S.eq_two hE22 h4414 hC58 h317 h122 h37c h38c h37 h38 h39 h3228 hE610 h63 hH11 h1
    h331 hF1 hF2
  subst h2
  have hle := S.nParam_le_two hE22 h4414 hC58 h317 h122 h37c h38c h37 h38 h39 h3228 hE610 h63
    hH11 h1 h331 hF1 hF2 hH
  have hne := S.nParam_ne_zero hH.1.1
  obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp (ne_top_of_le_ne_top (ENat.natCast_ne_top 2) hle)
  rw [← hk] at hle hne
  have hk2 : k ≤ 2 := by exact_mod_cast hle
  have hk0 : k ≠ 0 := fun h => hne (by rw [h]; rfl)
  interval_cases k
  · exact (hk0 rfl).elim
  ·
    obtain ⟨K, _, _, _, e, ψ, hc⟩ := S.exists_isCoord
    exact hc.false_of_nParam_eq_one h36 h312 h314 h37 h38 h39 h37c h38c h3104 h3108 hFa hFb
      h3228 hE610 h612 hH11 h1 rfl hH (by rw [← hk, Nat.cast_one])
  ·
    have hn2 : E1.nParam H = 2 := by rw [← hk]; rfl
    have hn1 : 1 < E1.nParam H := by rw [hn2]; norm_num
    obtain ⟨K, hKc, hHK, hTK, hJ, htype, hBall⟩ := S.exists_comp_of_nParam_eq_two hE22 h4414
      hC58 h317 h122 h37c h38c h37 h38 h39 h3228 hE610 h63 hH11 h1 h331 hF1 hF2 hH hn2
    obtain ⟨B, hB⟩ := S.exists_hall hE22 h331 hH hn1
    obtain ⟨hBK, hB3, hBTK⟩ := hBall B hB
    obtain ⟨-, -, -, -, D, hD, hBD⟩ := S.hall_eq_cartan hE22 h4414 hC58 h317 h331 h122 h37c h38c
      h37 h38 h39 h3228 hE610 h63 hH11 h1 hH hn1 hB
    rcases htype with hL24 | hL34'
    · exact S.false_of_L24_slices h36 h37 h38 h39 h312 h314 hA3 hFB hFC hFD hFI hFE hFH h3108 hDSA
        hDSB
        hC32 h37c h38c hC58 h317 rfl h1 hH hHK hKc hTK hJ hL24 hB hBK hB3 hBTK hD hBD
    · exact hL34 G T L I S h1 H K B D hH hn2 hHK hKc hTK hJ hL34' hB hBK hB3 hBTK hD hBD

theorem stmt9_omegaPlusA_of_slices
    (h36 : A36ForSQTK) (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (h37c : Vol2Native.A37ForSQTKCat) (h38c : Vol2Native.A38ForSQTKCat) (h312 : A312ForSQTK)
    (h314 : A314Facts) (h3104 : Stmt3_2_10_four) (h3108 : Stmt3_2_10_eight)
    (h3228 : Stmt3_2_2_eight) (h326 : Stmt3_2_6LtA) (h331 : Stmt3_3_1)
    (h316 : Theorem316Statement) (hB69 : B69One) (hC58 : TheoremC58) (h317 : AS317Sylow)
    (hE22 : E2.E22StatementC) (h4414 : Stmt4_4_14) (h122 : Vol2Native.Lemma122A)
    (hE610 : Ch6InE610Four) (h63 : ASInputs.AS_E_6_3) (h612 : ASInputs.AS_E_6_12)
    (hH11 : Ch9InH11Plus) (hF1 : FactBorelOddLarge) (hF2 : FactBenderCartanFrob)
    (hA3 : A314ThreeNormFact) (hFB : A314FFFactE9) (hFC : A314InnerLieFact) (hFD : A7FFNoA5Fact)
    (hFI : F112FourLinkFactC) (hFE : SL3FourTorusFact) (hFH : Sp4BlockParabolicFact)
    (hDSA : DSAL2Statement) (hDSB : CFSG.Quasithin.F112R.DSBStatementL2)
    (hC32 : ASInputs.AS_C_1_32)
    (hFa : A314QuasiRankFact) (hFb : A314FFCohomFact) (hL34 : Ch9L34Branch) :
    Stmt9_omegaPlusA := by
  intro G _ _ T L I hyp hcomm n hrow
  have := hcomm
  exact stmt9_false_of_setup_slices h36 h37 h38 h39 h37c h38c h312 h314 h3104 h3108 h3228 h331
    h316 hB69
    hC58 h317 hE22 h4414 h122 hE610 h63 h612 hH11 hF1 hF2 hA3 hFB hFC hFD hFI hFE hFH hDSA hDSB hC32
    hFa hFb hL34
    (Setup.of h37 h38 h39 h3228 h326 hyp hrow)

end CFSG.Quasithin.H13.Ch9

namespace CFSG.Quasithin.H13.Ch9

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H

theorem ch9L34Push_of_slices
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK) (h37c : Vol2Native.A37ForSQTKCat)
    (h38c : Vol2Native.A38ForSQTKCat) (hFB : A314FFFactE9) (hFD : A7FFNoA5Fact)
    (hFE : SL3FourTorusFact) (hFH : Sp4BlockParabolicFact) (hC32 : ASInputs.AS_C_1_32)
    (h3108 : Stmt3_2_10_eight) (hDSA : DSAL2Statement) (hFI : F112FourLinkFactC)
    (hTorus : FactL34Torus) : Ch9L34Push := by
  intro G _ _ T L I S h1 H K B D hH _ hHK hKc hTK hJ hKL hB hBK hB3 hBTK hD hBD _ hDK hKV
  exfalso
  obtain ⟨K', hV⟩ := S.exists_vertex_l34 h37 h38 h37c h38c hTorus rfl hH hHK hKc hTK hJ hKL hB
    hBK hBTK hD hBD hDK hKV
  set T₁ := T ⊓ Subgroup.normalizer (L : Set G) with hT₁
  have hKns : ¬ Group.IsSolvable ↥K' := not_isSolvable_of_mem_cComp hV.lfam
  have hKperf : ⁅K', K'⁆ = K' := perfect_of_mem_cComp hV.lfam
  have hM₀O := S.lem933'_slices h37 h38 h37c h38c hDSA hFI rfl hD hV.T1_le hV.D_le hV.centralizer_V1
    hV.sylow hV.alt5 hKns hV.r0 hV.borel hV.borelL
  have hM₀M : ¬ L ⊔ D ⊔ T₁ ⊔ K' ≤ fsuM T L := fun h => hV.not_le_M (le_sup_right.trans h)
  have hsyl := S.lem934 h37 h38 h37c h38c h3108
    (le_sup_left.trans (le_sup_left.trans le_sup_left)) (le_sup_right.trans le_sup_left) hM₀O
    hM₀M
  have hBK' : D ⊓ Subgroup.centralizer ((fsuV T I ⊓ Subgroup.centralizer
      ((T ⊓ fsuL0 T L : Subgroup G) : Set G) : Subgroup G) : Set G) ≤ K' := hBD ▸ hV.B_le
  obtain ⟨K₀, hK₀, hLK₀, hKK₀, hK₀n⟩ := S.exists_K0' h37 h38 h39 h37c h38c rfl hV.lfam hD hBK'
    hM₀O hsyl
  obtain ⟨-, -, hchar⟩ := S.lem936 h37 h38 h37c h38c h3108 rfl h1 hD hBK' hM₀O hsyl hM₀M hK₀
    hLK₀ hKK₀
  obtain ⟨F, _, _, _, e, ψ, hc⟩ := S.exists_isCoord
  have hJT₁ : thompsonJ T ≤ T₁ :=
    le_inf (thompsonJ_le_self T) fun j hj => hc.r0_le_normalizer_L h37 h38 h37c h38c
      (Subgroup.mem_sup_right ⟨thompsonJ_le_self T hj, S.hJ hj⟩)
  have hs : IsSimpleGroup (O2Q K') := by
    obtain ⟨eA⟩ := hV.alt5
    have : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
    exact eA.isSimpleGroup
  have hKJ := S.commutator_thompsonJ_eq' h3108 hKperf hs (hJT₁.trans hV.T1_le) hV.pCore_le
    hV.not_le_M
  rcases S.lem937' h37 h38 h37c h38c hFB hFD h3108 rfl h1 hV.lfam hV.T1_le hV.alt5 hD hBK'
      hV.inf_M hKJ hV.centralizer_V1 hM₀O hsyl hchar hK₀ hLK₀ hKK₀ hK₀n with hSL | hSp | hG2
  · exact S.lem938' h37 h38 h37c h38c hFE rfl hV.alt5 hKperf hV.not_le_M hV.T1_le hV.B_le hB3 hD
      hBD hV.D_le hV.other hsyl hK₀ hLK₀ hKK₀ hK₀n hSL
  · exact S.lem9310' h37 h38 h37c h38c hC32 hFH h3108 rfl hV.not_le_M hKns hD hBK' h1 hM₀O hsyl
      hK₀ hLK₀ hKK₀ hK₀n hSp
  · exact S.lem939' h37 h38 h37c h38c hC32 h3108 rfl hV.not_le_M hKns hD hBK' h1 hM₀O hsyl hK₀
      hLK₀ hKK₀ hK₀n hG2

end CFSG.Quasithin.H13.Ch9
