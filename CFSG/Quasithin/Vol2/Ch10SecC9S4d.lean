module

public import CFSG.Quasithin.Vol2.Ch10SecC9Ctx
public import CFSG.Quasithin.Vol2.Ch10SecC9S4b
public import CFSG.Quasithin.Vol2.Ch10SecC9S4c

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC

open CFSG.Open CFSG.Quasithin.H13 CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem le_normalizer_VI (T L I J : Subgroup G) (w : G) :
    J ⊔ (T ⊓ Subgroup.centralizer ({w} : Set G)) ≤ Subgroup.normalizer (VI T L I J w : Set G) :=
  le_normalizer_conjClosure _ _

namespace Conf

variable {T L I J : Subgroup G} {t w : G} (c : Conf T L I t w J)
include c

theorem conjClosure_eq : conjClosure L J = J :=
  conjClosure_eq_of_lt c.mem c.le (not_isSolvable_of_mem_cComp c.hyp.fsu.maximal.1.2.1)

theorem L_not_le_centralizer (hC : Subgroup.centralizer (VI T L I J w : Set G) ≤ fsuM T L) :
    ¬ L ≤ Subgroup.centralizer (VI T L I J w : Set G) := by
  intro hL
  apply c.not_le
  have hJN : J ≤ Subgroup.normalizer (Subgroup.centralizer (VI T L I J w : Set G) : Set G) :=
    fun j hj => mem_normalizer_centralizer' (le_normalizer_VI T L I J w (Subgroup.mem_sup_left hj))
  have hle : conjClosure L J ≤ Subgroup.centralizer (VI T L I J w : Set G) := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro _ ⟨h, hh, l, hl, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp (hJN hh) l).mp (hL hl)
  rw [c.conjClosure_eq] at hle
  exact hle.trans hC

theorem not_thompsonJ_le_centralizer
    (h37 : QuasithinUnique.Vol2Native.A37ForSQTKCat)
    (h38 : QuasithinUnique.Vol2Native.A38ForSQTKCat) (h1026 : Stmt10_2_6)
    (hC : Subgroup.centralizer (VI T L I J w : Set G) ≤ fsuM T L) :
    ¬ thompsonJ T ≤ Subgroup.centralizer (VI T L I J w : Set G) := by
  intro hJ
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Tw := T ⊓ Subgroup.centralizer ({w} : Set G) with hTw
  set V' := VI T L I J w with hV'
  have hyp := c.hyp
  have hTw2 : IsPGroup 2 Tw := hyp.fsu.sylow.1.to_inf_left
  have hTwL : Tw ≤ Subgroup.normalizer (L : Set G) := (c.Tw_le_T1 h37 h38).trans inf_le_right
  have hsimp : IsSimpleGroup (↥L ⧸ CFSG.pCore 2 ↥L) :=
    SecA.isSimpleGroup_of_not_normal h37 h38 hyp.fsu.simple hyp.fsu.nonabelian hyp.fsu.qtke
      hyp.fsu.faithful hyp.not_normal
  have hLperf : ⁅L, L⁆ = L := commutator_self_of_local hyp.fsu.faithful.1
  have hNV : ∀ x ∈ J ⊔ Tw, x ∈ Subgroup.normalizer (Subgroup.centralizer (V' : Set G) : Set G) :=
    fun x hx => mem_normalizer_centralizer' (le_normalizer_VI T L I J w hx)
  have hLC : L ⊓ Subgroup.centralizer (V' : Set G) ≤ pCoreOf 2 L := by
    rcases le_pCoreOf_or_eq_of_normal hLperf hsimp inf_le_left (fun l hl =>
      mem_normalizer_inf' (Subgroup.le_normalizer hl) (hNV l (Subgroup.mem_sup_left (c.le hl))))
      with h | h
    · exact h
    · refine absurd (fun l hl => ?_) (c.L_not_le_centralizer hC)
      have hl' : l ∈ L ⊓ Subgroup.centralizer (V' : Set G) := by rw [h]; exact hl
      exact hl'.2
  set X := (L ⊔ Tw) ⊓ Subgroup.centralizer (V' : Set G) with hX
  have hX2 : IsPGroup 2 X := by
    rintro ⟨x, hxH, hxC⟩
    have hx' : x ∈ (↑(L ⊔ Tw) : Set G) := hxH
    rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ hTwL] at hx'
    obtain ⟨l, hl, s, hs, hls⟩ := hx'
    have hls' : l * s = x := hls
    obtain ⟨k, hk⟩ := hTw2 ⟨s, hs⟩
    have hsk : s ^ 2 ^ k = 1 := congrArg Subtype.val hk
    obtain ⟨l', hl', he⟩ := exists_pow_eq_mul hl (hTwL hs) (2 ^ k)
    rw [hsk, mul_one, hls'] at he
    have hxk : x ^ 2 ^ k ∈ L ⊓ Subgroup.centralizer (V' : Set G) :=
      ⟨he ▸ hl', Subgroup.pow_mem _ hxC _⟩
    obtain ⟨m, hm⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L ⟨_, hLC hxk⟩
    have hxm : (x ^ 2 ^ k) ^ 2 ^ m = 1 := congrArg Subtype.val hm
    refine ⟨k + m, Subtype.ext ?_⟩
    show x ^ 2 ^ (k + m) = 1
    rw [pow_add, pow_mul, hxm]
  have hLTw : L ⊔ Tw ≤ J ⊔ Tw := sup_le_sup_right c.le _
  have hXn : L ⊔ Tw ≤ Subgroup.normalizer (X : Set G) := fun x hx =>
    mem_normalizer_inf' (Subgroup.le_normalizer hx) (hNV x (hLTw hx))
  have hXO : X ≤ pCoreOf 2 (L ⊔ Tw) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer (r := 2) inf_le_left hXn hX2
  have hJT : thompsonJ T ≤ Tw := le_inf (B6.thompsonJ_le T) c.claim.2.2.2.2.1
  have hJP : thompsonJ T ≤ pCoreOf 2 (L ⊔ Tw) := (le_inf (hJT.trans le_sup_right) hJ).trans hXO
  have hSylL : IsSylowTwoOf Tw (L ⊔ Tw) :=
    A4.isSylowTwoOf_mono c.sylow le_sup_right (hLTw.trans (sup_le c.J_le inf_le_right))
  have hPT : pCoreOf 2 (L ⊔ Tw) ≤ T :=
    (A4.le_of_normal_of_isSylowTwoOf hSylL (CFSG.LieType.BorelTits.pCoreOf_le 2 _)
      ((Subgroup.normal_subgroupOf_iff_le_normalizer (CFSG.LieType.BorelTits.pCoreOf_le 2 _)).mpr
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)).trans inf_le_left
  have hJeq : thompsonJ (pCoreOf 2 (L ⊔ Tw)) = thompsonJ T := B6.thompsonJ_eq_of_le hJP hPT
  have hLN : L ⊔ Tw ≤ Subgroup.normalizer (thompsonJ T : Set G) := by
    rw [← hJeq]
    exact (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _).trans
      (normalizer_le_normalizer_thompsonJ _)
  have hTN : T ≤ Subgroup.normalizer (thompsonJ T : Set G) :=
    Subgroup.le_normalizer.trans (normalizer_le_normalizer_thompsonJ T)
  have hL0N : fsuL0 T L ≤ Subgroup.normalizer (thompsonJ T : Set G) := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro _ ⟨h, hh, l, hl, rfl⟩
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (hTN hh) (hLN (Subgroup.mem_sup_left hl)))
      (Subgroup.inv_mem _ (hTN hh))
  have hJne : thompsonJ T ≠ ⊥ := by
    obtain ⟨A, hA⟩ := exists_isMaxElemAbelian T
    have hcard := hA.2.2 _ (SecA.fsuVM_le_T hyp) (SecA.isElemAbelian_fsuVM hyp)
    have hV1 : 1 < Nat.card (fsuVM T L I) :=
      (Subgroup.one_lt_card_iff_ne_bot _).mpr fun h => c.w_ne_one (by
        have := c.w_mem_V
        rw [h, Subgroup.mem_bot] at this
        exact this)
    intro h
    have hAb : A = ⊥ := le_bot_iff.mp (h ▸ le_thompsonJ_of_isMaxElemAbelian hA)
    rw [hAb, Subgroup.card_bot] at hcard
    omega
  have hNM : Subgroup.normalizer (thompsonJ T : Set G) ≤ fsuM T L := by
    refine le_fsuM_of_le hyp h1026 (sup_le hL0N (inf_le_left.trans hTN)) fun h => hJne ?_
    rw [eq_bot_iff, ← h]
    exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer (r := 2) Subgroup.le_normalizer le_rfl
      (hyp.fsu.sylow.1.to_le (B6.thompsonJ_le T))
  set K := (J ⊔ Tw) ⊓ Subgroup.centralizer (V' : Set G) with hK
  have hKn : J ⊔ Tw ≤ Subgroup.normalizer (K : Set G) := fun x hx =>
    mem_normalizer_inf' (Subgroup.le_normalizer hx) (hNV x hx)
  have hSylK : IsSylowTwoOf (Tw ⊓ K) K :=
    A4.isSylowTwoOf_inf_normal c.isSylowTwoOf_sup inf_le_left hKn
  have hJK : thompsonJ T ≤ Tw ⊓ K := le_inf hJT (le_inf (hJT.trans le_sup_right) hJ)
  have hJeq2 : thompsonJ (Tw ⊓ K) = thompsonJ T :=
    B6.thompsonJ_eq_of_le hJK (inf_le_left.trans inf_le_left)
  apply c.not_le
  intro j hj
  obtain ⟨n, hn, k', hk', rfl⟩ := exists_mul_of_sylow inf_le_left hKn inf_le_right hSylK.2.1
    hSylK.2.2 j (Subgroup.mem_sup_left hj)
  have hnJ : n ∈ Subgroup.normalizer (thompsonJ T : Set G) := by
    rw [← hJeq2]
    exact normalizer_le_normalizer_thompsonJ _ hn.2
  exact (fsuM T L).mul_mem (hNM hnJ) (hC hk'.2)

end Conf

end CFSG.Quasithin.Vol2.Ch10.SecC
