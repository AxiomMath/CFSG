module

public import CFSG.Quasithin.Background.SmithB51SL3L

public section

namespace CFSG.Quasithin

namespace B5

open CFSG.Assembly.LowTwoRank

section Nat

variable {V : Type} [CommGroup V] {L : Subgroup (MulAut V)}

theorem NatSec.not_commSub_le_bot {K : Type} [Field K] {J : Subgroup V} (c : NatSec L J ⊥ K)
    (hLJ : L ≤ stabSub J) : ¬ commSub J L ≤ ⊥ := by
  intro hle
  obtain ⟨x, hx⟩ := c.hfs (Multiplicative.ofAdd (Pi.single 1 1))
  set γ := elT (K := K) (show (0 : Fin 3) ≠ 1 by decide) 1 with hγ
  have hxJ : ((c.π γ : ↥L) : MulAut V) x ∈ J := ((hLJ (c.π γ).2) x).2 x.2
  have h1 : ((c.π γ : ↥L) : MulAut V) x * (x : V)⁻¹ ∈ commSub J L :=
    Subgroup.subset_closure ⟨_, (c.π γ).2, x, x.2, rfl⟩
  have h2 := hle h1
  rw [Subgroup.mem_bot, mul_inv_eq_one] at h2
  have h3 := c.hfe γ x hxJ
  have e1 : (⟨_, hxJ⟩ : ↥J) = x := Subtype.ext h2
  rw [e1, hx] at h3
  have h4 := congrFun (congrArg Multiplicative.toAdd h3) 0
  have h5 : slAct γ (Pi.single 1 1) 0 = 1 := by
    rw [hγ, slAct_elT]
    simp
  simp only [toAdd_ofAdd] at h4
  change (Pi.single 1 (1 : K) : Fin 3 → K) 0 = slAct γ (Pi.single 1 1) 0 at h4
  rw [h5] at h4
  simp at h4

theorem NatSec.inf_centSec_eq_bot {K : Type} [Field K] {J : Subgroup V} (c : NatSec L J ⊥ K) :
    L ⊓ centSec J ⊥ = ⊥ := by
  rw [eq_bot_iff]
  rintro l ⟨hl, -, hlJ⟩
  obtain ⟨γ, hγ⟩ := c.hπ.2 ⟨l, hl⟩
  have hfix : ∀ x : ↥J, ((c.π γ : ↥L) : MulAut V) x = x := by
    intro x
    have := hlJ x x.2
    rw [Subgroup.mem_bot, mul_inv_eq_one] at this
    rw [hγ]
    exact this
  have hγ1 : γ = 1 := by
    apply ext_slAct
    intro v
    rw [slAct_one]
    obtain ⟨x, hx⟩ := c.hfs (Multiplicative.ofAdd v)
    have hxJ : ((c.π γ : ↥L) : MulAut V) x ∈ J := by rw [hfix x]; exact x.2
    have h1 := c.hfe γ x hxJ
    have e1 : (⟨_, hxJ⟩ : ↥J) = x := Subtype.ext (hfix x)
    rw [e1, hx] at h1
    exact (congrArg Multiplicative.toAdd h1).symm
  rw [hγ1, map_one] at hγ
  rw [Subgroup.mem_bot]
  exact (congrArg Subtype.val hγ).symm

end Nat

section Equal

variable {V : Type} [CommGroup V] [Finite V] {G L : Subgroup (MulAut V)}

theorem SL3Split.le_L_of_offender (hA21 : AsA21SQTKSection) (hB42 : AsB42)
    (hA36 : AsA36NoOddCover) (hV : ∀ v : V, v ^ 2 = 1) (h : B51Hyp G L) (s : SL3Split G L)
    {B : Subgroup (MulAut V)} (hB : IsFFStarOffender G B) : B ≤ L := by
  classical
  have hBG := hB.1
  have hBel := hB.2.2.1
  have hBne := hB.2.1
  have hBL : ∀ b ∈ B, ∀ l ∈ L, b * l * b⁻¹ ∈ L := fun b hb l hl => normal_L h b (hBG hb) l hl
  obtain ⟨J, -, hLJ, hBJ, c, hcπ⟩ := s.exists_fixed_natural hBel.isPGroup hBL
  have hbot : ∀ X : Subgroup (MulAut V), X ≤ stabSub (⊥ : Subgroup V) := fun X g _ u => by
    simp only [Subgroup.mem_bot, MulEquiv.map_eq_one_iff]
  have hnc := c.not_commSub_le_bot hLJ
  have sB : SecCtx G L B J ⊥ := ⟨hBG, hBel, hBne, bot_le, sup_le hLJ hBJ, hbot _, hnc⟩
  set eL : ↥L ≃* ↥(StatedSL 3 s.K) := (MulEquiv.ofBijective s.e₁.π s.e₁.hπ).symm with heL
  have hT : IsL345Type ↥(autSec L J ⊥) :=
    Or.inl ⟨s.n, s.K, inferInstance, inferInstance, s.hK,
      ⟨(secEquiv L hLJ (hbot L) c.inf_centSec_eq_bot).symm.trans eL⟩⟩
  have hfaith := sec_faithful hA36 h sB hT
  have hfB : B ⊓ centSec J ⊥ = ⊥ := by
    rw [eq_bot_iff, ← hfaith]
    exact inf_le_inf_right _ le_sup_right
  have hJpos : (⊥ : Subgroup V) < J := by
    rw [bot_lt_iff_ne_bot]
    intro hJ
    have h1 := c.card_eq
    rw [hJ, Subgroup.card_bot] at h1
    have h2 : 1 < Nat.card s.K := Finite.one_lt_card
    have h3 : 1 < Nat.card s.K ^ 3 := Nat.one_lt_pow (by norm_num) h2
    omega
  have hirr : XMod.IsIrrSec ↥(autSec L J ⊥) (⊥ : Subgroup (Sec J ⊥)) ⊤ :=
    isIrrSec_autSec hJpos (fun J' hJ' _ hle => c.eq_bot_or_eq hLJ hle hJ') hLJ (hbot L)
  have hBoff : IsFFStarOffender (L ⊔ B) B := ⟨le_sup_right, hBne, hBel, hB.2.2.2⟩
  have hB' := isFFStarOffender_autSec_bot hBoff (sup_le hLJ hBJ) hfB
  rcases b42_trichotomy hA21 hB42 hV h sB hirr hB' with h2 | h9 | hbig
  · have h1 := B6.le_ffJ hB'
    rw [h2.1] at h1
    exact le_of_autSec_le sB.hMW sB.hMU hfaith le_sup_left le_sup_right h1
  · exact (false_of_b42Case9 hA36 h sB s.hK eL h9).elim
  ·
    exfalso
    have hAG : s.A ≤ G := s.hmin.1.1
    have hAel : IsElemAbelian2 s.A := s.hmin.1.2.2.1
    have hAne : s.A ≠ ⊥ := s.hmin.1.2.1
    have hAJ : s.A ≤ stabSub J := s.hAL.trans hLJ
    have sA : SecCtx G L s.A J ⊥ := ⟨hAG, hAel, hAne, bot_le, sup_le hLJ hAJ, hbot _, hnc⟩
    have hA2 := isA2_secA h sA
    have hA2' : IsA2 (autSec (L ⊔ B) J ⊥) (autSec s.A J ⊥) :=
      ⟨autSec_mono (s.hAL.trans le_sup_left) J ⊥, hA2.2.1, hA2.2.2⟩
    have hle : qOf (autSec (L ⊔ B) J ⊥) ≤ ((rAV (autSec s.A J ⊥) : ℚ) : WithTop ℚ) :=
      qOf_le_iff.2 ⟨_, hA2', isQuadratic_secA sA s.hquad, le_rfl⟩
    have hpre : (s.A.subgroupOf L).comap c.π = axisSub (stdAxis s.K) := by
      rw [hcπ]
      exact s.hpre
    have hne : axisSub (stdAxis s.K) ≠ ⊥ := by
      intro h0
      have h1 := xW_mem (K := s.K) (Pi.single 0 1) (by simp)
      rw [h0, Subgroup.mem_bot] at h1
      have h2 := congrFun (congrArg (fun g => slAct g (Pi.single 2 1)) h1) 0
      simp [slAct_xW, slAct_one] at h2
    have hfixK : Module.finrank s.K (fixK ((s.A.subgroupOf L).comap c.π)) = 2 := by
      rw [hpre, fixK_eq_of_le_axisSub (finrank_coordHyp 2) le_rfl hne, finrank_coordHyp]
    have hrk1 : rkIdx (fixV (autSec s.A J ⊥)) = s.n := by
      rw [rkIdx_fixV_autSec_nat s.hK c.hπ.2 c.f c.hfs c.hfk c.hfe hLJ (hbot L) bot_le s.hAL,
        hfixK]
      omega
    have hrk2 : rk (autSec s.A J ⊥) = 2 * s.n := by
      rw [rk_autSec_eq hAJ (hbot _) (sec_A_inf_centSec h sA)]
      have h1 := B1.card_elemAbelian hAel
      rw [s.hcardA, s.hK, ← pow_mul] at h1
      exact (Nat.pow_right_injective le_rfl h1).symm.trans (by ring)
    have hn : 0 < s.n := by
      rcases Nat.eq_zero_or_pos s.n with h0 | h0
      · have : (1 : ℕ) < Nat.card s.K := Finite.one_lt_card
        rw [s.hK, h0] at this
        norm_num at this
      · exact h0
    have hr : rAV (autSec s.A J ⊥) = 1 / 2 := by
      unfold rAV
      rw [hrk1, hrk2]
      have : (s.n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
      push_cast
      field_simp
    rw [hr] at hle
    have := hbig.trans hle
    have h23 : (2 / 3 : ℚ) ≤ 1 / 2 := by exact_mod_cast this
    norm_num at h23

theorem SL3Split.eq_L (hA21 : AsA21SQTKSection) (hB42 : AsB42) (hA36 : AsA36NoOddCover)
    (hV : ∀ v : V, v ^ 2 = 1) (h : B51Hyp G L) (s : SL3Split G L) : G = L := by
  refine le_antisymm ?_ (le_G h)
  rw [h.2.2.2.2.2]
  exact iSup₂_le fun B hB => s.le_L_of_offender hA21 hB42 hA36 hV h hB

end Equal

end B5

end CFSG.Quasithin
