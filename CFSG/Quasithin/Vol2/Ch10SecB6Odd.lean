module

public import CFSG.Quasithin.Vol2.Ch10SecCBasic
public import CFSG.Quasithin.Vol2.Ch10SecA1012Two
public import CFSG.Quasithin.Background.B2FactorizationR2
public import CFSG.Quasithin.Vol2.Ch10SecBSetup
public import CFSG.Quasithin.Vol2.Ch10StatementsB
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

theorem fsuVM_le_T1 (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (hyp : Hyp10 G T L I) : fsuVM T L I ≤ T1 T L := by
  have hV := SecA.isElemAbelian_fsuVM hyp
  refine (le_inf (SecA.fsuVM_le_T hyp) fun v hv => Subgroup.mem_centralizer_iff.mpr
    fun w hw => B2F.isElemAbelian_comm hV hw hv).trans (SecA.inf_centralizer_le_T1 h37 h38 hyp)

theorem pCoreOf_fsuM_le_T1 (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (h1011 : Stmt10_1_1) (hyp : Hyp10 G T L I) : pCoreOf 2 (fsuM T L) ≤ T1 T L := by
  obtain ⟨hVM, hR, -, -⟩ := h1011 G T L I hyp
  have hC := SecC.pCoreOf_le_centralizer_of_subnormal hR hVM (IsSubnormal.refl (fsuM T L))
  have hT : IsSylowTwoOf T (fsuM T L) :=
    isSylowTwoOf_of_quasithinIsSylowTwo hyp.fsu.sylow (le_fsuM T L)
  exact (le_inf (CFSG.Quasithin.pCoreOf_le_of_isSylowTwoOf hT) hC).trans
    (SecA.inf_centralizer_le_T1 h37 h38 hyp)

theorem fsuL0_perfect' (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (hyp : Hyp10 G T L I) : ⁅fsuL0 T L, fsuL0 T L⁆ = fsuL0 T L := by
  obtain ⟨t, ht, htn⟩ := Set.not_subset.mp hyp.not_normal
  have hL := SecA.perfect_L hyp.fsu.maximal.1
  have hLt : ⁅CFSG.conjugate L t, CFSG.conjugate L t⁆ = CFSG.conjugate L t := by
    rw [SecA.conjugate_eq_map, ← Subgroup.map_commutator, hL]
  rw [SecA.fsuL0_eq_sup h37 h38 hyp ht htn]
  refine le_antisymm (Subgroup.commutator_le.mpr fun a ha b hb => ?_) ?_
  · rw [commutatorElement_def]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ ha hb)
      (Subgroup.inv_mem _ ha)) (Subgroup.inv_mem _ hb)
  · have e : L ⊔ CFSG.conjugate L t =
        ⁅L, L⁆ ⊔ ⁅CFSG.conjugate L t, CFSG.conjugate L t⁆ := by rw [hL, hLt]
    calc L ⊔ CFSG.conjugate L t = ⁅L, L⁆ ⊔ ⁅CFSG.conjugate L t, CFSG.conjugate L t⁆ := e
      _ ≤ _ := sup_le (Subgroup.commutator_mono le_sup_left le_sup_left)
        (Subgroup.commutator_mono le_sup_right le_sup_right)

theorem inf_eq_bot_of_two_odd {A B : Subgroup G} (hA : IsPGroup 2 A) (hB : Odd (Nat.card B)) :
    A ⊓ B = ⊥ := by
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (hA.to_le inf_le_left : IsPGroup 2 ↥(A ⊓ B))
  have h2 := Subgroup.card_dvd_of_le (inf_le_right : A ⊓ B ≤ B)
  rw [hn] at h2
  rcases n with _ | n
  · rw [pow_zero] at hn
    exact Subgroup.card_eq_one.mp hn
  · exfalso
    have h3 : 2 ∣ Nat.card B := (dvd_pow_self 2 (Nat.succ_ne_zero n)).trans h2
    exact (Nat.not_even_iff_odd.mpr hB) (even_iff_two_dvd.mpr h3)

theorem odd_card_oddCoreOf (H : Subgroup G) : Odd (Nat.card (A37.oddCoreOf H)) := by
  rw [A37.oddCoreOf, Subgroup.card_map_of_injective H.subtype_injective]
  exact CFSG.ABGLocalTools.odd_card_oddCore

omit [Finite G] in
theorem le_normalizer_oddCoreOf' (H : Subgroup G) :
    H ≤ Subgroup.normalizer (A37.oddCoreOf H : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    exact A37.conj_mem_oddCoreOf (Subgroup.le_normalizer hg) hx
  · intro hx
    have := A37.conj_mem_oddCoreOf (Subgroup.le_normalizer (H.inv_mem hg)) hx
    simpa [mul_assoc] using this

theorem charTwo_fsuM (hyp : Hyp10 G T L I) : CharTwo (fsuM T L) := by
  obtain ⟨S, hS⟩ := CFSG.Quasithin.exists_sylow_of_quasithinIsSylowTwo hyp.fsu.sylow
  exact charTwo_of_inH hyp.fsu.qtke.2.1 S
    ⟨hS ▸ le_fsuM T L, SecA.pCoreOf_fsuM_ne_bot hyp.fsu.faithful⟩

theorem oddCoreOf_eq_bot (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (h331 : Stmt3_3_1) (h1011 : Stmt10_1_1) (hyp : Hyp10 G T L I) {H : Subgroup G}
    (hH : InM (fsuL0 T L ⊔ T1 T L) H) : A37.oddCoreOf H = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hH2 : pCoreOf 2 H ≠ ⊥ := (inH_of_inM hH).2
  have hV := SecA.isElemAbelian_fsuVM hyp
  have hL0H : fsuL0 T L ≤ H := le_sup_left.trans hH.2
  have hT1H : T1 T L ≤ H := le_sup_right.trans hH.2
  have hVT1 := fsuVM_le_T1 h37 h38 hyp
  have hVO : fsuVM T L I ≤ Subgroup.centralizer (fusionOddCoreOf H : Set G) :=
    a126_one hL0H (C2Nine.opResidual_eq_of_perfect (fsuL0_perfect' h37 h38 hyp))
      (hVT1.trans hT1H) (SecA.isPGroup_fsuVM hyp) (SecA.fsuVM_eq_commutator hyp.fsu).symm
      (fun p hp hp2 => (CFSG.SectionRank.pRank_mono hp.one_lt
        (CFSG.LieType.BorelTits.pCoreOf_le p H)).trans
          (pRank_le_two_of_pCoreOf_ne_bot hyp.fsu.qtke hH2 hp hp2))
      (C2Nine.frattiniIn_eq_bot_of_isElemAbelian hV)
  have hOV : A37.oddCoreOf H ≤ Subgroup.centralizer (fsuVM T L I : Set G) :=
    Subgroup.le_centralizer_iff.mp hVO
  have hNV := SecA.normalizer_fsuVM_eq hyp (fsuM_isMaxTwoLocal h331 hyp)
  have hOM : A37.oddCoreOf H ≤ fsuM T L :=
    hOV.trans ((Subgroup.centralizer_le_normalizer _).trans hNV.le)
  have hPM := pCoreOf_fsuM_le_T1 h37 h38 h1011 hyp
  have h1 : ⁅pCoreOf 2 (fsuM T L), A37.oddCoreOf H⁆ ≤ pCoreOf 2 (fsuM T L) :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp
      (hOM.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _))
  have h2 : ⁅pCoreOf 2 (fsuM T L), A37.oddCoreOf H⁆ ≤ A37.oddCoreOf H := by
    rw [Subgroup.commutator_comm]
    exact Subgroup.le_normalizer_iff_commutator_le_left.mp
      ((hPM.trans hT1H).trans (le_normalizer_oddCoreOf' H))
  have hinf : pCoreOf 2 (fsuM T L) ⊓ A37.oddCoreOf H = ⊥ :=
    inf_eq_bot_of_two_odd (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _) (odd_card_oddCoreOf H)
  have hc : ⁅pCoreOf 2 (fsuM T L), A37.oddCoreOf H⁆ = ⊥ := le_bot_iff.mp (hinf ▸ le_inf h1 h2)
  have hOC : A37.oddCoreOf H ≤ Subgroup.centralizer (pCoreOf 2 (fsuM T L) : Set G) :=
    Subgroup.le_centralizer_iff.mp
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hc)
  have hO2 : A37.oddCoreOf H ≤ pCoreOf 2 (fsuM T L) :=
    fun x hx => charTwo_fsuM hyp ⟨hOM hx, hOC hx⟩
  exact le_bot_iff.mp (hinf ▸ le_inf hO2 le_rfl)

end CFSG.Quasithin.Vol2.Ch10.SecB
