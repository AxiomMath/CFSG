module

public import CFSG.Milestones.ASVolI.B610.BlkD
public import CFSG.Milestones.ASVolI.B610.BlkC

public section

namespace CFSG.Quasithin.B610T.TwoBlk

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {V H : Subgroup G} (hV : IsElemAbelian 2 V)
  (hHN : H ≤ Subgroup.normalizer (V : Set G))

theorem burnsideB610_exists_mem_twoResidual {Φ : Subgroup (MulAut (IntMod V hV))}
    (hS : B19.Setting (autI hV H) Φ) {t y : MulAut (IntMod V hV)} {w : IntMod V hV}
    (ht : t ∈ B19.tvSet (autI hV H) Φ) (h : B19.TvBlock Φ t y w) :
    ∃ k ∈ twoResidual H, ∃ hk : k ∈ Subgroup.normalizer (V : Set G), convI hV ⟨k, hk⟩ = y := by
  have hW : ∀ w : IntMod V hV, w ^ 2 = 1 := fun w => IntMod.sq_eq_one w
  have hFK : B19.FOf Φ t ≤ autI hV (twoResidual H) :=
    burnsideB610_le_autI_twoResidual hV ((hS.FOf_le hW ht).trans hS.le)
      (by rw [hS.card_FOf hW ht]; decide)
  have hy : y ∈ B19.FOf Φ t := by
    rw [h.FOf_eq]
    exact Subgroup.mem_zpowers y
  obtain ⟨g, hgK, hgy⟩ := (mem_autI hV).1 (hFK hy)
  exact ⟨g, hgK, g.2, hgy⟩

include hHN in
theorem burnsideB610_block_fix {Φ : Subgroup (MulAut (IntMod V hV))}
    (hS : B19.Setting (autI hV H) Φ) {t : MulAut (IntMod V hV)}
    (ht : t ∈ B19.tvSet (autI hV H) Φ) {F : Type} [Field F]
    (D : NatData (preI hV H hHN (B19.GOf Φ t)) V F) :
    fixV (D.img (twoResidual H)) = ⊥ := by
  have hW : ∀ w : IntMod V hV, w ^ 2 = 1 := fun w => IntMod.sq_eq_one w
  have hB : B19.GOf Φ t ∈ burnsideB610_blocks (autI hV H) Φ := ⟨t, ht, rfl⟩
  have hBH := burnsideB610_block_le hW hS hB
  have hinj := burnsideB610_beta_injective D
    (burnsideB610_preI_inf_centralizer hV hHN hBH (burnsideB610_commV_inf_fixV hW hS hB))
  obtain ⟨y, w, h⟩ := hS.exists_tvBlock hW ht
  obtain ⟨k, hkK, hkN, hky⟩ := burnsideB610_exists_mem_twoResidual hV hS ht h
  have hkH : k ∈ H := twoResidual_le H hkK
  have hyG : y ∈ B19.GOf Φ t := by
    rw [h.GOf_eq]
    exact Subgroup.mem_sup_left (Subgroup.mem_zpowers y)
  have hkY : k ∈ Subgroup.normalizer (preI hV H hHN (B19.GOf Φ t) : Set G) := by
    refine burnsideB610_mem_normalizer_preI hV hHN hkH ?_
    rw [show convI hV ⟨k, hHN hkH⟩ = y from hky]
    exact Subgroup.le_normalizer hyG
  have hYN := burnsideB610_preI_le_normalizer hV hHN (B := B19.GOf Φ t)
  refine burnsideB610_fixV_img_eq_bot D hinj hkK ⟨hkY, hkN⟩ fun u hu hku => ?_
  have huV : u ∈ V := Subgroup.le_normalizer_iff_commutator_le_left.mp hYN hu
  have hm := burnsideB610_mk_mem_commV hV hYN hu huV
  rw [autI_preI hV hBH] at hm
  have hym : y (IntMod.mk hV ⟨u, huV⟩) = IntMod.mk hV ⟨u, huV⟩ := by
    apply IntMod.val_injective
    rw [← hky, convI_apply_val]
    exact hku
  have := burnsideB610_eq_one_of_fix hW hS ht h hm hym
  exact congrArg IntMod.val this

theorem burnsideB610_eq_inv_mul_inv {Γ : Type*} [Group Γ] {y : Γ} (hy : y ^ 3 = 1) :
    y = y⁻¹ * y⁻¹ := by
  rw [← mul_inv_rev, eq_inv_iff_mul_eq_one, ← pow_two, ← pow_succ', hy]

include hHN in
theorem burnsideB610_block_gen {Φ : Subgroup (MulAut (IntMod V hV))}
    (hS : B19.Setting (autI hV H) Φ) {t : MulAut (IntMod V hV)}
    (ht : t ∈ B19.tvSet (autI hV H) Φ) {F : Type} [Field F] (hF : Nat.card F ≠ 1)
    (D : NatData (preI hV H hHN (B19.GOf Φ t)) V F) (P : Subgroup G)
    (hPX : P ≤ preI hV H hHN (B19.GOf Φ t)) (hP2 : IsPGroup 2 P)
    (hcard : Nat.card (D.img P) = Nat.card F) :
    ∃ k ∈ preI hV H hHN (B19.GOf Φ t) ⊓ twoResidual H,
      autI hV (preI hV H hHN (B19.GOf Φ t)) ≤ autI hV P ⊔ autI hV (cjSub k P) := by
  have hW : ∀ w : IntMod V hV, w ^ 2 = 1 := fun w => IntMod.sq_eq_one w
  have hBH : B19.GOf Φ t ≤ autI hV H := hS.GOf_le hW ht
  have hYN := burnsideB610_preI_le_normalizer hV hHN (B := B19.GOf Φ t)
  have hPN : P ≤ Subgroup.normalizer (V : Set G) := hPX.trans hYN
  have hPs : autI hV P ≤ B19.GOf Φ t := by
    rw [← autI_preI hV hBH (hA := hHN)]
    exact autI_mono hV hPX
  have hImg : D.img P ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hcard
    exact hF hcard.symm
  have hPne := burnsideB610_autI_ne_bot hV D hYN hPN hImg
  obtain ⟨⟨s, hsP⟩, hs1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hPne
  have hs1' : s ≠ 1 := fun h => hs1 (Subtype.ext h)
  have hP2' : IsPGroup 2 (autI hV P) := B2F.isPGroup_autI hV hP2 hPN
  obtain ⟨y, w, h⟩ := hS.exists_tvBlock hW ht
  have hsG : s ∈ Subgroup.zpowers y ⊔ Subgroup.zpowers t := by
    rw [← h.GOf_eq]
    exact hPs hsP
  have hsq := h.sq hW
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right hsq
  have hodd : Odd (Nat.card (Subgroup.zpowers y)) := by rw [h.card_zpowers]; decide
  rcases B19.mem_or_mul_mem_of_mem_sup hsq (fun f hf => by
      rw [h.inv_zpowers hf]; exact Subgroup.inv_mem _ hf) hsG with h1 | h1
  · exact absurd (B19.eq_one_of_isPGroup_of_odd hP2' hodd hsP h1) hs1'
  ·
    set c := s * t with hc
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 h1
    have hcy : c * y = y * c := by
      rw [← hn]
      exact ((Commute.refl y).zpow_left n).eq
    have hs_eq : s = c * t⁻¹ := by rw [hc]; group
    have hty : t⁻¹ * y * t = y⁻¹ := by
      have := h.inv
      rw [htinv] at this ⊢
      exact this
    have hsy : s * y * s⁻¹ = y⁻¹ := by
      rw [hs_eq]
      calc c * t⁻¹ * y * (c * t⁻¹)⁻¹ = c * (t⁻¹ * y * t) * c⁻¹ := by group
        _ = c * y⁻¹ * c⁻¹ := by rw [hty]
        _ = y⁻¹ := by
          have : c * y⁻¹ = y⁻¹ * c := by
            calc c * y⁻¹ = y⁻¹ * (y * c) * y⁻¹ := by group
              _ = y⁻¹ * (c * y) * y⁻¹ := by rw [hcy]
              _ = y⁻¹ * c := by group
          rw [this]
          group
    have hss : s * s = 1 := by
      have htc : t * c * t⁻¹ = c⁻¹ := h.inv_zpowers h1
      rw [htinv] at htc
      rw [hs_eq, htinv]
      calc c * t * (c * t) = c * (t * c * t) := by group
        _ = 1 := by rw [htc, mul_inv_cancel]
    have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hss
    obtain ⟨k, hkK, hkN, hky⟩ := burnsideB610_exists_mem_twoResidual hV hS ht h
    have hkH : k ∈ H := twoResidual_le H hkK
    have hyG : y ∈ B19.GOf Φ t := by
      rw [h.GOf_eq]
      exact Subgroup.mem_sup_left (Subgroup.mem_zpowers y)
    have hkY : k ∈ preI hV H hHN (B19.GOf Φ t) := by
      refine (mem_preI hV).2 ⟨hkH, ?_⟩
      show convI hV ⟨k, hHN hkH⟩ ∈ B19.GOf Φ t
      rw [show convI hV ⟨k, hHN hkH⟩ = y from hky]
      exact hyG
    refine ⟨k, ⟨hkY, hkK⟩, ?_⟩
    rw [autI_preI hV hBH, ← autI_cjSub hV hkN P, hky, h.GOf_eq]
    set Q := autI hV P ⊔ (autI hV P).map (MulAut.conj y).toMonoidHom with hQ
    have hsQ : s ∈ Q := Subgroup.mem_sup_left hsP
    have hysQ : y * s * y⁻¹ ∈ Q := Subgroup.mem_sup_right ⟨s, hsP, rfl⟩
    have hyQ : y ∈ Q := by
      have hsys : s * y * s = y⁻¹ := by
        have := hsy
        rw [hsinv] at this
        exact this
      have e : y = s * (y * s * y⁻¹) := by
        calc y = y⁻¹ * y⁻¹ := burnsideB610_eq_inv_mul_inv h.x3
          _ = (s * y * s) * y⁻¹ := by rw [hsys]
          _ = s * (y * s * y⁻¹) := by group
      rw [e]
      exact Q.mul_mem hsQ hysQ
    have htQ : t ∈ Q := by
      have hcQ : c ∈ Q := Subgroup.zpowers_le.2 hyQ h1
      have e : t = s⁻¹ * c := by rw [hc]; group
      rw [e]
      exact Q.mul_mem (Q.inv_mem hsQ) hcQ
    exact sup_le (Subgroup.zpowers_le.2 hyQ) (Subgroup.zpowers_le.2 htQ)

theorem burnsideB610_autI_thompsonJ_le_ffJ (hred : IsTwoReducedIn H V) {T : Subgroup G}
    (hT : IsSylowTwoOf T H) : autI hV (thompsonJ T) ≤ ffJ (autI hV H) := by
  refine (autI_mono hV (thompsonJ_le_thompsonJ_of_isSylowTwoOf hT)).trans ?_
  rw [autI_thompsonJ hV hred.2.1]
  exact iSup₂_le fun B hB => iSup_le fun _ =>
    B19.le_ffJ (offenderImages_isFFStarOffender hV hred.1 hred.2.1 hB)

theorem burnsideB610_block_thomp (hred : IsTwoReducedIn H V) {T : Subgroup G}
    (hT : IsSylowTwoOf T H) {Φ : Subgroup (MulAut (IntMod V hV))}
    (hS : B19.Setting (autI hV H) Φ) {t : MulAut (IntMod V hV)}
    (ht : t ∈ B19.tvSet (autI hV H) Φ) :
    thompsonJ T ≤ Subgroup.normalizer (preI hV H hred.2.1 (B19.GOf Φ t) : Set G) := by
  have hW : ∀ w : IntMod V hV, w ^ 2 = 1 := fun w => IntMod.sq_eq_one w
  intro j hj
  have hjH : j ∈ H := hT.1 (B6.thompsonJ_le T hj)
  refine burnsideB610_mem_normalizer_preI hV hred.2.1 hjH ?_
  refine burnsideB610_ffJ_le_normalizer hW hS ht ?_
  exact burnsideB610_autI_thompsonJ_le_ffJ hV hred hT
    (convI_mem_autI hV hj (hred.2.1 hjH))

theorem burnsideB610_res {T M : Subgroup G} (hMP : MinParabolic H T M)
    (hred : IsTwoReducedIn H V) {ι : Type} (S : Finset ι) (X : ι → Subgroup G)
    (hXH : ∀ i ∈ S, X i ≤ H) (hconj : ∀ i ∈ S, ∀ h ∈ H, ∃ j ∈ S, cjSub h (X i) = X j)
    {i₀ : ι} (hi₀ : i₀ ∈ S) (heven : ¬ Odd (Nat.card (autI hV (X i₀)))) :
    twoResidual H ≤ ⨆ i ∈ S, X i := by
  set Y := ⨆ i ∈ S, X i with hY
  have hYH : Y ≤ H := iSup₂_le hXH
  have hYn : H ≤ Subgroup.normalizer (Y : Set G) := by
    intro h hh
    refine B19.mem_normalizer_of_map_conj_le (X := H) (fun g hg => ?_) h hh
    rw [hY, Subgroup.map_iSup]
    refine iSup_le fun i => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun hi => ?_
    obtain ⟨j, hj, hij⟩ := hconj i hi g hg
    have hij' : (X i).map (MulAut.conj g).toMonoidHom = X j := hij
    rw [hij']
    exact le_iSup₂_of_le (f := fun (k : ι) (_ : k ∈ S) => X k) j hj le_rfl
  rcases hMP.le_kerIn_or_twoResidual_le hYH hYn with hYk | hKY
  · exfalso
    apply heven
    refine Odd.of_dvd_nat (E2.odd_card_autI_kerIn hMP hred) (Subgroup.card_dvd_of_le ?_)
    exact autI_mono hV ((le_iSup₂_of_le (f := fun (k : ι) (_ : k ∈ S) => X k) i₀ hi₀
      le_rfl).trans hYk)
  · exact hKY

include hHN in
theorem burnsideB610_block_fix' {Φ : Subgroup (MulAut (IntMod V hV))}
    (hS : B19.Setting (autI hV H) Φ) {B : Subgroup (MulAut (IntMod V hV))}
    (hB : B ∈ burnsideB610_blocks (autI hV H) Φ) {F : Type} [Field F]
    (D : NatData (preI hV H hHN B) V F) : fixV (D.img (twoResidual H)) = ⊥ := by
  obtain ⟨t, ht, rfl⟩ := hB
  exact burnsideB610_block_fix hV hHN hS ht D

include hHN in
theorem burnsideB610_block_gen' {Φ : Subgroup (MulAut (IntMod V hV))}
    (hS : B19.Setting (autI hV H) Φ) {B : Subgroup (MulAut (IntMod V hV))}
    (hB : B ∈ burnsideB610_blocks (autI hV H) Φ) {F : Type} [Field F] (hF : Nat.card F ≠ 1)
    (D : NatData (preI hV H hHN B) V F) (P : Subgroup G) (hPX : P ≤ preI hV H hHN B)
    (hP2 : IsPGroup 2 P) (hcard : Nat.card (D.img P) = Nat.card F) :
    ∃ k ∈ preI hV H hHN B ⊓ twoResidual H,
      autI hV (preI hV H hHN B) ≤ autI hV P ⊔ autI hV (cjSub k P) := by
  obtain ⟨t, ht, rfl⟩ := hB
  exact burnsideB610_block_gen hV hHN hS ht hF D P hPX hP2 hcard

theorem burnsideB610_block_thomp' (hred : IsTwoReducedIn H V) {T : Subgroup G}
    (hT : IsSylowTwoOf T H) {Φ : Subgroup (MulAut (IntMod V hV))}
    (hS : B19.Setting (autI hV H) Φ) {B : Subgroup (MulAut (IntMod V hV))}
    (hB : B ∈ burnsideB610_blocks (autI hV H) Φ) :
    thompsonJ T ≤ Subgroup.normalizer (preI hV H hred.2.1 B : Set G) := by
  obtain ⟨t, ht, rfl⟩ := hB
  exact burnsideB610_block_thomp hV hred hT hS ht

end CFSG.Quasithin.B610T.TwoBlk
