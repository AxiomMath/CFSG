module

import CFSG.RankThree.PartTwo.Sec21.Item221ProofCover
public import CFSG.RankThree.PartTwo.Sec21.HeringSec217OutJ
public import CFSG.RankThree.PartTwo.Sec21.HeringSec217OutSteps

public section

namespace CFSG.AGLEmbeddingD2.Wilson.NormalizerAction

open Subgroup CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec21 CFSG.Blueprint
open scoped commutatorElement

section Second

variable {G : Type} [Group G] [Finite G] {A E U : Subgroup G} {c : G} {L : Subgroup G}


set_option linter.unusedSectionVars false

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem CoverOut.decomp_F (h45 : Sec4.Item4_5) (h : CoverOut A E U c L) {a : G}
    (hfr : Frame217 E c L a) :
    ∀ f ∈ A ⊓ L, ∃ d ∈ dGroup a c ⊓ L, ∃ y ∈ iCore L a, f = d * y := by
  obtain ⟨l, I', hlA, ⟨i, hai⟩, hl1, hl3, hlnc, hI'C, hI'perf, ⟨φ⟩, hI, hI'max, hD3, hDI,
    hDcomm, hCeq, hDeq, hDL⟩ := h.local_frame h45 hfr
  have hab := isElemAbelian_iff.1 h.isElemAbelian_A
  rintro f ⟨hfA, hfL⟩
  have hfl : (⟨f, hfL⟩ : ↥L) * l = l * ⟨f, hfL⟩ := Subtype.ext (hab.1 f hfA l hlA)
  have hmem : (⟨f, hfL⟩ : ↥L) ∈ Subgroup.zpowers l ⊔ I' := by
    rw [hCeq]; exact Subgroup.mem_centralizer_singleton_iff.2 hfl
  obtain ⟨x, hx, y, hy, hxy⟩ := (mem_sup_of_commute
    (fun x hx y hy => hDcomm x hx y (hI'C hy))).1 hmem
  refine ⟨(x : G), ?_, (y : G), ?_, ?_⟩
  · rw [hDL]
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hx
    exact Subgroup.mem_zpowers_iff.2 ⟨k, by rw [← hk]; simp⟩
  · rw [hI]; exact ⟨y, hy, rfl⟩
  · exact (congrArg Subtype.val hxy).symm

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem CoverOut.exists_U0 (h45 : Sec4.Item4_5) (h : CoverOut A E U c L) {a : G}
    (hfr : Frame217 E c L a) :
    ∃ U₀ ∈ fourGroupsMinus E, U₀ ≤ iCore L a ∧
      ∀ b ∈ E ⊓ Subgroup.centralizer (U₀ : Set G), b ∈ Subgroup.zpowers a ⊔ Subgroup.zpowers c := by
  obtain ⟨⟨eI⟩, hIA, hIcen, hIcomm, hcardAI, hAC⟩ := h.iCore_structure h45 hfr
  obtain ⟨l, hlA, ⟨i₀, hai⟩, hl1, hl3, hlnc, hDeq, hDL, hDA, hDE⟩ := h.dgroup_decomp h45 hfr
  have hEA : E ≤ A := h.pair.mem_E.2
  have hcE : c ∈ E := (mem_lThreeStarPairs_iff.mp h.pair.mem_pair).1.1
  have hE27 : Nat.card E = 27 := h.pair.mem_E.1.2.1
  have hab := isElemAbelian_iff.1 h.isElemAbelian_A
  have hD9 := h.card_dGroup h45 hfr
  set D : Subgroup G := dGroup a c with hD
  set I : Subgroup G := iCore L a with hI
  have hDI : D ≤ Subgroup.centralizer (I : Set G) := by rw [← hAC]; exact inf_le_right
  have hcommDI : ∀ x ∈ D, ∀ y ∈ I, x * y = y * x := fun x hx y hy =>
    (Subgroup.mem_centralizer_iff.1 (hDI hx) y hy).symm
  obtain ⟨e₀, he₀, he₀D⟩ : ∃ e₀ ∈ E, e₀ ∉ D := by
    by_contra hno
    push Not at hno
    have : Nat.card E ≤ Nat.card D := Subgroup.card_le_of_le (fun x hx => hno x hx)
    omega
  obtain ⟨f, hf, k, hfk⟩ := h.decomp_A h45 e₀ (hEA he₀)
  have hfE : f ∈ E := by
    have : f = e₀ * (c ^ k)⁻¹ := by rw [hfk]; group
    rw [this]
    exact E.mul_mem he₀ (E.inv_mem (Subgroup.zpow_mem _ hcE k))
  obtain ⟨d', hd', y, hy, hdy⟩ := h.decomp_F h45 hfr f hf
  have hyE : y ∈ E := by
    have : y = d'⁻¹ * f := by rw [hdy]; group
    rw [this]
    exact E.mul_mem (E.inv_mem (hDE hd'.1)) hfE
  have hyD : y ∉ D := by
    intro hyD
    apply he₀D
    rw [hfk, hdy]
    exact D.mul_mem (D.mul_mem hd'.1 hyD) (Subgroup.zpow_mem _ (Subgroup.mem_sup_right
      (Subgroup.mem_zpowers c)) k)
  have hy1 : y ≠ 1 := fun h1 => hyD (h1 ▸ D.one_mem)
  have hy3 : y ^ 3 = 1 := hab.2 y (hEA hyE)
  have hord : orderOf y = 3 := orderOf_eq_prime hy3 hy1
  have hdisj : Disjoint D (Subgroup.zpowers y) := by
    rw [Subgroup.disjoint_def]
    intro x hxD hxi
    rcases mem_zpowers_of_pow_three hy3 hxi with h1 | h1 | h1
    · exact h1
    · exact absurd (h1 ▸ hxD) hyD
    · exfalso
      apply hyD
      have : y = (y ^ 2) ^ 2 := by
        have : (y ^ 2) ^ 2 = y ^ 3 * y := by group
        rw [this, hy3, one_mul]
      rw [this]
      exact pow_mem (h1 ▸ hxD) 2
  have hsup27 : 27 ≤ Nat.card ↥(D ⊔ Subgroup.zpowers y) := by
    have := card_mul_le_card_sup_of_disjoint D (Subgroup.zpowers y) hdisj
    rw [hD9, Nat.card_zpowers, hord] at this
    omega
  have hDyE : D ⊔ Subgroup.zpowers y ≤ E := sup_le hDE (Subgroup.zpowers_le.2 hyE)
  have hEeq : E = D ⊔ Subgroup.zpowers y :=
    (Subgroup.eq_of_le_of_card_ge hDyE (by rw [hE27]; exact hsup27)).symm
  obtain ⟨u, v, huI, hvI, huv, huu, hvv, hyu, hyv, hu1, hv1, hne⟩ :=
    exists_V4_data I eI hy hy3 hy1
  obtain ⟨W, hWeq, -, hW2, hWcomm, hWN⟩ := V4_aux y u v hy3 huv huu hvv hyu hyv hu1
  have hWcard : Nat.card W = 4 :=
    hWeq ▸ card_closure_pair_of_involutions u v huv huu hvv hu1 hv1 hne
  have hWI : W ≤ I := by
    rw [hWeq, Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact huI
    · exact hvI
  have hDW : D ≤ Subgroup.normalizer (W : Set G) := by
    refine le_trans ?_ (Subgroup.centralizer_le_normalizer (W : Set G))
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    exact (hcommDI x hx w (hWI hw)).symm
  have hEW : E ≤ Subgroup.normalizer (W : Set G) := by
    rw [hEeq]
    exact sup_le hDW (Subgroup.zpowers_le.2 hWN)
  have hWel : CFSG.Assembly.IsElemAbelian 2 W := by
    rw [isElemAbelian_iff]
    exact ⟨hWcomm, hW2⟩
  have hWfour : W ∈ fourGroups E := mem_fourGroups_iff.2 ⟨hEW, hWel, hWcard⟩
  have huW : u ∈ W := by rw [hWeq]; exact Subgroup.subset_closure (Or.inl rfl)
  have hvW : v ∈ W := by rw [hWeq]; exact Subgroup.subset_closure (Or.inr rfl)
  have hWcomm' : W = ⁅W, E⁆ := by
    apply le_antisymm
    · have hcm := comm_V4 y u v huu hvv hyu hyv
      have hu : u ∈ ⁅W, E⁆ := by
        rw [← hcm.1]; exact Subgroup.commutator_mem_commutator hvW hyE
      have huv' : u * v ∈ ⁅W, E⁆ := by
        rw [← hcm.2]; exact Subgroup.commutator_mem_commutator huW hyE
      have hv : v ∈ ⁅W, E⁆ := by
        have := mul_mem (inv_mem hu) huv'
        simpa using this
      intro x hx
      rw [hWeq] at hx
      induction hx using Subgroup.closure_induction with
      | mem z hz => rcases hz with rfl | rfl <;> assumption
      | one => exact one_mem _
      | mul a b _ _ ha hb => exact mul_mem ha hb
      | inv a _ ha => exact inv_mem ha
    · refine Subgroup.commutator_le.2 fun x hx z hz => ?_
      have hzN := Subgroup.mem_normalizer_iff.1 (hEW hz) x⁻¹
      have h2 : z * x⁻¹ * z⁻¹ ∈ W := hzN.1 (inv_mem hx)
      have : ⁅x, z⁆ = x * (z * x⁻¹ * z⁻¹) := by rw [commutatorElement_def]; group
      rw [this]
      exact mul_mem hx h2
  refine ⟨W, ⟨hWfour, hWcomm'⟩, hWI, ?_⟩
  intro b hb
  obtain ⟨hbE, hbC⟩ := hb
  have hbE' := hbE
  rw [hEeq] at hbE'
  have hDy : ∀ x ∈ D, ∀ z ∈ Subgroup.zpowers y, x * z = z * x := by
    intro x hx z hz
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
    exact ((show Commute x y from hcommDI x hx y hy).zpow_right j).eq
  obtain ⟨d'', hd'', z, hz, hdz⟩ := (mem_sup_of_commute hDy).1 hbE'
  have hbu : u * b = b * u := Subgroup.mem_centralizer_iff.1 hbC u huW
  have hd''u : d'' * u = u * d'' := hcommDI d'' hd'' u huI
  have hzu : u * z = z * u := by
    have h1 : d'' * (u * z) = d'' * (z * u) := by
      calc d'' * (u * z) = (d'' * u) * z := by rw [mul_assoc]
        _ = (u * d'') * z := by rw [hd''u]
        _ = u * (d'' * z) := by rw [mul_assoc]
        _ = u * b := by rw [hdz]
        _ = b * u := hbu
        _ = d'' * z * u := by rw [hdz]
        _ = d'' * (z * u) := by rw [mul_assoc]
    exact mul_left_cancel h1
  have hz1 : z = 1 := by
    rcases mem_zpowers_of_pow_three hy3 hz with h1 | h1 | h1
    · exact h1
    · exfalso
      rw [h1] at hzu
      apply hne
      have : y * u * y⁻¹ = u := by rw [← hzu]; group
      rw [hyu] at this
      exact this.symm
    · exfalso
      rw [h1] at hzu
      apply hv1
      have hzu' : u * (y * y) = (y * y) * u := by rw [← sq]; exact hzu
      have e1 : (y * y) * u * (y * y)⁻¹ = u := by rw [← hzu']; group
      have e2 : (y * y) * u * (y * y)⁻¹ = u * v := by
        have : (y * y) * u * (y * y)⁻¹ = y * (y * u * y⁻¹) * y⁻¹ := by group
        rw [this, hyu, hyv]
      rw [e1] at e2
      exact (mul_eq_left.1 e2.symm)
  rw [hz1, mul_one] at hdz
  rw [← hdz]
  exact hd''

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem CoverOut.frame_of_mem_D (h45 : Sec4.Item4_5) (h : CoverOut A E U c L) {a : G}
    (hfr : Frame217 E c L a) {b : G} (hbE : b ∈ E) (hbD : b ∈ dGroup a c)
    (hbc : b ∉ Subgroup.zpowers c) : Frame217 E c L b ∧ iCore L b = iCore L a := by
  obtain ⟨l, hlA, ⟨i, hai⟩, hl1, hl3, hlnc, hDeq, hDL, hDA, hDE⟩ := h.dgroup_decomp h45 hfr
  have hab := isElemAbelian_iff.1 h.isElemAbelian_A
  have hcomm' : ∀ x ∈ Subgroup.zpowers (l : G), ∀ y ∈ Subgroup.zpowers c, x * y = y * x := by
    intro x hx y hy
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    exact ((show Commute (l : G) c from hab.1 _ hlA c h.c_mem_A).zpow_zpow j k).eq
  rw [hDeq] at hbD
  obtain ⟨x, hx, y, hy, hxy⟩ := (mem_sup_of_commute hcomm').1 hbD
  have hx1 : x ≠ 1 := by
    intro hx1
    apply hbc
    rw [← hxy, hx1, one_mul]
    exact hy
  have hxL : x ∈ L := by
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    exact L.zpow_mem l.2 j
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
  have hl3L : l ^ 3 = 1 := Subtype.ext hl3
  have hxz : (⟨x, hxL⟩ : ↥L) ∈ Subgroup.zpowers l := by
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 hx
    exact Subgroup.mem_zpowers_iff.2 ⟨j, Subtype.ext (by rw [Subgroup.coe_zpow]; exact hj)⟩
  have hx1L : (⟨x, hxL⟩ : ↥L) ≠ 1 := fun h1 => hx1 (congrArg Subtype.val h1)
  have hlx : l ∈ Subgroup.zpowers (⟨x, hxL⟩ : ↥L) := mem_zpowers_of_mem_zpowers hl3L hx1L hxz
  have hb : b = ((⟨x, hxL⟩ : ↥L) : G) * c ^ k := hxy.symm
  refine ⟨⟨hbE, hbc, ⟨⟨x, hxL⟩, ⟨c ^ k, ?_, hb⟩, ?_⟩⟩, ?_⟩
  · rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact ((show Commute c z from h.c_comm z hz).zpow_left k).eq.symm
  · rcases mem_zpowers_of_pow_three hl3L hxz with h1 | h1 | h1
    · exact absurd h1 hx1L
    · rw [h1]; exact hlnc
    · have hlq3 : (l : ↥L ⧸ center ↥L) ^ 3 = 1 := by
        rw [← QuotientGroup.mk_pow, hl3L]; rfl
      rw [h1, QuotientGroup.mk_pow]
      exact nonCentral_sq hlq3 hlnc
  · have h1 := h.centralizer_inf_eq (l := l) (i := i) (a := a) hai
    have h2 := h.centralizer_inf_eq (l := ⟨x, hxL⟩) (i := k) (a := b) hb
    have hcent : Subgroup.centralizer ({(⟨x, hxL⟩ : ↥L)} : Set ↥L) =
        Subgroup.centralizer ({l} : Set ↥L) :=
      centralizer_singleton_eq_of_mem_zpowers hxz hlx
    unfold iCore
    rw [h2, h1, hcent]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem CoverOut.K_type (h : CoverOut A E U c L) (h211 : Item211) (h213 : Item213)
    (h214 : Item214Unitary) (h2116 : Item2116At217Out)
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    {a : G} (hfr : Frame217 E c L a) {U₀ K : Subgroup G} (hU₀ : U₀ ∈ fourGroupsMinus E)
    (hpair : (a, K) ∈ lThreeStarPairs A E U₀) (hU₀K : U₀ ≤ K) :
    (Nonempty (lBar K ≃* NativeSporadic.J3) ∨ Sec4.IsTripleCover (lBar K) NativeSporadic.J3) ∧
      Sec4.IsExtOf ↥(starOf A K) (Multiplicative (ZMod 8)) (Multiplicative (ZMod 3 × ZMod 3)) := by
  have hp : Sec21Pair G A E U₀ a K :=
    { h.pair.toSec21Std with
      mem_E := h.pair.mem_E
      mem_U := fourGroupsMinus_subset E hU₀
      mem_pair := hpair }
  have hcase := h211 G A E U₀ a K hp
  have hA := h.card
  have h116 := h2116 G A E U c L h.pair h.quot h.notMem h.card h.ext a hfr U₀ hU₀ K hpair
  unfold Case211 at hcase
  have h34 : Nat.card A = 3 ^ 3 → False := fun hA3 => by
    rw [hA3] at hA; norm_num at hA
  rcases hcase with ⟨-, -, hA3, -⟩ | ⟨-, hA3, -⟩ | ⟨-, hA3, -⟩ | ⟨-, hA3, -⟩ | ⟨-, hA3, -⟩ |
    ⟨-, hA3, -⟩ | ⟨-, hA3, -⟩ | ⟨-, hA3, -⟩ | ⟨-, hA3, -⟩ | ⟨h10, -, -⟩ | ⟨h11, -, hext⟩ |
    ⟨-, hA3, -⟩ | ⟨h13, -, -⟩
  · exact (h34 hA3).elim
  · exact (h34 hA3).elim
  · exact (h34 hA3).elim
  · exact (h34 hA3).elim
  · exact (h34 hA3).elim
  · exact (h34 hA3).elim
  · exact (h34 hA3).elim
  · exact (h34 hA3).elim
  · exact (h34 hA3).elim
  · exfalso
    obtain ⟨n, hn, hno, ⟨e⟩⟩ := h10
    have : IsSimpleGroup (Assembly.RankThreeEven.projSU 4 2 n) :=
      isSimpleGroup_projSU le_rfl (by omega)
    have hq := h213 G A E U₀ a K hp
    have hKe : Nonempty (↥K ≃* Assembly.RankThreeEven.projSU 4 2 n) :=
      Item221Proof.nonempty_mulEquiv_of_center_eq_bot hq e fun e' =>
        Item223PrintProof.center_eq_bot_of_quotient_projSU_four hGA hq.1 (by omega) e'
    exact h214 G A E U₀ a K hp ⟨n, hno, hKe⟩ ⟨U₀, hU₀, hU₀K⟩
  · exact ⟨h11, hext⟩
  · exact (h34 hA3).elim
  · exact absurd (Or.inr (Or.inr h13)) h116

end Second

section SecondMain


set_option linter.unusedSectionVars false

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem sec217OutSecond_of (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8) (h211 : Item211)
    (h212 : Item212) (h213 : Item213) (h214 : Item214Unitary) (h215 : Item215)
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels) : Sec217OutSecond := by
  intro G _ _ A E U c L h
  have h2116 : Item2116At217Out := item2116At217Out_of h212 (sec217OutNoFix_holds h45)
  obtain ⟨a₀, hfr₀⟩ := sec217OutFrame_of h45 G A E U c L h
  obtain ⟨U₀, hU₀, hU₀I, hCE⟩ := h.exists_U0 h45 hfr₀
  obtain ⟨b, hb, hbc, K, hK, hpair⟩ := h215 G A E U c L h.pair U₀ hU₀
  obtain ⟨hfrb, hIb⟩ := h.frame_of_mem_D h45 hfr₀ hb.1 (hCE b hb) hbc
  obtain ⟨K', hK', hIK'⟩ := h.exists_component_ge_iCore h48 h45 hfrb
  have hU₀b : U₀ ≤ iCore L b := hIb ▸ hU₀I
  have hKK' : K = K' :=
    eq_of_commutator_eq_of_le hK.2 hK' (hU₀b.trans hIK') hpair.2.2.2.2.2.1
  subst hKK'
  obtain ⟨htype, hext⟩ :=
    h.K_type h211 h213 h214 h2116 hGA hfrb hU₀ hpair (hU₀b.trans hIK')
  have hp : Sec21Pair G A E U₀ b K :=
    { h.pair.toSec21Std with
      mem_E := h.pair.mem_E
      mem_U := fourGroupsMinus_subset E hU₀
      mem_pair := hpair }
  exact ⟨b, U₀, K, ⟨h, hfrb, hU₀, hU₀b, hK, hpair, htype, hext, hIK', h213 G A E U₀ b K hp⟩⟩

end SecondMain

end CFSG.AGLEmbeddingD2.Wilson.NormalizerAction
