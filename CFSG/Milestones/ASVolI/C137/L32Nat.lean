module

public import CFSG.Milestones.ASVolI.C137.Cases
public import CFSG.Quasithin.H13.GoldschmidtC137L32Core
public import CFSG.Quasithin.H13.GoldschmidtC137L32ZFin
public import CFSG.Quasithin.H13.GoldschmidtC137SQFinal
public import CFSG.Milestones.ASVolI.C135.WMain
public import CFSG.Milestones.ASVolI.C137.Setup
public import CFSG.Quasithin.H13.GoldschmidtC137BaumMain
public import CFSG.Quasithin.H13.GoldschmidtC137L32DE
public import CFSG.Quasithin.H13.GoldschmidtC137L32Lie
public import CFSG.Quasithin.H13.GoldschmidtC137MSd

public section

namespace CFSG.ASVolI

open Subgroup CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Blueprint CFSG.ASVolI.ChC
open CFSG.Quasithin.H13.U3 CFSG.Quasithin.H13.U3.GC137
open scoped Pointwise

variable {G : Type} [Group G]

theorem burnsideC137_zMod_case4W {L W G₀ S : Subgroup G} {u z : G}
    (D : ZFacts L (CFSG.Open.pCoreOf 2 G₀) W u z) (h : burnsideC135_Case4W G₀ S L) :
    ZModData L u z := by
  obtain ⟨⟨n, K, hK, hKin, α, -, hα, -, -, hU⟩, -, -⟩ := h
  exact ⟨⁅centerOf (c134Q G₀ L), L⁆, K, hK, hKin, α, 1, hα, Or.inl rfl, hU, D.hWU D.huW,
    cocycle_mem_commutator_of_perfect D.hLZ (centerOf_comm_gc _) D.hperf D.hcZ⟩

theorem burnsideC137_zMod_of_caseW {L W G₀ S : Subgroup G} {u z : G}
    (D : ZFacts L (CFSG.Open.pCoreOf 2 G₀) W u z) {i : ℕ}
    (hi : MS93.burnsideC134w_CaseWeak i G₀ S L) (hi2 : 2 ≤ i) (hi4 : i ≤ 4) :
    ZModData L u z := by
  rcases hi with ⟨hne, hi⟩ | ⟨rfl, hi⟩
  · obtain rfl | rfl : i = 2 ∨ i = 3 := by omega
    · exact zMod_case2 D hi
    · exact zMod_case3 D hi
  · exact burnsideC137_zMod_case4W D hi

theorem burnsideC137_l32_zcentralW [Finite G] {X T L P W : Subgroup G} {u : G} (h : L32Ctx X T L P W u)
    {S S' : Subgroup G} (hSP : S ≤ P) (hCT : CharTwo (L ⊔ S))
    (hset : ((L ⊔ S : Subgroup G) : Set G) = (L : Set G) * (S : Set G))
    (hS'H : IsSylowTwoOf S' (P ⊓ (L ⊔ S))) (hS'G : IsSylowTwoOf S' (L ⊔ S)) (hSS' : S ≤ S')
    {i : ℕ} (hi : MS93.burnsideC134w_CaseWeak i (L ⊔ S) S L) (hi2 : 2 ≤ i) (hi4 : i ≤ 4)
    {z : G} (hz : z ∈ omegaOneCenterOf S') : ∀ x ∈ P ⊓ (L ⊔ S), x * z = z * x := by
  have hSX : S ≤ X := hSP.trans h.hPX.le
  have hzS : z ∈ centerOf S' := omegaOneCenterOf_le_gc S' hz
  have hNS' : pCoreOf 2 (L ⊔ S) ≤ S' :=
    pCoreOf_two_le_of_sylowIn hS'G.1 hS'G.2.1 hS'G.2.2
  have hzC : ∀ n ∈ pCoreOf 2 (L ⊔ S), n * z = z * n := fun n hn =>
    Subgroup.mem_centralizer_iff.1 hzS.2 n (hNS' hn)
  have hzN : z ∈ pCoreOf 2 (L ⊔ S) :=
    hCT ⟨hS'G.1 hzS.1, Subgroup.mem_centralizer_iff.2 hzC⟩
  have D : ZFacts L (pCoreOf 2 (L ⊔ S)) W u z :=
    ⟨le_sup_left.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (L ⊔ S)),
      isPerfect_of_commutator_eq_gc (perfect_of_mem_cComp h.hL), hzN, hzC,
      h.hWO.trans (h.pCoreOf_le_sup hSX), fun n hn w hw =>
        (Subgroup.mem_centralizer_iff.1 (h.pCoreOf_sup_le_centralizer hSX hn) w hw).symm,
      h.hWL, h.huW⟩
  obtain ⟨M, K', hK', hKin, α, j, hα, hj, hM, huM, hc⟩ := burnsideC137_zMod_of_caseW D hi hi2 hi4
  set K : Subgroup G := L ⊓ centralizer ({u} : Set G) with hKdef
  have hKu : ∀ l ∈ L, l * u = u * l → l ∈ K := fun l hl hlu =>
    ⟨hl, Subgroup.mem_centralizer_iff.2 fun y hy => by
      rw [Set.mem_singleton_iff] at hy
      rw [hy]
      exact hlu.symm⟩
  have hKu' : ∀ k ∈ K, k * u = u * k := fun k hk =>
    (Subgroup.mem_centralizer_iff.1 hk.2 u (Set.mem_singleton u)).symm
  have hKH : K ≤ P ⊓ (L ⊔ S) := fun k hk =>
    ⟨by rw [h.hP]; exact ⟨h.hLX hk.1, hk.2⟩, (le_sup_left : L ≤ L ⊔ S) hk.1⟩
  have conjK : ∀ x ∈ P ⊓ (L ⊔ S), ∀ k ∈ K, x * k * x⁻¹ ∈ K := by
    intro x hx k hk
    have hxn : x ∈ normalizer (L : Set G) := h.hn (h.hPX.le hx.1)
    refine ⟨(Subgroup.mem_normalizer_iff.1 hxn k).1 hk.1,
      Subgroup.mem_centralizer_iff.2 fun y hy => ?_⟩
    rw [Set.mem_singleton_iff] at hy
    subst hy
    have h1 : x⁻¹ * y * x = y := by simpa using h.hpu (P.inv_mem hx.1)
    have h2 : k * y = y * k := hKu' k hk
    calc y * (x * k * x⁻¹) = x * (x⁻¹ * y * x) * k * x⁻¹ := by group
      _ = x * (y * k) * x⁻¹ := by rw [h1, mul_assoc x y k]
      _ = x * (k * y) * x⁻¹ := by rw [h2]
      _ = x * k * x⁻¹ * (x * y * x⁻¹) := by group
      _ = x * k * x⁻¹ * y := by rw [h.hpu hx.1]
  have hnorm : P ⊓ (L ⊔ S) ≤ normalizer (K : Set G) := fun x hx =>
    Subgroup.mem_normalizer_iff.2 fun k => ⟨fun hk => conjK x hx k hk, fun hk => by
      have := conjK x⁻¹ ((P ⊓ (L ⊔ S)).inv_mem hx) _ hk
      simpa [mul_assoc] using this⟩
  have hP' : IsSylowTwoOf (S' ⊓ K) K := A4.isSylowTwoOf_inf_normal hS'H hKH hnorm
  have hzP' : ∀ p ∈ S' ⊓ K, p * z = z * p := fun p hp =>
    Subgroup.mem_centralizer_iff.1 hzS.2 p hp.1
  have hKz := zcentral_of_sum (card_of_psl32 h.lie) hα hj hM huM h.hu1
    (inf_le_left : K ≤ L) hKu hKu' hP' hzP' fun k hk => hc k hk.1
  intro x hx
  have hxLS : x ∈ (L : Set G) * (S : Set G) := by
    rw [← hset]
    exact hx.2
  obtain ⟨l, hl, s, hs, rfl⟩ := hxLS
  have hsu : s * u * s⁻¹ = u := h.hpu (hSP hs)
  have hlu : l * u = u * l := by
    have h1 : l * u * l⁻¹ = u := by
      calc l * u * l⁻¹ = l * (s * u * s⁻¹) * l⁻¹ := by rw [hsu]
        _ = (l * s) * u * (l * s)⁻¹ := by group
        _ = u := h.hpu hx.1
    calc l * u = (l * u * l⁻¹) * l := by group
      _ = u * l := by rw [h1]
  have hlz : l * z = z * l := hKz l (hKu l hl hlu)
  have hsz : s * z = z * s := Subgroup.mem_centralizer_iff.1 hzS.2 s (hSS' hs)
  calc l * s * z = l * (s * z) := by group
    _ = l * (z * s) := by rw [hsz]
    _ = (l * z) * s := by group
    _ = (z * l) * s := by rw [hlz]
    _ = z * (l * s) := by group

variable [Finite G] in
theorem burnsideC137_l32_core_finalW {X T L P W : Subgroup G} {u : G} (hSQ : SQTKGroup ↥X)
    (hL2 : CharTwo L) (h : L32Ctx X T L P W u) (hC134 : MS93.burnsideC134w_AS_C_1_34_corrOneWeak) :
    CharNormal (baum (pCoreOf 2 P)) X ∨ BlockPart L := by
  by_cases hCN : CharNormal (baum (pCoreOf 2 P)) X
  · exact Or.inl hCN
  right
  set R := pCoreOf 2 P with hR
  set S := baum R with hS
  have hn1 : ∀ C : Subgroup G, C ≤ S → C ≠ ⊥ → (C.subgroupOf S).Characteristic →
      ¬ X ≤ normalizer (C : Set G) := fun C hCS hC0 hCc hCn => hCN ⟨C, hCS, hC0, hCc, hCn⟩
  have hM8 : Nat.card (IntMod W h.hWe) = 8 := h.hW8
  obtain ⟨φ⟩ := S153E58.nonempty_mulEquiv_pi_of_sq_eq_one
    (fun m : IntMod W h.hWe => IntMod.sq_eq_one m) (d := 3) (by rw [hM8]; norm_num)
  have hW1 : W ≠ ⊥ := by
    intro hb
    have h8 := h.hW8
    have h1 : Nat.card W = 1 := by rw [hb]; exact Subgroup.card_bot
    omega
  have hVL : ⁅W, L⁆ ≠ ⊥ := by rw [h.hWL]; exact hW1
  obtain ⟨-, -, -, hdich⟩ := C124.B2_10_2 h.hWe h.hred h.hQR h.hRT h.hT h.hLX h.hn h.hprod hVL
    (Or.inl (isQuasisimple_L32 h.lie))
  rcases hdich with hbq | ⟨hst, -⟩
  · exact absurd (charNormal_of_baum_eq (X := X) (R := R) (Q := pCoreOf 2 X)
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X)
      ⟨W, C124.le_pCoreOf_of_reduced h.hred, h.hWe, hW1⟩ hbq) hCN
  obtain ⟨A₀, hA₀, hc⟩ := h.exists_offender_order_two φ hst
  have hRne : autI h.hWe R ≠ ⊥ := by
    intro hb
    have : autI h.hWe A₀ ≤ ⊥ := hb ▸ autI_mono h.hWe hA₀.1
    rw [le_bot_iff] at this
    rw [this, Subgroup.card_bot] at hc
    omega
  have hRv := h.autI_R_eq_v4M φ hRne
  have hJne : autI h.hWe (thompsonJ R) ≠ ⊥ := by
    intro hb
    have : autI h.hWe A₀ ≤ ⊥ := hb ▸ autI_mono h.hWe (le_iSup₂_of_le A₀ hA₀ le_rfl)
    rw [le_bot_iff] at this
    rw [this, Subgroup.card_bot] at hc
    omega
  have hJnorm : ∀ p ∈ P, ∀ y ∈ thompsonJ R, p * y * p⁻¹ ∈ thompsonJ R := by
    intro p hp y hy
    have hpn : p⁻¹ ∈ normalizer (R : Set G) :=
      Subgroup.inv_mem _ (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 P hp)
    have := hy
    rw [← cjSub_thompsonJ hpn, mem_cjSub] at this
    simpa using this
  have hJv := h.autI_eq_v4M_of_normal φ (thompsonJ_le_self R) hJnorm hJne
  have hRS : autI h.hWe R ≤ autI h.hWe S := by
    rw [hRv, ← hJv]
    exact autI_mono h.hWe (B2F.thompsonJ_le_baum R)
  have hRX : R ≤ X := (CFSG.LieType.BorelTits.pCoreOf_le 2 P).trans h.hPX.le
  obtain ⟨hCV, -⟩ := b2_19_rel h.hWe h.hred.1 h.hXN h.hLeq.symm (isPGroup_pCoreOf_two_gc P) hRX
    h.hWR h.hA1 h.hA2 h.hA3 h.hB (h.hC φ) (h.hDE φ hA₀ hc)
  obtain ⟨hMS, hLcomp, hset⟩ := isMSPair_of_baumann hSQ h.hT h.hprod h.hL hL2 h.hn h.hTP h.hPX
    h.hXN (isRankTwoLie2Derived_L32 h.lie) hn1 hCV hRS
  obtain ⟨α, hα⟩ := exists_modO2Surj_L32 h.lie
  obtain ⟨i, hi⟩ := hC134 G (L ⊔ S) S L hMS hLcomp hset
    ⟨ZMod 2, inferInstance, inferInstance, α, by simp, hα⟩
  obtain ⟨hHlt, hHodd, hSeq⟩ := msA_of_baumann h.hT h.hprod h.hL h.hn h.hTP h.hPX h.hXN hCV hRS
  set H' := P ⊓ (L ⊔ S) with hH'
  obtain ⟨S', hS'⟩ := exists_isSylowTwoOf H'
  have hSS' : S ≤ S' :=
    hSeq.le.trans (pCoreOf_two_le_of_sylowIn hS'.1 hS'.2.1 hS'.2.2)
  have hH'G : H' ≤ L ⊔ S := inf_le_right
  have hH'P : H' ≤ P := inf_le_left
  have hS'G : IsSylowTwoOf S' (L ⊔ S) := by
    refine ⟨hS'.1.trans hH'G, hS'.2.1, fun h2 => ?_⟩
    have h1 := Subgroup.relIndex_mul_relIndex S' H' (L ⊔ S) hS'.1 hH'G
    have h3 : 2 ∣ S'.relIndex H' * H'.relIndex (L ⊔ S) := by rw [h1]; exact h2
    rcases (Nat.Prime.dvd_mul Nat.prime_two).1 h3 with h4 | h4
    · exact hS'.2.2 h4
    · exact hHodd h4
  have hLSX : L ⊔ S ≤ X := sup_le h.hLX (((inf_le_left : S ≤ R).trans
    (CFSG.LieType.BorelTits.pCoreOf_le 2 P)).trans h.hPX.le)
  have hWL' : W ≤ L := by
    rw [← h.hWL]
    refine Subgroup.commutator_le.2 fun w hw l hl => ?_
    have h1 : w * l * w⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.1 (h.hn (h.hred.1 hw)) l).1 hl
    have : w * l * w⁻¹ * l⁻¹ ∈ L := L.mul_mem h1 (L.inv_mem hl)
    simpa [commutatorElement_def] using this
  have hWO : W ≤ pCoreOf 2 L :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hWL' (h.hLX.trans h.hXN)
      (B2F.isPGroup_of_isElemAbelian h.hWe)
  have hSnOL : S ≤ normalizer ((pCoreOf 2 L : Subgroup G) : Set G) :=
    (((inf_le_left : S ≤ R).trans (CFSG.LieType.BorelTits.pCoreOf_le 2 P)).trans h.hPX.le).trans
      (h.hn.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L))
  have hOLG : pCoreOf 2 L ≤ pCoreOf 2 (L ⊔ S) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 L).trans le_sup_left)
      (sup_le (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L) hSnOL)
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L)
  have hOGS' : pCoreOf 2 (L ⊔ S) ≤ S' :=
    pCoreOf_two_le_of_sylowIn hS'G.1 hS'G.2.1 hS'G.2.2
  have huS' : u ∈ S' := hOGS' (hOLG (hWO h.huW))
  have huC : u ∈ centralizer (S' : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    have := h.hpu (hH'P (hS'.1 hs))
    calc s * u = (s * u * s⁻¹) * s := by group
      _ = u * s := by rw [this]
  have hu2 : u ^ 2 = 1 := h.hWe.2 u h.huW
  have huΩ : u ∈ omegaOneCenterOf S' :=
    Subgroup.subset_closure ⟨⟨huS', huC⟩, hu2⟩
  have hCT : CharTwo (L ⊔ S) := hMS.1.2.1
  have hSP : S ≤ P := (inf_le_left : S ≤ R).trans (CFSG.LieType.BorelTits.pCoreOf_le 2 P)
  have hZeq : (2 ≤ i ∧ i ≤ 4) →
      S = pCoreOf 2 ((L ⊔ S) ⊓ centralizer (omegaOneCenterOf S' : Set G)) := by
    intro hi24
    have hCH : (L ⊔ S) ⊓ centralizer (omegaOneCenterOf S' : Set G) = H' := by
      apply le_antisymm
      · intro x hx
        have hcu : x ∈ centralizer ({u} : Set G) := by
          rw [Subgroup.mem_centralizer_iff]
          intro z hz
          rw [Set.mem_singleton_iff] at hz
          rw [hz]
          exact Subgroup.mem_centralizer_iff.1 hx.2 u huΩ
        refine ⟨?_, hx.1⟩
        rw [h.hP]
        exact ⟨hLSX hx.1, hcu⟩
      · intro x hx
        have hxc : x ∈ centralizer (omegaOneCenterOf S' : Set G) := by
          rw [Subgroup.mem_centralizer_iff]
          intro z hz
          exact (burnsideC137_l32_zcentralW h hSP hCT hset hS' hS'G hSS' hi hi24.1 hi24.2 hz x hx).symm
        exact ⟨hH'G hx, hxc⟩
    rw [hCH]
    exact hSeq
  rcases hi with ⟨hi4, hi'⟩ | ⟨rfl, hi'⟩
  swap
  · exact absurd (hZeq ⟨by norm_num, by norm_num⟩) (hi'.2.1 S' hS'G hSS')
  rcases i with _ | _ | _ | _ | _ | _ | i
  · exact (hi' : False).elim
  · exact blockPart_of_psl32 h.lie (isLnBlock_of_isSL3Block (card_of_psl32 h.lie) hi'.1)
  · exact absurd (hZeq ⟨by norm_num, by norm_num⟩) (hi'.2 S' hS'G hSS')
  · exact absurd (hZeq ⟨by norm_num, by norm_num⟩) (hi'.2 S' hS'G hSS')
  · exact absurd rfl hi4
  · exfalso
    have hz := (hi'.2 S' hS'G hSS').1 huΩ
    have hcomm : ∀ l ∈ L, l * u = u * l := fun l hl =>
      Subgroup.mem_centralizer_iff.1 hz.2 l ((le_sup_left : L ≤ L ⊔ S) hl)
    have hfix : h.uM ∈ fixV (autI h.hWe L) := by
      intro a ha
      obtain ⟨l, hlL, rfl⟩ := (mem_autI h.hWe).1 ha
      apply IntMod.val_injective
      rw [convI_apply_val]
      show (l : G) * u * (l : G)⁻¹ = u
      rw [hcomm l hlL]
      group
    rw [h.autI_L_top, fixV_top φ, Subgroup.mem_bot] at hfix
    exact h.uM_ne_one hfix
  · exact (hi' : False).elim

section Canonical

set_option linter.unusedSectionVars false

theorem burnsideC137_card_eight
    {L V : Subgroup G}
    {α : ↥L →* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)}
    {β : ↥⁅V, L⁆ →* Multiplicative (Fin 3 → ZMod 2)} (h : IsNatVia L ⁅V, L⁆ ⊥ α β) :
    Nat.card ↥⁅V, L⁆ = 8 := by
  obtain ⟨hs, hk, -⟩ := h
  have hinj : Function.Injective β := by
    rw [← MonoidHom.ker_eq_bot_iff, hk]
    exact Subgroup.bot_subgroupOf _
  rw [Nat.card_congr (Equiv.ofBijective β ⟨hinj, hs⟩)]
  simp [Nat.card_eq_fintype_card]

theorem burnsideC137_caseL32Nat
    : burnsideC137_CaseL32Nat := by
  intro G _ _ X T L P M V hyp hpsl hnat
  obtain ⟨hXLT, hT, hL, hX, -, -, hTP, hPM, hM, hPeq, hred, hVL, -⟩ := hyp
  have hprod := burnsideC137_prod hXLT
  have hL2 := burnsideC137_charTwo_L hL hX
  have hlie : LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 3 2 1 := Or.inl ⟨by decide, hpsl⟩
  obtain ⟨hMX, -⟩ := burnsideC137_max hM
  have hP : P = M := hPeq.resolve_right fun h =>
    not_hatA6_of_psl32 hlie ⟨h.1.1.1, h.1.2.1, h.1.2.2⟩
  obtain ⟨⟨α, β, -, -, hβ⟩, u, huW, hu1, hPu⟩ := hnat
  have h8 := burnsideC137_card_eight hβ
  have hSQ : SQTKGroup ↥X := c137SQTKSupply_holds G X T L hX hT hprod hL hL2 (Or.inl hlie)
  have hn := C124.le_normalizer_of_prod hT hprod hL
  obtain ⟨-, -, -, hWL, hred'⟩ := l32_reduce hL hlie hn hred h8
  have ctx : L32Ctx X T L P ⁅V, L⁆ u :=
    ⟨hT, hprod, hL, hlie, hTP, lt_of_le_of_lt hPM hMX, hred', hWL, h8, huW, hu1, hPu⟩
  rcases burnsideC137_l32_core_finalW hSQ hL2 ctx MS93.burnsideC134w_corrOneWeak with
    ⟨C, hC1, hC0, hCc, hCn⟩ | hb
  · exact Or.inl ⟨C, hC0, hC1, hCc, hCn⟩
  · refine Or.inr (Or.inl ⟨Or.inl (hb.1 hlie), fun hH => ?_⟩)
    exact (not_hatA6_of_psl32 hlie ⟨hH.2.1.1.1, hH.2.1.2.1, hH.2.1.2.2⟩).elim

end Canonical

end CFSG.ASVolI
