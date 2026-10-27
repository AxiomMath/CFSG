module

public import CFSG.RankThree.PartTwo.Sec17.Item174Host
import CFSG.RankThree.PartTwo.Sec6.Item612Plus
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.RankThree.PartTwo.Sec16.Item167StepsProof
import CFSG.RankThree.GF2n.Tim78Normal
import CFSG.GH74.GLS.Stage2.Signalizer.Odd87GrpCoreA
import CFSG.CGT.PushingUp.TwoLocals
import CFSG.GroupTheory.PCore.OpenTransport
import CFSG.RankThree.PartTwo.Sec17.Item1712StepsProofSeven

public section

namespace CFSG.RankThree.PartTwo.Sec17.Proof174Host

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15 CFSG.RankThree.PartTwo.Sec16
  CFSG.RankThree.PartTwo.Sec17 CFSG.RankThree.PartTwo.Late CFSG.RankThree.LocalRank CFSG.GH74.GLS
  CFSG.RankThree.PartTwo.Sec16.Proof165
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem not_three_dvd_card_of_isPGroup_two {W : Subgroup G} (hW : IsPGroup 2 W) :
    ¬ 3 ∣ Nat.card W := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := hW.exists_card_eq
  rw [hk]
  exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp
    (Nat.Coprime.pow_right k (by norm_num))

theorem le_pCoreOf_two_of_mem_scriptQ {A : Subgroup G} {LB : Subgroup G → Subgroup G}
    {Ŷ W R : Subgroup G} (hŶ : Ŷ ∈ scriptY1Star A LB) (hW2 : IsPGroup 2 W)
    (hŶW : Ŷ ≤ Subgroup.normalizer (W : Set G)) (htop : Ŷ ⊔ W ≠ ⊤)
    (hR : R ∈ scriptQ A LB) (hRW : R ≤ W) : R ≤ CFSG.Open.pCoreOf 2 Ŷ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_cases hR1 : R = ⊥
  · rw [hR1]
    exact bot_le
  obtain ⟨⟨⟨⟨-, hAŶ⟩, -⟩, hŶΔ⟩, hŶo⟩ := hŶ.prop
  have hŶ3 : ¬ 3 ∣ Nat.card Ŷ := not_three_dvd_of_oPrimeResidualOf_eq_bot hŶo
  have hAR : A ≤ Subgroup.normalizer (R : Set G) := (mem_scriptQ_iff.mp hR).2.1
  set Y := Ŷ ⊔ R with hYdef
  have hYW : Y ≤ Ŷ ⊔ W := sup_le_sup_left hRW Ŷ
  have hYnW : Y ≤ Subgroup.normalizer (W : Set G) :=
    sup_le hŶW (hRW.trans Subgroup.le_normalizer)
  have hYnWY : Y ≤ Subgroup.normalizer ((W ⊓ Y : Subgroup G) : Set G) :=
    le_normalizer_inf hYnW Subgroup.le_normalizer
  have hRle : R ≤ CFSG.Open.pCoreOf 2 Y :=
    (le_inf hRW le_sup_right).trans
      (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right hYnWY
        (hW2.to_le inf_le_left))
  have hY3 : ¬ 3 ∣ Nat.card Y := fun h3 =>
    Sec6.not_dvd_card_sup Nat.prime_three hŶW hŶ3 (not_three_dvd_card_of_isPGroup_two hW2)
      (h3.trans (Subgroup.card_dvd_of_le hYW))
  have hmem : Y ∈ scriptY1 A LB := by
    refine ⟨⟨⟨⟨fun h => htop (top_le_iff.mp (h ▸ hYW)), le_normalizer_sup hAŶ hAR⟩, ?_⟩, ?_⟩,
      oPrimeResidualOf_three_eq_bot_of_not_dvd hY3⟩
    · intro h0
      exact hR1 (le_bot_iff.mp (h0 ▸ hRle))
    · exact le_antisymm (sup_le (hŶΔ.le.trans (delta_mono le_sup_left)) (le_delta hR le_sup_right))
        (delta_le _)
  have hYŶ : Y ≤ Ŷ := hŶ.2 hmem le_sup_left
  exact (le_inf hRW (le_sup_right.trans hYŶ)).trans
    (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right
      (le_normalizer_inf hŶW Subgroup.le_normalizer) (hW2.to_le inf_le_left))

theorem normalizer_y0_ne_top {A : Subgroup G} {c : G} {L Y₀ : Subgroup G}
    (h : Sec17Std G A c L Y₀) : Subgroup.normalizer (Y₀ : Set G) ≠ ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨⟨hY₀Y, -, -, -⟩, hY₀2⟩ := h.mem_y0Star.prop
  have hY₀1 : Y₀ ≠ ⊥ := fun h0 => hY₀2.2 (by
    rw [eq_bot_iff, ← h0]
    exact CFSG.LieType.BorelTits.pCoreOf_le 2 Y₀)
  have : IsSimpleGroup G := h.isSimpleGroup
  intro htop
  rcases (Subgroup.normalizer_eq_top_iff.mp htop).eq_bot_or_eq_top with h0 | h1
  · exact hY₀1 h0
  · exact hY₀Y.1 h1

theorem commute_y0_of_odd {A : Subgroup G} {c : G} {L Y₀ : Subgroup G} (h : Sec17Std G A c L Y₀)
    (hQ : CFSG.Open.pCoreOf 2 Y₀ ∈ scriptQ A (lB A))
    (hF : generalizedFitting ↥Y₀ = CFSG.pCore 2 ↥Y₀) {Ŷ : Subgroup G}
    (hŶ : Ŷ ∈ scriptY1Star A (lB A)) (hŶM : Ŷ ≤ Subgroup.normalizer (Y₀ : Set G)) {y : G}
    (hyM : y ∈ Subgroup.normalizer (Y₀ : Set G)) (hodd : Odd (orderOf y))
    (hyB : ∀ b ∈ CFSG.Open.pCoreOf 2 Ŷ, y * b = b * y) : ∀ g ∈ Y₀, y * g = g * y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M := Subgroup.normalizer (Y₀ : Set G) with hMdef
  set Q := CFSG.Open.pCoreOf 2 Y₀ with hQdef
  set B := CFSG.Open.pCoreOf 2 Ŷ with hBdef
  have hQ2 : IsPGroup 2 Q := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y₀
  have hB2 : IsPGroup 2 B := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Ŷ
  have hMQ : M ≤ Subgroup.normalizer (Q : Set G) :=
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y₀
  have hBM : B ≤ M := (CFSG.LieType.BorelTits.pCoreOf_le 2 Ŷ).trans hŶM
  have hAQ : A ≤ Subgroup.normalizer (Q : Set G) := (mem_scriptQ_iff.mp hQ).2.1
  have hAŶ : A ≤ Subgroup.normalizer (Ŷ : Set G) := hŶ.prop.1.1.1.2
  have hAB : A ≤ Subgroup.normalizer (B : Set G) :=
    hAŶ.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Ŷ)
  set V := Q ⊓ Subgroup.centralizer (B : Set G) with hVdef
  have hVQ : V ∈ scriptQ A (lB A) :=
    mem_scriptQ_of_le hQ inf_le_left
      (le_normalizer_inf hAQ (Sec16.le_normalizer_centralizer_of_le_normalizer hAB))
  have hVB : V ≤ B :=
    le_pCoreOf_two_of_mem_scriptQ hŶ hQ2 (hŶM.trans hMQ)
      (fun htop => normalizer_y0_ne_top h (top_le_iff.mp
        (htop ▸ sup_le hŶM ((CFSG.LieType.BorelTits.pCoreOf_le 2 Y₀).trans
          Subgroup.le_normalizer))))
      hVQ inf_le_left
  have hfix : ∀ q ∈ Q, (∀ b ∈ B, q * b = b * q) → y * q = q * y := fun q hq hqB =>
    hyB q (hVB ⟨hq, Subgroup.mem_centralizer_iff.mpr fun b hb => (hqB b hb).symm⟩)
  have hyQc := CFSG.RankThree.GF2n.Tim78.commute_of_thompson_A_times_B hQ2 hB2 (hMQ hyM)
    (hBM.trans hMQ) hodd hyB hfix
  exact commute_of_odd_of_commute_pCoreOf hF hyM hodd hyQc

theorem mem_normalizer_of_conj_mem {H : Subgroup G} {g : G} (h1 : ∀ x ∈ H, g * x * g⁻¹ ∈ H)
    (h2 : ∀ x ∈ H, g⁻¹ * x * g ∈ H) : g ∈ Subgroup.normalizer (H : Set G) :=
  Subgroup.mem_normalizer_iff.mpr fun x =>
    ⟨h1 x, fun hx => by simpa [mul_assoc] using h2 _ hx⟩

theorem le_normalizer_commutator {X H K : Subgroup G} (hH : X ≤ Subgroup.normalizer (H : Set G))
    (hK : X ≤ Subgroup.normalizer (K : Set G)) :
    X ≤ Subgroup.normalizer ((⁅H, K⁆ : Subgroup G) : Set G) := by
  have key : ∀ g : G, g ∈ Subgroup.normalizer (H : Set G) → g ∈ Subgroup.normalizer (K : Set G) →
      ∀ x ∈ ⁅H, K⁆, g * x * g⁻¹ ∈ ⁅H, K⁆ := by
    intro g hgH hgK
    have hle : ⁅H, K⁆ ≤ ⁅H, K⁆.comap (MulAut.conj g).toMonoidHom := by
      rw [Subgroup.commutator_le]
      intro a ha b hb
      rw [Subgroup.mem_comap]
      have e : (MulAut.conj g).toMonoidHom ⁅a, b⁆ = ⁅g * a * g⁻¹, g * b * g⁻¹⁆ := by
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, commutatorElement_def]
        group
      rw [e]
      exact Subgroup.commutator_mem_commutator ((Subgroup.mem_normalizer_iff.mp hgH a).mp ha)
        ((Subgroup.mem_normalizer_iff.mp hgK b).mp hb)
    intro x hx
    simpa using hle hx
  intro g hg
  refine mem_normalizer_of_conj_mem (key g (hH hg) (hK hg)) fun x hx => ?_
  simpa using key g⁻¹ (inv_mem (hH hg)) (inv_mem (hK hg)) x hx

theorem le_normalizer_normalClosureIn (M : Subgroup G) (c : G) :
    M ≤ Subgroup.normalizer (normalClosureIn M c : Set G) := by
  have key : ∀ m ∈ M, ∀ x ∈ normalClosureIn M c, m * x * m⁻¹ ∈ normalClosureIn M c := by
    intro m hm x hx
    unfold normalClosureIn at hx ⊢
    induction hx using Subgroup.closure_induction with
    | mem a ha =>
      obtain ⟨n, hn, rfl⟩ := ha
      exact Subgroup.subset_closure ⟨m * n, mul_mem hm hn, by group⟩
    | one => simp
    | mul a b _ _ iha ihb =>
      have e : m * (a * b) * m⁻¹ = (m * a * m⁻¹) * (m * b * m⁻¹) := by group
      rw [e]
      exact mul_mem iha ihb
    | inv a _ iha =>
      have e : m * a⁻¹ * m⁻¹ = (m * a * m⁻¹)⁻¹ := by group
      rw [e]
      exact inv_mem iha
  intro m hm
  refine mem_normalizer_of_conj_mem (key m hm) fun x hx => ?_
  simpa using key m⁻¹ (inv_mem hm) x hx

theorem sup_zpowers_eq_of_isHyperplane' {A B : Subgroup G} (hB : IsHyperplane A B) {u : G}
    (huA : u ∈ A) (huB : u ∉ B) : B ⊔ Subgroup.zpowers u = A := by
  have hle : B ⊔ Subgroup.zpowers u ≤ A := sup_le hB.1 (Subgroup.zpowers_le.mpr huA)
  obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le (le_sup_left : B ≤ B ⊔ Subgroup.zpowers u)
  have h2 := Subgroup.card_dvd_of_le hle
  rw [hk, hB.2, mul_comm 3] at h2
  have hpos : 0 < Nat.card B := Nat.card_pos
  have hk3 : k ∣ 3 := Nat.dvd_of_mul_dvd_mul_left hpos h2
  rcases (Nat.dvd_prime Nat.prime_three).mp hk3 with rfl | rfl
  · exfalso
    rw [mul_one] at hk
    have heq := Subgroup.eq_of_le_of_card_ge (le_sup_left : B ≤ B ⊔ Subgroup.zpowers u) hk.le
    have hu : u ∈ B ⊔ Subgroup.zpowers u := Subgroup.mem_sup_right (Subgroup.mem_zpowers u)
    rw [← heq] at hu
    exact huB hu
  · refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [hk, hB.2, mul_comm]

theorem centralizer_inf_le_of_isHyperplane {A B B' : Subgroup G} (hB : IsHyperplane A B)
    (hB' : IsHyperplane A B') (hne : B' ≠ B) :
    Subgroup.centralizer (B : Set G) ⊓ Subgroup.centralizer (B' : Set G) ≤
      Subgroup.centralizer (A : Set G) := by
  obtain ⟨g, hgB', hgB⟩ : ∃ g ∈ B', g ∉ B := by
    by_contra hcon
    push Not at hcon
    apply hne
    refine Subgroup.eq_of_le_of_card_ge (fun g hg => hcon g hg) ?_
    have h1 := hB.2
    have h2 := hB'.2
    omega
  have hA : B ⊔ B' = A :=
    le_antisymm (sup_le hB.1 hB'.1) ((sup_zpowers_eq_of_isHyperplane' hB (hB'.1 hgB') hgB).symm.le.trans
      (sup_le_sup_left (Subgroup.zpowers_le.mpr hgB') B))
  intro x hx
  have : B ⊔ B' ≤ Subgroup.centralizer ({x} : Set G) := by
    refine sup_le (fun b hb => ?_) (fun b hb => ?_)
    · rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff.mp hy]
      exact (Subgroup.mem_centralizer_iff.mp hx.1 b hb).symm
    · rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff.mp hy]
      exact (Subgroup.mem_centralizer_iff.mp hx.2 b hb).symm
  rw [hA] at this
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  have := Subgroup.mem_centralizer_iff.mp (this ha) x rfl
  exact this.symm

theorem normalizer_le_normalizer_w (Y₀ : Subgroup G) :
    Subgroup.normalizer (Y₀ : Set G) ≤
      Subgroup.normalizer
        (CFSG.Open.pCoreOf 2 (Subgroup.centralizer (Y₀ : Set G)) : Set G) :=
  (Sec16.le_normalizer_centralizer_of_le_normalizer le_rfl).trans
    (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _)

theorem le_centralizer_normalClosureIn {E : Subgroup G} {c : G}
    (hc : c ∈ Subgroup.centralizer (E : Set G)) :
    normalClosureIn (Subgroup.centralizer (E : Set G)) c ≤ Subgroup.centralizer (E : Set G) := by
  refine (Subgroup.closure_le _).mpr ?_
  rintro _ ⟨m, hm, rfl⟩
  exact mul_mem (mul_mem hm hc) (inv_mem hm)

theorem mem_scriptQ_of_commutator_le {A : Subgroup G} {c : G} {L Y₀ : Subgroup G}
    (h : Sec17Std G A c L Y₀) (hE : IsHyperplane A (A ⊓ L)) (hcL : c ∉ L) {R : Subgroup G}
    (hRW : R ≤ CFSG.Open.pCoreOf 2 (Subgroup.centralizer (Y₀ : Set G)))
    (hAR : A ≤ Subgroup.normalizer (R : Set G))
    (hRc : ⁅R, Subgroup.zpowers c⁆ ≤
      pPrimeCoreOf 3 (normalClosureIn (Subgroup.centralizer ((A ⊓ L : Subgroup G) : Set G)) c)) :
    R ∈ scriptQ A (lB A) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set E : Subgroup G := A ⊓ L with hEdef
  set W := CFSG.Open.pCoreOf 2 (Subgroup.centralizer (Y₀ : Set G)) with hWdef
  set X := normalClosureIn (Subgroup.centralizer (E : Set G)) c with hXdef
  have hA : IsE27 A := h.toSec14Std.isE27
  have hcA : c ∈ A := h.mem_A
  have hcE : c ∉ E := fun hc => hcL hc.2
  have hAE : E ⊔ Subgroup.zpowers c = A := sup_zpowers_eq_of_isHyperplane' hE hcA hcE
  have hW2 : IsPGroup 2 W := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  have hWC : W ≤ Subgroup.centralizer (E : Set G) :=
    (CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans
      (Subgroup.centralizer_le (inf_le_right.trans h.le_y0))
  have hRE : R ≤ Subgroup.centralizer (E : Set G) := hRW.trans hWC
  have hR2 : IsPGroup 2 R := hW2.to_le hRW
  have hR3 : ¬ 3 ∣ Nat.card R := not_three_dvd_card_of_isPGroup_two hR2
  have hCAW : Subgroup.centralizer (A : Set G) ≤ Subgroup.normalizer (W : Set G) :=
    ((Subgroup.centralizer_le_normalizer (A : Set G)).trans h.normalizer_le).trans
      (normalizer_le_normalizer_w Y₀)
  have hWA : W ⊓ Subgroup.centralizer (A : Set G) ≤
      pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) :=
    le_pPrimeCoreOf inf_le_right (le_normalizer_inf hCAW Subgroup.le_normalizer)
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr
        (not_three_dvd_card_of_isPGroup_two (hW2.to_le inf_le_left)))
  have hcCE : c ∈ Subgroup.centralizer (E : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun e he => h.commute he.1 hcA
  have hXCE : X ≤ Subgroup.centralizer (E : Set G) := le_centralizer_normalClosureIn hcCE
  have hCEX : Subgroup.centralizer (E : Set G) ≤ Subgroup.normalizer (X : Set G) :=
    le_normalizer_normalClosureIn _ c
  have hKE : pPrimeCoreOf 3 X ≤ pPrimeCoreOf 3 (Subgroup.centralizer (E : Set G)) :=
    le_pPrimeCoreOf ((pPrimeCoreOf_le 3 X).trans hXCE)
      (hCEX.trans (normalizer_le_normalizer_pPrimeCoreOf 3 X)) (coprime_card_pPrimeCoreOf 3 X)
  have hcR : Subgroup.zpowers c ≤ Subgroup.normalizer (R : Set G) :=
    (Subgroup.zpowers_le.mpr hcA).trans hAR
  have hRsol : Group.IsSolvable ↥R := by
    haveI := hR2.isNilpotent
    infer_instance
  have hcop : Nat.Coprime (Nat.card (Subgroup.zpowers c)) (Nat.card R) := by
    obtain ⟨k, hk⟩ := hR2.exists_card_eq
    obtain ⟨l, hl⟩ := (hA.isPGroup.to_le (Subgroup.zpowers_le.mpr hcA)).exists_card_eq
    rw [hk, hl]
    exact Nat.Coprime.pow l k (by norm_num)
  have hdec := CFSG.GH74.GLS.Stage2.Signalizer.Odd87.CoreA.le_commutator_sup_inf_centralizer
    hcR hRsol hcop
  have hRcA : R ⊓ Subgroup.centralizer (Subgroup.zpowers c : Set G) ≤
      W ⊓ Subgroup.centralizer (A : Set G) := by
    refine le_inf (inf_le_left.trans hRW) ?_
    rw [Subgroup.le_centralizer_iff, ← hAE]
    refine sup_le ?_ ?_
    · rw [← Subgroup.le_centralizer_iff]
      exact inf_le_left.trans hRE
    · rw [← Subgroup.le_centralizer_iff]
      exact inf_le_right
  have hRle : R ≤ pPrimeCoreOf 3 (Subgroup.centralizer (E : Set G)) ⊔
      pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) :=
    hdec.trans (sup_le_sup (hRc.trans hKE) (hRcA.trans hWA))
  refine mem_scriptQ_iff.mpr ⟨(isPiSubgroup_piCompl_iff Nat.prime_three R).mpr hR3, hAR, ?_⟩
  intro B hB
  by_cases hBE : B = E
  · subst hBE
    exact inf_le_left.trans (hRle.trans le_sup_left)
  · have hRB : R ⊓ Subgroup.centralizer (B : Set G) ≤ Subgroup.centralizer (A : Set G) :=
      (le_inf inf_le_right (inf_le_left.trans hRE)).trans
        (centralizer_inf_le_of_isHyperplane hB hE (Ne.symm hBE))
    exact (le_inf (inf_le_left.trans hRW) hRB).trans (hWA.trans (le_sup_right.trans le_sup_left))

theorem commutator_mem_scriptQ {A : Subgroup G} {c : G} {L Y₀ : Subgroup G}
    (h : Sec17Std G A c L Y₀) (hE : IsHyperplane A (A ⊓ L)) (hcL : c ∉ L) {Y : Subgroup G}
    (hYA : Y ≤ Subgroup.centralizer (A : Set G)) (hAY : A ≤ Subgroup.normalizer (Y : Set G))
    (hYX : ⁅Y, normalClosureIn (Subgroup.centralizer ((A ⊓ L : Subgroup G) : Set G)) c⁆ ≤
      pPrimeCoreOf 3 (normalClosureIn (Subgroup.centralizer ((A ⊓ L : Subgroup G) : Set G)) c)) :
    ⁅CFSG.Open.pCoreOf 2 (Subgroup.centralizer (Y₀ : Set G)), Y⁆ ∈ scriptQ A (lB A) := by
  set E : Subgroup G := A ⊓ L with hEdef
  set W := CFSG.Open.pCoreOf 2 (Subgroup.centralizer (Y₀ : Set G)) with hWdef
  set X := normalClosureIn (Subgroup.centralizer (E : Set G)) c with hXdef
  set K := pPrimeCoreOf 3 X with hKdef
  have hcA : c ∈ A := h.mem_A
  have hM : Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (W : Set G) :=
    h.normalizer_le.trans (normalizer_le_normalizer_w Y₀)
  have hcCE : c ∈ Subgroup.centralizer (E : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun e he => h.commute he.1 hcA
  have hCEK : Subgroup.centralizer (E : Set G) ≤ Subgroup.normalizer (K : Set G) :=
    (le_normalizer_normalClosureIn _ c).trans
      (normalizer_le_normalizer_pPrimeCoreOf 3 X)
  have hCAE : Subgroup.centralizer (A : Set G) ≤ Subgroup.centralizer (E : Set G) :=
    Subgroup.centralizer_le inf_le_left
  have hWC : W ≤ Subgroup.centralizer (E : Set G) :=
    (CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans
      (Subgroup.centralizer_le (inf_le_right.trans h.le_y0))
  have hYW : Y ≤ Subgroup.normalizer (W : Set G) :=
    hYA.trans ((Subgroup.centralizer_le_normalizer (A : Set G)).trans hM)
  have hcW : Subgroup.zpowers c ≤ Subgroup.normalizer (W : Set G) :=
    (Subgroup.zpowers_le.mpr hcA).trans (Subgroup.le_normalizer.trans hM)
  have hcK : Subgroup.zpowers c ≤ Subgroup.normalizer (K : Set G) :=
    (Subgroup.zpowers_le.mpr hcCE).trans hCEK
  have h3 : ⁅⁅W, Y⁆, Subgroup.zpowers c⁆ ≤ W ⊓ K := by
    refine Sec6.three_subgroups_mod (le_normalizer_inf hYW (hYA.trans (hCAE.trans hCEK)))
      (le_normalizer_inf hcW hcK)
      (le_normalizer_inf Subgroup.le_normalizer (hWC.trans hCEK)) ?_ ?_
    · have hYc : ⁅Y, Subgroup.zpowers c⁆ = ⊥ :=
        (Subgroup.commutator_eq_bot_iff_le_centralizer).mpr
          (hYA.trans (Subgroup.centralizer_le (Subgroup.zpowers_le.mpr hcA)))
      rw [hYc, Subgroup.commutator_bot_left]
      exact bot_le
    · have hcWX : ⁅Subgroup.zpowers c, W⁆ ≤ W ⊓ X := by
        refine le_inf (Subgroup.le_normalizer_iff_commutator_le_right.mp hcW) ?_
        rw [Subgroup.commutator_le]
        intro g hg w hw
        have hcX : c ∈ X := by
          rw [hXdef, normalClosureIn]
          exact Subgroup.subset_closure ⟨1, one_mem _, by simp⟩
        have hgX : g ∈ X := (Subgroup.zpowers_le.mpr hcX) hg
        have hwX : w * g⁻¹ * w⁻¹ ∈ X :=
          (Subgroup.mem_normalizer_iff.mp (le_normalizer_normalClosureIn _ c (hWC hw))
            _).mp (inv_mem hgX)
        rw [commutatorElement_def]
        have := mul_mem hgX hwX
        rwa [show g * (w * g⁻¹ * w⁻¹) = g * w * g⁻¹ * w⁻¹ by group] at this
      refine (Subgroup.commutator_mono hcWX le_rfl).trans (le_inf ?_ ?_)
      · exact (Subgroup.commutator_mono inf_le_left le_rfl).trans
          (Subgroup.le_normalizer_iff_commutator_le_left.mp hYW)
      · rw [Subgroup.commutator_comm]
        exact (Subgroup.commutator_mono le_rfl inf_le_right).trans hYX
  exact mem_scriptQ_of_commutator_le h hE hcL
    (Subgroup.le_normalizer_iff_commutator_le_left.mp hYW)
    (le_normalizer_commutator (Subgroup.le_normalizer.trans hM) hAY) (h3.trans inf_le_right)

theorem commute_of_mem_pCoreOf_of_ne {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (hpq : p ≠ q)
    (Y : Subgroup G) {x y : G} (hx : x ∈ CFSG.Open.pCoreOf p Y)
    (hy : y ∈ CFSG.Open.pCoreOf q Y) : x * y = y * x := by
  have hxY := CFSG.LieType.BorelTits.pCoreOf_le p Y hx
  have hyY := CFSG.LieType.BorelTits.pCoreOf_le q Y hy
  have h1 : x * y * x⁻¹ * y⁻¹ ∈ CFSG.Open.pCoreOf p Y := by
    have : y * x⁻¹ * y⁻¹ ∈ CFSG.Open.pCoreOf p Y :=
      (Subgroup.mem_normalizer_iff.mp (CFSG.LieType.BorelTits.le_normalizer_pCoreOf p Y hyY)
        _).mp (inv_mem hx)
    simpa [mul_assoc] using mul_mem hx this
  have h2 : x * y * x⁻¹ * y⁻¹ ∈ CFSG.Open.pCoreOf q Y :=
    mul_mem ((Subgroup.mem_normalizer_iff.mp
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf q Y hxY) _).mp hy) (inv_mem hy)
  have h3 : x * y * x⁻¹ * y⁻¹ = 1 :=
    Subgroup.disjoint_def.mp (IsPGroup.disjoint_of_ne p q hpq _ _
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup p Y)
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup q Y)) h1 h2
  calc x * y = (x * y * x⁻¹ * y⁻¹) * (y * x) := by group
    _ = y * x := by rw [h3, one_mul]

theorem odd_orderOf_of_mem_pCoreOf {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {Y : Subgroup G} {z : G}
    (hz : z ∈ CFSG.Open.pCoreOf p Y) : Odd (orderOf z) := by
  obtain ⟨k, hk⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup p Y ⟨z, hz⟩
  have hk' : z ^ (p ^ k) = 1 := by simpa using congrArg Subtype.val hk
  exact Odd.of_dvd_nat ((Nat.Prime.odd_of_ne_two Fact.out hp2).pow) (orderOf_dvd_of_pow_eq_one hk')

theorem mem_pCoreOf_of_isCharacteristicP {H : Subgroup G} (hH : IsCharacteristicP 2 ↥H) {g : G}
    (hg : g ∈ H) (hgW : ∀ w ∈ CFSG.Open.pCoreOf 2 H, g * w = w * g) :
    g ∈ CFSG.Open.pCoreOf 2 H := by
  rw [CFSG.openPCoreOf_eq_map_pCore] at hgW ⊢
  refine ⟨⟨g, hg⟩, hH (Subgroup.mem_centralizer_iff.mpr fun w hw => ?_), rfl⟩
  exact Subtype.ext (hgW (w : G) ⟨w, hw, rfl⟩).symm

theorem isCharacteristicP_normalizer_y0 {A : Subgroup G} {c : G} {L Y₀ : Subgroup G}
    (h : Sec17Std G A c L Y₀) : IsCharacteristicP 2 ↥(Subgroup.normalizer (Y₀ : Set G)) := by
  have hM : Subgroup.normalizer (Y₀ : Set G) ∈
      CFSG.maximalTwoLocalsContaining ((Y₀ ⊔ A : Subgroup G) : Set G) := by
    rw [h.scriptM_eq]
    exact Set.mem_singleton _
  exact CFSG.CGT.PushingUp.isCharacteristicP_of_isPLocal h.toTheoremFourHyp.charTwoType hM.1.1

theorem isCharacteristicP_centralizer_y0 {A : Subgroup G} {c : G} {L Y₀ : Subgroup G}
    (h : Sec17Std G A c L Y₀) : IsCharacteristicP 2 ↥(Subgroup.centralizer (Y₀ : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact Sec15.isCharacteristicP_of_le_normalizer (Subgroup.centralizer_le_normalizer _)
    (Sec16.le_normalizer_centralizer_of_le_normalizer le_rfl) (isCharacteristicP_normalizer_y0 h)

@[expose] def trivialOn (X K : Subgroup G) : Subgroup G where
  carrier := {g | g ∈ Subgroup.normalizer (X : Set G) ∧ g ∈ Subgroup.normalizer (K : Set G) ∧
    ∀ x ∈ X, g * x * g⁻¹ * x⁻¹ ∈ K}
  one_mem' := ⟨one_mem _, one_mem _, fun x _ => by simp [one_mem]⟩
  mul_mem' := by
    rintro g k ⟨hgX, hgK, hg⟩ ⟨hkX, hkK, hk⟩
    refine ⟨mul_mem hgX hkX, mul_mem hgK hkK, fun x hx => ?_⟩
    have e : g * k * x * (g * k)⁻¹ * x⁻¹ =
        g * (k * x * k⁻¹ * x⁻¹) * g⁻¹ * (g * x * g⁻¹ * x⁻¹) := by group
    rw [e]
    exact mul_mem ((Subgroup.mem_normalizer_iff.mp hgK _).mp (hk x hx)) (hg x hx)
  inv_mem' := by
    rintro g ⟨hgX, hgK, hg⟩
    refine ⟨inv_mem hgX, inv_mem hgK, fun x hx => ?_⟩
    have h1 := (Subgroup.mem_normalizer_iff.mp (inv_mem hgK) _).mp (hg x hx)
    have e : g⁻¹ * x * g⁻¹⁻¹ * x⁻¹ = (g⁻¹ * (g * x * g⁻¹ * x⁻¹) * g⁻¹⁻¹)⁻¹ := by group
    rw [e]
    exact inv_mem h1

theorem mem_trivialOn {X K : Subgroup G} {g : G} :
    g ∈ trivialOn X K ↔ g ∈ Subgroup.normalizer (X : Set G) ∧
      g ∈ Subgroup.normalizer (K : Set G) ∧ ∀ x ∈ X, g * x * g⁻¹ * x⁻¹ ∈ K :=
  Iff.rfl

theorem eq_bot_of_le_pCoreOf_of_commute {A : Subgroup G} {c : G} {L Y₀ : Subgroup G}
    (h : Sec17Std G A c L Y₀) (hQ : CFSG.Open.pCoreOf 2 Y₀ ∈ scriptQ A (lB A))
    (hF : generalizedFitting ↥Y₀ = CFSG.pCore 2 ↥Y₀) {Ŷ : Subgroup G}
    (hŶ : Ŷ ∈ scriptY1Star A (lB A)) (hŶM : Ŷ ≤ Subgroup.normalizer (Y₀ : Set G)) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {Z : Subgroup G} (hZ : Z ≤ CFSG.Open.pCoreOf p Ŷ)
    (hZW : ∀ z ∈ Z, ∀ w ∈ CFSG.Open.pCoreOf 2 (Subgroup.centralizer (Y₀ : Set G)),
      z * w = w * z) : Z = ⊥ := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZp : IsPGroup p Z := (CFSG.LieType.BorelTits.pCoreOf_isPGroup p Ŷ).to_le hZ
  have hW2 : IsPGroup 2 (CFSG.Open.pCoreOf 2 (Subgroup.centralizer (Y₀ : Set G))) :=
    CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  have hZŶ : Z ≤ Ŷ := hZ.trans (CFSG.LieType.BorelTits.pCoreOf_le p Ŷ)
  have hZW' : Z ≤ CFSG.Open.pCoreOf 2 (Subgroup.centralizer (Y₀ : Set G)) := by
    intro z hz
    have hzC : z ∈ Subgroup.centralizer (Y₀ : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      exact (commute_y0_of_odd h hQ hF hŶ hŶM (hŶM (hZŶ hz)) (odd_orderOf_of_mem_pCoreOf hp2 (hZ hz))
        (fun b hb => commute_of_mem_pCoreOf_of_ne hp2 Ŷ (hZ hz) hb) g hg).symm
    exact mem_pCoreOf_of_isCharacteristicP (isCharacteristicP_centralizer_y0 h) hzC (hZW z hz)
  exact (IsPGroup.disjoint_of_ne p 2 hp2 Z _ hZp hW2).eq_bot_of_le hZW'

theorem eq_bot_of_le_pCoreOf_of_trivial {A : Subgroup G} {c : G} {L Y₀ : Subgroup G}
    (h : Sec17Std G A c L Y₀) (hE : IsHyperplane A (A ⊓ L)) (hcL : c ∉ L)
    (hQ : CFSG.Open.pCoreOf 2 Y₀ ∈ scriptQ A (lB A))
    (hF : generalizedFitting ↥Y₀ = CFSG.pCore 2 ↥Y₀) {Ŷ : Subgroup G}
    (hŶ : Ŷ ∈ scriptY1Star A (lB A)) (hŶM : Ŷ ≤ Subgroup.normalizer (Y₀ : Set G)) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {Z : Subgroup G} (hZ : Z ≤ CFSG.Open.pCoreOf p Ŷ)
    (hZA : Z ≤ Subgroup.centralizer (A : Set G))
    (hZX : ⁅Z, normalClosureIn (Subgroup.centralizer ((A ⊓ L : Subgroup G) : Set G)) c⁆ ≤
      pPrimeCoreOf 3 (normalClosureIn (Subgroup.centralizer ((A ⊓ L : Subgroup G) : Set G)) c)) :
    Z = ⊥ := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set W := CFSG.Open.pCoreOf 2 (Subgroup.centralizer (Y₀ : Set G)) with hWdef
  set B := CFSG.Open.pCoreOf 2 Ŷ with hBdef
  have hZp : IsPGroup p Z := (CFSG.LieType.BorelTits.pCoreOf_isPGroup p Ŷ).to_le hZ
  have hW2 : IsPGroup 2 W := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  have hŶW : Ŷ ≤ Subgroup.normalizer (W : Set G) := hŶM.trans (normalizer_le_normalizer_w Y₀)
  have hZW : Z ≤ Subgroup.normalizer (W : Set G) :=
    (hZ.trans (CFSG.LieType.BorelTits.pCoreOf_le p Ŷ)).trans hŶW
  have hWM : W ≤ Subgroup.normalizer (Y₀ : Set G) :=
    (CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans (Subgroup.centralizer_le_normalizer _)
  have htop : Ŷ ⊔ W ≠ ⊤ := fun ht =>
    normalizer_y0_ne_top h (top_le_iff.mp (ht ▸ sup_le hŶM hWM))
  have hAZ : A ≤ Subgroup.normalizer (Z : Set G) :=
    (Subgroup.le_centralizer_iff.mp hZA).trans (Subgroup.centralizer_le_normalizer _)
  have hWZB : ⁅W, Z⁆ ≤ B :=
    le_pCoreOf_two_of_mem_scriptQ hŶ hW2 hŶW htop (commutator_mem_scriptQ h hE hcL hZA hAZ hZX)
      (Subgroup.le_normalizer_iff_commutator_le_left.mp hZW)
  have h1 : ⁅⁅W, Z⁆, Z⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact commute_of_mem_pCoreOf_of_ne hp2 Ŷ (hZ hz) (hWZB hx)
  have hpW : ¬ p ∣ Nat.card W := by
    obtain ⟨k, hk⟩ := hW2.exists_card_eq
    rw [hk]
    intro hd
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hd))
  have hWZ : ⁅W, Z⁆ = ⊥ :=
    (CFSG.RankThreeEvenClassification.Helpers.coprime_commutator_idempotent p hp Z W hZp hpW
      hZW).symm.trans h1
  refine eq_bot_of_le_pCoreOf_of_commute h hQ hF hŶ hŶM hp hp2 hZ fun z hz w hw => ?_
  exact (Subgroup.mem_centralizer_iff.mp
    (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hWZ hw)) z hz

theorem eq_one_of_le_y0 {A : Subgroup G} {c : G} {L Y₀ : Subgroup G} (h : Sec17Std G A c L Y₀)
    (hQ : CFSG.Open.pCoreOf 2 Y₀ ∈ scriptQ A (lB A)) (hAY : A ≤ Y₀) {Ŷ : Subgroup G}
    (hŶ : Ŷ ∈ scriptY1Star A (lB A)) (hŶM : Ŷ ≤ Subgroup.normalizer (Y₀ : Set G)) {x : G}
    (hxM : x ∈ Subgroup.normalizer (Y₀ : Set G)) (hodd : Odd (orderOf x))
    (hxB : ∀ b ∈ CFSG.Open.pCoreOf 2 Ŷ, x * b = b * x) (hxY : ∀ g ∈ Y₀, x * g = g * x) :
    x = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set M := Subgroup.normalizer (Y₀ : Set G) with hMdef
  set P₂ := CFSG.Open.pCoreOf 2 M with hP₂def
  set B := CFSG.Open.pCoreOf 2 Ŷ with hBdef
  set Q := CFSG.Open.pCoreOf 2 Y₀ with hQdef
  have hA : IsE27 A := h.toSec14Std.isE27
  have hP2 : IsPGroup 2 P₂ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M
  have hB2 : IsPGroup 2 B := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Ŷ
  have hMP : M ≤ Subgroup.normalizer (P₂ : Set G) := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M
  have hŶP : Ŷ ≤ Subgroup.normalizer (P₂ : Set G) := hŶM.trans hMP
  have hP₂M : P₂ ≤ M := CFSG.LieType.BorelTits.pCoreOf_le 2 M
  have htop : Ŷ ⊔ P₂ ≠ ⊤ := fun ht =>
    normalizer_y0_ne_top h (top_le_iff.mp (ht ▸ sup_le hŶM hP₂M))
  have hAM : A ≤ M := Subgroup.le_normalizer.trans h.normalizer_le
  have hQ2 : IsPGroup 2 Q := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y₀
  have hQP : Q ≤ P₂ :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 Y₀).trans Subgroup.le_normalizer)
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y₀) hQ2
  have hQB : Q ≤ B := le_pCoreOf_two_of_mem_scriptQ hŶ hP2 hŶP htop hQ hQP
  have hCAM : Subgroup.centralizer (A : Set G) ≤ M :=
    (Subgroup.centralizer_le_normalizer _).trans h.normalizer_le
  have hRA : P₂ ⊓ Subgroup.centralizer (A : Set G) ≤
      pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) :=
    le_pPrimeCoreOf inf_le_right (le_normalizer_inf (hCAM.trans hMP) Subgroup.le_normalizer)
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr
        (not_three_dvd_card_of_isPGroup_two (hP2.to_le inf_le_left)))
  have hRQ : P₂ ⊓ Subgroup.centralizer (A : Set G) ∈ scriptQ A (lB A) := by
    refine mem_scriptQ_iff.mpr ⟨(isPiSubgroup_piCompl_iff Nat.prime_three _).mpr
      (not_three_dvd_card_of_isPGroup_two (hP2.to_le inf_le_left)), ?_, ?_⟩
    · exact (Subgroup.le_centralizer_iff.mp inf_le_right).trans
        (Subgroup.centralizer_le_normalizer _)
    · intro B' _
      exact inf_le_left.trans (hRA.trans (le_sup_right.trans le_sup_left))
  have hRB : P₂ ⊓ Subgroup.centralizer (A : Set G) ≤ B :=
    le_pCoreOf_two_of_mem_scriptQ hŶ hP2 hŶP htop hRQ inf_le_left
  set Z₀ := P₂ ⊓ Subgroup.centralizer (Q : Set G) with hZ₀def
  have hAQ : A ≤ Subgroup.normalizer (Q : Set G) := (mem_scriptQ_iff.mp hQ).2.1
  have hAZ₀ : A ≤ Subgroup.normalizer (Z₀ : Set G) :=
    le_normalizer_inf (hAM.trans hMP) (Sec16.le_normalizer_centralizer_of_le_normalizer hAQ)
  have hZ₀2 : IsPGroup 2 Z₀ := hP2.to_le inf_le_left
  have hZ₀s : Group.IsSolvable ↥Z₀ := by
    haveI := hZ₀2.isNilpotent
    infer_instance
  have hcop : Nat.Coprime (Nat.card A) (Nat.card Z₀) := by
    obtain ⟨k, hk⟩ := hZ₀2.exists_card_eq
    obtain ⟨l, hl⟩ := hA.isPGroup.exists_card_eq
    rw [hk, hl]
    exact Nat.Coprime.pow l k (by norm_num)
  have hdec := CFSG.GH74.GLS.Stage2.Signalizer.Odd87.CoreA.le_commutator_sup_inf_centralizer
    hAZ₀ hZ₀s hcop
  have hZ₀Y : ⁅Z₀, A⁆ ≤ Y₀ :=
    (Subgroup.commutator_mono le_rfl hAY).trans
      (Subgroup.le_normalizer_iff_commutator_le_right.mp (inf_le_left.trans hP₂M))
  have hZ₀x : Z₀ ≤ Subgroup.centralizer ({x} : Set G) := by
    refine hdec.trans (sup_le (fun y hy => ?_) (fun y hy => ?_))
    · exact Subgroup.mem_centralizer_singleton_iff.mpr (hxY y (hZ₀Y hy)).symm
    · exact Subgroup.mem_centralizer_singleton_iff.mpr
        (hxB y (hRB ⟨hy.1.1, hy.2⟩)).symm
  have hfix : ∀ q ∈ P₂, (∀ b ∈ B, q * b = b * q) → x * q = q * x := fun q hq hqB =>
    (Subgroup.mem_centralizer_singleton_iff.mp
      (hZ₀x ⟨hq, Subgroup.mem_centralizer_iff.mpr fun y hy => (hqB y (hQB hy)).symm⟩)).symm
  have hxP := CFSG.RankThree.GF2n.Tim78.commute_of_thompson_A_times_B hP2 hB2 (hMP hxM)
    ((CFSG.LieType.BorelTits.pCoreOf_le 2 Ŷ).trans hŶP) hodd hxB hfix
  have hxP₂ : x ∈ P₂ := mem_pCoreOf_of_isCharacteristicP (isCharacteristicP_normalizer_y0 h) hxM hxP
  obtain ⟨k, hk⟩ := hP2 ⟨x, hxP₂⟩
  have hk' : x ^ (2 ^ k) = 1 := by simpa using congrArg Subtype.val hk
  have h1 : orderOf x ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
  have h2 : orderOf x = 1 :=
    Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr hodd)) h1
  exact orderOf_eq_one_iff.mp h2

@[expose] def KFact39At (A : Subgroup G) (c : G) (L Y₀ : Subgroup G) : Prop :=
  omegaA A = {Subgroup.zpowers c} → ¬ IsL3TwoPow L →
    ¬ ⁅CFSG.Open.pCoreOf 2 (Subgroup.centralizer (Y₀ : Set G)), Subgroup.zpowers c⁆ ≤
        pPrimeCoreOf 3 (normalClosureIn (Subgroup.centralizer ((A ⊓ L : Subgroup G) : Set G)) c) →
    ∀ γ ∈ Subgroup.centralizer (A : Set G), (∃ k : ℕ, γ ^ (2 ^ k) = 1) →
      ∀ x ∈ normalClosureIn (Subgroup.centralizer ((A ⊓ L : Subgroup G) : Set G)) c,
        γ * x * γ⁻¹ * x⁻¹ ∈
          pPrimeCoreOf 3 (normalClosureIn (Subgroup.centralizer ((A ⊓ L : Subgroup G) : Set G)) c)

theorem stellmacherSub_inf_le_centralizer {A : Subgroup G} {c : G} {L Y₀ : Subgroup G}
    (h : Sec17Std G A c L Y₀) (h149 : Item149 A (lB A)) (h146 : Item146 A (lB A))
    (hE : IsHyperplane A (A ⊓ L)) (hcL : c ∉ L)
    (hQ : CFSG.Open.pCoreOf 2 Y₀ ∈ scriptQ A (lB A))
    (hF : generalizedFitting ↥Y₀ = CFSG.pCore 2 ↥Y₀) (hK39 : KFact39At A c L Y₀)
    (hL : ¬ IsL3TwoPow L) {Ŷ : Subgroup G} (hŶ : Ŷ ∈ scriptY1Star A (lB A))
    (hŶM : Ŷ ≤ Subgroup.normalizer (Y₀ : Set G)) {S : Subgroup G}
    (hS : S ∈ scriptQPiStar A (lB A) ⊤ (piOf 2)) (hSŶ : S ≤ Ŷ) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) :
    stellmacherSub S ⊓ Subgroup.centralizer (A : Set G) ≤
      Subgroup.centralizer (CFSG.Open.pCoreOf p Ŷ : Set G) := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Zp := CFSG.Open.pCoreOf p Ŷ with hZpdef
  set E : Subgroup G := A ⊓ L with hEdef
  set X := normalClosureIn (Subgroup.centralizer (E : Set G)) c with hXdef
  set K := pPrimeCoreOf 3 X with hKdef
  set W := CFSG.Open.pCoreOf 2 (Subgroup.centralizer (Y₀ : Set G)) with hWdef
  have hZpŶ : Zp ≤ Ŷ := CFSG.LieType.BorelTits.pCoreOf_le p Ŷ
  have hbot : Zp = ⊥ → stellmacherSub S ⊓ Subgroup.centralizer (A : Set G) ≤
      Subgroup.centralizer (Zp : Set G) := by
    intro h0 g _
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [h0, Subgroup.coe_bot, Set.mem_singleton_iff] at hz
    rw [hz, one_mul, mul_one]
  rcases h.a10_or_omega with hA10 | hΩ
  ·
    refine hbot (eq_bot_iff.mpr fun z hz => Subgroup.mem_bot.mpr ?_)
    exact eq_one_of_le_y0 h hQ (h.le_y0_of_alternating_ten hA10) hŶ hŶM (hŶM (hZpŶ hz))
      (odd_orderOf_of_mem_pCoreOf hp2 hz) (fun b hb => commute_of_mem_pCoreOf_of_ne hp2 Ŷ hz hb)
      (commute_y0_of_odd h hQ hF hŶ hŶM (hŶM (hZpŶ hz)) (odd_orderOf_of_mem_pCoreOf hp2 hz)
        (fun b hb => commute_of_mem_pCoreOf_of_ne hp2 Ŷ hz hb))
  have hW2 : IsPGroup 2 W := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  have hŶW : Ŷ ≤ Subgroup.normalizer (W : Set G) := hŶM.trans (normalizer_le_normalizer_w Y₀)
  have hWM : W ≤ Subgroup.normalizer (Y₀ : Set G) :=
    (CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans (Subgroup.centralizer_le_normalizer _)
  have htop : Ŷ ⊔ W ≠ ⊤ := fun ht =>
    normalizer_y0_ne_top h (top_le_iff.mp (ht ▸ sup_le hŶM hWM))
  by_cases hW : ⁅W, Subgroup.zpowers c⁆ ≤ K
  ·
    have hAW : A ≤ Subgroup.normalizer (W : Set G) :=
      Subgroup.le_normalizer.trans (h.normalizer_le.trans (normalizer_le_normalizer_w Y₀))
    have hWB : W ≤ CFSG.Open.pCoreOf 2 Ŷ :=
      le_pCoreOf_two_of_mem_scriptQ hŶ hW2 hŶW htop
        (mem_scriptQ_of_commutator_le h hE hcL le_rfl hAW hW) le_rfl
    exact hbot (eq_bot_of_le_pCoreOf_of_commute h hQ hF hŶ hŶM hp hp2 le_rfl
      fun z hz w hw => commute_of_mem_pCoreOf_of_ne hp2 Ŷ hz (hWB hw))
  have hZpA : Zp ≤ Subgroup.centralizer (A : Set G) :=
    (pCoreOf_le_pPrimeCoreOf_two hp hp2 Ŷ).trans
      (Subgroup.le_centralizer_iff.mp (le_centralizer_pPrimeCoreOf h.toSec15R h149 h146 hŶ))
  have hCAE : Subgroup.centralizer (A : Set G) ≤ Subgroup.centralizer (E : Set G) :=
    Subgroup.centralizer_le inf_le_left
  have hCX : Subgroup.centralizer (A : Set G) ≤ Subgroup.normalizer (X : Set G) :=
    hCAE.trans (le_normalizer_normalClosureIn _ c)
  have hCK : Subgroup.centralizer (A : Set G) ≤ Subgroup.normalizer (K : Set G) :=
    hCX.trans (normalizer_le_normalizer_pPrimeCoreOf 3 X)
  have hT : ∀ γ ∈ Subgroup.centralizer (A : Set G), (∃ k : ℕ, γ ^ (2 ^ k) = 1) →
      γ ∈ trivialOn X K := fun γ hγ hk =>
    mem_trivialOn.mpr ⟨hCX hγ, hCK hγ, hK39 hΩ hL hW γ hγ hk⟩
  have hZ0 : Zp ⊓ trivialOn X K = ⊥ := by
    refine eq_bot_of_le_pCoreOf_of_trivial h hE hcL hQ hF hŶ hŶM hp hp2 inf_le_left
      (inf_le_left.trans hZpA) ?_
    rw [Subgroup.commutator_le]
    intro g hg x hx
    rw [commutatorElement_def]
    exact (mem_trivialOn.mp hg.2).2.2 x hx
  have hWS : stellmacherSub S ≤ S := Subgroup.map_subtype_le _
  have hS2 : IsPGroup 2 S := isPGroup_of_mem_scriptQPi Nat.prime_two hS.prop
  intro γ hγ
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  have hγS : γ ∈ S := hWS hγ.1
  obtain ⟨k, hk⟩ := hS2 ⟨γ, hγS⟩
  have hk' : γ ^ (2 ^ k) = 1 := by simpa using congrArg Subtype.val hk
  have hzA : z ∈ Subgroup.centralizer (A : Set G) := hZpA hz
  have hδA : z * γ * z⁻¹ ∈ Subgroup.centralizer (A : Set G) :=
    mul_mem (mul_mem hzA hγ.2) (inv_mem hzA)
  have hδk : (z * γ * z⁻¹) ^ (2 ^ k) = 1 := by rw [conj_pow, hk', mul_one, mul_inv_cancel]
  have ht : z * γ * z⁻¹ * γ⁻¹ ∈ Zp ⊓ trivialOn X K := by
    refine Subgroup.mem_inf.mpr ⟨?_, (trivialOn X K).mul_mem (hT _ hδA ⟨k, hδk⟩)
      ((trivialOn X K).inv_mem (hT γ hγ.2 ⟨k, hk'⟩))⟩
    have hγN : γ ∈ Subgroup.normalizer (Zp : Set G) :=
      CFSG.LieType.BorelTits.le_normalizer_pCoreOf p Ŷ (hSŶ hγS)
    have := (Subgroup.mem_normalizer_iff.mp hγN _).mp (inv_mem hz)
    simpa [mul_assoc] using mul_mem hz this
  rw [hZ0] at ht
  have h1 : z * γ * z⁻¹ * γ⁻¹ = 1 := Subgroup.mem_bot.mp ht
  calc z * γ = (z * γ * z⁻¹ * γ⁻¹) * (γ * z) := by group
    _ = γ * z := by rw [h1, one_mul]

end CFSG.RankThree.PartTwo.Sec17.Proof174Host
