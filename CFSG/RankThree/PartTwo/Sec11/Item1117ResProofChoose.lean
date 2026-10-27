module

public import CFSG.RankThree.PartTwo.Sec11.SetUp1118ProofChoice
import CFSG.RankThree.PartTwo.Sec11.Item1117ResProofSAlt
import CFSG.RankThree.PartTwo.Sec11.Item1118StepsProofChooseG
import CFSG.RankThree.PartTwo.Sec11.Item1118StepsProofS
import CFSG.RankThree.PartTwo.Sec11.Item1119StepsProofCenter
import CFSG.RankThree.PartTwo.Sec11.Item1117ProofBasic
import CFSG.RankThree.PartTwo.Sec11.Item1115Proof
import CFSG.RankThree.PartTwo.Sec11.Inverter1118Proof
import CFSG.RankThree.PartTwo.Sec12.Item123Inputs

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

section Statements

@[expose] def KFact1118InvD : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a : G)
    (R Y : Subgroup G), Sec11Std G A c L a R Y → ∀ d : G, A ⊓ L = Subgroup.zpowers d →
      A = Subgroup.closure {c, a, d} → ∃ t ∈ sec11K L a, t * d * t⁻¹ = d⁻¹

@[expose] def KFact1118InvElt : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a : G)
    (R Y : Subgroup G) (d x s r g : G), Sec11Data G A c L a R Y d x s r g →
      ¬ KFacts.InducesStdKind Y c .field →
      ((∃ q : TauCeti.PrimePower, Sec4.IsoGTwo (Y ⧸ aschbacherSolvableCore 3 Y) q) ∨
        (∃ n : ℕ, Sec8.IsoTrialityD4 (Y ⧸ aschbacherSolvableCore 3 Y) n) ∨
        Sec13.IsLThreePi (Y ⧸ aschbacherSolvableCore 3 Y)) →
      ∃ g₀ ∈ Y ⊓ Subgroup.normalizer (A : Set G), orderOf g₀ = 3 ∧
        ∃ z ∈ A, g₀ * z * g₀⁻¹ ≠ z

end Statements

namespace Item1117ResProof

section Group

variable {G : Type*} [Group G]

theorem conj_mul_inv_mem_zpowers_of_not_mem {A Y : Subgroup G} {c a d g : G}
    (hcomm : ∀ y ∈ A, ∀ z ∈ A, y * z = z * y) (hexp : ∀ y ∈ A, y ^ 3 = 1)
    (hA : A = Subgroup.closure {c, a, d}) (hcad : c ∉ Subgroup.closure ({a, d} : Set G))
    (hgA : g ∈ Subgroup.normalizer (A : Set G)) (hga : g * a = a * g) (hgd : g * d = d * g)
    (hg3 : ∀ z ∈ A, g ^ 3 * z * (g ^ 3)⁻¹ = z) (hgY : g ∈ Y)
    (hAY : A ≤ Subgroup.normalizer (Y : Set G)) (hdY : d ∈ Y) (haY : a ∉ Y) :
    g * c * g⁻¹ * c⁻¹ ∈ Subgroup.zpowers d := by
  set B := Subgroup.closure ({a, d} : Set G) with hBdef
  have hcA : c ∈ A := hA ▸ Subgroup.subset_closure (by simp)
  have haA : a ∈ A := hA ▸ Subgroup.subset_closure (by simp)
  have hdA : d ∈ A := hA ▸ Subgroup.subset_closure (by simp)
  have hBA : B ≤ A := by
    rw [hBdef, Subgroup.closure_le]
    rintro y (rfl | rfl)
    exacts [haA, hdA]
  have hc3 : c ^ 3 = 1 := hexp c hcA
  have ha3 : a ^ 3 = 1 := hexp a haA
  have hgB : ∀ b ∈ B, g * b * g⁻¹ = b := by
    intro b hb
    have hle : B ≤ Subgroup.centralizer ({g} : Set G) := by
      rw [hBdef, Subgroup.closure_le]
      rintro y (rfl | rfl)
      · exact Subgroup.mem_centralizer_singleton_iff.mpr hga.symm
      · exact Subgroup.mem_centralizer_singleton_iff.mpr hgd.symm
    have hbg := Subgroup.mem_centralizer_singleton_iff.mp (hle hb)
    rw [← hbg, mul_inv_cancel_right]
  set u := g * c * g⁻¹ * c⁻¹ with hu
  obtain ⟨i, b₀, hb₀, hgc⟩ :=
    ActOnA.exists_zpow_mul_of_mem hcomm hA ((Subgroup.mem_normalizer_iff.mp hgA c).mp hcA)
  have hgact : ∀ (k : ℤ) (b : G), b ∈ B →
      ∃ b' ∈ B, g * (c ^ k * b) * g⁻¹ = c ^ (i * k) * b' := by
    intro k b hb
    refine ⟨b₀ ^ k * b, B.mul_mem (B.zpow_mem hb₀ k) hb, ?_⟩
    have e1 : g * (c ^ k * b) * g⁻¹ = (g * c * g⁻¹) ^ k * (g * b * g⁻¹) := by
      rw [conj_zpow]
      group
    have hcb : Commute (c ^ i) b₀ := hcomm _ (A.zpow_mem hcA i) _ (hBA hb₀)
    rw [e1, hgB b hb, hgc, hcb.mul_zpow, ← zpow_mul]
    group
  obtain ⟨b₁, hb₁, h1⟩ := hgact i b₀ hb₀
  obtain ⟨b₂, hb₂, h2⟩ := hgact (i * i) b₁ hb₁
  have h3 : c = c ^ (i * (i * i)) * b₂ := by
    have e : g ^ 3 * c * (g ^ 3)⁻¹ = g * (g * (g * c * g⁻¹) * g⁻¹) * g⁻¹ := by
      simp only [pow_succ, pow_zero, one_mul]
      group
    calc c = g ^ 3 * c * (g ^ 3)⁻¹ := (hg3 c hcA).symm
      _ = g * (g * (g * c * g⁻¹) * g⁻¹) * g⁻¹ := e
      _ = c ^ (i * (i * i)) * b₂ := by rw [hgc, h1, h2]
  have hk : c ^ (1 - i * (i * i)) ∈ B := by
    have hcb₂ : Commute (c ^ (i * (i * i))) b₂ := hcomm _ (A.zpow_mem hcA _) _ (hBA hb₂)
    have e : c ^ (1 - i * (i * i)) = b₂ := by
      rw [zpow_sub, zpow_one]
      calc c * (c ^ (i * (i * i)))⁻¹ = c ^ (i * (i * i)) * b₂ * (c ^ (i * (i * i)))⁻¹ := by
            rw [← h3]
        _ = b₂ := by rw [hcb₂.eq]; group
    rw [e]
    exact hb₂
  have hi : (3 : ℤ) ∣ i - 1 := by
    refine ActOnA.three_dvd_sub_one_of_dvd_one_sub_cube ?_
    by_contra h3'
    exact hcad (ActOnA.mem_of_zpow_mem hc3 hk h3')
  have hci : c ^ i = c := by
    rw [← sub_add_cancel i 1, zpow_add, ActOnA.zpow_eq_one_of_dvd hc3 hi, one_mul, zpow_one]
  have hub : u = b₀ := by
    rw [hu, hgc, hci]
    calc c * b₀ * c⁻¹ = b₀ * c * c⁻¹ := by rw [hcomm c hcA b₀ (hBA hb₀)]
      _ = b₀ := by group
  have huB : u ∈ B := hub ▸ hb₀
  have huY : u ∈ Y := by
    have hc : c * g⁻¹ * c⁻¹ ∈ Y :=
      (Subgroup.mem_normalizer_iff.mp (hAY hcA) g⁻¹).mp (Y.inv_mem hgY)
    have e : u = g * (c * g⁻¹ * c⁻¹) := by rw [hu]; group
    rw [e]
    exact Y.mul_mem hgY hc
  obtain ⟨α, β, huab⟩ :=
    Sec12.exists_zpow_mul_zpow_of_mem_closure_pair (hcomm a haA d hdA) huB
  have hu1 : a ^ α = 1 := by
    by_contra hα
    have h3α : ¬ (3 : ℤ) ∣ α := fun h => hα (ActOnA.zpow_eq_one_of_dvd ha3 h)
    apply haY
    refine ActOnA.mem_of_zpow_mem ha3 ?_ h3α
    have e : a ^ α = u * (d ^ β)⁻¹ := by rw [huab]; group
    rw [e]
    exact Y.mul_mem huY (Y.inv_mem (Y.zpow_mem hdY β))
  rw [huab, hu1, one_mul]
  exact Subgroup.zpow_mem_zpowers d β

theorem mem_normalizer_closure_of_inverts [Finite G] {t c a d : G} (htc : t * c = c * t)
    (hta : t * a = a * t) (htd : t * d * t⁻¹ = d⁻¹) :
    t ∈ Subgroup.normalizer ((Subgroup.closure {c, a, d} : Subgroup G) : Set G) := by
  refine Item1118StepsProof.mem_normalizer_closure_of_forall ?_
  rintro y (rfl | rfl | rfl)
  · rw [htc, mul_inv_cancel_right]
    exact Subgroup.subset_closure (by simp)
  · rw [hta, mul_inv_cancel_right]
    exact Subgroup.subset_closure (by simp)
  · rw [htd]
    exact Subgroup.inv_mem _ (Subgroup.subset_closure (by simp))

end Group

section Data

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {a : G}
  {R Y : Subgroup G} {d x s r g : G}

theorem c_not_mem_closure_a_d (h : Sec11Std G A c L a R Y) (hA : A = Subgroup.closure {c, a, d})
    (hdA : d ∈ A) : c ∉ Subgroup.closure ({a, d} : Set G) := by
  have hAe := h.mem_partTwoF.1
  have hexp : ∀ y ∈ A, y ^ 3 = 1 := hAe.2
  have hcomm : ∀ y ∈ A, ∀ z ∈ A, y * z = z * y := fun y hy z hz =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨y, hy⟩ ⟨z, hz⟩)
  intro hc
  have hle : A ≤ Subgroup.closure ({a, d} : Set G) := by
    rw [hA, Subgroup.closure_le]
    rintro z (rfl | rfl | rfl)
    · exact hc
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.subset_closure (by simp)
  have h1 := Subgroup.card_le_of_le hle
  have h2 := Sec10.card_closure_pair_le (hcomm a h.a_mem d hdA) (hexp a h.a_mem) (hexp d hdA)
  rw [h.card_eq] at h1
  omega

theorem inverts_on_A (h : Sec11Std G A c L a R Y) (hA : A = Subgroup.closure {c, a, d})
    {t g' : G} (ht : t ∈ sec11K L a) (htd : t * d * t⁻¹ = d⁻¹) (hga : g' * a = a * g')
    (hgd : g' * d = d * g') (hgc : g' * c * g'⁻¹ * c⁻¹ ∈ Subgroup.zpowers d) :
    t ∈ sec11K L a ⊓ Subgroup.normalizer (A : Set G) ∧
      ∀ z ∈ A, t * g' * t⁻¹ * z * (t * g' * t⁻¹)⁻¹ = g'⁻¹ * z * g' := by
  have htc : t * c = c * t := Subgroup.mem_centralizer_singleton_iff.mp
    (Sec6.le_centralizer_of_mem_thetaComponentsAt h.mem_thetaComponentsAt (sec11K_le L a ht))
  have hta : t * a = a * t := Subgroup.mem_centralizer_singleton_iff.mp
    (Sec6.le_centralizer_of_mem_thetaComponentsAt h.mem_thetaComponentsAt_Y (h.sec11K_le ht))
  have htu : t * (g' * c * g'⁻¹ * c⁻¹) * t⁻¹ = (g' * c * g'⁻¹ * c⁻¹)⁻¹ :=
    Inverter1118Proof.inverts_of_mem_zpowers htd hgc
  have hgu : g' * (g' * c * g'⁻¹ * c⁻¹) = g' * c * g'⁻¹ * c⁻¹ * g' := by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hgc
    rw [← hk]
    exact ((Commute.zpow_right hgd k)).eq
  refine ⟨⟨ht, ?_⟩, ?_⟩
  · rw [hA]
    exact mem_normalizer_closure_of_inverts htc hta htd
  · intro z hz
    rw [hA] at hz
    exact Item1118StepsProof.conj_conj_eq_of_inverts htc hta htd hga hgd htu hgu z hz

end Data

section List

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {a : G}
  {R Y : Subgroup G}

theorem a_not_mem_Y_of_list (h : Sec11Std G A c L a R Y)
    (hlist : (∃ q : TauCeti.PrimePower, Sec4.IsoGTwo (Y ⧸ aschbacherSolvableCore 3 Y) q) ∨
      (∃ n : ℕ, Sec8.IsoTrialityD4 (Y ⧸ aschbacherSolvableCore 3 Y) n) ∨
      Sec13.IsLThreePi (Y ⧸ aschbacherSolvableCore 3 Y)) : a ∉ Y := by
  have hq := Sec12.isQuasisimple_thetaQuot_of_mem h.mem_thetaComponentsAt_Y
  refine a_not_mem_Y_of_center_eq_bot h ?_
  rcases hlist with ⟨q, hq'⟩ | ⟨n, hn⟩ | hL
  · exact Item1119StepsProof.center_eq_bot_of_isoGTwo hq.1 hq'
  · exact Item1119StepsProof.center_eq_bot_of_isoTrialityD4 hq.1 hn
  · exact Item1119StepsProof.center_eq_bot_of_isLThreePi hq hL

end List

end Item1117ResProof

section MainList

open Item1117ResProof in
theorem kFact1118Inverter_of (h45 : Sec4.Item4_5) (h117 : Item117) (hD : KFact1118InvD)
    (hE : KFact1118InvElt) : KFact1118Inverter := by
  intro G _ _ A c L a R Y d x s r g h hnf hlist
  obtain ⟨g₀, ⟨hg₀Y, hg₀A⟩, hg₀3, hg₀ne⟩ := hE G A c L a R Y d x s r g h hnf hlist
  obtain ⟨t, ht, htd⟩ := hD G A c L a R Y h.toSec11Std d h.inf_eq h.closure_eq
  have hAe := h.mem_partTwoF.1
  have hexp : ∀ y ∈ A, y ^ 3 = 1 := hAe.2
  have hcomm : ∀ y ∈ A, ∀ z ∈ A, y * z = z * y := fun y hy z hz =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨y, hy⟩ ⟨z, hz⟩)
  have hdA := Item1117Proof.d_mem_A h
  have hd3 : orderOf d = 3 := Item1117Proof.orderOf_d h
  have hg₀a : g₀ * a = a * g₀ := Subgroup.mem_centralizer_singleton_iff.mp
    (Sec6.le_centralizer_of_mem_thetaComponentsAt h.mem_thetaComponentsAt_Y hg₀Y)
  have hk₁ : g₀ ^ 3 ^ 1 = 1 := by rw [pow_one, ← hg₀3, pow_orderOf_eq_one]
  have hg₀d : g₀ * d = d * g₀ := Sec12.commute_of_conj_mem_zpowers hd3
    ((Subgroup.mem_normalizer_iff.mp (Item1115Proof.W_le_normalizer_d h117 h hg₀A) d).mp
      (Subgroup.mem_zpowers d)) hk₁
  have hg₀cube : ∀ z ∈ A, g₀ ^ 3 * z * (g₀ ^ 3)⁻¹ = z := fun z _ => by
    rw [show g₀ ^ 3 = 1 by rw [← hg₀3, pow_orderOf_eq_one]]
    group
  have hAY : A ≤ Subgroup.normalizer (Y : Set G) :=
    Sec6.le_normalizer_of_mem_thetaComponentsAt h45 h.toTheoremFourHyp hAe h.a_mem h.a_ne_one Y
      h.mem_thetaComponentsAt_Y
  have hdY : d ∈ Y := h.sec11K_le (h.toSec11Std.d_mem_sec11K h.inf_eq)
  have hgc : g₀ * c * g₀⁻¹ * c⁻¹ ∈ Subgroup.zpowers d :=
    conj_mul_inv_mem_zpowers_of_not_mem hcomm hexp h.closure_eq
      (c_not_mem_closure_a_d h.toSec11Std h.closure_eq hdA) hg₀A hg₀a hg₀d hg₀cube hg₀Y hAY hdY
      (a_not_mem_Y_of_list h.toSec11Std hlist)
  obtain ⟨htW, hinv⟩ := inverts_on_A h.toSec11Std h.closure_eq ht htd hg₀a hg₀d hgc
  exact ⟨g₀, t, ⟨hg₀Y, hg₀A⟩, hg₀3, hg₀ne, htW, hinv⟩

end MainList

end CFSG.RankThree.PartTwo.Sec11
