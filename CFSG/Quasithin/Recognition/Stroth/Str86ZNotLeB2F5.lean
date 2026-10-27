module


import CFSG.Quasithin.Recognition.Stroth.Str86ZTwoOrth
import CFSG.Quasithin.Recognition.Stroth.Str86ZTwoBound
import CFSG.Quasithin.Recognition.Stroth.Str83G3Tools
import CFSG.Quasithin.Background.OddIndexAveraging
public import CFSG.Adapters.QiuzhenLegacy.Glauberman.RelIndexSup
public import CFSG.Quasithin.Recognition.Stroth.BenderH7
public import CFSG.Quasithin.Recognition.Stroth.F112Tree
import CFSG.Blueprint.SourceClassicalTransport

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.F112R CFSG.LieType.BorelTits
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem centralizerMod_bot_eq (X U : Subgroup G) :
    centralizerMod ⊥ X U = X ⊓ Subgroup.centralizer (U : Set G) := by
  ext x
  rw [mem_centralizerMod, Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
  constructor
  · rintro ⟨hx, -, h⟩
    refine ⟨hx, fun u hu => ?_⟩
    have h1 := h u hu
    rw [Subgroup.mem_bot] at h1
    have h2 : x * u * x⁻¹ = u := mul_inv_eq_one.mp h1
    calc u * x = x * u * x⁻¹ * x := by rw [h2]
      _ = x * u := by group
  · rintro ⟨hx, h⟩
    refine ⟨hx, by rw [Subgroup.normalizer_eq_top]; exact Subgroup.mem_top x, fun u hu => ?_⟩
    rw [Subgroup.mem_bot, ← h u hu]
    group

theorem conj_commutatorElement_eq_inv_of_mul_self {z a : G} (haa : a * a = 1) :
    a * ⁅z, a⁆ * a⁻¹ = ⁅z, a⁆⁻¹ := by
  have ha1 : a⁻¹ = a := inv_eq_of_mul_eq_one_right haa
  calc a * ⁅z, a⁆ * a⁻¹ = a * (z * a * z⁻¹ * a⁻¹) * a⁻¹ := by rw [commutatorElement_def]
    _ = a * z * a * z⁻¹ * (a⁻¹ * a⁻¹) := by group
    _ = a * z * a * z⁻¹ := by rw [ha1, haa, mul_one]
    _ = a * z * a⁻¹ * z⁻¹ := by rw [ha1]
    _ = ⁅z, a⁆⁻¹ := by rw [commutatorElement_def]; group

theorem str86_b2_f5 {L1 L2 S A : Subgroup G} {k n : ℕ}
    {F : Type} [Field F] [Finite F] (hF : F112Hyp L1 L2 S)
    (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G)) (hk : 2 ≤ k)
    (hFc : Nat.card F = (2 ^ k) ^ 2)
    (hU3 : Nonempty (oTwoQuot ↥L1 ≃* StatedSU 3 (2 ^ k) F) ∨
      Nonempty (oTwoQuot ↥L1 ≃* StatedProj (StatedSU 3 (2 ^ k) F)))
    (hB2 : VBig L2) (hn : 2 ≤ n) (hL2 : IsL2Quot n (oTwoQuot ↥L2))
    (hZI : L1 ⊔ Q1 L1 L2 S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G))
    (hAS : A ≤ S) (hA : IsElemAbelian 2 A) (hAQ : ¬ A ≤ Q2 L1 L2 S)
    (hbound : (Z2 L1 L2 S ⊓ Subgroup.centralizer (A : Set G)).relIndex (Z2 L1 L2 S) ≤
      (A ⊓ Q2 L1 L2 S).relIndex A) :
    (A ⊓ Q2 L1 L2 S).relIndex A = 2 ^ n ∧
      (Z2 L1 L2 S ⊓ Subgroup.centralizer (A : Set G)).relIndex (Z2 L1 L2 S) = 2 ^ n ∧
      IsChiefStep (L2 ⊔ Q2 L1 L2 S) (Z2 L1 L2 S) ⊥ (Z2 L1 L2 S) ∧
      ¬ IsCentralStep (L2 ⊔ Q2 L1 L2 S) ⊥ (Z2 L1 L2 S) ∧
      ∀ z ∈ Z2 L1 L2 S, ∀ s ∈ S, ⁅z, s⁆ ∈ Z1 L1 L2 S := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : VU3Big L1 := ⟨k, hk, F, inferInstance, inferInstance, hFc, hU3⟩
  have h2 : VL2 L2 := ⟨n, hL2⟩
  obtain ⟨-, hZ1Z2, hZ2H, -, hZ2CS⟩ := str86_caseI_basics hF hSB h1 hB2 h2 hZI
  have hne : ∀ X Y : Subgroup G, X.relIndex Y ≠ 0 := fun X Y =>
    CFSG.Quasithin.D15Proof.relIndex_ne_zero _ _
  have hpH : pCoreOf 2 (L2 ⊔ Q2 L1 L2 S) = Q2 L1 L2 S := str86_pCoreOf_u3H hF.toW
  have hLH : IsL2Quot n (oTwoQuot ↥(L2 ⊔ Q2 L1 L2 S)) := str86_isL2Quot_u3H hF.toW hL2
  have hZ2e : IsElemAbelian 2 (Z2 L1 L2 S) := SmithC27.isElemAbelian_omegaOneCenterOf _
  have hZ2p : IsPGroup 2 ↥(Z2 L1 L2 S) := hZ2e.isPGroup
  have hZ2Q2 : Z2 L1 L2 S ≤ Q2 L1 L2 S := omegaOneCenterOf_le _
  have hZ2H' : Z2 L1 L2 S ≤ L2 ⊔ Q2 L1 L2 S := hZ2Q2.trans le_sup_right
  have hQ2S : Q2 L1 L2 S ≤ S := F7.isSylowTwoOf_pCoreOf_le (f112_isSylowTwoOf_P2 hF.toW)
  have hSH : S ≤ L2 ⊔ Q2 L1 L2 S := str86_s_le_u3H hF.toW hSB hn hL2
  have hAH : A ≤ L2 ⊔ Q2 L1 L2 S := hAS.trans hSH
  have hHZ : L2 ⊔ Q2 L1 L2 S ≤ Subgroup.normalizer (Z2 L1 L2 S : Set G) :=
    str86_z2_normal_u3H L1 L2 S
  have hQ2CZ : Q2 L1 L2 S ≤ Subgroup.centralizer (Z2 L1 L2 S : Set G) :=
    SmithC27.pCoreOf_le_centralizer_omegaOneCenterOf (P2 L1 L2 S)
  have hcommZ2 : ∀ x ∈ Z2 L1 L2 S, ∀ y ∈ Z2 L1 L2 S, x * y = y * x := fun x hx y hy =>
    A4.mul_comm_of_mem_omegaOneCenterOf hx hy
  have hSQ2 : ¬ S ≤ Q2 L1 L2 S := fun hle => hAQ (hAS.trans hle)
  have hSP1 : S ≤ P1 L1 L2 S := (le_sup_right : S ≤ bigB L1 L2 S).trans le_sup_right
  have hZ1N : S ≤ Subgroup.normalizer (Z1 L1 L2 S : Set G) :=
    hSP1.trans (SmithC27.le_normalizer_omegaOneCenterOf_pCoreOf (P1 L1 L2 S))
  obtain ⟨W, hWZ2, hstepW, hncW⟩ := str86_exists_chiefStep_u3H hF hSB hk hFc hU3 hB2 h2 hZI
  have hstepW' : IsChiefStep (L2 ⊔ Q2 L1 L2 S) (Z2 L1 L2 S) ⊥ W :=
    ⟨⟨hWZ2, hstepW.1.2⟩, ⟨bot_le, hstepW.2.1.2⟩, hstepW.2.2.1,
      fun K hK hK1 hK2 => hstepW.2.2.2 K ⟨hK.1.trans hZ2Q2, hK.2⟩ hK1 hK2⟩
  have hHW : L2 ⊔ Q2 L1 L2 S ≤ Subgroup.normalizer (W : Set G) :=
    D14.le_normalizer_of_isNormalIn hstepW'.1
  obtain ⟨t, htA, htQ⟩ := Set.not_subset.mp hAQ
  have htt : t * t = 1 := by simpa [pow_two] using hA.2 t htA
  have hq := l2ChiefSectionRep_pow_le_relIndex_centralizerMod (m := n) hn hLH hZ2p hZ2H'
    hstepW' hncW (hAH htA) (by rw [htt]; exact Subgroup.one_mem _) (by rw [hpH]; exact htQ)
  have hc1 : (centralizerMod ⊥ W (Subgroup.zpowers t)).relIndex W ≤
      (centralizerMod ⊥ W A).relIndex W :=
    Subgroup.relIndex_le_of_le_left
      (centralizerMod_anti_right W (Subgroup.zpowers_le.mpr htA)) (hne _ _)
  have hconv : ∀ X : Subgroup G, (X ⊓ Subgroup.centralizer (A : Set G)).relIndex X =
      (Subgroup.centralizer (A : Set G)).relIndex X := by
    intro X
    rw [inf_comm, Subgroup.inf_relIndex_right]
  have hc2 : (centralizerMod ⊥ W A).relIndex W ≤
      (Z2 L1 L2 S ⊓ Subgroup.centralizer (A : Set G)).relIndex (Z2 L1 L2 S) := by
    rw [centralizerMod_bot_eq, hconv, hconv]
    exact Subgroup.relIndex_le_of_le_right hWZ2 (hne _ _)
  have hc3 := relIndex_inf_pCoreOf_le_two_pow hn hLH hAH hA
  rw [hpH] at hc3
  have hkeq : (A ⊓ Q2 L1 L2 S).relIndex A = 2 ^ n :=
    le_antisymm hc3 (hq.trans (hc1.trans (hc2.trans hbound)))
  have hzeq : (Z2 L1 L2 S ⊓ Subgroup.centralizer (A : Set G)).relIndex (Z2 L1 L2 S) = 2 ^ n :=
    le_antisymm (hbound.trans hc3) (hq.trans (hc1.trans hc2))
  have hweq : (centralizerMod ⊥ W A).relIndex W = 2 ^ n :=
    le_antisymm (hc2.trans hzeq.le) (hq.trans hc1)
  have hAN : A ≤ Subgroup.normalizer (Q2 L1 L2 S : Set G) :=
    hAS.trans (le_normalizer_q2_of_sylow (L1 := L1) (L2 := L2) (S := S))
  have hAQS : A ⊔ Q2 L1 L2 S = S := by
    have hle : A ⊔ Q2 L1 L2 S ≤ S := sup_le hAS hQ2S
    have hsec := (CFSG.GroupTheory.relIndex_sup_eq_relIndex_inf_of_le_normalizer
      (H := A) (K := Q2 L1 L2 S) hAN).2
    have hmul := Subgroup.relIndex_mul_relIndex _ _ _
      (le_sup_right : Q2 L1 L2 S ≤ A ⊔ Q2 L1 L2 S) hle
    rw [hsec, hkeq, str86_relIndex_q2_s hF.toW hSB hn hL2] at hmul
    have h1' : (A ⊔ Q2 L1 L2 S).relIndex S = 1 := by
      have h' : 2 ^ n * (A ⊔ Q2 L1 L2 S).relIndex S = 2 ^ n * 1 := by rw [hmul, mul_one]
      exact Nat.eq_of_mul_eq_mul_left (by positivity) h'
    exact le_antisymm hle (Subgroup.relIndex_eq_one.mp h1')
  have hCA : Z2 L1 L2 S ⊓ Subgroup.centralizer (A : Set G) = Z1 L1 L2 S := by
    rw [← hZ2CS]
    refine le_antisymm (fun z hz => ?_) (inf_le_inf_left _ (Subgroup.centralizer_le hAS))
    obtain ⟨hzZ, hzA⟩ := Subgroup.mem_inf.mp hz
    refine Subgroup.mem_inf.mpr ⟨hzZ, ?_⟩
    have hle : A ⊔ Q2 L1 L2 S ≤ Subgroup.centralizer ({z} : Set G) := by
      refine sup_le (fun a ha => ?_) (fun q hq => ?_)
      · rw [Subgroup.mem_centralizer_iff]
        intro y hy
        rw [Set.mem_singleton_iff] at hy
        subst hy
        exact ((Subgroup.mem_centralizer_iff.mp hzA) a ha).symm
      · rw [Subgroup.mem_centralizer_iff]
        intro y hy
        rw [Set.mem_singleton_iff] at hy
        subst hy
        exact (Subgroup.mem_centralizer_iff.mp (hQ2CZ hq) y hzZ)
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    have h' := hle (by rw [hAQS]; exact hs)
    rw [Subgroup.mem_centralizer_iff] at h'
    exact (h' z (Set.mem_singleton z)).symm
  have hZ1rel : (Z1 L1 L2 S).relIndex (Z2 L1 L2 S) = 2 ^ n := by
    rw [← hCA]
    exact hzeq
  have hWN1 : W ≤ Subgroup.normalizer (Z1 L1 L2 S : Set G) :=
    ((hWZ2.trans hZ2Q2).trans hQ2S).trans hZ1N
  have hZW : Z2 L1 L2 S ≤ W ⊔ Z1 L1 L2 S := by
    have hsec := (CFSG.GroupTheory.relIndex_sup_eq_relIndex_inf_of_le_normalizer
      (H := W) (K := Z1 L1 L2 S) hWN1).2
    have hWZ1 : (W ⊓ Z1 L1 L2 S).relIndex W = 2 ^ n := by
      rw [← hCA, ← inf_assoc, inf_eq_left.mpr hWZ2, ← centralizerMod_bot_eq]
      exact hweq
    have hle : W ⊔ Z1 L1 L2 S ≤ Z2 L1 L2 S := sup_le hWZ2 hZ1Z2
    have hmul := Subgroup.relIndex_mul_relIndex _ _ _
      (le_sup_right : Z1 L1 L2 S ≤ W ⊔ Z1 L1 L2 S) hle
    rw [hsec, hWZ1, hZ1rel] at hmul
    have h1' : (W ⊔ Z1 L1 L2 S).relIndex (Z2 L1 L2 S) = 1 := by
      have h' : 2 ^ n * (W ⊔ Z1 L1 L2 S).relIndex (Z2 L1 L2 S) = 2 ^ n * 1 := by
        rw [hmul, mul_one]
      exact Nat.eq_of_mul_eq_mul_left (by positivity) h'
    exact Subgroup.relIndex_eq_one.mp h1'
  set C4 : Subgroup G := centralizerMod W (L2 ⊔ Q2 L1 L2 S) (Z2 L1 L2 S) with hC4def
  have hC4n : L2 ⊔ Q2 L1 L2 S ≤ Subgroup.normalizer (C4 : Set G) :=
    le_normalizer_centralizerMod hHW Subgroup.le_normalizer hHZ
  have hSC4 : S ≤ C4 := by
    intro s hs
    refine mem_centralizerMod.mpr ⟨hSH hs, hHW (hSH hs), fun z hz => ?_⟩
    obtain ⟨w, hw, z1, hz1, rfl⟩ :=
      (F1.mem_sup_iff_exists_mul_of_le_normalizer hWN1).mp (hZW hz)
    have hz1C : z1 ∈ Subgroup.centralizer (S : Set G) := by
      rw [← hZ2CS] at hz1
      exact (Subgroup.mem_inf.mp hz1).2
    have hsz1 : s * z1 * s⁻¹ = z1 := by
      rw [Subgroup.mem_centralizer_iff.mp hz1C s hs]
      group
    have e : s * (w * z1) * s⁻¹ * (w * z1)⁻¹ =
        (s * w * s⁻¹) * (s * z1 * s⁻¹) * z1⁻¹ * w⁻¹ := by group
    rw [e, hsz1, mul_inv_cancel_right]
    exact W.mul_mem ((Subgroup.mem_normalizer_iff.mp (hHW (hSH hs)) w).mp hw) (W.inv_mem hw)
  have hC4eq : C4 = L2 ⊔ Q2 L1 L2 S := by
    rcases eq_or_eq_sup_of_normal_of_isL2Quot hF.toW hn hL2 (centralizerMod_le_left _ _ _) hC4n
      (hQ2S.trans hSC4) with h | h
    · exact absurd (hSC4.trans h.le) hSQ2
    · exact h
  have hSsyl : IsSylowTwoOf S (L2 ⊔ Q2 L1 L2 S) :=
    F7.isSylowTwoOf_mono_right (f112_isSylowTwoOf_P2 hF.toW) hSH (u3H_le_p2 L1 L2 S)
  have hodd : Odd (S.relIndex (L2 ⊔ Q2 L1 L2 S)) := by
    rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
    exact hSsyl.2.2
  have hLA := mem_of_centralizerMod_odd (P := L2 ⊔ Q2 L1 L2 S) (T := S) (Q := Z2 L1 L2 S)
    (Z := ⊥) (N := W) hSH hodd bot_le hWZ2
    (by rw [Subgroup.normalizer_eq_top]; exact le_top) hHW hHZ
    (fun x hx y hy => by rw [Subgroup.mem_bot, hcommZ2 x hx y hy]; group)
    (fun x hx => by rw [Subgroup.mem_bot, ← pow_two]; exact hZ2e.2 x hx)
    (fun p hp x hx => by
      have hpC : p ∈ C4 := by rw [hC4eq]; exact hp
      exact (mem_centralizerMod.mp hpC).2.2 x hx)
    (fun x hx hp => by
      rw [← hZ2H]
      refine Subgroup.mem_inf.mpr ⟨hx, Subgroup.mem_centralizer_iff.mpr fun p hpH => ?_⟩
      have h' := hp p hpH
      rw [Subgroup.mem_bot] at h'
      have h'' : p * x * p⁻¹ = x := mul_inv_eq_one.mp h'
      calc p * x = p * x * p⁻¹ * p := by group
        _ = x * p := by rw [h''])
  have hZ1W : Z1 L1 L2 S ≤ W := by
    rw [← hZ2CS, ← centralizerMod_bot_eq]
    exact hLA
  have hWeq : W = Z2 L1 L2 S := le_antisymm hWZ2 (hZW.trans (sup_le le_rfl hZ1W))
  rw [hWeq] at hstepW' hncW
  have hquad : ∀ z ∈ Z2 L1 L2 S, ∀ a ∈ A, ⁅z, a⁆ ∈ Z1 L1 L2 S := by
    intro z hz a ha
    by_cases haQ : a ∈ Q2 L1 L2 S
    · have hza : z * a = a * z :=
        Subgroup.mem_centralizer_iff.mp (hQ2CZ haQ) z hz
      have e : ⁅z, a⁆ = 1 := by rw [commutatorElement_def, hza]; group
      rw [e]
      exact Subgroup.one_mem _
    · have haa : a * a = 1 := by simpa [pow_two] using hA.2 a ha
      have hqa := l2ChiefSectionRep_pow_le_relIndex_centralizerMod (m := n) hn hLH hZ2p hZ2H'
        hstepW' hncW (hAH ha) (by rw [haa]; exact Subgroup.one_mem _) (by rw [hpH]; exact haQ)
      rw [centralizerMod_bot_eq] at hqa
      set X : Subgroup G := Z2 L1 L2 S ⊓ Subgroup.centralizer (Subgroup.zpowers a : Set G)
        with hXdef
      have hZ1X : Z1 L1 L2 S ≤ X := by
        refine le_inf hZ1Z2 ?_
        rw [← hZ2CS]
        exact inf_le_right.trans
          (Subgroup.centralizer_le (Subgroup.zpowers_le.mpr (hAS ha)))
      have hXZ1 : X ≤ Z1 L1 L2 S := by
        have hmul := Subgroup.relIndex_mul_relIndex _ _ _ hZ1X (inf_le_left : X ≤ Z2 L1 L2 S)
        rw [hZ1rel] at hmul
        have hle := Nat.mul_le_mul_left ((Z1 L1 L2 S).relIndex X) hqa
        rw [hmul] at hle
        have hle' : (Z1 L1 L2 S).relIndex X * 2 ^ n ≤ 1 * 2 ^ n := by rwa [one_mul]
        have h1' := Nat.le_of_mul_le_mul_right hle' (by positivity)
        have h0 := hne (Z1 L1 L2 S) X
        exact Subgroup.relIndex_eq_one.mp (by omega)
      apply hXZ1
      have hu : a * z⁻¹ * a⁻¹ ∈ Z2 L1 L2 S :=
        (Subgroup.mem_normalizer_iff.mp (hHZ (hAH ha)) z⁻¹).mp ((Z2 L1 L2 S).inv_mem hz)
      have hx : ⁅z, a⁆ ∈ Z2 L1 L2 S := by
        have e : ⁅z, a⁆ = z * (a * z⁻¹ * a⁻¹) := by rw [commutatorElement_def]; group
        rw [e]
        exact (Z2 L1 L2 S).mul_mem hz hu
      have hxinv : ⁅z, a⁆⁻¹ = ⁅z, a⁆ := by
        have h' : ⁅z, a⁆ ^ 2 = 1 := hZ2e.2 _ hx
        rw [pow_two] at h'
        exact inv_eq_of_mul_eq_one_right h'
      have hcomm : Commute a ⁅z, a⁆ := by
        have h' := conj_commutatorElement_eq_inv_of_mul_self (z := z) haa
        rw [hxinv] at h'
        calc a * ⁅z, a⁆ = a * ⁅z, a⁆ * a⁻¹ * a := by group
          _ = ⁅z, a⁆ * a := by rw [h']
      refine Subgroup.mem_inf.mpr ⟨hx, Subgroup.mem_centralizer_iff.mpr fun h hh => ?_⟩
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
      exact (hcomm.zpow_left j).eq
  refine ⟨hkeq, hzeq, hstepW', hncW, fun z hz s hs => ?_⟩
  rw [← hAQS] at hs
  obtain ⟨a, ha, q, hq', rfl⟩ := (F1.mem_sup_iff_exists_mul_of_le_normalizer hAN).mp hs
  have hzq : ⁅z, q⁆ = 1 := by
    have hzq' : z * q = q * z := Subgroup.mem_centralizer_iff.mp (hQ2CZ hq') z hz
    rw [commutatorElement_def, hzq']
    group
  have e : ⁅z, a * q⁆ = ⁅z, a⁆ * (a * ⁅z, q⁆ * a⁻¹) := by
    simp only [commutatorElement_def]
    group
  rw [e, hzq, mul_one, mul_inv_cancel, mul_one]
  exact hquad z hz a ha

end CFSG.Quasithin.Stroth

end
