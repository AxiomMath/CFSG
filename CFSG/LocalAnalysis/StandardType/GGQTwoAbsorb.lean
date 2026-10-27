module

public import CFSG.LocalAnalysis.StandardType.GGQTwoPairsBasic
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyDichotomy

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.ComponentClassification

open scoped commutatorElement

private theorem ggQ2x_commutator_zpowers_le {G : Type} [Group G] {X P : Subgroup G} {c : G}
    (hcP : c ∈ Subgroup.normalizer (P : Set G))
    (h : ∀ x ∈ X, ⁅x, c⁆ ∈ P) :
    ⁅X, Subgroup.zpowers c⁆ ≤ P := by
  rw [Subgroup.commutator_le]
  intro x hx z hz
  have hT : ∀ z ∈ Subgroup.zpowers c, ⁅x, z⁆ ∈ P := by
    let T : Subgroup G :=
      { carrier := {z : G | z ∈ Subgroup.normalizer (P : Set G) ∧ ⁅x, z⁆ ∈ P}
        one_mem' := ⟨Subgroup.one_mem _, by simp⟩
        mul_mem' := by
          intro y z hy hz
          obtain ⟨hyN, hyP⟩ := hy
          obtain ⟨hzN, hzP⟩ := hz
          refine ⟨Subgroup.mul_mem _ hyN hzN, ?_⟩
          have h1 : ⁅x, y * z⁆ = ⁅x, y⁆ * (y * ⁅x, z⁆ * y⁻¹) := by
            rw [commutatorElement_def, commutatorElement_def]
            group
          rw [h1]
          exact P.mul_mem hyP ((Subgroup.mem_normalizer_iff.mp hyN _).mp hzP)
        inv_mem' := by
          intro y hy
          obtain ⟨hyN, hyP⟩ := hy
          refine ⟨Subgroup.inv_mem _ hyN, ?_⟩
          have h1 : ⁅x, y⁻¹⁆ = y⁻¹ * ⁅x, y⁆⁻¹ * y := by
            rw [commutatorElement_def, commutatorElement_def]
            group
          have h2 : y⁻¹ * ⁅x, y⁆ * y ∈ P := by
            have h3 := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hyN) _).mp hyP
            simpa only [inv_inv] using h3
          rw [h1]
          simpa only [mul_inv_rev, inv_inv, mul_assoc] using Subgroup.inv_mem _ h2 }
    have hcT : c ∈ T := ⟨hcP, h x hx⟩
    intro z hz
    exact (Subgroup.zpowers_le.mpr hcT hz).2
  exact hT z hz

theorem ggQ2_absorb {G : Type} [Group G] [Finite G] (hLB : GGLBalanceInput) {p : ℕ}
    {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hHyp : GGCorFiveTwentyHyp p B Bs x L D J) {w : G} {F X Q : Subgroup G}
    (hFBs : F ≤ Bs) (hwF : w ∈ F) (hX : GGStdPair p Bs w X)
    (hQ : LargeEvenPComponent p (Subgroup.centralizer (F : Set G)) Q)
    (hQa : ggAutomizer Q Bs ≠ ⊥) : Q ≤ X := by
  classical
  obtain ⟨hcfg, -, -, hNoTr, -⟩ := hHyp
  obtain ⟨hI, hBs, -⟩ := hcfg
  haveI : IsSimpleGroup G := hI.1
  have hp : p.Prime := hI.2.2.2.2.2.1.1
  haveI : Fact p.Prime := ⟨hp⟩
  have hBsabel : IsElemAbelian p Bs := hBs.2.1
  have hcomm : ∀ a ∈ Bs, ∀ b ∈ Bs, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hBsabel.1.is_comm.comm (⟨a, ha⟩ : ↥Bs) ⟨b, hb⟩)
  have hexp : ∀ b ∈ Bs, b ^ p = 1 := hBsabel.2
  have hwBs : w ∈ Bs := hX.1
  let Y : Subgroup G := Subgroup.centralizer ({w} : Set G)
  have hQF : Q ≤ Subgroup.centralizer (F : Set G) :=
    ((largeEvenPComponent_iff_lBalance p (Subgroup.centralizer (F : Set G)) Q).1 hQ).1
  have hQY : Q ≤ Y := hQF.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hwF))
  have hBsY : Bs ≤ Y := fun b hb =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hcomm w hwBs b hb).symm
  have hYne : Y ≠ ⊤ := centralizer_singleton_ne_top_of_isSimpleGroup hI.2.1 hX.2.1
  have hYK : CFSG.Open.lBalanceIsKGroup ↥Y := lBalanceIsKGroup_of_kProper hI.2.2.1 hYne
  have hXpc : CFSG.Open.lBalanceIsPComponent p Y X :=
    ((largeEvenPComponent_iff_lBalance p Y X).1 hX.2.2.1).2
  have hTpc : CFSG.Open.lBalanceIsPComponent p (Subgroup.centralizer (F : Set G)) Q :=
    ((largeEvenPComponent_iff_lBalance p (Subgroup.centralizer (F : Set G)) Q).1 hQ).2
  rcases GGDichotomy.dichotomy_core hLB hp hcomm hexp hFBs hwF hYK hX.2.2.2.1 hXpc hTpc with
    hQX | hcommQ
  · exact hQX
  · exfalso
    let O : Subgroup G := CFSG.Open.lBalancePrimeCore p Y
    have hXY : X ≤ Y := ((largeEvenPComponent_iff_lBalance p Y X).1 hX.2.2.1).1
    have hOn : Y ≤ Subgroup.normalizer (O : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer (LBalance.primeCore_le p Y)).mp
        (LBalance.primeCore_normal p Y)
    have hXO : X ⊓ O ≤ LargeEvenPPrimeCoreOf p X := by
      have hK : ((X ⊓ O).subgroupOf X) ≤ CFSG.pPrimeCore p X := by
        apply le_sSup
        refine ⟨?_, ?_⟩
        · rw [Subgroup.normal_subgroupOf_iff inf_le_left]
          intro y k hy hk
          obtain ⟨hyX, hyO⟩ := hy
          refine ⟨X.mul_mem (X.mul_mem hk hyX) (X.inv_mem hk), ?_⟩
          exact (Subgroup.mem_normalizer_iff.mp (hOn (hXY hk)) y).mp hyO
        · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv]
          exact (LBalance.primeCore_coprime p Y).of_dvd_right
            (Subgroup.card_dvd_of_le inf_le_right)
      calc X ⊓ O = ((X ⊓ O).subgroupOf X).map X.subtype :=
            (Subgroup.map_subgroupOf_eq_of_le inf_le_left).symm
        _ ≤ (CFSG.pPrimeCore p X).map X.subtype := Subgroup.map_mono hK
    have hgen : ∃ φ ∈ ggInduced Q Bs, φ ≠ 1 := by
      by_contra hcon
      apply hQa
      rw [ggAutomizer, Subgroup.closure_eq_bot_iff]
      intro φ hφ
      by_contra hφ1
      exact hcon ⟨φ, hφ, fun h => hφ1 (by simp [h])⟩
    obtain ⟨φ, hφS, hφne⟩ := hgen
    obtain ⟨n, hnQ, hnN, hφg⟩ := hφS
    have hφA : φ ∈ ggInduced ⊤ Bs := ⟨n, Subgroup.mem_top n, hnN, hφg⟩
    have hnY : n ∈ Y := hQY hnQ
    have hnw : n * w * n⁻¹ = w := by
      have h1 : w * n = n * w := (Subgroup.mem_centralizer_iff.mp (hQF hnQ)) w hwF
      rw [← h1, mul_inv_cancel_right]
    have hmem : ∀ b ∈ Bs, ⁅n, b⁆ ∈ Subgroup.zpowers w := by
      intro b hb
      set h : G := b * n * b⁻¹ with hhdef
      set c : G := n * h⁻¹ with hcdef
      have hc_eq : c = ⁅n, b⁆ := by
        rw [hcdef, hhdef, commutatorElement_def]
        group
      have hcBs : c ∈ Bs := by
        have h1 : n * b * n⁻¹ ∈ Bs := (Subgroup.mem_normalizer_iff.mp hnN b).mp hb
        rw [hc_eq, commutatorElement_def]
        exact Bs.mul_mem h1 (Bs.inv_mem hb)
      have hcN : c ∈ Subgroup.normalizer (X : Set G) := hX.2.2.2.1 hcBs
      have hcP : c ∈ Subgroup.normalizer (LargeEvenPPrimeCoreOf p X : Set G) :=
        mem_normalizer_largeEvenPPrimeCoreOf hcN
      have hhY : h ∈ Y := by
        rw [hhdef]
        exact Y.mul_mem (Y.mul_mem (hBsY hb) hnY) (Y.inv_mem (hBsY hb))
      have hxc : ∀ z ∈ X, ⁅z, c⁆ ∈ LargeEvenPPrimeCoreOf p X := by
        intro z hz
        have hhz : ⁅h, z⁆ ∈ O := by
          have hbz : b⁻¹ * z * b ∈ X := by
            have hbN : b⁻¹ ∈ Subgroup.normalizer (X : Set G) :=
              Subgroup.inv_mem _ (hX.2.2.2.1 hb)
            simpa only [inv_inv] using (Subgroup.mem_normalizer_iff.mp hbN z).mp hz
          have h1 : ⁅h, z⁆ = b * ⁅n, b⁻¹ * z * b⁆ * b⁻¹ := by
            rw [hhdef, commutatorElement_def, commutatorElement_def]
            group
          rw [h1]
          exact (Subgroup.mem_normalizer_iff.mp (hOn (hBsY hb)) _).mp
            ((Subgroup.commutator_le.mp hcommQ) n hnQ (b⁻¹ * z * b) hbz)
        have hnz : ⁅n, z⁆ ∈ O := (Subgroup.commutator_le.mp hcommQ) n hnQ z hz
        set o3 : G := (n * ⁅h⁻¹, z⁆ * n⁻¹) * ⁅n, z⁆ with ho3def
        have hhinv : ⁅h⁻¹, z⁆ ∈ O := by
          have h1 : h⁻¹ * ⁅h, z⁆ * h ∈ O := by
            have h3 := (Subgroup.mem_normalizer_iff.mp (hOn (Y.inv_mem hhY)) _).mp hhz
            simpa only [inv_inv] using h3
          have h2 : (h⁻¹ * ⁅h, z⁆ * h)⁻¹ ∈ O := Subgroup.inv_mem _ h1
          have h3 : (h⁻¹ * ⁅h, z⁆ * h)⁻¹ = ⁅h⁻¹, z⁆ := by
            rw [commutatorElement_def, commutatorElement_def]
            group
          rwa [h3] at h2
        have ho3O : o3 ∈ O :=
          O.mul_mem ((Subgroup.mem_normalizer_iff.mp (hOn hnY) _).mp hhinv) hnz
        have hcx : c * z * c⁻¹ = o3 * z := by
          rw [hcdef, ho3def, hhdef]
          simp only [commutatorElement_def]
          group
        have ho3X : o3 ∈ X := by
          have h1 : o3 = (c * z * c⁻¹) * z⁻¹ := by
            rw [hcx]
            group
          rw [h1]
          exact X.mul_mem ((Subgroup.mem_normalizer_iff.mp hcN z).mp hz) (X.inv_mem hz)
        have ho3P : o3 ∈ LargeEvenPPrimeCoreOf p X := hXO ⟨ho3X, ho3O⟩
        have hcz : ⁅c, z⁆ = o3 := by
          rw [commutatorElement_def, hcx]
          group
        have hzc : ⁅z, c⁆ = o3⁻¹ := by
          rw [← commutatorElement_inv c z, hcz]
        rw [hzc]
        exact Subgroup.inv_mem _ ho3P
      have hcommzp : ⁅X, Subgroup.zpowers c⁆ ≤ LargeEvenPPrimeCoreOf p X :=
        ggQ2x_commutator_zpowers_le hcP hxc
      have hmem_c : c ∈ Subgroup.zpowers w := (hX.2.2.2.2.1 c hcBs).mp hcommzp
      rw [← hc_eq]
      exact hmem_c
    have hcommBs : ∀ a b : ↥Bs, a * b = b * a := fun a b => hBsabel.1.is_comm.comm a b
    let δ : ↥Bs →* ↥Bs :=
      { toFun := fun b => b⁻¹ * φ b
        map_one' := by simp
        map_mul' := fun c c' => by
          rw [map_mul, mul_inv_rev, hcommBs c'⁻¹ c⁻¹, mul_assoc, mul_assoc, ← mul_assoc c'⁻¹,
            hcommBs c'⁻¹ (φ c), mul_assoc] }
    let wn : ↥Bs := ⟨w, hwBs⟩
    let Pw : Subgroup ↥Bs := Subgroup.zpowers wn
    have hPwcard : Nat.card Pw = p := by
      change Nat.card (Subgroup.zpowers wn) = p
      rw [Nat.card_zpowers]
      exact orderOf_eq_prime (Subtype.ext (by simp only [Subgroup.coe_pow]; exact hexp w hwBs))
        (fun hh => hX.2.1 (Subtype.ext_iff.mp hh))
    have hPwmap : Pw.map Bs.subtype = Subgroup.zpowers w := by
      change (Subgroup.zpowers wn).map Bs.subtype = Subgroup.zpowers w
      rw [MonoidHom.map_zpowers]
      rfl
    have hrange_le_Pw : δ.range ≤ Pw := by
      rintro y ⟨b, rfl⟩
      have hG : ((δ b : ↥Bs) : G) ∈ Subgroup.zpowers w := by
        have h1 : ((δ b : ↥Bs) : G) = (b : G)⁻¹ * ⁅n, (b : G)⁆ * (b : G) := by
          change ((b⁻¹ * φ b : ↥Bs) : G) = _
          rw [Subgroup.coe_mul, Subgroup.coe_inv, hφg b, commutatorElement_def]
          group
        rw [h1]
        obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hmem b b.2)
        have hbw : (b : G) * w = w * (b : G) := hcomm b b.2 w hwBs
        have hconj : (b : G)⁻¹ * w * (b : G) = w := by
          calc (b : G)⁻¹ * w * (b : G) = (b : G)⁻¹ * (w * (b : G)) := by rw [mul_assoc]
            _ = (b : G)⁻¹ * ((b : G) * w) := by rw [← hbw]
            _ = w := by rw [← mul_assoc, inv_mul_cancel, one_mul]
        have hconjpow : (b : G)⁻¹ * w ^ k * (b : G) = w ^ k := by
          have h := conj_zpow (a := (b : G)⁻¹) (b := w) (i := k)
          rw [inv_inv] at h
          rw [← h, hconj]
        rw [← hk, hconjpow]
        exact Subgroup.mem_zpowers_iff.mpr ⟨k, rfl⟩
      rw [← hPwmap] at hG
      exact (Subgroup.mem_map_iff_mem Bs.subtype_injective).mp hG
    have hδker : ∀ b : ↥Bs, b ∈ δ.ker ↔ φ b = b := by
      intro b
      rw [MonoidHom.mem_ker, show δ b = b⁻¹ * φ b from rfl, inv_mul_eq_one, eq_comm]
    have hrange_ne_bot : δ.range ≠ ⊥ := by
      intro hbot
      apply hφne
      ext b
      have h1 : δ b ∈ δ.range := ⟨b, rfl⟩
      rw [hbot] at h1
      have h2 : δ b = 1 := Subgroup.mem_bot.mp h1
      rw [show δ b = b⁻¹ * φ b from rfl, inv_mul_eq_one] at h2
      simpa using h2.symm
    have hrange_card_dvd : Nat.card δ.range ∣ p := by
      have h1 := Subgroup.card_dvd_of_le hrange_le_Pw
      rwa [hPwcard] at h1
    have hrange_card : Nat.card δ.range = p := by
      rcases (Nat.dvd_prime hp).mp hrange_card_dvd with h1 | h2
      · exact absurd (Subgroup.eq_bot_of_card_eq δ.range h1) hrange_ne_bot
      · exact h2
    have hcard : Nat.card {b : ↥Bs // φ b = b} * p = Nat.card ↥Bs := by
      have hker := Subgroup.card_ker_mul_card_range δ
      rw [hrange_card] at hker
      have hcongr : Nat.card δ.ker = Nat.card {b : ↥Bs // φ b = b} :=
        Nat.card_congr (Equiv.subtypeEquivRight hδker)
      rw [← hcongr]
      exact hker
    have hφwn : φ wn = wn := by
      apply Subtype.ext
      rw [hφg wn]
      exact hnw
    have hfixmem : ∀ y ∈ Pw, φ y = y := by
      intro y hy
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hy
      rw [← hk, map_zpow, hφwn]
    have htrans : GGIsTransvection p φ := ⟨hcard, fun b => by
      change φ (b⁻¹ * φ b) = b⁻¹ * φ b
      have h1 : φ (δ b) = δ b := hfixmem (δ b) (hrange_le_Pw ⟨b, rfl⟩)
      exact h1⟩
    exact hNoTr φ hφA htrans

end CFSG.StandardType

end
