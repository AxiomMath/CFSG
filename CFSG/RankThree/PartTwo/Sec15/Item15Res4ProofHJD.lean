module

public import CFSG.RankThree.PartTwo.Sec15.Item15Res4ProofTools
public import CFSG.RankThree.PartTwo.Sec17.RouteForms
import CFSG.RankThree.PartTwo.Sec14.Concl142HJPoint
import CFSG.RankThree.PartTwo.Sec14.Item1417
import CFSG.RankThree.PartTwo.Sec4.Sporadic.Item415
public import CFSG.Monster.B.TwoA.Census.PermClasses
public import CFSG.RankThree.PartTwo.Sec14.Item1411HJ
public import CFSG.RankThree.PartTwo.Sec15.Item15Res2ProofHJ

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

@[expose] def Passage1515 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Q : Subgroup G), IsPGroup 2 Q → ∀ c d : G,
    c * d = d * c → c ^ 3 = 1 → d ^ 3 = 1 →
    c ∈ Subgroup.normalizer (Q : Set G) → d ∈ Subgroup.normalizer (Q : Set G) →
    Q ⊓ Subgroup.centralizer ({c * d} : Set G) ≤ Subgroup.centralizer ({d} : Set G) →
    Q ⊓ Subgroup.centralizer ({c * d⁻¹} : Set G) ≤ Subgroup.centralizer ({d} : Set G) →
      ⁅Q, Subgroup.zpowers c⁆ ≤ Subgroup.centralizer ({d} : Set G)

variable {G : Type} [Group G] [Finite G] {A L Y : Subgroup G} {c : G}

namespace Proof15Res4

omit [Finite G] in
theorem mem_normalizer_of_map_conj_eq_self {H : Subgroup G} {g : G}
    (h : H.map (MulAut.conj g).toMonoidHom = H) : g ∈ Subgroup.normalizer (H : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    rw [← h]
    exact ⟨x, hx, rfl⟩
  · intro hx
    rw [← h] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    have : y = x := by
      simpa [MulAut.conj_apply] using hyx
    exact this ▸ hy

omit [Finite G] in
theorem map_conj_eq_self_of_mem_normalizer {H : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (H : Set G)) : H.map (MulAut.conj g).toMonoidHom = H := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hg y).mp hy
  · intro hx
    refine ⟨g⁻¹ * x * g, ?_, by simp [MulAut.conj_apply, mul_assoc]⟩
    have := (Subgroup.mem_normalizer_iff.mp (inv_mem hg) x).mp hx
    simpa [mul_assoc] using this

omit [Finite G] in
theorem map_conj_zpowers (w c : G) :
    (Subgroup.zpowers c).map (MulAut.conj w).toMonoidHom = Subgroup.zpowers (w * c * w⁻¹) := by
  rw [MonoidHom.map_zpowers]
  rfl

omit [Finite G] in
theorem mem_of_isZCentral {L : Subgroup G} {d : G} (h : IsZCentral L d) : d ∈ L := by
  obtain ⟨S, hS, hZ⟩ := h
  have hd : d ∈ (Subgroup.center S).map S.subtype := hZ ▸ Subgroup.mem_zpowers d
  obtain ⟨s, -, rfl⟩ := hd
  exact hS.le s.2

omit [Finite G] in
theorem mem_normalizer_centralizer {d w : G}
    (hw : w ∈ Subgroup.normalizer (Subgroup.zpowers d : Set G)) :
    w ∈ Subgroup.normalizer (Subgroup.centralizer ({d} : Set G) : Set G) := by
  have key : ∀ g ∈ Subgroup.normalizer (Subgroup.zpowers d : Set G), ∀ x : G,
      x ∈ Subgroup.centralizer ({d} : Set G) →
        g * x * g⁻¹ ∈ Subgroup.centralizer ({d} : Set G) := by
    intro g hg x hx
    rw [Subgroup.mem_centralizer_singleton_iff] at hx ⊢
    have hd' : g⁻¹ * d * g ∈ Subgroup.zpowers d := by
      have := (Subgroup.mem_normalizer_iff.mp (inv_mem hg) d).mp (Subgroup.mem_zpowers d)
      simpa using this
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hd'
    have hxk : x * d ^ k = d ^ k * x := (Commute.zpow_right hx k).eq
    calc g * x * g⁻¹ * d = g * (x * (g⁻¹ * d * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * d * g) * x) * g⁻¹ := by rw [← hk, hxk]
      _ = d * (g * x * g⁻¹) := by group
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨key w hw x, fun hx => ?_⟩
  have := key w⁻¹ (inv_mem hw) _ hx
  simpa [mul_assoc] using this

omit [Finite G] in
theorem map_conj_one (H : Subgroup G) : H.map (MulAut.conj (1 : G)).toMonoidHom = H := by
  ext x
  simp

omit [Finite G] in
theorem map_conj_mul (g h : G) (H : Subgroup G) :
    H.map (MulAut.conj (g * h)).toMonoidHom =
      (H.map (MulAut.conj h).toMonoidHom).map (MulAut.conj g).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

theorem map_conj_mem_scriptQPi' {w : G} (hw : w ∈ Subgroup.normalizer (A : Set G))
    {Y Q : Subgroup G} {π : Set Nat.Primes} (hQ : Q ∈ scriptQPi A (lB A) Y π) :
    Q.map (MulAut.conj w).toMonoidHom ∈
      scriptQPi A (lB A) (Y.map (MulAut.conj w).toMonoidHom) π :=
  ⟨⟨rank3II_14_4_5_lB hw hQ.1.1, Subgroup.map_mono hQ.1.2⟩,
    fun q hq => hQ.2 q (by rwa [Subgroup.card_map_of_injective (MulAut.conj w).injective] at hq)⟩

theorem map_conj_mem_scriptQPiStar' {w : G} (hw : w ∈ Subgroup.normalizer (A : Set G))
    {Y Q : Subgroup G} {π : Set Nat.Primes} (hQ : Q ∈ scriptQPiStar A (lB A) Y π) :
    Q.map (MulAut.conj w).toMonoidHom ∈
      scriptQPiStar A (lB A) (Y.map (MulAut.conj w).toMonoidHom) π := by
  refine ⟨map_conj_mem_scriptQPi' hw hQ.prop, fun V hV hle => ?_⟩
  have hV' := map_conj_mem_scriptQPi' (inv_mem hw) hV
  rw [← map_conj_mul, inv_mul_cancel, map_conj_one] at hV'
  have hle' : Q ≤ V.map (MulAut.conj w⁻¹).toMonoidHom := by
    have h := Subgroup.map_mono (f := (MulAut.conj w⁻¹).toMonoidHom) hle
    rwa [← map_conj_mul, inv_mul_cancel, map_conj_one] at h
  have h := Subgroup.map_mono (f := (MulAut.conj w).toMonoidHom) (hQ.2 hV' hle')
  rwa [← map_conj_mul, mul_inv_cancel, map_conj_one] at h

theorem conj_eq_of_mem_coprime {A Y' : Subgroup G} (hA : IsPGroup 3 A)
    (hY' : Nat.Coprime 3 (Nat.card Y')) (hAY' : A ≤ Subgroup.normalizer (Y' : Set G))
    {y : G} (hyA : y ∈ Subgroup.normalizer (A : Set G)) (hyY' : y ∈ Y') {a : G} (ha : a ∈ A) :
    y⁻¹ * a * y = a := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hz1 : y⁻¹ * a * y * a⁻¹ ∈ A := by
    have := (Subgroup.mem_normalizer_iff.mp (inv_mem hyA) a).mp ha
    exact A.mul_mem (by simpa using this) (A.inv_mem ha)
  have hz2 : y⁻¹ * a * y * a⁻¹ ∈ Y' := by
    have h1 : a * y * a⁻¹ ∈ Y' := (Subgroup.mem_normalizer_iff.mp (hAY' ha) y).mp hyY'
    have : y⁻¹ * a * y * a⁻¹ = y⁻¹ * (a * y * a⁻¹) := by group
    rw [this]
    exact Y'.mul_mem (Y'.inv_mem hyY') h1
  have hbot : A ⊓ Y' = ⊥ := by
    obtain ⟨n, hn⟩ := (hA.to_le (inf_le_left : A ⊓ Y' ≤ A)).exists_card_eq
    have hdvd : Nat.card (A ⊓ Y' : Subgroup G) ∣ Nat.card Y' :=
      Subgroup.card_dvd_of_le inf_le_right
    have hcop : Nat.Coprime (3 ^ n) (Nat.card Y') := Nat.Coprime.pow_left n hY'
    have h1 : Nat.card (A ⊓ Y' : Subgroup G) = 1 :=
      Nat.eq_one_of_dvd_coprimes hcop (hn ▸ dvd_refl _) hdvd
    exact Subgroup.eq_bot_of_card_eq _ h1
  have hz : y⁻¹ * a * y * a⁻¹ = 1 := by
    have : y⁻¹ * a * y * a⁻¹ ∈ A ⊓ Y' := ⟨hz1, hz2⟩
    rwa [hbot, Subgroup.mem_bot] at this
  calc y⁻¹ * a * y = y⁻¹ * a * y * a⁻¹ * a := by group
    _ = a := by rw [hz, one_mul]

end Proof15Res4

open Proof15Res4

section Certificates


theorem Conf1515HJ.exists_isZCentral (h : Conf1515HJ A c L Y) :
    ∃ d ∈ A, d ≠ 1 ∧ IsZCentral L d := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨d, hdA, hd1, hdL, S, hdS, hSd⟩ := exists_three_central_of_j2 h.sec13Data h.j2
  obtain ⟨-, -, hθ3, -⟩ :=
    solvable_prime_complement_core_characterization (H := ↥L) Nat.prime_three
  obtain ⟨hS, hZ⟩ :=
    center_sylow_eq_zpowers_of_quot_j2 Sec4.Sporadic.rank3II_4_15 hθ3 h.j2 hdL hd1 S hdS hSd
  exact ⟨d, hdA, hd1, _, hS, hZ⟩

theorem Conf1515HJ.not_mem_L (h : Conf1515HJ A c L Y) : c ∉ L :=
  (j2_point_facts h.sec13Data h.j2).1

theorem Conf1515HJ.facts_mul_pow (h : Conf1515HJ A c L Y) {d : G} (hd1 : d ≠ 1)
    (hdZ : IsZCentral L d) {k : ℤ} (hk : k = 1 ∨ k = -1) :
    c * d ^ k ∈ Subgroup.closure {c, d} ∧ c * d ^ k ∉ Subgroup.zpowers d ∧
      ∀ x : G, Subgroup.zpowers x = Subgroup.zpowers (c * d ^ k) → x ∉ Subgroup.zpowers c := by
  have hD := h.sec13Data
  have hdL : d ∈ L := mem_of_isZCentral hdZ
  have hcL := h.not_mem_L
  have hcB : c ∈ Subgroup.closure {c, d} := Subgroup.subset_closure (Set.mem_insert c _)
  have hdB : d ∈ Subgroup.closure {c, d} :=
    Subgroup.subset_closure (Set.mem_insert_of_mem c rfl)
  refine ⟨Subgroup.mul_mem _ hcB (Subgroup.zpow_mem _ hdB k), fun hmem => ?_, fun x hx hxc => ?_⟩
  ·
    apply hcL
    have : c = c * d ^ k * (d ^ k)⁻¹ := by group
    rw [this]
    exact L.mul_mem ((Subgroup.zpowers_le.mpr hdL) hmem)
      (L.inv_mem (L.zpow_mem hdL k))
  ·
    have hcdk : c * d ^ k ∈ Subgroup.zpowers c := by
      have : c * d ^ k ∈ Subgroup.zpowers x := hx ▸ Subgroup.mem_zpowers _
      exact (Subgroup.zpowers_le.mpr hxc) this
    have hdk : d ^ k ∈ Subgroup.zpowers c := by
      have : d ^ k = c⁻¹ * (c * d ^ k) := by group
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mem_zpowers c)) hcdk
    have hdc : d ∈ Subgroup.zpowers c := by
      rcases hk with rfl | rfl
      · simpa using hdk
      · have := Subgroup.inv_mem _ hdk
        simpa using this
    have hle : Subgroup.zpowers d ≤ Subgroup.zpowers c := Subgroup.zpowers_le.mpr hdc
    have hd3 : Nat.card (Subgroup.zpowers d) ∣ 3 := by
      rw [← hD.card_zpowers]
      exact Subgroup.card_dvd_of_le hle
    have hdne : Nat.card (Subgroup.zpowers d) ≠ 1 := by
      intro h1
      apply hd1
      have : Subgroup.zpowers d = ⊥ := Subgroup.eq_bot_of_card_eq _ h1
      rwa [Subgroup.zpowers_eq_bot] at this
    have hcard : Nat.card (Subgroup.zpowers d) = 3 := by
      rcases (Nat.dvd_prime Nat.prime_three).mp hd3 with h1 | h3
      · exact absurd h1 hdne
      · exact h3
    have heq : Subgroup.zpowers d = Subgroup.zpowers c :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, hD.card_zpowers])
    apply hcL
    have : c ∈ Subgroup.zpowers d := heq ▸ Subgroup.mem_zpowers c
    exact (Subgroup.zpowers_le.mpr hdL) this

theorem Conf1515HJ.inf_centralizer_le (h : Conf1515HJ A c L Y) (hT : Step1515HJTrans)
    (hC : Step1515HJConj) {d : G} (hdA : d ∈ A) (hd1 : d ≠ 1) (hdZ : IsZCentral L d)
    {k : ℤ} (hk : k = 1 ∨ k = -1) :
    CFSG.Open.pCoreOf 2 Y ⊓ Subgroup.centralizer ({c * d ^ k} : Set G) ≤
      Subgroup.centralizer ({d} : Set G) := by
  obtain ⟨hB, hnd, hnc⟩ := h.facts_mul_pow hd1 hdZ hk
  obtain ⟨w, hwA, hwd, hwc⟩ := hT G A c L h.sec15R h.j2 h.omega_ne d hdA hd1 hdZ _ hB hnd
  rw [map_conj_zpowers] at hwc
  have hwcB : w * c * w⁻¹ ∈ Subgroup.closure {c, d} :=
    (Subgroup.zpowers_le.mpr hB) (hwc ▸ Subgroup.mem_zpowers _)
  have hwcn : w * c * w⁻¹ ∉ Subgroup.zpowers c := hnc _ hwc
  have hCeq : Subgroup.centralizer ({w * c * w⁻¹} : Set G) =
      Subgroup.centralizer ({c * d ^ k} : Set G) := centralizer_singleton_eq_of_zpowers_eq hwc
  have hU : ⁅CFSG.Open.pCoreOf 2 Y ⊓ Subgroup.centralizer ({w * c * w⁻¹} : Set G),
      Subgroup.zpowers d⁆ = ⊥ := by
    by_contra hne
    have hYw := hC G A c L Y h d hdA hd1 hdZ w hwA hwd hwcB hwcn hne
    exact hwcn (h.conj_mem_zpowers hwA (mem_normalizer_of_map_conj_eq_self hYw))
  rw [hCeq] at hU
  intro x hx
  have hxd := (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hU) hx
  rw [Subgroup.mem_centralizer_iff] at hxd
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact (hxd d (Subgroup.mem_zpowers d)).symm

theorem Conf1515HJ.commutator_le_centralizer (h : Conf1515HJ A c L Y) (hT : Step1515HJTrans)
    (hC : Step1515HJConj) (hP : Passage1515) {d : G} (hdA : d ∈ A) (hd1 : d ≠ 1)
    (hdZ : IsZCentral L d) :
    ⁅CFSG.Open.pCoreOf 2 Y, Subgroup.zpowers c⁆ ≤ Subgroup.centralizer ({d} : Set G) := by
  have hD := h.sec13Data
  have h1 := h.inf_centralizer_le hT hC hdA hd1 hdZ (k := 1) (Or.inl rfl)
  have h2 := h.inf_centralizer_le hT hC hdA hd1 hdZ (k := -1) (Or.inr rfl)
  rw [zpow_one] at h1
  rw [zpow_neg, zpow_one] at h2
  exact hP G _ (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y) c d (hD.commute hD.mem_A hdA)
    (hD.isElemAbelian.2 c hD.mem_A) (hD.isElemAbelian.2 d hdA)
    (h.A_le_normalizer_pCoreOf hD.mem_A) (h.A_le_normalizer_pCoreOf hdA) h1 h2

theorem Conf1515HJ.odd_card (h : Conf1515HJ A c L Y) (hT : Step1515HJTrans)
    (hQN : Step1515HJQN) (hloc : Claim1411LocalR) {d : G} (hdA : d ∈ A) (hd1 : d ≠ 1)
    (hdZ : IsZCentral L d) :
    Odd (Nat.card ↥(Subgroup.normalizer (Y : Set G) ⊓
      pPrimeCoreOf 3 (Subgroup.centralizer ({d} : Set G)))) := by
  by_contra hodd
  have hD := h.sec13Data
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨Q, hQ, hQY⟩ := hQN G A c L Y h d hdA hd1 hdZ hodd
  obtain ⟨hB, hnd, hnc⟩ := h.facts_mul_pow hd1 hdZ (k := 1) (Or.inl rfl)
  obtain ⟨w, hwA, hwd, hwc⟩ := hT G A c L h.sec15R h.j2 h.omega_ne d hdA hd1 hdZ _ hB hnd
  rw [map_conj_zpowers] at hwc
  have hwcn : w * c * w⁻¹ ∉ Subgroup.zpowers c := hnc _ hwc
  set Y' := pPrimeCoreOf 3 (Subgroup.centralizer ({d} : Set G)) with hY'
  have hwY' : w ∈ Subgroup.normalizer (Y' : Set G) :=
    normalizer_le_normalizer_pPrimeCoreOf 3 _ (mem_normalizer_centralizer hwd)
  have hQw : Q.map (MulAut.conj w).toMonoidHom ∈ scriptQPiStar A (lB A) Y' (piOf 2) := by
    have := map_conj_mem_scriptQPiStar' hwA hQ
    rwa [map_conj_eq_self_of_mem_normalizer hwY'] at this
  have hAC : A ≤ Subgroup.centralizer ({d} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hD.commute hx hdA)
  have hAY' : A ≤ Subgroup.normalizer (Y' : Set G) :=
    (hAC.trans Subgroup.le_normalizer).trans (normalizer_le_normalizer_pPrimeCoreOf 3 _)
  have hY'Y : Y' ∈ scriptY A := by
    refine ⟨fun htop => ?_, hAY'⟩
    apply centralizer_singleton_ne_top hD.isSimpleGroup hD.nonabelian hd1
    exact eq_top_iff.mpr (htop ▸ pPrimeCoreOf_le 3 _)
  obtain ⟨y, hy, hyQ⟩ := (hloc G A c L h.sec15R).1 Y' hY'Y Q hQ _ hQw
  have hw'Q : (y⁻¹ * w) ∈ Subgroup.normalizer (Q : Set G) := by
    refine mem_normalizer_of_map_conj_eq_self ?_
    rw [map_conj_mul, hyQ, ← map_conj_mul, inv_mul_cancel, map_conj_one]
  have hw'A : (y⁻¹ * w) ∈ Subgroup.normalizer (A : Set G) := mul_mem (inv_mem hy.1) hwA
  have hA3 : IsPGroup 3 A := IsPGroup.of_card (n := 3) (by rw [hD.card_eq]; norm_num)
  have hyA : ∀ a ∈ A, y⁻¹ * a * y = a := fun a ha =>
    conj_eq_of_mem_coprime hA3 (coprime_card_pPrimeCoreOf 3 _) hAY' hy.1 hy.2 ha
  set B := Subgroup.closure ({c, d} : Set G) with hBdef
  have hdB : d ∈ B := Subgroup.subset_closure (Set.mem_insert_of_mem c rfl)
  have hBA : B ≤ A := by
    rw [hBdef, Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact hD.mem_A
    · exact hdA
  have hwB : B ≤ B.comap (MulAut.conj w).toMonoidHom := by
    rw [hBdef, Subgroup.closure_le]
    rintro x (rfl | rfl)
    · rw [SetLike.mem_coe, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      exact (Subgroup.zpowers_le.mpr hB) (hwc ▸ Subgroup.mem_zpowers _)
    · rw [SetLike.mem_coe, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      exact (Subgroup.zpowers_le.mpr hdB)
        ((Subgroup.mem_normalizer_iff.mp hwd x).mp (Subgroup.mem_zpowers x))
  have hw'B : (y⁻¹ * w) ∈ Subgroup.normalizer (B : Set G) := by
    refine mem_normalizer_of_map_conj_eq_self (Subgroup.eq_of_le_of_card_ge ?_ ?_)
    · rintro _ ⟨x, hx, rfl⟩
      have h1 : w * x * w⁻¹ ∈ B := by
        have := hwB hx
        rwa [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at this
      have e : (MulAut.conj (y⁻¹ * w)).toMonoidHom x = y⁻¹ * (w * x * w⁻¹) * y := by
        simp [MulAut.conj_apply, mul_assoc]
      rw [e, hyA _ (hBA h1)]
      exact h1
    · rw [Subgroup.card_map_of_injective (MulAut.conj _).injective]
  have hK := h.conj_mem_zpowers hw'A (hQY ⟨⟨hw'A, hw'Q⟩, hw'B⟩)
  have hwcA : w * c * w⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp hwA c).mp hD.mem_A
  apply hwcn
  have e : y⁻¹ * w * c * (y⁻¹ * w)⁻¹ = y⁻¹ * (w * c * w⁻¹) * y := by group
  rw [e, hyA _ hwcA] at hK
  exact hK

theorem step1515HJD_of (hT : Step1515HJTrans) (hC : Step1515HJConj) (hQN : Step1515HJQN)
    (hloc : Claim1411LocalR) (hP : Passage1515) : Step1515HJD := by
  intro G _ _ A c L hR hJ Y hY hm hYL hLY hΩ
  have h : Conf1515HJ A c L Y := ⟨hR, hJ, hY, hm, hYL, hLY, hΩ⟩
  obtain ⟨d, hdA, hd1, hdZ⟩ := h.exists_isZCentral
  exact ⟨d, hdA, hd1, hdZ, h.commutator_le_centralizer hT hC hP hdA hd1 hdZ,
    h.odd_card hT hQN hloc hdA hd1 hdZ⟩

end Certificates

end CFSG.RankThree.PartTwo.Sec15
