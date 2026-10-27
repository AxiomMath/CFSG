module

public import CFSG.RankThree.PartTwo.Sec11.Item1117Res7ProofZ9
import CFSG.RankThree.PartTwo.Sec11.Item1119Proof
import CFSG.RankThree.PartTwo.Sec4.LThreePiCaseI
import CFSG.RankThree.CentralCover.FourGroupWitness
public import CFSG.RankThree.PartTwo.Sec11.Item1117Res7Proof

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.Assembly.RankThreeEven (projImage)
open scoped commutatorElement Pointwise

namespace Item1117Res7Proof

section Data

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {a : G}
  {R Y : Subgroup G} {d x s r g : G}

theorem conj_mul_inv_ne_one (h45 : Sec4.Item4_5) (h : Sec11Data G A c L a R Y d x s r g)
    {e : G} (heA : e ∈ A) (hecd : e ∉ Subgroup.closure ({c, d} : Set G)) {Y' : Subgroup G}
    (hY' : Y' ∈ thetaComponentsAt 3 e) (hKY' : sec11K L e ≤ Y') :
    x * e * x⁻¹ * e⁻¹ ≠ 1 := by
  intro h1
  have hstdE := h.toSec11Std.change_a h45 h.inf_eq h.closure_eq heA hecd hY' hKY'
  have hxe' : x * e = e * x := by
    calc x * e = (x * e * x⁻¹ * e⁻¹) * e * x := by group
      _ = e * x := by rw [h1, one_mul]
  apply Item1116Proof.not_le_centralizer_of_isSylowOf hstdE (h.inf_L_eq ▸ hstdE.isSylowOf_inf_L)
  rw [Subgroup.zpowers_le]
  exact Subgroup.mem_centralizer_singleton_iff.mpr hxe'

theorem false_of_cyclic (h45 : Sec4.Item4_5) (h118 : Item118) (hK : AutThree1129)
    (h : Sec11Data G A c L a R Y d x s r g) (hx9 : orderOf x = 9) {e : G} (heA : e ∈ A)
    (hecd : e ∉ Subgroup.closure ({c, d} : Set G))
    (hxe : x * e * x⁻¹ * e⁻¹ ∈ Subgroup.zpowers d) (hδ1 : x * e * x⁻¹ * e⁻¹ ≠ 1)
    {Y' : Subgroup G} (hY' : Y' ∈ thetaComponentsAt 3 e) (hKY' : sec11K L e ≤ Y')
    (hP : Sec8.IsZ3PGLThreePi (sec11YA e Y' A)) {Q : Subgroup G}
    (hQ : IsSylowOf 3 Q (Subgroup.centralizer {e}))
    (hTQ : sec11P R g ⊓ Subgroup.centralizer {e} ≤ Q) {v : G}
    (hv : v ∈ Q ⊓ Sec4.thetaQuotCentralizer Y' ⊓ Subgroup.normalizer (A : Set G))
    (hvc : v * c ≠ c * v) (hv3 : v ^ 3 ≠ 1) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hstdE := h.toSec11Std.change_a h45 h.inf_eq h.closure_eq heA hecd hY' hKY'
  have hA' := h.toSec11Std.closure_eq_of_not_mem h.inf_eq h.closure_eq heA hecd
  have hAe := h.mem_partTwoF.1
  have hAc : ∀ u ∈ A, ∀ w ∈ A, u * w = w * u := fun u hu w hw =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨u, hu⟩ ⟨w, hw⟩)
  have hA3 : ∀ u ∈ A, u ^ 3 = 1 := hAe.2
  have he1 : e ≠ 1 := fun he => hecd (he ▸ Subgroup.one_mem _)
  have he3 : e ^ 3 = 1 := hA3 e heA
  have he3o : orderOf e = 3 := orderOf_eq_prime he3 he1
  have hdA := Item1117Proof.d_mem_A h
  have hd3 := Item1117Proof.orderOf_d h
  have hcA := h.mem_A
  have hc3 : c ^ 3 = 1 := hA3 c hcA
  have hc3o : orderOf c = 3 := orderOf_eq_prime hc3 h.ne_one
  have hed : e ∉ Subgroup.zpowers d := fun hm =>
    hecd (Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp)) hm)
  have hAC : A ≤ Subgroup.centralizer ({e} : Set G) := fun y hy =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hAc y hy e heA)
  have hAY : A ≤ Subgroup.normalizer (Y' : Set G) :=
    Sec6.le_normalizer_of_mem_thetaComponentsAt h45 h.toTheoremFourHyp hAe heA he1 Y' hY'
  have hYC : Y' ≤ Subgroup.centralizer ({e} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt hY'
  have hQ3 : IsPGroup 3 Q := hQ.isPGroup
  have hQY : Q ≤ Subgroup.normalizer (Y' : Set G) :=
    Item1117Res4Proof.le_normalizer_of_isPGroup h45 h.toTheoremFourHyp he1 he3 hQ3 hQ.le Y' hY'
  have hAQ : A ≤ Q := fun z hz =>
    hTQ ⟨Item1119Proof.R_le_P R g (Item1115Proof.A_le_R h.toHyp91 hz), hAC hz⟩
  have hdY : d ∈ Y' := hKY' (hstdE.d_mem_sec11K h.inf_eq)
  have hpow : ∀ z ∈ Q, ∃ k : ℕ, z ^ 3 ^ k = 1 := fun z hz => by
    obtain ⟨k, hk⟩ := hQ3 ⟨z, hz⟩
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  have hcT : c ∈ Subgroup.normalizer (Sec4.thetaQuotCentralizer Y' : Set G) :=
    Sec6.normalizer_le_normalizer_thetaQuotCentralizer Y' (hAY hcA)
  set V := Q ⊓ Sec4.thetaQuotCentralizer Y' ⊓ Subgroup.normalizer (A : Set G) with hVdef
  have hVA : ∀ y ∈ V, y ∈ Subgroup.centralizer (A : Set G) → y ∈ Subgroup.zpowers e :=
    fun y hy hyA =>
      Item1117ResProof.mem_zpowers_of_mem_centralizer_A h45 h118 h heA hecd hY' hKY' hQ hTQ hy hyA
  have hVe : ∀ y ∈ V, y * e = e * y := fun y hy =>
    Subgroup.mem_centralizer_singleton_iff.mp (hQ.le hy.1.1)
  have hVd : ∀ y ∈ V, y * d = d * y := fun y hy => by
    obtain ⟨k, hk⟩ := hpow (d⁻¹ * (y * d * y⁻¹)) (Q.mul_mem (Q.inv_mem (hAQ hdA))
      (Q.mul_mem (Q.mul_mem hy.1.1 (hAQ hdA)) (Q.inv_mem hy.1.1)))
    exact commute_of_mem_thetaQuotCentralizer hy.1.2 hdY hk
  have hVa : ∀ y ∈ V, ∀ b ∈ A, y * b * y⁻¹ * b⁻¹ ∈ Subgroup.zpowers e := by
    intro y hy b hb
    have hbN : b ∈ Subgroup.normalizer (Sec4.thetaQuotCentralizer Y' : Set G) :=
      Sec6.normalizer_le_normalizer_thetaQuotCentralizer Y' (hAY hb)
    have hyb : y * b * y⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp hy.2 b).mp hb
    have hmA : y * b * y⁻¹ * b⁻¹ ∈ A := A.mul_mem hyb (A.inv_mem hb)
    refine hVA _ ⟨⟨Q.mul_mem (Q.mul_mem (Q.mul_mem hy.1.1 (hAQ hb)) (Q.inv_mem hy.1.1))
      (Q.inv_mem (hAQ hb)), ?_⟩, Subgroup.le_normalizer hmA⟩ ?_
    · have h1 : b * y⁻¹ * b⁻¹ ∈ Sec4.thetaQuotCentralizer Y' :=
        (Subgroup.mem_normalizer_iff.mp hbN _).mp (Subgroup.inv_mem _ hy.1.2)
      have e1 : y * b * y⁻¹ * b⁻¹ = y * (b * y⁻¹ * b⁻¹) := by group
      rw [e1]
      exact Subgroup.mul_mem _ hy.1.2 h1
    · rw [Subgroup.mem_centralizer_iff]
      intro z hz
      exact hAc z hz _ hmA
  set κ := v * c * v⁻¹ * c⁻¹ with hκdef
  have hκe : κ ∈ Subgroup.zpowers e := hVa v hv c hcA
  have hκ1 : κ ≠ 1 := fun h1 => hvc (by
    calc v * c = (v * c * v⁻¹ * c⁻¹) * c * v := by group
      _ = c * v := by rw [← hκdef, h1, one_mul])
  have hev : ∀ t ∈ Subgroup.zpowers e, v * t = t * v := fun t ht => by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ht
    exact (Commute.zpow_right (show Commute v e from hVe v hv) k).eq
  have hκ3 : κ ^ 3 = 1 := hA3 κ (Subgroup.zpowers_le.mpr heA hκe)
  have hvn := pow_conj_mul_inv_eq (hev κ hκe)
  have hv3c : v ^ 3 * c = c * v ^ 3 := by
    have h1 := hvn 3
    rw [← hκdef, hκ3] at h1
    calc v ^ 3 * c = (v ^ 3 * c * (v ^ 3)⁻¹ * c⁻¹) * c * v ^ 3 := by group
      _ = c * v ^ 3 := by rw [h1, one_mul]
  have hv3V : v ^ 3 ∈ V := V.pow_mem hv 3
  have hcentral : ∀ y ∈ V, y * c = c * y → y ∈ Subgroup.centralizer (A : Set G) := by
    intro y hy hyc
    have hle : A ≤ Subgroup.centralizer ({y} : Set G) := by
      rw [hA', Subgroup.closure_le]
      rintro z (rfl | rfl | rfl)
      · exact Subgroup.mem_centralizer_singleton_iff.mpr hyc.symm
      · exact Subgroup.mem_centralizer_singleton_iff.mpr (hVe y hy).symm
      · exact Subgroup.mem_centralizer_singleton_iff.mpr (hVd y hy).symm
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle hz)
  have hv3e : v ^ 3 ∈ Subgroup.zpowers e := hVA _ hv3V (hcentral _ hv3V hv3c)
  have hev3 : e ∈ Subgroup.zpowers (v ^ 3) := mem_zpowers_of_mem_zpowers he3 hv3e hv3
  have hv9 : orderOf v = 9 := by
    have hv9' : v ^ 3 ^ 2 = 1 := by
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hv3e
      rw [show (3 : ℕ) ^ 2 = 3 * 3 by norm_num, pow_mul, ← hk, ← zpow_natCast, ← zpow_mul,
        mul_comm, zpow_mul, zpow_natCast, he3, one_zpow]
    obtain ⟨i, hi, hio⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp
      (orderOf_dvd_of_pow_eq_one hv9')
    have hi2 : i = 2 := by
      by_contra hne
      have hi1 : i ≤ 1 := by omega
      apply hv3
      refine orderOf_dvd_iff_pow_eq_one.mp ?_
      rw [hio]
      exact (pow_dvd_pow 3 hi1).trans (by norm_num)
    rw [hio, hi2]
    norm_num
  have hVv : ∀ y ∈ V, y ∈ Subgroup.zpowers v := by
    intro y hy
    have hκy := hVa y hy c hcA
    have heκ : e ∈ Subgroup.zpowers κ := mem_zpowers_of_mem_zpowers he3 hκe hκ1
    obtain ⟨m, hm⟩ : ∃ m : ℕ, κ ^ m = y * c * y⁻¹ * c⁻¹ :=
      (mem_powers_iff_mem_zpowers).mpr ((Subgroup.zpowers_le.mpr heκ) hκy)
    have hyv : y * v ^ (2 * m) ∈ V := V.mul_mem hy (V.pow_mem hv _)
    have hκm : ∀ n : ℕ, y * κ ^ n = κ ^ n * y := fun n =>
      (Commute.pow_right (show Commute y κ by
        obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hκe
        rw [← hk]
        exact Commute.zpow_right (show Commute y e from hVe y hy) k) n).eq
    have hyvc : y * v ^ (2 * m) * c = c * (y * v ^ (2 * m)) := by
      have h1 : v ^ (2 * m) * c = κ ^ (2 * m) * c * v ^ (2 * m) := by
        rw [← hvn (2 * m)]; group
      have h2 : y * c = κ ^ m * c * y := by rw [hm]; group
      calc y * v ^ (2 * m) * c = y * κ ^ (2 * m) * c * v ^ (2 * m) := by rw [mul_assoc y, h1]; group
        _ = κ ^ (2 * m) * (y * c) * v ^ (2 * m) := by rw [hκm]; group
        _ = κ ^ (2 * m) * κ ^ m * c * y * v ^ (2 * m) := by rw [h2]; group
        _ = (κ ^ 3) ^ m * c * y * v ^ (2 * m) := by
          rw [← pow_add, ← pow_mul, show 2 * m + m = 3 * m by ring]
        _ = c * (y * v ^ (2 * m)) := by rw [hκ3, one_pow, one_mul]; group
    have hye := hVA _ hyv (hcentral _ hyv hyvc)
    have hy' : y = (y * v ^ (2 * m)) * (v ^ (2 * m))⁻¹ := by group
    rw [hy']
    refine Subgroup.mul_mem _ ?_
      (Subgroup.inv_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers v) _))
    exact (Subgroup.zpowers_le.mpr ((Subgroup.zpowers_le.mpr (Subgroup.pow_mem _
      (Subgroup.mem_zpowers v) 3)) hev3)) hye
  set X₀ := Q ⊓ Sec4.thetaQuotCentralizer Y' with hX₀
  have hX₀v : X₀ ≤ Subgroup.zpowers v := by
    refine Item1118StepsProof.le_of_inf_normalizer_le (p := 3) (A := A ⊔ Subgroup.zpowers v)
      (V := X₀) (E := Subgroup.zpowers v) ?_ ?_ le_sup_right ?_
    · refine sup_le (fun z hz => Subgroup.inf_normalizer_le_normalizer_inf
        ⟨Subgroup.le_normalizer (hAQ hz),
          Sec6.normalizer_le_normalizer_thetaQuotCentralizer Y' (hAY hz)⟩) ?_
      rw [Subgroup.zpowers_le]
      exact Subgroup.le_normalizer hv.1
    · exact hQ3.to_le (sup_le (sup_le hAQ (Subgroup.zpowers_le.mpr hv.1.1)) inf_le_left)
    · rintro y ⟨hyX, hyN⟩
      have hyA : y ∈ Subgroup.normalizer (A : Set G) := by
        refine Subgroup.mem_normalizer_fintype fun b hb => ?_
        refine mem_of_pow_three_eq_one hAc hA3 heA (hVe v hv) hv.2 (hVa v hv) hv9 hv3e
          ((Subgroup.mem_normalizer_iff.mp hyN b).mp (Subgroup.mem_sup_left hb)) ?_
        rw [conj_pow, hA3 b hb, mul_one, mul_inv_cancel]
      exact hVv y ⟨hyX, hyA⟩
  have hX₀9 : Nat.card X₀ ≤ 9 := by
    have := Subgroup.card_le_of_le hX₀v
    rwa [Nat.card_zpowers, hv9] at this
  have hAQ' : ∀ u ∈ A, ∀ w ∈ A, u * w = w * u := hAc
  obtain ⟨π, p, f, K, _, hKf, hq, ⟨φ⟩⟩ := id hP
  have hX : IsList119 (projImage (Sec4.glPi π 3 (p ^ f) K)) :=
    Or.inr (Or.inr (Or.inr (Or.inl ⟨π, p, f, K, inferInstance, hKf, hq, ⟨MulEquiv.refl _⟩⟩)))
  obtain ⟨ψ⟩ := Item1116Proof.nonempty_thetaQuot_equiv_commutator hY' hAC hAY hAQ' φ
  have hQle := hK G Y' (sec11K L e) c ⟨_, inferInstance, hX, ⟨ψ⟩⟩ (hAY hcA) hc3
    (mem_thetaComponentsIn_sec11K_inf hstdE) (kType119 G A c L e R Y' hstdE d h.inf_eq hA')
    (Item1117Res4Proof.card_sec11K_factorization_eq_one h45 h hx9 heA hecd hY' hKY') Q hQ3 hQY
  have hQ243 : Nat.card Q ≤ 243 :=
    hQle.trans ((Nat.mul_le_mul_left 27 hX₀9).trans (by norm_num))
  obtain ⟨hZ, E₀, hE₀Y, hE₀, hE₀9⟩ := facts_of_isZ3PGLThreePi hY' hAC hAY hAc hP
  obtain ⟨E', hE'S, hE', hE'9⟩ := exists_elemAbelian_le_of_isSylowOf
    (isSylowOf_inf_of_le_normalizer hQ hQY hYC) hE₀Y hE₀ hE₀9
  set S₀ := Q ⊓ Y' with hS₀def
  have hvS : ∀ t ∈ S₀, v * t = t * v := fun t ht => by
    obtain ⟨k, hk⟩ := hpow (t⁻¹ * (v * t * v⁻¹)) (Q.mul_mem (Q.inv_mem ht.1)
      (Q.mul_mem (Q.mul_mem hv.1.1 ht.1) (Q.inv_mem hv.1.1)))
    exact commute_of_mem_thetaQuotCentralizer hv.1.2 ht.2 hk
  have hdisj : S₀ ⊓ Subgroup.zpowers v = ⊥ := by
    rw [eq_bot_iff]
    rintro y ⟨hyS, hyv⟩
    obtain ⟨k, hk⟩ := hpow y hyS.1
    exact Subgroup.mem_bot.mpr (eq_one_of_mem_thetaQuotCentralizer hZ hyS.2
      ((Subgroup.zpowers_le.mpr hv.1.2) hyv) hk)
  have hvN : Subgroup.zpowers v ≤ Subgroup.normalizer (S₀ : Set G) := by
    rw [Subgroup.zpowers_le]
    refine Subgroup.mem_normalizer_fintype fun t ht => ?_
    rw [hvS t ht, mul_inv_cancel_right]
    exact ht
  set B := S₀ ⊔ Subgroup.zpowers v with hBdef
  have hBcard : Nat.card B = Nat.card S₀ * 9 := by
    rw [hBdef, CentralCover.card_sup_eq_mul_of_le_normalizer hvN hdisj, Nat.card_zpowers, hv9]
  have hBv : B ≤ Subgroup.centralizer ({v} : Set G) := by
    refine sup_le (fun t ht => Subgroup.mem_centralizer_singleton_iff.mpr (hvS t ht).symm) ?_
    rw [Subgroup.zpowers_le]
    exact Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hcS : c ∈ Subgroup.normalizer (S₀ : Set G) :=
    Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer (hAQ hcA), hAY hcA⟩
  have hcV : c ∈ Subgroup.normalizer (Subgroup.zpowers v : Set G) := by
    refine Sec10.mem_normalizer_zpowers_of_conj_mem (hVv _ ⟨⟨?_, ?_⟩, ?_⟩)
    · exact Q.mul_mem (Q.mul_mem (hAQ hcA) hv.1.1) (Q.inv_mem (hAQ hcA))
    · exact (Subgroup.mem_normalizer_iff.mp hcT v).mp hv.1.2
    · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.le_normalizer hcA) hv.2)
        (Subgroup.inv_mem _ (Subgroup.le_normalizer hcA))
  have hcB : c ∈ Subgroup.normalizer (B : Set G) :=
    Subgroup.inf_normalizer_le_normalizer_sup _ _ ⟨hcS, hcV⟩
  have hcnB : c ∉ B := fun hc => hvc (Subgroup.mem_centralizer_singleton_iff.mp (hBv hc)).symm
  set T := B ⊔ Subgroup.zpowers c with hTdef
  have hTcard : Nat.card T = Nat.card S₀ * 27 := by
    rw [hTdef, CentralCover.card_sup_eq_mul_of_le_normalizer (Subgroup.zpowers_le.mpr hcB)
      (Sec12.inf_zpowers_eq_bot_of_not_mem hc3o hcnB), hBcard, Nat.card_zpowers, hc3o]
    ring
  have hTQ' : T ≤ Q :=
    sup_le (sup_le inf_le_left (Subgroup.zpowers_le.mpr hv.1.1))
      (Subgroup.zpowers_le.mpr (hAQ hcA))
  have hE'card : 9 ≤ Nat.card S₀ := hE'9 ▸ Subgroup.card_le_of_le hE'S
  have hS₀9 : Nat.card S₀ ≤ 9 := by
    have := Subgroup.card_le_of_le hTQ'
    rw [hTcard] at this
    omega
  have hS₀E : E' = S₀ := Subgroup.eq_of_le_of_card_ge hE'S (by rw [hE'9]; exact hS₀9)
  have hQT : T = Q := Subgroup.eq_of_le_of_card_ge hTQ' (by rw [hTcard]; omega)
  have hS₀ab : CFSG.Assembly.IsElemAbelian 3 S₀ := hS₀E ▸ hE'
  have hdS : d ∈ S₀ := ⟨hAQ hdA, hdY⟩
  have hS₀c : ∀ t ∈ S₀, ∀ u ∈ S₀, t * u = u * t := fun t ht u hu =>
    congrArg Subtype.val (hS₀ab.1.is_comm.comm ⟨t, ht⟩ ⟨u, hu⟩)
  have hcd : c * d = d * c := hAc c hcA d hdA
  have hcs : ∀ t ∈ S₀, c * t * c⁻¹ * t⁻¹ ∈ Subgroup.zpowers d := by
    intro t ht
    by_cases htd : t ∈ Subgroup.zpowers d
    · obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp htd
      rw [(Commute.zpow_right (show Commute c d from hcd) k).eq, mul_inv_cancel_right,
        mul_inv_cancel]
      exact Subgroup.one_mem _
    · have hcl : Subgroup.closure ({d, t} : Set G) = S₀ := by
        refine Subgroup.eq_of_le_of_card_ge ?_ ?_
        · rw [Subgroup.closure_le]
          rintro z (rfl | rfl)
          · exact hdS
          · exact ht
        · rw [Set.insert_eq, Subgroup.closure_union, ← Subgroup.zpowers_eq_closure,
            ← Subgroup.zpowers_eq_closure,
            Sec4.card_zpowers_sup_zpowers (hS₀ab.2 t ht) hd3 htd (hS₀c t ht d hdS)]
          exact hS₀9
      have hz : c * t * c⁻¹ ∈ Subgroup.closure ({d, t} : Set G) :=
        hcl ▸ (Subgroup.mem_normalizer_iff.mp hcS t).mp ht
      exact Sec12.conj_mul_inv_mem_zpowers_of_mem_closure (hS₀c d hdS t ht) (hA3 d hdA)
        (hS₀ab.2 t ht) htd hcd (k := 1) (by rw [pow_one]; exact hc3) hz
  set K₀ := Subgroup.zpowers e ⊔ Subgroup.zpowers d with hK₀def
  have hK₀A : K₀ ≤ A := sup_le (Subgroup.zpowers_le.mpr heA) (Subgroup.zpowers_le.mpr hdA)
  have hBC : B ≤ Subgroup.centralizer ({e} : Set G) ⊓ Subgroup.centralizer ({d} : Set G) := by
    refine sup_le (le_inf (inf_le_left.trans hQ.le) fun t ht =>
      Subgroup.mem_centralizer_singleton_iff.mpr (hS₀c t ht d hdS)) ?_
    rw [Subgroup.zpowers_le]
    exact ⟨hQ.le hv.1.1, Subgroup.mem_centralizer_singleton_iff.mpr (hVd v hv)⟩
  have hK₀B : ∀ k ∈ K₀, ∀ b ∈ B, k * b = b * k := by
    have hle : K₀ ≤ Subgroup.centralizer (B : Set G) := by
      refine sup_le ?_ ?_ <;> rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
      · exact fun b hb => (Subgroup.mem_centralizer_singleton_iff.mp (hBC hb).1)
      · exact fun b hb => (Subgroup.mem_centralizer_singleton_iff.mp (hBC hb).2)
    intro k hk b hb
    exact (Subgroup.mem_centralizer_iff.mp (hle hk) b hb).symm
  have hcB' : ∀ b ∈ B, c * b * c⁻¹ * b⁻¹ ∈ K₀ := by
    intro b hb
    have hmem : b ∈ (S₀ : Set G) * (Subgroup.zpowers v : Set G) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left S₀ _ hvN]
      exact hb
    obtain ⟨t, ht, w, hw, rfl⟩ := Set.mem_mul.mp hmem
    have hwV : w ∈ V := (Subgroup.zpowers_le.mpr hv) hw
    have hcw : c * w * c⁻¹ * w⁻¹ ∈ Subgroup.zpowers e := by
      have h1 := hVa _ (V.inv_mem hwV) c hcA
      have h2 : c * w * c⁻¹ * w⁻¹ = w * (w⁻¹ * c * w⁻¹⁻¹ * c⁻¹) * w⁻¹ := by group
      rw [h2]
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h1
      rw [← hk, (Commute.zpow_right (show Commute w e from hVe w hwV) k).eq,
        mul_inv_cancel_right]
      exact Subgroup.zpow_mem_zpowers e k
    have hte : t * (c * w * c⁻¹ * w⁻¹) = (c * w * c⁻¹ * w⁻¹) * t := by
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hcw
      rw [← hk]
      exact (Commute.zpow_right (show Commute t e from
        Subgroup.mem_centralizer_singleton_iff.mp (hQ.le ht.1)) k).eq
    have e1 : c * (t * w) * c⁻¹ * (t * w)⁻¹ =
        (c * t * c⁻¹ * t⁻¹) * (t * (c * w * c⁻¹ * w⁻¹) * t⁻¹) := by group
    rw [e1, hte, mul_inv_cancel_right]
    exact K₀.mul_mem ((le_sup_right : Subgroup.zpowers d ≤ K₀) (hcs t ht))
      ((le_sup_left : Subgroup.zpowers e ≤ K₀) hcw)
  have hcube : ∀ q ∈ Q, q ^ 3 ∈ Subgroup.zpowers e := by
    intro q hq
    rw [← hQT] at hq
    obtain ⟨b, hb, hqb⟩ := exists_pow_three_eq (fun k hk => hA3 k (hK₀A hk)) hK₀B
      (fun k hk => hAc k (hK₀A hk) c hcA) hcB' hcB hc3 hq
    rw [hqb]
    have hmem : b ∈ (S₀ : Set G) * (Subgroup.zpowers v : Set G) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left S₀ _ hvN]
      exact hb
    obtain ⟨t, ht, w, hw, rfl⟩ := Set.mem_mul.mp hmem
    have htw : Commute t w := by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
      exact (Commute.zpow_right (show Commute t v from (hvS t ht).symm) k)
    rw [htw.mul_pow, hS₀ab.2 t ht, one_mul]
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast]
    exact Subgroup.zpow_mem _ hv3e k
  set N := Subgroup.centralizer ({e} : Set G) ⊓ Subgroup.centralizer ({d} : Set G) with hNdef
  have hQN : Q ≤ N := by
    rw [← hQT]
    refine sup_le hBC ?_
    rw [Subgroup.zpowers_le]
    exact ⟨hAC hcA, Subgroup.mem_centralizer_singleton_iff.mpr hcd⟩
  have hQNs : IsSylowOf 3 Q N := hQ.of_le hQN inf_le_left
  have hxd : x * d = d * x := (Item1117Proof.commute_d_x h).symm
  set δ := x * e * x⁻¹ * e⁻¹ with hδdef
  have hxN : ∀ y ∈ N, x * y * x⁻¹ ∈ N := by
    intro y hy
    have hye : y * e = e * y := Subgroup.mem_centralizer_singleton_iff.mp hy.1
    have hyd : y * d = d * y := Subgroup.mem_centralizer_singleton_iff.mp hy.2
    have hxid : x⁻¹ * d = d * x⁻¹ := (Commute.inv_left (show Commute x d from hxd)).eq
    have hzd : x * y * x⁻¹ * d = d * (x * y * x⁻¹) := by
      calc x * y * x⁻¹ * d = x * y * (x⁻¹ * d) := by group
        _ = x * (y * d) * x⁻¹ := by rw [hxid]; group
        _ = (x * d) * y * x⁻¹ := by rw [hyd]; group
        _ = d * (x * y * x⁻¹) := by rw [hxd]; group
    have hzδ : x * y * x⁻¹ * δ = δ * (x * y * x⁻¹) := by
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hxe
      rw [← hk]
      exact (Commute.zpow_right (show Commute (x * y * x⁻¹) d from hzd) k).eq
    have hzxe : x * y * x⁻¹ * (x * e * x⁻¹) = (x * e * x⁻¹) * (x * y * x⁻¹) := by
      calc x * y * x⁻¹ * (x * e * x⁻¹) = x * (y * e) * x⁻¹ := by group
        _ = x * (e * y) * x⁻¹ := by rw [hye]
        _ = (x * e * x⁻¹) * (x * y * x⁻¹) := by group
    have hxe' : x * e * x⁻¹ = δ * e := by rw [hδdef]; group
    rw [hxe'] at hzxe
    refine ⟨Subgroup.mem_centralizer_singleton_iff.mpr ?_,
      Subgroup.mem_centralizer_singleton_iff.mpr hzd⟩
    calc x * y * x⁻¹ * e = δ⁻¹ * (x * y * x⁻¹ * (δ * e)) := by
          rw [show x * y * x⁻¹ * (δ * e) = (x * y * x⁻¹ * δ) * e by group, hzδ]; group
      _ = δ⁻¹ * ((δ * e) * (x * y * x⁻¹)) := by rw [hzxe]
      _ = e * (x * y * x⁻¹) := by group
  have hconj := conj_mem_zpowers_of_isSylowOf hQNs hxN inf_le_left hcube hv.1.1 hev3
  apply hδ1
  have hδe : δ ∈ Subgroup.zpowers e := Subgroup.mul_mem _ hconj
    (Subgroup.inv_mem _ (Subgroup.mem_zpowers e))
  have hbot := Sec12.inf_zpowers_eq_bot_of_not_mem he3o hed
  have hδ : δ ∈ Subgroup.zpowers d ⊓ Subgroup.zpowers e := ⟨hxe, hδe⟩
  rw [hbot] at hδ
  exact Subgroup.mem_bot.mp hδ

end Data

end Item1117Res7Proof

section Main

open Item1117Res7Proof in
theorem step1129PGLNotZ9_of_autThree (h45 : Sec4.Item4_5) (h118 : Item118)
    (hK : AutThree1129) : Step1129PGLNotZ9 := by
  intro G _ _ A c L a R Y d x s r g e Y' h _ _ hx9 heA hecd hcase hY' hKY' _ hP Q hQ hTQ _ v hv
    hvc
  by_contra hv3
  have hxe : x * e * x⁻¹ * e⁻¹ ∈ Subgroup.zpowers d := by
    rcases hcase with hPP | ⟨-, hPP, -⟩
    · exact conj_mul_inv_mem_of_commutator_eq h heA hecd hPP
    · have hxP : x ∈ sec11P R g := Item1119Proof.R_le_P R g (Item1116Proof.mem_R h).2.1
      have heP : e ∈ sec11P R g :=
        Item1119Proof.R_le_P R g (Item1115Proof.A_le_R h.toHyp91 heA)
      have hc : ⁅x, e⁆ ∈ Subgroup.zpowers d := hPP ▸ Subgroup.commutator_mem_commutator hxP heP
      rwa [commutatorElement_def] at hc
  exact false_of_cyclic h45 h118 hK h hx9 heA hecd hxe (conj_mul_inv_ne_one h45 h heA hecd hY' hKY')
    hY' hKY' hP hQ hTQ hv hvc hv3

theorem sylow11PGLWATwo_of_autThree (h45 : Sec4.Item4_5) (h118 : Item118)
    (hK : AutThree1129) : Sylow11PGLWATwo :=
  sylow11PGLWATwo_of_res7 h45 (step1129PGLNotZ9_of_autThree h45 h118 hK)

theorem gap1117NotActXPGL_of_autThree (h45 : Sec4.Item4_5) (h118 : Item118)
    (hK : AutThree1129) : Gap1117NotActXPGL :=
  gap1117NotActXPGL_of_res7 h45 (step1129PGLNotZ9_of_autThree h45 h118 hK)

end Main

section Routes

theorem sylow1129_of_res7' (h45 : Sec4.Item4_5) (h113 : Item113) (h117 : Item117)
    (h118 : Item118) (h119 : Item119Used) (hK : AutThree1129) : Sylow1129 :=
  sylow1129_of_res4 h45 h113 h117 h118 h119 hK (sylow11PGLWATwo_of_autThree h45 h118 hK)

theorem item1132_of_res7' (h45 : Sec4.Item4_5) (h113 : Item113) (h117 : Item117)
    (h118 : Item118) (h119 : Item119Used) (hK : AutThree1129) : Item1132 :=
  item1132_of_res4 h45 h113 h117 h118 h119 hK (sylow11PGLWATwo_of_autThree h45 h118 hK)

theorem item1117_of_res7' (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8) (h97 : Sec9.Item97)
    (h113 : Item113) (h117 : Item117) (h118 : Item118) (h119 : Item119)
    (h82 : Sec8.Item82One) (h1016 : Sec10.Item1016) (h1116 : Item1116)
    (hG2 : KFact1117CubeG2) (hL3 : KFact1117CubeL3) (hK : AutThree1129) : Item1117 :=
  item1117_of_res6 h45 h48 h97 h113 h117 h118 h119 h82 h1016 h1116 hG2 hL3 hK
    (gap1117NotActXPGL_of_autThree h45 h118 hK)

end Routes

end CFSG.RankThree.PartTwo.Sec11
