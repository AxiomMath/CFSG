module

public import CFSG.RankThree.PartTwo.Sec11.Inverter1118ProofSteps
public import CFSG.RankThree.PartTwo.Sec11.Steps
import CFSG.RankThree.PartTwo.Sec11.Item1119Proof
import CFSG.RankThree.PartTwo.Sec11.Item1115NotFieldProof
import CFSG.RankThree.PartTwo.Sec11.Item1116NoFifteen
import CFSG.RankThree.PartTwo.Sec11.DataExistsAct

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open scoped commutatorElement


@[expose] def Step1118SComm : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a : G)
    (R Y : Subgroup G) (d x s r g : G), Sec11Big G A c L a R Y d x s r g →
      Subgroup.normalizer ((sec11P R g : Subgroup G) : Set G) ≤
        Subgroup.normalizer ((Subgroup.closure {c, d} : Subgroup G) : Set G) →
      Subgroup.normalizer ((sec11P R g : Subgroup G) : Set G) ≤
        Subgroup.normalizer (Subgroup.zpowers d : Set G) →
      Subgroup.closure ({r, s} : Set G) = Subgroup.closure {a, s} →
      (∀ (K : Subgroup (sec11P R g)) [K.Normal], IsEmpty (sec11P R g ⧸ K ≃* W33)) →
        ∃ i : ℤ, x * g * x⁻¹ * g⁻¹ ∈ Subgroup.closure {x ^ 3, a * s ^ i, s ^ 3} ∧
          s * g * s⁻¹ * g⁻¹ ∈ Subgroup.closure {x ^ 3, a * s ^ i, s ^ 3}

namespace Item1118StepsProof

section Group

variable {G : Type*} [Group G]


theorem mem_normalizer_closure_of_forall [Finite G] {S : Set G} {g : G}
    (h : ∀ y ∈ S, g * y * g⁻¹ ∈ Subgroup.closure S) :
    g ∈ Subgroup.normalizer ((Subgroup.closure S : Subgroup G) : Set G) := by
  refine Subgroup.mem_normalizer_fintype fun z hz => ?_
  have hle : Subgroup.closure S ≤ (Subgroup.closure S).comap (MulAut.conj g).toMonoidHom := by
    rw [Subgroup.closure_le]
    intro y hy
    exact h y hy
  exact hle hz

theorem commute_of_mem_closure {S : Set G} {g : G} (h : ∀ y ∈ S, g * y = y * g) {z : G}
    (hz : z ∈ Subgroup.closure S) : g * z = z * g := by
  have hle : Subgroup.closure S ≤ Subgroup.centralizer ({g} : Set G) := by
    rw [Subgroup.closure_le]
    intro y hy
    exact Subgroup.mem_centralizer_singleton_iff.mpr (h y hy).symm
  exact (Subgroup.mem_centralizer_singleton_iff.mp (hle hz)).symm

theorem exists_zpow_inv_mul_mem {u v w : G}
    (hu : u ∈ Subgroup.normalizer ((Subgroup.closure {v, w} : Subgroup G) : Set G)) {y : G}
    (hy : y ∈ Subgroup.closure {v, u, w}) :
    ∃ k : ℤ, (u ^ k)⁻¹ * y ∈ Subgroup.closure {v, w} := by
  set N := Subgroup.closure ({v, w} : Set G) with hN
  have hvN : v ∈ N := Subgroup.subset_closure (by simp)
  have hwN : w ∈ N := Subgroup.subset_closure (by simp)
  have huk : ∀ k : ℤ, u ^ k ∈ Subgroup.normalizer (N : Set G) := fun k => Subgroup.zpow_mem _ hu k
  induction hy using Subgroup.closure_induction with
  | mem z hz =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl
    · exact ⟨0, by simpa using hvN⟩
    · exact ⟨1, by simp⟩
    · exact ⟨0, by simpa using hwN⟩
  | one => exact ⟨0, by simp⟩
  | mul y z _ _ hy hz =>
    obtain ⟨k, hk⟩ := hy
    obtain ⟨l, hl⟩ := hz
    refine ⟨k + l, ?_⟩
    have h1 : (u ^ l)⁻¹ * ((u ^ k)⁻¹ * y) * ((u ^ l)⁻¹)⁻¹ ∈ N :=
      (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (huk l)) _).mp hk
    have e : (u ^ (k + l))⁻¹ * (y * z) =
        ((u ^ l)⁻¹ * ((u ^ k)⁻¹ * y) * ((u ^ l)⁻¹)⁻¹) * ((u ^ l)⁻¹ * z) := by
      rw [zpow_add]
      group
    rw [e]
    exact N.mul_mem h1 hl
  | inv y _ hy =>
    obtain ⟨k, hk⟩ := hy
    refine ⟨-k, ?_⟩
    have h1 := (Subgroup.mem_normalizer_iff.mp (huk k) _).mp (N.inv_mem hk)
    have e : (u ^ (-k))⁻¹ * y⁻¹ = u ^ k * ((u ^ k)⁻¹ * y)⁻¹ * (u ^ k)⁻¹ := by
      rw [zpow_neg]
      group
    rw [e]
    exact h1

theorem mem_zpowers_pow_three {x d : G} (hx : ∃ k : ℕ, x ^ 3 ^ k = 1) (hx9 : 9 < orderOf x)
    (hd : d ∈ Subgroup.zpowers x) (hd3 : d ^ 3 = 1) : d ∈ Subgroup.zpowers (x ^ 3) := by
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hd
  obtain ⟨n, hn⟩ := Item1119Proof.exists_orderOf_eq_three_pow' hx
  have hn3 : 3 ≤ n := by
    by_contra h
    have : 3 ^ n ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [hn] at hx9
    omega
  have h1 : (x ^ m) ^ (3 : ℤ) = 1 := by
    rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) by norm_num, zpow_natCast, hd3]
  rw [← zpow_mul] at h1
  have h2 : ((orderOf x : ℕ) : ℤ) ∣ m * 3 := orderOf_dvd_iff_zpow_eq_one.mpr h1
  rw [hn] at h2
  have h27 : (27 : ℤ) ∣ m * 3 := by
    refine dvd_trans ?_ h2
    have : (3 : ℤ) ^ 3 ∣ (3 : ℤ) ^ n := pow_dvd_pow 3 hn3
    push_cast
    simpa using this
  have h3 : (3 : ℤ) ∣ m := by omega
  obtain ⟨m', rfl⟩ := h3
  refine Subgroup.mem_zpowers_iff.mpr ⟨m', ?_⟩
  rw [zpow_mul, show (3 : ℤ) = ((3 : ℕ) : ℤ) by norm_num, zpow_natCast]

end Group

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {a : G}
  {R Y : Subgroup G} {d x s r g : G}

theorem not_mem_closure (h : Sec11Data G A c L a R Y d x s r g) (hsa : s * a = a * s)
    (hax : a * x ^ 3 * a⁻¹ = x ^ 3) (i : ℤ) :
    s ∉ Subgroup.closure {x ^ 3, a * s ^ i, s ^ 3} := by
  intro hs
  have hxs : s * x = x * s := h.commute_s_x
  have hc3 : Commute (x ^ 3) (s ^ 3) := (Commute.pow_pow (hxs : Commute s x).symm 3 3)
  have hsa' : Commute s a := hsa
  have huN : a * s ^ i ∈ Subgroup.normalizer
      ((Subgroup.closure {x ^ 3, s ^ 3} : Subgroup G) : Set G) := by
    refine Subgroup.centralizer_le_normalizer _ ?_
    refine Subgroup.mem_centralizer_iff.mpr fun z hz => ?_
    refine (commute_of_mem_closure (S := {x ^ 3, s ^ 3}) ?_ hz).symm
    rintro y (rfl | rfl)
    · have h1 : a * x ^ 3 = x ^ 3 * a := by
        calc a * x ^ 3 = a * x ^ 3 * a⁻¹ * a := by group
          _ = x ^ 3 * a := by rw [hax]
      have h2 : s ^ i * x ^ 3 = x ^ 3 * s ^ i :=
        ((Commute.pow_right (hxs : Commute s x) 3).zpow_left i).eq
      calc a * s ^ i * x ^ 3 = a * (s ^ i * x ^ 3) := by group
        _ = a * x ^ 3 * s ^ i := by rw [h2]; group
        _ = x ^ 3 * (a * s ^ i) := by rw [h1]; group
    · have h1 : a * s ^ 3 = s ^ 3 * a := (hsa'.pow_left 3).eq.symm
      have h2 : s ^ i * s ^ 3 = s ^ 3 * s ^ i := ((Commute.refl s).zpow_left i |>.pow_right 3).eq
      calc a * s ^ i * s ^ 3 = a * (s ^ i * s ^ 3) := by group
        _ = a * s ^ 3 * s ^ i := by rw [h2]; group
        _ = s ^ 3 * (a * s ^ i) := by rw [h1]; group
  have hs' : s ∈ Subgroup.closure ({x ^ 3, a * s ^ i, s ^ 3} : Set G) := hs
  obtain ⟨k, hk⟩ := exists_zpow_inv_mul_mem huN hs'
  set N := Subgroup.closure ({x ^ 3, s ^ 3} : Set G) with hN
  set D := Subgroup.closure ({s, x} : Set G) with hD
  have hsD : s ∈ D := Subgroup.subset_closure (by simp)
  have hxD : x ∈ D := Subgroup.subset_closure (by simp)
  have hND : N ≤ D := by
    rw [hN, Subgroup.closure_le]
    rintro y (rfl | rfl)
    · exact D.pow_mem hxD 3
    · exact D.pow_mem hsD 3
  have hDI : D ≤ innerPreimage L := by
    rw [hD, ← h.inf_innerPreimage_eq]
    exact inf_le_right
  have hu : (a * s ^ i) ^ k = a ^ k * s ^ (i * k) := by
    rw [(Commute.zpow_right hsa'.symm i).mul_zpow, ← zpow_mul]
  rw [hu] at hk
  set n := (a ^ k * s ^ (i * k))⁻¹ * s with hn
  have hak : a ^ k = s * n⁻¹ * (s ^ (i * k))⁻¹ := by
    rw [hn]
    group
  have ha3 : a ^ 3 = 1 := h.mem_partTwoF.1.2 a h.a_mem
  by_cases h3 : (3 : ℤ) ∣ k
  ·
    have hak1 : a ^ k = 1 := ActOnA.zpow_eq_one_of_dvd ha3 h3
    have hsn : s ^ (1 - i * k) ∈ N := by
      have e : s ^ (1 - i * k) = n := by
        rw [hn, hak1, one_mul, zpow_sub, zpow_one]
        group
      rw [e]
      exact hk
    obtain ⟨m₁, m₂, hm⟩ := Sec12.exists_zpow_mul_zpow_of_mem_closure_pair hc3.eq hsn
    have hmem : s ^ (1 - i * k - 3 * m₂) ∈ Subgroup.zpowers s ⊓ Subgroup.zpowers x := by
      refine ⟨Subgroup.zpow_mem_zpowers s _, ?_⟩
      have e : s ^ (1 - i * k - 3 * m₂) = (x ^ 3) ^ m₁ := by
        have hs3 : (s ^ 3) ^ m₂ = s ^ ((3 : ℤ) * m₂) := by
          rw [zpow_mul]
          norm_cast
        have e1 : s ^ (1 - i * k - 3 * m₂) = s ^ (1 - i * k) * ((s ^ 3) ^ m₂)⁻¹ := by
          rw [hs3, ← zpow_neg, ← zpow_add, sub_eq_add_neg]
        rw [e1, hm, mul_inv_cancel_right]
      rw [e, ← zpow_natCast, ← zpow_mul]
      exact Subgroup.zpow_mem_zpowers x _
    rw [Item1115Proof.inf_zpowers_eq_bot h, Subgroup.mem_bot] at hmem
    have hnd : ¬ (3 : ℤ) ∣ 1 - i * k - 3 * m₂ := by
      obtain ⟨k', rfl⟩ := h3
      intro hd
      have : (3 : ℤ) ∣ 1 := by
        have e : (1 : ℤ) = (1 - i * (3 * k') - 3 * m₂) + 3 * (i * k' + m₂) := by ring
        rw [e]
        exact dvd_add hd (dvd_mul_right 3 _)
      omega
    have hs1 := Item1116Proof.mem_zpowers_zpow_of_not_dvd
      (Item1116Proof.exists_pow_eq_one_of_mem h (Item1116Proof.mem_R h).2.2) hnd
    rw [hmem, Subgroup.zpowers_one_eq_bot, Subgroup.mem_bot] at hs1
    apply h.ne_one
    have hc := h.c_mem_zpowers_s
    rw [hs1, Subgroup.zpowers_one_eq_bot, Subgroup.mem_bot] at hc
    exact hc
  ·
    have hakD : a ^ k ∈ D := by
      rw [hak]
      exact D.mul_mem (D.mul_mem hsD (D.inv_mem (hND hk)))
        (D.inv_mem (D.zpow_mem hsD _))
    have haD : a ∈ D :=
      Subgroup.zpowers_le.mpr hakD
        (Item1116Proof.mem_zpowers_zpow_of_not_dvd ⟨1, by rw [pow_one]; exact ha3⟩ h3)
    exact h.toSec11Std.a_not_mem_innerPreimage (hDI haD)

theorem commutator_le_closure (h45 : Sec4.Item4_5) (h : Sec11Data G A c L a R Y d x s r g)
    (hx9 : 9 < orderOf x) (hrs : Subgroup.closure ({r, s} : Set G) = Subgroup.closure {a, s})
    (hsa : s * a = a * s) {i : ℤ}
    (hxg : x * g * x⁻¹ * g⁻¹ ∈ Subgroup.closure {x ^ 3, a * s ^ i, s ^ 3})
    (hsg : s * g * s⁻¹ * g⁻¹ ∈ Subgroup.closure {x ^ 3, a * s ^ i, s ^ 3}) :
    ⁅sec11P R g, sec11P R g⁆ ≤ Subgroup.closure {x ^ 3, a * s ^ i, s ^ 3} := by
  set T := Subgroup.closure ({x ^ 3, a * s ^ i, s ^ 3} : Set G) with hT
  have hx3T : x ^ 3 ∈ T := Subgroup.subset_closure (by simp)
  have huT : a * s ^ i ∈ T := Subgroup.subset_closure (by simp)
  have hs3T : s ^ 3 ∈ T := Subgroup.subset_closure (by simp)
  have hxs : s * x = x * s := h.commute_s_x
  have hxsc : Commute s x := hxs
  have hsa' : Commute s a := hsa
  have hax : a * x ^ 3 * a⁻¹ = x ^ 3 := (Item1119Proof.a_x_facts h45 h).1
  have hag : a * g = g * a := (Subgroup.mem_centralizer_singleton_iff.mp
    (Sec6.le_centralizer_of_mem_thetaComponentsAt h.mem_thetaComponentsAt_Y h.g_mem.1)).symm
  have hdT : Subgroup.zpowers d ≤ T := by
    rw [Subgroup.zpowers_le]
    exact Subgroup.zpowers_le.mpr hx3T (mem_zpowers_pow_three
      (Item1116Proof.exists_pow_eq_one_of_mem h (Item1116Proof.mem_R h).2.1) hx9
      (Item1115Proof.d_mem_zpowers_x h) (Item1115Proof.d_mem h).2.2)
  have hxaT : x * a * x⁻¹ * a⁻¹ ∈ T := hdT (Item1119Proof.commutator_x_a_facts h45 h).1
  have haT : ∀ z ∈ T, a * z = z * a := by
    intro z hz
    refine commute_of_mem_closure ?_ hz
    rintro y (rfl | rfl | rfl)
    · calc a * x ^ 3 = a * x ^ 3 * a⁻¹ * a := by group
        _ = x ^ 3 * a := by rw [hax]
    · have hasi : s ^ i * a = a * s ^ i := (hsa'.zpow_left i).eq
      show a * (a * s ^ i) = a * s ^ i * a
      rw [mul_assoc a (s ^ i) a, hasi]
    · exact (hsa'.symm.pow_right 3).eq
  have hsT : ∀ z ∈ T, s * z = z * s := by
    intro z hz
    refine commute_of_mem_closure ?_ hz
    rintro y (rfl | rfl | rfl)
    · exact (hxsc.pow_right 3).eq
    · calc s * (a * s ^ i) = s * a * s ^ i := by group
        _ = a * s * s ^ i := by rw [hsa]
        _ = a * (s * s ^ i) := by group
        _ = a * (s ^ i * s) := by rw [((Commute.refl s).zpow_right i).eq]
        _ = a * s ^ i * s := by group
    · exact ((Commute.refl s).pow_right 3).eq
  have haN : a ∈ Subgroup.normalizer (T : Set G) := by
    refine Subgroup.centralizer_le_normalizer _ ?_
    exact Subgroup.mem_centralizer_iff.mpr fun z hz => (haT z hz).symm
  have hsN : s ∈ Subgroup.normalizer (T : Set G) := by
    refine Subgroup.centralizer_le_normalizer _ ?_
    exact Subgroup.mem_centralizer_iff.mpr fun z hz => (hsT z hz).symm
  have hxN : x ∈ Subgroup.normalizer (T : Set G) := by
    refine mem_normalizer_closure_of_forall ?_
    rintro y (rfl | rfl | rfl)
    · rw [show x * x ^ 3 * x⁻¹ = x ^ 3 by group]
      exact hx3T
    · have hxsi : x * s ^ i * x⁻¹ = s ^ i := by
        rw [(hxsc.symm.zpow_right i).eq, mul_inv_cancel_right]
      have e : x * (a * s ^ i) * x⁻¹ = (x * a * x⁻¹ * a⁻¹) * (a * s ^ i) := by
        calc x * (a * s ^ i) * x⁻¹ = (x * a * x⁻¹) * (x * s ^ i * x⁻¹) := by group
          _ = (x * a * x⁻¹) * s ^ i := by rw [hxsi]
          _ = (x * a * x⁻¹ * a⁻¹) * (a * s ^ i) := by group
      rw [e]
      exact T.mul_mem hxaT huT
    · rw [show x * s ^ 3 * x⁻¹ = s ^ 3 by rw [(hxsc.symm.pow_right 3).eq]; group]
      exact hs3T
  set w := g * x * g⁻¹ * x⁻¹ with hw
  set v := g * s * g⁻¹ * s⁻¹ with hv
  have hwT : w ∈ T := by
    have e : w = (x * g * x⁻¹ * g⁻¹)⁻¹ := by rw [hw]; group
    rw [e]
    exact T.inv_mem hxg
  have hvT : v ∈ T := by
    have e : v = (s * g * s⁻¹ * g⁻¹)⁻¹ := by rw [hv]; group
    rw [e]
    exact T.inv_mem hsg
  have hgx : g * x * g⁻¹ = w * x := by rw [hw]; group
  have hgs : g * s * g⁻¹ = v * s := by rw [hv]; group
  have hvs : Commute v s := (hsT v hvT).symm
  have hgN : g ∈ Subgroup.normalizer (T : Set G) := by
    refine mem_normalizer_closure_of_forall ?_
    rintro y (rfl | rfl | rfl)
    · have e : g * x ^ 3 * g⁻¹ = w * (x * w * x⁻¹) * (x * (x * w * x⁻¹) * x⁻¹) * x ^ 3 := by
        rw [← conj_pow, hgx, pow_three]
        group
      rw [e]
      have h1 := (Subgroup.mem_normalizer_iff.mp hxN w).mp hwT
      have h2 := (Subgroup.mem_normalizer_iff.mp hxN _).mp h1
      exact T.mul_mem (T.mul_mem (T.mul_mem hwT h1) h2) hx3T
    · have e : g * (a * s ^ i) * g⁻¹ = v ^ i * (a * s ^ i) := by
        calc g * (a * s ^ i) * g⁻¹ = (g * a * g⁻¹) * (g * s * g⁻¹) ^ i := by
              rw [conj_zpow]; group
          _ = a * (v * s) ^ i := by rw [hgs, ← hag, mul_inv_cancel_right]
          _ = a * (v ^ i * s ^ i) := by rw [hvs.mul_zpow]
          _ = (a * v ^ i) * s ^ i := by group
          _ = (v ^ i * a) * s ^ i := by
              rw [haT (v ^ i) (T.zpow_mem hvT i)]
          _ = v ^ i * (a * s ^ i) := by group
      rw [e]
      exact T.mul_mem (T.zpow_mem hvT i) huT
    · have e : g * s ^ 3 * g⁻¹ = v ^ 3 * s ^ 3 := by
        rw [← conj_pow, hgs, hvs.mul_pow]
      rw [e]
      exact T.mul_mem (T.pow_mem hvT 3) hs3T
  have hR := Item1116NoFifteen.R_eq_of_closure_eq h hrs
  have hPS : sec11P R g = Subgroup.closure ({a, x, s, g} : Set G) := by
    apply le_antisymm
    · refine sup_le ?_ ?_
      · rw [hR, Subgroup.closure_le]
        rintro y (rfl | rfl | rfl) <;> exact Subgroup.subset_closure (by simp)
      · rw [Subgroup.zpowers_le]
        exact Subgroup.subset_closure (by simp)
    · rw [Subgroup.closure_le]
      have hmem : ∀ y ∈ ({a, x, s} : Set G), y ∈ sec11P R g := fun y hy =>
        Item1119Proof.R_le_P R g (by rw [hR]; exact Subgroup.subset_closure hy)
      have hgP := Item1119Proof.g_mem_P R g
      rintro y (rfl | rfl | rfl | rfl)
      · exact hmem _ (by simp)
      · exact hmem _ (by simp)
      · exact hmem _ (by simp)
      · exact hgP
  rw [hPS]
  refine commutator_closure_le ?_ ?_
  · rw [Subgroup.closure_le]
    rintro y (rfl | rfl | rfl | rfl)
    exacts [haN, hxN, hsN, hgN]
  ·
    have hone : ∀ u v : G, u * v = v * u → ⁅u, v⁆ ∈ T := fun u v huv => by
      rw [commutatorElement_def, huv, mul_inv_cancel_right, mul_inv_cancel]
      exact T.one_mem
    have hinv : ∀ u v : G, ⁅u, v⁆ ∈ T → ⁅v, u⁆ ∈ T := fun u v huv => by
      rw [← commutatorElement_inv]
      exact T.inv_mem huv
    have hax' : ⁅x, a⁆ ∈ T := by rw [commutatorElement_def]; exact hxaT
    have hxg' : ⁅x, g⁆ ∈ T := by rw [commutatorElement_def]; exact hxg
    have hsg' : ⁅s, g⁆ ∈ T := by rw [commutatorElement_def]; exact hsg
    have hxs' : x * s = s * x := hxs.symm
    have hsa'' : a * s = s * a := hsa.symm
    have hga : g * a = a * g := hag.symm
    rintro u (rfl | rfl | rfl | rfl) v (rfl | rfl | rfl | rfl)
    exacts [hone _ _ rfl, hinv _ _ hax', hone _ _ hsa'', hone _ _ hag,
      hax', hone _ _ rfl, hone _ _ hxs', hxg',
      hone _ _ hsa, hone _ _ hxs, hone _ _ rfl, hsg',
      hone _ _ hga, hinv _ _ hxg', hinv _ _ hsg', hone _ _ rfl]

end Item1118StepsProof

theorem step1118S_of (h45 : Sec4.Item4_5) (h113 : Item113) (h117 : Item117)
    (hC : Step1118SComm) : Step1118S := by
  intro G _ _ A c L a R Y d x s r g hbig hcdN hNd hrs hW
  have h := hbig.toSec11Data
  obtain ⟨i, hxg, hsg⟩ := hC G A c L a R Y d x s r g hbig hcdN hNd hrs hW
  have hsa : s * a = a * s := item1115_of_mhoV h45 h113 h117 G A c L a R Y d x s r g h
  have hPP := Item1118StepsProof.commutator_le_closure h45 h hbig.orderOf_x_gt hrs hsa hxg hsg
  have hV : ⁅sec11P R g, sec11P R g⁆ ⊔ Subgroup.closure ({x ^ 3, s ^ 3} : Set G) ≤
      Subgroup.closure {x ^ 3, a * s ^ i, s ^ 3} := by
    refine sup_le hPP ?_
    rw [Subgroup.closure_le]
    rintro y (rfl | rfl) <;> exact Subgroup.subset_closure (by simp)
  exact fun hs => Item1118StepsProof.not_mem_closure h hsa (Item1119Proof.a_x_facts h45 h).1 i
    (hV hs)

end CFSG.RankThree.PartTwo.Sec11
