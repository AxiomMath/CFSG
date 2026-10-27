module

public import CFSG.RankThree.PartTwo.Sec11.LaterSteps
public import CFSG.RankThree.PartTwo.Sec11.Steps
public import CFSG.RankThree.PartTwo.Sec11.Item1119ProofBasic
import CFSG.RankThree.PartTwo.Sec11.Item1115Proof
import CFSG.RankThree.PartTwo.Sec11.Item1123Proof

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open scoped commutatorElement

section Statements


@[expose] def Step1119Comm : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a : G)
    (R Y : Subgroup G) (d x s r g : G), Sec11Big G A c L a R Y d x s r g →
      ∃ v : G, v ∉ Subgroup.closure ({x ^ 9, v ^ 3} : Set G) ∧
        g ∈ Subgroup.normalizer ((Subgroup.closure {x ^ 9, v ^ 3} : Subgroup G) : Set G) ∧
        (∀ z ∈ sec11P R g ⊓ Y, (∀ w ∈ sec11P R g ⊓ Y, z * w = w * z) →
          z ∈ Subgroup.closure ({x ^ 9, v ^ 3} : Set G)) ∧
        ∃ w ∈ Subgroup.closure ({x ^ 9, v ^ 3} : Set G), (x ^ 3)⁻¹ * g⁻¹ * x ^ 3 * g = v * w

@[expose] def Step1119Sym : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a : G)
    (R Y : Subgroup G) (d x s r g : G), Sec11Big G A c L a R Y d x s r g →
      A ≤ (Subgroup.upperCentralSeries (sec11P R g) 2).map (sec11P R g).subtype →
      (Subgroup.upperCentralSeries (sec11P R g) 2).map (sec11P R g).subtype ≤ R →
      Subgroup.normalizer ((sec11P R g : Subgroup G) : Set G) ≤
        Subgroup.normalizer (A : Set G) →
      Subgroup.normalizer ((sec11P R g : Subgroup G) : Set G) ≤
        Subgroup.normalizer (Subgroup.zpowers d : Set G) →
      r * a = a * r → s * a = a * s →
      ¬ Subgroup.normalizer ((sec11P R g : Subgroup G) : Set G) ≤
          Subgroup.normalizer ((Subgroup.closure {c, d} : Subgroup G) : Set G) →
      ∃ (c' : G) (L' : Subgroup G) (a' : G) (R' Y' : Subgroup G) (x' s' r' g' : G),
        Sec11Big G A c' L' a' R' Y' d x' s' r' g' ∧
          Subgroup.normalizer ((sec11P R' g' : Subgroup G) : Set G) ≤
            Subgroup.normalizer ((Subgroup.closure {c', d} : Subgroup G) : Set G)

end Statements

namespace Item1119Proof

section Generic

variable {G : Type*} [Group G]

theorem R_le_P (R : Subgroup G) (g : G) : R ≤ sec11P R g := le_sup_left

theorem g_mem_P (R : Subgroup G) (g : G) : g ∈ sec11P R g :=
  (le_sup_right : Subgroup.zpowers g ≤ sec11P R g) (Subgroup.mem_zpowers g)

end Generic

section Data


variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {a : G}
  {R Y : Subgroup G} {d x s r g : G}

theorem exists_pow_eq_one_of_mem_P (h : Sec11Data G A c L a R Y d x s r g) {q : G}
    (hq : q ∈ sec11P R g) : ∃ k : ℕ, q ^ 3 ^ k = 1 := by
  obtain ⟨k, hk⟩ := h.isPGroup_sec11P ⟨q, hq⟩
  exact ⟨k, by simpa using congrArg Subtype.val hk⟩

theorem P_le_normalizer_d (h113 : Item113) (h117 : Item117)
    (h : Sec11Data G A c L a R Y d x s r g) :
    sec11P R g ≤ Subgroup.normalizer (Subgroup.zpowers d : Set G) :=
  (h.sec11P_le_normalizer_A h113).trans (Item1115Proof.W_le_normalizer_d h117 h)

theorem commute_d (h113 : Item113) (h117 : Item117) (h : Sec11Data G A c L a R Y d x s r g)
    {q : G} (hq : q ∈ sec11P R g) : q * d = d * q := by
  have hd3 := (Item1115Proof.d_mem h).2.2
  have h1 := conj_eq_self_of_threeElement hd3 (exists_pow_eq_one_of_mem_P h hq)
    ((Subgroup.mem_normalizer_iff.mp (P_le_normalizer_d h113 h117 h hq) d).mp
      (Subgroup.mem_zpowers d))
  calc q * d = q * d * q⁻¹ * q := by group
    _ = d * q := by rw [h1]

theorem commute_of_mem_zpowers_d (h113 : Item113) (h117 : Item117)
    (h : Sec11Data G A c L a R Y d x s r g) {z : G} (hz : z ∈ Subgroup.zpowers d) {q : G}
    (hq : q ∈ sec11P R g) : q * z = z * q := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
  exact ((Commute.zpow_right (commute_d h113 h117 h hq) k)).eq

theorem c_d_facts (h : Sec11Data G A c L a R Y d x s r g) :
    c * d = d * c ∧ c ^ 3 = 1 ∧ d ^ 3 = 1 := by
  obtain ⟨hdA, -, hd3⟩ := Item1115Proof.d_mem h
  exact ⟨congrArg Subtype.val (h.mem_partTwoF.1.1.is_comm.comm ⟨c, h.mem_A⟩ ⟨d, hdA⟩),
    h.mem_partTwoF.1.2 c h.mem_A, hd3⟩

theorem R_le_centralizer_c (h : Sec11Data G A c L a R Y d x s r g) :
    R ≤ Subgroup.centralizer ({c} : Set G) :=
  le_centralizer_of_le_normalizer_zpowers (Item1115Proof.orderOf_c_d h).1 h.isSylowOf.isPGroup
    h.isSylowOf.le

theorem P_le_normalizer_cd (h113 : Item113) (h117 : Item117)
    (h : Sec11Data G A c L a R Y d x s r g) :
    sec11P R g ≤ Subgroup.normalizer ((Subgroup.closure {c, d} : Subgroup G) : Set G) := by
  have key : ∀ q ∈ sec11P R g, q * c * q⁻¹ ∈ Subgroup.closure ({c, d} : Set G) →
      q ∈ Subgroup.normalizer ((Subgroup.closure {c, d} : Subgroup G) : Set G) := by
    intro q hq hqc
    refine Subgroup.mem_normalizer_fintype fun z hz => ?_
    have hle : Subgroup.closure ({c, d} : Set G) ≤
        (Subgroup.closure ({c, d} : Set G)).comap (MulAut.conj q).toMonoidHom := by
      rw [Subgroup.closure_le]
      intro w hw
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
      rw [SetLike.mem_coe, Subgroup.mem_comap]
      rcases hw with rfl | rfl
      · exact hqc
      · change q * w * q⁻¹ ∈ _
        have h1 := (Subgroup.mem_normalizer_iff.mp (P_le_normalizer_d h113 h117 h hq) w).mp
          (Subgroup.mem_zpowers w)
        exact Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp)) h1
    exact hle hz
  refine sup_le (fun q hq => key q (R_le_P R g hq) ?_) ?_
  · rw [Subgroup.mem_centralizer_singleton_iff.mp (R_le_centralizer_c h hq), mul_inv_cancel_right]
    exact Subgroup.subset_closure (by simp)
  · rw [Subgroup.zpowers_le]
    exact key g (g_mem_P R g) h.conj_mem

theorem conj_c_mul_inv_mem (h113 : Item113) (h117 : Item117)
    (h : Sec11Data G A c L a R Y d x s r g) {q : G} (hq : q ∈ sec11P R g) :
    q * c * q⁻¹ * c⁻¹ ∈ Subgroup.zpowers d := by
  obtain ⟨hcd, hc3, -⟩ := c_d_facts h
  have hqc : q * c * q⁻¹ ∈ Subgroup.closure ({c, d} : Set G) :=
    (Subgroup.mem_normalizer_iff.mp (P_le_normalizer_cd h113 h117 h hq) c).mp
      (Subgroup.subset_closure (by simp))
  obtain ⟨i, j, hij⟩ := Sec12.exists_zpow_mul_zpow_of_mem_closure_pair hcd hqc
  have hcN : c ∈ Subgroup.normalizer (Subgroup.zpowers d : Set G) := by
    apply Sec10.mem_normalizer_zpowers_of_conj_mem
    rw [hcd, mul_inv_cancel_right]
    exact Subgroup.mem_zpowers d
  refine Item1123Proof.conj_mul_inv_mem_of_pow_three_mem (P_le_normalizer_d h113 h117 h hq) hcN
    (by rw [hc3]; exact Subgroup.one_mem _) (exists_pow_eq_one_of_mem_P h hq) (k := i) ?_
  rw [hij, ← mul_assoc, inv_mul_cancel, one_mul]
  exact Subgroup.zpow_mem_zpowers d j

theorem c_d_mem_secondCenter (h113 : Item113) (h117 : Item117)
    (h : Sec11Data G A c L a R Y d x s r g) :
    c ∈ (Subgroup.upperCentralSeries (sec11P R g) 2).map (sec11P R g).subtype ∧
      d ∈ (Subgroup.upperCentralSeries (sec11P R g) 2).map (sec11P R g).subtype := by
  have hcP : c ∈ sec11P R g := R_le_P R g (c_mem_of_hyp91 h.toHyp91)
  have hdP : d ∈ sec11P R g := R_le_P R g (Item1115Proof.A_le_R h.toHyp91 (Item1115Proof.d_mem h).1)
  refine ⟨mem_secondCenter_iff.mpr ⟨hcP, fun p hp q hq => ?_⟩,
    mem_secondCenter_of_mem_center hdP fun q hq => commute_d h113 h117 h hq⟩
  have h1 := conj_c_mul_inv_mem h113 h117 h hp
  have e : ⁅c, p⁆ = (p * c * p⁻¹ * c⁻¹)⁻¹ := by
    rw [commutatorElement_def]
    group
  have h2 : ⁅c, p⁆ ∈ Subgroup.zpowers d := by
    rw [e]
    exact Subgroup.inv_mem _ h1
  exact commute_of_mem_zpowers_d h113 h117 h h2 hq

theorem closure_cd_le_secondCenter (h113 : Item113) (h117 : Item117)
    (h : Sec11Data G A c L a R Y d x s r g) :
    Subgroup.closure ({c, d} : Set G) ≤
      (Subgroup.upperCentralSeries (sec11P R g) 2).map (sec11P R g).subtype := by
  obtain ⟨hc, hd⟩ := c_d_mem_secondCenter h113 h117 h
  rw [Subgroup.closure_le]
  rintro y (rfl | rfl)
  exacts [hc, hd]

theorem mem_A_of_mem_R (h113 : Item113) (h : Sec11Data G A c L a R Y d x s r g) {y : G}
    (hyR : y ∈ R) (hy3 : y ^ 3 = 1) : y ∈ A := by
  rw [(h113 G A c L a R Y h.toSec11Std).1]
  exact Subgroup.subset_closure ⟨hyR, hy3⟩

theorem a_mem_normalizer_x (h45 : Sec4.Item4_5) (h : Sec11Data G A c L a R Y d x s r g) :
    a ∈ Subgroup.normalizer (Subgroup.zpowers x : Set G) :=
  Item1115Proof.mem_normalizer_zpowers_x h45 h (Item1115Proof.A_le_R h.toHyp91 h.a_mem)

theorem a_x_facts (h45 : Sec4.Item4_5) (h : Sec11Data G A c L a R Y d x s r g) :
    a * x ^ 3 * a⁻¹ = x ^ 3 ∧ (a * x * a⁻¹ * x⁻¹) ^ 3 = 1 :=
  conj_pow_three_eq_of_pow_three_eq_one (h.mem_partTwoF.1.2 a h.a_mem)
    (Item1116Proof.exists_pow_eq_one_of_mem h (Item1116Proof.mem_R h).2.1)
    (a_mem_normalizer_x h45 h)

theorem x_cube_mem_Y (h45 : Sec4.Item4_5) (h : Sec11Data G A c L a R Y d x s r g) :
    x ^ 3 ∈ Y := by
  obtain ⟨haN, ha3, -, hQ⟩ := h.toSec11Std.a_facts
  have hxL : x ∈ L := by
    have : x ∈ R ⊓ L := by
      rw [h.inf_L_eq]
      exact Subgroup.mem_zpowers x
    exact this.2
  obtain ⟨n, hn⟩ := Item1116Proof.exists_pow_eq_one_of_mem h (Item1116Proof.mem_R h).2.1
  have hxa := (a_x_facts h45 h).1
  have hC : x ^ 3 ∈ Subgroup.centralizer ({a} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc x ^ 3 * a = a * x ^ 3 * a⁻¹ * a := by rw [hxa]
      _ = a * x ^ 3 := by group
  refine h.sec11K_le (mem_sec11K_of_pow_eq_one haN ha3 hQ.1 ⟨L.pow_mem hxL 3, hC⟩ (k := n) ?_)
  rw [← pow_mul, mul_comm, pow_mul, hn, one_pow]

theorem secondCenter_le_R (h45 : Sec4.Item4_5) (h : Sec11Data G A c L a R Y d x s r g)
    (hg3 : orderOf g = 3) {v : G} (hvN : v ∉ Subgroup.closure ({x ^ 9, v ^ 3} : Set G))
    (hgN : g ∈ Subgroup.normalizer ((Subgroup.closure {x ^ 9, v ^ 3} : Subgroup G) : Set G))
    (hZ : ∀ z ∈ sec11P R g ⊓ Y, (∀ w ∈ sec11P R g ⊓ Y, z * w = w * z) →
      z ∈ Subgroup.closure ({x ^ 9, v ^ 3} : Set G))
    (hcomm : ∃ w ∈ Subgroup.closure ({x ^ 9, v ^ 3} : Set G),
      (x ^ 3)⁻¹ * g⁻¹ * x ^ 3 * g = v * w) :
    (Subgroup.upperCentralSeries (sec11P R g) 2).map (sec11P R g).subtype ≤ R := by
  set P := sec11P R g with hPdef
  set N := Subgroup.closure ({x ^ 9, v ^ 3} : Set G) with hNdef
  set Z2 := (Subgroup.upperCentralSeries P 2).map P.subtype with hZ2
  obtain ⟨w₀, hw₀, hcg⟩ := hcomm
  have hx3Y : x ^ 3 ∈ Y := x_cube_mem_Y h45 h
  have hgY : g ∈ Y := h.g_mem.1
  have hgR : g ∈ Subgroup.normalizer (R : Set G) := h.g_mem_normalizer
  have hx9N : x ^ 9 ∈ N := Subgroup.subset_closure (by simp)
  have hxR : x ∈ R := (Item1116Proof.mem_R h).2.1
  have hx : ∃ n : ℕ, x ^ 3 ^ n = 1 := Item1116Proof.exists_pow_eq_one_of_mem h hxR
  have hx3P : x ^ 3 ∈ P := P.pow_mem (R_le_P R g hxR) 3
  have key : ∀ u ∈ R, u * g ∉ Z2 := by
    intro u hu hug
    have hu3 := Item1116Proof.exists_pow_eq_one_of_mem h hu
    have huN := Item1115Proof.mem_normalizer_zpowers_x h45 h hu
    have hcu := inv_pow_three_mul_conj_mem_zpowers_pow_nine hx hu3 huN
    have hcuN : g⁻¹ * ((x ^ 3)⁻¹ * u⁻¹ * x ^ 3 * u) * g ∈ N := by
      have h1 : (x ^ 3)⁻¹ * u⁻¹ * x ^ 3 * u ∈ N := Subgroup.zpowers_le.mpr hx9N hcu
      have h2 := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hgN) _).mp h1
      rwa [inv_inv] at h2
    set e := (x ^ 3)⁻¹ * (u * g)⁻¹ * x ^ 3 * (u * g) with he
    have he_eq : e = (v * w₀) * (g⁻¹ * ((x ^ 3)⁻¹ * u⁻¹ * x ^ 3 * u) * g) := by
      rw [← hcg, he]
      group
    have huxY : u⁻¹ * x ^ 3 * u ∈ Y := by
      have h1 : u⁻¹ * x * u⁻¹⁻¹ ∈ Subgroup.zpowers x :=
        conj_mem_zpowers_of_mem_normalizer (Subgroup.inv_mem _ huN)
      obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp h1
      have h2 : u⁻¹ * x ^ 3 * u = (x ^ 3) ^ m := by
        rw [inv_inv] at hm
        rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, hm, zpow_natCast]
        simpa using (conj_pow (a := u⁻¹) (b := x) (i := 3)).symm
      rw [h2]
      exact Y.zpow_mem hx3Y m
    have heY : e ∈ Y := by
      have e1 : e = (x ^ 3)⁻¹ * g⁻¹ * (u⁻¹ * x ^ 3 * u) * g := by
        rw [he]
        group
      rw [e1]
      exact Y.mul_mem (Y.mul_mem (Y.mul_mem (Y.inv_mem hx3Y) (Y.inv_mem hgY)) huxY) hgY
    have hugP : u * g ∈ P := P.mul_mem (R_le_P R g hu) (g_mem_P R g)
    have heP : e ∈ P :=
      P.mul_mem (P.mul_mem (P.mul_mem (P.inv_mem hx3P) (P.inv_mem hugP)) hx3P) hugP
    have hecent : ∀ q ∈ P, q * e = e * q := by
      intro q hq
      have h1 := commutator_central_of_mem_secondCenter (Z2.inv_mem hug) (P.inv_mem hx3P) q hq
      have e2 : e = ⁅(u * g)⁻¹, (x ^ 3)⁻¹⁆⁻¹ := by
        rw [he, commutatorElement_def]
        group
      rw [e2]
      exact (Commute.inv_right h1).eq
    have heN : e ∈ N := hZ e ⟨heP, heY⟩ (fun w hw => (hecent w hw.1).symm)
    apply hvN
    have e3 : v = e * (g⁻¹ * ((x ^ 3)⁻¹ * u⁻¹ * x ^ 3 * u) * g)⁻¹ * w₀⁻¹ := by
      rw [he_eq]
      group
    rw [e3]
    exact N.mul_mem (N.mul_mem heN (N.inv_mem hcuN)) (N.inv_mem hw₀)
  intro y hy
  have hyP : y ∈ P := (mem_secondCenter_iff.mp hy).1
  have hle : Subgroup.zpowers g ≤ Subgroup.normalizer (R : Set G) := Subgroup.zpowers_le.mpr hgR
  have hyP' : y ∈ ((R ⊔ Subgroup.zpowers g : Subgroup G) : Set G) := hyP
  rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ hle] at hyP'
  obtain ⟨u, hu, w, hw, rfl⟩ := Set.mem_mul.mp hyP'
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
  have hg3' : g ^ (3 : ℤ) = 1 := by
    rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) from rfl, zpow_natCast, ← hg3, pow_orderOf_eq_one]
  have hk : g ^ k = g ^ (k % 3) := zpow_eq_zpow_emod k hg3'
  rcases (by omega : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2) with h0 | h1 | h2
  · rw [hk, h0, zpow_zero, mul_one]
    exact hu
  · exfalso
    rw [hk, h1, zpow_one] at hy
    exact key u hu hy
  · exfalso
    rw [hk, h2] at hy
    have hinv := Z2.inv_mem hy
    have hg2 : g ^ (2 : ℤ) = g⁻¹ := by
      rw [eq_inv_iff_mul_eq_one, ← zpow_add_one, show (2 : ℤ) + 1 = 3 by norm_num, hg3']
    have e : (u * g ^ (2 : ℤ))⁻¹ = (g * u⁻¹ * g⁻¹) * g := by
      rw [hg2]
      group
    rw [e] at hinv
    exact key _ ((Subgroup.mem_normalizer_iff.mp hgR _).mp (R.inv_mem hu)) hinv

theorem closure_cd_le_A (h : Sec11Data G A c L a R Y d x s r g) :
    Subgroup.closure ({c, d} : Set G) ≤ A := by
  rw [Subgroup.closure_le]
  rintro y (rfl | rfl)
  exacts [h.mem_A, (Item1115Proof.d_mem h).1]

theorem exists_zpow_mul_of_mem_A (h : Sec11Data G A c L a R Y d x s r g) {y : G} (hy : y ∈ A) :
    ∃ i : ℤ, ∃ w ∈ Subgroup.closure ({c, d} : Set G), y = a ^ i * w := by
  have hcomm : ∀ u ∈ A, ∀ v ∈ A, u * v = v * u := fun u hu v hv =>
    congrArg Subtype.val (h.mem_partTwoF.1.1.is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩)
  have haN : a ∈ Subgroup.normalizer ((Subgroup.closure {c, d} : Subgroup G) : Set G) := by
    refine Subgroup.mem_normalizer_fintype fun z hz => ?_
    rw [hcomm a h.a_mem z (closure_cd_le_A h hz), mul_inv_cancel_right]
    exact hz
  have hle : A ≤ Subgroup.zpowers a ⊔ Subgroup.closure ({c, d} : Set G) := by
    rw [h.closure_eq, Subgroup.closure_le]
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl
    · exact (le_sup_right : _ ≤ Subgroup.zpowers a ⊔ _) (Subgroup.subset_closure (by simp))
    · exact (le_sup_left : _ ≤ _ ⊔ Subgroup.closure ({c, d} : Set G)) (Subgroup.mem_zpowers z)
    · exact (le_sup_right : _ ≤ Subgroup.zpowers a ⊔ _) (Subgroup.subset_closure (by simp))
  exact exists_zpow_mul_of_mem_sup haN (hle hy)

theorem normalizer_le_of_not_mem (h113 : Item113) (h117 : Item117)
    (h : Sec11Data G A c L a R Y d x s r g)
    (hZR : (Subgroup.upperCentralSeries (sec11P R g) 2).map (sec11P R g).subtype ≤ R)
    (ha : a ∉ (Subgroup.upperCentralSeries (sec11P R g) 2).map (sec11P R g).subtype) :
    Subgroup.normalizer ((sec11P R g : Subgroup G) : Set G) ≤
      Subgroup.normalizer ((Subgroup.closure {c, d} : Subgroup G) : Set G) := by
  set Z2 := (Subgroup.upperCentralSeries (sec11P R g) 2).map (sec11P R g).subtype with hZ2
  have hexp : ∀ y ∈ A, y ^ 3 = 1 := h.mem_partTwoF.1.2
  intro n hn
  refine Subgroup.mem_normalizer_fintype fun z hz => ?_
  have hzZ := closure_cd_le_secondCenter h113 h117 h hz
  have hzA : z ∈ A := closure_cd_le_A h hz
  have h1 : n * z * n⁻¹ ∈ Z2 := conj_mem_secondCenter hn hzZ
  have h2 : (n * z * n⁻¹) ^ 3 = 1 := by rw [conj_pow, hexp z hzA, mul_one, mul_inv_cancel]
  have h3 : n * z * n⁻¹ ∈ A := mem_A_of_mem_R h113 h (hZR h1) h2
  obtain ⟨i, w, hw, hiw⟩ := exists_zpow_mul_of_mem_A h h3
  have hai : a ^ i ∈ Z2 := by
    have e : a ^ i = (n * z * n⁻¹) * w⁻¹ := by rw [hiw]; group
    rw [e]
    exact Z2.mul_mem h1 (Z2.inv_mem (closure_cd_le_secondCenter h113 h117 h hw))
  have ha3 : a ^ 3 = 1 := hexp a h.a_mem
  by_cases h3i : (3 : ℤ) ∣ i
  · obtain ⟨t, rfl⟩ := h3i
    have hat : a ^ (3 * t) = 1 := by
      rw [zpow_mul, show (3 : ℤ) = ((3 : ℕ) : ℤ) from rfl, zpow_natCast, ha3, one_zpow]
    rw [hiw, hat, one_mul]
    exact hw
  · exfalso
    apply ha
    have h4 := Item1116Proof.mem_zpowers_zpow_of_not_dvd (r := a) ⟨1, by rw [pow_one]; exact ha3⟩
      h3i
    exact Subgroup.zpowers_le.mpr hai h4

theorem A_le_secondCenter (h113 : Item113) (h117 : Item117)
    (h : Sec11Data G A c L a R Y d x s r g)
    (ha : a ∈ (Subgroup.upperCentralSeries (sec11P R g) 2).map (sec11P R g).subtype) :
    A ≤ (Subgroup.upperCentralSeries (sec11P R g) 2).map (sec11P R g).subtype := by
  obtain ⟨hc, hd⟩ := c_d_mem_secondCenter h113 h117 h
  rw [h.closure_eq, Subgroup.closure_le]
  intro y hy
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
  rcases hy with rfl | rfl | rfl
  exacts [hc, ha, hd]

theorem normalizer_le_normalizer_A (h113 : Item113) (h : Sec11Data G A c L a R Y d x s r g)
    (hZR : (Subgroup.upperCentralSeries (sec11P R g) 2).map (sec11P R g).subtype ≤ R)
    (hA : A ≤ (Subgroup.upperCentralSeries (sec11P R g) 2).map (sec11P R g).subtype) :
    Subgroup.normalizer ((sec11P R g : Subgroup G) : Set G) ≤
      Subgroup.normalizer (A : Set G) := by
  intro n hn
  refine Subgroup.mem_normalizer_fintype fun y hy => ?_
  have h1 := conj_mem_secondCenter hn (hA hy)
  have h2 : (n * y * n⁻¹) ^ 3 = 1 := by
    rw [conj_pow, h.mem_partTwoF.1.2 y hy, mul_one, mul_inv_cancel]
  exact mem_A_of_mem_R h113 h (hZR h1) h2

theorem commutator_x_a_facts (h45 : Sec4.Item4_5) (h : Sec11Data G A c L a R Y d x s r g) :
    x * a * x⁻¹ * a⁻¹ ∈ Subgroup.zpowers d ∧ x * a * x⁻¹ * a⁻¹ ≠ 1 := by
  have h1 := (a_x_facts h45 h).2
  have hmem : a * x * a⁻¹ * x⁻¹ ∈ Subgroup.zpowers x :=
    Subgroup.mul_mem _ (conj_mem_zpowers_of_mem_normalizer (a_mem_normalizer_x h45 h))
      (Subgroup.inv_mem _ (Subgroup.mem_zpowers x))
  have hdvd : orderOf (a * x * a⁻¹ * x⁻¹) ∣ orderOf d := by
    rw [(Item1115Proof.orderOf_c_d h).2]
    exact orderOf_dvd_of_pow_eq_one h1
  have h2 : a * x * a⁻¹ * x⁻¹ ∈ Subgroup.zpowers d :=
    Item1115Proof.mem_zpowers_of_orderOf_dvd hmem (Item1115Proof.d_mem_zpowers_x h) hdvd
  have e : x * a * x⁻¹ * a⁻¹ = (a * x * a⁻¹ * x⁻¹)⁻¹ := by group
  refine ⟨by rw [e]; exact Subgroup.inv_mem _ h2, fun h0 => ?_⟩
  apply Item1115Proof.not_commute_a_x h
  calc a * x = (x * a * x⁻¹ * a⁻¹)⁻¹ * (x * a) := by group
    _ = x * a := by rw [h0, inv_one, one_mul]

theorem normalizer_le_normalizer_d (h45 : Sec4.Item4_5) (h113 : Item113) (h117 : Item117)
    (h : Sec11Data G A c L a R Y d x s r g)
    (hZR : (Subgroup.upperCentralSeries (sec11P R g) 2).map (sec11P R g).subtype ≤ R) :
    Subgroup.normalizer ((sec11P R g : Subgroup G) : Set G) ≤
      Subgroup.normalizer (Subgroup.zpowers d : Set G) := by
  set P := sec11P R g with hPdef
  obtain ⟨hcd, hc3, hd3⟩ := c_d_facts h
  have hcomm : ∀ u ∈ A, ∀ v ∈ A, u * v = v * u := fun u hu v hv =>
    congrArg Subtype.val (h.mem_partTwoF.1.1.is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩)
  have hdA := (Item1115Proof.d_mem h).1
  have hxR : x ∈ R := (Item1116Proof.mem_R h).2.1
  have hxP : x ∈ P := R_le_P R g hxR
  have hdP : d ∈ P := R_le_P R g (Item1115Proof.A_le_R h.toHyp91 hdA)
  intro n hn
  apply Sec10.mem_normalizer_zpowers_of_conj_mem
  set y := n * d * n⁻¹ with hy
  have hconj : ∀ z ∈ P, n⁻¹ * z * n ∈ P := fun z hz => by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hn) z).mp hz
    rwa [inv_inv] at this
  have hyP : y ∈ P := (Subgroup.mem_normalizer_iff.mp hn d).mp hdP
  have hycent : ∀ q ∈ P, q * y = y * q := by
    intro q hq
    have h1 := commute_d h113 h117 h (hconj q hq)
    calc q * y = n * ((n⁻¹ * q * n) * d) * n⁻¹ := by rw [hy]; group
      _ = n * (d * (n⁻¹ * q * n)) * n⁻¹ := by rw [h1]
      _ = y * q := by rw [hy]; group
  have hyZ := mem_secondCenter_of_mem_center hyP hycent
  have hy3 : y ^ 3 = 1 := by rw [hy, conj_pow, hd3, mul_one, mul_inv_cancel]
  have hyA : y ∈ A := mem_A_of_mem_R h113 h (hZR hyZ) hy3
  obtain ⟨i, w, hw, hiw⟩ := exists_zpow_mul_of_mem_A h hyA
  obtain ⟨hz, hz1⟩ := commutator_x_a_facts h45 h
  set z := x * a * x⁻¹ * a⁻¹ with hzdef
  have hxw : x * w * x⁻¹ = w := by
    have hle : Subgroup.closure ({c, d} : Set G) ≤ Subgroup.centralizer ({x} : Set G) := by
      rw [Subgroup.closure_le]
      rintro u (rfl | rfl)
      · exact Subgroup.mem_centralizer_singleton_iff.mpr
          (Subgroup.mem_centralizer_singleton_iff.mp (R_le_centralizer_c h hxR)).symm
      · exact Subgroup.mem_centralizer_singleton_iff.mpr (commute_d h113 h117 h hxP).symm
    rw [← Subgroup.mem_centralizer_singleton_iff.mp (hle hw), mul_inv_cancel_right]
  have hza : Commute z a := by
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hz
    rw [← hm]
    exact Commute.zpow_left (hcomm d hdA a h.a_mem) m
  have hxa : x * a * x⁻¹ = z * a := by rw [hzdef]; group
  have h1 : x * a ^ i * x⁻¹ = z ^ i * a ^ i := by rw [← conj_zpow, hxa, hza.mul_zpow]
  have h2 : x * y * x⁻¹ = z ^ i * y := by
    rw [hiw]
    calc x * (a ^ i * w) * x⁻¹ = (x * a ^ i * x⁻¹) * (x * w * x⁻¹) := by group
      _ = z ^ i * (a ^ i * w) := by rw [h1, hxw]; group
  have h3 : z ^ i = 1 := by
    have e : x * y * x⁻¹ = y := by rw [hycent x hxP, mul_inv_cancel_right]
    rw [e] at h2
    calc z ^ i = z ^ i * y * y⁻¹ := by group
      _ = 1 := by rw [← h2, mul_inv_cancel]
  have hz3 : orderOf z = 3 := by
    refine orderOf_eq_prime ?_ hz1
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hz
    rw [← hm, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hd3, one_zpow]
  have h3i : ((3 : ℕ) : ℤ) ∣ i := by
    rw [← hz3]
    exact orderOf_dvd_iff_zpow_eq_one.mpr h3
  have hai : a ^ i = 1 := by
    obtain ⟨t, rfl⟩ := h3i
    rw [zpow_mul, zpow_natCast, h.mem_partTwoF.1.2 a h.a_mem, one_zpow]
  have hyw : y = w := by rw [hiw, hai, one_mul]
  obtain ⟨j, k, hjk⟩ := Sec12.exists_zpow_mul_zpow_of_mem_closure_pair hcd hw
  set e' := g * c * g⁻¹ * c⁻¹ with he'def
  have he' : e' ∈ Subgroup.zpowers d := conj_c_mul_inv_mem h113 h117 h (g_mem_P R g)
  have he'1 : e' ≠ 1 := by
    intro h0
    apply h.g_not_mem
    apply Sec10.mem_normalizer_zpowers_of_conj_mem
    have e : g * c * g⁻¹ = c := by
      calc g * c * g⁻¹ = e' * c := by rw [he'def]; group
        _ = c := by rw [h0, one_mul]
    rw [e]
    exact Subgroup.mem_zpowers c
  have he'c : Commute e' c := by
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp he'
    rw [← hm]
    exact Commute.zpow_left hcd.symm m
  have hgc : g * c * g⁻¹ = e' * c := by rw [he'def]; group
  have hgd : g * d * g⁻¹ = d := by rw [commute_d h113 h117 h (g_mem_P R g), mul_inv_cancel_right]
  have h4 : g * y * g⁻¹ = e' ^ j * y := by
    rw [hyw, hjk]
    calc g * (c ^ j * d ^ k) * g⁻¹ = (g * c * g⁻¹) ^ j * (g * d * g⁻¹) ^ k := by
          rw [conj_zpow, conj_zpow]
          group
      _ = e' ^ j * (c ^ j * d ^ k) := by rw [hgc, hgd, he'c.mul_zpow]; group
  have h5 : e' ^ j = 1 := by
    have e : g * y * g⁻¹ = y := by rw [hycent g (g_mem_P R g), mul_inv_cancel_right]
    rw [e] at h4
    calc e' ^ j = e' ^ j * y * y⁻¹ := by group
      _ = 1 := by rw [← h4, mul_inv_cancel]
  have he'3 : orderOf e' = 3 := by
    refine orderOf_eq_prime ?_ he'1
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp he'
    rw [← hm, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hd3, one_zpow]
  have h3j : ((3 : ℕ) : ℤ) ∣ j := by
    rw [← he'3]
    exact orderOf_dvd_iff_zpow_eq_one.mpr h5
  have hcj : c ^ j = 1 := by
    obtain ⟨t, rfl⟩ := h3j
    rw [zpow_mul, zpow_natCast, hc3, one_zpow]
  rw [hyw, hjk, hcj, one_mul]
  exact Subgroup.zpow_mem_zpowers d k

theorem commute_a_of_mem_zpowers_c (h : Sec11Data G A c L a R Y d x s r g)
    (ha : a ∈ (Subgroup.upperCentralSeries (sec11P R g) 2).map (sec11P R g).subtype) {y : G}
    (hyP : y ∈ sec11P R g) (hmem : y * a * y⁻¹ * a⁻¹ ∈ Subgroup.zpowers c) :
    y * a = a * y := by
  have hexp : ∀ y ∈ A, y ^ 3 = 1 := h.mem_partTwoF.1.2
  have hcent := commutator_central_of_mem_secondCenter ha hyP
  set e := y * a * y⁻¹ * a⁻¹ with hedef
  have he : e = ⁅a, y⁆⁻¹ := by rw [hedef, commutatorElement_def]; group
  have hecent : ∀ q ∈ sec11P R g, q * e = e * q := fun q hq => by
    rw [he]
    exact (Commute.inv_right (hcent q hq)).eq
  by_contra hne
  have he1 : e ≠ 1 := by
    intro h0
    apply hne
    calc y * a = e * (a * y) := by rw [hedef]; group
      _ = a * y := by rw [h0, one_mul]
  have he3 : e ^ 3 = 1 := by
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hmem
    rw [← hm, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hexp c h.mem_A,
      one_zpow]
  have hce : c ∈ Subgroup.zpowers e :=
    Item1115Proof.mem_zpowers_of_orderOf_dvd (Subgroup.mem_zpowers c) hmem
      (by rw [(Item1115Proof.orderOf_c_d h).1, orderOf_eq_prime he3 he1])
  have hgc : g * c = c * g := by
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hce
    rw [← hm]
    exact (Commute.zpow_right (hecent g (g_mem_P R g)) m).eq
  apply h.g_not_mem
  apply Sec10.mem_normalizer_zpowers_of_conj_mem
  rw [hgc, mul_inv_cancel_right]
  exact Subgroup.mem_zpowers c

theorem commute_r_a (h45 : Sec4.Item4_5) (h113 : Item113) (h : Sec11Data G A c L a R Y d x s r g)
    (ha : a ∈ (Subgroup.upperCentralSeries (sec11P R g) 2).map (sec11P R g).subtype) :
    r * a = a * r := by
  have hexp : ∀ y ∈ A, y ^ 3 = 1 := h.mem_partTwoF.1.2
  have hrR := (Item1116Proof.mem_R h).1
  have hrN : r ∈ Subgroup.normalizer ((Subgroup.closure {c, a} : Subgroup G) : Set G) :=
    h.closure_rs_le_normalizer h45 h113 (Subgroup.subset_closure (by simp))
  have hca : c * a = a * c :=
    congrArg Subtype.val (h.mem_partTwoF.1.1.is_comm.comm ⟨c, h.mem_A⟩ ⟨a, h.a_mem⟩)
  have hra : r * a * r⁻¹ ∈ Subgroup.closure ({c, a} : Set G) :=
    (Subgroup.mem_normalizer_iff.mp hrN a).mp (Subgroup.subset_closure (by simp))
  obtain ⟨i, j, hij⟩ := Sec12.exists_zpow_mul_zpow_of_mem_closure_pair hca hra
  have hrc : r ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G) := h.isSylowOf.le hrR
  have haNc : a ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G) := by
    apply Sec10.mem_normalizer_zpowers_of_conj_mem
    rw [← hca, mul_inv_cancel_right]
    exact Subgroup.mem_zpowers c
  have hmem : r * a * r⁻¹ * a⁻¹ ∈ Subgroup.zpowers c := by
    refine Item1123Proof.conj_mul_inv_mem_of_pow_three_mem hrc haNc
      (by rw [hexp a h.a_mem]; exact Subgroup.one_mem _)
      (Item1116Proof.exists_pow_eq_one_of_mem h hrR) (k := j) ?_
    have hcom : Commute (c ^ i) (a ^ j) := (Commute.zpow_zpow hca i j)
    rw [hij, hcom.eq, ← mul_assoc, inv_mul_cancel, one_mul]
    exact Subgroup.zpow_mem_zpowers c i
  exact commute_a_of_mem_zpowers_c h ha (R_le_P R g hrR) hmem

theorem commute_s_a (h113 : Item113) (h : Sec11Data G A c L a R Y d x s r g)
    (ha : a ∈ (Subgroup.upperCentralSeries (sec11P R g) 2).map (sec11P R g).subtype) :
    s * a = a * s :=
  commute_a_of_mem_zpowers_c h ha (R_le_P R g (Item1116Proof.mem_R h).2.2)
    (Item1115Proof.comm_s_a_mem h113 h)

theorem normalizer_le_or_case (h45 : Sec4.Item4_5) (h113 : Item113) (h117 : Item117)
    (hbig : Sec11Big G A c L a R Y d x s r g) {v : G}
    (hvN : v ∉ Subgroup.closure ({x ^ 9, v ^ 3} : Set G))
    (hgN : g ∈ Subgroup.normalizer ((Subgroup.closure {x ^ 9, v ^ 3} : Subgroup G) : Set G))
    (hZ : ∀ z ∈ sec11P R g ⊓ Y, (∀ w ∈ sec11P R g ⊓ Y, z * w = w * z) →
      z ∈ Subgroup.closure ({x ^ 9, v ^ 3} : Set G))
    (hcomm : ∃ w ∈ Subgroup.closure ({x ^ 9, v ^ 3} : Set G),
      (x ^ 3)⁻¹ * g⁻¹ * x ^ 3 * g = v * w) :
    Subgroup.normalizer ((sec11P R g : Subgroup G) : Set G) ≤
        Subgroup.normalizer ((Subgroup.closure {c, d} : Subgroup G) : Set G) ∨
      (A ≤ (Subgroup.upperCentralSeries (sec11P R g) 2).map (sec11P R g).subtype ∧
        (Subgroup.upperCentralSeries (sec11P R g) 2).map (sec11P R g).subtype ≤ R ∧
        Subgroup.normalizer ((sec11P R g : Subgroup G) : Set G) ≤
          Subgroup.normalizer (A : Set G) ∧
        Subgroup.normalizer ((sec11P R g : Subgroup G) : Set G) ≤
          Subgroup.normalizer (Subgroup.zpowers d : Set G) ∧
        r * a = a * r ∧ s * a = a * s) := by
  have h := hbig.toSec11Data
  have hZR := secondCenter_le_R h45 h hbig.orderOf_g hvN hgN hZ hcomm
  by_cases ha : a ∈ (Subgroup.upperCentralSeries (sec11P R g) 2).map (sec11P R g).subtype
  · right
    have hA := A_le_secondCenter h113 h117 h ha
    exact ⟨hA, hZR, normalizer_le_normalizer_A h113 h hZR hA,
      normalizer_le_normalizer_d h45 h113 h117 h hZR, commute_r_a h45 h113 h ha,
      commute_s_a h113 h ha⟩
  · left
    exact normalizer_le_of_not_mem h113 h117 h hZR ha

end Data

end Item1119Proof

section Main


theorem item1119_of (h45 : Sec4.Item4_5) (h113 : Item113) (h117 : Item117)
    (hcomm : Step1119Comm) (hsym : Step1119Sym) : Item1119 := by
  intro G _ _ A c L a R Y d x s r g hbig
  by_cases hN : Subgroup.normalizer ((sec11P R g : Subgroup G) : Set G) ≤
      Subgroup.normalizer ((Subgroup.closure {c, d} : Subgroup G) : Set G)
  · exact ⟨c, L, a, R, Y, x, s, r, g, hbig, hN⟩
  obtain ⟨v, hvN, hgN, hZ, hc⟩ := hcomm G A c L a R Y d x s r g hbig
  rcases Item1119Proof.normalizer_le_or_case h45 h113 h117 hbig hvN hgN hZ hc with
    hN' | ⟨hA, hZR, hNA, hNd, hra, hsa⟩
  · exact absurd hN' hN
  · exact hsym G A c L a R Y d x s r g hbig hA hZR hNA hNd hra hsa hN

end Main


end CFSG.RankThree.PartTwo.Sec11
