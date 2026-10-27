module

public import CFSG.Quasithin.Recognition.St84.Gen.D4qAmalBorel
public import CFSG.Quasithin.Recognition.St84.Gen.D4qVertexOneDefs
import CFSG.Quasithin.Background.SpecialPowCenter
import CFSG.Quasithin.Recognition.St84.Gen.L2SectionHall
import CFSG.Quasithin.Recognition.St84.Gen.VertexComplement
public import CFSG.Quasithin.Recognition.St84.Gen.CoprimeComplement

public section

namespace CFSG.Quasithin.F112R.St84

open Matrix CFSG.Open CFSG.Quasithin CFSG.Quasithin.F1 CFSG.QuasithinUnique
  CFSG.LieType.BorelTits
open scoped MatrixGroups commutatorElement

open Subgroup

variable {G : Type} [Group G] [Finite G] {L1 L2 S : Subgroup G} {f : ℕ}

private theorem specialPow_commutator_eq_centerOf (hD : D4qLocalData L1 L2 S f) :
    ⁅pCoreOf 2 L1, pCoreOf 2 L1⁆ = centerOf (pCoreOf 2 L1) ∧
      Nat.card (centerOf (pCoreOf 2 L1)) = 2 ^ f := by
  have h2 : 2 ≤ 2 ^ f :=
    Nat.succ_le_iff.mpr (Nat.one_lt_two_pow (by have := hD.one_le; omega))
  exact CFSG.Quasithin.H13.commutator_eq_centerOf_of_isSpecialPow (p := 2) (q := 2 ^ f)
    (w := 4) (by norm_num) h2 hD.special_left

private theorem centerOf_sq_eq_one (hD : D4qLocalData L1 L2 S f) :
    ∀ z ∈ centerOf (pCoreOf 2 L1), z * z = 1 := by
  obtain ⟨hsp, hcard, hZcard⟩ := hD.special_left
  rcases hsp.2 with ⟨hab, -⟩ | ⟨-, -, hZ2⟩
  · exfalso
    have htop : Subgroup.center ↥(pCoreOf 2 L1) = ⊤ := by
      rw [eq_top_iff]
      intro x _
      rw [Subgroup.mem_center_iff]
      intro y
      exact hab.is_comm.comm y x
    rw [htop, Subgroup.card_top, hD.card_left] at hZcard
    have h9 : 9 * f = f := Nat.pow_right_injective (by norm_num) hZcard
    have h1 : 1 ≤ f := hD.one_le
    omega
  · intro z hz
    have hzQ : z ∈ pCoreOf 2 L1 := (Subgroup.mem_inf.mp hz).1
    have hz' : (⟨z, hzQ⟩ : ↥(pCoreOf 2 L1)) ∈ Subgroup.center ↥(pCoreOf 2 L1) := by
      rw [Subgroup.mem_center_iff]
      intro y
      exact Subtype.ext
        (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hz).2 y y.2)
    have h := hZ2 ⟨z, hzQ⟩ hz'
    have := congrArg (fun w : ↥(pCoreOf 2 L1) => (w : G)) h
    simpa [Subgroup.coe_pow, pow_two] using this

private theorem centerOf_ne_bot (hD : D4qLocalData L1 L2 S f) :
    centerOf (pCoreOf 2 L1) ≠ ⊥ := by
  intro hbot
  have h := (specialPow_commutator_eq_centerOf hD).2
  rw [hbot, Subgroup.card_bot] at h
  have h2 : 1 < 2 ^ f := Nat.one_lt_two_pow (n := f) (by have := hD.one_le; omega)
  omega

private theorem conj_mem_centerOf_of_mem_normalizer {Q : Subgroup G} {h : G}
    (hh : h ∈ Subgroup.normalizer (Q : Set G)) {z : G} (hz : z ∈ centerOf Q) :
    h * z * h⁻¹ ∈ centerOf Q := by
  obtain ⟨hzQ, hzC⟩ := Subgroup.mem_inf.mp hz
  refine Subgroup.mem_inf.mpr ⟨(Subgroup.mem_normalizer_iff.mp hh z).mp hzQ, ?_⟩
  rw [Subgroup.mem_centralizer_iff] at hzC ⊢
  intro y hy
  have hy' : h⁻¹ * y * h ∈ Q := by
    simpa using (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hh) y).mp hy
  calc y * (h * z * h⁻¹) = h * ((h⁻¹ * y * h) * z) * h⁻¹ := by group
    _ = h * (z * (h⁻¹ * y * h)) * h⁻¹ := by rw [hzC (h⁻¹ * y * h) hy']
    _ = h * z * h⁻¹ * y := by group

private def commFixing (Q : Subgroup G) (h : G) : Subgroup G where
  carrier := {v | v ∈ Q ∧ ⁅h, v⁆ ∈ centerOf Q}
  one_mem' := ⟨Q.one_mem, by rw [commutatorElement_def]; simp⟩
  mul_mem' := by
    rintro u v ⟨huQ, hcu⟩ ⟨hvQ, hcv⟩
    refine ⟨Q.mul_mem huQ hvQ, ?_⟩
    have hcomm : u * ⁅h, v⁆ * u⁻¹ = ⁅h, v⁆ := by
      have hcu' := (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hcv).2) u huQ
      rw [show u * ⁅h, v⁆ * u⁻¹ = ⁅h, v⁆ by rw [hcu']; group]
    have heq : ⁅h, u * v⁆ = ⁅h, u⁆ * ⁅h, v⁆ := by
      rw [commutatorElement_def]
      rw [show h * (u * v) * h⁻¹ * (u * v)⁻¹ = ⁅h, u⁆ * (u * ⁅h, v⁆ * u⁻¹) by
        rw [commutatorElement_def]; group]
      rw [hcomm]
    rw [heq]
    exact (centerOf Q).mul_mem hcu hcv
  inv_mem' := by
    rintro u ⟨huQ, hcu⟩
    refine ⟨Q.inv_mem huQ, ?_⟩
    have hcu' : u * ⁅h, u⁆ = ⁅h, u⁆ * u :=
      (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hcu).2) u huQ
    have hinv : u⁻¹ * ⁅h, u⁆⁻¹ * u = ⁅h, u⁆⁻¹ := by
      have hinv2 := congrArg Inv.inv hcu'
      have h' : u⁻¹ * ⁅h, u⁆⁻¹ = ⁅h, u⁆⁻¹ * u⁻¹ := by
        simpa [_root_.mul_inv_rev] using hinv2.symm
      rw [h']
      group
    have heq : ⁅h, u⁻¹⁆ = ⁅h, u⁆⁻¹ := by
      rw [commutatorElement_def]
      rw [show h * u⁻¹ * h⁻¹ * (u⁻¹)⁻¹ = u⁻¹ * ⁅h, u⁆⁻¹ * u by
        rw [commutatorElement_def]; group]
      rw [hinv]
    rw [heq]
    exact (centerOf Q).inv_mem hcu

private theorem centerOf_le_commFixing {Q : Subgroup G} {h : G}
    (hh : h ∈ Subgroup.normalizer (Q : Set G)) :
    centerOf Q ≤ commFixing Q h := by
  intro z hz
  refine ⟨(Subgroup.mem_inf.mp hz).1, ?_⟩
  have hconj : h * z * h⁻¹ ∈ centerOf Q := conj_mem_centerOf_of_mem_normalizer hh hz
  rw [commutatorElement_def]
  exact (centerOf Q).mul_mem hconj ((centerOf Q).inv_mem hz)

private theorem commutatorElement_mul_centerOf_left {Q : Subgroup G} {c x y : G}
    (hc : c ∈ centerOf Q) (hx : x ∈ Q) (hy : y ∈ Q) : ⁅c * x, y⁆ = ⁅x, y⁆ := by
  have hcxy : c * (x * y * x⁻¹) = (x * y * x⁻¹) * c :=
    (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hc).2 _
      (Q.mul_mem (Q.mul_mem hx hy) (Q.inv_mem hx))).symm
  rw [commutatorElement_def]
  rw [show (c * x) * y * (c * x)⁻¹ * y⁻¹ = c * (x * y * x⁻¹) * c⁻¹ * y⁻¹ by group]
  rw [hcxy]
  group

private theorem commutatorElement_mul_centerOf_right {Q : Subgroup G} {c x y : G}
    (hc : c ∈ centerOf Q) (hx : x ∈ Q) (hy : y ∈ Q) : ⁅x, y * c⁆ = ⁅x, y⁆ := by
  have hcy : c * y = y * c :=
    (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hc).2 y hy).symm
  calc ⁅x, y * c⁆ = ⁅y * c, x⁆⁻¹ := (commutatorElement_inv _ _).symm
    _ = ⁅c * y, x⁆⁻¹ := by rw [← hcy]
    _ = ⁅y, x⁆⁻¹ := by rw [commutatorElement_mul_centerOf_left hc hy hx]
    _ = ⁅x, y⁆ := commutatorElement_inv _ _

private theorem conj_commutator_eq_self {Q Z : Subgroup G} (hZ : Z ≤ centerOf Q) {h u v : G}
    (hu : u ∈ Q) (hv : v ∈ Q) (hcu : ⁅h, u⁆ ∈ Z) (hcv : ⁅h, v⁆ ∈ Z) :
    h * ⁅u, v⁆ * h⁻¹ = ⁅u, v⁆ := by
  have hcuZ : ⁅h, u⁆ ∈ centerOf Q := hZ hcu
  have hcvZ : ⁅h, v⁆ ∈ centerOf Q := hZ hcv
  have hcvQ : ⁅h, v⁆ ∈ Q := (Subgroup.mem_inf.mp hcvZ).1
  have hua : h * u * h⁻¹ = ⁅h, u⁆ * u := by rw [commutatorElement_def]; group
  have hvb : h * v * h⁻¹ = ⁅h, v⁆ * v := by rw [commutatorElement_def]; group
  calc h * ⁅u, v⁆ * h⁻¹
      = (h * u * h⁻¹) * (h * v * h⁻¹) * (h * u * h⁻¹)⁻¹ * (h * v * h⁻¹)⁻¹ := by group
    _ = (⁅h, u⁆ * u) * (⁅h, v⁆ * v) * (⁅h, u⁆ * u)⁻¹ * (⁅h, v⁆ * v)⁻¹ := by rw [hua, hvb]
    _ = ⁅⁅h, u⁆ * u, ⁅h, v⁆ * v⁆ := (commutatorElement_def _ _).symm
    _ = ⁅u, ⁅h, v⁆ * v⁆ :=
      commutatorElement_mul_centerOf_left hcuZ hu (Q.mul_mem hcvQ hv)
    _ = ⁅u, v * ⁅h, v⁆⁆ := by
        rw [show v * ⁅h, v⁆ = ⁅h, v⁆ * v from
          Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hcvZ).2 v hv]
    _ = ⁅u, v⁆ := commutatorElement_mul_centerOf_right hcvZ hu hv

private theorem conj_eq_self_of_mem_commutator {Q Z : Subgroup G} (hZ : Z ≤ centerOf Q) {h : G}
    (hh : ∀ v ∈ Q, ⁅h, v⁆ ∈ Z) {z : G} (hz : z ∈ ⁅Q, Q⁆) :
    h * z * h⁻¹ = z := by
  rw [Subgroup.commutator_def] at hz
  induction hz using Subgroup.closure_induction with
  | mem x hx =>
      obtain ⟨u, hu, v, hv, rfl⟩ := hx
      exact conj_commutator_eq_self hZ hu hv (hh u hu) (hh v hv)
  | one => simp
  | mul x y _ _ ihx ihy =>
      calc h * (x * y) * h⁻¹ = (h * x * h⁻¹) * (h * y * h⁻¹) := by group
        _ = x * y := by rw [ihx, ihy]
  | inv x _ ih =>
      calc h * x⁻¹ * h⁻¹ = (h * x * h⁻¹)⁻¹ := by group
        _ = x⁻¹ := by rw [ih]

private theorem commutatorElement_eq_one_of_odd {Q Z : Subgroup G} (hZ : Z ≤ centerOf Q)
    {h : G} (hh : ∀ v ∈ Q, ⁅h, v⁆ ∈ Z) (hZh : ∀ z ∈ Z, h * z * h⁻¹ = z)
    (hZ2 : ∀ z ∈ Z, z * z = 1) (hodd : Odd (orderOf h)) :
    ∀ v ∈ Q, ⁅h, v⁆ = 1 := by
  intro v hv
  set c : G := ⁅h, v⁆ with hc
  have hcZ : c ∈ Z := hh v hv
  have hcv : h * v * h⁻¹ = c * v := by rw [hc, commutatorElement_def]; group
  have hcpow : ∀ m : ℕ, h * c ^ m * h⁻¹ = c ^ m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
        rw [pow_succ]
        calc h * (c ^ m * c) * h⁻¹ = (h * c ^ m * h⁻¹) * (h * c * h⁻¹) := by group
          _ = c ^ m * c := by rw [ih, hZh c hcZ]
  have hstep : ∀ m : ℕ, h ^ m * v * (h ^ m)⁻¹ = c ^ m * v := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
        calc h ^ (m + 1) * v * (h ^ (m + 1))⁻¹ = h * (h ^ m * v * (h ^ m)⁻¹) * h⁻¹ := by
              group
          _ = h * (c ^ m * v) * h⁻¹ := by rw [ih]
          _ = (h * c ^ m * h⁻¹) * (h * v * h⁻¹) := by group
          _ = c ^ m * (c * v) := by rw [hcpow, hcv]
          _ = c ^ (m + 1) * v := by rw [pow_succ]; group
  have hck : c ^ orderOf h = 1 := by
    have hok := hstep (orderOf h)
    rw [pow_orderOf_eq_one] at hok
    simpa using hok.symm
  have hc2 : c ^ 2 = 1 := by rw [pow_two]; exact hZ2 c hcZ
  obtain ⟨t, ht⟩ := hodd
  rw [ht] at hck
  have h2 : c ^ (2 * t) = 1 := by rw [pow_mul, hc2, one_pow]
  have h3 : c ^ (2 * t + 1) = c := by rw [pow_succ, h2, one_mul]
  rw [h3] at hck
  exact hck

private theorem le_normalizer_commFixing (hD : D4qLocalData L1 L2 S f) {h : G}
    (hh : h ∈ trivOTwoQuot L1) :
    L1 ≤ Subgroup.normalizer (commFixing (pCoreOf 2 L1) h : Set G) := by
  rw [Subgroup.le_normalizer_iff]
  intro l hl v hv
  obtain ⟨hvQ, hcv⟩ := hv
  obtain ⟨-, htriv⟩ := mem_trivOTwoQuot.mp hh
  set n : G := h * l * h⁻¹ * l⁻¹ with hn
  set c : G := ⁅h, v⁆ with hc
  set x : G := l * v * l⁻¹ with hx
  have hnQ : n ∈ pCoreOf 2 L1 := by rw [hn]; exact htriv l hl
  have hxQ : x ∈ pCoreOf 2 L1 := by
    rw [hx]
    exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 L1 hl) v).mp hvQ
  have hcZ : c ∈ centerOf (pCoreOf 2 L1) := hcv
  refine ⟨hxQ, ?_⟩
  have hlc : l * c = c * l := by
    have hZ : c ∈ centerOf L1 := by
      rw [← hD.center_left]
      exact hcZ
    exact Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hZ).2 l hl
  have hcn : n * c = c * n :=
    Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hcZ).2 n hnQ
  have hlh : h * l * h⁻¹ = n * l := by rw [hn]; group
  have hvh : h * v * h⁻¹ = c * v := by rw [hc, commutatorElement_def]; group
  have hconj : h * x * h⁻¹ = n * (c * x) * n⁻¹ := by
    rw [hx]
    calc h * (l * v * l⁻¹) * h⁻¹ = (h * l * h⁻¹) * (h * v * h⁻¹) * (h * l * h⁻¹)⁻¹ := by
          group
      _ = (n * l) * (c * v) * (n * l)⁻¹ := by rw [hlh, hvh]
      _ = n * (c * (l * v * l⁻¹)) * n⁻¹ := by
          rw [show n * l * (c * v) * (n * l)⁻¹ = n * (l * c) * v * (n * l)⁻¹ by group]
          rw [hlc]
          group
  have hfin : ⁅h, x⁆ = c * ⁅n, x⁆ := by
    rw [commutatorElement_def, hconj]
    calc n * (c * x) * n⁻¹ * x⁻¹ = (n * c) * (x * n⁻¹ * x⁻¹) := by group
      _ = (c * n) * (x * n⁻¹ * x⁻¹) := by rw [hcn]
      _ = c * (n * x * n⁻¹ * x⁻¹) := by group
  have hnxZ : ⁅n, x⁆ ∈ centerOf (pCoreOf 2 L1) := by
    rw [← (specialPow_commutator_eq_centerOf hD).1]
    exact Subgroup.commutator_mem_commutator hnQ hxQ
  rw [hfin]
  exact (centerOf (pCoreOf 2 L1)).mul_mem hcZ hnxZ

theorem D4qLocalData.eq_one_of_mem_pCoreOf_left_of_commute (hf : 2 ≤ f) (hH : Hyp111 L1 L2 S)
    (hD : D4qLocalData L1 L2 S f) (h1 : IsL2Quot (3 * f) (oTwoQuot ↥L1)) {H : Subgroup G}
    (hHB : H ≤ bigB L1 L2 S) (hSH : S ⊔ H = bigB L1 L2 S) (hSinfH : S ⊓ H = ⊥)
    (hHcard : Nat.card H = (2 ^ (3 * f) - 1) * (2 ^ f - 1))
    (hHcomm : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a) {x : G} (hx : x ∈ pCoreOf 2 L1)
    (hxH : ∀ h ∈ H ⊓ trivOTwoQuot L1, h * x * h⁻¹ = x) : x = 1 := by
  classical
  set Q : Subgroup G := pCoreOf 2 L1 with hQ
  set Z : Subgroup G := centerOf Q with hZ
  set H₀ : Subgroup G := H ⊓ trivOTwoQuot L1 with hH0
  obtain ⟨-, -, -, -, hsupB⟩ :=
    hD.torus_left_of_hall hH h1 hHB hSH hSinfH hHcard hHcomm
  have hZL : Z = centerOf L1 := hD.center_left
  have hZfix : ∀ z ∈ Z, (∀ h ∈ H₀, h * z * h⁻¹ = z) → z = 1 := by
    intro z hz hzfix
    have hzL : z ∈ centerOf L1 := by rw [← hZL]; exact hz
    have hL1C : L1 ≤ Subgroup.centralizer ({z} : Set G) := by
      intro l hl
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hzL).2 l hl
    have hH0C : H₀ ≤ Subgroup.centralizer ({z} : Set G) := by
      intro h hh
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc h * z = (h * z * h⁻¹) * h := by group
        _ = z * h := by rw [hzfix h hh]
    have hsupBC : L1 ⊔ bigB L1 L2 S ≤ Subgroup.centralizer ({z} : Set G) := by
      rw [hsupB]
      exact sup_le hL1C hH0C
    have hBigC : bigB L1 L2 S ≤ Subgroup.centralizer ({z} : Set G) :=
      le_sup_right.trans hsupBC
    have hB2 : borelOf L2 S ≤ Subgroup.centralizer ({z} : Set G) :=
      (le_sup_right.trans le_sup_left).trans hBigC
    exact hD.eq_one_of_mem_centerOf_left_of_commute hf hH h1 hz fun b hb => by
      have hbz := hB2 hb
      rw [Subgroup.mem_centralizer_singleton_iff] at hbz
      calc b * z * b⁻¹ = z * b * b⁻¹ := by rw [hbz]
        _ = z := by group
  have hdich : ∀ h ∈ H₀, commFixing Q h = Z ∨ commFixing Q h = Q := by
    intro h hh
    have hhNQ : h ∈ Subgroup.normalizer (Q : Set G) :=
      hH.bigB_le_normalizer_pCoreOf_left (hHB (Subgroup.mem_inf.mp hh).1)
    refine hD.irred_left (commFixing Q h) (centerOf_le_commFixing hhNQ) ?_ ?_
    · intro v hv
      exact hv.1
    · exact le_normalizer_commFixing hD (Subgroup.mem_inf.mp hh).2
  by_cases hcase : ∃ h ∈ H₀, commFixing Q h = Z
  · obtain ⟨h, hhh, hW⟩ := hcase
    have hxW : x ∈ commFixing Q h := by
      refine ⟨hx, ?_⟩
      rw [commutatorElement_def, hxH h hhh]
      simp
    rw [hW] at hxW
    exact hZfix x hxW hxH
  · exfalso
    have hall : ∀ h ∈ H₀, commFixing Q h = Q := fun h hh =>
      (hdich h hh).resolve_left fun hW => hcase ⟨h, hh, hW⟩
    have hZle : Z ≤ ⊥ := by
      intro z hz
      rw [Subgroup.mem_bot]
      refine hZfix z hz ?_
      intro h hh
      have hhQ : ∀ v ∈ Q, ⁅h, v⁆ ∈ Z := by
        intro v hv
        have hv' : v ∈ commFixing Q h := by rw [hall h hh]; exact hv
        exact hv'.2
      have hzQ : z ∈ ⁅Q, Q⁆ := by
        rw [(specialPow_commutator_eq_centerOf hD).1]
        exact hz
      exact conj_eq_self_of_mem_commutator le_rfl hhQ hzQ
    exact centerOf_ne_bot hD (le_bot_iff.mp hZle)

private theorem odd_of_dvd_two_pow_sub_one {k : ℕ} (hk : 1 ≤ k) {m : ℕ} (hm : m ∣ 2 ^ k - 1) :
    Odd m := by
  have h2 : Even (2 ^ k) := (show Even 2 by norm_num).pow_of_ne_zero (by omega)
  have hodd : Odd (2 ^ k - 1) := Nat.Even.sub_odd Nat.one_le_two_pow h2 odd_one
  exact hodd.of_dvd_nat hm

private theorem torus_faithful_left (hH : Hyp111 L1 L2 S) (hD : D4qLocalData L1 L2 S f)
    (h1 : IsL2Quot (3 * f) (oTwoQuot ↥L1)) {H : Subgroup G} (hHB : H ≤ bigB L1 L2 S)
    {h : G} (hh : h ∈ H ⊓ trivOTwoQuot L1)
    (hcardH0 : Nat.card ↥(H ⊓ trivOTwoQuot L1) = 2 ^ f - 1)
    (hH0infL : H ⊓ trivOTwoQuot L1 ⊓ L1 = ⊥)
    (htriv : ∀ x ∈ pCoreOf 2 L1, h * x * h⁻¹ * x⁻¹ ∈ centerOf (pCoreOf 2 L1)) :
    h = 1 := by
  classical
  have hS1 : S ≤ L1 := hD.le_left hH h1
  have hhH : h ∈ H := (Subgroup.mem_inf.mp hh).1
  have hhhB : h ∈ bigB L1 L2 S := hHB hhH
  have hZh : ∀ z ∈ centerOf (pCoreOf 2 L1), h * z * h⁻¹ = z := by
    intro z hz
    have hzQ : z ∈ ⁅pCoreOf 2 L1, pCoreOf 2 L1⁆ := by
      rw [(specialPow_commutator_eq_centerOf hD).1]
      exact hz
    exact conj_eq_self_of_mem_commutator le_rfl htriv hzQ
  have hodd : Odd (orderOf h) :=
    odd_of_dvd_two_pow_sub_one (by have := hD.one_le; omega) <|
      hcardH0 ▸ Subgroup.orderOf_dvd_natCard _ hh
  have hcen : ∀ v ∈ pCoreOf 2 L1, h * v * h⁻¹ = v := by
    intro v hv
    have hcv : ⁅h, v⁆ = 1 :=
      commutatorElement_eq_one_of_odd le_rfl htriv hZh (centerOf_sq_eq_one hD) hodd v hv
    rw [commutatorElement_def] at hcv
    calc h * v * h⁻¹ = (h * v * h⁻¹ * v⁻¹) * v := by group
      _ = v := by rw [hcv, one_mul]
  have hEq : L1 ⊔ S ⊔ borelOf L2 S = L1 ⊔ bigB L1 L2 S := by
    have hLS : L1 ⊔ S = L1 := sup_eq_left.mpr hS1
    have hB2 : borelOf L2 S ≤ bigB L1 L2 S := le_sup_right.trans le_sup_left
    have hbig : bigB L1 L2 S ≤ L1 ⊔ borelOf L2 S := by
      rw [bigB]
      exact sup_le (sup_le ((borelOf_le L1 S).trans le_sup_left) le_sup_right)
        (hS1.trans le_sup_left)
    rw [hLS]
    exact le_antisymm (sup_le le_sup_left (hB2.trans le_sup_right))
      (sup_le le_sup_left hbig)
  have hhChar : h ∈ (L1 ⊔ S ⊔ borelOf L2 S) ⊓
      Subgroup.centralizer (pCoreOf 2 (L1 ⊔ S ⊔ borelOf L2 S) : Set G) := by
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · rw [hEq]
      exact Subgroup.mem_sup_right hhhB
    · rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [hEq, hD.pCoreOf_sup_bigB_left hH h1] at hy
      have hyh : h * y * h⁻¹ = y := hcen y hy
      calc y * h = (h * y * h⁻¹) * h := by rw [hyh]
        _ = h * y := by group
  have hhQ : h ∈ pCoreOf 2 L1 := by
    have hq := hH.h1.charTwo hhChar
    rwa [hEq, hD.pCoreOf_sup_bigB_left hH h1] at hq
  have hhL : h ∈ L1 := (pCoreOf_le 2 L1) hhQ
  have hhbot : h ∈ H ⊓ trivOTwoQuot L1 ⊓ L1 := ⟨hh, hhL⟩
  rw [hH0infL, Subgroup.mem_bot] at hhbot
  exact hhbot

private theorem levi_mulEquiv_left (hH : Hyp111 L1 L2 S) (hD : D4qLocalData L1 L2 S f)
    (h1 : IsL2Quot (3 * f) (oTwoQuot ↥L1)) {K : Subgroup G} (hKL : K ≤ L1)
    (hsupQK : pCoreOf 2 L1 ⊔ K = L1) (hinfQK : pCoreOf 2 L1 ⊓ K = ⊥) :
    Nonempty (↥K ≃* SL(2, GaloisField 2 (3 * f))) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨c1⟩ := hD.exists_coordLeft hH h1
  letI := c1.field
  letI := c1.fintype
  let φ : ↥K →* SL(2, c1.F) := c1.α.comp (Subgroup.inclusion hKL)
  have hφinj : Function.Injective φ := by
    intro a b hab
    have hx1 : φ (a * b⁻¹) = 1 := by rw [map_mul, map_inv, hab, mul_inv_cancel]
    have hx1' : c1.α (Subgroup.inclusion hKL (a * b⁻¹)) = 1 := hx1
    have hxQ : ((a * b⁻¹ : ↥K) : G) ∈ pCoreOf 2 L1 := (c1.ker _).mp hx1'
    have hxK : ((a * b⁻¹ : ↥K) : G) ∈ K := (a * b⁻¹).2
    have hbot : (a * b⁻¹ : ↥K) = 1 := by
      have hmem : ((a * b⁻¹ : ↥K) : G) ∈ pCoreOf 2 L1 ⊓ K := ⟨hxQ, hxK⟩
      rw [hinfQK, Subgroup.mem_bot] at hmem
      exact Subtype.ext hmem
    rwa [mul_inv_eq_one] at hbot
  have hφsurj : Function.Surjective φ := by
    intro y
    obtain ⟨x, hx⟩ := c1.surj y
    have hKNQ : K ≤ Subgroup.normalizer (pCoreOf 2 L1 : Set G) :=
      hKL.trans (le_normalizer_pCoreOf 2 L1)
    have hxQK : (x : G) ∈ pCoreOf 2 L1 ⊔ K := by rw [hsupQK]; exact x.2
    obtain ⟨q, hqQ, k, hkK, hqk⟩ :=
      (CFSG.Quasithin.F1.mem_sup_iff_exists_mul_of_normalizes hKNQ).mp hxQK
    refine ⟨⟨k, hkK⟩, ?_⟩
    have hq1 : c1.α ⟨q, (pCoreOf_le 2 L1) hqQ⟩ = 1 :=
      (c1.ker ⟨q, (pCoreOf_le 2 L1) hqQ⟩).mpr hqQ
    have hxeq : (⟨q, (pCoreOf_le 2 L1) hqQ⟩ * ⟨k, hKL hkK⟩ : ↥L1) = x := by
      ext
      exact hqk.symm
    calc φ ⟨k, hkK⟩ = c1.α ⟨k, hKL hkK⟩ := rfl
      _ = c1.α ⟨q, (pCoreOf_le 2 L1) hqQ⟩ * c1.α ⟨k, hKL hkK⟩ := by rw [hq1, one_mul]
      _ = c1.α (⟨q, (pCoreOf_le 2 L1) hqQ⟩ * ⟨k, hKL hkK⟩) := (map_mul _ _ _).symm
      _ = c1.α x := by rw [hxeq]
      _ = y := hx
  let e1 : ↥K ≃* SL(2, c1.F) := MulEquiv.ofBijective φ ⟨hφinj, hφsurj⟩
  haveI : Fintype (GaloisField 2 (3 * f)) := Fintype.ofFinite _
  have hFcard : Fintype.card c1.F = Fintype.card (GaloisField 2 (3 * f)) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, c1.card,
      GaloisField.card 2 (3 * f) (by have := hD.one_le; omega)]
  let e : c1.F ≃+* GaloisField 2 (3 * f) := FiniteField.ringEquivOfCardEq hFcard
  let ψ : SL(2, c1.F) →* SL(2, GaloisField 2 (3 * f)) :=
    Matrix.SpecialLinearGroup.map e.toRingHom
  let ψ' : SL(2, GaloisField 2 (3 * f)) →* SL(2, c1.F) :=
    Matrix.SpecialLinearGroup.map e.symm.toRingHom
  have hψ : ψ.comp ψ' = MonoidHom.id _ := by
    ext x i j
    simp [ψ, ψ']
  have hψ' : ψ'.comp ψ = MonoidHom.id _ := by
    ext x i j
    simp [ψ, ψ']
  exact ⟨e1.trans (MonoidHom.toMulEquiv ψ ψ' hψ' hψ)⟩

private theorem coprime_card_torus (hD : D4qLocalData L1 L2 S f) {H : Subgroup G}
    (hcardH0 : Nat.card ↥(H ⊓ trivOTwoQuot L1) = 2 ^ f - 1) :
    Nat.Coprime (Nat.card ↥(H ⊓ trivOTwoQuot L1)) (Nat.card ↥(pCoreOf 2 L1)) := by
  rw [hcardH0, hD.card_left]
  have h2 : Even (2 ^ f) :=
    (show Even 2 by norm_num).pow_of_ne_zero (by have := hD.one_le; omega)
  have hodd : Odd (2 ^ f - 1) := Nat.Even.sub_odd Nat.one_le_two_pow h2 odd_one
  exact Nat.Coprime.pow_right (9 * f) (Nat.coprime_two_left.mpr hodd).symm

private theorem sup_pCoreOf_inf_centralizer (hH : Hyp111 L1 L2 S)
    (hD : D4qLocalData L1 L2 S f) (h1 : IsL2Quot (3 * f) (oTwoQuot ↥L1)) {H : Subgroup G}
    (hHB : H ≤ bigB L1 L2 S) (hSH : S ⊔ H = bigB L1 L2 S) (hSinfH : S ⊓ H = ⊥)
    (hHcard : Nat.card H = (2 ^ (3 * f) - 1) * (2 ^ f - 1))
    (hHcomm : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a) :
    pCoreOf 2 L1 ⊔ (L1 ⊓ centralizer ((H ⊓ trivOTwoQuot L1 : Subgroup G) : Set G)) = L1 := by
  classical
  set H₀ : Subgroup G := H ⊓ trivOTwoQuot L1 with hH0
  obtain ⟨-, hcardH0, -, -, -⟩ := hD.torus_left_of_hall hH h1 hHB hSH hSinfH hHcard hHcomm
  refine sup_inf_centralizer_eq_of_coprime (Q := pCoreOf 2 L1) (H := H₀) (L := L1)
    (pCoreOf_le 2 L1) (le_normalizer_pCoreOf 2 L1) ?_ (coprime_card_torus hD hcardH0) ?_
  · exact (inf_le_left.trans hHB).trans hH.bigB_le_normalizer_pCoreOf_left
  · intro h hh l hl
    exact (mem_trivOTwoQuot.mp (Subgroup.mem_inf.mp hh).2).2 l hl

private theorem inf_pCoreOf_inf_centralizer (hf : 2 ≤ f) (hH : Hyp111 L1 L2 S)
    (hD : D4qLocalData L1 L2 S f) (h1 : IsL2Quot (3 * f) (oTwoQuot ↥L1)) {H : Subgroup G}
    (hHB : H ≤ bigB L1 L2 S) (hSH : S ⊔ H = bigB L1 L2 S) (hSinfH : S ⊓ H = ⊥)
    (hHcard : Nat.card H = (2 ^ (3 * f) - 1) * (2 ^ f - 1))
    (hHcomm : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a) :
    pCoreOf 2 L1 ⊓ (L1 ⊓ centralizer ((H ⊓ trivOTwoQuot L1 : Subgroup G) : Set G)) = ⊥ := by
  classical
  set Q : Subgroup G := pCoreOf 2 L1 with hQ
  set H₀ : Subgroup G := H ⊓ trivOTwoQuot L1 with hH0
  have hcore : ∀ y ∈ Q, (∀ h ∈ H₀, h * y * h⁻¹ = y) → y = 1 := fun y hy hyfix =>
    hD.eq_one_of_mem_pCoreOf_left_of_commute hf hH h1 hHB hSH hSinfH hHcard hHcomm hy hyfix
  have h := inf_centralizer_inf_eq_bot_of_fixed (L := L1) (Q := Q) (H := H₀) hcore
  rwa [inf_comm]

private theorem inf_le_inf_centralizer {H : Subgroup G}
    (hHcomm : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a) :
    H ⊓ L1 ≤ L1 ⊓ centralizer ((H ⊓ trivOTwoQuot L1 : Subgroup G) : Set G) := by
  intro x hx
  obtain ⟨hxH, hxL⟩ := Subgroup.mem_inf.mp hx
  refine Subgroup.mem_inf.mpr ⟨hxL, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  exact (hHcomm x hxH h (Subgroup.mem_inf.mp hh).1).symm

private theorem sup_sup_centralizer_eq (hH : Hyp111 L1 L2 S) (hD : D4qLocalData L1 L2 S f)
    (h1 : IsL2Quot (3 * f) (oTwoQuot ↥L1)) {H : Subgroup G} (hHB : H ≤ bigB L1 L2 S)
    (hSH : S ⊔ H = bigB L1 L2 S) (hSinfH : S ⊓ H = ⊥)
    (hHcard : Nat.card H = (2 ^ (3 * f) - 1) * (2 ^ f - 1))
    (hHcomm : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a) :
    pCoreOf 2 L1 ⊔ ((L1 ⊓ centralizer ((H ⊓ trivOTwoQuot L1 : Subgroup G) : Set G)) ⊔
      (H ⊓ trivOTwoQuot L1)) = L1 ⊔ bigB L1 L2 S := by
  obtain ⟨-, hcardH0, -, -, hsupB⟩ :=
    hD.torus_left_of_hall hH h1 hHB hSH hSinfH hHcard hHcomm
  exact (sup_inf_centralizer_sup_eq_of_coprime (Q := pCoreOf 2 L1) (L := L1)
    (H := H ⊓ trivOTwoQuot L1) (pCoreOf_le 2 L1) (le_normalizer_pCoreOf 2 L1)
    ((inf_le_left.trans hHB).trans hH.bigB_le_normalizer_pCoreOf_left)
    (coprime_card_torus hD hcardH0)
    (fun h hh l hl => (mem_trivOTwoQuot.mp (Subgroup.mem_inf.mp hh).2).2 l hl)).trans
      hsupB.symm

private theorem inf_pCoreOf_sup_eq_bot (hf : 2 ≤ f) (hH : Hyp111 L1 L2 S)
    (hD : D4qLocalData L1 L2 S f) (h1 : IsL2Quot (3 * f) (oTwoQuot ↥L1)) {H : Subgroup G}
    (hHB : H ≤ bigB L1 L2 S) (hSH : S ⊔ H = bigB L1 L2 S) (hSinfH : S ⊓ H = ⊥)
    (hHcard : Nat.card H = (2 ^ (3 * f) - 1) * (2 ^ f - 1))
    (hHcomm : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a) :
    pCoreOf 2 L1 ⊓ ((L1 ⊓ centralizer ((H ⊓ trivOTwoQuot L1 : Subgroup G) : Set G)) ⊔
      (H ⊓ trivOTwoQuot L1)) = ⊥ :=
  inf_inf_centralizer_sup_eq_bot (Q := pCoreOf 2 L1) (L := L1)
    (H := H ⊓ trivOTwoQuot L1) (pCoreOf_le 2 L1)
    (fun x hx hxfix =>
      hD.eq_one_of_mem_pCoreOf_left_of_commute hf hH h1 hHB hSH hSinfH hHcard hHcomm hx hxfix)
    (hD.torus_left_of_hall hH h1 hHB hSH hSinfH hHcard hHcomm).2.2.2.1

private theorem irreducible_pCoreOf (hH : Hyp111 L1 L2 S) (hD : D4qLocalData L1 L2 S f)
    (h1 : IsL2Quot (3 * f) (oTwoQuot ↥L1)) {H : Subgroup G}
    (hsupQK : pCoreOf 2 L1 ⊔ (L1 ⊓ centralizer ((H ⊓ trivOTwoQuot L1 : Subgroup G) : Set G)) =
      L1) :
    ∀ W : Subgroup G, centerOf (pCoreOf 2 L1) ≤ W → W ≤ pCoreOf 2 L1 →
      (L1 ⊓ centralizer ((H ⊓ trivOTwoQuot L1 : Subgroup G) : Set G)) ≤
        Subgroup.normalizer (W : Set G) → W = centerOf (pCoreOf 2 L1) ∨ W = pCoreOf 2 L1 := by
  classical
  set Q : Subgroup G := pCoreOf 2 L1 with hQ
  set H₀ : Subgroup G := H ⊓ trivOTwoQuot L1 with hH0
  set K : Subgroup G := L1 ⊓ Subgroup.centralizer (H₀ : Set G) with hK
  intro W hZW hWQ hKW
  have hQNW : Q ≤ Subgroup.normalizer (W : Set G) := by
    rw [Subgroup.le_normalizer_iff_commutator_le_right]
    refine (Subgroup.commutator_mono le_rfl hWQ).trans ?_
    rw [(specialPow_commutator_eq_centerOf hD).1]
    exact hZW
  have hL1NW : L1 ≤ Subgroup.normalizer (W : Set G) := by
    rw [← hsupQK]
    exact sup_le hQNW hKW
  exact hD.irred_left W hZW hWQ hL1NW

private theorem vertexOne_data (hf : 2 ≤ f) (hH : Hyp111 L1 L2 S)
    (hD : D4qLocalData L1 L2 S f) (h1 : IsL2Quot (3 * f) (oTwoQuot ↥L1)) {H : Subgroup G}
    (hHB : H ≤ bigB L1 L2 S) (hSH : S ⊔ H = bigB L1 L2 S) (hSinfH : S ⊓ H = ⊥)
    (hHcard : Nat.card H = (2 ^ (3 * f) - 1) * (2 ^ f - 1))
    (hHcomm : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a)
    (hsupQK : pCoreOf 2 L1 ⊔ (L1 ⊓ centralizer ((H ⊓ trivOTwoQuot L1 : Subgroup G) : Set G)) =
      L1)
    (hinfQK : pCoreOf 2 L1 ⊓ (L1 ⊓ centralizer ((H ⊓ trivOTwoQuot L1 : Subgroup G) : Set G)) =
      ⊥) :
    D4qVertexOneData (pCoreOf 2 L1) (centerOf (pCoreOf 2 L1))
      (L1 ⊓ centralizer ((H ⊓ trivOTwoQuot L1 : Subgroup G) : Set G))
      (H ⊓ trivOTwoQuot L1) f := by
  classical
  set Q : Subgroup G := pCoreOf 2 L1 with hQ
  set Z : Subgroup G := centerOf Q with hZ
  set H₀ : Subgroup G := H ⊓ trivOTwoQuot L1 with hH0
  set K : Subgroup G := L1 ⊓ Subgroup.centralizer (H₀ : Set G) with hK
  obtain ⟨-, hcardH0, -, hH0infL, -⟩ :=
    hD.torus_left_of_hall hH h1 hHB hSH hSinfH hHcard hHcomm
  have hKL : K ≤ L1 := inf_le_left
  have hZL : Z = centerOf L1 := hD.center_left
  have hH0H : H₀ ≤ H := inf_le_left
  have hH0B : H₀ ≤ bigB L1 L2 S := hH0H.trans hHB
  have hKH0 : K ⊓ H₀ = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxK, hxH0⟩ := Subgroup.mem_inf.mp hx
    have hmem : x ∈ H₀ ⊓ L1 := ⟨hxH0, hKL hxK⟩
    rwa [hH0infL, Subgroup.mem_bot] at hmem
  exact
    { special := hD.special_left
      centerOf_eq := rfl
      levi_le_normalizer := hKL.trans (le_normalizer_pCoreOf 2 L1)
      torus_le_normalizer := hH0B.trans hH.bigB_le_normalizer_pCoreOf_left
      disjoint := disjoint_iff.mpr
        (inf_pCoreOf_sup_eq_bot hf hH hD h1 hHB hSH hSinfH hHcard hHcomm)
      levi_inf_torus := hKH0
      levi_commute_torus := fun k hk h hh =>
        (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hk).2 h hh).symm
      levi_mulEquiv := levi_mulEquiv_left hH hD h1 hKL hsupQK hinfQK
      levi_centralizes := by
        intro k hk z hz
        have hkL : k ∈ L1 := hKL hk
        have hzL : z ∈ centerOf L1 := by rw [← hZL]; exact hz
        have hcomm := Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hzL).2 k hkL
        calc k * z * k⁻¹ = (z * k) * k⁻¹ := by rw [hcomm]
          _ = z := by group
      irreducible := irreducible_pCoreOf hH hD h1 hsupQK
      card_torus := hcardH0
      torus_comm := fun a ha b hb => hHcomm a (hH0H ha) b (hH0H hb)
      torus_faithful := fun h hh htriv =>
        torus_faithful_left hH hD h1 hHB hh hcardH0 hH0infL htriv }

theorem D4qLocalData.vertexOne_left (hf : 2 ≤ f) (hH : Hyp111 L1 L2 S)
    (hD : D4qLocalData L1 L2 S f) (h1 : IsL2Quot (3 * f) (oTwoQuot ↥L1)) {H : Subgroup G}
    (hHB : H ≤ bigB L1 L2 S) (hSH : S ⊔ H = bigB L1 L2 S) (hSinfH : S ⊓ H = ⊥)
    (hHcard : Nat.card H = (2 ^ (3 * f) - 1) * (2 ^ f - 1))
    (hHcomm : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a) :
    D4qVertexOneData (pCoreOf 2 L1) (centerOf (pCoreOf 2 L1))
        (L1 ⊓ centralizer ((H ⊓ trivOTwoQuot L1 : Subgroup G) : Set G))
        (H ⊓ trivOTwoQuot L1) f ∧
      pCoreOf 2 L1 ⊔ (L1 ⊓ centralizer ((H ⊓ trivOTwoQuot L1 : Subgroup G) : Set G)) = L1 ∧
      pCoreOf 2 L1 ⊓ (L1 ⊓ centralizer ((H ⊓ trivOTwoQuot L1 : Subgroup G) : Set G)) = ⊥ ∧
      H ⊓ L1 ≤ (L1 ⊓ centralizer ((H ⊓ trivOTwoQuot L1 : Subgroup G) : Set G)) ∧
      pCoreOf 2 L1 ⊔ ((L1 ⊓ centralizer ((H ⊓ trivOTwoQuot L1 : Subgroup G) : Set G)) ⊔
        (H ⊓ trivOTwoQuot L1)) = L1 ⊔ bigB L1 L2 S :=
  ⟨vertexOne_data hf hH hD h1 hHB hSH hSinfH hHcard hHcomm
      (sup_pCoreOf_inf_centralizer hH hD h1 hHB hSH hSinfH hHcard hHcomm)
      (inf_pCoreOf_inf_centralizer hf hH hD h1 hHB hSH hSinfH hHcard hHcomm),
    sup_pCoreOf_inf_centralizer hH hD h1 hHB hSH hSinfH hHcard hHcomm,
    inf_pCoreOf_inf_centralizer hf hH hD h1 hHB hSH hSinfH hHcard hHcomm,
    inf_le_inf_centralizer hHcomm,
    sup_sup_centralizer_eq hH hD h1 hHB hSH hSinfH hHcard hHcomm⟩

end CFSG.Quasithin.F112R.St84

end
