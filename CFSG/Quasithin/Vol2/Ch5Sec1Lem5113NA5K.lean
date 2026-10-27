module

public import CFSG.Quasithin.Background.G64SymCase
public import CFSG.Quasithin.Background.C124YLA7Off
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5113FourCZ

public section

namespace CFSG.Quasithin.H13.A7Four

open Equiv Equiv.Perm CFSG.QuasithinUnique.L246.C123

@[expose] def eL : List (Perm (Fin 7)) :=
  [1, swap 1 2 * swap 3 4, swap 1 3 * swap 2 4, swap 1 4 * swap 2 3]

@[expose] def c04 : Perm (Fin 7) := swap 0 1 * swap 1 2 * swap 2 3 * swap 3 4

@[expose] def kleinL : List (Perm (Fin 7)) := [1, x7, y7, x7 * y7]

theorem mem_kleinSet_iff {b : Perm (Fin 7)} :
    b ∈ kleinSet ↔ b ∈ kleinL := by
  simp [kleinSet, kleinL]

theorem eL_check :
    (eL.all fun a => eL.all fun b => eL.contains (a * b)) &&
    eL.all (fun a => decide (a * a = 1)) &&
    eL.all (fun a => A7Std.p0L.contains a) &&
    eL.all (fun a => kleinL.contains (c04⁻¹ * a * c04)) &&
    kleinL.all (fun b => eL.contains (c04 * b * c04⁻¹)) && decide (sign c04 = 1) = true := by
  decide +kernel

theorem eL_mul {a b : Perm (Fin 7)} (ha : a ∈ eL) (hb : b ∈ eL) : a * b ∈ eL := by
  have h := eL_check
  simp only [Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem] at h
  exact h.1.1.1.1.1 a ha b hb

theorem eL_sq {a : Perm (Fin 7)} (ha : a ∈ eL) : a * a = 1 := by
  have h := eL_check
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  exact h.1.1.1.1.2 a ha

theorem eL_p0L {a : Perm (Fin 7)} (ha : a ∈ eL) : a ∈ A7Std.p0L := by
  have h := eL_check
  simp only [Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem] at h
  exact h.1.1.1.2 a ha

theorem eL_conj_klein {a : Perm (Fin 7)} (ha : a ∈ eL) :
    c04⁻¹ * a * c04 ∈ kleinSet := by
  have h := eL_check
  simp only [Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem] at h
  exact mem_kleinSet_iff.mpr (h.1.1.2 a ha)

theorem klein_conj_eL {b : Perm (Fin 7)} (hb : b ∈ kleinSet) :
    c04 * b * c04⁻¹ ∈ eL := by
  have h := eL_check
  simp only [Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem] at h
  exact h.1.2 b (mem_kleinSet_iff.mp hb)

theorem sign_c04 : sign c04 = 1 := by
  have h := eL_check
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.2

@[expose] def eA : Subgroup (alternatingGroup (Fin 7)) where
  carrier := {g | (g : Perm (Fin 7)) ∈ eL}
  mul_mem' ha hb := eL_mul ha hb
  one_mem' := List.mem_cons_self
  inv_mem' {a} ha := by
    have hinv : (a : Perm (Fin 7))⁻¹ = a := inv_eq_of_mul_eq_one_right (eL_sq ha)
    change (a : Perm (Fin 7))⁻¹ ∈ eL
    rw [hinv]
    exact ha

theorem mem_eA {g : alternatingGroup (Fin 7)} : g ∈ eA ↔ (g : Perm (Fin 7)) ∈ eL := Iff.rfl

theorem eA_le_p0 : eA ≤ A7Std.p0 := fun _ hg => eL_p0L hg

@[expose] def c04A : alternatingGroup (Fin 7) := ⟨c04, Equiv.Perm.mem_alternatingGroup.mpr sign_c04⟩

theorem isKleinConj_eA : IsKleinConj eA := by
  refine ⟨c04A, Subgroup.ext fun x => ?_⟩
  rw [_root_.CFSG.QuasithinUnique.L246.C123.mem_conjSub, mem_eA,
    _root_.CFSG.QuasithinUnique.L246.C123.mem_kleinA]
  constructor
  · intro hx
    exact eL_conj_klein hx
  · intro hx
    have h1 := klein_conj_eL hx
    have e : c04 * ((c04A⁻¹ * x * c04A : alternatingGroup (Fin 7)) : Perm (Fin 7)) * c04⁻¹ =
        (x : Perm (Fin 7)) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, c04A]
      group
    rw [e] at h1
    exact h1

theorem swap_mul_swap_mem_eL :
    ∀ a b c d : Fin 7, (a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4) → (b = 1 ∨ b = 2 ∨ b = 3 ∨ b = 4) →
      (c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4) → (d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 4) → a ≠ b → a ≠ c →
      a ≠ d → b ≠ c → b ≠ d → c ≠ d → swap a b * swap c d ∈ eL := by
  decide +kernel

theorem eq_of_three :
    ∀ p q r j : Fin 7, (p = 0 ∨ p = 5 ∨ p = 6) → (q = 0 ∨ q = 5 ∨ q = 6) →
      (r = 0 ∨ r = 5 ∨ r = 6) → p ≠ q → p ≠ r → q ≠ r → (j = 0 ∨ j = 5 ∨ j = 6) →
        j = p ∨ j = q ∨ j = r := by
  intro p q r j hp hq hr hpq hpr hqr hj
  rcases hp with rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl <;>
    rcases hr with rfl | rfl | rfl <;> rcases hj with rfl | rfl | rfl <;> simp_all

theorem conj_mem_eL {σ : Perm (Fin 7)}
    (hσ : ∀ i : Fin 7, (i = 0 ∨ i = 5 ∨ i = 6) → (σ i = 0 ∨ σ i = 5 ∨ σ i = 6))
    {x : Perm (Fin 7)} (hx : x ∈ eL) : σ * x * σ⁻¹ ∈ eL := by
  have h4 : ∀ i : Fin 7, (i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) →
      (σ i = 1 ∨ σ i = 2 ∨ σ i = 3 ∨ σ i = 4) := by
    intro i hi
    by_contra hne
    have hj : σ i = 0 ∨ σ i = 5 ∨ σ i = 6 := by
      revert hne
      generalize σ i = j
      revert j
      decide
    have h05 : σ 0 ≠ σ 5 := fun h => absurd (σ.injective h) (by decide)
    have h06 : σ 0 ≠ σ 6 := fun h => absurd (σ.injective h) (by decide)
    have h56 : σ 5 ≠ σ 6 := fun h => absurd (σ.injective h) (by decide)
    rcases eq_of_three _ _ _ _ (hσ 0 (Or.inl rfl)) (hσ 5 (Or.inr (Or.inl rfl)))
      (hσ 6 (Or.inr (Or.inr rfl))) h05 h06 h56 hj with h | h | h <;>
      · have := σ.injective h
        rcases hi with rfl | rfl | rfl | rfl <;> exact absurd this (by decide)
  have hinj : ∀ i j : Fin 7, i ≠ j → σ i ≠ σ j := fun i j hij h => hij (σ.injective h)
  have key : ∀ a b c d : Fin 7, (a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4) → (b = 1 ∨ b = 2 ∨ b = 3 ∨ b = 4) →
      (c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4) → (d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 4) → a ≠ b → a ≠ c →
      a ≠ d → b ≠ c → b ≠ d → c ≠ d → σ * (swap a b * swap c d) * σ⁻¹ ∈ eL := by
    intro a b c d ha hb hc hd hab hac had hbc hbd hcd
    have e : σ * (swap a b * swap c d) * σ⁻¹ = swap (σ a) (σ b) * swap (σ c) (σ d) := by
      rw [swap_apply_apply, swap_apply_apply]
      group
    rw [e]
    exact swap_mul_swap_mem_eL _ _ _ _ (h4 a ha) (h4 b hb) (h4 c hc) (h4 d hd) (hinj _ _ hab)
      (hinj _ _ hac) (hinj _ _ had) (hinj _ _ hbc) (hinj _ _ hbd) (hinj _ _ hcd)
  simp only [eL, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · rw [mul_one, mul_inv_cancel]
    exact List.mem_cons_self
  · exact key 1 2 3 4 (Or.inl rfl) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
  · exact key 1 3 2 4 (Or.inl rfl) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
  · exact key 1 4 2 3 (Or.inl rfl) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)

end CFSG.Quasithin.H13.A7Four

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin Equiv Equiv.Perm
open Vol2.Ch10.SecB.C11AmS CFSG.QuasithinUnique.L246.C123
open scoped IsMulCommutative

section FourSide

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_normalizer_thompsonJ_of_mem_normalizer {R : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (R : Set G)) :
    g ∈ Subgroup.normalizer (thompsonJ R : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hg ⊢
  have h := B6.thompsonJ_conjSub R g
  have hg' : R.map (MulAut.conj g).toMonoidHom = R := hg
  change thompsonJ (R.map (MulAut.conj g).toMonoidHom) =
    (thompsonJ R).map (MulAut.conj g).toMonoidHom at h
  rw [hg'] at h
  exact h.symm

theorem ffJ_eq_of_four (h51 : AsB51) {T K Kh W : Subgroup G}
    {e : O2Q Kh ≃* alternatingGroup (Fin 7)} (pk : A7Pack T K Kh W e)
    (hSQ : SQTKGroup ↥(Kh ⊔ T)) (hJW : ¬ thompsonJ T ≤ Subgroup.centralizer (W : Set G))
    (h16 : Nat.card ↥⁅W, Kh⁆ = 2 ^ 4) [IsMulCommutative ↥W] :
    ffJ (autOn (Kh ⊔ T) W) = autOn Kh W := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hWe : IsElemAbelian 2 W := pk.red.2.2.1
  have hYK : Kh ⊔ T ≤ Subgroup.normalizer (Kh : Set G) := sup_le Subgroup.le_normalizer pk.T_le
  have hY2 : ∀ y ∈ Kh ⊔ T, ∃ e : ℕ, y ^ 2 ^ e ∈ Kh :=
    InternalSec.two_of_sup pk.sylow.2.1 pk.T_le
  have hSQK : SQTKGroup ↥Kh := K8.sqtkGroup_of_le hSQ le_sup_left
  have hKW : ¬ Kh ≤ Subgroup.centralizer (W : Set G) := fun h =>
    pk.not_le_centralizer (h.trans (Subgroup.centralizer_le fun x hx => pk.U_le hx))
  have hKhW : Kh ≤ Subgroup.normalizer (W : Set G) := le_sup_left.trans pk.red.2.1
  obtain ⟨hB, hN⟩ := K8.b51Hyp_A7 pk.sylow le_sup_left hYK hY2 hWe pk.red (Or.inl ⟨e⟩) hSQK
    hKW hJW
  have hV2 : ∀ v : ↥W, v ^ 2 = 1 := fun v => Subtype.ext (by simpa [sq] using hWe.2 v v.2)
  obtain ⟨hP1, hP2, -⟩ := h51 ↥W hV2 _ _ hB
  have hshape := K8.part1_shape hP1 hN
  have hcard : Nat.card ↥(autOn Kh W) = 2520 := hshape.elim K8.card_of_alt7 K8.card_of_a7Four
  have hdir := K8.part2_direct hP2 hcard
  have hcU : Nat.card ↥(commV (autOn Kh W)) = 16 := by
    rw [commV_autOn_eq1527d hKhW,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe pk.U_le).toEquiv, h16]
    norm_num
  have hZ0 : fixV (autOn Kh W) ⊓ commV (autOn Kh W) = ⊥ := by
    rw [inf_comm]
    exact hdir.2
  have hLG : autOn Kh W ≤ ffJ (autOn (Kh ⊔ T) W) := hB.2.2.2.1
  have h2520 : 2520 ∣ Nat.card ↥(ffJ (autOn (Kh ⊔ T) W)) := hcard ▸ Subgroup.card_dvd_of_le hLG
  obtain ⟨-, hc⟩ := hP1
  rcases hc with hi | hii | ⟨n, hiii⟩ | hiv
  · obtain ⟨-, -, hT⟩ := hi
    obtain ⟨T₀, hT₀⟩ := B5.exists_isSylowTwoOf (ffJ (autOn (Kh ⊔ T) W))
    rcases hT T₀ hT₀ with hGL | ⟨-, hcase⟩
    · exact hGL
    · exfalso
      rcases hcase with ⟨k, hk5, hk8, hsym⟩ | hg2
      · rw [hZ0] at hsym
        obtain ⟨π, hπ⟩ := hsym
        have hGk : Nat.card ↥(ffJ (autOn (Kh ⊔ T) W)) = k.factorial := by
          rw [← Nat.card_congr (Equiv.ofBijective π
            ⟨FFC.injective_of_faithful_sec (FFC.symDn_faithful hk5) hπ, hπ.1⟩)]
          exact (Nat.card_perm (α := Fin k)).trans (by rw [Nat.card_fin])
        rw [hGk] at h2520
        have hU := G64.RealizesVia.card_eq hπ
        rw [G64.card_symDn_mod (by omega), Subgroup.card_bot, mul_one, hcU] at hU
        interval_cases k
        · exact absurd h2520 (by decide)
        · exact absurd h2520 (by decide)
        · norm_num at hU
        · norm_num at hU
      · obtain ⟨F, _, _, hF, π, hπ⟩ := hg2
        have hcard2 : Nat.card ↥(ffJ (autOn (Kh ⊔ T) W)) =
            Nat.card ↥(CFSG.Open.quasithinG2 F) := by
          have := FFC.charP_two_of_card_pow hF
          exact (Nat.card_congr (Equiv.ofBijective π
            ⟨FFC.injective_of_faithful_sec (FFC.zornQ_faithful _ le_rfl) hπ, hπ.1⟩)).symm
        rw [hcard2, card_quasithinG2_1527d hF, hF] at h2520
        norm_num at h2520
  · exfalso
    obtain ⟨-, n, F, hF, hFin, hFc, I, π, -, -, hreal, -⟩ := hii
    have hc := card_eq_of_nat_realizes1527d (hreal 0)
    rw [card_statedSL_three1527d, hFc] at hc
    exact K8.sl3_ne hN hc.symm
  · exfalso
    obtain ⟨-, hn, π, U₁, U₂, -, hr1, -⟩ := hiii
    exact K8.not_surj_sl hn hN π hr1.1
  · exfalso
    obtain ⟨-, n, hn, k, hk1, -, I, π, -, -, -, hreal⟩ := hiv
    exact K8.not_surj_sl hn hN π (hreal ⟨0, hk1⟩).1

theorem le_normalizer_thompsonJ_of_four (h51 : AsB51)
    {T K Kh W : Subgroup G} {e : O2Q Kh ≃* alternatingGroup (Fin 7)} (pk : A7Pack T K Kh W e)
    (hSQ : SQTKGroup ↥(Kh ⊔ T)) (hJW : ¬ thompsonJ T ≤ Subgroup.centralizer (W : Set G))
    (h16 : Nat.card ↥⁅W, Kh⁆ = 2 ^ 4) {D₃ : Subgroup G} (hD₃ : D₃ ≤ Kh)
    (hpos : ∀ d : ↥Kh, (d : G) ∈ D₃ → ∀ i : Fin 7, (i = 0 ∨ i = 5 ∨ i = 6) →
      ((e (QuotientGroup.mk d) : alternatingGroup (Fin 7)) : Perm (Fin 7)) i = 0 ∨
        ((e (QuotientGroup.mk d) : alternatingGroup (Fin 7)) : Perm (Fin 7)) i = 5 ∨
        ((e (QuotientGroup.mk d) : alternatingGroup (Fin 7)) : Perm (Fin 7)) i = 6) :
    D₃ ≤ Subgroup.normalizer (thompsonJ T : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hWe : IsElemAbelian 2 W := pk.red.2.2.1
  have := hWe.1
  have hYW : Kh ⊔ T ≤ Subgroup.normalizer (W : Set G) := pk.red.2.1
  have hKhW : Kh ≤ Subgroup.normalizer (W : Set G) := le_sup_left.trans hYW
  have hTW : T ≤ Subgroup.normalizer (W : Set G) := le_sup_right.trans hYW
  have hT2 : IsPGroup 2 T := pk.sylow.2.1
  have hWT : W ≤ T := pk.le_T
  have hWY : W ≤ Kh ⊔ T := hWT.trans le_sup_right
  have hKW : ¬ Kh ≤ Subgroup.centralizer (W : Set G) := fun h =>
    pk.not_le_centralizer (h.trans (Subgroup.centralizer_le fun x hx => pk.U_le hx))
  set C := (Kh ⊔ T) ⊓ Subgroup.centralizer (W : Set G) with hC
  have hCY : Kh ⊔ T ≤ Subgroup.normalizer (C : Set G) := fun y hy =>
    Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer hy, B6.le_normalizer_centralizer hYW hy⟩
  have hCT : C ≤ T := by
    have hC2 := isPGroup_sup_inf_centralizer pk.perf pk.simple hT2 pk.T_le hYW hKW
    exact (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left hCY hC2).trans
      (F7.isSylowTwoOf_pCoreOf_le pk.sylow)
  have hOT : pCoreOf 2 Kh ≤ T :=
    (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans le_sup_left)
      (sup_le (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _)
        (pk.T_le.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _)))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)).trans (F7.isSylowTwoOf_pCoreOf_le pk.sylow)
  have hGL := ffJ_eq_of_four h51 pk hSQ hJW h16
  set φ : ↥Kh →* alternatingGroup (Fin 7) :=
    e.toMonoidHom.comp (QuotientGroup.mk' (CFSG.pCore 2 ↥Kh)) with hφ
  set Ehat : Subgroup G := (A7Four.eA.comap φ).map Kh.subtype with hEhat
  have hEhatT : Ehat ≤ T := by
    rintro _ ⟨k, hk, rfl⟩
    have h1 : φ k ∈ A7Std.p0 := A7Four.eA_le_p0 hk
    rw [← pk.p0] at h1
    obtain ⟨q, ⟨t, ht, rfl⟩, hq⟩ := h1
    have h2 : (QuotientGroup.mk t : O2Q Kh) = QuotientGroup.mk k := e.injective hq
    rw [QuotientGroup.eq] at h2
    have h3 : ((t⁻¹ * k : ↥Kh) : G) ∈ pCoreOf 2 Kh := by
      rw [Vol2.Ch11.SecS.pCoreOf_two_eq_map]
      exact ⟨_, h2, rfl⟩
    have htT : (t : G) ∈ T := (Subgroup.mem_subgroupOf.mp ht).1
    have e1 : Kh.subtype k = t * ((t⁻¹ * k : ↥Kh) : G) := by simp
    rw [e1]
    exact T.mul_mem htT (hOT h3)
  set R := Ehat ⊔ C with hR
  have hRT : R ≤ T := sup_le hEhatT hCT
  have hU : IsElemAbelian 2 ⁅W, Kh⁆ := pk.elemAbelian
  have hKhU : Kh ≤ Subgroup.normalizer ((⁅W, Kh⁆ : Subgroup G) : Set G) := pk.le_normalizer
  have hTU : T ≤ Subgroup.normalizer ((⁅W, Kh⁆ : Subgroup G) : Set G) := pk.T_le_normalizer
  have hUT : ⁅W, Kh⁆ ≤ T := pk.U_le.trans hWT
  let _ : CommGroup ↥⁅W, Kh⁆ := commGroupOfElemAbelian hU
  set ρY := A7ZK.conjAut hKhU with hρY
  have hker : CFSG.pCore 2 ↥Kh ≤ ρY.ker := by
    intro y hy
    rw [MonoidHom.mem_ker]
    ext u
    have hyO : (y : G) ∈ pCoreOf 2 Kh := by
      rw [Vol2.Ch11.SecS.pCoreOf_two_eq_map]
      exact ⟨y, hy, rfl⟩
    have h1 : (u : G) * y = y * u := Subgroup.mem_centralizer_iff.mp (pk.pCoreOf_le hyO) u u.2
    show (y : G) * u * (y : G)⁻¹ = u
    rw [← h1, mul_inv_cancel_right]
  set ρ : alternatingGroup (Fin 7) →* MulAut ↥⁅W, Kh⁆ :=
    (QuotientGroup.lift (CFSG.pCore 2 ↥Kh) ρY hker).comp e.symm.toMonoidHom with hρ
  have hρφ : ∀ y : ↥Kh, ρ (φ y) = ρY y := fun y => by
    rw [hρ, hφ, MonoidHom.comp_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
    rfl
  have hρi : Function.Injective ρ := by
    rw [← MonoidHom.ker_eq_bot_iff]
    have : IsSimpleGroup (alternatingGroup (Fin 7)) := alternatingGroup.isSimpleGroup (by simp)
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ρ.ker with h | h
    · exact h
    · exfalso
      apply pk.not_le_centralizer
      intro k hk
      rw [Subgroup.mem_centralizer_iff]
      intro u hu
      have h1 : ρ (φ ⟨k, hk⟩) = 1 := by
        rw [← MonoidHom.mem_ker, h]
        exact Subgroup.mem_top _
      rw [hρφ] at h1
      have h2 := congrArg (fun f : MulAut ↥⁅W, Kh⁆ => ((f ⟨u, hu⟩ : ↥⁅W, Kh⁆) : G)) h1
      simp only [MulAut.one_apply] at h2
      rw [hρY, A7ZK.coe_conjAut] at h2
      have h2' : k * u * k⁻¹ = u := h2
      calc u * k = (k * u * k⁻¹) * k := by rw [h2']
        _ = k * u := by group
  have hJR : thompsonJ T ≤ R := by
    refine iSup₂_le fun A hA => ?_
    by_cases hAW : A ≤ Subgroup.centralizer (W : Set G)
    · exact le_sup_of_le_right (le_inf (hA.1.trans le_sup_right) hAW)
    have hAY : IsMaxElemAbelian (Kh ⊔ T) A := isMaxElemAbelian_of_isSylowTwoOf pk.sylow hA
    have hoff : IsFFStarOffender (autOn (Kh ⊔ T) W) (autOn A W) :=
      offenderImages_isFFStarOffender hWe hWY hYW ⟨A, ⟨hAY, hAW⟩, rfl⟩
    have hAK : autOn A W ≤ autOn Kh W := by
      rw [← hGL]
      exact le_iSup₂_of_le (autOn A W) hoff le_rfl
    have hAT : A ≤ T := hA.1
    have hAW' : A ≤ Subgroup.normalizer (W : Set G) := hAT.trans hTW
    have hrep : ∀ a ∈ A, ∃ k : ↥Kh, (k : G)⁻¹ * a ∈ C := by
      intro a ha
      have h1 : A4.actionOn W A hAW' ⟨a, ha⟩ ∈ autOn Kh W :=
        hAK ((A4.mem_autOn_iff hAW').mpr ⟨⟨a, ha⟩, rfl⟩)
      obtain ⟨k, hk⟩ := (A4.mem_autOn_iff hKhW).mp h1
      refine ⟨k, Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mem_sup_left k.2))
        (Subgroup.mem_sup_right (hAT ha)), ?_⟩
      show (k : G)⁻¹ * a ∈ Subgroup.centralizer (W : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      have h2 := congrArg (fun f : MulAut ↥W => ((f ⟨w, hw⟩ : ↥W) : G)) hk
      simp only [A4.actionOn_apply_coe] at h2
      calc w * ((k : G)⁻¹ * a) = (k : G)⁻¹ * ((k : G) * w * (k : G)⁻¹) * a := by group
        _ = (k : G)⁻¹ * (a * w * a⁻¹) * a := by rw [h2]
        _ = (k : G)⁻¹ * a * w := by group
    have hAU : A ≤ Subgroup.normalizer ((⁅W, Kh⁆ : Subgroup G) : Set G) := hAT.trans hTU
    set B : Subgroup (alternatingGroup (Fin 7)) := (autOn A ⁅W, Kh⁆).comap ρ with hB
    have hact : ∀ a (ha : a ∈ A) (k : ↥Kh), (k : G)⁻¹ * a ∈ C →
        ρ (φ k) = A4.actionOn ⁅W, Kh⁆ A hAU ⟨a, ha⟩ := by
      intro a ha k hkc
      rw [hρφ]
      refine MulEquiv.ext fun u => Subtype.ext ?_
      have hc : (k : G)⁻¹ * a ∈ Subgroup.centralizer (W : Set G) := hkc.2
      have h1 : (u : G) * ((k : G)⁻¹ * a) = ((k : G)⁻¹ * a) * u :=
        Subgroup.mem_centralizer_iff.mp hc u (pk.U_le u.2)
      show (k : G) * u * (k : G)⁻¹ = a * u * a⁻¹
      calc (k : G) * u * (k : G)⁻¹ = (k : G) * (u * ((k : G)⁻¹ * a)) * a⁻¹ := by group
        _ = (k : G) * (((k : G)⁻¹ * a) * u) * a⁻¹ := by rw [h1]
        _ = a * u * a⁻¹ := by group
    have hkB : ∀ a (ha : a ∈ A) (k : ↥Kh), (k : G)⁻¹ * a ∈ C → φ k ∈ B := by
      intro a ha k hkc
      show ρ (φ k) ∈ autOn A ⁅W, Kh⁆
      rw [hact a ha k hkc]
      exact (A4.mem_autOn_iff hAU).mpr ⟨⟨a, ha⟩, rfl⟩
    have hBim : ∀ x ∈ autOn A ⁅W, Kh⁆, ∃ σ ∈ B, ρ σ = x := by
      intro x hx
      obtain ⟨⟨a, ha⟩, hax⟩ := (A4.mem_autOn_iff hAU).mp hx
      obtain ⟨k, hkc⟩ := hrep a ha
      exact ⟨φ k, hkB a ha k hkc, (hact a ha k hkc).trans hax⟩
    have hBP : B ≤ A7Std.p0 := by
      intro σ hσ
      obtain ⟨⟨a, ha⟩, haσ⟩ := (A4.mem_autOn_iff hAU).mp hσ
      obtain ⟨k, hkc⟩ := hrep a ha
      have hσk : σ = φ k := hρi (by rw [hact a ha k hkc, haσ])
      have hkT : (k : G) ∈ T := by
        have e1 : (k : G) = a * ((k : G)⁻¹ * a)⁻¹ := by group
        rw [e1]
        exact T.mul_mem (hAT ha) (T.inv_mem (hCT hkc))
      rw [hσk, ← pk.p0]
      exact ⟨_, ⟨k, Subgroup.mem_subgroupOf.mpr ⟨hkT, k.2⟩, rfl⟩, rfl⟩
    have hBcard : Nat.card B = Nat.card (autOn A ⁅W, Kh⁆) := by
      refine Nat.card_congr (Equiv.ofBijective
        (fun σ : ↥B => (⟨ρ σ, σ.2⟩ : ↥(autOn A ⁅W, Kh⁆))) ⟨fun σ τ h => ?_, fun x => ?_⟩)
      · exact Subtype.ext (hρi (congrArg Subtype.val h))
      · obtain ⟨σ, hσ, hσx⟩ := hBim x x.2
        exact ⟨⟨σ, hσ⟩, Subtype.ext hσx⟩
    have hBfix : fixU ρ B = fixV (autOn A ⁅W, Kh⁆) := by
      ext u
      rw [mem_fixU, mem_fixV]
      constructor
      · intro h x hx
        obtain ⟨σ, hσ, rfl⟩ := hBim x hx
        exact h σ hσ
      · intro h σ hσ
        exact h _ hσ
    have hff := (offender_core hU hUT hTU hA (B := ⊥) bot_le).1
    rw [B1.card_bot_mul_card_fixV] at hff
    have h16' : 16 ≤ Nat.card B * Nat.card (fixU ρ B) := by
      rw [hBcard, hBfix]
      have h1 : Nat.card (IntMod ⁅W, Kh⁆ hU) = 16 := by
        show Nat.card ↥⁅W, Kh⁆ = 16
        rw [h16]
        norm_num
      rw [h1] at hff
      exact hff
    have hBne : B ≠ ⊥ := by
      intro hb
      apply hAW
      intro a ha
      obtain ⟨k, hkc⟩ := hrep a ha
      have hk1 := hkB a ha k hkc
      rw [hb, Subgroup.mem_bot] at hk1
      have hρk : ρY k = 1 := by
        rw [← hρφ, hk1, map_one]
      have hkW : (k : G) ∈ Subgroup.centralizer (W : Set G) := by
        have hle : W ≤ Subgroup.centralizer ({(k : G)} : Set G) := by
          rw [← pk.dec]
          refine sup_le (fun u hu => ?_) (fun c hc => ?_)
          · have h2 := congrArg (fun f : MulAut ↥⁅W, Kh⁆ => ((f ⟨u, hu⟩ : ↥⁅W, Kh⁆) : G)) hρk
            simp only [MulAut.one_apply] at h2
            rw [hρY, A7ZK.coe_conjAut] at h2
            have h2' : (k : G) * u * (k : G)⁻¹ = u := h2
            rw [Subgroup.mem_centralizer_singleton_iff]
            calc u * (k : G) = ((k : G) * u * (k : G)⁻¹) * k := by rw [h2']
              _ = (k : G) * u := by group
          · exact Subgroup.mem_centralizer_singleton_iff.mpr
              (Subgroup.mem_centralizer_iff.mp hc.2 k k.2).symm
        rw [Subgroup.mem_centralizer_iff]
        intro w hw
        exact Subgroup.mem_centralizer_singleton_iff.mp (hle hw)
      have e1 : a = (k : G) * ((k : G)⁻¹ * a) := by group
      rw [e1]
      exact Subgroup.mul_mem _ hkW hkc.2
    have hAel := isElemAbelian2_autI hU hA.2.1 hAU
    have hBc : ∀ σ ∈ B, ∀ τ ∈ B, σ * τ = τ * σ := fun σ hσ τ hτ =>
      hρi (by rw [map_mul, map_mul]; exact hAel.1 _ hσ _ hτ)
    have hBs : ∀ σ ∈ B, σ * σ = 1 := fun σ hσ =>
      hρi (by rw [map_mul, map_one, ← pow_two]; exact hAel.2 _ hσ)
    have hcardU : Nat.card ↥⁅W, Kh⁆ = 16 := by
      rw [h16]
      norm_num
    have hU2 : ∀ u : ↥⁅W, Kh⁆, u ^ 2 = 1 := fun u =>
      Subtype.ext (by simpa [sq] using hU.2 u u.2)
    have hK := C124.YL.A7.klein_of_woff ρ hcardU hρi hU2 hBne hBc hBs h16'
    have hBE : B = A7Four.eA :=
      IsKleinConj.eq_of_le A7Std.card_p0 hK A7Four.isKleinConj_eA hBP A7Four.eA_le_p0
    intro a ha
    obtain ⟨k, hkc⟩ := hrep a ha
    have hkE : (k : G) ∈ Ehat := by
      have h1 := hkB a ha k hkc
      rw [hBE] at h1
      exact ⟨k, h1, rfl⟩
    have e1 : a = (k : G) * ((k : G)⁻¹ * a) := by group
    rw [e1]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hkE) (Subgroup.mem_sup_right hkc)
  have hDE : ∀ d ∈ D₃, ∀ x ∈ Ehat, d * x * d⁻¹ ∈ Ehat := by
    intro d hd x hx
    obtain ⟨k, hk, rfl⟩ := hx
    set dk : ↥Kh := ⟨d, hD₃ hd⟩ with hdk
    refine ⟨dk * k * dk⁻¹, ?_, rfl⟩
    show φ (dk * k * dk⁻¹) ∈ A7Four.eA
    rw [map_mul, map_mul, map_inv, A7Four.mem_eA]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact A7Four.conj_mem_eL (hpos dk hd) hk
  have hDR : D₃ ≤ Subgroup.normalizer (R : Set G) := by
    intro d hd
    have hdE : d ∈ Subgroup.normalizer (Ehat : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro x
      refine ⟨hDE d hd x, fun hx => ?_⟩
      have h1 := hDE d⁻¹ (D₃.inv_mem hd) _ hx
      simpa [mul_assoc] using h1
    have hdC : d ∈ Subgroup.normalizer (C : Set G) := hCY (Subgroup.mem_sup_left (hD₃ hd))
    rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hdE hdC ⊢
    rw [hR, Subgroup.map_sup, hdE, hdC]
  intro d hd
  rw [← B6.thompsonJ_eq_of_le hJR hRT]
  exact mem_normalizer_thompsonJ_of_mem_normalizer (hDR hd)

end FourSide

end CFSG.Quasithin.H13
