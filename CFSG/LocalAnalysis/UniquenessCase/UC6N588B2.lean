module

public import CFSG.LocalAnalysis.UniquenessCase.UC6N588B1
public import CFSG.RankThree.PartOne.S12.LinAlg
public import CFSG.LocalAnalysis.UniquenessCase.UC6C623Defs
public import CFSG.LocalAnalysis.UniquenessCase.UC6C623a
public import CFSG.LocalAnalysis.UniquenessCase.UC6S27
public import CFSG.LocalAnalysis.UniquenessCase.UC6S9
public import CFSG.LocalAnalysis.UniquenessCase.UCKInputs2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6

open Subgroup CFSG.Open CFSG.ABGLocalTools
open CFSG.LocalAnalysis.UniquenessCase.UC22 (calMOf IrrOn)
open CFSG.RankThree.PartOne (torusWeyl torusIrreducible torusInvariant)
open CFSG.RankThree.PartOne.LinAlg (bsub torusWeylGL wActionGL)
open scoped Matrix

namespace Mz614

variable {G : Type} [Group G] [Finite G] (m : Mz614 G)

@[expose] def W : Subgroup G := normalizer (m.A : Set G)

theorem normalizer_le_M_of_E_normalizes {Q : Subgroup G} (hQp : IsPGroup 2 Q) (hQ : Q ≠ ⊥)
    (hEQ : m.E ≤ normalizer (Q : Set G)) : normalizer (Q : Set G) ≤ m.M := by
  have hEM : m.E ≤ m.M := fun x hx => m.R_le_M (m.E_le_R hx)
  have hU := r6_3_dataOfSetup4 m.hS m.hU m.S m.hC m.r m.hr m.d.odd m.E hEM m.d.E_el
    m.d.E_card m.d.E_gamma
  have hloc : IsTwoLocal (normalizer (Q : Set G)) := ⟨Q, hQ, hQp, rfl⟩
  obtain ⟨N, hN, hQN⟩ := exists_rankThreeIsMaxTwoLocal_ge_uc6 hloc
  have hNM : N = m.M := by
    have hmem : N ∈ calMOf m.E := ⟨hN, hEQ.trans hQN⟩
    rw [hU] at hmem
    exact hmem
  exact hNM ▸ hQN

@[expose] def twoCenterL : Subgroup G where
  carrier := {x | x ∈ m.L ∧ (∀ l ∈ m.L, x * l = l * x) ∧ x ^ 2 ^ Nat.card G = 1}
  mul_mem' := by
    rintro a b ⟨haL, hac, ha2⟩ ⟨hbL, hbc, hb2⟩
    refine ⟨m.L.mul_mem haL hbL, fun l hl => ?_, ?_⟩
    · calc a * b * l = a * (l * b) := by rw [mul_assoc, hbc l hl]
        _ = l * (a * b) := by rw [← mul_assoc, hac l hl, mul_assoc]
    · rw [(Commute.mul_pow (show Commute a b from hac b hbL)), ha2, hb2, one_mul]
  one_mem' := ⟨m.L.one_mem, fun l _ => by simp, by simp⟩
  inv_mem' := by
    rintro a ⟨haL, hac, ha2⟩
    refine ⟨m.L.inv_mem haL, fun l hl => ?_, by rw [inv_pow, ha2, inv_one]⟩
    have h1 := hac l hl
    calc a⁻¹ * l = a⁻¹ * (l * a) * a⁻¹ := by group
      _ = a⁻¹ * (a * l) * a⁻¹ := by rw [h1]
      _ = l * a⁻¹ := by group

theorem isPGroup_twoCenterL : IsPGroup 2 m.twoCenterL := fun x =>
  ⟨Nat.card G, Subtype.ext x.2.2.2⟩

theorem H_le_normalizer_twoCenterL : m.H ≤ normalizer (m.twoCenterL : Set G) := by
  intro h hh
  refine mem_normalizer_of_forward_uc6 fun x hx => ?_
  obtain ⟨hxL, hxc, hx2⟩ := hx
  have hLn := m.H_le_normalizer_L hh
  refine ⟨(mem_normalizer_iff.1 hLn x).1 hxL, fun l hl => ?_, ?_⟩
  · have hl' : h⁻¹ * l * h ∈ m.L := by
      have := (mem_normalizer_iff.1 (inv_mem hLn) l).1 hl
      simpa using this
    have h1 := hxc _ hl'
    calc h * x * h⁻¹ * l = h * (x * (h⁻¹ * l * h)) * h⁻¹ := by group
      _ = h * ((h⁻¹ * l * h) * x) * h⁻¹ := by rw [h1]
      _ = l * (h * x * h⁻¹) := by group
  · rw [conj_pow, hx2]
    group

theorem L_not_le_M (h619 : m.C619) : ¬ m.L ≤ m.M := by
  intro hLM
  apply m.hZ.not_le
  have : m.H ≤ m.M := by
    rw [h619]
    exact sup_le hLM inf_le_right
  exact this

theorem center_L_eq_bot (h67 : R6_7 (dataOfSetup4 m.hS m.hU m.S)) (h619 : m.C619)
    (hmult : Odd (Nat.card (center ↥m.L)) → center ↥m.L = ⊥) : center ↥m.L = ⊥ := by
  apply hmult
  rw [Nat.odd_iff, ← Nat.two_dvd_ne_zero]
  intro h2
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' 2 h2
  have h2c : c ^ 2 = 1 := by
    have := pow_orderOf_eq_one c
    rwa [hc] at this
  have h2G : ((c : ↥m.L) : G) ^ 2 = 1 := by
    have h1 := congrArg (fun t : ↥(center ↥m.L) => ((t : ↥m.L) : G)) h2c
    simpa using h1
  have hc1 : ((c : ↥m.L) : G) ≠ 1 := by
    intro h1
    have : c = 1 := by
      ext
      simpa using h1
    rw [this, orderOf_one] at hc
    norm_num at hc
  have hcT : ((c : ↥m.L) : G) ∈ m.twoCenterL := by
    refine ⟨(c : ↥m.L).2, fun l hl => ?_, ?_⟩
    · have := mem_center_iff.1 c.2 ⟨l, hl⟩
      exact (congrArg Subtype.val this).symm
    · obtain ⟨k, hk⟩ : 2 ∣ 2 ^ Nat.card G :=
        dvd_pow_self 2 (Nat.card_pos (α := G)).ne'
      rw [hk, pow_mul, h2G, one_pow]
  have hTne : m.twoCenterL ≠ ⊥ := by
    intro hb
    rw [hb, mem_bot] at hcT
    exact hc1 hcT
  have hEN : m.E ≤ normalizer (m.twoCenterL : Set G) :=
    m.hZ.E_le_centralizer.trans m.H_le_normalizer_twoCenterL
  have hNM := m.normalizer_le_M_of_E_normalizes m.isPGroup_twoCenterL hTne hEN
  exact m.L_not_le_M h619 (m.L_le_H.trans (m.H_le_normalizer_twoCenterL.trans hNM))

theorem R_isSylowOf_top : IsSylowOf m.r m.R ⊤ := by
  haveI : Fact m.r.Prime := ⟨m.hr⟩
  rw [isSylowOf_iff]
  refine ⟨le_top, m.d.sylow.isPGroup, ?_⟩
  have := m.toMc614.sylowTop.not_dvd_index
  rw [m.toMc614.coe_sylowTop] at this
  rwa [Subgroup.relIndex_top_right]

theorem normalizer_R_le_W (h69 : R6_9 (dataOfSetup4 m.hS m.hU m.S)) :
    normalizer (m.R : Set G) ≤ m.W := by
  intro n hnR
  refine mem_normalizer_of_forward_uc6 fun a ha => ?_
  have haR : a ∈ m.R := m.A_le_R ha
  have hnaR : n * a * n⁻¹ ∈ m.R := (mem_normalizer_iff.1 hnR a).1 haR
  have hpow : (n * a * n⁻¹) ^ m.r = 1 := by
    rw [conj_pow, m.isElemAbelian_A.2 a ha]
    group
  exact (m.hZ.sixteen h69).2 _ hnaR hpow

theorem not_W_le_of_not_c623 (h69 : R6_9 (dataOfSetup4 m.hS m.hU m.S)) (hne : ¬ m.C623) :
    ¬ m.W ≤ normalizer (m.Z : Set G) := by
  intro hW
  apply hne
  haveI : Fact m.r.Prime := ⟨m.hr⟩
  have hsix := m.hZ.sixteen h69
  intro g hg
  by_contra hne'
  have hZgA : CFSG.conjugate m.Z g ≤ m.A := by
    intro x hx
    have hxR := hg hx
    have hxz : g * x * g⁻¹ ∈ m.Z := mem_conjugate_iff_uc6.1 hx
    have hpow : (g * x * g⁻¹) ^ m.r = 1 := (isElemAbelian_of_card_prime m.hr m.card_Z).2 _ hxz
    have hx1 : x ^ m.r = 1 := by
      have h1 : (MulAut.conj g) (x ^ m.r) = 1 := by
        rw [map_pow, MulAut.conj_apply]
        exact hpow
      exact (MulAut.conj g).injective (h1.trans (map_one _).symm)
    exact hsix.2 x hxR hx1
  have hZ' : ∀ z ∈ m.Z, ∀ x ∈ m.R, x * z = z * x := fun z hz x hx =>
    (hsix.1 z (m.Z_le_A hz) x hx).symm
  have hZg' : ∀ z ∈ m.Z, ∀ x ∈ m.R, x * (g⁻¹ * z * g) = (g⁻¹ * z * g) * x := by
    intro z hz x hx
    have hmem : g⁻¹ * z * g ∈ CFSG.conjugate m.Z g := by
      rw [mem_conjugate_iff_uc6]
      have e : g * (g⁻¹ * z * g) * g⁻¹ = z := by group
      rw [e]
      exact hz
    exact (hsix.1 _ (hZgA hmem) x hx).symm
  obtain ⟨n, hnR, hn⟩ := exists_mem_normalizer_conj_eq m.R_isSylowOf_top hZ' hZg'
  have hnZ := hW (m.normalizer_R_le_W h69 hnR)
  apply hne'
  have hcardc : Nat.card (CFSG.conjugate m.Z g) = Nat.card m.Z :=
    Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective
  refine Subgroup.eq_of_le_of_card_ge ?_ hcardc.ge
  intro x hx
  have hxz : g * x * g⁻¹ ∈ m.Z := mem_conjugate_iff_uc6.1 hx
  have h1 := hn _ hxz
  have e : g⁻¹ * (g * x * g⁻¹) * g = x := by group
  rw [e] at h1
  rw [← h1]
  exact (mem_normalizer_iff''.1 hnZ _).1 hxz

theorem R_le_centralizer_A (h69 : R6_9 (dataOfSetup4 m.hS m.hU m.S)) :
    m.R ≤ centralizer (m.A : Set G) := fun x hx =>
  mem_centralizer_iff.2 fun a ha => (m.hZ.sixteen h69).1 a ha x hx

theorem not_dvd_relIndex_W (h69 : R6_9 (dataOfSetup4 m.hS m.hU m.S)) :
    ¬ m.r ∣ (centralizer (m.A : Set G) ⊓ m.W).relIndex m.W := by
  haveI : Fact m.r.Prime := ⟨m.hr⟩
  have hRC := m.R_le_centralizer_A h69
  have hRW : m.R ≤ m.W := hRC.trans (Subgroup.centralizer_le_normalizer _)
  have hRWsyl : IsSylowOf m.r m.R m.W := m.R_isSylowOf_top.of_le hRW le_top
  have hndvd := (isSylowOf_iff.1 hRWsyl).2.2
  have hRC' : m.R ≤ centralizer (m.A : Set G) ⊓ m.W := le_inf hRC hRW
  intro hd
  apply hndvd
  rw [← Subgroup.relIndex_mul_relIndex m.R _ _ hRC' inf_le_right]
  exact hd.mul_left _

theorem card_torusWeyl :
    Nat.card (torusWeyl m.A) = (centralizer (m.A : Set G) ⊓ m.W).relIndex m.W := by
  rw [torusWeyl, ← Subgroup.index_ker, Subgroup.normalizerMonoidHom_ker,
    Subgroup.inf_relIndex_right]
  rfl

theorem not_dvd_card_torusWeyl (h69 : R6_9 (dataOfSetup4 m.hS m.hU m.S)) :
    ¬ m.r ∣ Nat.card (torusWeyl m.A) := by
  rw [card_torusWeyl]
  exact m.not_dvd_relIndex_W h69

theorem mem_centralizer_of_pow (h69 : R6_9 (dataOfSetup4 m.hS m.hU m.S)) :
    ∀ g ∈ m.W, g ^ m.r ∈ centralizer (m.A : Set G) → g ∈ centralizer (m.A : Set G) := by
  intro g hg hgr
  set φ := m.A.normalizerMonoidHom ⟨g, hg⟩ with hφ
  have hker : ∀ x : normalizer (m.A : Set G), m.A.normalizerMonoidHom x = 1 ↔
      (x : G) ∈ centralizer (m.A : Set G) := by
    intro x
    rw [← MonoidHom.mem_ker, Subgroup.normalizerMonoidHom_ker, mem_subgroupOf]
  have hφr : φ ^ m.r = 1 := by
    rw [hφ, ← map_pow, hker]
    simpa using hgr
  have hdvd1 : orderOf φ ∣ m.r := orderOf_dvd_of_pow_eq_one hφr
  have hdvd2 : orderOf φ ∣ Nat.card (torusWeyl m.A) := by
    have h := orderOf_dvd_natCard (⟨φ, ⟨⟨g, hg⟩, rfl⟩⟩ : torusWeyl m.A)
    rw [← Subgroup.orderOf_coe] at h
    exact h
  have h1 : orderOf φ = 1 := by
    rcases (Nat.dvd_prime m.hr).1 hdvd1 with h | h
    · exact h
    · exact absurd (h ▸ hdvd2) (m.not_dvd_card_torusWeyl h69)
  exact (hker ⟨g, hg⟩).1 (orderOf_eq_one_iff.1 h1)

theorem Z_inf_A_inf_L (h620 : m.C620) : m.Z ⊓ (m.A ⊓ m.L) = ⊥ := by
  have hZL : m.Z ⊓ m.L = ⊥ := inf_eq_bot_of_not_le_of_card_prime m.hr m.card_Z h620.2
  refine le_bot_iff.1 ?_
  rw [← hZL]
  exact inf_le_inf_left _ inf_le_right

theorem L_inf_W_le_normalizer : m.L ⊓ m.W ≤ normalizer ((m.A ⊓ m.L : Subgroup G) : Set G) := by
  intro n hn
  refine mem_normalizer_of_forward_uc6 fun p hp => ?_
  exact ⟨(mem_normalizer_iff.1 hn.2 p).1 hp.1,
    m.L.mul_mem (m.L.mul_mem hn.1 hp.2) (m.L.inv_mem hn.1)⟩

theorem scalarTriple (h620 : m.C620) (h621 : m.C621) {y : G} (hy : y ∈ m.L ⊓ m.W) {s : ℕ}
    (hs : s % m.r ≠ 1) (hyB : ∀ b ∈ m.A ⊓ m.L, y * b * y⁻¹ = b ^ s) :
    ScalarTriple m.r m.A m.W (m.L ⊓ m.W) m.Z (m.A ⊓ m.L) y s where
  prime := m.hr
  elem := m.isElemAbelian_A
  card_A := m.card_A
  inf_eq_bot := m.Z_inf_A_inf_L h620
  Z_le := m.Z_le_A
  P_le := inf_le_left
  card_Z := m.card_Z
  card_P := m.card_A_inf_L h620
  W_le := le_rfl
  N_le := inf_le_right
  N_P := m.L_inf_W_le_normalizer
  N_Z := fun n hn z hz => (m.Z_comm_L hz hn.1).symm
  irr := fun B hB hN => h621 B hB hN
  y_mem := hy
  y_P := hyB
  s_ne := hs

theorem torusIrreducible_A (h69 : R6_9 (dataOfSetup4 m.hS m.hU m.S)) (h620 : m.C620)
    (h621 : m.C621) {y : G} (hy : y ∈ m.L ⊓ m.W) {s : ℕ} (hs : s % m.r ≠ 1)
    (hyB : ∀ b ∈ m.A ⊓ m.L, y * b * y⁻¹ = b ^ s) (hne : ¬ m.C623) : torusIrreducible m.A := by
  intro B hBA hinv
  have hWB : m.W ≤ normalizer (B : Set G) := fun w hw =>
    mem_normalizer_of_forward_uc6 fun b hb => hinv w ⟨trivial, hw⟩ b hb
  exact (m.scalarTriple h620 h621 hy hs hyB).irreducible (m.not_W_le_of_not_c623 h69 hne)
    (m.mem_centralizer_of_pow h69) hBA hWB

section Matrix

variable [Fact m.r.Prime] (f : Multiplicative (Fin 3 → ZMod m.r) ≃* ↥m.A)

theorem exists_coords_A : Nonempty (Multiplicative (Fin 3 → ZMod m.r) ≃* ↥m.A) := by
  haveI : CFSG.IsElementaryAbelian m.r ↥m.A := m.isElemAbelian_A.isElementaryAbelian
  exact CFSG.RankThree.PartOne.LinAlg.exists_coords m.A m.card_A

theorem irredGL3_torusWeylGL (h : torusIrreducible m.A) : UCK.IrredGL3 m.r (torusWeylGL f) :=
  (CFSG.RankThree.PartOne.LinAlg.torusIrreducible_iff_isIrreducibleOn f).1 h

theorem not_dvd_card_torusWeylGL (h69 : R6_9 (dataOfSetup4 m.hS m.hU m.S)) :
    ¬ m.r ∣ Nat.card (torusWeylGL f) := by
  rw [CFSG.RankThree.PartOne.LinAlg.natCard_torusWeylGL]
  exact m.not_dvd_card_torusWeyl h69

theorem finrank_bsub_of_card {B : Subgroup G} (hBA : B ≤ m.A) (hB : Nat.card B = m.r) :
    Module.finrank (ZMod m.r) (bsub f B) = 1 := by
  have h := CFSG.RankThree.PartOne.LinAlg.natCard_eq_pow_finrank_bsub f hBA
  rw [hB] at h
  exact (Nat.pow_right_injective m.hr.two_le (h.symm.trans (pow_one m.r).symm))

theorem finrank_bsub_Z : Module.finrank (ZMod m.r) (bsub f m.Z) = 1 :=
  m.finrank_bsub_of_card f m.Z_le_A m.card_Z

theorem coe_f_wActionGL_mulVec (w : normalizer (m.A : Set G)) (v : Fin 3 → ZMod m.r) :
    ((f (Multiplicative.ofAdd
        (((wActionGL f w : GL (Fin 3) (ZMod m.r)) : Matrix (Fin 3) (Fin 3) (ZMod m.r)) *ᵥ v)) :
        ↥m.A) : G) = (w : G) * (f (Multiplicative.ofAdd v) : G) * (w : G)⁻¹ := by
  have h1 : ((wActionGL f w : GL (Fin 3) (ZMod m.r)) : Matrix (Fin 3) (Fin 3) (ZMod m.r)) *ᵥ v =
      CFSG.RankThree.PartOne.LinAlg.wAction f w v :=
    CFSG.RankThree.PartOne.LinAlg.toGL_mulVec _ v
  rw [h1]
  exact CFSG.RankThree.PartOne.LinAlg.wAction_apply f w v

theorem wActionGL_mulVec_eq_iff (w : normalizer (m.A : Set G)) (v : Fin 3 → ZMod m.r) :
    ((wActionGL f w : GL (Fin 3) (ZMod m.r)) : Matrix (Fin 3) (Fin 3) (ZMod m.r)) *ᵥ v = v ↔
      (w : G) * (f (Multiplicative.ofAdd v) : G) * (w : G)⁻¹ = (f (Multiplicative.ofAdd v) : G) := by
  rw [← m.coe_f_wActionGL_mulVec f w v]
  constructor
  · intro h
    rw [h]
  · intro h
    have h2 := Subtype.ext h
    have h3 := f.injective h2
    exact Multiplicative.ofAdd.injective h3

theorem wActionGL_mem (w : normalizer (m.A : Set G)) : wActionGL f w ∈ torusWeylGL f := by
  rw [← CFSG.RankThree.PartOne.LinAlg.range_wActionGL]
  exact ⟨w, rfl⟩

theorem exists_of_mem_torusWeylGL {g : GL (Fin 3) (ZMod m.r)} (hg : g ∈ torusWeylGL f) :
    ∃ w : normalizer (m.A : Set G), wActionGL f w = g := by
  rw [← CFSG.RankThree.PartOne.LinAlg.range_wActionGL] at hg
  exact hg

theorem mulVec_mem_bsub_conj_iff (w : normalizer (m.A : Set G)) {B : Subgroup G}
    (v : Fin 3 → ZMod m.r) :
    ((wActionGL f w : GL (Fin 3) (ZMod m.r)) : Matrix (Fin 3) (Fin 3) (ZMod m.r)) *ᵥ v ∈
        bsub f (B.map (MulAut.conj (w : G)).toMonoidHom) ↔ v ∈ bsub f B := by
  rw [CFSG.RankThree.PartOne.LinAlg.mem_bsub, CFSG.RankThree.PartOne.LinAlg.mem_bsub,
    m.coe_f_wActionGL_mulVec f w v]
  constructor
  · rintro ⟨b, hb, hbe⟩
    have : b = (f (Multiplicative.ofAdd v) : G) := by
      have := congrArg (fun t => (w : G)⁻¹ * t * (w : G)) hbe
      simpa [MulAut.conj_apply, mul_assoc] using this
    rw [← this]
    exact hb
  · intro h
    exact ⟨_, h, by simp [MulAut.conj_apply]⟩

end Matrix

end Mz614

end CFSG.LocalAnalysis.UniquenessCase.UC6
