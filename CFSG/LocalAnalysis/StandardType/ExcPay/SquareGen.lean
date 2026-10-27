module

public import CFSG.LocalAnalysis.StandardType.ExcPay.Defs
public import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.WeylTorusAct
import CFSG.LieType.Chevalley.GraphFixedD4TorusWords
import CFSG.LieType.Chevalley.RootDiagonalWeylTransporter
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

public section

namespace CFSG.StandardType.ExcPay

open CFSG.Open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.ClassicalInvolution.Phan CFSG.LieType.Universal CFSG.StandardType
  CFSG.StandardType.GGFinModel CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.Tables.T1b

private lemma excPayG_eq_one_of_mem_centralizer {G : Type} [Group G] {X : Subgroup G}
    (hZ : Subgroup.center ↥X = ⊥) {z : G} (hzX : z ∈ X)
    (hzC : z ∈ Subgroup.centralizer (X : Set G)) : z = 1 := by
  have hz' : (⟨z, hzX⟩ : ↥X) ∈ Subgroup.center ↥X := by
    rw [Subgroup.mem_center_iff]
    intro x
    apply Subtype.ext
    have hcomm : (x : G) * z = z * (x : G) := by
      rw [Subgroup.mem_centralizer_iff] at hzC
      exact hzC (x : G) x.property
    simpa using hcomm
  have hzbot : (⟨z, hzX⟩ : ↥X) = 1 := by
    rw [hZ] at hz'
    simpa using hz'
  simpa using congrArg Subtype.val hzbot

private lemma excPayG_component_unique {G : Type} [Group G] {X : Subgroup G}
    (hZ : Subgroup.center ↥X = ⊥) {b : G} {x x' : X}
    (hbx : (x : G)⁻¹ * b ∈ Subgroup.centralizer (X : Set G))
    (hbx' : (x' : G)⁻¹ * b ∈ Subgroup.centralizer (X : Set G)) :
    x = x' := by
  have hc : ((x' : G)⁻¹ * x) = ((x' : G)⁻¹ * b) * ((x : G)⁻¹ * b)⁻¹ := by group
  have hmemC : ((x' : G)⁻¹ * x) ∈ Subgroup.centralizer (X : Set G) := by
    rw [hc]
    exact Subgroup.mul_mem _ hbx' (Subgroup.inv_mem _ hbx)
  have hmemX : ((x' : G)⁻¹ * x) ∈ X :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ x'.property) x.property
  have hone : ((x' : G)⁻¹ * x) = 1 := excPayG_eq_one_of_mem_centralizer hZ hmemX hmemC
  apply Subtype.ext
  have h1 : (x' : G) * ((x' : G)⁻¹ * x) = x := by group
  rw [hone, mul_one] at h1
  exact h1.symm

private lemma excPayG_conj_eq_of_centralizer {G : Type} [Group G] {X : Subgroup G}
    {b : G} {x : X} (hx : (x : G)⁻¹ * b ∈ Subgroup.centralizer (X : Set G)) :
    ∀ y ∈ X, b * y * b⁻¹ = (x : G) * y * (x : G)⁻¹ := by
  intro y hy
  rw [Subgroup.mem_centralizer_iff] at hx
  have hcomm : y * ((x : G)⁻¹ * b) = ((x : G)⁻¹ * b) * y := hx y hy
  calc
    b * y * b⁻¹ = (x : G) * ((x : G)⁻¹ * b) * y * b⁻¹ := by group
    _ = (x : G) * (((x : G)⁻¹ * b) * y) * b⁻¹ := by group
    _ = (x : G) * (y * ((x : G)⁻¹ * b)) * b⁻¹ := by rw [← hcomm]
    _ = (x : G) * y * (x : G)⁻¹ := by group

private lemma excPayG_cent_inv {G : Type} [Group G] {X : Subgroup G} {b : G} {x : X}
    (hx : (x : G) ∈ X) (h : b * (x : G)⁻¹ ∈ Subgroup.centralizer (X : Set G)) :
    (x : G)⁻¹ * b ∈ Subgroup.centralizer (X : Set G) := by
  have hcomm : (x : G) * b = b * (x : G) := by
    have h' := (Subgroup.mem_centralizer_iff.mp h) (x : G) hx
    have h'' : (x : G) * b * (x : G)⁻¹ = b := by simpa [mul_assoc] using h'
    calc
      (x : G) * b = ((x : G) * b * (x : G)⁻¹) * (x : G) := by group
      _ = b * (x : G) := by rw [h'']
  have hcomm_inv : (x : G)⁻¹ * b = b * (x : G)⁻¹ := by
    calc
      (x : G)⁻¹ * b = (x : G)⁻¹ * (b * (x : G)) * (x : G)⁻¹ := by group
      _ = (x : G)⁻¹ * ((x : G) * b) * (x : G)⁻¹ := by rw [← hcomm]
      _ = b * (x : G)⁻¹ := by group
  rw [hcomm_inv]
  exact h

private noncomputable def excPayG_pi {G : Type} [Group G] {Bs X : Subgroup G}
    (hsplit : ∀ b ∈ Bs, ∃ x ∈ X ⊓ Bs, b * x⁻¹ ∈ Subgroup.centralizer (X : Set G))
    (b : ↥Bs) : ↥X :=
  ⟨(hsplit (b : G) b.2).choose, (hsplit (b : G) b.2).choose_spec.1.1⟩

private lemma excPayG_pi_mem {G : Type} [Group G] {Bs X : Subgroup G}
    (hsplit : ∀ b ∈ Bs, ∃ x ∈ X ⊓ Bs, b * x⁻¹ ∈ Subgroup.centralizer (X : Set G))
    (b : ↥Bs) : (excPayG_pi hsplit b : G) ∈ X ⊓ Bs :=
  (hsplit (b : G) b.2).choose_spec.1

private lemma excPayG_pi_cent {G : Type} [Group G] {Bs X : Subgroup G}
    (hsplit : ∀ b ∈ Bs, ∃ x ∈ X ⊓ Bs, b * x⁻¹ ∈ Subgroup.centralizer (X : Set G))
    (b : ↥Bs) :
    (b : G) * (excPayG_pi hsplit b : G)⁻¹ ∈ Subgroup.centralizer (X : Set G) :=
  (hsplit (b : G) b.2).choose_spec.2

private lemma excPayG_pi_unique {G : Type} [Group G] {Bs X : Subgroup G}
    (hsplit : ∀ b ∈ Bs, ∃ x ∈ X ⊓ Bs, b * x⁻¹ ∈ Subgroup.centralizer (X : Set G))
    (hZ : Subgroup.center ↥X = ⊥) {b : G} {x x' : X}
    (hx : (x : G) ∈ X) (hx' : (x' : G) ∈ X)
    (h : b * (x : G)⁻¹ ∈ Subgroup.centralizer (X : Set G))
    (h' : b * (x' : G)⁻¹ ∈ Subgroup.centralizer (X : Set G)) :
    x = x' :=
  excPayG_component_unique hZ (excPayG_cent_inv hx h) (excPayG_cent_inv hx' h')

private lemma excPayG_component_mul' {G : Type} [Group G] {X : Subgroup G}
    {b b' : G} {x x' : X}
    (hx : b * (x : G)⁻¹ ∈ Subgroup.centralizer (X : Set G))
    (hx' : b' * (x' : G)⁻¹ ∈ Subgroup.centralizer (X : Set G)) :
    (b * b') * ((x * x' : X) : G)⁻¹ ∈ Subgroup.centralizer (X : Set G) := by
  have hcoe : ((x * x' : X) : G) = (x : G) * (x' : G) := rfl
  have hcx : (b' * (x' : G)⁻¹) * (x : G) = (x : G) * (b' * (x' : G)⁻¹) :=
    ((Subgroup.mem_centralizer_iff.mp hx') (x : G) x.property).symm
  have hgoal : (b * b') * ((x * x' : X) : G)⁻¹ =
      (b * (x : G)⁻¹) * (b' * (x' : G)⁻¹) := by
    rw [hcoe, mul_inv_rev]
    calc
      (b * b') * ((x' : G)⁻¹ * (x : G)⁻¹) =
          (b * (x : G)⁻¹) * ((x : G) * (b' * (x' : G)⁻¹)) *
            ((x' : G) * (x' : G)⁻¹) * (x : G)⁻¹ := by group
      _ = (b * (x : G)⁻¹) * ((b' * (x' : G)⁻¹) * (x : G)) *
            ((x' : G) * (x' : G)⁻¹) * (x : G)⁻¹ := by rw [hcx]
      _ = (b * (x : G)⁻¹) * (b' * (x' : G)⁻¹) := by group
  rw [hgoal]
  exact Subgroup.mul_mem _ hx hx'

private lemma excPayG_pi_one {G : Type} [Group G] {Bs X : Subgroup G}
    (hsplit : ∀ b ∈ Bs, ∃ x ∈ X ⊓ Bs, b * x⁻¹ ∈ Subgroup.centralizer (X : Set G))
    (hZ : Subgroup.center ↥X = ⊥) :
    excPayG_pi hsplit (1 : ↥Bs) = 1 := by
  refine excPayG_pi_unique hsplit hZ (b := (1 : G))
    (x := excPayG_pi hsplit (1 : ↥Bs)) (x' := 1)
    ((excPayG_pi_mem hsplit (1 : ↥Bs)).1) (X.one_mem) ?_ ?_
  · exact excPayG_pi_cent hsplit (1 : ↥Bs)
  · simpa using (Subgroup.centralizer (X : Set G)).one_mem

private lemma excPayG_pi_mul {G : Type} [Group G] {Bs X : Subgroup G}
    (hsplit : ∀ b ∈ Bs, ∃ x ∈ X ⊓ Bs, b * x⁻¹ ∈ Subgroup.centralizer (X : Set G))
    (hZ : Subgroup.center ↥X = ⊥) (b b' : ↥Bs) :
    excPayG_pi hsplit (b * b') = excPayG_pi hsplit b * excPayG_pi hsplit b' := by
  have hxb : (excPayG_pi hsplit b : G) ∈ X := (excPayG_pi_mem hsplit b).1
  have hxb' : (excPayG_pi hsplit b' : G) ∈ X := (excPayG_pi_mem hsplit b').1
  refine excPayG_pi_unique hsplit hZ (b := ((b * b') : G))
    (x := excPayG_pi hsplit (b * b'))
    (x' := excPayG_pi hsplit b * excPayG_pi hsplit b')
    ((excPayG_pi_mem hsplit (b * b')).1) (X.mul_mem hxb hxb') ?_ ?_
  · exact excPayG_pi_cent hsplit (b * b')
  · have h := excPayG_component_mul' (excPayG_pi_cent hsplit b) (excPayG_pi_cent hsplit b')
    simpa [Subgroup.coe_mul] using h

private lemma excPayG_weylAct_simple_simple {tau : Tag} {K : Type} [Field K]
    (k : Fin tau.rank) (a : Fin tau.rank → Kˣ) :
    weylAct (simple tau k) (weylAct (simple tau k) a) = a := by
  rw [← weylAct_mul, (coxeterSystem tau).simple_mul_simple_self, weylAct_one]

private lemma excPayG_weylAct_simple_apply_self
    {tau : Tag} {K : Type} [Field K]
    (k : Fin tau.rank) (a : Fin tau.rank → Kˣ) :
    weylAct (simple tau k) a k = (a k)⁻¹ := by
  change rootChar a ((simple tau k)⁻¹ • (Pi.single k 1)) = (a k)⁻¹
  rw [simple_inv, simple_smul, reflect_single k k, tau.cartan_self]
  rw [rootChar_sub, rootChar_zsmul, CFSG.HardMathSupport.Timmesfeld.Tables.T1b.rootChar_single]
  group

private lemma excPayG_weylAct_simple_of_apply_eq_one
    {tau : Tag} {K : Type} [Field K]
    (k : Fin tau.rank) (a : Fin tau.rank → Kˣ) (hk : a k = 1) :
    weylAct (simple tau k) a = a := by
  funext i
  change rootChar a ((simple tau k)⁻¹ • (Pi.single i 1)) = a i
  rw [simple_inv, simple_smul, reflect_single k i, rootChar_sub, rootChar_zsmul,
    CFSG.HardMathSupport.Timmesfeld.Tables.T1b.rootChar_single,
    CFSG.HardMathSupport.Timmesfeld.Tables.T1b.rootChar_single, hk]
  simp

private lemma excPayG_weylAct_simple_eq_self_iff
    {tau : Tag} {K : Type} [Field K]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (k : Fin tau.rank) (a : Fin tau.rank → Kˣ)
    (ha : ∀ i, a i ^ p = 1) :
    weylAct (simple tau k) a = a ↔ a k = 1 := by
  constructor
  · intro h
    have h2 := congrFun h k
    rw [excPayG_weylAct_simple_apply_self] at h2
    have h3 : (a k) ^ 2 = 1 := by
      rw [sq]
      nth_rewrite 2 [← h2]
      exact mul_inv_cancel _
    have hdiv2 : orderOf (a k) ∣ 2 := orderOf_dvd_of_pow_eq_one h3
    have hdivp : orderOf (a k) ∣ p := orderOf_dvd_of_pow_eq_one (ha k)
    rcases (Nat.dvd_prime Nat.prime_two).mp hdiv2 with h1 | h1
    · exact orderOf_eq_one_iff.mp h1
    · exfalso
      have : 2 ∣ p := h1 ▸ hdivp
      exact (hp.odd_of_ne_two hp2).not_two_dvd_nat this
  · exact excPayG_weylAct_simple_of_apply_eq_one k a

private lemma excPayG_weylAct_simple_pow
    {tau : Tag} {K : Type} [Field K]
    {p : ℕ} (k : Fin tau.rank) (a : Fin tau.rank → Kˣ) (ha : ∀ i, a i ^ p = 1) :
    ∀ i, weylAct (simple tau k) a i ^ p = 1 := by
  intro i
  change rootChar a ((simple tau k)⁻¹ • (Pi.single i 1)) ^ p = 1
  rw [simple_inv, simple_smul, reflect_single k i, rootChar_sub, rootChar_zsmul,
    CFSG.HardMathSupport.Timmesfeld.Tables.T1b.rootChar_single,
    CFSG.HardMathSupport.Timmesfeld.Tables.T1b.rootChar_single]
  have hpow : (a k ^ (tau.cartan k i)) ^ p = 1 := by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ha k, one_zpow]
  have hinv : (((a k) ^ (tau.cartan k i))⁻¹) ^ p = 1 := by
    rw [inv_pow, hpow, inv_one]
  rw [mul_pow, ha i, hinv, mul_one]

private lemma excPayG_eta_conj_simple {t : StatedLieTag} {p f : ℕ} {ht : GGExcFive t}
    {G : Type} [Group G] {Bs X : Subgroup G}
    (M : GGDatumModel t f p ht) (η : ↥X ≃* ↥M.D.Γ)
    (k : Fin (langTag t).rank) (g x : ↥X) {a : Fin (langTag t).rank → GGLˣ}
    (hg : (η g : ModGL (langTag t) GGL) =
      canonicalRep (coxeterSystem (langTag t)) GGL (simple (langTag t) k))
    (hx : (η x : ModGL (langTag t) GGL) = rootDiagUnit (langTag t) a) :
    (η (g * x * g⁻¹) : ModGL (langTag t) GGL) =
      rootDiagUnit (langTag t) (weylAct (simple (langTag t) k) a) := by
  have h1 : (η (g * x * g⁻¹) : ↥M.D.Γ) = η g * η x * (η g)⁻¹ := by
    rw [map_mul, map_mul, map_inv]
  have h2 : ((η (g * x * g⁻¹) : ↥M.D.Γ) : ModGL (langTag t) GGL) =
      (η g : ModGL (langTag t) GGL) * (η x : ModGL (langTag t) GGL) *
        ((η g : ModGL (langTag t) GGL))⁻¹ := by
    rw [h1]
    rfl
  rw [h2, hg, hx, CFSG.HardMathSupport.Timmesfeld.Tables.T1b.canonicalRep_conj_rootDiagUnit]

private lemma excPayG_conj_mem_Bs_X {t : StatedLieTag} {p f : ℕ} {ht : GGExcFive t}
    {G : Type} [Group G] [Finite G] {Bs X : Subgroup G}
    (M : GGDatumModel t f p ht) (η : ↥X ≃* ↥M.D.Γ)
    (hη : ∀ z : ModGL (langTag t) GGL,
      (∃ x : ↥X, (x : G) ∈ Bs ∧ (η x : ModGL (langTag t) GGL) = z) ↔
        ∃ a : Fin (langTag t).rank → GGLˣ, (∀ i, a i ^ p = 1) ∧
          rootDiagUnit (langTag t) a = z)
    (k : Fin (langTag t).rank) (g : ↥X)
    (hg : (η g : ModGL (langTag t) GGL) =
      canonicalRep (coxeterSystem (langTag t)) GGL (simple (langTag t) k))
    {x : ↥X} (hxX : (x : G) ∈ X) (hxBs : (x : G) ∈ Bs)
    {a : Fin (langTag t).rank → GGLˣ} (ha : ∀ i, a i ^ p = 1)
    (hx : (η x : ModGL (langTag t) GGL) = rootDiagUnit (langTag t) a) :
    ((g * x * g⁻¹ : ↥X) : G) ∈ Bs := by
  have hmemX : ((g * x * g⁻¹ : ↥X) : G) ∈ X :=
    X.mul_mem (X.mul_mem g.property hxX) (X.inv_mem g.property)
  have heta := excPayG_eta_conj_simple (Bs := Bs) M η k g x hg hx
  have ha' := excPayG_weylAct_simple_pow k a ha
  let hex : ∃ y : ↥X, (y : G) ∈ Bs ∧
      (η y : ModGL (langTag t) GGL) = rootDiagUnit (langTag t)
        (weylAct (simple (langTag t) k) a) :=
    (hη _).mpr ⟨weylAct (simple (langTag t) k) a, ha', rfl⟩
  let y : ↥X := Classical.choose hex
  have hyBs : (y : G) ∈ Bs := (Classical.choose_spec hex).1
  have hyeta : (η y : ModGL (langTag t) GGL) =
      rootDiagUnit (langTag t) (weylAct (simple (langTag t) k) a) :=
    (Classical.choose_spec hex).2
  have hy_eq : (⟨((g * x * g⁻¹ : ↥X) : G), hmemX⟩ : ↥X) = y :=
    η.injective (Subtype.ext (heta.trans hyeta.symm))
  have hyG : ((g * x * g⁻¹ : ↥X) : G) = (y : G) := congrArg Subtype.val hy_eq
  rw [hyG]
  exact hyBs

private lemma excPayG_conj_mem_Bs {t : StatedLieTag} {p f : ℕ} {ht : GGExcFive t}
    {G : Type} [Group G] [Finite G] {Bs X : Subgroup G}
    (M : GGDatumModel t f p ht) (η : ↥X ≃* ↥M.D.Γ)
    (hη : ∀ z : ModGL (langTag t) GGL,
      (∃ x : ↥X, (x : G) ∈ Bs ∧ (η x : ModGL (langTag t) GGL) = z) ↔
        ∃ a : Fin (langTag t).rank → GGLˣ, (∀ i, a i ^ p = 1) ∧
          rootDiagUnit (langTag t) a = z)
    (hsplit : ∀ b ∈ Bs, ∃ x ∈ X ⊓ Bs, b * x⁻¹ ∈ Subgroup.centralizer (X : Set G))
    (k : Fin (langTag t).rank) (g : ↥X)
    (hg : (η g : ModGL (langTag t) GGL) =
      canonicalRep (coxeterSystem (langTag t)) GGL (simple (langTag t) k)) :
    ∀ b : ↥Bs, (g : G) * (b : G) * (g : G)⁻¹ ∈ Bs := by
  intro b
  have hb : (b : G) ∈ Bs := b.2
  let xb : ↥X := excPayG_pi hsplit b
  let c : G := (b : G) * (xb : G)⁻¹
  have hxbX : (xb : G) ∈ X := (excPayG_pi_mem hsplit b).1
  have hxbBs : (xb : G) ∈ Bs := (excPayG_pi_mem hsplit b).2
  have hc_bs : c ∈ Bs := Bs.mul_mem hb (Bs.inv_mem hxbBs)
  have hc_cent : c ∈ Subgroup.centralizer (X : Set G) := excPayG_pi_cent hsplit b
  have hb_eq : (b : G) = (xb : G) * c := by
    have h1 : c * (xb : G) = b := by
      simp only [c]
      group
    rw [← h1]
    exact ((Subgroup.mem_centralizer_iff.mp hc_cent) (xb : G) hxbX).symm
  let hex : ∃ a : Fin (langTag t).rank → GGLˣ, (∀ i, a i ^ p = 1) ∧
      rootDiagUnit (langTag t) a = (η xb : ModGL (langTag t) GGL) :=
    (hη _).mp ⟨xb, hxbBs, rfl⟩
  let a : Fin (langTag t).rank → GGLˣ := Classical.choose hex
  have ha : ∀ i, a i ^ p = 1 := (Classical.choose_spec hex).1
  have hda : (η xb : ModGL (langTag t) GGL) = rootDiagUnit (langTag t) a :=
    (Classical.choose_spec hex).2.symm
  have hmem : ((g * xb * g⁻¹ : ↥X) : G) ∈ Bs :=
    excPayG_conj_mem_Bs_X (Bs := Bs) M η hη k g hg hxbX hxbBs ha hda
  rw [hb_eq]
  have hcomm : c * (g : G)⁻¹ = (g : G)⁻¹ * c :=
    (Subgroup.mem_centralizer_iff.mp hc_cent (g : G)⁻¹ (X.inv_mem g.property)).symm
  have hgoal : (g : G) * ((xb : G) * c) * (g : G)⁻¹ =
      ((g * xb * g⁻¹ : ↥X) : G) * c := by
    rw [show ((g * xb * g⁻¹ : ↥X) : G) = (g : G) * (xb : G) * (g : G)⁻¹ from rfl]
    calc
      (g : G) * ((xb : G) * c) * (g : G)⁻¹ =
          (g : G) * (xb : G) * (c * (g : G)⁻¹) := by group
      _ = (g : G) * (xb : G) * ((g : G)⁻¹ * c) := by rw [hcomm]
      _ = (g : G) * (xb : G) * (g : G)⁻¹ * c := by group
  rw [hgoal]
  exact Bs.mul_mem hmem hc_bs

private lemma excPayG_conj_pi_mul {G : Type} [Group G] {Bs X : Subgroup G}
    (hsplit : ∀ b ∈ Bs, ∃ x ∈ X ⊓ Bs, b * x⁻¹ ∈ Subgroup.centralizer (X : Set G))
    (g : ↥X) (b : ↥Bs) :
    ∃ c : G, c ∈ Subgroup.centralizer (X : Set G) ∧
      (b : G) = (excPayG_pi hsplit b : G) * c ∧
      (g : G) * (b : G) * (g : G)⁻¹ =
        ((g : G) * (excPayG_pi hsplit b : G) * (g : G)⁻¹) * c := by
  let xb : ↥X := excPayG_pi hsplit b
  let c : G := (b : G) * (xb : G)⁻¹
  have hxbX : (xb : G) ∈ X := (excPayG_pi_mem hsplit b).1
  have hc_cent : c ∈ Subgroup.centralizer (X : Set G) := excPayG_pi_cent hsplit b
  have hb_eq : (b : G) = (xb : G) * c := by
    have h1 : c * (xb : G) = b := by
      simp only [c]
      group
    rw [← h1]
    exact ((Subgroup.mem_centralizer_iff.mp hc_cent) (xb : G) hxbX).symm
  have hcomm : c * (g : G)⁻¹ = (g : G)⁻¹ * c :=
    (Subgroup.mem_centralizer_iff.mp hc_cent (g : G)⁻¹ (X.inv_mem g.property)).symm
  refine ⟨c, hc_cent, hb_eq, ?_⟩
  rw [hb_eq]
  calc
    (g : G) * ((xb : G) * c) * (g : G)⁻¹ =
        (g : G) * (xb : G) * (c * (g : G)⁻¹) := by group
    _ = (g : G) * (xb : G) * ((g : G)⁻¹ * c) := by rw [hcomm]
    _ = (g : G) * (xb : G) * (g : G)⁻¹ * c := by group

private lemma excPayG_conj_fix_iff_fwd {t : StatedLieTag} {p f : ℕ} {ht : GGExcFive t}
    {G : Type} [Group G] {Bs X : Subgroup G}
    (hp : p.Prime) (hp2 : p ≠ 2) (M : GGDatumModel t f p ht) (η : ↥X ≃* ↥M.D.Γ)
    (hsplit : ∀ b ∈ Bs, ∃ x ∈ X ⊓ Bs, b * x⁻¹ ∈ Subgroup.centralizer (X : Set G))
    (k : Fin (langTag t).rank) (g : ↥X)
    (hg : (η g : ModGL (langTag t) GGL) =
      canonicalRep (coxeterSystem (langTag t)) GGL (simple (langTag t) k))
    (b : ↥Bs) {a : Fin (langTag t).rank → GGLˣ} (ha : ∀ i, a i ^ p = 1)
    (hx : (η (excPayG_pi hsplit b) : ModGL (langTag t) GGL) =
      rootDiagUnit (langTag t) a) :
    (g : G) * (b : G) * (g : G)⁻¹ = b → a k = 1 := by
  obtain ⟨c, _, hb_eq, hconj⟩ := excPayG_conj_pi_mul hsplit g b
  let xb : ↥X := excPayG_pi hsplit b
  have hxeta : (η xb : ModGL (langTag t) GGL) =
      rootDiagUnit (langTag t) a := hx
  intro h
  have h1 : ((g : G) * (xb : G) * (g : G)⁻¹) * c = (xb : G) * c := by
    rw [← hconj, ← hb_eq]
    exact h
  have hxb_eq : (g : G) * (xb : G) * (g : G)⁻¹ = (xb : G) :=
    mul_right_cancel h1
  have h4 : (g * xb * g⁻¹ : ↥X) = xb := Subtype.ext hxb_eq
  have h5 : (η (g * xb * g⁻¹) : ModGL (langTag t) GGL) =
      (η xb : ModGL (langTag t) GGL) := by
    rw [h4]
  have h6 : (η (g * xb * g⁻¹) : ModGL (langTag t) GGL) =
      rootDiagUnit (langTag t) (weylAct (simple (langTag t) k) a) :=
    excPayG_eta_conj_simple (Bs := Bs) M η k g xb hg hxeta
  have h7 : rootDiagUnit (langTag t) (weylAct (simple (langTag t) k) a) =
      rootDiagUnit (langTag t) a := by
    rw [← h6, h5]
    exact hxeta
  have h8 : weylAct (simple (langTag t) k) a = a :=
    rootDiagUnit_injective h7
  exact (excPayG_weylAct_simple_eq_self_iff hp hp2 k a ha).mp h8

private lemma excPayG_conj_fix_iff_bwd {t : StatedLieTag} {p f : ℕ} {ht : GGExcFive t}
    {G : Type} [Group G] {Bs X : Subgroup G}
    (hp : p.Prime) (hp2 : p ≠ 2) (M : GGDatumModel t f p ht) (η : ↥X ≃* ↥M.D.Γ)
    (hsplit : ∀ b ∈ Bs, ∃ x ∈ X ⊓ Bs, b * x⁻¹ ∈ Subgroup.centralizer (X : Set G))
    (k : Fin (langTag t).rank) (g : ↥X)
    (hg : (η g : ModGL (langTag t) GGL) =
      canonicalRep (coxeterSystem (langTag t)) GGL (simple (langTag t) k))
    (b : ↥Bs) {a : Fin (langTag t).rank → GGLˣ} (ha : ∀ i, a i ^ p = 1)
    (hx : (η (excPayG_pi hsplit b) : ModGL (langTag t) GGL) =
      rootDiagUnit (langTag t) a) :
    a k = 1 → (g : G) * (b : G) * (g : G)⁻¹ = b := by
  obtain ⟨c, _, hb_eq, hconj⟩ := excPayG_conj_pi_mul hsplit g b
  let xb : ↥X := excPayG_pi hsplit b
  have hxeta : (η xb : ModGL (langTag t) GGL) =
      rootDiagUnit (langTag t) a := hx
  intro hk
  have h8 : weylAct (simple (langTag t) k) a = a :=
    (excPayG_weylAct_simple_eq_self_iff hp hp2 k a ha).mpr hk
  have h6 : (η (g * xb * g⁻¹) : ModGL (langTag t) GGL) =
      rootDiagUnit (langTag t) (weylAct (simple (langTag t) k) a) :=
    excPayG_eta_conj_simple (Bs := Bs) M η k g xb hg hxeta
  have h5 : (η (g * xb * g⁻¹) : ModGL (langTag t) GGL) =
      (η xb : ModGL (langTag t) GGL) := by
    rw [h6, h8]
    exact hxeta.symm
  have h4 : (g * xb * g⁻¹ : ↥X) = xb := η.injective (Subtype.ext h5)
  have hxb_eq : (g : G) * (xb : G) * (g : G)⁻¹ = (xb : G) :=
    congrArg Subtype.val h4
  rw [hconj, hxb_eq, ← hb_eq]

private lemma excPayG_conj_fix_iff {t : StatedLieTag} {p f : ℕ} {ht : GGExcFive t}
    {G : Type} [Group G] {Bs X : Subgroup G}
    (hp : p.Prime) (hp2 : p ≠ 2) (M : GGDatumModel t f p ht) (η : ↥X ≃* ↥M.D.Γ)
    (hsplit : ∀ b ∈ Bs, ∃ x ∈ X ⊓ Bs, b * x⁻¹ ∈ Subgroup.centralizer (X : Set G))
    (k : Fin (langTag t).rank) (g : ↥X)
    (hg : (η g : ModGL (langTag t) GGL) =
      canonicalRep (coxeterSystem (langTag t)) GGL (simple (langTag t) k))
    (b : ↥Bs) {a : Fin (langTag t).rank → GGLˣ} (ha : ∀ i, a i ^ p = 1)
    (hx : (η (excPayG_pi hsplit b) : ModGL (langTag t) GGL) =
      rootDiagUnit (langTag t) a) :
    (g : G) * (b : G) * (g : G)⁻¹ = b ↔ a k = 1 := by
  constructor
  · exact excPayG_conj_fix_iff_fwd hp hp2 M η hsplit k g hg b ha hx
  · exact excPayG_conj_fix_iff_bwd hp hp2 M η hsplit k g hg b ha hx

private lemma excPayG_rootKerFam_closure {t : StatedLieTag} {p : ℕ} (k : Fin (langTag t).rank) :
    Subgroup.closure (Set.range fun a : rootKerFam (langTag t) p k =>
        rootDiagUnit (langTag t) a.1) =
      Subgroup.map (rootDiagUnitHom (langTag t) GGL)
        (MonoidHom.ker (powMonoidHom p : (Fin (langTag t).rank → GGLˣ) →*
          (Fin (langTag t).rank → GGLˣ)) ⊓
          MonoidHom.ker (Pi.evalMonoidHom (fun _ : Fin (langTag t).rank => GGLˣ) k)) := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro z ⟨a, rfl⟩
    exact Subgroup.mem_map.mpr ⟨a.1, by
      rw [Subgroup.mem_inf, MonoidHom.mem_ker, MonoidHom.mem_ker]
      exact ⟨funext a.2.1, a.2.2⟩, rfl⟩
  · intro z hz
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hz
    rw [Subgroup.mem_inf, MonoidHom.mem_ker, MonoidHom.mem_ker] at ha
    exact Subgroup.subset_closure ⟨⟨a, fun i => by simpa using congrFun ha.1 i, ha.2⟩, rfl⟩

private lemma excPayG_fix_fwd {t : StatedLieTag} {p f : ℕ} {ht : GGExcFive t} {G : Type} [Group G]
    {Bs X : Subgroup G}
    (hp : p.Prime) (hp2 : p ≠ 2) (M : GGDatumModel t f p ht) (η : ↥X ≃* ↥M.D.Γ)
    (hη : ∀ z : ModGL (langTag t) GGL,
      (∃ x : ↥X, (x : G) ∈ Bs ∧ (η x : ModGL (langTag t) GGL) = z) ↔
        ∃ a : Fin (langTag t).rank → GGLˣ, (∀ i, a i ^ p = 1) ∧
          rootDiagUnit (langTag t) a = z)
    (hsplit : ∀ b ∈ Bs, ∃ x ∈ X ⊓ Bs, b * x⁻¹ ∈ Subgroup.centralizer (X : Set G))
    (hZ : Subgroup.center ↥X = ⊥) (k : Fin (langTag t).rank) (g : ↥X)
    (hg : (η g : ModGL (langTag t) GGL) =
      canonicalRep (coxeterSystem (langTag t)) GGL (simple (langTag t) k))
    (hgN : (g : G) ∈ Subgroup.normalizer (Bs : Set G))
    (z : ModGL (langTag t) GGL)
    (hz : z ∈ Subgroup.closure (Set.range fun a : rootKerFam (langTag t) p k =>
        rootDiagUnit (langTag t) a.1)) :
    ∃ b : ↥Bs, ggConjAut Bs hgN b = b ∧
      ((η (excPayG_pi hsplit b) : ↥M.D.Γ) : ModGL (langTag t) GGL) = z := by
  rw [excPayG_rootKerFam_closure (t := t) k, Subgroup.mem_map] at hz
  obtain ⟨a, ha, hz'⟩ := hz
  rw [Subgroup.mem_inf, MonoidHom.mem_ker, MonoidHom.mem_ker] at ha
  have hap : ∀ i, a i ^ p = 1 := fun i => by simpa using congrFun ha.1 i
  have hak : a k = 1 := ha.2
  obtain ⟨x, hxBs, hxη⟩ := (hη z).mpr ⟨a, hap, hz'⟩
  let b : ↥Bs := ⟨(x : G), hxBs⟩
  have hpi : excPayG_pi hsplit b = x := by
    refine excPayG_pi_unique hsplit hZ (b := (x : G)) ?_ ?_ ?_ ?_
    · exact (excPayG_pi_mem hsplit b).1
    · exact x.property
    · exact excPayG_pi_cent hsplit b
    · simpa using (Subgroup.centralizer (X : Set G)).one_mem
  have hxda : (η (excPayG_pi hsplit b) : ModGL (langTag t) GGL) =
      rootDiagUnit (langTag t) a := by
    rw [hpi]
    exact hxη.trans hz'.symm
  refine ⟨b, ?_, ?_⟩
  · apply Subtype.ext
    rw [ggConjAut_apply]
    exact (excPayG_conj_fix_iff hp hp2 M η hsplit k g hg b hap hxda).mpr hak
  · rw [hpi]
    exact hxη

private lemma excPayG_fix_bwd {t : StatedLieTag} {p f : ℕ} {ht : GGExcFive t} {G : Type} [Group G]
    {Bs X : Subgroup G}
    (hp : p.Prime) (hp2 : p ≠ 2) (M : GGDatumModel t f p ht) (η : ↥X ≃* ↥M.D.Γ)
    (hη : ∀ z : ModGL (langTag t) GGL,
      (∃ x : ↥X, (x : G) ∈ Bs ∧ (η x : ModGL (langTag t) GGL) = z) ↔
        ∃ a : Fin (langTag t).rank → GGLˣ, (∀ i, a i ^ p = 1) ∧
          rootDiagUnit (langTag t) a = z)
    (hsplit : ∀ b ∈ Bs, ∃ x ∈ X ⊓ Bs, b * x⁻¹ ∈ Subgroup.centralizer (X : Set G))
    (hZ : Subgroup.center ↥X = ⊥) (k : Fin (langTag t).rank) (g : ↥X)
    (hg : (η g : ModGL (langTag t) GGL) =
      canonicalRep (coxeterSystem (langTag t)) GGL (simple (langTag t) k))
    (hgN : (g : G) ∈ Subgroup.normalizer (Bs : Set G))
    (z : ModGL (langTag t) GGL)
    (h : ∃ b : ↥Bs, ggConjAut Bs hgN b = b ∧
      ((η (excPayG_pi hsplit b) : ↥M.D.Γ) : ModGL (langTag t) GGL) = z) :
    z ∈ Subgroup.closure (Set.range fun a : rootKerFam (langTag t) p k =>
        rootDiagUnit (langTag t) a.1) := by
  rw [excPayG_rootKerFam_closure (t := t) k, Subgroup.mem_map]
  obtain ⟨b, hfix, hβ⟩ := h
  obtain ⟨a, hap, hda⟩ :=
    (hη _).mp ⟨excPayG_pi hsplit b, (excPayG_pi_mem hsplit b).2, rfl⟩
  have hfixG : (g : G) * (b : G) * (g : G)⁻¹ = (b : G) := by
    have hv := congrArg Subtype.val hfix
    rw [ggConjAut_apply] at hv
    exact hv
  have hak : a k = 1 :=
    (excPayG_conj_fix_iff hp hp2 M η hsplit k g hg b hap hda.symm).mp hfixG
  refine ⟨a, ?_, ?_⟩
  · rw [Subgroup.mem_inf, MonoidHom.mem_ker, MonoidHom.mem_ker]
    exact ⟨funext hap, hak⟩
  · change rootDiagUnit (langTag t) a = z
    rw [hda]
    exact hβ

private lemma excPayG_fix {t : StatedLieTag} {p f : ℕ} {ht : GGExcFive t} {G : Type} [Group G]
    {Bs X : Subgroup G}
    (hp : p.Prime) (hp2 : p ≠ 2) (M : GGDatumModel t f p ht) (η : ↥X ≃* ↥M.D.Γ)
    (hη : ∀ z : ModGL (langTag t) GGL,
      (∃ x : ↥X, (x : G) ∈ Bs ∧ (η x : ModGL (langTag t) GGL) = z) ↔
        ∃ a : Fin (langTag t).rank → GGLˣ, (∀ i, a i ^ p = 1) ∧
          rootDiagUnit (langTag t) a = z)
    (hsplit : ∀ b ∈ Bs, ∃ x ∈ X ⊓ Bs, b * x⁻¹ ∈ Subgroup.centralizer (X : Set G))
    (hZ : Subgroup.center ↥X = ⊥) (k : Fin (langTag t).rank) (g : ↥X)
    (hg : (η g : ModGL (langTag t) GGL) =
      canonicalRep (coxeterSystem (langTag t)) GGL (simple (langTag t) k))
    (hgN : (g : G) ∈ Subgroup.normalizer (Bs : Set G))
    (z : ModGL (langTag t) GGL) :
    z ∈ Subgroup.closure (Set.range fun a : rootKerFam (langTag t) p k =>
        rootDiagUnit (langTag t) a.1) ↔
      ∃ b : ↥Bs, ggConjAut Bs hgN b = b ∧
        ((η (excPayG_pi hsplit b) : ↥M.D.Γ) : ModGL (langTag t) GGL) = z := by
  constructor
  · exact excPayG_fix_fwd hp hp2 M η hη hsplit hZ k g hg hgN z
  · exact excPayG_fix_bwd hp hp2 M η hη hsplit hZ k g hg hgN z

private noncomputable def excPayG_tuple {t : StatedLieTag} {p f : ℕ} {ht : GGExcFive t}
    {G : Type} [Group G]
    {Bs X : Subgroup G} (M : GGDatumModel t f p ht) (η : ↥X ≃* ↥M.D.Γ)
    (hη : ∀ z : ModGL (langTag t) GGL,
      (∃ x : ↥X, (x : G) ∈ Bs ∧ (η x : ModGL (langTag t) GGL) = z) ↔
        ∃ a : Fin (langTag t).rank → GGLˣ, (∀ i, a i ^ p = 1) ∧
          rootDiagUnit (langTag t) a = z)
    (hsplit : ∀ b ∈ Bs, ∃ x ∈ X ⊓ Bs, b * x⁻¹ ∈ Subgroup.centralizer (X : Set G))
    (k : Fin (langTag t).rank) (b : ↥Bs) : Fin (langTag t).rank → GGLˣ :=
  Classical.choose ((hη _).mp ⟨excPayG_pi hsplit b, (excPayG_pi_mem hsplit b).2, rfl⟩)

private lemma excPayG_tuple_pow {t : StatedLieTag} {p f : ℕ} {ht : GGExcFive t} {G : Type} [Group G]
    {Bs X : Subgroup G} (M : GGDatumModel t f p ht) (η : ↥X ≃* ↥M.D.Γ)
    (hη : ∀ z : ModGL (langTag t) GGL,
      (∃ x : ↥X, (x : G) ∈ Bs ∧ (η x : ModGL (langTag t) GGL) = z) ↔
        ∃ a : Fin (langTag t).rank → GGLˣ, (∀ i, a i ^ p = 1) ∧
          rootDiagUnit (langTag t) a = z)
    (hsplit : ∀ b ∈ Bs, ∃ x ∈ X ⊓ Bs, b * x⁻¹ ∈ Subgroup.centralizer (X : Set G))
    (k : Fin (langTag t).rank) (b : ↥Bs) :
    ∀ i, excPayG_tuple M η hη hsplit k b i ^ p = 1 :=
  (Classical.choose_spec ((hη _).mp ⟨excPayG_pi hsplit b, (excPayG_pi_mem hsplit b).2, rfl⟩)).1

private lemma excPayG_tuple_spec {t : StatedLieTag} {p f : ℕ} {ht : GGExcFive t}
    {G : Type} [Group G]
    {Bs X : Subgroup G} (M : GGDatumModel t f p ht) (η : ↥X ≃* ↥M.D.Γ)
    (hη : ∀ z : ModGL (langTag t) GGL,
      (∃ x : ↥X, (x : G) ∈ Bs ∧ (η x : ModGL (langTag t) GGL) = z) ↔
        ∃ a : Fin (langTag t).rank → GGLˣ, (∀ i, a i ^ p = 1) ∧
          rootDiagUnit (langTag t) a = z)
    (hsplit : ∀ b ∈ Bs, ∃ x ∈ X ⊓ Bs, b * x⁻¹ ∈ Subgroup.centralizer (X : Set G))
    (k : Fin (langTag t).rank) (b : ↥Bs) :
    rootDiagUnit (langTag t) (excPayG_tuple M η hη hsplit k b) =
      (η (excPayG_pi hsplit b) : ModGL (langTag t) GGL) :=
  (Classical.choose_spec ((hη _).mp ⟨excPayG_pi hsplit b, (excPayG_pi_mem hsplit b).2, rfl⟩)).2

private lemma excPayG_tuple_mul {t : StatedLieTag} {p f : ℕ} {ht : GGExcFive t} {G : Type} [Group G]
    {Bs X : Subgroup G} (M : GGDatumModel t f p ht) (η : ↥X ≃* ↥M.D.Γ)
    (hη : ∀ z : ModGL (langTag t) GGL,
      (∃ x : ↥X, (x : G) ∈ Bs ∧ (η x : ModGL (langTag t) GGL) = z) ↔
        ∃ a : Fin (langTag t).rank → GGLˣ, (∀ i, a i ^ p = 1) ∧
          rootDiagUnit (langTag t) a = z)
    (hsplit : ∀ b ∈ Bs, ∃ x ∈ X ⊓ Bs, b * x⁻¹ ∈ Subgroup.centralizer (X : Set G))
    (hZ : Subgroup.center ↥X = ⊥) (k : Fin (langTag t).rank) (b b' : ↥Bs) :
    excPayG_tuple M η hη hsplit k (b * b') =
      excPayG_tuple M η hη hsplit k b * excPayG_tuple M η hη hsplit k b' := by
  apply rootDiagUnit_injective
  rw [rootDiagUnit_mul, excPayG_tuple_spec, excPayG_tuple_spec, excPayG_tuple_spec]
  rw [← Subgroup.coe_mul, ← map_mul, ← excPayG_pi_mul hsplit hZ]

private lemma excPayG_tuple_one {t : StatedLieTag} {p f : ℕ} {ht : GGExcFive t} {G : Type} [Group G]
    {Bs X : Subgroup G} (M : GGDatumModel t f p ht) (η : ↥X ≃* ↥M.D.Γ)
    (hη : ∀ z : ModGL (langTag t) GGL,
      (∃ x : ↥X, (x : G) ∈ Bs ∧ (η x : ModGL (langTag t) GGL) = z) ↔
        ∃ a : Fin (langTag t).rank → GGLˣ, (∀ i, a i ^ p = 1) ∧
          rootDiagUnit (langTag t) a = z)
    (hsplit : ∀ b ∈ Bs, ∃ x ∈ X ⊓ Bs, b * x⁻¹ ∈ Subgroup.centralizer (X : Set G))
    (hZ : Subgroup.center ↥X = ⊥) (k : Fin (langTag t).rank) :
    excPayG_tuple M η hη hsplit k (1 : ↥Bs) = 1 := by
  apply rootDiagUnit_injective
  rw [excPayG_tuple_spec, excPayG_pi_one hsplit hZ, map_one, rootDiagUnit_one]
  rfl

private noncomputable def excPayG_chi {t : StatedLieTag} {p f : ℕ} {ht : GGExcFive t}
    {G : Type} [Group G]
    {Bs X : Subgroup G} (M : GGDatumModel t f p ht) (η : ↥X ≃* ↥M.D.Γ)
    (hη : ∀ z : ModGL (langTag t) GGL,
      (∃ x : ↥X, (x : G) ∈ Bs ∧ (η x : ModGL (langTag t) GGL) = z) ↔
        ∃ a : Fin (langTag t).rank → GGLˣ, (∀ i, a i ^ p = 1) ∧
          rootDiagUnit (langTag t) a = z)
    (hsplit : ∀ b ∈ Bs, ∃ x ∈ X ⊓ Bs, b * x⁻¹ ∈ Subgroup.centralizer (X : Set G))
    (hZ : Subgroup.center ↥X = ⊥) (k : Fin (langTag t).rank) : ↥Bs →* GGLˣ where
  toFun b := excPayG_tuple M η hη hsplit k b k
  map_one' := by rw [excPayG_tuple_one M η hη hsplit hZ k]; rfl
  map_mul' := by
    intro b b'
    rw [excPayG_tuple_mul M η hη hsplit hZ k b b']
    rfl

private lemma excPayG_chi_fix_iff {t : StatedLieTag} {p f : ℕ} {ht : GGExcFive t}
    {G : Type} [Group G]
    {Bs X : Subgroup G} (hp : p.Prime) (hp2 : p ≠ 2) (M : GGDatumModel t f p ht)
    (η : ↥X ≃* ↥M.D.Γ)
    (hη : ∀ z : ModGL (langTag t) GGL,
      (∃ x : ↥X, (x : G) ∈ Bs ∧ (η x : ModGL (langTag t) GGL) = z) ↔
        ∃ a : Fin (langTag t).rank → GGLˣ, (∀ i, a i ^ p = 1) ∧
          rootDiagUnit (langTag t) a = z)
    (hsplit : ∀ b ∈ Bs, ∃ x ∈ X ⊓ Bs, b * x⁻¹ ∈ Subgroup.centralizer (X : Set G))
    (hZ : Subgroup.center ↥X = ⊥) (k : Fin (langTag t).rank) (g : ↥X)
    (hg : (η g : ModGL (langTag t) GGL) =
      canonicalRep (coxeterSystem (langTag t)) GGL (simple (langTag t) k))
    (hgN : (g : G) ∈ Subgroup.normalizer (Bs : Set G)) (b : ↥Bs) :
    ggConjAut Bs hgN b = b ↔ excPayG_chi M η hη hsplit hZ k b = 1 := by
  have hiff : ggConjAut Bs hgN b = b ↔ (g : G) * (b : G) * (g : G)⁻¹ = (b : G) := by
    constructor
    · intro h
      have := congrArg Subtype.val h
      rwa [ggConjAut_apply] at this
    · intro h
      apply Subtype.ext
      rw [ggConjAut_apply]
      exact h
  rw [hiff]
  rw [excPayG_conj_fix_iff hp hp2 M η hsplit k g hg b
    (excPayG_tuple_pow M η hη hsplit k b) (excPayG_tuple_spec M η hη hsplit k b).symm]
  rfl

private lemma excPayG_chi_range {t : StatedLieTag} {p f : ℕ} {ht : GGExcFive t} {G : Type} [Group G]
    {Bs X : Subgroup G} (hp : p.Prime) (hp2 : p ≠ 2) (M : GGDatumModel t f p ht)
    (η : ↥X ≃* ↥M.D.Γ)
    (hη : ∀ z : ModGL (langTag t) GGL,
      (∃ x : ↥X, (x : G) ∈ Bs ∧ (η x : ModGL (langTag t) GGL) = z) ↔
        ∃ a : Fin (langTag t).rank → GGLˣ, (∀ i, a i ^ p = 1) ∧
          rootDiagUnit (langTag t) a = z)
    (hsplit : ∀ b ∈ Bs, ∃ x ∈ X ⊓ Bs, b * x⁻¹ ∈ Subgroup.centralizer (X : Set G))
    (hZ : Subgroup.center ↥X = ⊥) (k : Fin (langTag t).rank) :
    (excPayG_chi M η hη hsplit hZ k).range = rootsOfUnity p GGL := by
  ext ζ
  constructor
  · rintro ⟨b, rfl⟩
    rw [mem_rootsOfUnity]
    exact excPayG_tuple_pow M η hη hsplit k b k
  · intro hζ
    rw [mem_rootsOfUnity] at hζ
    let a : Fin (langTag t).rank → GGLˣ := Pi.mulSingle k ζ
    have hap : ∀ i, a i ^ p = 1 := by
      intro i
      by_cases hi : i = k
      · subst hi
        simp [a, hζ]
      · simp [a, Pi.mulSingle_eq_of_ne hi, one_pow]
    obtain ⟨x, hxBs, hxη⟩ := (hη _).mpr ⟨a, hap, rfl⟩
    let b : ↥Bs := ⟨(x : G), hxBs⟩
    have hpi : excPayG_pi hsplit b = x := by
      refine excPayG_pi_unique hsplit hZ (b := (x : G)) ?_ ?_ ?_ ?_
      · exact (excPayG_pi_mem hsplit b).1
      · exact x.property
      · exact excPayG_pi_cent hsplit b
      · simpa using (Subgroup.centralizer (X : Set G)).one_mem
    refine ⟨b, ?_⟩
    have htuple : excPayG_tuple M η hη hsplit k b = a := by
      apply rootDiagUnit_injective
      rw [excPayG_tuple_spec, hpi]
      exact hxη
    change excPayG_tuple M η hη hsplit k b k = ζ
    rw [htuple]
    simp [a]

private lemma excPayG_card_rootsOfUnity {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    Nat.card (rootsOfUnity p GGL) = p := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  exact IsPrimitiveRoot.card_rootsOfUnity' (IsPrimitiveRoot.iff_orderOf.2 (ggZeta_order p hp hp2))

private lemma excPayG_card_ker {t : StatedLieTag} {p f : ℕ} {ht : GGExcFive t} {G : Type} [Group G]
    {Bs X : Subgroup G} (hp : p.Prime) (hp2 : p ≠ 2) (M : GGDatumModel t f p ht)
    (η : ↥X ≃* ↥M.D.Γ)
    (hη : ∀ z : ModGL (langTag t) GGL,
      (∃ x : ↥X, (x : G) ∈ Bs ∧ (η x : ModGL (langTag t) GGL) = z) ↔
        ∃ a : Fin (langTag t).rank → GGLˣ, (∀ i, a i ^ p = 1) ∧
          rootDiagUnit (langTag t) a = z)
    (hsplit : ∀ b ∈ Bs, ∃ x ∈ X ⊓ Bs, b * x⁻¹ ∈ Subgroup.centralizer (X : Set G))
    (hZ : Subgroup.center ↥X = ⊥) (k : Fin (langTag t).rank) :
    Nat.card ↥Bs = Nat.card ↥(excPayG_chi M η hη hsplit hZ k).ker * p := by
  have hq : Nat.card (↥Bs ⧸ (excPayG_chi M η hη hsplit hZ k).ker) =
      Nat.card ↥(excPayG_chi M η hη hsplit hZ k).range :=
    Nat.card_congr (QuotientGroup.quotientKerEquivRange _).toEquiv
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup
    (excPayG_chi M η hη hsplit hZ k).ker, hq,
    excPayG_chi_range hp hp2 M η hη hsplit hZ k, excPayG_card_rootsOfUnity hp hp2, mul_comm]

private noncomputable def excPayG_chi_fix_equiv {t : StatedLieTag} {p f : ℕ} {ht : GGExcFive t}
    {G : Type} [Group G]
    {Bs X : Subgroup G} (hp : p.Prime) (hp2 : p ≠ 2) (M : GGDatumModel t f p ht)
    (η : ↥X ≃* ↥M.D.Γ)
    (hη : ∀ z : ModGL (langTag t) GGL,
      (∃ x : ↥X, (x : G) ∈ Bs ∧ (η x : ModGL (langTag t) GGL) = z) ↔
        ∃ a : Fin (langTag t).rank → GGLˣ, (∀ i, a i ^ p = 1) ∧
          rootDiagUnit (langTag t) a = z)
    (hsplit : ∀ b ∈ Bs, ∃ x ∈ X ⊓ Bs, b * x⁻¹ ∈ Subgroup.centralizer (X : Set G))
    (hZ : Subgroup.center ↥X = ⊥) (k : Fin (langTag t).rank) (g : ↥X)
    (hg : (η g : ModGL (langTag t) GGL) =
      canonicalRep (coxeterSystem (langTag t)) GGL (simple (langTag t) k))
    (hgN : (g : G) ∈ Subgroup.normalizer (Bs : Set G)) :
    {b : ↥Bs // ggConjAut Bs hgN b = b} ≃
      ↥(excPayG_chi M η hη hsplit hZ k).ker :=
  Equiv.subtypeEquivRight (fun b => by
    rw [MonoidHom.mem_ker]
    exact excPayG_chi_fix_iff hp hp2 M η hη hsplit hZ k g hg hgN b)

private lemma excPayG_sq {t : StatedLieTag} {p f : ℕ} {ht : GGExcFive t} {G : Type} [Group G]
    {Bs X : Subgroup G} (hp : p.Prime) (hp2 : p ≠ 2) (M : GGDatumModel t f p ht)
    (η : ↥X ≃* ↥M.D.Γ)
    (hη : ∀ z : ModGL (langTag t) GGL,
      (∃ x : ↥X, (x : G) ∈ Bs ∧ (η x : ModGL (langTag t) GGL) = z) ↔
        ∃ a : Fin (langTag t).rank → GGLˣ, (∀ i, a i ^ p = 1) ∧
          rootDiagUnit (langTag t) a = z)
    (hsplit : ∀ b ∈ Bs, ∃ x ∈ X ⊓ Bs, b * x⁻¹ ∈ Subgroup.centralizer (X : Set G))
    (k : Fin (langTag t).rank) (g : ↥X)
    (hg : (η g : ModGL (langTag t) GGL) =
      canonicalRep (coxeterSystem (langTag t)) GGL (simple (langTag t) k))
    (hgN : (g : G) ∈ Subgroup.normalizer (Bs : Set G)) :
    (ggConjAut Bs hgN) ^ 2 = 1 := by
  ext b
  rw [MulAut.one_apply]
  rw [pow_two, MulAut.mul_apply, ggConjAut_apply, ggConjAut_apply]
  let xb : ↥X := excPayG_pi hsplit b
  let c : G := (b : G) * (xb : G)⁻¹
  have hxbX : (xb : G) ∈ X := (excPayG_pi_mem hsplit b).1
  have hc_cent : c ∈ Subgroup.centralizer (X : Set G) := excPayG_pi_cent hsplit b
  have hb_eq : (b : G) = (xb : G) * c := by
    have h1 : c * (xb : G) = b := by
      simp only [c]
      group
    rw [← h1]
    exact ((Subgroup.mem_centralizer_iff.mp hc_cent) (xb : G) hxbX).symm
  have hcomm : c * (g : G)⁻¹ = (g : G)⁻¹ * c :=
    (Subgroup.mem_centralizer_iff.mp hc_cent (g : G)⁻¹ (X.inv_mem g.property)).symm
  obtain ⟨a, hap, hda⟩ := (hη _).mp ⟨xb, (excPayG_pi_mem hsplit b).2, rfl⟩
  have h1 : (η (g * xb * g⁻¹) : ModGL (langTag t) GGL) =
      rootDiagUnit (langTag t) (weylAct (simple (langTag t) k) a) :=
    excPayG_eta_conj_simple (Bs := Bs) M η k g xb hg hda.symm
  have h2 : (η (g * (g * xb * g⁻¹) * g⁻¹) : ModGL (langTag t) GGL) =
      rootDiagUnit (langTag t) (weylAct (simple (langTag t) k)
        (weylAct (simple (langTag t) k) a)) :=
    excPayG_eta_conj_simple (Bs := Bs) M η k g (g * xb * g⁻¹) hg h1
  rw [excPayG_weylAct_simple_simple] at h2
  have h3 : (g * (g * xb * g⁻¹) * g⁻¹ : ↥X) = xb :=
    η.injective (Subtype.ext (h2.trans hda))
  have h4 : (g : G) * ((g : G) * (xb : G) * (g : G)⁻¹) * (g : G)⁻¹ = (xb : G) :=
    congrArg Subtype.val h3
  rw [hb_eq]
  calc
    (g : G) * ((g : G) * ((xb : G) * c) * (g : G)⁻¹) * (g : G)⁻¹ =
        (g : G) * ((g : G) * (xb : G) * (c * (g : G)⁻¹)) * (g : G)⁻¹ := by group
    _ = (g : G) * ((g : G) * (xb : G) * ((g : G)⁻¹ * c)) * (g : G)⁻¹ := by rw [hcomm]
    _ = (g : G) * ((g : G) * (xb : G) * (g : G)⁻¹) * (c * (g : G)⁻¹) := by group
    _ = (g : G) * ((g : G) * (xb : G) * (g : G)⁻¹) * ((g : G)⁻¹ * c) := by rw [hcomm]
    _ = ((g : G) * ((g : G) * (xb : G) * (g : G)⁻¹) * (g : G)⁻¹) * c := by group
    _ = (xb : G) * c := by rw [h4]

private lemma excPayG_s_refl {t : StatedLieTag} {p f : ℕ} {ht : GGExcFive t} {G : Type} [Group G]
    {Bs X : Subgroup G} (hp : p.Prime) (hp2 : p ≠ 2) (M : GGDatumModel t f p ht)
    (η : ↥X ≃* ↥M.D.Γ)
    (hη : ∀ z : ModGL (langTag t) GGL,
      (∃ x : ↥X, (x : G) ∈ Bs ∧ (η x : ModGL (langTag t) GGL) = z) ↔
        ∃ a : Fin (langTag t).rank → GGLˣ, (∀ i, a i ^ p = 1) ∧
          rootDiagUnit (langTag t) a = z)
    (hsplit : ∀ b ∈ Bs, ∃ x ∈ X ⊓ Bs, b * x⁻¹ ∈ Subgroup.centralizer (X : Set G))
    (hZ : Subgroup.center ↥X = ⊥) (k : Fin (langTag t).rank) (g : ↥X)
    (hg : (η g : ModGL (langTag t) GGL) =
      canonicalRep (coxeterSystem (langTag t)) GGL (simple (langTag t) k))
    (hgN : (g : G) ∈ Subgroup.normalizer (Bs : Set G)) :
    GGIsReflection p (ggConjAut Bs hgN) := by
  refine ⟨excPayG_sq hp hp2 M η hη hsplit k g hg hgN, ?_⟩
  rw [Nat.card_congr (excPayG_chi_fix_equiv hp hp2 M η hη hsplit hZ k g hg hgN)]
  rw [← excPayG_card_ker hp hp2 M η hη hsplit hZ k]

private lemma excPayG_psi_injective {t : StatedLieTag} {p f : ℕ} {ht : GGExcFive t}
    {G : Type} [Group G] {X : Subgroup G}
    (M : GGDatumModel t f p ht) (η : ↥X ≃* ↥M.D.Γ) :
    Function.Injective (X.subtype.comp η.symm.toMonoidHom) := by
  intro a b hab
  apply η.symm.injective
  exact Subtype.ext hab

private lemma excPayG_psi_range {t : StatedLieTag} {p f : ℕ} {ht : GGExcFive t}
    {G : Type} [Group G] {X : Subgroup G}
    (M : GGDatumModel t f p ht) (η : ↥X ≃* ↥M.D.Γ) :
    (X.subtype.comp η.symm.toMonoidHom).range = X := by
  ext g
  constructor
  · rintro ⟨a, rfl⟩
    exact (η.symm a).property
  · intro hg
    exact ⟨η ⟨g, hg⟩, by simp⟩

private lemma excPayG_psi_compat {t : StatedLieTag} {p f : ℕ} {ht : GGExcFive t}
    {G : Type} [Group G] {Bs X : Subgroup G}
    (M : GGDatumModel t f p ht) (η : ↥X ≃* ↥M.D.Γ)
    (πhom : ↥Bs →* ↥X)
    (hπcent : ∀ b : ↥Bs,
      ((πhom b : G))⁻¹ * (b : G) ∈ Subgroup.centralizer (X : Set G))
    (β : ↥Bs →* ModGL (langTag t) GGL)
    (hβeq : ∀ b : ↥Bs, β b = (η (πhom b) : ModGL (langTag t) GGL))
    (hpres : ∀ (b : ↥Bs) (y : ↥M.D.Γ),
      β b * (y : ModGL (langTag t) GGL) * (β b)⁻¹ ∈ M.D.Γ) :
    ∀ (b : ↥Bs) (y : ↥M.D.Γ),
      (X.subtype.comp η.symm.toMonoidHom)
          ⟨β b * (y : ModGL (langTag t) GGL) * (β b)⁻¹, hpres b y⟩ =
        (b : G) * (X.subtype.comp η.symm.toMonoidHom) y * (b : G)⁻¹ := by
  intro b y
  have harg : (⟨β b * (y : ModGL (langTag t) GGL) * (β b)⁻¹,
      hpres b y⟩ : ↥M.D.Γ) = η (πhom b) * y * (η (πhom b))⁻¹ := by
    apply Subtype.ext
    simp [hβeq b]
  have h1 : (X.subtype.comp η.symm.toMonoidHom)
        ⟨β b * (y : ModGL (langTag t) GGL) * (β b)⁻¹, hpres b y⟩ =
      (X.subtype.comp η.symm.toMonoidHom) (η (πhom b)) *
        (X.subtype.comp η.symm.toMonoidHom) y *
        ((X.subtype.comp η.symm.toMonoidHom) (η (πhom b)))⁻¹ := by
    rw [harg, map_mul, map_mul, map_inv]
  rw [h1]
  have hπ : (X.subtype.comp η.symm.toMonoidHom) (η (πhom b)) = (πhom b : G) := by
    simp
  rw [hπ]
  have hψy : (X.subtype.comp η.symm.toMonoidHom) y ∈ X := (η.symm y).property
  exact (excPayG_conj_eq_of_centralizer (hπcent b) _ hψy).symm

private lemma excPayG_torus_mem {t : StatedLieTag} {p f : ℕ} {ht : GGExcFive t}
    {G : Type} [Group G] {Bs X : Subgroup G}
    (M : GGDatumModel t f p ht) (η : ↥X ≃* ↥M.D.Γ)
    (hη : ∀ z : ModGL (langTag t) GGL,
      (∃ x : ↥X, (x : G) ∈ Bs ∧ (η x : ModGL (langTag t) GGL) = z) ↔
        ∃ a : Fin (langTag t).rank → GGLˣ, (∀ i, a i ^ p = 1) ∧
          rootDiagUnit (langTag t) a = z) :
    ∀ a : Fin (langTag t).rank → GGLˣ, (∀ i, a i ^ p = 1) →
      rootDiagUnit (langTag t) a ∈ M.D.torus := by
  intro a ha
  have hΓ : rootDiagUnit (langTag t) a ∈ M.D.Γ := by
    obtain ⟨x, hxBs, hxeta⟩ := (hη _).mpr ⟨a, ha, rfl⟩
    rw [← hxeta]
    exact (η x).property
  rw [LangDatum.torus, CFSG.RankThree.PartOne.KE.mem_twistedTorusOf]
  refine ⟨CFSG.LieType.Chevalley.rootDiagUnit_mem_torusGroup (τ := langTag t) a, ?_⟩
  have hΓ_le : M.D.Γ ≤ M.D.model := by
    rw [LangDatum.Γ]
    exact Subgroup.commutator_le_self _
  exact (hΓ_le hΓ).2

private lemma excPayG_mem_normalizer {G : Type} [Group G] [Finite G]
    {Bs X : Subgroup G} (g : ↥X)
    (hg_conj : ∀ b : ↥Bs, (g : G) * (b : G) * (g : G)⁻¹ ∈ Bs) :
    (g : G) ∈ Subgroup.normalizer (Bs : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  have hle : Bs.map (MulAut.conj (g : G)) ≤ Bs := by
    intro b hb
    rw [Subgroup.mem_map] at hb
    obtain ⟨b₀, hb₀, rfl⟩ := hb
    simpa [MulAut.conj_apply] using hg_conj ⟨b₀, hb₀⟩
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [Subgroup.card_map_of_injective (MulAut.conj (g : G)).injective]

private lemma excPayG_exists_weylLifts {t : StatedLieTag} {p f : ℕ} {ht : GGExcFive t}
    {G : Type} [Group G] [Finite G] {Bs X : Subgroup G}
    (M : GGDatumModel t f p ht) (η : ↥X ≃* ↥M.D.Γ)
    (hη : ∀ z : ModGL (langTag t) GGL,
      (∃ x : ↥X, (x : G) ∈ Bs ∧ (η x : ModGL (langTag t) GGL) = z) ↔
        ∃ a : Fin (langTag t).rank → GGLˣ, (∀ i, a i ^ p = 1) ∧
          rootDiagUnit (langTag t) a = z)
    (hsplit : ∀ b ∈ Bs, ∃ x ∈ X ⊓ Bs, b * x⁻¹ ∈ Subgroup.centralizer (X : Set G))
    (hnk : ∀ k, canonicalRep (coxeterSystem (langTag t)) GGL (simple (langTag t) k) ∈ M.D.Γ) :
    ∃ gk : Fin (langTag t).rank → ↥X,
      (∀ k, (η (gk k) : ModGL (langTag t) GGL) =
        canonicalRep (coxeterSystem (langTag t)) GGL (simple (langTag t) k)) ∧
      (∀ k, (gk k : G) ∈ X) ∧
      (∀ k, ∀ b : ↥Bs, (gk k : G) * (b : G) * (gk k : G)⁻¹ ∈ Bs) ∧
      (∀ k, (gk k : G) ∈ Subgroup.normalizer (Bs : Set G)) := by
  let nk : Fin (langTag t).rank → ModGL (langTag t) GGL := fun k =>
    canonicalRep (coxeterSystem (langTag t)) GGL (simple (langTag t) k)
  let gk : Fin (langTag t).rank → ↥X := fun k => η.symm ⟨nk k, hnk k⟩
  have hgk_eta : ∀ k, (η (gk k) : ModGL (langTag t) GGL) = nk k := by
    intro k
    simp [gk]
  refine ⟨gk, hgk_eta, ?_, ?_, ?_⟩
  · intro k
    exact (gk k).property
  · intro k
    exact excPayG_conj_mem_Bs (Bs := Bs) M η hη hsplit k (gk k) (hgk_eta k)
  · intro k
    exact excPayG_mem_normalizer (gk k) (fun b =>
      excPayG_conj_mem_Bs (Bs := Bs) M η hη hsplit k (gk k) (hgk_eta k) b)

theorem exists_excPaySquare_of_model {G : Type} [Group G] [Finite G] {t : StatedLieTag}
    {p f : ℕ} {Bs X : Subgroup G} {ht : GGExcFive t}
    (hp : p.Prime) (hp2 : p ≠ 2)
    (M : GGDatumModel t f p ht) (η : ↥X ≃* ↥M.D.Γ)
    (hη : ∀ z : ModGL (langTag t) GGL,
      (∃ x : ↥X, (x : G) ∈ Bs ∧ (η x : ModGL (langTag t) GGL) = z) ↔
        ∃ a : Fin (langTag t).rank → GGLˣ, (∀ i, a i ^ p = 1) ∧ rootDiagUnit (langTag t) a = z)
    (hsplit : ∀ b ∈ Bs, ∃ x ∈ X ⊓ Bs, b * x⁻¹ ∈ Subgroup.centralizer (X : Set G))
    (hZ : Subgroup.center ↥X = ⊥)
    (hnk : ∀ k, canonicalRep (coxeterSystem (langTag t)) GGL (simple (langTag t) k) ∈ M.D.Γ) :
    ∃ S : ExcPaySquare t ht f p Bs X, ∀ k, ∃ (g : G) (hg : g ∈ Subgroup.normalizer (Bs : Set G)),
      g ∈ X ∧ S.s k = ggConjAut Bs hg := by
  classical
  let πhom : ↥Bs →* ↥X :=
    { toFun := excPayG_pi hsplit
      map_one' := excPayG_pi_one hsplit hZ
      map_mul' := excPayG_pi_mul hsplit hZ }
  let psi : ↥M.D.Γ →* G := X.subtype.comp η.symm.toMonoidHom
  have hψ_inj : Function.Injective psi := excPayG_psi_injective M η
  have hψ_range : psi.range = X := excPayG_psi_range M η
  let betaΓ : ↥Bs →* ↥M.D.Γ := η.toMonoidHom.comp πhom
  let β : ↥Bs →* ModGL (langTag t) GGL := (M.D.Γ.subtype).comp betaΓ
  have hβ_mem : ∀ b : ↥Bs, β b ∈ M.D.Γ := fun b => (betaΓ b).property
  have hpres : ∀ (b : ↥Bs) (y : ↥M.D.Γ),
      β b * (y : ModGL (langTag t) GGL) * (β b)⁻¹ ∈ M.D.Γ := by
    intro b y
    exact M.D.Γ.mul_mem (M.D.Γ.mul_mem (hβ_mem b) y.property) (M.D.Γ.inv_mem (hβ_mem b))
  have hcompat : ∀ (b : ↥Bs) (y : ↥M.D.Γ),
      psi ⟨β b * (y : ModGL (langTag t) GGL) * (β b)⁻¹, hpres b y⟩ =
        (b : G) * psi y * (b : G)⁻¹ :=
    excPayG_psi_compat M η πhom
      (fun b => excPayG_cent_inv (excPayG_pi_mem hsplit b).1
        (excPayG_pi_cent hsplit b)) β (fun b => rfl) hpres
  have htorus : ∀ a : Fin (langTag t).rank → GGLˣ, (∀ i, a i ^ p = 1) →
      rootDiagUnit (langTag t) a ∈ M.D.torus := excPayG_torus_mem M η hη
  obtain ⟨gk, hgk_eta, hgk_mem, hgk_conj, hxkN⟩ :=
    excPayG_exists_weylLifts M η hη hsplit hnk
  let s : Fin (langTag t).rank → MulAut ↥Bs := fun k => ggConjAut Bs (hxkN k)
  have s_mem : ∀ k, s k ∈ ggAutomizer X Bs := by
    intro k
    exact ggConjAut_mem_ggAutomizer (hgk_mem k) (hxkN k)
  refine ⟨⟨M, psi, hψ_inj, hψ_range, β, hpres, hcompat, htorus, s, s_mem, ?_, ?_⟩, ?_⟩
  · intro k
    exact excPayG_s_refl hp hp2 M η hη hsplit hZ k (gk k) (hgk_eta k) (hxkN k)
  · intro k z
    exact excPayG_fix hp hp2 M η hη hsplit hZ k (gk k) (hgk_eta k) (hxkN k) z
  · intro k
    exact ⟨gk k, hxkN k, hgk_mem k, rfl⟩

end CFSG.StandardType.ExcPay
