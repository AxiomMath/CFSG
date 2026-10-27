module

public import CFSG.LocalAnalysis.StandardType.ExcPay.Defs
public import CFSG.LocalAnalysis.StandardType.GGLieBridgeTheta
public import Certificates.Certificate13723
public import Certificates.Certificate13724

import CFSG.HardMathSupport.Timmesfeld.LangTorus.TorusAtCore
import CFSG.LocalAnalysis.StandardType.ExcPay.DatumTwE6

public section

namespace CFSG.StandardType.ExcPay

open CFSG.Open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Universal CFSG.StandardType CFSG.StandardType.GGFinModel
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley


private theorem excPayN6_torsion_closure (p : ℕ) :
    (powMonoidHom p).ker.map (rootDiagUnitHom (langTag .twistedE6) GGL) =
      Subgroup.closure {z | ∃ a : Fin (langTag .twistedE6).rank → GGLˣ,
        (∀ i, a i ^ p = 1) ∧ rootDiagUnit (langTag .twistedE6) a = z} := by
  apply le_antisymm
  · intro z hz
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hz
    refine Subgroup.subset_closure ⟨a, ?_, rfl⟩
    intro i
    rw [MonoidHom.mem_ker, powMonoidHom_apply] at ha
    simpa [Pi.pow_apply] using congrFun ha i
  · rw [Subgroup.closure_le]
    rintro z ⟨a, ha, rfl⟩
    refine Subgroup.mem_map.mpr ⟨a, ?_, rfl⟩
    rw [MonoidHom.mem_ker, powMonoidHom_apply]
    funext i
    simpa [Pi.pow_apply] using ha i

private theorem excPayN6_inf_center_eq_bot {G : Type} [Group G] {p : ℕ} {X : Subgroup G}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hZ3 : Nat.card ↥(Subgroup.center ↥X) ∣ 3)
    {A0 : Subgroup ↥X} (hA0el : IsElemAbelian p A0) :
    A0 ⊓ Subgroup.center ↥X = ⊥ := by
  obtain ⟨-, hpow⟩ := hA0el
  rw [eq_bot_iff]
  intro z hz
  obtain ⟨hzA0, hzZ⟩ := Subgroup.mem_inf.mp hz
  have hdvdP : orderOf z ∣ p := orderOf_dvd_iff_pow_eq_one.2 (hpow z hzA0)
  have hdvdZ : orderOf z ∣ Nat.card ↥(Subgroup.center ↥X) :=
    Subgroup.orderOf_dvd_natCard _ hzZ
  have hp3 : p ≠ 3 := by omega
  have hcop3 : Nat.Coprime 3 p := (Nat.coprime_primes Nat.prime_three hp).2 (Ne.symm hp3)
  have hcop : Nat.Coprime (orderOf z) (Nat.card ↥(Subgroup.center ↥X)) :=
    Nat.Coprime.coprime_dvd_left hdvdP (Nat.Coprime.coprime_dvd_left hZ3 hcop3).symm
  exact Subgroup.mem_bot.mpr (orderOf_eq_one_iff.mp (hcop.eq_one_of_dvd hdvdZ))

private theorem excPayN6_conj_theta_range {G : Type} [Group G] {f p : ℕ} {X : Subgroup G}
    {ht : GGExcFive .twistedE6} (M : GGDatumModel .twistedE6 f p ht)
    {θ : ↥X →* ModGL (langTag .twistedE6) GGL}
    (hθrange : θ.range = ⁅ggFixGp .twistedE6 f, ggFixGp .twistedE6 f⁆) :
    ((MulAut.conj M.D.g0⁻¹).toMonoidHom.comp θ).range = M.D.Γ := by
  rw [MonoidHom.range_comp, hθrange, ← ggFixGp_eq_fix M.D M.hΦ, Subgroup.map_commutator,
    (LangDescent.model_eq M.D).symm]
  rfl

private theorem excPayN6_eta_exists {G : Type} [Group G] {f p : ℕ} {X : Subgroup G}
    {ht : GGExcFive .twistedE6} (M : GGDatumModel .twistedE6 f p ht)
    {θ : ↥X →* ModGL (langTag .twistedE6) GGL}
    (hθrange : θ.range = ⁅ggFixGp .twistedE6 f, ggFixGp .twistedE6 f⁆) :
    ∃ η : ↥X →* ↥M.D.Γ, Function.Surjective η ∧ ∀ x : ↥X,
      (η x : ModGL (langTag .twistedE6) GGL) = (MulAut.conj M.D.g0⁻¹) (θ x) := by
  let θ' : ↥X →* ModGL (langTag .twistedE6) GGL :=
    (MulAut.conj M.D.g0⁻¹).toMonoidHom.comp θ
  have hθ'range : θ'.range = M.D.Γ := excPayN6_conj_theta_range M hθrange
  let ψ : ↥X →* ↥M.D.Γ := θ'.codRestrict M.D.Γ (fun x => by
    have hx : θ' x ∈ θ'.range := ⟨x, rfl⟩
    rwa [hθ'range] at hx)
  have hψsurj : Function.Surjective ψ := by
    intro y
    have hy : (y : ModGL (langTag .twistedE6) GGL) ∈ θ'.range := by
      rw [hθ'range]
      exact y.2
    obtain ⟨x, hx⟩ := MonoidHom.mem_range.mp hy
    exact ⟨x, Subtype.ext hx⟩
  exact ⟨ψ, hψsurj, fun x => rfl⟩

private theorem excPayN6_eta_ker {G : Type} [Group G] {f p : ℕ} {X : Subgroup G}
    {ht : GGExcFive .twistedE6} (M : GGDatumModel .twistedE6 f p ht)
    {θ : ↥X →* ModGL (langTag .twistedE6) GGL} {η : ↥X →* ↥M.D.Γ}
    (hηval : ∀ x : ↥X, (η x : ModGL (langTag .twistedE6) GGL) =
      (MulAut.conj M.D.g0⁻¹) (θ x))
    (hθker : θ.ker = Subgroup.center ↥X) :
    η.ker = Subgroup.center ↥X := by
  rw [← hθker]
  ext x
  rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
  constructor
  · intro h
    have h1 : (MulAut.conj M.D.g0⁻¹) (θ x) = 1 := by
      rw [← hηval x]
      simpa using congrArg Subtype.val h
    exact (MulAut.conj M.D.g0⁻¹).injective (by rw [h1, map_one])
  · intro h
    have hθ1 : θ x = 1 := MonoidHom.mem_ker.mp h
    apply Subtype.ext
    show (η x : ModGL (langTag .twistedE6) GGL) = 1
    rw [hηval x, hθ1, map_one]

private theorem excPayN6_theta_comm_of_center {G : Type} [Group G] {f p : ℕ} {X : Subgroup G}
    {ht : GGExcFive .twistedE6} (M : GGDatumModel .twistedE6 f p ht)
    {θ : ↥X →* ModGL (langTag .twistedE6) GGL} {η : ↥X →* ↥M.D.Γ}
    (hηval : ∀ x : ↥X, (η x : ModGL (langTag .twistedE6) GGL) =
      (MulAut.conj M.D.g0⁻¹) (θ x))
    {x : ↥X} {z : ↥M.D.Γ} (hz : z ∈ Subgroup.center ↥M.D.Γ)
    (hxval : (MulAut.conj M.D.g0⁻¹) (θ x) = (z : ModGL (langTag .twistedE6) GGL)) :
    ∀ y : ↥X, θ x * θ y = θ y * θ x := by
  let c : ModGL (langTag .twistedE6) GGL →* ModGL (langTag .twistedE6) GGL :=
    (MulAut.conj M.D.g0⁻¹).toMonoidHom
  have hcinj : Function.Injective c := fun a b h => (MulAut.conj M.D.g0⁻¹).injective h
  have hηc : ∀ y : ↥X, (η y : ModGL (langTag .twistedE6) GGL) = c (θ y) := fun y => hηval y
  have hxvalc : c (θ x) = (z : ModGL (langTag .twistedE6) GGL) := hxval
  intro y
  have h1 := Subgroup.mem_center_iff.mp hz (η y)
  have h2 : (η y : ModGL (langTag .twistedE6) GGL) * (z : ModGL _ GGL) =
      (z : ModGL _ GGL) * (η y : ModGL (langTag .twistedE6) GGL) := by
    simpa using congrArg Subtype.val h1
  have h3 : c (θ y) * c (θ x) = c (θ x) * c (θ y) := by
    rw [hxvalc]
    simpa [← hηc y] using h2
  have h4 : c (θ x * θ y) = c (θ y * θ x) := by
    rw [map_mul c, map_mul c]
    exact h3.symm
  exact hcinj h4

private theorem excPayN6_eta_center_eq_bot {G : Type} [Group G] {f p : ℕ} {X : Subgroup G}
    {ht : GGExcFive .twistedE6} (M : GGDatumModel .twistedE6 f p ht)
    {θ : ↥X →* ModGL (langTag .twistedE6) GGL} {η : ↥X →* ↥M.D.Γ}
    (hηval : ∀ x : ↥X, (η x : ModGL (langTag .twistedE6) GGL) =
      (MulAut.conj M.D.g0⁻¹) (θ x))
    (hθrange : θ.range = ⁅ggFixGp .twistedE6 f, ggFixGp .twistedE6 f⁆)
    (hθcent : ∀ z ∈ ggFixGp .twistedE6 f, (∀ x : ↥X, z * θ x = θ x * z) → z = 1) :
    Subgroup.center ↥M.D.Γ = ⊥ := by
  let c : ModGL (langTag .twistedE6) GGL →* ModGL (langTag .twistedE6) GGL :=
    (MulAut.conj M.D.g0⁻¹).toMonoidHom
  let θ' : ↥X →* ModGL (langTag .twistedE6) GGL := c.comp θ
  have hθ'range : θ'.range = M.D.Γ := excPayN6_conj_theta_range M hθrange
  rw [eq_bot_iff]
  intro z hz
  have hzmem : (z : ModGL (langTag .twistedE6) GGL) ∈ θ'.range := by
    rw [hθ'range]
    exact z.2
  obtain ⟨x, hx⟩ := MonoidHom.mem_range.mp hzmem
  have hxvalc : c (θ x) = (z : ModGL (langTag .twistedE6) GGL) := by
    simpa [θ'] using hx
  have hxval : (MulAut.conj M.D.g0⁻¹) (θ x) = (z : ModGL (langTag .twistedE6) GGL) := hxvalc
  have hfix : θ x ∈ ggFixGp .twistedE6 f := by
    have h1 : θ x ∈ θ.range := ⟨x, rfl⟩
    rw [hθrange] at h1
    exact Subgroup.commutator_le_self _ h1
  have hcomm := excPayN6_theta_comm_of_center M hηval hz hxval
  have hx1 : θ x = 1 := hθcent (θ x) hfix hcomm
  have hz1 : (z : ModGL (langTag .twistedE6) GGL) = 1 := by
    rw [← hxvalc, hx1, map_one]
  exact Subgroup.mem_bot.mpr (Subtype.ext hz1)

private theorem excPayN6_exists_eta {G : Type} [Group G] {f p : ℕ} {X : Subgroup G}
    {ht : GGExcFive .twistedE6} (M : GGDatumModel .twistedE6 f p ht)
    {θ : ↥X →* ModGL (langTag .twistedE6) GGL}
    (hθrange : θ.range = ⁅ggFixGp .twistedE6 f, ggFixGp .twistedE6 f⁆)
    (hθker : θ.ker = Subgroup.center ↥X)
    (hθcent : ∀ z ∈ ggFixGp .twistedE6 f, (∀ x : ↥X, z * θ x = θ x * z) → z = 1) :
    ∃ η : ↥X →* ↥M.D.Γ, Function.Surjective η ∧ η.ker = Subgroup.center ↥X ∧
      Subgroup.center ↥M.D.Γ = ⊥ ∧ ∀ x : ↥X,
        (η x : ModGL (langTag .twistedE6) GGL) = (MulAut.conj M.D.g0⁻¹) (θ x) := by
  obtain ⟨η, hηs, hηval⟩ := excPayN6_eta_exists M hθrange
  exact ⟨η, hηs, excPayN6_eta_ker M hηval hθker,
    excPayN6_eta_center_eq_bot M hηval hθrange hθcent, hηval⟩

private theorem excPayN6_card_subgroupOf {G : Type} [Group G] {p : ℕ} {Bs X : Subgroup G}
    (hinf : Nat.card ↥(X ⊓ Bs : Subgroup G) = p ^ 6) :
    Nat.card ↥((X ⊓ Bs).subgroupOf X) = p ^ 6 := by
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
    (inf_le_left : (X ⊓ Bs : Subgroup G) ≤ X)).toEquiv, hinf]

private theorem excPayN6_theta_injOn {G : Type} [Group G] {X : Subgroup G}
    {θ : ↥X →* ModGL (langTag .twistedE6) GGL} {A0 : Subgroup ↥X}
    (hθker : θ.ker = Subgroup.center ↥X) (hA0infZ : A0 ⊓ Subgroup.center ↥X = ⊥) :
    ∀ a ∈ A0, ∀ b ∈ A0, θ a = θ b → a = b := by
  intro a ha b hb hab
  have hmem : a * b⁻¹ ∈ A0 := A0.mul_mem ha (A0.inv_mem hb)
  have hker : a * b⁻¹ ∈ θ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hab, mul_inv_cancel]
  rw [hθker] at hker
  have hbot : a * b⁻¹ ∈ (⊥ : Subgroup ↥X) := by
    rw [← hA0infZ]
    exact ⟨hmem, hker⟩
  exact mul_inv_eq_one.mp (Subgroup.mem_bot.mp hbot)

private theorem excPayN6_card_map_of_injOn {G : Type} [Group G] {p : ℕ} {X : Subgroup G}
    {θ : ↥X →* ModGL (langTag .twistedE6) GGL} {A0 : Subgroup ↥X} {n : ℕ}
    (hinj : ∀ a ∈ A0, ∀ b ∈ A0, θ a = θ b → a = b) (hcardA0 : Nat.card A0 = p ^ n) :
    Nat.card ↥(A0.map θ) = p ^ n := by
  have hsubInj : Function.Injective (θ.subgroupMap A0) := by
    intro a b hab
    exact Subtype.ext (hinj a a.2 b b.2 (by simpa using congrArg Subtype.val hab))
  have h := Nat.card_congr (Equiv.ofBijective (θ.subgroupMap A0)
    ⟨hsubInj, θ.subgroupMap_surjective A0⟩)
  rw [← hcardA0]
  exact h.symm

private theorem excPayN6_map_le_ggFixGp {G : Type} [Group G] {f : ℕ} {X : Subgroup G}
    {θ : ↥X →* ModGL (langTag .twistedE6) GGL} {A0 : Subgroup ↥X}
    (hθrange : θ.range = ⁅ggFixGp .twistedE6 f, ggFixGp .twistedE6 f⁆) :
    A0.map θ ≤ ggFixGp .twistedE6 f := by
  calc A0.map θ ≤ θ.range := Subgroup.map_le_range θ A0
    _ = ⁅ggFixGp .twistedE6 f, ggFixGp .twistedE6 f⁆ := hθrange
    _ ≤ ggFixGp .twistedE6 f := Subgroup.commutator_le_self _

private theorem excPayN6_tp_forward {G : Type} [Group G] {f p : ℕ} {Bs X : Subgroup G}
    {ht : GGExcFive .twistedE6} {M : GGDatumModel .twistedE6 f p ht}
    {θ : ↥X →* ModGL (langTag .twistedE6) GGL}
    (hM : ((X ⊓ Bs).subgroupOf X |>.map θ).map (MulAut.conj M.D.g0⁻¹).toMonoidHom =
      Subgroup.closure {z | ∃ a : Fin (langTag .twistedE6).rank → GGLˣ,
        (∀ i, a i ^ p = 1) ∧ rootDiagUnit (langTag .twistedE6) a = z})
    {η : ↥X →* ↥M.D.Γ} (hηval : ∀ x : ↥X,
      (η x : ModGL (langTag .twistedE6) GGL) = (MulAut.conj M.D.g0⁻¹) (θ x)) :
    ∀ z : ModGL (langTag .twistedE6) GGL,
      (∃ x : ↥X, (x : G) ∈ Bs ∧ (η x : ModGL (langTag .twistedE6) GGL) = z) →
        ∃ a : Fin (langTag .twistedE6).rank → GGLˣ, (∀ i, a i ^ p = 1) ∧
          rootDiagUnit (langTag .twistedE6) a = z := by
  intro z
  rintro ⟨x, hxBs, rfl⟩
  have hxmem : x ∈ (X ⊓ Bs).subgroupOf X := Subgroup.mem_subgroupOf.mpr ⟨x.2, hxBs⟩
  have hzA : (MulAut.conj M.D.g0⁻¹) (θ x) ∈
      ((X ⊓ Bs).subgroupOf X |>.map θ).map (MulAut.conj M.D.g0⁻¹).toMonoidHom :=
    Subgroup.mem_map.mpr ⟨θ x, Subgroup.mem_map.mpr ⟨x, hxmem, rfl⟩, rfl⟩
  rw [hM, ← excPayN6_torsion_closure p] at hzA
  obtain ⟨a, ha, heq⟩ := Subgroup.mem_map.mp hzA
  refine ⟨a, ?_, ?_⟩
  · rw [MonoidHom.mem_ker, powMonoidHom_apply] at ha
    intro i
    simpa [Pi.pow_apply] using congrFun ha i
  · rw [hηval x]
    exact heq

private theorem excPayN6_tp_backward {G : Type} [Group G] {f p : ℕ} {Bs X : Subgroup G}
    {ht : GGExcFive .twistedE6} {M : GGDatumModel .twistedE6 f p ht}
    {θ : ↥X →* ModGL (langTag .twistedE6) GGL}
    (hM : ((X ⊓ Bs).subgroupOf X |>.map θ).map (MulAut.conj M.D.g0⁻¹).toMonoidHom =
      Subgroup.closure {z | ∃ a : Fin (langTag .twistedE6).rank → GGLˣ,
        (∀ i, a i ^ p = 1) ∧ rootDiagUnit (langTag .twistedE6) a = z})
    {η : ↥X →* ↥M.D.Γ} (hηval : ∀ x : ↥X,
      (η x : ModGL (langTag .twistedE6) GGL) = (MulAut.conj M.D.g0⁻¹) (θ x)) :
    ∀ z : ModGL (langTag .twistedE6) GGL,
      (∃ a : Fin (langTag .twistedE6).rank → GGLˣ, (∀ i, a i ^ p = 1) ∧
        rootDiagUnit (langTag .twistedE6) a = z) →
        ∃ x : ↥X, (x : G) ∈ Bs ∧ (η x : ModGL (langTag .twistedE6) GGL) = z := by
  intro z
  rintro ⟨a, ha, rfl⟩
  have haP : a ∈ (powMonoidHom p).ker := by
    rw [MonoidHom.mem_ker, powMonoidHom_apply]
    funext i
    simpa [Pi.pow_apply] using ha i
  have hzTp : rootDiagUnit (langTag .twistedE6) a ∈
      (powMonoidHom p).ker.map (rootDiagUnitHom (langTag .twistedE6) GGL) :=
    Subgroup.mem_map.mpr ⟨a, haP, rfl⟩
  rw [excPayN6_torsion_closure p, ← hM] at hzTp
  obtain ⟨y, hyA, hy⟩ := Subgroup.mem_map.mp hzTp
  obtain ⟨x, hxmem, rfl⟩ := Subgroup.mem_map.mp hyA
  refine ⟨x, (Subgroup.mem_subgroupOf.mp hxmem).2, ?_⟩
  rw [hηval x]
  exact hy

theorem exists_excPayModel_TwE6 {G : Type} [Group G] [Finite G] {p f : ℕ} {Bs X : Subgroup G}
    {ht : GGExcFive .twistedE6} (hp : p.Prime) (hp5 : 5 ≤ p) (hf : 1 ≤ f)
    (hplus : p ∣ 2 ^ f + 1) (hBs : IsElemAbelian p Bs) {ψ₀ : (ggU .twistedE6 0 f).K →* G}
    (hpres : GGPresentsG0 X (ggU .twistedE6 0 f).D .twistedE6 0 f ψ₀)
    (hZ3 : Nat.card ↥(Subgroup.center ↥X) ∣ 3)
    (hinf : Nat.card ↥(X ⊓ Bs : Subgroup G) = p ^ 6) :
    ∃ (M : GGDatumModel .twistedE6 f p ht) (η : ↥X →* ↥M.D.Γ),
      Function.Surjective η ∧ η.ker = Subgroup.center ↥X ∧ Subgroup.center ↥M.D.Γ = ⊥ ∧
      ∀ z : ModGL (langTag .twistedE6) GGL,
        (∃ x : ↥X, (x : G) ∈ Bs ∧ (η x : ModGL (langTag .twistedE6) GGL) = z) ↔
          ∃ a : Fin (langTag .twistedE6).rank → GGLˣ, (∀ i, a i ^ p = 1) ∧
            rootDiagUnit (langTag .twistedE6) a = z := by
  classical
  obtain ⟨θ, -, hθker, hθrange, hθcent⟩ :=
    LieCore.ggLieBridge_theta (t := .twistedE6) (n := 0) (f := f) ht hf hpres
  let A0 : Subgroup ↥X := (X ⊓ Bs).subgroupOf X
  let A : Subgroup (ModGL (langTag .twistedE6) GGL) := A0.map θ
  have hA : A ≤ ggFixGp .twistedE6 f := excPayN6_map_le_ggFixGp hθrange
  have hA0el : IsElemAbelian p A0 := (hBs.mono inf_le_right).comap X.subtype_injective
  have hcardA0 : Nat.card A0 = p ^ 6 := excPayN6_card_subgroupOf hinf
  have hA0infZ : A0 ⊓ Subgroup.center ↥X = ⊥ :=
    excPayN6_inf_center_eq_bot hp hp5 hZ3 hA0el
  have hcardA : Nat.card A = p ^ 6 :=
    excPayN6_card_map_of_injOn (excPayN6_theta_injOn hθker hA0infZ) hcardA0
  have hAel : IsElemAbelian p A := hA0el.map θ
  obtain ⟨M, hM⟩ :=
    exists_datumModel_TwE6_of_card (ht := ht) hp hp5 hf hplus A hA hAel hcardA
  obtain ⟨η, hηs, hηker, hZΓ, hηval⟩ := excPayN6_exists_eta (ht := ht) M hθrange hθker hθcent
  refine ⟨M, η, hηs, hηker, hZΓ, ?_⟩
  intro z
  exact ⟨excPayN6_tp_forward hM hηval z, excPayN6_tp_backward hM hηval z⟩

end CFSG.StandardType.ExcPay
