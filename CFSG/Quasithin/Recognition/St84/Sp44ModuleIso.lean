module

public import CFSG.Quasithin.Recognition.St84.Sp44Module
public import CFSG.RankThree.PartOne.KC.EvenSymplecticFourRootAxisNormalizer

public section

namespace CFSG.Quasithin.F112R.St84

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F112R
open CFSG.RankThree.PartOne.KCRootAxis
open CFSG.QuasithinUnique.Setup.X7b
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain
open CFSG.CGT.PushingUpLit.CGT6.TwoThree
open scoped Matrix IsMulCommutative

namespace Sp44

open ModHyp

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]
variable {G : Type} [Group G] [Finite G]
variable {Q Z K : Subgroup G} {τ : G}
variable {α : ↥K ≃* SL₂ F} {β : ↥Q →* Multiplicative (Fin 2 → F)}

theorem conjHom_conj (D : ModHyp Q Z K τ α β) (k h : ↥K) (q : ↥Q) :
    conjHom D.norm_Q k (conjHom D.norm_Q h q) = conjHom D.norm_Q (k * h) q := by
  refine Subtype.ext ?_
  simp only [conjHom, MonoidHom.coe_mk, OneHom.coe_mk, Subtype.coe_mk, Subgroup.coe_mul]
  group

theorem tauHom_conjHom (D : ModHyp Q Z K τ α β) (k : ↥K) (q : ↥Q) :
    tauHom D.tau_Q (conjHom D.norm_Q k q) = conjHom D.norm_Q k (tauHom D.tau_Q q) := by
  refine Subtype.ext ?_
  have hk : τ * (k : G) = (k : G) * τ := D.tau_K k k.2
  have hk'' : (k : G)⁻¹ * τ⁻¹ = τ⁻¹ * (k : G)⁻¹ := by
    calc (k : G)⁻¹ * τ⁻¹ = (τ * (k : G))⁻¹ := by rw [mul_inv_rev]
      _ = ((k : G) * τ)⁻¹ := by rw [hk]
      _ = τ⁻¹ * (k : G)⁻¹ := by rw [mul_inv_rev]
  simp only [tauHom, conjHom, MonoidHom.coe_mk, OneHom.coe_mk, Subtype.coe_mk]
  calc τ * ((k : G) * (q : G) * (k : G)⁻¹) * τ⁻¹
      = (τ * (k : G)) * (q : G) * ((k : G)⁻¹ * τ⁻¹) := by group
    _ = ((k : G) * τ) * (q : G) * (τ⁻¹ * (k : G)⁻¹) := by rw [hk, hk'']
    _ = (k : G) * (τ * (q : G) * τ⁻¹) * (k : G)⁻¹ := by group

theorem conj_mem_Cplus_hOf (hF : Fintype.card F = 4) (D : ModHyp Q Z K τ α β)
    (μ : Fˣ) {q : G} (hq : q ∈ Cplus α Q) :
    ((hOf α μ : ↥K) : G) * q * ((hOf α μ : ↥K) : G)⁻¹ ∈ Cplus α Q := by
  obtain ⟨hqQ, hqC⟩ := mem_Cplus_iff.mp hq
  have hμ2 : ((μ : F)) ^ 2 ≠ 0 := pow_ne_zero 2 (Units.ne_zero μ)
  refine mem_Cplus_iff.mpr ⟨D.norm_Q _ (hOf α μ).2 q hqQ, fun t => ?_⟩
  set s : F := ((μ : F) ^ 2)⁻¹ * t with hs
  have hx : ((xElt α t : ↥K) : G) =
      ((hOf α μ : ↥K) : G) * ((xElt α s : ↥K) : G) * ((hOf α μ : ↥K) : G)⁻¹ := by
    have h := conj_hOf_x α μ s
    have hst : (μ : F) ^ 2 * s = t := by
      rw [hs, ← mul_assoc, mul_inv_cancel₀ hμ2, one_mul]
    rw [hst] at h
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using
      (congrArg Subtype.val h).symm
  calc ((xElt α t : ↥K) : G) * (((hOf α μ : ↥K) : G) * q * ((hOf α μ : ↥K) : G)⁻¹)
      = (((hOf α μ : ↥K) : G) * ((xElt α s : ↥K) : G) * ((hOf α μ : ↥K) : G)⁻¹) *
          (((hOf α μ : ↥K) : G) * q * ((hOf α μ : ↥K) : G)⁻¹) := by rw [hx]
    _ = ((hOf α μ : ↥K) : G) * (((xElt α s : ↥K) : G) * q) * ((hOf α μ : ↥K) : G)⁻¹ := by
        group
    _ = ((hOf α μ : ↥K) : G) * (q * ((xElt α s : ↥K) : G)) * ((hOf α μ : ↥K) : G)⁻¹ := by
        rw [hqC s]
    _ = (((hOf α μ : ↥K) : G) * q * ((hOf α μ : ↥K) : G)⁻¹) *
          ((xElt α t : ↥K) : G) := by rw [hx]; group

theorem conj_mem_Cplus_tau (D : ModHyp Q Z K τ α β) {q : G} (hq : q ∈ Cplus α Q) :
    τ * q * τ⁻¹ ∈ Cplus α Q := by
  obtain ⟨hqQ, hqC⟩ := mem_Cplus_iff.mp hq
  refine mem_Cplus_iff.mpr ⟨D.tau_Q q hqQ, fun t => ?_⟩
  have hxτ : τ * ((xElt α t : ↥K) : G) * τ⁻¹ = ((xElt α t : ↥K) : G) := by
    have h := D.tau_K (xElt α t) (xElt α t).2
    rw [h]
    group
  calc ((xElt α t : ↥K) : G) * (τ * q * τ⁻¹)
      = (τ * ((xElt α t : ↥K) : G) * τ⁻¹) * (τ * q * τ⁻¹) := by rw [hxτ]
    _ = τ * (((xElt α t : ↥K) : G) * q) * τ⁻¹ := by group
    _ = τ * (q * ((xElt α t : ↥K) : G)) * τ⁻¹ := by rw [hqC t]
    _ = (τ * q * τ⁻¹) * (τ * ((xElt α t : ↥K) : G) * τ⁻¹) := by group
    _ = (τ * q * τ⁻¹) * ((xElt α t : ↥K) : G) := by rw [hxτ]

@[expose] noncomputable def hT (α : ↥K ≃* SL₂ F) (hF : Fintype.card F = 4) : ↥K :=
  hOf α (mu0 hF)

theorem alpha_hT (hF : Fintype.card F = 4) : α (hT α hF) = diagSL (mu0 hF) :=
  alpha_hOf α (mu0 hF)

theorem hOf_comm_hT (hF : Fintype.card F = 4) (μ : Fˣ) :
    hOf α μ * hT α hF = hT α hF * hOf α μ := by
  apply α.injective
  simp only [map_mul, alpha_hOf, alpha_hT]
  rw [← diagSL_mul, ← diagSL_mul, mul_comm]

theorem one_add_mu0_eq_sq (hF : Fintype.card F = 4) :
    1 + ((mu0 hF : Fˣ) : F) = (mu0 hF : F) ^ 2 := by
  have h := one_add_mu0_add_mu0_sq hF
  have h' : 1 + ((mu0 hF : Fˣ) : F) = -((mu0 hF : F) ^ 2) := by
    linear_combination h
  rwa [CharTwo.neg_eq] at h'

@[expose] noncomputable def coeC (D : ModHyp Q Z K τ α β) (c : ↥(Cplus α Q)) : ↥Q :=
  ⟨(c : G), Cplus_le_Q α c.2⟩

@[simp] theorem coeC_val (D : ModHyp Q Z K τ α β) (c : ↥(Cplus α Q)) :
    ((coeC D c : ↥Q) : G) = (c : G) := rfl

@[simp] theorem coeC_mul (D : ModHyp Q Z K τ α β) (x y : ↥(Cplus α Q)) :
    coeC D (x * y) = coeC D x * coeC D y :=
  Subtype.ext (Subgroup.coe_mul (H := Cplus α Q) x y)

@[expose] noncomputable def phiC1 (hF : Fintype.card F = 4) (D : ModHyp Q Z K τ α β) :
    ↥(Cplus α Q) →* ↥Q where
  toFun c := coeC D c * conjHom D.norm_Q (hT α hF) (coeC D c)
  map_one' := by
    have h1 : coeC D (1 : ↥(Cplus α Q)) = 1 := Subtype.ext rfl
    rw [h1, map_one, mul_one]
  map_mul' x y := by
    haveI : IsMulCommutative ↥Q := D.elem.1
    show coeC D (x * y) * conjHom D.norm_Q (hT α hF) (coeC D (x * y)) =
      (coeC D x * conjHom D.norm_Q (hT α hF) (coeC D x)) *
        (coeC D y * conjHom D.norm_Q (hT α hF) (coeC D y))
    rw [coeC_mul, map_mul]
    ac_rfl

@[expose] noncomputable def L1 (hF : Fintype.card F = 4) (D : ModHyp Q Z K τ α β) :
    Subgroup ↥Q :=
  (phiC1 hF D).range

theorem mem_L1 {hF : Fintype.card F = 4} {D : ModHyp Q Z K τ α β} {c : ↥Q} :
    c ∈ L1 hF D ↔ ∃ x : ↥(Cplus α Q), phiC1 hF D x = c :=
  MonoidHom.mem_range

theorem phiC1_mem_Cplus (hF : Fintype.card F = 4) (D : ModHyp Q Z K τ α β)
    (x : ↥(Cplus α Q)) : ((phiC1 hF D x : ↥Q) : G) ∈ Cplus α Q := by
  have h1 : ((phiC1 hF D x : ↥Q) : G) =
      (x : G) * (((hOf α (mu0 hF) : ↥K) : G) * (x : G) *
        ((hOf α (mu0 hF) : ↥K) : G)⁻¹) := by
    show ((coeC D x * conjHom D.norm_Q (hT α hF) (coeC D x) : ↥Q) : G) = _
    simp only [Subgroup.coe_mul, coeC_val, conjHom, MonoidHom.coe_mk, OneHom.coe_mk,
      Subtype.coe_mk, hT]
  rw [h1]
  exact Subgroup.mul_mem _ x.2
    (conj_mem_Cplus_hOf hF D (mu0 hF) x.2)

theorem L1_le_Cplus (hF : Fintype.card F = 4) (D : ModHyp Q Z K τ α β) {c : ↥Q}
    (hc : c ∈ L1 hF D) : (c : G) ∈ Cplus α Q := by
  obtain ⟨x, rfl⟩ := (mem_L1 (hF := hF) (D := D)).mp hc
  exact phiC1_mem_Cplus hF D x

theorem phiC1_beta (hF : Fintype.card F = 4) (D : ModHyp Q Z K τ α β)
    (x : ↥(Cplus α Q)) :
    betaAdd β (phiC1 hF D x) =
      ![(mu0 hF : F) ^ 2 * betaAdd β (coeC D x) 0, 0] := by
  set a : F := betaAdd β (coeC D x) 0 with ha
  have hb : betaAdd β (coeC D x) = ![a, 0] :=
    Cplus_beta_eq (α := α) (β := β) (c := coeC D x) D.equiv D.norm_Q x.2
  have h := betaAdd_conj D.equiv D.norm_Q (hT α hF) (coeC D x)
  rw [alpha_hT, diagSL_mulVec_four hF, hb] at h
  have h1 : a + ((mu0 hF : Fˣ) : F) * a = (mu0 hF : F) ^ 2 * a := by
    linear_combination a * one_add_mu0_eq_sq hF
  show betaAdd β (coeC D x * conjHom D.norm_Q (hT α hF) (coeC D x)) = _
  have h' : betaAdd β (conjHom D.norm_Q (hT α hF) (coeC D x)) =
      ![((mu0 hF : Fˣ) : F) * a, 0] := by
    simpa [conjHom] using h
  rw [betaAdd_mul, hb, h']
  ext i
  fin_cases i
  · simpa using h1
  · simp

theorem L1_beta_inj (hF : Fintype.card F = 4) (D : ModHyp Q Z K τ α β) {c : ↥Q}
    (hc : c ∈ L1 hF D) (hbeta : betaAdd β c = 0) : c = 1 := by
  obtain ⟨x, rfl⟩ := (mem_L1 (hF := hF) (D := D)).mp hc
  have h := phiC1_beta hF D x
  rw [hbeta] at h
  have ha : betaAdd β (coeC D x) 0 = 0 := by
    have h0 := congrFun h 0
    simpa using h0
  have hxZ : ((coeC D x : ↥Q) : G) ∈ Z := by
    refine (betaAdd_eq_zero_iff D.ker (coeC D x)).mp ?_
    rw [Cplus_beta_eq (α := α) (β := β) (c := coeC D x) D.equiv D.norm_Q x.2, ha]
    ext i
    fin_cases i <;> rfl
  have hfix : conjHom D.norm_Q (hT α hF) (coeC D x) = coeC D x :=
    conjHom_eq_self_of_mem_Z D hF hxZ (hT α hF)
  show coeC D x * conjHom D.norm_Q (hT α hF) (coeC D x) = 1
  rw [hfix, mul_self_mem_Q D.elem]

theorem L1_beta_surj (hF : Fintype.card F = 4) (D : ModHyp Q Z K τ α β) (a : F) :
    ∃ c ∈ L1 hF D, betaAdd β c = ![a, 0] := by
  have hμ0 : (mu0 hF : F) ≠ 0 := Units.ne_zero (mu0 hF)
  have hμ2 : (mu0 hF : F) ^ 2 ≠ 0 := pow_ne_zero 2 hμ0
  set m : F := ((mu0 hF : F) ^ 2)⁻¹ * a with hm
  obtain ⟨c, hcC, hcβ⟩ :=
    exists_Cplus_beta hF D.equiv D.ker D.norm_Q D.cent_Z D.le_Z D.card_Z D.cardT m
  refine ⟨phiC1 hF D ⟨(c : G), hcC⟩, ⟨_, rfl⟩, ?_⟩
  rw [phiC1_beta]
  have hval : betaAdd β (coeC D ⟨(c : G), hcC⟩) 0 = m := by
    have h : betaAdd β (coeC D ⟨(c : G), hcC⟩) = ![m, 0] := by
      rw [show (coeC D ⟨(c : G), hcC⟩ : ↥Q) = c from Subtype.ext rfl]
      exact hcβ
    simpa using congrFun h 0
  rw [hval]
  have hmul : (mu0 hF : F) ^ 2 * m = a := by
    rw [hm, ← mul_assoc, mul_inv_cancel₀ hμ2, one_mul]
  ext i
  fin_cases i <;> simp [hmul]

noncomputable def qq1 (hF : Fintype.card F = 4) (D : ModHyp Q Z K τ α β) (a : F) : ↥Q :=
  Classical.choose (L1_beta_surj hF D a)

theorem qq1_mem (hF : Fintype.card F = 4) (D : ModHyp Q Z K τ α β) (a : F) :
    qq1 hF D a ∈ L1 hF D :=
  (Classical.choose_spec (L1_beta_surj hF D a)).1

theorem qq1_beta (hF : Fintype.card F = 4) (D : ModHyp Q Z K τ α β) (a : F) :
    betaAdd β (qq1 hF D a) = ![a, 0] :=
  (Classical.choose_spec (L1_beta_surj hF D a)).2

theorem qq1_unique (hF : Fintype.card F = 4) (D : ModHyp Q Z K τ α β) {a : F} {c : ↥Q}
    (hc : c ∈ L1 hF D) (h : betaAdd β c = ![a, 0]) : c = qq1 hF D a := by
  have hmem : c * (qq1 hF D a)⁻¹ ∈ L1 hF D :=
    Subgroup.mul_mem _ hc (Subgroup.inv_mem _ (qq1_mem hF D a))
  have hzero : betaAdd β (c * (qq1 hF D a)⁻¹) = 0 := by
    rw [betaAdd_mul, betaAdd_inv, h, qq1_beta]
    ext i
    fin_cases i <;> simp
  have h1 : c * (qq1 hF D a)⁻¹ = 1 := L1_beta_inj hF D hmem hzero
  calc c = c * (qq1 hF D a)⁻¹ * qq1 hF D a := by group
    _ = qq1 hF D a := by rw [h1]; simp

theorem qq1_add (hF : Fintype.card F = 4) (D : ModHyp Q Z K τ α β) (a b : F) :
    qq1 hF D (a + b) = qq1 hF D a * qq1 hF D b := by
  refine (qq1_unique hF D ?_ ?_).symm
  · exact Subgroup.mul_mem _ (qq1_mem hF D a) (qq1_mem hF D b)
  · rw [betaAdd_mul, qq1_beta, qq1_beta]
    ext i
    fin_cases i <;> simp

theorem qq1_zero (hF : Fintype.card F = 4) (D : ModHyp Q Z K τ α β) :
    qq1 hF D 0 = 1 := by
  refine (qq1_unique hF D (Subgroup.one_mem _) ?_).symm
  rw [betaAdd_one]
  ext i
  fin_cases i <;> rfl

theorem qq1_mem_Cplus (hF : Fintype.card F = 4) (D : ModHyp Q Z K τ α β) (a : F) :
    ((qq1 hF D a : ↥Q) : G) ∈ Cplus α Q :=
  L1_le_Cplus hF D (qq1_mem hF D a)

theorem conj_mem_L1_hOf (hF : Fintype.card F = 4) (D : ModHyp Q Z K τ α β)
    (μ : Fˣ) {c : ↥Q} (hc : c ∈ L1 hF D) :
    conjHom D.norm_Q (hOf α μ) c ∈ L1 hF D := by
  obtain ⟨x, rfl⟩ := (mem_L1 (hF := hF) (D := D)).mp hc
  have hx : ((hOf α μ : ↥K) : G) * (x : G) * ((hOf α μ : ↥K) : G)⁻¹ ∈ Cplus α Q :=
    conj_mem_Cplus_hOf hF D μ x.2
  refine (mem_L1 (hF := hF) (D := D)).mpr ⟨⟨_, hx⟩, ?_⟩
  have hcalc : conjHom D.norm_Q (hOf α μ) (phiC1 hF D x) =
      phiC1 hF D ⟨((hOf α μ : ↥K) : G) * (x : G) * ((hOf α μ : ↥K) : G)⁻¹, hx⟩ := by
    calc conjHom D.norm_Q (hOf α μ) (phiC1 hF D x)
        = conjHom D.norm_Q (hOf α μ) (coeC D x) *
            conjHom D.norm_Q (hOf α μ) (conjHom D.norm_Q (hT α hF) (coeC D x)) := by
          rw [show phiC1 hF D x = coeC D x * conjHom D.norm_Q (hT α hF) (coeC D x) from rfl]
          exact map_mul (conjHom D.norm_Q (hOf α μ)) _ _
      _ = conjHom D.norm_Q (hOf α μ) (coeC D x) *
            conjHom D.norm_Q (hOf α μ * hT α hF) (coeC D x) := by
          rw [conjHom_conj (D := D) (k := hOf α μ) (h := hT α hF)]
      _ = conjHom D.norm_Q (hOf α μ) (coeC D x) *
            conjHom D.norm_Q (hT α hF * hOf α μ) (coeC D x) := by
          rw [hOf_comm_hT]
      _ = conjHom D.norm_Q (hOf α μ) (coeC D x) *
            conjHom D.norm_Q (hT α hF) (conjHom D.norm_Q (hOf α μ) (coeC D x)) := by
          rw [conjHom_conj (D := D) (k := hT α hF) (h := hOf α μ)]
      _ = phiC1 hF D ⟨((hOf α μ : ↥K) : G) * (x : G) * ((hOf α μ : ↥K) : G)⁻¹, hx⟩ := by
          show _ = coeC D ⟨_, hx⟩ * conjHom D.norm_Q (hT α hF) (coeC D ⟨_, hx⟩)
          congr 2 <;> exact Subtype.ext rfl
  exact hcalc.symm

theorem tau_mem_L1 (hF : Fintype.card F = 4) (D : ModHyp Q Z K τ α β) {c : ↥Q}
    (hc : c ∈ L1 hF D) : tauHom D.tau_Q c ∈ L1 hF D := by
  obtain ⟨x, rfl⟩ := (mem_L1 (hF := hF) (D := D)).mp hc
  have hx : τ * (x : G) * τ⁻¹ ∈ Cplus α Q := conj_mem_Cplus_tau D x.2
  refine (mem_L1 (hF := hF) (D := D)).mpr ⟨⟨_, hx⟩, ?_⟩
  have hcalc : tauHom D.tau_Q (phiC1 hF D x) =
      phiC1 hF D ⟨τ * (x : G) * τ⁻¹, hx⟩ := by
    calc tauHom D.tau_Q (phiC1 hF D x)
        = tauHom D.tau_Q (coeC D x) *
            tauHom D.tau_Q (conjHom D.norm_Q (hT α hF) (coeC D x)) := by
          rw [show phiC1 hF D x = coeC D x * conjHom D.norm_Q (hT α hF) (coeC D x) from rfl]
          exact map_mul (tauHom D.tau_Q) _ _
      _ = tauHom D.tau_Q (coeC D x) *
            conjHom D.norm_Q (hT α hF) (tauHom D.tau_Q (coeC D x)) := by
          rw [tauHom_conjHom (Q := Q) (Z := Z) (K := K) (τ := τ) (α := α) (β := β)
            D (hT α hF) (coeC D x)]
      _ = phiC1 hF D ⟨τ * (x : G) * τ⁻¹, hx⟩ := by
          show _ = coeC D ⟨_, hx⟩ * conjHom D.norm_Q (hT α hF) (coeC D ⟨_, hx⟩)
          congr 2 <;> exact Subtype.ext rfl
  exact hcalc.symm

theorem conj_hOf_qq1 (hF : Fintype.card F = 4) (D : ModHyp Q Z K τ α β)
    (μ : Fˣ) (a : F) :
    conjHom D.norm_Q (hOf α μ) (qq1 hF D a) = qq1 hF D ((μ : F) * a) := by
  have hbeta : betaAdd β (conjHom D.norm_Q (hOf α μ) (qq1 hF D a)) =
      ![(μ : F) * a, 0] := by
    have h := betaAdd_conj D.equiv D.norm_Q (hOf α μ) (qq1 hF D a)
    rw [alpha_hOf, diagSL_mulVec_four hF, qq1_beta] at h
    simpa [conjHom] using h
  exact qq1_unique hF D (conj_mem_L1_hOf hF D μ (qq1_mem hF D a)) hbeta

theorem conj_tau_qq1 (hF : Fintype.card F = 4) (D : ModHyp Q Z K τ α β) {ν : F}
    (hν : ∀ q : ↥Q, betaAdd β (tauHom D.tau_Q q) = ν • betaAdd β q) (a : F) :
    tauHom D.tau_Q (qq1 hF D a) = qq1 hF D (ν * a) := by
  have hbeta : betaAdd β (tauHom D.tau_Q (qq1 hF D a)) = ![ν * a, 0] := by
    rw [hν, qq1_beta]
    ext i
    fin_cases i <;> simp [Pi.smul_apply, smul_eq_mul]
  exact qq1_unique hF D (tau_mem_L1 hF D (qq1_mem hF D a)) hbeta

theorem conj_x_qq1 (hF : Fintype.card F = 4) (D : ModHyp Q Z K τ α β) (t a : F) :
    conjHom D.norm_Q (xElt α t) (qq1 hF D a) = qq1 hF D a := by
  refine Subtype.ext ?_
  have hc := mem_Cplus_iff.mp (qq1_mem_Cplus hF D a)
  simp only [conjHom, MonoidHom.coe_mk, OneHom.coe_mk, Subtype.coe_mk]
  rw [hc.2 t]
  group

noncomputable def qq2 (hF : Fintype.card F = 4) (D : ModHyp Q Z K τ α β) (b : F) : ↥Q :=
  conjHom D.norm_Q (wElt α) (qq1 hF D b)

@[expose] noncomputable def L2 (hF : Fintype.card F = 4) (D : ModHyp Q Z K τ α β) :
    Subgroup ↥Q :=
  (L1 hF D).map (conjHom D.norm_Q (wElt α))

theorem qq2_mem (hF : Fintype.card F = 4) (D : ModHyp Q Z K τ α β) (b : F) :
    qq2 hF D b ∈ L2 hF D :=
  ⟨qq1 hF D b, qq1_mem hF D b, rfl⟩

theorem qq2_beta (hF : Fintype.card F = 4) (D : ModHyp Q Z K τ α β) (b : F) :
    betaAdd β (qq2 hF D b) = ![0, b] := by
  have h := betaAdd_conj D.equiv D.norm_Q (wElt α) (qq1 hF D b)
  rw [alpha_wElt, weylSL_mulVec, qq1_beta] at h
  simpa [qq2, conjHom] using h

theorem conjHom_w_qq2 (hF : Fintype.card F = 4) (D : ModHyp Q Z K τ α β) (b : F) :
    conjHom D.norm_Q (wElt α) (qq2 hF D b) = qq1 hF D b := by
  calc conjHom D.norm_Q (wElt α) (qq2 hF D b)
      = conjHom D.norm_Q (wElt α) (conjHom D.norm_Q (wElt α) (qq1 hF D b)) := rfl
    _ = conjHom D.norm_Q (wElt α * wElt α) (qq1 hF D b) := by
        rw [conjHom_conj (D := D) (k := wElt α) (h := wElt α)]
    _ = conjHom D.norm_Q 1 (qq1 hF D b) := by rw [wElt_mul_self]
    _ = qq1 hF D b := conjHom_one (D := D) _

theorem qq2_add (hF : Fintype.card F = 4) (D : ModHyp Q Z K τ α β) (a b : F) :
    qq2 hF D (a + b) = qq2 hF D a * qq2 hF D b := by
  have hq : qq1 hF D (a + b) = qq1 hF D a * qq1 hF D b := qq1_add hF D a b
  show conjHom D.norm_Q (wElt α) (qq1 hF D (a + b)) =
    conjHom D.norm_Q (wElt α) (qq1 hF D a) * conjHom D.norm_Q (wElt α) (qq1 hF D b)
  rw [hq, map_mul]

theorem qq2_zero (hF : Fintype.card F = 4) (D : ModHyp Q Z K τ α β) :
    qq2 hF D 0 = 1 := by
  have hq : qq1 hF D 0 = 1 := qq1_zero hF D
  show conjHom D.norm_Q (wElt α) (qq1 hF D 0) = 1
  rw [hq, map_one]

theorem conj_hOf_qq2 (hF : Fintype.card F = 4) (D : ModHyp Q Z K τ α β)
    (μ : Fˣ) (b : F) :
    conjHom D.norm_Q (hOf α μ) (qq2 hF D b) = qq2 hF D (((μ⁻¹ : Fˣ) : F) * b) := by
  have hw : hOf α μ * wElt α = wElt α * (hOf α μ) ^ 2 := by
    calc hOf α μ * wElt α = (hOf α μ * wElt α * (hOf α μ)⁻¹) * hOf α μ := by group
      _ = (wElt α * hOf α μ) * hOf α μ := by rw [conj_hOf_w α hF μ]
      _ = wElt α * (hOf α μ * hOf α μ) := by group
      _ = wElt α * (hOf α μ) ^ 2 := by rw [pow_two]
  have hsq : conjHom D.norm_Q ((hOf α μ) ^ 2) (qq1 hF D b) =
      qq1 hF D (((μ : F) ^ 2) * b) := by
    rw [pow_two]
    rw [conjHom_mul (D := D) (k₁ := hOf α μ) (k₂ := hOf α μ)]
    rw [conj_hOf_qq1 (D := D) (μ := μ), conj_hOf_qq1 (D := D) (μ := μ)]
    congr 1
    ring
  calc conjHom D.norm_Q (hOf α μ) (qq2 hF D b)
      = conjHom D.norm_Q (hOf α μ) (conjHom D.norm_Q (wElt α) (qq1 hF D b)) := rfl
    _ = conjHom D.norm_Q (hOf α μ * wElt α) (qq1 hF D b) := by
        rw [conjHom_conj (D := D) (k := hOf α μ) (h := wElt α)]
    _ = conjHom D.norm_Q (wElt α * (hOf α μ) ^ 2) (qq1 hF D b) := by rw [hw]
    _ = conjHom D.norm_Q (wElt α) (conjHom D.norm_Q ((hOf α μ) ^ 2) (qq1 hF D b)) := by
        rw [conjHom_conj (D := D) (k := wElt α) (h := (hOf α μ) ^ 2)]
    _ = conjHom D.norm_Q (wElt α) (qq1 hF D (((μ : F) ^ 2) * b)) := by rw [hsq]
    _ = qq2 hF D (((μ : F) ^ 2) * b) := rfl
    _ = qq2 hF D (((μ⁻¹ : Fˣ) : F) * b) := by rw [units_inv_eq_sq hF]

theorem conj_tau_qq2 (hF : Fintype.card F = 4) (D : ModHyp Q Z K τ α β) {ν : F}
    (hν : ∀ q : ↥Q, betaAdd β (tauHom D.tau_Q q) = ν • betaAdd β q) (b : F) :
    tauHom D.tau_Q (qq2 hF D b) = qq2 hF D (ν * b) := by
  calc tauHom D.tau_Q (qq2 hF D b)
      = tauHom D.tau_Q (conjHom D.norm_Q (wElt α) (qq1 hF D b)) := rfl
    _ = conjHom D.norm_Q (wElt α) (tauHom D.tau_Q (qq1 hF D b)) :=
        tauHom_conjHom (Q := Q) (Z := Z) (K := K) (τ := τ) (α := α) (β := β)
          D (wElt α) (qq1 hF D b)
    _ = conjHom D.norm_Q (wElt α) (qq1 hF D (ν * b)) := by rw [conj_tau_qq1 hF D hν]
    _ = qq2 hF D (ν * b) := rfl

theorem conj_y_qq2 (hF : Fintype.card F = 4) (D : ModHyp Q Z K τ α β) (t b : F) :
    conjHom D.norm_Q (yElt α t) (qq2 hF D b) = qq2 hF D b := by
  have hw : (wElt α)⁻¹ = wElt α := inv_eq_of_mul_eq_one_right (wElt_mul_self α)
  calc conjHom D.norm_Q (yElt α t) (qq2 hF D b)
      = conjHom D.norm_Q (wElt α * xElt α t * (wElt α)⁻¹)
          (conjHom D.norm_Q (wElt α) (qq1 hF D b)) := by
        rw [← wElt_conj_xElt]
        rfl
    _ = conjHom D.norm_Q ((wElt α * xElt α t * (wElt α)⁻¹) * wElt α) (qq1 hF D b) := by
        rw [conjHom_conj (D := D) (k := wElt α * xElt α t * (wElt α)⁻¹) (h := wElt α)]
    _ = conjHom D.norm_Q (wElt α * xElt α t) (qq1 hF D b) := by
        have harg : (wElt α * xElt α t * (wElt α)⁻¹) * wElt α = wElt α * xElt α t := by
          rw [hw]
          calc wElt α * xElt α t * wElt α * wElt α
              = (wElt α * xElt α t) * (wElt α * wElt α) := by group
            _ = wElt α * xElt α t := by rw [wElt_mul_self, mul_one]
        rw [harg]
    _ = conjHom D.norm_Q (wElt α) (conjHom D.norm_Q (xElt α t) (qq1 hF D b)) := by
        rw [conjHom_conj (D := D) (k := wElt α) (h := xElt α t)]
    _ = conjHom D.norm_Q (wElt α) (qq1 hF D b) := by rw [conj_x_qq1]
    _ = qq2 hF D b := rfl

theorem L2_beta_line (hF : Fintype.card F = 4) (D : ModHyp Q Z K τ α β) {c : ↥Q}
    (hc : c ∈ L2 hF D) : betaAdd β c = ![0, betaAdd β c 1] := by
  obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.mp hc
  have h := betaAdd_conj D.equiv D.norm_Q (wElt α) q
  rw [alpha_wElt, weylSL_mulVec, Cplus_beta_eq (α := α) (β := β) D.equiv D.norm_Q
    (L1_le_Cplus hF D hq)] at h
  have h' : betaAdd β (conjHom D.norm_Q (wElt α) q) =
      ![![betaAdd β q 0, 0] 1, ![betaAdd β q 0, 0] 0] := by
    simpa [conjHom] using h
  rw [h']
  ext i
  fin_cases i <;> simp

@[expose] noncomputable def zz (hF : Fintype.card F = 4) (D : ModHyp Q Z K τ α β)
    (t b : F) : ↥Q :=
  conjHom D.norm_Q (xElt α t) (qq2 hF D b) * (qq1 hF D (t * b) * qq2 hF D b)⁻¹

theorem zz_mem_Z (hF : Fintype.card F = 4) (D : ModHyp Q Z K τ α β) (t b : F) :
    ((zz hF D t b : ↥Q) : G) ∈ Z := by
  refine (betaAdd_eq_zero_iff D.ker (zz hF D t b)).mp ?_
  have h1 : betaAdd β (conjHom D.norm_Q (xElt α t) (qq2 hF D b)) = ![t * b, b] := by
    have h := betaAdd_conj D.equiv D.norm_Q (xElt α t) (qq2 hF D b)
    rw [alpha_xElt, unipotent_mulVec, qq2_beta] at h
    simpa [conjHom] using h
  show betaAdd β (conjHom D.norm_Q (xElt α t) (qq2 hF D b) *
    (qq1 hF D (t * b) * qq2 hF D b)⁻¹) = 0
  rw [betaAdd_mul, betaAdd_inv, betaAdd_mul, h1, qq1_beta, qq2_beta]
  ext i
  fin_cases i <;> simp

theorem zz_add_b (hF : Fintype.card F = 4) (D : ModHyp Q Z K τ α β) (t b c : F) :
    zz hF D t (b + c) = zz hF D t b * zz hF D t c := by
  haveI : IsMulCommutative ↥Q := D.elem.1
  have h2 : conjHom D.norm_Q (xElt α t) (qq2 hF D (b + c)) =
      conjHom D.norm_Q (xElt α t) (qq2 hF D b) *
        conjHom D.norm_Q (xElt α t) (qq2 hF D c) := by
    rw [qq2_add, map_mul]
  show conjHom D.norm_Q (xElt α t) (qq2 hF D (b + c)) *
      (qq1 hF D (t * (b + c)) * qq2 hF D (b + c))⁻¹ =
    (conjHom D.norm_Q (xElt α t) (qq2 hF D b) *
      (qq1 hF D (t * b) * qq2 hF D b)⁻¹) *
    (conjHom D.norm_Q (xElt α t) (qq2 hF D c) *
      (qq1 hF D (t * c) * qq2 hF D c)⁻¹)
  rw [h2, mul_add, qq1_add, qq2_add]
  simp only [mul_inv_rev]
  ac_rfl

theorem zz_zero_t (hF : Fintype.card F = 4) (D : ModHyp Q Z K τ α β) (b : F) :
    zz hF D 0 b = 1 := by
  show conjHom D.norm_Q (xElt α 0) (qq2 hF D b) *
    (qq1 hF D (0 * b) * qq2 hF D b)⁻¹ = 1
  rw [zero_mul, qq1_zero]
  have hx0 : xElt α 0 = 1 := by
    apply α.injective
    rw [alpha_xElt, map_one]
    exact CFSG.SL2MinimalFaithful.unipotent_zero
  rw [hx0, conjHom_one (D := D) (q := qq2 hF D b)]
  simp

theorem zz_zero_b (hF : Fintype.card F = 4) (D : ModHyp Q Z K τ α β) (t : F) :
    zz hF D t 0 = 1 := by
  show conjHom D.norm_Q (xElt α t) (qq2 hF D 0) * (qq1 hF D (t * 0) * qq2 hF D 0)⁻¹ = 1
  rw [mul_zero, qq1_zero, qq2_zero]
  simp

theorem hOf_mul_xElt (hF : Fintype.card F = 4) (μ : Fˣ) (t : F) :
    hOf α μ * xElt α t = xElt α ((μ : F) ^ 2 * t) * hOf α μ := by
  calc hOf α μ * xElt α t =
      (hOf α μ * xElt α t * (hOf α μ)⁻¹) * hOf α μ := by group
    _ = xElt α ((μ : F) ^ 2 * t) * hOf α μ := by rw [conj_hOf_x α μ]

theorem zz_scale (hF : Fintype.card F = 4) (D : ModHyp Q Z K τ α β) (μ : Fˣ) (t b : F) :
    zz hF D ((μ : F) ^ 2 * t) ((μ : F)⁻¹ * b) = zz hF D t b := by
  have hx : hOf α μ * xElt α t = xElt α ((μ : F) ^ 2 * t) * hOf α μ :=
    hOf_mul_xElt hF μ t
  have hconj : conjHom D.norm_Q (hOf α μ) (zz hF D t b) =
      zz hF D ((μ : F) ^ 2 * t) ((μ : F)⁻¹ * b) := by
    show conjHom D.norm_Q (hOf α μ)
          (conjHom D.norm_Q (xElt α t) (qq2 hF D b) *
            (qq1 hF D (t * b) * qq2 hF D b)⁻¹) =
      conjHom D.norm_Q (xElt α ((μ : F) ^ 2 * t)) (qq2 hF D ((μ : F)⁻¹ * b)) *
        (qq1 hF D (((μ : F) ^ 2 * t) * ((μ : F)⁻¹ * b)) *
          qq2 hF D ((μ : F)⁻¹ * b))⁻¹
    rw [map_mul, map_inv]
    rw [conjHom_conj (D := D) (k := hOf α μ) (h := xElt α t), hx]
    rw [← conjHom_conj (D := D) (k := xElt α ((μ : F) ^ 2 * t)) (h := hOf α μ)]
    rw [conj_hOf_qq2 hF D μ]
    rw [map_mul, conj_hOf_qq1 hF D μ, conj_hOf_qq2 hF D μ]
    simp only [Units.val_inv_eq_inv_val]
    congr 2
    field_simp
  rw [← hconj]
  exact conjHom_eq_self_of_mem_Z D hF (zz_mem_Z hF D t b) (hOf α μ)

theorem zz_tau (hF : Fintype.card F = 4) (D : ModHyp Q Z K τ α β) {ν : F}
    (hν : ∀ q : ↥Q, betaAdd β (tauHom D.tau_Q q) = ν • betaAdd β q) (t b : F) :
    tauHom D.tau_Q (zz hF D t b) = zz hF D t (ν * b) := by
  have hqq : tauHom D.tau_Q (qq2 hF D b) = qq2 hF D (ν * b) := conj_tau_qq2 hF D hν b
  have hA : tauHom D.tau_Q (conjHom D.norm_Q (xElt α t) (qq2 hF D b)) =
      conjHom D.norm_Q (xElt α t) (qq2 hF D (ν * b)) := by
    rw [tauHom_conjHom (Q := Q) (Z := Z) (K := K) (τ := τ) (α := α) (β := β)
      D (xElt α t) (qq2 hF D b), hqq]
  have hB : tauHom D.tau_Q (qq1 hF D (t * b) * qq2 hF D b) =
      qq1 hF D (t * (ν * b)) * qq2 hF D (ν * b) := by
    rw [map_mul, conj_tau_qq1 hF D hν, hqq]
    congr 2
    ring
  calc tauHom D.tau_Q (zz hF D t b)
      = tauHom D.tau_Q (conjHom D.norm_Q (xElt α t) (qq2 hF D b) *
          (qq1 hF D (t * b) * qq2 hF D b)⁻¹) := rfl
    _ = tauHom D.tau_Q (conjHom D.norm_Q (xElt α t) (qq2 hF D b)) *
          (tauHom D.tau_Q (qq1 hF D (t * b) * qq2 hF D b))⁻¹ := by
        rw [map_mul, map_inv]
    _ = conjHom D.norm_Q (xElt α t) (qq2 hF D (ν * b)) *
          (qq1 hF D (t * (ν * b)) * qq2 hF D (ν * b))⁻¹ := by
        rw [hA, hB]
    _ = zz hF D t (ν * b) := rfl

@[expose] noncomputable def zeta (hF : Fintype.card F = 4) (D : ModHyp Q Z K τ α β)
    (s : F) : ↥Q :=
  zz hF D 1 (s * s)

theorem zeta_mem_Z (hF : Fintype.card F = 4) (D : ModHyp Q Z K τ α β) (s : F) :
    ((zeta hF D s : ↥Q) : G) ∈ Z :=
  zz_mem_Z hF D 1 (s * s)

theorem zeta_add (hF : Fintype.card F = 4) (D : ModHyp Q Z K τ α β) (s t : F) :
    zeta hF D (s + t) = zeta hF D s * zeta hF D t := by
  have hst : (s + t) * (s + t) = s * s + t * t := by
    have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
    linear_combination (s * t) * h2
  rw [zeta, hst, zz_add_b, zeta, zeta]

theorem zeta_zero (hF : Fintype.card F = 4) (D : ModHyp Q Z K τ α β) :
    zeta hF D 0 = 1 := by
  rw [zeta, mul_zero, zz_zero_b]

theorem zz_eq_zeta (hF : Fintype.card F = 4) (D : ModHyp Q Z K τ α β) (t b : F) :
    zz hF D t b = zeta hF D (t * b * b) := by
  by_cases ht : t = 0
  · subst ht
    rw [zz_zero_t, zeta]
    simp [zz_zero_b]
  · let μ : Fˣ := Units.mk0 (t * t) (mul_ne_zero ht ht)
    have hμ : (μ : F) = t * t := rfl
    have hμ2 : ((μ : F) ^ 2) = t := by
      rw [hμ]
      calc (t * t) ^ 2 = t ^ 4 := by ring
        _ = t := pow_four_eq_self hF t
    have hμinv : (μ : F)⁻¹ * ((μ : F) * b) = b := by
      have h0 : (μ : F) ≠ 0 := Units.ne_zero μ
      rw [← mul_assoc, inv_mul_cancel₀ h0, one_mul]
    have h := zz_scale hF D μ 1 ((μ : F) * b)
    rw [mul_one, hμ2, hμinv, hμ] at h
    rw [h, zeta]
    congr 1
    calc (t * t) * b = t ^ 2 * b := by ring
      _ = t ^ 2 * b ^ 4 := by rw [pow_four_eq_self hF b]
      _ = (t * b * b) * (t * b * b) := by ring

theorem zeta_tau (hF : Fintype.card F = 4) (D : ModHyp Q Z K τ α β) {ν : F}
    (hν : ∀ q : ↥Q, betaAdd β (tauHom D.tau_Q q) = ν • betaAdd β q)
    (hν3 : ν ^ 3 = 1) (s : F) :
    tauHom D.tau_Q (zeta hF D s) = zeta hF D (ν ^ 2 * s) := by
  rw [zeta, zz_tau hF D hν, zeta]
  congr 1
  have hν4 : ν ^ 4 = ν := by
    rw [show ν ^ 4 = ν ^ 3 * ν by ring, hν3, one_mul]
  calc ν * (s * s) = ν ^ 4 * s ^ 2 := by
        rw [hν4]
        ring
    _ = (ν ^ 2 * s) * (ν ^ 2 * s) := by ring


theorem units_trichotomy (hF : Fintype.card F = 4) {ν : F} (hν3 : ν ^ 3 = 1) (hν1 : ν ≠ 1)
    {x : F} (hx : x ≠ 0) : x = 1 ∨ x = ν ∨ x = ν ^ 2 := by
  have hν0 : ν ≠ 0 := by
    rintro rfl
    norm_num at hν3
  let νu : Fˣ := Units.mk0 ν hν0
  have hνu : (νu : F) = ν := Units.val_mk0 hν0
  have hνu3 : νu ^ 3 = 1 := by
    apply Units.ext
    simpa [hνu] using hν3
  have hνu1 : νu ≠ 1 := by
    intro h
    exact hν1 (by rw [← hνu]; exact congrArg Units.val h)
  have hνu2ne1 : νu ^ 2 ≠ 1 := by
    intro h
    have h1 : (1 : Fˣ) = νu := by
      calc (1 : Fˣ) = νu ^ 3 := hνu3.symm
        _ = νu ^ 2 * νu := by
          rw [show (3 : ℕ) = 2 + 1 by norm_num, pow_succ]
        _ = 1 * νu := by rw [h]
        _ = νu := one_mul _
    exact hνu1 h1.symm
  have hνu2neνu : νu ^ 2 ≠ νu := by
    intro h
    have h1 : νu = 1 := by
      calc νu = νu ^ 2 * νu⁻¹ := by group
        _ = νu * νu⁻¹ := by rw [h]
        _ = 1 := mul_inv_cancel νu
    exact hνu1 h1
  have hcard : ({1, νu, νu ^ 2} : Finset Fˣ).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem]
    · simp
    · simp only [Finset.mem_singleton]
      exact fun h => hνu2neνu h.symm
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨fun h => hνu1 h.symm, fun h => hνu2ne1 h.symm⟩
  have huniv : ({1, νu, νu ^ 2} : Finset Fˣ) = Finset.univ :=
    Finset.eq_univ_of_card _ (by rw [hcard, card_units_of_card_four hF])
  have hmem : (Units.mk0 x hx : Fˣ) ∈ ({1, νu, νu ^ 2} : Finset Fˣ) := by
    rw [huniv]
    exact Finset.mem_univ _
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with h | h | h
  · exact Or.inl (by simpa using congrArg Units.val h)
  · exact Or.inr (Or.inl (by simpa [hνu] using congrArg Units.val h))
  · exact Or.inr (Or.inr (by simpa [hνu] using congrArg Units.val h))

theorem zeta_ker_invariant (hF : Fintype.card F = 4) (D : ModHyp Q Z K τ α β) {ν : F}
    (hν : ∀ q : ↥Q, betaAdd β (tauHom D.tau_Q q) = ν • betaAdd β q)
    (hν3 : ν ^ 3 = 1) {s : F} (hs : zeta hF D s = 1) :
    zeta hF D (ν ^ 2 * s) = 1 := by
  rw [← zeta_tau hF D hν hν3 s, hs]
  exact map_one _

theorem zeta_either (hF : Fintype.card F = 4) (D : ModHyp Q Z K τ α β) {ν : F}
    (hν : ∀ q : ↥Q, betaAdd β (tauHom D.tau_Q q) = ν • betaAdd β q)
    (hν3 : ν ^ 3 = 1) (hν1 : ν ≠ 1) :
    (∀ s, zeta hF D s = 1) ∨ (∀ s, zeta hF D s = 1 → s = 0) := by
  classical
  have hν2 : ν ^ 2 * ν = 1 := by
    rw [show ν ^ 2 * ν = ν ^ 3 by ring, hν3]
  have hν2sq : ν ^ 2 * ν ^ 2 = ν := by
    rw [show ν ^ 2 * ν ^ 2 = ν ^ 4 by ring]
    calc ν ^ 4 = ν ^ 3 * ν := by ring
      _ = ν := by rw [hν3, one_mul]
  by_cases h : ∃ s, s ≠ 0 ∧ zeta hF D s = 1
  · left
    obtain ⟨s, hs0, hzs⟩ := h
    have h1 : zeta hF D 1 = 1 := by
      rcases units_trichotomy hF hν3 hν1 hs0 with hs1 | hsν | hsν2
      · rwa [hs1] at hzs
      · rw [hsν] at hzs
        have hstep := zeta_ker_invariant hF D hν hν3 hzs
        rwa [hν2] at hstep
      · rw [hsν2] at hzs
        have hstep : zeta hF D ν = 1 := by
          have h2 := zeta_ker_invariant hF D hν hν3 hzs
          rwa [hν2sq] at h2
        have h3 := zeta_ker_invariant hF D hν hν3 hstep
        rwa [hν2] at h3
    have hν2z : zeta hF D (ν ^ 2) = 1 := by
      have := zeta_ker_invariant hF D hν hν3 h1
      rwa [show ν ^ 2 * 1 = ν ^ 2 by rw [mul_one]] at this
    have hνz : zeta hF D ν = 1 := by
      have := zeta_ker_invariant hF D hν hν3 hν2z
      rwa [hν2sq] at this
    intro t
    by_cases ht : t = 0
    · rw [ht]
      exact zeta_zero hF D
    · rcases units_trichotomy hF hν3 hν1 ht with ht1 | htν | htν2
      · rwa [ht1]
      · rwa [htν]
      · rwa [htν2]
  · right
    intro s hzs
    by_contra hs0
    exact h ⟨s, hs0, hzs⟩

theorem xElt_mul_self (α : ↥K ≃* SL₂ F) (t : F) : xElt α t * xElt α t = 1 := by
  apply α.injective
  rw [map_mul, map_one, alpha_xElt]
  rw [← CFSG.SL2MinimalFaithful.unipotent_add, CharTwo.add_self_eq_zero,
    CFSG.SL2MinimalFaithful.unipotent_zero]

theorem yElt_mul_self (α : ↥K ≃* SL₂ F) (t : F) : yElt α t * yElt α t = 1 := by
  apply α.injective
  rw [map_mul, map_one, alpha_yElt]
  rw [← lowerUni_add, CharTwo.add_self_eq_zero, lowerUni_zero]

theorem closure_xElt_yElt_eq_top (α : ↥K ≃* SL₂ F) :
    Subgroup.closure (Set.range (xElt α) ∪ Set.range (yElt α)) = ⊤ := by
  have hmap : (Subgroup.closure (Set.range (xElt α) ∪ Set.range (yElt α))).map
      α.toMonoidHom = ⊤ := by
    rw [MonoidHom.map_closure]
    have himg : α.toMonoidHom '' (Set.range (xElt α) ∪ Set.range (yElt α)) =
        Set.range (CFSG.SL2MinimalFaithful.unipotent (F := F)) ∪ Set.range (lowerUni (K := F)) := by
      ext M
      simp only [Set.mem_image, Set.mem_union, Set.mem_range, MonoidHom.coe_mk, OneHom.coe_mk]
      constructor
      · rintro ⟨k, (⟨t, rfl⟩ | ⟨t, rfl⟩), rfl⟩
        · exact Or.inl ⟨t, (alpha_xElt α t).symm⟩
        · exact Or.inr ⟨t, (alpha_yElt α t).symm⟩
      · rintro (⟨t, rfl⟩ | ⟨t, rfl⟩)
        · exact ⟨xElt α t, Or.inl ⟨t, rfl⟩, alpha_xElt α t⟩
        · exact ⟨yElt α t, Or.inr ⟨t, rfl⟩, alpha_yElt α t⟩
    rw [himg, closure_unipotent_lowerUni]
  rw [eq_top_iff]
  intro k _
  have hk : α k ∈ (Subgroup.closure (Set.range (xElt α) ∪ Set.range (yElt α))).map
      α.toMonoidHom := by
    rw [hmap]
    trivial
  obtain ⟨s, hs, hsk⟩ := Subgroup.mem_map.mp hk
  have hsk' : s = k := α.injective hsk
  rwa [hsk'] at hs

@[expose] noncomputable def wHom (hF : Fintype.card F = 4) (D : ModHyp Q Z K τ α β) :
    Multiplicative (F × F) →* ↥Q where
  toFun x := qq1 hF D x.toAdd.1 * qq2 hF D x.toAdd.2
  map_one' := by
    simp [qq1_zero, qq2_zero]
  map_mul' x y := by
    haveI : IsMulCommutative ↥Q := D.elem.1
    show qq1 hF D (x.toAdd + y.toAdd).1 * qq2 hF D (x.toAdd + y.toAdd).2 =
      (qq1 hF D x.toAdd.1 * qq2 hF D x.toAdd.2) *
        (qq1 hF D y.toAdd.1 * qq2 hF D y.toAdd.2)
    simp only [Prod.fst_add, Prod.snd_add, qq1_add, qq2_add]
    ac_rfl

@[expose] noncomputable def W0 (hF : Fintype.card F = 4) (D : ModHyp Q Z K τ α β) :
    Subgroup ↥Q :=
  (wHom hF D).range

theorem mem_W0 {hF : Fintype.card F = 4} {D : ModHyp Q Z K τ α β} {q : ↥Q} :
    q ∈ W0 hF D ↔ ∃ a b : F, q = qq1 hF D a * qq2 hF D b := by
  rw [W0, MonoidHom.mem_range]
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x.toAdd.1, x.toAdd.2, rfl⟩
  · rintro ⟨a, b, rfl⟩
    exact ⟨Multiplicative.ofAdd (a, b), rfl⟩

theorem wHom_injective (hF : Fintype.card F = 4) (D : ModHyp Q Z K τ α β) :
    Function.Injective (wHom hF D) := by
  intro x y hxy
  have hxy' : qq1 hF D x.toAdd.1 * qq2 hF D x.toAdd.2 =
      qq1 hF D y.toAdd.1 * qq2 hF D y.toAdd.2 := hxy
  have hb : betaAdd β (qq1 hF D x.toAdd.1 * qq2 hF D x.toAdd.2) =
      betaAdd β (qq1 hF D y.toAdd.1 * qq2 hF D y.toAdd.2) := by rw [hxy']
  rw [betaAdd_mul, betaAdd_mul, qq1_beta, qq2_beta, qq1_beta, qq2_beta] at hb
  have h1 := congrFun hb 0
  have h2 := congrFun hb 1
  simp at h1 h2
  apply Multiplicative.toAdd.injective
  exact Prod.ext h1 h2

theorem W0_inf_Z (hF : Fintype.card F = 4) (D : ModHyp Q Z K τ α β) :
    W0 hF D ⊓ Z.subgroupOf Q = ⊥ := by
  refine le_antisymm ?_ bot_le
  intro q hq
  rw [Subgroup.mem_bot]
  obtain ⟨hqW, hqZ⟩ := Subgroup.mem_inf.mp hq
  obtain ⟨a, b, rfl⟩ := (mem_W0 (hF := hF) (D := D)).mp hqW
  have hz : betaAdd β (qq1 hF D a * qq2 hF D b) = 0 :=
    (betaAdd_eq_zero_iff D.ker _).mpr (Subgroup.mem_subgroupOf.mp hqZ)
  rw [betaAdd_mul, qq1_beta, qq2_beta] at hz
  have ha := congrFun hz 0
  have hb := congrFun hz 1
  simp at ha hb
  rw [ha, hb, qq1_zero, qq2_zero, one_mul]

@[expose] noncomputable def Wsub (hF : Fintype.card F = 4) (D : ModHyp Q Z K τ α β) :
    Subgroup G :=
  (W0 hF D).map Q.subtype

theorem Wsub_le_Q (hF : Fintype.card F = 4) (D : ModHyp Q Z K τ α β) :
    Wsub hF D ≤ Q :=
  Subgroup.map_subtype_le _

theorem Wsub_inf_Z (hF : Fintype.card F = 4) (D : ModHyp Q Z K τ α β) :
    Wsub hF D ⊓ Z = ⊥ := by
  refine le_antisymm ?_ bot_le
  intro x hx
  obtain ⟨hxW, hxZ⟩ := Subgroup.mem_inf.mp hx
  obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.mp hxW
  have hqZ : q ∈ Z.subgroupOf Q := Subgroup.mem_subgroupOf.mpr hxZ
  have hmem : q ∈ W0 hF D ⊓ Z.subgroupOf Q := ⟨hq, hqZ⟩
  rw [W0_inf_Z hF D, Subgroup.mem_bot] at hmem
  rw [hmem]
  exact Subgroup.one_mem _

theorem exists_decomp (hF : Fintype.card F = 4) (D : ModHyp Q Z K τ α β) (q : ↥Q) :
    ∃ a b : F, ∃ z ∈ Z.subgroupOf Q, q = qq1 hF D a * qq2 hF D b * z := by
  let a : F := betaAdd β q 0
  let b : F := betaAdd β q 1
  let z : ↥Q := q * (qq1 hF D a * qq2 hF D b)⁻¹
  have hq : betaAdd β q = ![a, b] := by
    ext i
    fin_cases i <;> rfl
  have hz : z ∈ Z.subgroupOf Q := by
    rw [Subgroup.mem_subgroupOf]
    apply (betaAdd_eq_zero_iff D.ker z).mp
    show betaAdd β (q * (qq1 hF D a * qq2 hF D b)⁻¹) = 0
    rw [betaAdd_mul, betaAdd_inv, betaAdd_mul, qq1_beta, qq2_beta, hq]
    ext i
    fin_cases i <;> simp
  refine ⟨a, b, z, hz, ?_⟩
  show q = qq1 hF D a * qq2 hF D b * (q * (qq1 hF D a * qq2 hF D b)⁻¹)
  haveI : IsMulCommutative ↥Q := D.elem.1
  calc q = q * ((qq1 hF D a * qq2 hF D b) * (qq1 hF D a * qq2 hF D b)⁻¹) := by
        rw [mul_inv_cancel, mul_one]
    _ = qq1 hF D a * qq2 hF D b * (q * (qq1 hF D a * qq2 hF D b)⁻¹) := by ac_rfl

theorem Wsub_sup_Z (hF : Fintype.card F = 4) (D : ModHyp Q Z K τ α β) :
    Wsub hF D ⊔ Z = Q := by
  refine le_antisymm (sup_le (Wsub_le_Q hF D) D.le_Z) ?_
  intro q hq
  obtain ⟨a, b, z, hz, hq'⟩ := exists_decomp hF D ⟨q, hq⟩
  have hw : ((qq1 hF D a * qq2 hF D b : ↥Q) : G) ∈ Wsub hF D :=
    ⟨qq1 hF D a * qq2 hF D b, (mem_W0 (hF := hF) (D := D)).mpr ⟨a, b, rfl⟩, rfl⟩
  have hzG : (z : G) ∈ Z := Subgroup.mem_subgroupOf.mp hz
  have hprod : ((qq1 hF D a * qq2 hF D b : ↥Q) : G) * (z : G) = q := by
    rw [← Subgroup.coe_mul]
    exact (congrArg Subtype.val hq').symm
  rw [← hprod]
  exact Subgroup.mul_mem_sup hw hzG


theorem conj_x_qq2 (hF : Fintype.card F = 4) (D : ModHyp Q Z K τ α β) (t b : F) :
    conjHom D.norm_Q (xElt α t) (qq2 hF D b) =
      qq1 hF D (t * b) * qq2 hF D b * zz hF D t b := by
  haveI : IsMulCommutative ↥Q := D.elem.1
  calc conjHom D.norm_Q (xElt α t) (qq2 hF D b)
      = (conjHom D.norm_Q (xElt α t) (qq2 hF D b) *
          (qq1 hF D (t * b) * qq2 hF D b)⁻¹) *
          (qq1 hF D (t * b) * qq2 hF D b) := by group
    _ = zz hF D t b * (qq1 hF D (t * b) * qq2 hF D b) := rfl
    _ = qq1 hF D (t * b) * qq2 hF D b * zz hF D t b := by ac_rfl

theorem conj_y_qq1 (hF : Fintype.card F = 4) (D : ModHyp Q Z K τ α β) (t a : F) :
    conjHom D.norm_Q (yElt α t) (qq1 hF D a) =
      qq1 hF D a * qq2 hF D (t * a) * zz hF D t a := by
  have hw : (wElt α)⁻¹ = wElt α := inv_eq_of_mul_eq_one_right (wElt_mul_self α)
  haveI : IsMulCommutative ↥Q := D.elem.1
  calc conjHom D.norm_Q (yElt α t) (qq1 hF D a)
      = conjHom D.norm_Q (wElt α * xElt α t * (wElt α)⁻¹) (qq1 hF D a) := by
        rw [wElt_conj_xElt]
    _ = conjHom D.norm_Q (wElt α * xElt α t * wElt α) (qq1 hF D a) := by rw [hw]
    _ = conjHom D.norm_Q (wElt α) (conjHom D.norm_Q (xElt α t)
          (conjHom D.norm_Q (wElt α) (qq1 hF D a))) := by
        rw [← conjHom_conj (D := D) (k := wElt α * xElt α t) (h := wElt α)]
        rw [← conjHom_conj (D := D) (k := wElt α) (h := xElt α t)]
    _ = conjHom D.norm_Q (wElt α) (conjHom D.norm_Q (xElt α t) (qq2 hF D a)) := by
        rw [show conjHom D.norm_Q (wElt α) (qq1 hF D a) = qq2 hF D a from rfl]
    _ = conjHom D.norm_Q (wElt α)
          (qq1 hF D (t * a) * qq2 hF D a * zz hF D t a) := by rw [conj_x_qq2]
    _ = qq2 hF D (t * a) * qq1 hF D a * zz hF D t a := by
        rw [map_mul, map_mul, conjHom_w_qq2,
          conjHom_eq_self_of_mem_Z D hF (zz_mem_Z hF D t a) (wElt α)]
        rfl
    _ = qq1 hF D a * qq2 hF D (t * a) * zz hF D t a := by ac_rfl

theorem conj_x_mem_W0 (hF : Fintype.card F = 4) (D : ModHyp Q Z K τ α β)
    (hall : ∀ s, zeta hF D s = 1) (t : F) {q : ↥Q} (hq : q ∈ W0 hF D) :
    conjHom D.norm_Q (xElt α t) q ∈ W0 hF D := by
  haveI : IsMulCommutative ↥Q := D.elem.1
  obtain ⟨a, b, rfl⟩ := (mem_W0 (hF := hF) (D := D)).mp hq
  rw [map_mul, conj_x_qq1, conj_x_qq2]
  rw [show zz hF D t b = 1 by rw [zz_eq_zeta, hall]]
  refine (mem_W0 (hF := hF) (D := D)).mpr ⟨a + t * b, b, ?_⟩
  rw [qq1_add]
  ac_rfl

theorem conj_y_mem_W0 (hF : Fintype.card F = 4) (D : ModHyp Q Z K τ α β)
    (hall : ∀ s, zeta hF D s = 1) (t : F) {q : ↥Q} (hq : q ∈ W0 hF D) :
    conjHom D.norm_Q (yElt α t) q ∈ W0 hF D := by
  haveI : IsMulCommutative ↥Q := D.elem.1
  obtain ⟨a, b, rfl⟩ := (mem_W0 (hF := hF) (D := D)).mp hq
  rw [map_mul, conj_y_qq1, conj_y_qq2]
  rw [show zz hF D t a = 1 by rw [zz_eq_zeta, hall]]
  refine (mem_W0 (hF := hF) (D := D)).mpr ⟨a, b + t * a, ?_⟩
  rw [qq2_add]
  ac_rfl

theorem mem_normalizer_Wsub_of_W0 (hF : Fintype.card F = 4) (D : ModHyp Q Z K τ α β)
    (k : ↥K) (hk2 : k * k = 1)
    (hfw : ∀ q ∈ W0 hF D, conjHom D.norm_Q k q ∈ W0 hF D) :
    ((k : ↥K) : G) ∈ Subgroup.normalizer (Wsub hF D : Set G) := by
  have hkG : ((k : ↥K) : G) * ((k : ↥K) : G) = 1 := by
    simpa using congrArg Subtype.val hk2
  have hkinv : ((k : ↥K) : G)⁻¹ = ((k : ↥K) : G) :=
    inv_eq_of_mul_eq_one_right hkG
  rw [Subgroup.mem_normalizer_iff]
  intro w
  constructor
  · intro hw
    obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.mp hw
    exact Subgroup.mem_map.mpr ⟨conjHom D.norm_Q k q, hfw q hq, rfl⟩
  · intro hw
    obtain ⟨q, hq, hqval⟩ := Subgroup.mem_map.mp hw
    refine Subgroup.mem_map.mpr ⟨conjHom D.norm_Q k q, hfw q hq, ?_⟩
    show ((k : ↥K) : G) * (q : G) * ((k : ↥K) : G)⁻¹ = w
    rw [show (q : G) = ((k : ↥K) : G) * w * ((k : ↥K) : G)⁻¹ from hqval, hkinv]
    calc ((k : ↥K) : G) * (((k : ↥K) : G) * w * ((k : ↥K) : G)) * ((k : ↥K) : G)
        = (((k : ↥K) : G) * ((k : ↥K) : G)) * w *
            (((k : ↥K) : G) * ((k : ↥K) : G)) := by group
      _ = w := by rw [hkG]; group

theorem le_normalizer_Wsub (hF : Fintype.card F = 4) (D : ModHyp Q Z K τ α β)
    (hall : ∀ s, zeta hF D s = 1) :
    K ≤ Subgroup.normalizer (Wsub hF D : Set G) := by
  have hgen := closure_xElt_yElt_eq_top (α := α)
  let H : Subgroup ↥K := (Subgroup.normalizer (Wsub hF D : Set G)).comap K.subtype
  have hle : Subgroup.closure (Set.range (xElt α) ∪ Set.range (yElt α)) ≤ H := by
    rw [Subgroup.closure_le]
    rintro k (⟨t, rfl⟩ | ⟨t, rfl⟩)
    · change xElt α t ∈ (Subgroup.normalizer (Wsub hF D : Set G)).comap K.subtype
      rw [Subgroup.mem_comap]
      exact mem_normalizer_Wsub_of_W0 hF D (xElt α t) (xElt_mul_self α t)
        (fun q hq => conj_x_mem_W0 hF D hall t hq)
    · change yElt α t ∈ (Subgroup.normalizer (Wsub hF D : Set G)).comap K.subtype
      rw [Subgroup.mem_comap]
      exact mem_normalizer_Wsub_of_W0 hF D (yElt α t) (yElt_mul_self α t)
        (fun q hq => conj_y_mem_W0 hF D hall t hq)
  intro k hk
  have hk' : (⟨k, hk⟩ : ↥K) ∈ Subgroup.closure (Set.range (xElt α) ∪ Set.range (yElt α)) := by
    rw [hgen]
    trivial
  have hmem := hle hk'
  rw [Subgroup.mem_comap] at hmem
  simpa using hmem

theorem not_zeta_all_one (hF : Fintype.card F = 4) (D : ModHyp Q Z K τ α β) {ν : F}
    (hν : ∀ q : ↥Q, betaAdd β (tauHom D.tau_Q q) = ν • betaAdd β q)
    (hν3 : ν ^ 3 = 1) (hν1 : ν ≠ 1) :
    ¬ (∀ s, zeta hF D s = 1) := by
  intro hall
  have hKnorm := le_normalizer_Wsub hF D hall
  have hinv : ∀ k ∈ K, ∀ w ∈ Wsub hF D, k * w * k⁻¹ ∈ Wsub hF D := by
    intro k hk w hw
    exact (Subgroup.mem_normalizer_iff.mp (hKnorm hk) w).mp hw
  have hWeq : Wsub hF D = Q :=
    D.indec (Wsub hF D) (Wsub_le_Q hF D) hinv (Wsub_sup_Z hF D)
  have hZle : Z ≤ Wsub hF D := by
    rw [hWeq]
    exact D.le_Z
  have hbot : Z ≤ Wsub hF D ⊓ Z := fun z hz => ⟨hZle hz, hz⟩
  rw [Wsub_inf_Z hF D] at hbot
  have hZbot : Z = ⊥ := le_bot_iff.mp hbot
  have hcard : Nat.card ↥Z = 1 := by
    rw [hZbot]
    simp
  rw [D.card_Z] at hcard
  norm_num at hcard


theorem zeta_injective (hF : Fintype.card F = 4) (D : ModHyp Q Z K τ α β) {ν : F}
    (hν : ∀ q : ↥Q, betaAdd β (tauHom D.tau_Q q) = ν • betaAdd β q)
    (hν3 : ν ^ 3 = 1) (hν1 : ν ≠ 1) : Function.Injective (zeta hF D) := by
  have hinj : ∀ s, zeta hF D s = 1 → s = 0 := by
    rcases zeta_either hF D hν hν3 hν1 with hall | hinj
    · exact absurd hall (not_zeta_all_one hF D hν hν3 hν1)
    · exact hinj
  intro s t hst
  have h1 : zeta hF D (s + t) = 1 := by
    rw [zeta_add, hst, mul_self_mem_Q D.elem]
  have h2 : s + t = 0 := hinj _ h1
  have h3 : s = -t := add_eq_zero_iff_eq_neg.mp h2
  rwa [CharTwo.neg_eq] at h3

@[expose] noncomputable def zetaZ (hF : Fintype.card F = 4) (D : ModHyp Q Z K τ α β)
    (s : F) : ↥Z :=
  ⟨zeta hF D s, zeta_mem_Z hF D s⟩

theorem zetaZ_injective (hF : Fintype.card F = 4) (D : ModHyp Q Z K τ α β) {ν : F}
    (hν : ∀ q : ↥Q, betaAdd β (tauHom D.tau_Q q) = ν • betaAdd β q)
    (hν3 : ν ^ 3 = 1) (hν1 : ν ≠ 1) : Function.Injective (zetaZ hF D) := by
  intro s t h
  let toG : ↥Z → G := fun z => z.1
  have hG : toG (zetaZ hF D s) = toG (zetaZ hF D t) := congrArg toG h
  have hQ : zeta hF D s = zeta hF D t := by
    apply Subtype.ext
    show ((zeta hF D s : ↥Q) : G) = ((zeta hF D t : ↥Q) : G)
    simpa [toG, zetaZ] using hG
  exact zeta_injective hF D hν hν3 hν1 hQ

theorem zetaZ_surjective (hF : Fintype.card F = 4) (D : ModHyp Q Z K τ α β) {ν : F}
    (hν : ∀ q : ↥Q, betaAdd β (tauHom D.tau_Q q) = ν • betaAdd β q)
    (hν3 : ν ^ 3 = 1) (hν1 : ν ≠ 1) : Function.Surjective (zetaZ hF D) := by
  letI : Fintype ↥Z := Fintype.ofFinite _
  have hcardF : Fintype.card F = 4 := hF
  have hcardZ : Fintype.card ↥Z = 4 := by
    rw [← Nat.card_eq_fintype_card, D.card_Z]
  have hcard : Fintype.card F = Fintype.card ↥Z := by rw [hcardF, hcardZ]
  let e : F ≃ ↥Z := Fintype.equivOfCardEq hcard
  have hinjZ : Function.Injective (fun z : ↥Z => zetaZ hF D (e.symm z)) := by
    intro z w hzw
    have h' : e.symm z = e.symm w := zetaZ_injective hF D hν hν3 hν1 hzw
    exact e.symm.injective h'
  have hsurjZ : Function.Surjective (fun z : ↥Z => zetaZ hF D (e.symm z)) :=
    Finite.surjective_of_injective hinjZ
  intro z
  obtain ⟨w, hw⟩ := hsurjZ z
  exact ⟨e.symm w, hw⟩

theorem zeta_surj (hF : Fintype.card F = 4) (D : ModHyp Q Z K τ α β) {ν : F}
    (hν : ∀ q : ↥Q, betaAdd β (tauHom D.tau_Q q) = ν • betaAdd β q)
    (hν3 : ν ^ 3 = 1) (hν1 : ν ≠ 1) {z : ↥Q} (hz : (z : G) ∈ Z) :
    ∃ e : F, zeta hF D e = z := by
  obtain ⟨e, he⟩ := zetaZ_surjective hF D hν hν3 hν1 ⟨z, hz⟩
  let toG : ↥Z → G := fun z => z.1
  have hG : toG (zetaZ hF D e) = toG ⟨z, hz⟩ := congrArg toG he
  refine ⟨e, ?_⟩
  apply Subtype.ext
  show ((zeta hF D e : ↥Q) : G) = (z : G)
  simpa [toG, zetaZ] using hG


@[expose] noncomputable def psi (hF : Fintype.card F = 4) (D : ModHyp Q Z K τ α β) :
    Multiplicative (F × F × F) →* ↥Q where
  toFun x := qq1 hF D x.toAdd.1 * qq2 hF D x.toAdd.2.1 * zeta hF D x.toAdd.2.2
  map_one' := by
    simp [qq1_zero, qq2_zero, zeta_zero]
  map_mul' x y := by
    haveI : IsMulCommutative ↥Q := D.elem.1
    show qq1 hF D (x.toAdd + y.toAdd).1 * qq2 hF D (x.toAdd + y.toAdd).2.1 *
        zeta hF D (x.toAdd + y.toAdd).2.2 =
      (qq1 hF D x.toAdd.1 * qq2 hF D x.toAdd.2.1 * zeta hF D x.toAdd.2.2) *
        (qq1 hF D y.toAdd.1 * qq2 hF D y.toAdd.2.1 * zeta hF D y.toAdd.2.2)
    simp only [Prod.fst_add, Prod.snd_add, qq1_add, qq2_add, zeta_add]
    ac_rfl

@[expose] noncomputable def phi (hF : Fintype.card F = 4) (D : ModHyp Q Z K τ α β) :
    Multiplicative (F × F × F) →* ↥(radA2 F) where
  toFun x :=
    ⟨aElt ![x.toAdd.1, x.toAdd.2.1] (x.toAdd.2.2 + x.toAdd.1 * x.toAdd.2.1),
      aElt_mem_radA2 _ _⟩
  map_one' := by
    apply Subtype.ext
    show aElt ![0, 0] (0 + 0 * 0) = 1
    rw [show (0 + 0 * 0 : F) = 0 by ring]
    exact aElt_zero_zero
  map_mul' x y := by
    apply Subtype.ext
    show aElt ![x.toAdd.1 + y.toAdd.1, x.toAdd.2.1 + y.toAdd.2.1]
        ((x.toAdd.2.2 + y.toAdd.2.2) + (x.toAdd.1 + y.toAdd.1) *
          (x.toAdd.2.1 + y.toAdd.2.1)) =
      aElt ![x.toAdd.1, x.toAdd.2.1] (x.toAdd.2.2 + x.toAdd.1 * x.toAdd.2.1) *
        aElt ![y.toAdd.1, y.toAdd.2.1] (y.toAdd.2.2 + y.toAdd.1 * y.toAdd.2.1)
    rw [aElt_mul]
    congr 1
    · ext i
      fin_cases i <;> simp
    · simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      ring

theorem psi_injective (hF : Fintype.card F = 4) (D : ModHyp Q Z K τ α β) {ν : F}
    (hν : ∀ q : ↥Q, betaAdd β (tauHom D.tau_Q q) = ν • betaAdd β q)
    (hν3 : ν ^ 3 = 1) (hν1 : ν ≠ 1) : Function.Injective (psi hF D) := by
  intro x y hxy
  have hbx : betaAdd β (psi hF D x) = ![x.toAdd.1, x.toAdd.2.1] := by
    show betaAdd β (qq1 hF D x.toAdd.1 * qq2 hF D x.toAdd.2.1 * zeta hF D x.toAdd.2.2) = _
    rw [betaAdd_mul, betaAdd_mul, qq1_beta, qq2_beta,
      (betaAdd_eq_zero_iff D.ker _).mpr (zeta_mem_Z hF D x.toAdd.2.2)]
    ext i
    fin_cases i <;> simp
  have hby : betaAdd β (psi hF D y) = ![y.toAdd.1, y.toAdd.2.1] := by
    show betaAdd β (qq1 hF D y.toAdd.1 * qq2 hF D y.toAdd.2.1 * zeta hF D y.toAdd.2.2) = _
    rw [betaAdd_mul, betaAdd_mul, qq1_beta, qq2_beta,
      (betaAdd_eq_zero_iff D.ker _).mpr (zeta_mem_Z hF D y.toAdd.2.2)]
    ext i
    fin_cases i <;> simp
  have hb : betaAdd β (psi hF D x) = betaAdd β (psi hF D y) := by rw [hxy]
  rw [hbx, hby] at hb
  have h1 : x.toAdd.1 = y.toAdd.1 := congrFun hb 0
  have h2 : x.toAdd.2.1 = y.toAdd.2.1 := congrFun hb 1
  have hzeta : zeta hF D x.toAdd.2.2 = zeta hF D y.toAdd.2.2 := by
    have hxy' := hxy
    change qq1 hF D x.toAdd.1 * qq2 hF D x.toAdd.2.1 * zeta hF D x.toAdd.2.2 =
      qq1 hF D y.toAdd.1 * qq2 hF D y.toAdd.2.1 * zeta hF D y.toAdd.2.2 at hxy'
    rw [h1, h2] at hxy'
    have h1' : qq2 hF D y.toAdd.2.1 * zeta hF D x.toAdd.2.2 =
        qq2 hF D y.toAdd.2.1 * zeta hF D y.toAdd.2.2 := by
      simpa [mul_assoc] using hxy'
    exact mul_left_cancel h1'
  have h3 : x.toAdd.2.2 = y.toAdd.2.2 := zeta_injective hF D hν hν3 hν1 hzeta
  apply Multiplicative.toAdd.injective
  exact Prod.ext h1 (Prod.ext h2 h3)

theorem psi_surjective (hF : Fintype.card F = 4) (D : ModHyp Q Z K τ α β) {ν : F}
    (hν : ∀ q : ↥Q, betaAdd β (tauHom D.tau_Q q) = ν • betaAdd β q)
    (hν3 : ν ^ 3 = 1) (hν1 : ν ≠ 1) : Function.Surjective (psi hF D) := by
  intro q
  obtain ⟨a, b, z, hz, hq⟩ := exists_decomp hF D q
  obtain ⟨e, he⟩ := zeta_surj hF D hν hν3 hν1 hz
  refine ⟨Multiplicative.ofAdd (a, b, e), ?_⟩
  show qq1 hF D a * qq2 hF D b * zeta hF D e = q
  rw [he]
  exact hq.symm

theorem phi_injective (hF : Fintype.card F = 4) (D : ModHyp Q Z K τ α β) :
    Function.Injective (phi hF D) := by
  intro x y hxy
  have h := congrArg (fun g : ↥(radA2 F) => ((g : antiSp F))) hxy
  have h' : uElt x.toAdd.2.1 x.toAdd.1
        (x.toAdd.2.2 + x.toAdd.1 * x.toAdd.2.1) 0 =
      uElt y.toAdd.2.1 y.toAdd.1
        (y.toAdd.2.2 + y.toAdd.1 * y.toAdd.2.1) 0 := by
    simpa [phi, aElt] using h
  obtain ⟨h1, h2, h3, -⟩ := uElt_inj h'
  have he : x.toAdd.2.2 = y.toAdd.2.2 := by
    rw [h1, h2] at h3
    exact add_right_cancel h3
  apply Multiplicative.toAdd.injective
  exact Prod.ext h2 (Prod.ext h1 he)

theorem phi_surjective (hF : Fintype.card F = 4) (D : ModHyp Q Z K τ α β) :
    Function.Surjective (phi hF D) := by
  rintro ⟨g, hg⟩
  obtain ⟨v, c, rfl⟩ := mem_radA2_iff.mp hg
  refine ⟨Multiplicative.ofAdd (v 0, v 1, c + v 0 * v 1), ?_⟩
  apply Subtype.ext
  show aElt ![v 0, v 1] ((c + v 0 * v 1) + v 0 * v 1) = aElt v c
  have hvec : (![v 0, v 1] : Fin 2 → F) = v := by
    ext i
    fin_cases i <;> rfl
  rw [hvec]
  congr 1
  linear_combination (v 0 * v 1) * (CharTwo.two_eq_zero : (2 : F) = 0)


noncomputable def psiEquiv (hF : Fintype.card F = 4) (D : ModHyp Q Z K τ α β) {ν : F}
    (hν : ∀ q : ↥Q, betaAdd β (tauHom D.tau_Q q) = ν • betaAdd β q)
    (hν3 : ν ^ 3 = 1) (hν1 : ν ≠ 1) :
    Multiplicative (F × F × F) ≃* ↥Q :=
  MulEquiv.ofBijective (psi hF D) ⟨psi_injective hF D hν hν3 hν1,
    psi_surjective hF D hν hν3 hν1⟩

noncomputable def phiEquiv (hF : Fintype.card F = 4) (D : ModHyp Q Z K τ α β) :
    Multiplicative (F × F × F) ≃* ↥(radA2 F) :=
  MulEquiv.ofBijective (phi hF D) ⟨phi_injective hF D, phi_surjective hF D⟩

noncomputable def moduleIso (hF : Fintype.card F = 4) (D : ModHyp Q Z K τ α β) {ν : F}
    (hν : ∀ q : ↥Q, betaAdd β (tauHom D.tau_Q q) = ν • betaAdd β q)
    (hν3 : ν ^ 3 = 1) (hν1 : ν ≠ 1) : ↥Q ≃* ↥(radA2 F) :=
  (psiEquiv hF D hν hν3 hν1).symm.trans (phiEquiv hF D)

theorem moduleIso_psi (hF : Fintype.card F = 4) (D : ModHyp Q Z K τ α β) {ν : F}
    (hν : ∀ q : ↥Q, betaAdd β (tauHom D.tau_Q q) = ν • betaAdd β q)
    (hν3 : ν ^ 3 = 1) (hν1 : ν ≠ 1) (a b e : F) :
    moduleIso hF D hν hν3 hν1 (psi hF D (Multiplicative.ofAdd (a, b, e))) =
      phi hF D (Multiplicative.ofAdd (a, b, e)) := by
  have hx : (psiEquiv hF D hν hν3 hν1) (Multiplicative.ofAdd (a, b, e)) =
      psi hF D (Multiplicative.ofAdd (a, b, e)) := rfl
  have hp : (phiEquiv hF D) (Multiplicative.ofAdd (a, b, e)) =
      phi hF D (Multiplicative.ofAdd (a, b, e)) := rfl
  change (phiEquiv hF D) ((psiEquiv hF D hν hν3 hν1).symm
    (psi hF D (Multiplicative.ofAdd (a, b, e)))) = phi hF D (Multiplicative.ofAdd (a, b, e))
  rw [← hx, MulEquiv.symm_apply_apply, hp]

theorem conj_x_psi (hF : Fintype.card F = 4) (D : ModHyp Q Z K τ α β) (t a b e : F) :
    conjHom D.norm_Q (xElt α t) (psi hF D (Multiplicative.ofAdd (a, b, e))) =
      psi hF D (Multiplicative.ofAdd (a + t * b, b, e + t * b * b)) := by
  haveI : IsMulCommutative ↥Q := D.elem.1
  change conjHom D.norm_Q (xElt α t) (qq1 hF D a * qq2 hF D b * zeta hF D e) =
    qq1 hF D (a + t * b) * qq2 hF D b * zeta hF D (e + t * b * b)
  rw [map_mul, map_mul, conj_x_qq1, conj_x_qq2,
    conjHom_eq_self_of_mem_Z D hF (zeta_mem_Z hF D e) (xElt α t), zz_eq_zeta]
  calc qq1 hF D a * (qq1 hF D (t * b) * qq2 hF D b * zeta hF D (t * b * b)) * zeta hF D e
      = (qq1 hF D a * qq1 hF D (t * b)) * (qq2 hF D b * zeta hF D (t * b * b)) *
          zeta hF D e := by group
    _ = qq1 hF D (a + t * b) * (qq2 hF D b * zeta hF D (t * b * b)) * zeta hF D e := by
        rw [← qq1_add]
    _ = qq1 hF D (a + t * b) * qq2 hF D b * (zeta hF D (t * b * b) * zeta hF D e) := by group
    _ = qq1 hF D (a + t * b) * qq2 hF D b * zeta hF D (t * b * b + e) := by
        rw [← zeta_add]
    _ = qq1 hF D (a + t * b) * qq2 hF D b * zeta hF D (e + t * b * b) := by
        rw [add_comm (t * b * b) e]

theorem conj_y_psi (hF : Fintype.card F = 4) (D : ModHyp Q Z K τ α β) (t a b e : F) :
    conjHom D.norm_Q (yElt α t) (psi hF D (Multiplicative.ofAdd (a, b, e))) =
      psi hF D (Multiplicative.ofAdd (a, b + t * a, e + t * a * a)) := by
  haveI : IsMulCommutative ↥Q := D.elem.1
  change conjHom D.norm_Q (yElt α t) (qq1 hF D a * qq2 hF D b * zeta hF D e) =
    qq1 hF D a * qq2 hF D (b + t * a) * zeta hF D (e + t * a * a)
  rw [map_mul, map_mul, conj_y_qq1, conj_y_qq2,
    conjHom_eq_self_of_mem_Z D hF (zeta_mem_Z hF D e) (yElt α t), zz_eq_zeta]
  calc (qq1 hF D a * qq2 hF D (t * a) * zeta hF D (t * a * a)) * qq2 hF D b * zeta hF D e
      = qq1 hF D a * (qq2 hF D (t * a) * qq2 hF D b) *
          (zeta hF D (t * a * a) * zeta hF D e) := by ac_rfl
    _ = qq1 hF D a * qq2 hF D (t * a + b) * (zeta hF D (t * a * a) * zeta hF D e) := by
        rw [← qq2_add]
    _ = qq1 hF D a * qq2 hF D (t * a + b) * zeta hF D (t * a * a + e) := by
        rw [← zeta_add]
    _ = qq1 hF D a * qq2 hF D (b + t * a) * zeta hF D (e + t * a * a) := by
        rw [add_comm (t * a) b, add_comm (t * a * a) e]

theorem conj_tau_psi (hF : Fintype.card F = 4) (D : ModHyp Q Z K τ α β) {ν : F}
    (hν : ∀ q : ↥Q, betaAdd β (tauHom D.tau_Q q) = ν • betaAdd β q)
    (hν3 : ν ^ 3 = 1) (a b e : F) :
    tauHom D.tau_Q (psi hF D (Multiplicative.ofAdd (a, b, e))) =
      psi hF D (Multiplicative.ofAdd (ν * a, ν * b, ν ^ 2 * e)) := by
  change tauHom D.tau_Q (qq1 hF D a * qq2 hF D b * zeta hF D e) =
    qq1 hF D (ν * a) * qq2 hF D (ν * b) * zeta hF D (ν ^ 2 * e)
  rw [map_mul, map_mul, conj_tau_qq1 hF D hν, conj_tau_qq2 hF D hν, zeta_tau hF D hν hν3]


theorem sElt_mul (M N : SL₂ F) : sElt (M * N) = sElt M * sElt N := by
  simpa only [sHom₂_apply] using map_mul (sHom₂ F) M N

theorem sElt_one : sElt (1 : SL₂ F) = 1 := by
  simpa only [sHom₂_apply] using map_one (sHom₂ F)

theorem sElt_inv (M : SL₂ F) : sElt M⁻¹ = (sElt M)⁻¹ := by
  simpa only [sHom₂_apply] using map_inv (sHom₂ F) M

theorem sElt_conj_aElt (M : SL₂ F) (v : Fin 2 → F) (c : F) :
    sElt M * aElt v c * (sElt M)⁻¹ =
      aElt ((M : Matrix (Fin 2) (Fin 2) F) *ᵥ v) c := by
  rw [sElt_mul_aElt, mul_assoc, mul_inv_cancel, mul_one]

theorem dElt_mul (l m : Fˣ) : dElt (l * m) = dElt l * dElt m := by
  simpa only [dHom₂_apply] using map_mul (dHom₂ F) l m

theorem dElt_one : dElt (1 : Fˣ) = 1 := by
  simpa only [dHom₂_apply] using map_one (dHom₂ F)

theorem dElt_inv (l : Fˣ) : dElt l⁻¹ = (dElt l)⁻¹ := by
  simpa only [dHom₂_apply] using map_inv (dHom₂ F) l

theorem dElt_conj_aElt (l : Fˣ) (v : Fin 2 → F) (c : F) :
    dElt l * aElt v c * (dElt l)⁻¹ =
      aElt ((l : F) • v) ((l : F) ^ 2 * c) := by
  rw [dElt_mul_aElt, mul_assoc, mul_inv_cancel, mul_one]

theorem moduleIso_conj_x (hF : Fintype.card F = 4) (D : ModHyp Q Z K τ α β) {ν : F}
    (hν : ∀ q : ↥Q, betaAdd β (tauHom D.tau_Q q) = ν • betaAdd β q)
    (hν3 : ν ^ 3 = 1) (hν1 : ν ≠ 1) (t a b e : F) :
    ((moduleIso hF D hν hν3 hν1
        (conjHom D.norm_Q (xElt α t) (psi hF D (Multiplicative.ofAdd (a, b, e)))) :
        ↥(radA2 F)) : antiSp F) =
      sElt (α (xElt α t)) *
        ((moduleIso hF D hν hν3 hν1
          (psi hF D (Multiplicative.ofAdd (a, b, e))) : ↥(radA2 F)) : antiSp F) *
        (sElt (α (xElt α t)))⁻¹ := by
  rw [conj_x_psi, moduleIso_psi, moduleIso_psi]
  change aElt ![a + t * b, b] ((e + t * b * b) + (a + t * b) * b) =
    sElt (α (xElt α t)) * aElt ![a, b] (e + a * b) * (sElt (α (xElt α t)))⁻¹
  rw [alpha_xElt, sElt_conj_aElt, unipotent_mulVec]
  congr 1
  linear_combination (t * b * b) * (CharTwo.two_eq_zero : (2 : F) = 0)

theorem moduleIso_conj_y (hF : Fintype.card F = 4) (D : ModHyp Q Z K τ α β) {ν : F}
    (hν : ∀ q : ↥Q, betaAdd β (tauHom D.tau_Q q) = ν • betaAdd β q)
    (hν3 : ν ^ 3 = 1) (hν1 : ν ≠ 1) (t a b e : F) :
    ((moduleIso hF D hν hν3 hν1
        (conjHom D.norm_Q (yElt α t) (psi hF D (Multiplicative.ofAdd (a, b, e)))) :
        ↥(radA2 F)) : antiSp F) =
      sElt (α (yElt α t)) *
        ((moduleIso hF D hν hν3 hν1
          (psi hF D (Multiplicative.ofAdd (a, b, e))) : ↥(radA2 F)) : antiSp F) *
        (sElt (α (yElt α t)))⁻¹ := by
  rw [conj_y_psi, moduleIso_psi, moduleIso_psi]
  change aElt ![a, b + t * a] ((e + t * a * a) + a * (b + t * a)) =
    sElt (α (yElt α t)) * aElt ![a, b] (e + a * b) * (sElt (α (yElt α t)))⁻¹
  rw [alpha_yElt, sElt_conj_aElt, lowerUni_mulVec]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  congr 1
  · ext i
    fin_cases i <;> simp [add_comm]
  · linear_combination (t * a * a) * (CharTwo.two_eq_zero : (2 : F) = 0)

theorem moduleIso_conj_tau (hF : Fintype.card F = 4) (D : ModHyp Q Z K τ α β) {ν : F}
    (hν : ∀ q : ↥Q, betaAdd β (tauHom D.tau_Q q) = ν • betaAdd β q)
    (hν3 : ν ^ 3 = 1) (hν1 : ν ≠ 1) (νu : Fˣ) (hνu : (νu : F) = ν) (a b e : F) :
    ((moduleIso hF D hν hν3 hν1
        (tauHom D.tau_Q (psi hF D (Multiplicative.ofAdd (a, b, e)))) :
        ↥(radA2 F)) : antiSp F) =
      dElt νu *
        ((moduleIso hF D hν hν3 hν1
          (psi hF D (Multiplicative.ofAdd (a, b, e))) : ↥(radA2 F)) : antiSp F) *
        (dElt νu)⁻¹ := by
  rw [conj_tau_psi hF D hν hν3, moduleIso_psi, moduleIso_psi]
  change aElt ![ν * a, ν * b] ((ν ^ 2 * e) + (ν * a) * (ν * b)) =
    dElt νu * aElt ![a, b] (e + a * b) * (dElt νu)⁻¹
  rw [show dElt νu * aElt ![a, b] (e + a * b) * (dElt νu)⁻¹ =
      aElt ((νu : F) • ![a, b]) ((νu : F) ^ 2 * (e + a * b)) from dElt_conj_aElt νu _ _]
  rw [hνu]
  congr 1
  · ext i
    fin_cases i <;> simp [Pi.smul_apply, smul_eq_mul]
  · ring


@[expose] def goodProp (hF : Fintype.card F = 4) (D : ModHyp Q Z K τ α β) {ν : F}
    (hν : ∀ q : ↥Q, betaAdd β (tauHom D.tau_Q q) = ν • betaAdd β q)
    (hν3 : ν ^ 3 = 1) (hν1 : ν ≠ 1) (k : ↥K) : Prop :=
  ∀ q : ↥Q,
    ((moduleIso hF D hν hν3 hν1 (conjHom D.norm_Q k q) : ↥(radA2 F)) : antiSp F) =
      sElt (α k) * ((moduleIso hF D hν hν3 hν1 q : ↥(radA2 F)) : antiSp F) *
        (sElt (α k))⁻¹

theorem good_all (hF : Fintype.card F = 4) (D : ModHyp Q Z K τ α β) {ν : F}
    (hν : ∀ q : ↥Q, betaAdd β (tauHom D.tau_Q q) = ν • betaAdd β q)
    (hν3 : ν ^ 3 = 1) (hν1 : ν ≠ 1) (k : ↥K) : goodProp hF D hν hν3 hν1 k := by
  have hgen := closure_xElt_yElt_eq_top (α := α)
  have hk : k ∈ Subgroup.closure (Set.range (xElt α) ∪ Set.range (yElt α)) := by
    rw [hgen]
    exact Subgroup.mem_top k
  refine Subgroup.closure_induction (p := fun k _ => goodProp hF D hν hν3 hν1 k)
    ?mem ?one ?mul ?inv hk
  · rintro k (⟨t, rfl⟩ | ⟨t, rfl⟩) q
    · obtain ⟨x, rfl⟩ := psi_surjective hF D hν hν3 hν1 q
      obtain ⟨a, b, e, rfl⟩ : ∃ a b e : F, x = Multiplicative.ofAdd (a, b, e) :=
        ⟨x.toAdd.1, x.toAdd.2.1, x.toAdd.2.2, rfl⟩
      exact moduleIso_conj_x hF D hν hν3 hν1 t a b e
    · obtain ⟨x, rfl⟩ := psi_surjective hF D hν hν3 hν1 q
      obtain ⟨a, b, e, rfl⟩ : ∃ a b e : F, x = Multiplicative.ofAdd (a, b, e) :=
        ⟨x.toAdd.1, x.toAdd.2.1, x.toAdd.2.2, rfl⟩
      exact moduleIso_conj_y hF D hν hν3 hν1 t a b e
  · intro q
    change ((moduleIso hF D hν hν3 hν1 (conjHom D.norm_Q (1 : ↥K) q) :
      ↥(radA2 F)) : antiSp F) = _
    rw [conjHom_one (D := D) (q := q), map_one, sElt_one]
    group
  · intro k₁ k₂ _ _ hk₁ hk₂ q
    change ((moduleIso hF D hν hν3 hν1 (conjHom D.norm_Q (k₁ * k₂) q) :
      ↥(radA2 F)) : antiSp F) = _
    rw [← conjHom_conj (D := D) (k := k₁) (h := k₂) q]
    rw [hk₁ (conjHom D.norm_Q k₂ q), hk₂ q, map_mul α k₁ k₂, sElt_mul]
    group
  · intro k _ hk q
    change ((moduleIso hF D hν hν3 hν1 (conjHom D.norm_Q k⁻¹ q) :
      ↥(radA2 F)) : antiSp F) = _
    have h := hk (conjHom D.norm_Q k⁻¹ q)
    rw [show conjHom D.norm_Q k (conjHom D.norm_Q k⁻¹ q) = q by
      rw [conjHom_conj (D := D) (k := k) (h := k⁻¹), mul_inv_cancel,
        conjHom_one (D := D)]] at h
    have hsinv : sElt (α k⁻¹) = (sElt (α k))⁻¹ := by
      rw [map_inv α k, sElt_inv]
    rw [hsinv, h, inv_inv]
    group

theorem moduleIso_conj (hF : Fintype.card F = 4) (D : ModHyp Q Z K τ α β) {ν : F}
    (hν : ∀ q : ↥Q, betaAdd β (tauHom D.tau_Q q) = ν • betaAdd β q)
    (hν3 : ν ^ 3 = 1) (hν1 : ν ≠ 1) (k : ↥K) (q : ↥Q) :
    ((moduleIso hF D hν hν3 hν1 (conjHom D.norm_Q k q) : ↥(radA2 F)) : antiSp F) =
      sElt (α k) * ((moduleIso hF D hν hν3 hν1 q : ↥(radA2 F)) : antiSp F) *
        (sElt (α k))⁻¹ :=
  good_all hF D hν hν3 hν1 k q

theorem moduleIso_tau (hF : Fintype.card F = 4) (D : ModHyp Q Z K τ α β) {ν : F}
    (hν : ∀ q : ↥Q, betaAdd β (tauHom D.tau_Q q) = ν • betaAdd β q)
    (hν3 : ν ^ 3 = 1) (hν1 : ν ≠ 1) (νu : Fˣ) (hνu : (νu : F) = ν) (q : ↥Q) :
    ((moduleIso hF D hν hν3 hν1 (tauHom D.tau_Q q) : ↥(radA2 F)) : antiSp F) =
      dElt νu * ((moduleIso hF D hν hν3 hν1 q : ↥(radA2 F)) : antiSp F) *
        (dElt νu)⁻¹ := by
  obtain ⟨x, rfl⟩ := psi_surjective hF D hν hν3 hν1 q
  obtain ⟨a, b, e, rfl⟩ : ∃ a b e : F, x = Multiplicative.ofAdd (a, b, e) :=
    ⟨x.toAdd.1, x.toAdd.2.1, x.toAdd.2.2, rfl⟩
  exact moduleIso_conj_tau hF D hν hν3 hν1 νu hνu a b e


theorem psi_beta (hF : Fintype.card F = 4) (D : ModHyp Q Z K τ α β) (a b e : F) :
    betaAdd β (psi hF D (Multiplicative.ofAdd (a, b, e))) = ![a, b] := by
  show betaAdd β (qq1 hF D a * qq2 hF D b * zeta hF D e) = ![a, b]
  rw [betaAdd_mul, betaAdd_mul, qq1_beta, qq2_beta,
    (betaAdd_eq_zero_iff D.ker _).mpr (zeta_mem_Z hF D e)]
  ext i
  fin_cases i <;> simp

theorem psi_mem_Z_iff (hF : Fintype.card F = 4) (D : ModHyp Q Z K τ α β) (a b e : F) :
    ((psi hF D (Multiplicative.ofAdd (a, b, e)) : ↥Q) : G) ∈ Z ↔ a = 0 ∧ b = 0 := by
  constructor
  · intro hz
    have h0 : betaAdd β (psi hF D (Multiplicative.ofAdd (a, b, e))) = 0 :=
      (betaAdd_eq_zero_iff D.ker _).mpr hz
    rw [psi_beta] at h0
    exact ⟨by simpa using congrFun h0 0, by simpa using congrFun h0 1⟩
  · rintro ⟨rfl, rfl⟩
    apply (betaAdd_eq_zero_iff D.ker _).mp
    rw [psi_beta]
    ext i
    fin_cases i <;> rfl

theorem phi_mem_rootU₂_iff (hF : Fintype.card F = 4) (D : ModHyp Q Z K τ α β) (a b e : F) :
    ((phi hF D (Multiplicative.ofAdd (a, b, e)) : ↥(radA2 F)) : antiSp F) ∈ rootU₂ F ↔
      a = 0 ∧ b = 0 := by
  have hphi : ((phi hF D (Multiplicative.ofAdd (a, b, e)) : ↥(radA2 F)) : antiSp F) =
      uElt b a (e + a * b) 0 := rfl
  rw [hphi, mem_rootU₂]
  constructor
  · rintro ⟨c, hc⟩
    obtain ⟨h1, h2, -, -⟩ := uElt_inj hc
    exact ⟨h2, h1⟩
  · rintro ⟨rfl, rfl⟩
    refine ⟨e, ?_⟩
    simp

theorem moduleIso_mem_Z_iff (hF : Fintype.card F = 4) (D : ModHyp Q Z K τ α β) {ν : F}
    (hν : ∀ q : ↥Q, betaAdd β (tauHom D.tau_Q q) = ν • betaAdd β q)
    (hν3 : ν ^ 3 = 1) (hν1 : ν ≠ 1) (q : ↥Q) :
    (q : G) ∈ Z ↔
      ((moduleIso hF D hν hν3 hν1 q : ↥(radA2 F)) : antiSp F) ∈ rootU₂ F := by
  obtain ⟨x, rfl⟩ := psi_surjective hF D hν hν3 hν1 q
  obtain ⟨a, b, e, rfl⟩ : ∃ a b e : F, x = Multiplicative.ofAdd (a, b, e) :=
    ⟨x.toAdd.1, x.toAdd.2.1, x.toAdd.2.2, rfl⟩
  rw [moduleIso_psi, psi_mem_Z_iff, phi_mem_rootU₂_iff]

theorem exists_moduleIso (hF : Fintype.card F = 4) (D : ModHyp Q Z K τ α β) :
    ∃ (ν : Fˣ) (b : ↥Q ≃* ↥(radA2 F)), ν ≠ 1 ∧
      (∀ q : ↥Q, (q : G) ∈ Z ↔ (b q : antiSp F) ∈ rootU₂ F) ∧
      (∀ (k : ↥K) (q q' : ↥Q), (q' : G) = k * q * k⁻¹ →
        (b q' : antiSp F) = sElt (α k) * b q * (sElt (α k))⁻¹) ∧
      (∀ q q' : ↥Q, (q' : G) = τ * q * τ⁻¹ →
        (b q' : antiSp F) = dElt ν * b q * (dElt ν)⁻¹) := by
  have hτZ : ∀ z ∈ Z, τ * z * τ⁻¹ ∈ Z := fun z hz =>
    tau_conj_mem_Z D.equiv D.ker D.norm_Q D.cent_Z D.tau_Q D.tau_K D.le_Z hz
  obtain ⟨νF, hνF⟩ :=
    exists_tau_scalar hF D.equiv D.ker D.norm_Q D.tau_Q hτZ D.tau_K D.surj
  have hν3 : νF ^ 3 = 1 := tau_scalar_pow_three D.tau_Q hνF D.surj D.tau_three
  have hν1 : νF ≠ 1 :=
    tau_scalar_ne_one hF D.tau_Q hνF D.elem D.le_Z D.card_Z D.ker D.surj D.tau_ff
  have hν0 : νF ≠ 0 := by
    rintro rfl
    norm_num at hν3
  let ν : Fˣ := Units.mk0 νF hν0
  have hνval : (ν : F) = νF := Units.val_mk0 hν0
  refine ⟨ν, moduleIso hF D hνF hν3 hν1, ?_, ?_, ?_, ?_⟩
  · intro h
    exact hν1 (by rw [← hνval]; exact congrArg Units.val h)
  · intro q
    exact moduleIso_mem_Z_iff hF D hνF hν3 hν1 q
  · intro k q q' hq'
    have hq'' : q' = conjHom D.norm_Q k q := Subtype.ext hq'
    subst hq''
    exact moduleIso_conj hF D hνF hν3 hν1 k q
  · intro q q' hq'
    have hq'' : q' = tauHom D.tau_Q q := Subtype.ext hq'
    subst hq''
    exact moduleIso_tau hF D hνF hν3 hν1 ν hνval q

theorem xElt_eq_symm (α : ↥K ≃* SL₂ F) (t : F) :
    xElt α t = α.symm (CFSG.SL2MinimalFaithful.unipotent t) := by
  apply α.injective
  rw [alpha_xElt, α.apply_symm_apply]

theorem Cplus_eq_centralizer (α : ↥K ≃* SL₂ F) (Q : Subgroup G) :
    Cplus α Q = Q ⊓ Subgroup.centralizer
      (Set.range fun t : F => ((α.symm (CFSG.SL2MinimalFaithful.unipotent t) : ↥K) : G)) := by
  rw [Cplus]
  apply congrArg (fun S : Set G => Q ⊓ Subgroup.centralizer S)
  ext g
  simp only [Set.mem_range]
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨t, by rw [xElt_eq_symm]⟩
  · rintro ⟨t, rfl⟩
    exact ⟨t, by rw [xElt_eq_symm]⟩

theorem exists_moduleIso_unbundled (hF : Fintype.card F = 4) {Q Z K : Subgroup G} {τ : G}
    {α : ↥K ≃* SL₂ F} {β : ↥Q →* Multiplicative (Fin 2 → F)}
    (hQe : IsElemAbelian 2 Q) (hZQ : Z ≤ Q) (hZc : Nat.card Z = 4)
    (hKQ : ∀ k ∈ K, ∀ q ∈ Q, k * q * k⁻¹ ∈ Q)
    (hKZ : ∀ k ∈ K, ∀ z ∈ Z, k * z = z * k)
    (hβs : Function.Surjective β)
    (hβk : ∀ q : ↥Q, β q = 1 ↔ (q : G) ∈ Z)
    (hβe : ∀ (k : ↥K) (q q' : ↥Q), (q' : G) = k * q * k⁻¹ →
      Multiplicative.toAdd (β q') = (α k : Matrix (Fin 2) (Fin 2) F) *ᵥ
        Multiplicative.toAdd (β q))
    (hind : ∀ W : Subgroup G, W ≤ Q → (∀ k ∈ K, ∀ w ∈ W, k * w * k⁻¹ ∈ W) →
      W ⊔ Z = Q → W = Q)
    (hT : 16 ≤ Nat.card ↥(Q ⊓ Subgroup.centralizer
      (Set.range fun t : F => ((α.symm (CFSG.SL2MinimalFaithful.unipotent t) : ↥K) : G))))
    (hτQ : ∀ q ∈ Q, τ * q * τ⁻¹ ∈ Q) (hτK : ∀ k ∈ K, τ * k = k * τ)
    (hτ3 : τ ^ 3 = 1) (hτff : ∀ q ∈ Q, τ * q * τ⁻¹ = q → q = 1) :
    ∃ (ν : Fˣ) (b : ↥Q ≃* ↥(radA2 F)), ν ≠ 1 ∧
      (∀ q : ↥Q, (q : G) ∈ Z ↔ (b q : antiSp F) ∈ rootU₂ F) ∧
      (∀ (k : ↥K) (q q' : ↥Q), (q' : G) = k * q * k⁻¹ →
        (b q' : antiSp F) = sElt (α k) * b q * (sElt (α k))⁻¹) ∧
      (∀ q q' : ↥Q, (q' : G) = τ * q * τ⁻¹ →
        (b q' : antiSp F) = dElt ν * b q * (dElt ν)⁻¹) :=
  have hT' : 16 ≤ Nat.card ↥(Cplus α Q) := by
    rwa [Cplus_eq_centralizer]
  exists_moduleIso hF
    ⟨hQe, hZQ, hZc, hKQ, hKZ, hβs, hβk, hβe, hind, hT', hτQ, hτK, hτ3, hτff⟩


end Sp44

end CFSG.Quasithin.F112R.St84
