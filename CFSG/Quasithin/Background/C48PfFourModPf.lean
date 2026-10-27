module

public import CFSG.Quasithin.Background.C48PfFourMod
public import CFSG.Quasithin.Background.C48PfFourModPfNat
public import CFSG.Quasithin.Background.C48PfFourModPfExt
public import CFSG.Quasithin.Background.C48PfFourModPfCov
public import CFSG.Quasithin.Background.C48PfFourModPfA8
public import CFSG.Quasithin.Background.FLc2Real
public import CFSG.Quasithin.Background.FFC13S
public import CFSG.Quasithin.Background.F918T1
public import CFSG.Quasithin.Background.F918F1
public import CFSG.Quasithin.Background.B15P4Res
public import CFSG.Quasithin.EmptyFaithful.T1515dC
public import CFSG.Quasithin.Background.G64ExtSq

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.C48Pf.FMod

open Matrix CFSG.QuasithinUnique.Vol2Native.A312L CFSG.Assembly.LowTwoRank

structure ModCtx {W : Type*} [CommGroup W] (n a m : ℕ)
    (ρ : SpecialLinearGroup (Fin n) (ZMod 2) →* MulAut W)
    (A : Subgroup (SpecialLinearGroup (Fin n) (ZMod 2))) (V : Subgroup W) : Prop where
  hm3 : 3 ≤ m
  hamn : a + m ≤ n
  hprop : 0 < a ∨ a + m < n
  hA : ∀ t ∈ A, BlockForm a m (t : Matrix (Fin n) (Fin n) (ZMod 2))
  hVA : ∀ t ∈ A, ∀ v ∈ V, ρ t v ∈ V
  hgen : V ≤ Subgroup.closure {w | ∃ t ∈ A, ∃ v ∈ V, ρ t v * v⁻¹ = w}
  hcross : ∀ (k l : Fin n) (hc : IsCross a m k l), ∀ v ∈ V,
    ρ (SpecialLinearGroup.transvection hc.ne (1 : ZMod 2)) v = v
  hne : V ≠ ⊥


section Reduction

open CFSG.Open hiding StatedSL StatedSp
open CFSG.QuasithinUnique
open scoped commutatorElement

theorem pCore_le_open_pCore {X : Type*} [Group X] : CFSG.pCore 2 X ≤ CFSG.Open.pCore 2 X :=
  le_rfl

theorem conj_mem_of_commutator_eq {G : Type} [Group G] {V P₀ : Subgroup G}
    (hVcomm : ⁅V, P₀⁆ = V) {x v : G} (hx : x ∈ P₀) (hv : v ∈ V) : x * v * x⁻¹ ∈ V := by
  have h1 : ⁅v, x⁆ ∈ V := by
    rw [← hVcomm]
    exact Subgroup.commutator_mem_commutator hv hx
  have h2 : ⁅x, v⁆ ∈ V := by
    rw [← commutatorElement_inv]
    exact V.inv_mem h1
  have : x * v * x⁻¹ = ⁅x, v⁆ * v := by
    rw [commutatorElement_def]
    group
  rw [this]
  exact V.mul_mem h2 hv

variable {G : Type} [Group G] [Finite G]

theorem reduction {K U P P₀ V : Subgroup G} (hU : IsElemAbelian 2 U)
    (hKU : K ≤ Subgroup.normalizer (U : Set G))
    (hCK : K ⊓ Subgroup.centralizer (U : Set G) ≤ pCoreOf 2 K)
    (hpar : IsParabolic2 K P) (hPK : P ≠ K) (hP₀P : P₀ ≤ P)
    (hPN : P ≤ Subgroup.normalizer (P₀ : Set G)) (hperf : ⁅P₀, P₀⁆ = P₀)
    {m : ℕ} (hm : m = 3 ∨ m = 4) (hpm : IsPSL m 2 1 (ModO2 P₀))
    (hV1 : V ≠ ⊥) (hVU : V ≤ U) (hVO : V ≤ Subgroup.centralizer (pCoreOf 2 P₀ : Set G))
    (hVcomm : ⁅V, P₀⁆ = V) {n : ℕ} (hn4 : 4 ≤ n) (hn5 : n ≤ 5)
    (π : ↥(StatedSL n (ZMod 2)) →* ↥(autOn K U)) (hπ : Function.Bijective π) :
    ∃ (g : SpecialLinearGroup (Fin n) (ZMod 2)) (a : ℕ) (hamn : a + m ≤ n)
      (α : ↥P₀ →* SpecialLinearGroup (Fin m) (ZMod 2))
      (θ : ↥P₀ →* SpecialLinearGroup (Fin n) (ZMod 2)),
      Function.Surjective α ∧ α.ker = CFSG.pCore 2 ↥P₀ ∧
      (∀ x, blkAt a m hamn ((θ x : SpecialLinearGroup (Fin n) (ZMod 2)) :
        Matrix (Fin n) (Fin n) (ZMod 2)) =
          ((α x : SpecialLinearGroup (Fin m) (ZMod 2)) : Matrix (Fin m) (Fin m) (ZMod 2))) ∧
      (∀ (x : ↥P₀) (u : ↥U), ((@FLc.rhoOf ↥U (commGroupOfElemAbelian hU) n (autOn K U)
        (π.comp (MulAut.conj (specialLinearGroupEquivStatedSL n (ZMod 2) g)).toMonoidHom)
          (θ x) u : ↥U) : G) = x * u * (x : G)⁻¹) ∧
      @ModCtx ↥U (commGroupOfElemAbelian hU) n a m
        (@FLc.rhoOf ↥U (commGroupOfElemAbelian hU) n (autOn K U)
          (π.comp (MulAut.conj (specialLinearGroupEquivStatedSL n (ZMod 2) g)).toMonoidHom))
        θ.range (V.subgroupOf U) := by
  classical
  let _ : CommGroup ↥U := commGroupOfElemAbelian hU
  have hP₀K : P₀ ≤ K := hP₀P.trans hpar.1
  set e := specialLinearGroupEquivStatedSL n (ZMod 2) with he
  set E : SpecialLinearGroup (Fin n) (ZMod 2) ≃* ↥(autOn K U) :=
    e.trans (MulEquiv.ofBijective π hπ) with hE
  have hEapp : ∀ h, E h = π (e h) := fun h => rfl
  set ψ : ↥K →* SpecialLinearGroup (Fin n) (ZMod 2) :=
    E.symm.toMonoidHom.comp (InternalSec.autOnHom hKU) with hψdef
  have hψE : ∀ k, E (ψ k) = InternalSec.autOnHom hKU k := fun k => E.apply_symm_apply _
  have hψs : Function.Surjective ψ := E.symm.surjective.comp (InternalSec.autOnHom_surjective hKU)
  have hψker : ∀ k : ↥K, ψ k = 1 → (k : G) ∈ pCoreOf 2 K := by
    intro k hk
    have h1 : InternalSec.autOnHom hKU k = 1 := by rw [← hψE, hk, map_one]
    exact hCK ⟨k.2, (InternalSec.mem_ker_autOnHom hKU k).1 h1⟩
  obtain ⟨g, a, hamn, α, hprop, hαs, hker, hblk, hcrossP⟩ :=
    exists_config hn4 hn5 ψ hψs hψker hpar hPK hP₀P hPN hperf hm hpm
  set θ : ↥P₀ →* SpecialLinearGroup (Fin n) (ZMod 2) :=
    (MulAut.conj g⁻¹).toMonoidHom.comp (ψ.comp (Subgroup.inclusion hP₀K)) with hθdef
  have hθ : ∀ x : ↥P₀, θ x = g⁻¹ * ψ ⟨x, hP₀K x.2⟩ * g := fun x => by
    simp [θ, Subgroup.inclusion]
  set ρ := FLc.rhoOf (π.comp (MulAut.conj (e g)).toMonoidHom) with hρdef
  have hρ : ∀ h, ρ h = ((E (g * h * g⁻¹) : ↥(autOn K U)) : MulAut ↥U) := by
    intro h
    have h1 : MulAut.conj (e g) (e h) = e (g * h * g⁻¹) := by
      rw [MulAut.conj_apply, map_mul, map_mul, map_inv]
    rw [hρdef, FLc.rhoOf_apply, hEapp, ← h1]
    rfl
  have hρθ : ∀ (x : ↥P₀) (u : ↥U), ((ρ (θ x) u : ↥U) : G) = x * u * (x : G)⁻¹ := by
    intro x u
    rw [hρ, hθ]
    have : g * (g⁻¹ * ψ ⟨x, hP₀K x.2⟩ * g) * g⁻¹ = ψ ⟨x, hP₀K x.2⟩ := by group
    rw [this, hψE]
    exact Setup.rho_apply_coe hKU ⟨x, hP₀K x.2⟩ u
  have hVN : ∀ x ∈ P₀, ∀ v ∈ V, x * v * x⁻¹ ∈ V := fun x hx v hv =>
    conj_mem_of_commutator_eq hVcomm hx hv
  refine ⟨g, a, hamn, α, θ, hαs, hker, fun x => ?_, hρθ, ?_⟩
  · rw [hθ]
    exact (hblk x).1
  refine ⟨by omega, hamn, hprop, ?_, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨x, rfl⟩
    rw [hθ]
    exact (hblk x).2
  · rintro _ ⟨x, rfl⟩ v hv
    rw [Subgroup.mem_subgroupOf, hρθ]
    exact hVN x x.2 v hv
  · intro w hw
    have hwG : (w : G) ∈ ⁅V, P₀⁆ := by
      rw [hVcomm]
      exact hw
    rw [Subgroup.commutator_def] at hwG
    have key : ∀ y ∈ Subgroup.closure {g | ∃ g₁ ∈ V, ∃ g₂ ∈ P₀, ⁅g₁, g₂⁆ = g},
        y ∈ (Subgroup.closure {w | ∃ t ∈ θ.range, ∃ v ∈ V.subgroupOf U, ρ t v * v⁻¹ = w}).map
          U.subtype := by
      intro y hy
      induction hy using Subgroup.closure_induction with
      | mem y hy =>
        obtain ⟨v, hv, x, hx, rfl⟩ := hy
        refine ⟨(ρ (θ ⟨x, hx⟩) ⟨v, hVU hv⟩ * (⟨v, hVU hv⟩ : ↥U)⁻¹)⁻¹,
          Subgroup.inv_mem _ (Subgroup.subset_closure ⟨_, ⟨⟨x, hx⟩, rfl⟩, _, hv, rfl⟩), ?_⟩
        simp only [Subgroup.coe_subtype, Subgroup.coe_inv, Subgroup.coe_mul]
        rw [hρθ]
        simp only [commutatorElement_def]
        group
      | one => exact Subgroup.one_mem _
      | mul y z _ _ hy hz => exact Subgroup.mul_mem _ hy hz
      | inv y _ hy => exact Subgroup.inv_mem _ hy
    obtain ⟨w', hw', hww'⟩ := key _ hwG
    have : w' = w := Subtype.ext hww'
    rw [← this]
    exact hw'
  · intro k l hc v hv
    obtain ⟨p, hp, hpT⟩ := hcrossP k l hc
    have hpθ : θ p = SpecialLinearGroup.transvection hc.ne (1 : ZMod 2) := by
      rw [hθ]
      exact hpT
    apply Subtype.ext
    rw [← hpθ, hρθ]
    have hpO : (p : G) ∈ pCoreOf 2 P₀ := ⟨p, pCore_le_open_pCore hp, rfl⟩
    have hc' : (p : G) * (v : G) = (v : G) * (p : G) :=
      Subgroup.mem_centralizer_iff.1 (hVO hv) _ hpO
    rw [hc', mul_inv_cancel_right]
  · intro hbot
    apply hV1
    rw [Subgroup.subgroupOf_eq_bot] at hbot
    rw [eq_bot_iff]
    intro v hv
    exact (Subgroup.disjoint_def.1 hbot hv (hVU hv))

omit [Finite G] in
theorem transfer {U V P₀ : Subgroup G} (hVU : V ≤ U) {n : ℕ}
    (ρ : SpecialLinearGroup (Fin n) (ZMod 2) →* MulAut ↥U)
    (θ : ↥P₀ →* SpecialLinearGroup (Fin n) (ZMod 2))
    (hρθ : ∀ (x : ↥P₀) (u : ↥U), ((ρ (θ x) u : ↥U) : G) = x * u * (x : G)⁻¹)
    {M : Type*} [Group M] (Ψ' : ↥(V.subgroupOf U) →* M) :
    ∃ Ψ : ↥V →* M, (Function.Injective Ψ' → Function.Injective Ψ) ∧
      (Function.Surjective Ψ' → Function.Surjective Ψ) ∧
      ∀ (a : ↥P₀) (u v : ↥V) (huv : (v : G) = a * u * (a : G)⁻¹),
        Ψ v = Ψ' ⟨ρ (θ a) ⟨u, hVU u.2⟩, by
          rw [Subgroup.mem_subgroupOf, hρθ, ← huv]
          exact v.2⟩ ∧ Ψ u = Ψ' ⟨⟨u, hVU u.2⟩, u.2⟩ := by
  let eV : ↥V →* ↥(V.subgroupOf U) :=
    { toFun := fun v => ⟨⟨v, hVU v.2⟩, v.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have heVb : Function.Bijective eV := by
    refine ⟨fun x y hxy => ?_, fun w => ⟨⟨(w : ↥U), w.2⟩, rfl⟩⟩
    have := congrArg (fun w : ↥(V.subgroupOf U) => ((w : ↥U) : G)) hxy
    exact Subtype.ext this
  refine ⟨Ψ'.comp eV, fun h => h.comp heVb.1, fun h => h.comp heVb.2, fun a u v huv => ⟨?_, rfl⟩⟩
  show Ψ' (eV v) = _
  congr 1
  apply Subtype.ext
  apply Subtype.ext
  show (v : G) = _
  rw [hρθ, huv]

end Reduction

section Coords

variable {W : Type} [CommGroup W] {X : Subgroup (MulAut W)} {J Z : Subgroup W} {n : ℕ}

theorem eq_one_of_mulVec_eq {d : ℕ} {g : Matrix (Fin d) (Fin d) (ZMod 2)}
    (h : ∀ x, g *ᵥ x = x) : g = 1 := by
  ext i j
  have := congrFun (h (Pi.single j 1)) i
  rw [Matrix.mulVec_single_one] at this
  simpa [Matrix.one_apply, Pi.single_apply, eq_comm] using this

theorem natCoords {π : ↥(StatedSL n (ZMod 2)) →* ↥X}
    (h : (FFModel.nat (StatedSL n (ZMod 2))).RealizesVia X J ⊥ π) :
    ∃ β : ↥J →* Multiplicative (Fin n → ZMod 2), Function.Injective β ∧ Function.Surjective β ∧
      (∀ g, ∀ u ∈ J, FLc.rhoOf π g u ∈ J) ∧
      (∀ g (u : ↥J) (hu : FLc.rhoOf π g u ∈ J), Multiplicative.toAdd (β ⟨FLc.rhoOf π g u, hu⟩) =
        (g : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ Multiplicative.toAdd (β u)) ∧
      Function.Surjective π := by
  obtain ⟨β, hβs, hβk, hβe, hUinv, hπs⟩ :=
    FLc.vmodel_of_realizes (natAct (StatedSL n (ZMod 2))) h
  refine ⟨β, ?_, hβs, fun g u hu => hUinv _ u hu, fun g u hu => ?_, hπs⟩
  · rw [injective_iff_map_eq_one]
    intro u hu
    exact Subtype.ext ((hβk u).1 hu)
  · have := hβe (specialLinearGroupEquivStatedSL n (ZMod 2) g) u hu
    exact congrArg Multiplicative.toAdd this

theorem dualCoords {π : ↥(StatedSL n (ZMod 2)) →* ↥X}
    (h : (FFModel.dualNat (StatedSL n (ZMod 2))).RealizesVia X J ⊥ π) :
    ∃ β : ↥J →* Multiplicative (Fin n → ZMod 2), Function.Injective β ∧ Function.Surjective β ∧
      (∀ g, ∀ u ∈ J, FLc.rhoOf π g u ∈ J) ∧
      (∀ g (u : ↥J) (hu : FLc.rhoOf π g u ∈ J), Multiplicative.toAdd (β ⟨FLc.rhoOf π g u, hu⟩) =
        ((g⁻¹ : SpecialLinearGroup (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2))ᵀ *ᵥ
          Multiplicative.toAdd (β u)) := by
  obtain ⟨β, hβs, hβk, hβe, hUinv, -⟩ :=
    FLc.vmodel_of_realizes (dualNatAct (StatedSL n (ZMod 2))) h
  refine ⟨β, ?_, hβs, fun g u hu => hUinv _ u hu, fun g u hu => ?_⟩
  · rw [injective_iff_map_eq_one]
    intro u hu
    exact Subtype.ext ((hβk u).1 hu)
  · have h1 := congrArg Multiplicative.toAdd
      (hβe (specialLinearGroupEquivStatedSL n (ZMod 2) g) u hu)
    refine h1.trans ?_
    show ((((specialLinearGroupEquivStatedSL n (ZMod 2) g)⁻¹ : ↥(StatedSL n (ZMod 2))) :
      GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2))ᵀ *ᵥ _ = _
    rw [← map_inv]
    rfl

theorem injective_of_natCoords {π : ↥(StatedSL n (ZMod 2)) →* ↥X}
    (β : ↥J →* Multiplicative (Fin n → ZMod 2)) (hβs : Function.Surjective β)
    (hinv : ∀ g, ∀ u ∈ J, FLc.rhoOf π g u ∈ J)
    (hβ : ∀ g (u : ↥J) (hu : FLc.rhoOf π g u ∈ J), Multiplicative.toAdd (β ⟨FLc.rhoOf π g u, hu⟩) =
      (g : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ Multiplicative.toAdd (β u)) :
    Function.Injective π := by
  rw [injective_iff_map_eq_one]
  intro γ hγ
  set g := (specialLinearGroupEquivStatedSL n (ZMod 2)).symm γ with hg
  have hρ : FLc.rhoOf π g = 1 := by
    rw [FLc.rhoOf_apply, hg, MulEquiv.apply_symm_apply, hγ]
    rfl
  have hfix : ∀ x, (g : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ x = x := by
    intro x
    obtain ⟨u, hu⟩ := hβs (Multiplicative.ofAdd x)
    have h1 := hβ g u (hinv g u u.2)
    have h2 : (⟨FLc.rhoOf π g u, hinv g u u.2⟩ : ↥J) = u := by
      apply Subtype.ext
      show FLc.rhoOf π g (u : W) = u
      rw [hρ]
      rfl
    rw [h2, hu] at h1
    exact h1.symm
  have hg1 : g = 1 := Subtype.ext (eq_one_of_mulVec_eq hfix)
  have : γ = specialLinearGroupEquivStatedSL n (ZMod 2) g := by
    rw [hg, MulEquiv.apply_symm_apply]
  rw [this, hg1, map_one]

theorem ext4Coords {π : ↥(StatedSL 4 (ZMod 2)) →* ↥X}
    (h : (FFModel.extSq (ZMod 2) 4).RealizesVia X J Z π) :
    ∃ q : ↥J →* Multiplicative (Fin 6 → ZMod 2), Function.Surjective q ∧
      (∀ u : ↥J, q u = 1 ↔ (u : W) ∈ Z) ∧ (∀ g, ∀ u ∈ J, FLc.rhoOf π g u ∈ J) ∧
      (∀ g (u : ↥J) (hu : FLc.rhoOf π g u ∈ J), Multiplicative.toAdd (q ⟨FLc.rhoOf π g u, hu⟩) =
        minors4 (g : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ Multiplicative.toAdd (q u)) := by
  obtain ⟨β, hβs, hβk, hβe, hUinv, -⟩ := FLc.vmodel_of_realizes (extSqAct (ZMod 2) 4) h
  let Φ : Multiplicative (⋀[ZMod 2]^2 (Fin 4 → ZMod 2)) ≃* Multiplicative (Fin 6 → ZMod 2) :=
    AddEquiv.toMultiplicative (JonesParshall.wedgeEquiv4 (ZMod 2)).toAddEquiv
  refine ⟨Φ.toMonoidHom.comp β, Φ.surjective.comp hβs, fun u => ?_, fun g u hu => hUinv _ u hu,
    fun g u hu => ?_⟩
  · rw [← hβk u, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    exact map_eq_one_iff Φ Φ.injective
  · have h1 := congrArg Φ (hβe (specialLinearGroupEquivStatedSL 4 (ZMod 2) g) u hu)
    have h2 : Multiplicative.toAdd (Φ (extSqAct (ZMod 2) 4
        (specialLinearGroupEquivStatedSL 4 (ZMod 2) g) (β u))) =
        minors4 (g : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ Multiplicative.toAdd (Φ (β u)) :=
      JonesParshall.wedgeCoord_map4 _ _
    exact (congrArg Multiplicative.toAdd h1).trans h2

theorem ext5Coords {π : ↥(StatedSL 5 (ZMod 2)) →* ↥X}
    (h : (FFModel.extSq (ZMod 2) 5).RealizesVia X J ⊥ π) :
    ∃ Φ : ↥J →* Multiplicative (Matrix (Fin 5) (Fin 5) (ZMod 2)),
      (∀ u, Multiplicative.toAdd (Φ u) ∈ altMat 5) ∧ Function.Injective Φ ∧
      (∀ g, ∀ u ∈ J, FLc.rhoOf π g u ∈ J) ∧
      (∀ (g : SpecialLinearGroup (Fin 5) (ZMod 2)) (u : ↥J) (hu : FLc.rhoOf π g u ∈ J),
        Multiplicative.toAdd (Φ ⟨FLc.rhoOf π g u, hu⟩) =
          (g : Matrix (Fin 5) (Fin 5) (ZMod 2)) * Multiplicative.toAdd (Φ u) *
            (g : Matrix (Fin 5) (Fin 5) (ZMod 2))ᵀ) := by
  obtain ⟨β, -, hβk, hβe, hUinv, -⟩ := FLc.vmodel_of_realizes (extSqAct (ZMod 2) 5) h
  obtain ⟨Ψ, hΨ⟩ := extSq5_equiv_alt
  let c : Multiplicative ↥(altMat 5) →* Multiplicative (Matrix (Fin 5) (Fin 5) (ZMod 2)) :=
    AddMonoidHom.toMultiplicative (altMat 5).subtype.toAddMonoidHom
  refine ⟨c.comp (Ψ.toMonoidHom.comp β), fun u => (Multiplicative.toAdd (Ψ (β u))).2, ?_,
    fun g u hu => hUinv _ u hu, fun g u hu => ?_⟩
  · rw [injective_iff_map_eq_one]
    intro u hu
    have h1 : ((Multiplicative.toAdd (Ψ (β u)) : ↥(altMat 5)) :
        Matrix (Fin 5) (Fin 5) (ZMod 2)) = 0 := congrArg Multiplicative.toAdd hu
    have h2 : Ψ (β u) = 1 := Multiplicative.toAdd.injective (Subtype.ext h1)
    have h3 : β u = 1 := (map_eq_one_iff Ψ Ψ.injective).1 h2
    exact Subtype.ext ((hβk u).1 h3)
  · have h1 := congrArg Ψ (hβe (specialLinearGroupEquivStatedSL 5 (ZMod 2) g) u hu)
    rw [hΨ] at h1
    exact congrArg (fun x => ((Multiplicative.toAdd x : ↥(altMat 5)) :
      Matrix (Fin 5) (Fin 5) (ZMod 2))) h1

@[expose] def alt4Of : (Fin 6 → ZMod 2) →+ Matrix (Fin 4) (Fin 4) (ZMod 2) where
  toFun c := !![0, c 0, c 1, c 2; c 0, 0, c 3, c 4; c 1, c 3, 0, c 5; c 2, c 4, c 5, 0]
  map_zero' := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  map_add' c d := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp

theorem alt4Of_mem (c : Fin 6 → ZMod 2) : alt4Of c ∈ altMat 4 :=
  ⟨by ext i j; fin_cases i <;> fin_cases j <;> rfl, fun i => by fin_cases i <;> rfl⟩

theorem altCoords4_alt4Of (c : Fin 6 → ZMod 2) : altCoords4 (alt4Of c) = c := by
  funext k
  fin_cases k <;> rfl

theorem alt4Of_altCoords4 {N : Matrix (Fin 4) (Fin 4) (ZMod 2)} (hN : N ∈ altMat 4) :
    alt4Of (altCoords4 N) = N :=
  (alt4_eq hN).symm

theorem alt4Of_minors4 (g : Matrix (Fin 4) (Fin 4) (ZMod 2)) (c : Fin 6 → ZMod 2) :
    alt4Of (minors4 g *ᵥ c) = g * alt4Of c * gᵀ := by
  have h1 := altCoords4_congr g (alt4Of_mem c)
  rw [altCoords4_alt4Of] at h1
  rw [← h1, alt4Of_altCoords4 (congr_mem_altMat g (alt4Of_mem c))]

theorem alt4Coords {ρ : SpecialLinearGroup (Fin 4) (ZMod 2) →* MulAut W}
    (q : ↥J →* Multiplicative (Fin 6 → ZMod 2))
    (hqk : ∀ u : ↥J, q u = 1 ↔ (u : W) ∈ (⊥ : Subgroup W))
    (hqe : ∀ g (u : ↥J) (hu : ρ g u ∈ J), Multiplicative.toAdd (q ⟨ρ g u, hu⟩) =
      minors4 (g : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ Multiplicative.toAdd (q u)) :
    ∃ Φ : ↥J →* Multiplicative (Matrix (Fin 4) (Fin 4) (ZMod 2)),
      (∀ u, Multiplicative.toAdd (Φ u) ∈ altMat 4) ∧ Function.Injective Φ ∧
      ∀ (h : SpecialLinearGroup (Fin 4) (ZMod 2)) (u : ↥J) (hu : ρ h u ∈ J),
        Multiplicative.toAdd (Φ ⟨ρ h u, hu⟩) = (h : Matrix (Fin 4) (Fin 4) (ZMod 2)) *
          Multiplicative.toAdd (Φ u) * (h : Matrix (Fin 4) (Fin 4) (ZMod 2))ᵀ := by
  refine ⟨(AddMonoidHom.toMultiplicative alt4Of).comp q, fun u => alt4Of_mem _, ?_,
    fun h u hu => ?_⟩
  · rw [injective_iff_map_eq_one]
    intro u hu
    have h1 : alt4Of (Multiplicative.toAdd (q u)) = 0 := congrArg Multiplicative.toAdd hu
    have h2 : Multiplicative.toAdd (q u) = 0 := by
      rw [← altCoords4_alt4Of (Multiplicative.toAdd (q u)), h1]
      rfl
    exact Subtype.ext ((hqk u).1 (Multiplicative.toAdd.injective h2))
  · show alt4Of (Multiplicative.toAdd (q ⟨ρ h u, hu⟩)) = _
    rw [hqe]
    exact alt4Of_minors4 _ _

theorem injective_of_realizesVia {D : FFModel} (hD : D.Faithful) {π : D.Gam →* ↥X}
    (h : D.RealizesVia X J Z π) : Function.Injective π :=
  CFSG.Quasithin.FFModel.RealizesVia.injective_of_faithful_on hD h

theorem commV_le_closure (hn : 3 ≤ n) {π : ↥(StatedSL n (ZMod 2)) →* ↥X}
    (hπ : Function.Surjective π) :
    commV X ≤ Subgroup.closure {c | ∃ γ, ∃ u ∈ commV X, FLc.rhoOf π γ u * u⁻¹ = c} := by
  have hrange : (⊤ : Subgroup (SpecialLinearGroup (Fin n) (ZMod 2))).map (FLc.rhoOf π) = X := by
    ext x
    constructor
    · rintro ⟨g, -, rfl⟩
      exact FLc.rhoOf_mem π g
    · intro hx
      obtain ⟨g, hg⟩ := FLc.rhoOf_surj hπ x hx
      exact ⟨g, Subgroup.mem_top g, hg⟩
  have hc := CFSG.ClassicalModels.specialLinear_commutator_eq_top_of_three_le (K := ZMod 2) hn
  rw [_root_.commutator_def] at hc
  have hX : ⁅X, X⁆ = X := by
    rw [← hrange, ← Subgroup.map_commutator, hc]
  have h1 := B15P4.commSub_commV_of_perfect hX
  intro u hu
  rw [← h1] at hu
  refine Subgroup.closure_mono ?_ hu
  rintro c ⟨x, hx, w, hw, rfl⟩
  obtain ⟨γ, hγ⟩ := FLc.rhoOf_surj hπ x hx
  exact ⟨γ, w, hw, by rw [hγ]⟩

theorem indep_fin_one (I : Subgroup W) :
    ∀ i : Fin 1, (fun _ : Fin 1 => I) i ⊓ (⊥ ⊔ ⨆ (j : Fin 1) (_ : j ≠ i), (fun _ : Fin 1 => I) j) =
      ⊥ := by
  intro i
  have : (⨆ (j : Fin 1) (_ : j ≠ i), (fun _ : Fin 1 => I) j) = ⊥ :=
    iSup_eq_bot.2 fun j => iSup_eq_bot.2 fun hj => absurd (Subsingleton.elim j i) hj
  rw [this, bot_sup_eq, inf_bot_eq]

end Coords

section Finish

open CFSG.Open hiding StatedSL StatedSp
open CFSG.QuasithinUnique

variable {G : Type} [Group G]

theorem commutator_le_of_le_normalizer {U K : Subgroup G}
    (hKU : K ≤ Subgroup.normalizer (U : Set G)) : ⁅U, K⁆ ≤ U := by
  rw [Subgroup.commutator_le]
  intro u hu k hk
  rw [commutatorElement_def]
  have h1 : k * u⁻¹ * k⁻¹ ∈ U := (Subgroup.mem_normalizer_iff.1 (hKU hk) u⁻¹).1 (U.inv_mem hu)
  have e : u * k * u⁻¹ * k⁻¹ = u * (k * u⁻¹ * k⁻¹) := by group
  rw [e]
  exact U.mul_mem hu h1

theorem le_normalizer_of_commutator_eq {V P₀ : Subgroup G} (hVcomm : ⁅V, P₀⁆ = V) :
    P₀ ≤ Subgroup.normalizer (V : Set G) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro v
  refine ⟨fun hv => conj_mem_of_commutator_eq hVcomm hx hv, fun hv => ?_⟩
  have h1 := conj_mem_of_commutator_eq hVcomm (P₀.inv_mem hx) hv
  have e : x⁻¹ * (x * v * x⁻¹) * x⁻¹⁻¹ = v := by group
  rwa [e] at h1

variable {U V P₀ : Subgroup G} (hVU : V ≤ U) (hP₀V : P₀ ≤ Subgroup.normalizer (V : Set G))
  {n m : ℕ} (ρ : SpecialLinearGroup (Fin n) (ZMod 2) →* MulAut ↥U)
  (θ : ↥P₀ →* SpecialLinearGroup (Fin n) (ZMod 2))
  (hρθ : ∀ (x : ↥P₀) (u : ↥U), ((ρ (θ x) u : ↥U) : G) = x * u * (x : G)⁻¹)
  (α : ↥P₀ →* SpecialLinearGroup (Fin m) (ZMod 2)) (hα : Function.Surjective α)
  (hker : α.ker = CFSG.pCore 2 ↥P₀)

include hVU hP₀V hρθ hα hker

theorem finish_nat (hm2 : 2 ≤ m) (hV1 : V ≠ ⊥) {k : ℕ} (hk4 : k ≤ 4)
    (Ψ' : ↥(V.subgroupOf U) →* Multiplicative (Fin k → Fin m → ZMod 2))
    (hΨ' : Function.Injective Ψ')
    (hΨe : ∀ (x : ↥P₀) (v : ↥(V.subgroupOf U)) (hv : ρ (θ x) v ∈ V.subgroupOf U),
      Multiplicative.toAdd (Ψ' ⟨ρ (θ x) v, hv⟩) =
        diagAct ((α x : SpecialLinearGroup (Fin m) (ZMod 2)) : Matrix (Fin m) (Fin m) (ZMod 2))
          (Multiplicative.toAdd (Ψ' v))) :
    ∃ k, 1 ≤ k ∧ k ≤ 4 ∧
      IsSumOfNaturalModules P₀ V ⊥ (CFSG.pCore 2 ↥P₀) (StatedSL m (ZMod 2)) false k := by
  obtain ⟨Ψ, hΨi, -, hΨt⟩ := transfer hVU ρ θ hρθ Ψ'
  obtain ⟨k', hk', hk1, hS⟩ := isSumOfNaturalModules_of_inj hm2 hP₀V α hα hker Ψ (hΨi hΨ')
    fun a u v huv => by
      obtain ⟨e1, e2⟩ := hΨt a u v huv
      rw [e1, e2]
      exact hΨe a ⟨⟨u, hVU u.2⟩, u.2⟩ _
  exact ⟨k', hk1 hV1, hk'.trans hk4, hS⟩

theorem finish_dual (hm2 : 2 ≤ m) (hV1 : V ≠ ⊥)
    (Ψ' : ↥(V.subgroupOf U) →* Multiplicative (Fin 1 → Fin m → ZMod 2))
    (hΨ' : Function.Injective Ψ')
    (hΨe : ∀ (x : ↥P₀) (v : ↥(V.subgroupOf U)) (hv : ρ (θ x) v ∈ V.subgroupOf U),
      Multiplicative.toAdd (Ψ' ⟨ρ (θ x) v, hv⟩) =
        diagAct (((α x)⁻¹ : SpecialLinearGroup (Fin m) (ZMod 2)) :
          Matrix (Fin m) (Fin m) (ZMod 2))ᵀ (Multiplicative.toAdd (Ψ' v))) :
    ∃ k, 1 ≤ k ∧ k ≤ 4 ∧
      IsSumOfNaturalModules P₀ V ⊥ (CFSG.pCore 2 ↥P₀) (StatedSL m (ZMod 2)) false k := by
  obtain ⟨Ψ, hΨi, -, hΨt⟩ := transfer hVU ρ θ hρθ Ψ'
  obtain ⟨k', hk', hk1, hS⟩ := isSumOfNaturalModules_of_inj_dual hm2 hP₀V α hα hker Ψ
    (hΨi hΨ') fun a u v huv => by
      obtain ⟨e1, e2⟩ := hΨt a u v huv
      rw [e1, e2]
      exact hΨe a ⟨⟨u, hVU u.2⟩, u.2⟩ _
  exact ⟨k', hk1 hV1, hk'.trans (by norm_num), hS⟩

omit hα hker in
theorem finish_alt (α : ↥P₀ →* SpecialLinearGroup (Fin 4) (ZMod 2)) (hα : Function.Surjective α)
    (hker : α.ker = CFSG.pCore 2 ↥P₀) (hne : V.subgroupOf U ≠ ⊥)
    (hVinv : ∀ (x : ↥P₀), ∀ v ∈ V.subgroupOf U, ρ (θ x) v ∈ V.subgroupOf U)
    (Ψ' : ↥(V.subgroupOf U) →* Multiplicative (Fin 6 → ZMod 2)) (hΨ' : Function.Injective Ψ')
    (hΨe : ∀ (x : ↥P₀) (v : ↥(V.subgroupOf U)) (hv : ρ (θ x) v ∈ V.subgroupOf U),
      Multiplicative.toAdd (Ψ' ⟨ρ (θ x) v, hv⟩) =
        minors4 ((α x : SpecialLinearGroup (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ
          Multiplicative.toAdd (Ψ' v)) :
    IsAltNaturalSection P₀ V ⊥ (CFSG.pCore 2 ↥P₀) 8 := by
  let S : AddSubgroup (Fin 6 → ZMod 2) :=
    { carrier := {w | ∃ v, Multiplicative.toAdd (Ψ' v) = w}
      add_mem' := by
        rintro _ _ ⟨u, rfl⟩ ⟨v, rfl⟩
        exact ⟨u * v, by rw [map_mul, toAdd_mul]⟩
      zero_mem' := ⟨1, by rw [map_one, toAdd_one]⟩
      neg_mem' := by
        rintro _ ⟨u, rfl⟩
        exact ⟨u⁻¹, by rw [map_inv, toAdd_inv]⟩ }
  have hS : S ≠ ⊥ := by
    intro hS
    apply hne
    rw [eq_bot_iff]
    intro v hv
    have h1 : Multiplicative.toAdd (Ψ' ⟨v, hv⟩) ∈ S := ⟨⟨v, hv⟩, rfl⟩
    rw [hS, AddSubgroup.mem_bot] at h1
    have h2 : Ψ' ⟨v, hv⟩ = Ψ' 1 := by
      rw [map_one]
      exact Multiplicative.toAdd.injective h1
    exact congrArg Subtype.val (hΨ' h2)
  have hinv : ∀ g : SpecialLinearGroup (Fin 4) (ZMod 2), ∀ w ∈ S,
      minors4 (g : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ w ∈ S := by
    rintro g _ ⟨v, rfl⟩
    obtain ⟨x, rfl⟩ := hα g
    exact ⟨⟨ρ (θ x) v, hVinv x v v.2⟩, hΨe x v _⟩
  have htop := eq_top_of_minors4_invariant S hS hinv
  have hsurj : Function.Surjective Ψ' := by
    intro y
    have hy : Multiplicative.toAdd y ∈ S := by
      rw [htop]
      exact AddSubgroup.mem_top _
    obtain ⟨v, hv⟩ := hy
    exact ⟨v, Multiplicative.toAdd.injective hv⟩
  obtain ⟨Ψ, hΨi, hΨs, hΨt⟩ := transfer hVU ρ θ hρθ Ψ'
  exact isAltNaturalSection_of_minors4 hP₀V α hα hker Ψ ⟨hΨi hΨ', hΨs hsurj⟩
    fun a u v huv => by
      obtain ⟨e1, e2⟩ := hΨt a u v huv
      rw [e1, e2]
      exact hΨe a ⟨⟨u, hVU u.2⟩, u.2⟩ _

end Finish

section Cases

open CFSG.Open hiding StatedSL StatedSp
open CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G] {K U P P₀ V : Subgroup G} (hU : IsElemAbelian 2 U)
  (hKU : K ≤ Subgroup.normalizer (U : Set G))
  (hCK : K ⊓ Subgroup.centralizer (U : Set G) ≤ pCoreOf 2 K)
  (hpar : IsParabolic2 K P) (hPK : P ≠ K) (hP₀P : P₀ ≤ P)
  (hPN : P ≤ Subgroup.normalizer (P₀ : Set G)) (hperf : ⁅P₀, P₀⁆ = P₀)
  {m : ℕ} (hm : m = 3 ∨ m = 4) (hpm : IsPSL m 2 1 (ModO2 P₀))
  (hV1 : V ≠ ⊥) (hVU : V ≤ U) (hVO : V ≤ Subgroup.centralizer (pCoreOf 2 P₀ : Set G))
  (hVcomm : ⁅V, P₀⁆ = V)
  (hVL : V.subgroupOf U ≤ @commV ↥U (commGroupOfElemAbelian hU) (autOn K U))

include hKU hCK hpar hPK hP₀P hPN hperf hm hpm hV1 hVU hVO hVcomm hVL

theorem case_ext5
    (h5 : @SLExteriorTwo ↥U (commGroupOfElemAbelian hU) (autOn K U)
      (@commV ↥U (commGroupOfElemAbelian hU) (autOn K U)) ⊥ 5) :
    (∃ k, 1 ≤ k ∧ k ≤ 4 ∧
      IsSumOfNaturalModules P₀ V ⊥ (CFSG.pCore 2 ↥P₀) (StatedSL m (ZMod 2)) false k) ∨
        (m = 4 ∧ IsAltNaturalSection P₀ V ⊥ (CFSG.pCore 2 ↥P₀) 8) := by
  classical
  let _ : CommGroup ↥U := commGroupOfElemAbelian hU
  obtain ⟨π, hπ⟩ := h5
  have hπb : Function.Bijective π :=
    ⟨injective_of_realizesVia (G64.extSq_faithful (by norm_num)) hπ, hπ.1⟩
  obtain ⟨g, a, hamn, α, θ, hαs, hker, hblk, hρθ, ctx⟩ :=
    reduction hU hKU hCK hpar hPK hP₀P hPN hperf hm hpm hV1 hVU hVO hVcomm (by norm_num) le_rfl
      π hπb
  have hπ' := B69.realizesVia_conj_of_isActionModel (FFModel.extSq_isActionModel (ZMod 2) 5) hπ
    (specialLinearGroupEquivStatedSL 5 (ZMod 2) g)
  obtain ⟨Φ, hΦalt, hΦinj, -, hΦ⟩ := ext5Coords hπ'
  have hP₀V := le_normalizer_of_commutator_eq hVcomm
  obtain ⟨hm3, -, hprop, hA, hVA, hgen, hcross, hne⟩ := ctx
  rcases (by omega : a = 0 ∨ a = 1 ∨ a = 2) with rfl | rfl | rfl
  · rcases hm with rfl | rfl
    · obtain ⟨Ψ', hΨ'i, hΨ'e⟩ :=
        extSq_zero_three hΦalt hΦinj hΦ hVL (A := θ.range) hamn hcross
      left
      refine finish_dual hVU hP₀V _ θ hρθ α hαs hker (by norm_num) hV1 Ψ' hΨ'i fun x v hv => ?_
      refine (hΨ'e (θ x) ⟨x, rfl⟩ v hv).trans ?_
      rw [hblk x, ← Matrix.SpecialLinearGroup.coe_inv]
    · obtain ⟨Ψ', hΨ'i, hΨ'e⟩ :=
        extSq_zero_four hΦalt hΦinj hΦ hVL (A := θ.range) hamn hcross
      right
      refine ⟨rfl, finish_alt hVU hP₀V _ θ hρθ α hαs hker hne
        (fun x v hv => hVA _ ⟨x, rfl⟩ v hv) Ψ' hΨ'i fun x v hv => ?_⟩
      refine (hΨ'e (θ x) ⟨x, rfl⟩ v hv).trans ?_
      rw [hblk x]
  · obtain ⟨Ψ', hΨ'i, hΨ'e⟩ := extSq_one hΦalt hΦinj hΦ hVL (by omega) hamn hA hcross
    left
    refine finish_nat hVU hP₀V _ θ hρθ α hαs hker (by omega) hV1 (by norm_num) Ψ' hΨ'i
      fun x v hv => ?_
    refine (hΨ'e (θ x) ⟨x, rfl⟩ v hv).trans ?_
    rw [hblk x]
  · exact absurd (eq_bot_of_forall_fixed hgen
      (extSq_two hΦalt hΦinj hΦ hVL (by omega) hA hVA hcross)) hne

theorem case_ext4 {Z : Subgroup ↥U}
    (hZ : Z ≤ @fixV ↥U (commGroupOfElemAbelian hU) (autOn K U) ⊓
      @commV ↥U (commGroupOfElemAbelian hU) (autOn K U))
    (hZ2 : Nat.card Z ≤ 2)
    (h4 : @SLExteriorTwo ↥U (commGroupOfElemAbelian hU) (autOn K U)
      (@commV ↥U (commGroupOfElemAbelian hU) (autOn K U)) Z 4) :
    (∃ k, 1 ≤ k ∧ k ≤ 4 ∧
      IsSumOfNaturalModules P₀ V ⊥ (CFSG.pCore 2 ↥P₀) (StatedSL m (ZMod 2)) false k) ∨
        (m = 4 ∧ IsAltNaturalSection P₀ V ⊥ (CFSG.pCore 2 ↥P₀) 8) := by
  classical
  have hW2 : ∀ w : ↥U, w ^ 2 = 1 := fun w => Subtype.ext (hU.2 w w.2)
  let _ : CommGroup ↥U := commGroupOfElemAbelian hU
  obtain ⟨π, hπ⟩ := h4
  have hπb : Function.Bijective π :=
    ⟨injective_of_realizesVia (G64.extSq_faithful (by norm_num)) hπ, hπ.1⟩
  obtain ⟨g, a, hamn, α, θ, hαs, hker, hblk, hρθ, ctx⟩ :=
    reduction hU hKU hCK hpar hPK hP₀P hPN hperf hm hpm hV1 hVU hVO hVcomm le_rfl (by norm_num)
      π hπb
  have hπ' := B69.realizesVia_conj_of_isActionModel (FFModel.extSq_isActionModel (ZMod 2) 4) hπ
    (specialLinearGroupEquivStatedSL 4 (ZMod 2) g)
  obtain ⟨q, hqs, hqk, hinv, hqe⟩ := ext4Coords hπ'
  have hP₀V := le_normalizer_of_commutator_eq hVcomm
  obtain ⟨hm3, -, hprop, hA, hVA, hgen, hcross, hne⟩ := ctx
  obtain rfl : m = 3 := by omega
  have hZpos : 0 < Nat.card Z := Nat.card_pos
  rcases (by omega : Nat.card Z = 1 ∨ Nat.card Z = 2) with hZ1 | hZ2'
  · obtain rfl : Z = ⊥ := Subgroup.eq_bot_of_card_eq Z hZ1
    obtain ⟨Φ, hΦalt, hΦinj, hΦ⟩ := alt4Coords q hqk hqe
    rcases (by omega : a = 0 ∨ a = 1) with rfl | rfl
    · obtain ⟨Ψ', hΨ'i, hΨ'e⟩ :=
        extSq_zero_three hΦalt hΦinj hΦ hVL (A := θ.range) hamn hcross
      left
      refine finish_dual hVU hP₀V _ θ hρθ α hαs hker (by norm_num) hV1 Ψ' hΨ'i fun x v hv => ?_
      refine (hΨ'e (θ x) ⟨x, rfl⟩ v hv).trans ?_
      rw [hblk x, ← Matrix.SpecialLinearGroup.coe_inv]
    · obtain ⟨Ψ', hΨ'i, hΨ'e⟩ := extSq_one hΦalt hΦinj hΦ hVL (by norm_num) hamn hA hcross
      left
      refine finish_nat hVU hP₀V _ θ hρθ α hαs hker (by norm_num) hV1 (by norm_num) Ψ' hΨ'i
        fun x v hv => ?_
      refine (hΨ'e (θ x) ⟨x, rfl⟩ v hv).trans ?_
      rw [hblk x]
  · exfalso
    have hZL : Z ≤ @commV ↥U (commGroupOfElemAbelian hU) (autOn K U) := fun z hz => (hZ hz).2
    have hcomm := commV_le_closure (by norm_num) hπ'.1
    apply hne
    refine eq_bot_of_forall_fixed hgen fun t _ v hv => ?_
    have hvZ : v ∈ Z := by
      rcases (by omega : a = 0 ∨ a = 1) with rfl | rfl
      · refine cover_fixed_031 hW2 hZL hZ2' hinv (fun γ w hw => (hZ hw).1 _ (FLc.rhoOf_mem _ γ))
          hqs hqk hqe hcomm (hVL hv) fun i => ?_
        fin_cases i
        · exact hcross 0 3 (Or.inr ⟨by decide, by decide, by decide⟩) v hv
        · exact hcross 1 3 (Or.inr ⟨by decide, by decide, by decide⟩) v hv
        · exact hcross 2 3 (Or.inr ⟨by decide, by decide, by decide⟩) v hv
      · refine cover_fixed_130 hW2 hZL hZ2' hinv (fun γ w hw => (hZ hw).1 _ (FLc.rhoOf_mem _ γ))
          hqs hqk hqe hcomm (hVL hv) fun i => ?_
        fin_cases i
        · exact hcross 0 1 (Or.inl ⟨by decide, by decide, by decide⟩) v hv
        · exact hcross 0 2 (Or.inl ⟨by decide, by decide, by decide⟩) v hv
        · exact hcross 0 3 (Or.inl ⟨by decide, by decide, by decide⟩) v hv
    exact (hZ hvZ).1 _ (FLc.rhoOf_mem _ t)

theorem case_natDual {n : ℕ}
    (hnd : @SumNatDual ↥U (commGroupOfElemAbelian hU) (autOn K U)
      (@commV ↥U (commGroupOfElemAbelian hU) (autOn K U)) n) :
    (∃ k, 1 ≤ k ∧ k ≤ 4 ∧
      IsSumOfNaturalModules P₀ V ⊥ (CFSG.pCore 2 ↥P₀) (StatedSL m (ZMod 2)) false k) ∨
        (m = 4 ∧ IsAltNaturalSection P₀ V ⊥ (CFSG.pCore 2 ↥P₀) 8) := by
  classical
  let _ : CommGroup ↥U := commGroupOfElemAbelian hU
  obtain ⟨hn, π, U₁, U₂, ⟨hsup, hinf⟩, h₁, h₂⟩ := hnd
  obtain ⟨β₀, -, hβ₀s, hinv₀, hβ₀e, hπs⟩ := natCoords h₁
  have hπb : Function.Bijective π := ⟨injective_of_natCoords β₀ hβ₀s hinv₀ hβ₀e, hπs⟩
  obtain ⟨g, a, hamn, α, θ, hαs, hker, hblk, hρθ, ctx⟩ :=
    reduction hU hKU hCK hpar hPK hP₀P hPN hperf hm hpm hV1 hVU hVO hVcomm (by omega) (by omega)
      π hπb
  have h₁' := B69.realizesVia_conj_of_isActionModel (FFModel.nat_isActionModel _) h₁
    (specialLinearGroupEquivStatedSL n (ZMod 2) g)
  have h₂' := B69.realizesVia_conj_of_isActionModel (FFModel.dualNat_isActionModel _) h₂
    (specialLinearGroupEquivStatedSL n (ZMod 2) g)
  obtain ⟨β₁, hβ₁i, -, hinv₁, hβ₁e, -⟩ := natCoords h₁'
  obtain ⟨β₂, hβ₂i, -, hinv₂, hβ₂e⟩ := dualCoords h₂'
  have hP₀V := le_normalizer_of_commutator_eq hVcomm
  obtain ⟨hm3, -, hprop, hA, hVA, hgen, hcross, hne⟩ := ctx
  have hVU' : V.subgroupOf U ≤ U₁ ⊔ U₂ := by
    rw [hsup]
    exact hVL
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · have hV₁ := natDual_zero_le (by omega) (by omega) hA hinf hinv₁ hinv₂ hβ₂i hβ₂e hVU' hgen
      hcross
    obtain ⟨Ψ', hΨ'i, hΨ'e⟩ := natSum_zero (k := 1) (by omega) hamn hA (fun _ => U₁)
      (indep_fin_one U₁) (fun _ => hinv₁) (fun _ => β₁) (fun _ => hβ₁i) (fun _ => hβ₁e)
      (hV₁.trans (le_iSup (fun _ : Fin 1 => U₁) 0)) hcross
    left
    refine finish_nat hVU hP₀V _ θ hρθ α hαs hker (by omega) hV1 (by norm_num) Ψ' hΨ'i
      fun x v hv => ?_
    refine (hΨ'e (θ x) ⟨x, rfl⟩ v hv).trans ?_
    rw [hblk x]
  · rcases (by omega : a + m = n ∨ a + m < n) with hlast | hmid
    · have hV₂ := natDual_last_le ha (by omega) hlast hA hinf hinv₁ hinv₂ hβ₁i hβ₁e hVU' hgen
        hcross
      obtain ⟨Ψ', hΨ'i, hΨ'e⟩ := dualSingle_last (by omega) hamn hlast hA hβ₂i hβ₂e hV₂ hcross
      left
      refine finish_dual hVU hP₀V _ θ hρθ α hαs hker (by omega) hV1 Ψ' hΨ'i fun x v hv => ?_
      refine (hΨ'e (θ x) ⟨x, rfl⟩ v hv).trans ?_
      rw [← map_inv θ, hblk, map_inv α]
    · exact absurd (eq_bot_of_forall_fixed hgen (natDual_mid ha (by omega) hmid hA hinf hinv₁
        hinv₂ hβ₁i hβ₁e hβ₂i hβ₂e hVU' hcross)) hne

theorem case_natSum {n k : ℕ} (hn : n = 4 ∨ n = 5) (hk1 : 1 ≤ k) (hkn : k ≤ n - 1)
    (hds : @DirectSumOfCopies ↥U (commGroupOfElemAbelian hU) (autOn K U)
      (@commV ↥U (commGroupOfElemAbelian hU) (autOn K U)) ⊥
        (FFModel.nat (StatedSL n (ZMod 2))) k) :
    (∃ k, 1 ≤ k ∧ k ≤ 4 ∧
      IsSumOfNaturalModules P₀ V ⊥ (CFSG.pCore 2 ↥P₀) (StatedSL m (ZMod 2)) false k) ∨
        (m = 4 ∧ IsAltNaturalSection P₀ V ⊥ (CFSG.pCore 2 ↥P₀) 8) := by
  classical
  let _ : CommGroup ↥U := commGroupOfElemAbelian hU
  obtain ⟨I, π, -, hind, hsup, hreal⟩ := hds
  obtain ⟨β₀, -, hβ₀s, hinv₀, hβ₀e, hπs⟩ := natCoords (hreal ⟨0, hk1⟩)
  have hπb : Function.Bijective π := ⟨injective_of_natCoords β₀ hβ₀s hinv₀ hβ₀e, hπs⟩
  obtain ⟨g, a, hamn, α, θ, hαs, hker, hblk, hρθ, ctx⟩ :=
    reduction hU hKU hCK hpar hPK hP₀P hPN hperf hm hpm hV1 hVU hVO hVcomm (by omega) (by omega)
      π hπb
  have hreal' := fun i => B69.realizesVia_conj_of_isActionModel (FFModel.nat_isActionModel _)
    (hreal i) (specialLinearGroupEquivStatedSL n (ZMod 2) g)
  choose β hβ using fun i => natCoords (hreal' i)
  have hP₀V := le_normalizer_of_commutator_eq hVcomm
  obtain ⟨hm3, -, hprop, hA, hVA, hgen, hcross, hne⟩ := ctx
  have hVU' : V.subgroupOf U ≤ ⨆ i, I i := by
    rw [← bot_sup_eq (⨆ i, I i), hsup]
    exact hVL
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · obtain ⟨Ψ', hΨ'i, hΨ'e⟩ := natSum_zero (by omega) hamn hA I hind (fun i => (hβ i).2.2.1) β
      (fun i => (hβ i).1) (fun i => (hβ i).2.2.2.1) hVU' hcross
    left
    refine finish_nat hVU hP₀V _ θ hρθ α hαs hker (by omega) hV1 (by omega) Ψ' hΨ'i
      fun x v hv => ?_
    refine (hΨ'e (θ x) ⟨x, rfl⟩ v hv).trans ?_
    rw [hblk x]
  · exact absurd (eq_bot_of_forall_fixed hgen (natSum_pos ha (by omega) hA I hind
      (fun i => (hβ i).2.2.1) β (fun i => (hβ i).1) (fun i => (hβ i).2.2.2.1) hVU' hcross)) hne

end Cases

end CFSG.Quasithin.C48Pf.FMod

namespace CFSG.Quasithin.C48Pf

open CFSG.Open hiding StatedSL StatedSp
open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank FMod

theorem fourModFact_holds : FourModFact := by
  intro G _ _ K U P P₀ V hU hKU hCK _ halt hpar hPK hP₀P hPN hperf m hm hpm hV1 hVUK hVO hVcomm
  have hVU : V ≤ U := hVUK.trans (commutator_le_of_le_normalizer hKU)
  have hVL : V.subgroupOf U ≤ @commV ↥U (commGroupOfElemAbelian hU) (autOn K U) := by
    have : IsMulCommutative ↥U := hU.1
    rw [commV_autOn_eq1527d hKU]
    intro v hv
    exact Subgroup.mem_subgroupOf.2 (hVUK (Subgroup.mem_subgroupOf.1 hv))
  rcases halt with ⟨Z, hZ, hZ2, h4⟩ | h5 | ⟨n, hnd⟩ | ⟨n, hn, k, hk1, hkn, hds⟩
  · exact case_ext4 hU hKU hCK hpar hPK hP₀P hPN hperf hm hpm hV1 hVU hVO hVcomm hVL hZ hZ2 h4
  · exact case_ext5 hU hKU hCK hpar hPK hP₀P hPN hperf hm hpm hV1 hVU hVO hVcomm hVL h5
  · exact case_natDual hU hKU hCK hpar hPK hP₀P hPN hperf hm hpm hV1 hVU hVO hVcomm hVL hnd
  · exact case_natSum hU hKU hCK hpar hPK hP₀P hPN hperf hm hpm hV1 hVU hVO hVcomm hVL hn hk1
      hkn hds

end CFSG.Quasithin.C48Pf
