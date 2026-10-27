module

public import CFSG.Quasithin.Background.SmithB42G2FOff
public import CFSG.Quasithin.Background.SmithB42G2Prop
public import CFSG.Quasithin.Background.SmithB42L2Sl2
public import CFSG.Quasithin.Background.SmithB42G2FNat

public section

namespace CFSG.Quasithin

namespace B42G2F

open CFSG.Open CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.B42G2Ten
open CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.Layer CFSG.QuasithinUnique.Setup.Layer.Actor
  CFSG.QuasithinUnique.Setup.X7b

section Real

variable {W : Type} [CommGroup W] {L : Subgroup (MulAut W)} {K : Type} [Field K] [Finite K]
  [CharP K 2]

theorem g2Natural_of_coords {f : ℕ} (hK : Nat.card K = 2 ^ f) (θL : ↥L ≃* ↥(cayleyGroup K))
    (φ : W → (Ix3 → K)) (hmul : ∀ u v, φ (u * v) = φ u + φ v) (hinj : Function.Injective φ)
    (hsurj : Function.Surjective φ)
    (hact : ∀ (l : ↥L) (w : W), φ ((l : MulAut W) w) = g2Act (θL l) (φ w)) :
    G2Natural L ⊤ ⊥ f := by
  classical
  have hq := CFSG.Quasithin.G11.P3G2.quasithinG2_eq_cayleyGroup (K := K)
  let ε : ↥(quasithinG2 K) ≃* ↥(cayleyGroup K) := MulEquiv.subgroupCongr hq
  let π' : ↥(quasithinG2 K) →* ↥L := (ε.trans θL.symm).toMonoidHom
  have hπ' : ∀ γ, θL (π' γ) = ε γ := fun γ => by
    change θL (θL.symm (ε γ)) = ε γ
    rw [MulEquiv.apply_symm_apply]
  set e := zornSecEquiv (F := K) (quasithinG2 K) with he
  have hφ1 : φ 1 = 0 := by
    have h := hmul 1 1
    rw [one_mul] at h
    exact (left_eq_add.mp h)
  let β : ↥(⊤ : Subgroup W) →* (FFModel.zornQ (quasithinG2 K)).Sec :=
    { toFun := fun u => e.symm (Multiplicative.ofAdd (φ u))
      map_one' := by
        change e.symm (Multiplicative.ofAdd (φ 1)) = 1
        rw [hφ1, ofAdd_zero, map_one]
      map_mul' := fun u v => by
        change e.symm (Multiplicative.ofAdd (φ (u * v))) =
          e.symm (Multiplicative.ofAdd (φ u)) * e.symm (Multiplicative.ofAdd (φ v))
        rw [hmul, ofAdd_add, map_mul] }
  have hβ : ∀ u, e (β u) = Multiplicative.ofAdd (φ u) := fun u => e.apply_symm_apply _
  refine ⟨K, inferInstance, inferInstance, hK, π', ?_⟩
  refine ⟨(ε.trans θL.symm).surjective, bot_le, zornR_le_zornO0, fun _ _ _ => trivial,
    fun h z hz => by
      rw [Subgroup.mem_bot] at hz ⊢
      rw [hz, map_one],
    fun γ m hm => zornAct_mem_O0 (quasithinG2 K) le_rfl γ hm,
    fun γ m hm => zornAct_mem_R (quasithinG2 K) le_rfl γ hm, β, ?_, ?_, ?_⟩
  ·
    intro q
    obtain ⟨u, hu⟩ := hsurj (Multiplicative.toAdd (e q))
    refine ⟨⟨u, trivial⟩, ?_⟩
    apply e.injective
    rw [hβ]
    change Multiplicative.ofAdd (φ u) = e q
    rw [hu]
    rfl
  ·
    intro u
    rw [Subgroup.mem_bot]
    constructor
    · intro h
      have h1 : Multiplicative.ofAdd (φ u) = 1 := by rw [← hβ, h, map_one]
      have h2 : φ u = φ 1 := by rw [hφ1]; exact h1
      exact hinj h2
    · intro h
      have h1 : u = 1 := Subtype.ext h
      rw [h1, map_one]
  ·
    intro γ u m hu hm hum
    apply e.injective
    rw [hβ]
    have h1 : Multiplicative.ofAdd (φ u) = e (QuotientGroup.mk m) := by rw [← hβ, hum]
    have h2 : φ u = zP (Multiplicative.toAdd m.1) := h1
    change Multiplicative.ofAdd (φ (((π' γ : ↥L) : MulAut W) (u : W))) =
      Multiplicative.ofAdd (zP (Multiplicative.toAdd (zornAct (quasithinG2 K) γ m.1)))
    rw [hact, h2]
    have h3 : θL (π' γ) = ε γ := hπ' γ
    simp only [h3]
    congr 1
    exact (g2_zP_apply (ε γ) _ m.2).symm

end Real

section Module

variable {K : Type} [Field K] [Fintype K] [CharP K 2]
variable {M : Type} [AddCommGroup M] [Module (ZMod 2) M] [Finite M]

omit [Fintype K] in
theorem tL_one_ne_one : (CFSG.Quasithin.Vol2.Ch11.G2Q8.tL (1 : K)) ≠ 1 := by
  intro h
  have h1 := congrArg (fun g => g2Act g (q6 0 0 1 0 0 0)) h
  simp only [CFSG.Quasithin.Vol2.Ch11.G2Q8.g2Act_tL, map_one, AddMonoid.End.coe_one, id_eq,
    mul_one, mul_zero, add_zero, zero_add] at h1
  have := (q6_inj h1).1
  exact one_ne_zero this

theorem exists_natural_of_offender {f : ℕ} (hK : Fintype.card K = 2 ^ f) (hf : 2 ≤ f)
    (π : ↥(cayleyGroup K) →* (M ≃ₗ[ZMod 2] M)) (hπ : Function.Injective π) (hnt : Nontrivial M)
    (hirr : ∀ U : Submodule (ZMod 2) M, (∀ g, ∀ u ∈ U, π g u ∈ U) → U = ⊥ ∨ U = ⊤)
    (A : Subgroup (M ≃ₗ[ZMod 2] M)) (hnorm : ∀ a ∈ A, ∀ x, ∃ y, a * π x * a⁻¹ = π y)
    (hAe : CFSG.IsElementaryAbelian 2 A) (hA1 : A ≠ ⊥)
    (hoff : Nat.card M ≤ Nat.card A * Nat.card {m : M // ∀ a ∈ A, a m = m}) :
    ∃ φ : M ≃+ (Ix3 → K), ∀ g w, φ (π g w) = g2Act g (φ w) := by
  let ρ : Representation (ZMod 2) ↥(cayleyGroup K) M :=
    (LinearEquiv.automorphismGroup.toLinearMapMonoidHom (R := ZMod 2) (M := M)).comp π
  have : Fact ρ.IsIrreducible :=
    ⟨(CFSG.QuasithinUnique.Setup.X7.isIrreducible_iff ρ).mpr ⟨hnt, hirr⟩⟩
  have hρnt : ∃ g, ρ g ≠ 1 := by
    refine ⟨CFSG.Quasithin.Vol2.Ch11.G2Q8.tL (1 : K), fun h => tL_one_ne_one (hπ ?_)⟩
    rw [map_one]
    exact LinearEquiv.toLinearMap_injective (h.trans rfl)
  rcases natural_or_large_displacement (ρ := ρ) hK (by omega) hρnt with ⟨φ, hφ⟩ | hdisp
  · exact ⟨φ, fun g w => hφ g w⟩
  · exact absurd hoff (not_le.mpr (g2_card_mul_card_fixed_lt hK hf π hπ hnt hirr
      (fun z hz hz1 => hdisp z hz hz1) A hnorm hAe hA1))

end Module

end B42G2F

open CFSG.Open CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall
open CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.Layer CFSG.QuasithinUnique.Setup.Layer.Actor

theorem gm04G2EvenFFNatural_holds : GM04G2EvenFFNatural := by
  intro W _ _ hW L f hf hZ hmodel hirr E hEN hE1 hEel hcard
  classical
  obtain ⟨-, K, _, _, _, hK, ⟨θL⟩⟩ :=
    CFSG.Quasithin.B42G2Id.exists_cayleyGroup_of_model_center_eq_bot hZ hmodel
  have : Fintype K := Fintype.ofFinite K
  have hKf : Fintype.card K = 2 ^ f := by rw [← Nat.card_eq_fintype_card]; exact hK
  have hW' : ∀ w : W, w * w = 1 := fun w => by rw [← pow_two]; exact hW w
  obtain ⟨M, _, _, _, ⟨θ⟩⟩ := exists_binModel_of_binary hW'
  set ψ := binPsi θ with hψ
  let πM : ↥(cayleyGroup K) →* (M ≃ₗ[ZMod 2] M) :=
    ψ.toMonoidHom.comp (L.subtype.comp θL.symm.toMonoidHom)
  have hπM : ∀ g, πM g = ψ ((θL.symm g : ↥L) : MulAut W) := fun g => rfl
  have hπinj : Function.Injective πM := fun g g' h => by
    have h1 := ψ.injective h
    exact θL.symm.injective (Subtype.ext h1)
  have hirrW := CFSG.QuasithinUnique.Bridge.TypeList.irr_of_isIrrSec hirr
  have hirrM : ∀ U : Submodule (ZMod 2) M, (∀ g, ∀ u ∈ U, πM g u ∈ U) → U = ⊥ ∨ U = ⊤ := by
    intro U hU
    refine B42L2.irr_map θ hirrW U fun x hx u hu => ?_
    obtain ⟨l, hl, rfl⟩ := hx
    have h1 := hU (θL ⟨l, hl⟩) u hu
    rwa [hπM, MulEquiv.symm_apply_apply] at h1
  have hntM : Nontrivial M := by
    obtain ⟨v, -, hv⟩ := IsConcreteLE.exists_of_lt hirr.1
    replace hv : v ≠ 1 := fun h => hv (h ▸ Subgroup.one_mem _)
    refine ⟨⟨Multiplicative.toAdd (θ v), 0, fun h => hv ?_⟩⟩
    have h1 : θ v = 1 := Multiplicative.toAdd.injective (by simpa using h)
    simpa using congrArg θ.symm h1
  set A₀ := E.map ψ.toMonoidHom with hA₀
  have hnorm : ∀ a ∈ A₀, ∀ x, ∃ y, a * πM x * a⁻¹ = πM y := by
    rintro _ ⟨a, ha, rfl⟩ x
    have hl : a * ((θL.symm x : ↥L) : MulAut W) * a⁻¹ ∈ L :=
      (Subgroup.mem_normalizer_iff.mp (hEN ha) _).mp (θL.symm x).2
    refine ⟨θL ⟨_, hl⟩, ?_⟩
    rw [hπM (θL _), MulEquiv.symm_apply_apply, hπM x]
    change ψ a * ψ ((θL.symm x : ↥L) : MulAut W) * (ψ a)⁻¹ =
      ψ (a * ((θL.symm x : ↥L) : MulAut W) * a⁻¹)
    rw [map_mul, map_mul, map_inv]
  have hAe : CFSG.IsElementaryAbelian 2 ↥A₀ := (isElemAbelian2_iff_map θ E).1 hEel
  have hA1 : A₀ ≠ ⊥ := by
    rw [hA₀, Ne, Subgroup.map_eq_bot_iff_of_injective E ψ.injective]
    exact hE1
  have hoff : Nat.card M ≤ Nat.card A₀ * Nat.card {m : M // ∀ a ∈ A₀, a m = m} := by
    have h1 := weight_map θ E
    rw [natCard_eq θ] at hcard
    calc Nat.card M ≤ Nat.card E * Nat.card (fixV E) := hcard
      _ = _ := h1.symm
  obtain ⟨φ, hφ⟩ := B42G2F.exists_natural_of_offender hKf hf πM hπinj hntM hirrM A₀ hnorm hAe hA1
    hoff
  refine B42G2F.g2Natural_of_coords hK θL (fun w => φ (Multiplicative.toAdd (θ w)))
    (fun u v => by rw [map_mul, toAdd_mul, map_add]) (fun u v h => ?_) (fun x => ?_)
    (fun l w => ?_)
  · have h1 := φ.injective h
    exact θ.injective (Multiplicative.toAdd.injective h1)
  · refine ⟨θ.symm (Multiplicative.ofAdd (φ.symm x)), ?_⟩
    simp
  · have h1 := hφ (θL l) (Multiplicative.toAdd (θ w))
    rw [hπM, MulEquiv.symm_apply_apply, B42L2.toAdd_binPsi] at h1
    exact h1

end CFSG.Quasithin
