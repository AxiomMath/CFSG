module

public import CFSG.Quasithin.H13.A5W1623Rg
public import CFSG.Quasithin.Background.FLcModel
public import CFSG.Quasithin.H13.A5W1623a
public import CFSG.Quasithin.H13.A5Y1367c

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open hiding StatedSL StatedSp StatedProj
open CFSG.QuasithinUnique CFSG.Quasithin
open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag.BinaryParabolic

theorem reflection_eq_of_eq {n i j : ℕ} (h : i = j) (hi : 1 ≤ i) (hin : i < n) (hj : 1 ≤ j)
    (hjn : j < n) : reflection n (ZMod 2) i hi hin = reflection n (ZMod 2) j hj hjn := by
  subst h
  rfl

section Twist

variable {G : Type} [Group G] [Finite G] {K W : Subgroup G}

omit [Finite G] in
theorem exists_mulEquiv_autOn (hKW : K ≤ Subgroup.normalizer (W : Set G)) {H : Type} [Group H]
    {α : ↥K →* H} (hαs : Function.Surjective α)
    (hαC : ∀ k : ↥K, α k = 1 ↔ (k : G) ∈ Subgroup.centralizer (W : Set G)) :
    ∃ e : ↥(autOn K W) ≃* H, ∀ k, e (InternalSec.autOnHom hKW k) = α k := by
  set φ := InternalSec.autOnHom hKW with hφ
  have hφs : Function.Surjective φ := InternalSec.autOnHom_surjective hKW
  have hker : φ.ker ≤ α.ker := fun k hk =>
    (hαC k).mpr ((InternalSec.mem_ker_autOnHom hKW k).mp hk)
  set ab : ↥(autOn K W) →* H := φ.liftOfSurjective hφs ⟨α, hker⟩ with hab_def
  have hab : ∀ k, ab (φ k) = α k := fun k => by
    rw [hab_def]
    exact MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ k
  have habi : Function.Injective ab := by
    rw [injective_iff_map_eq_one]
    intro y hy
    obtain ⟨k, rfl⟩ := hφs y
    rw [hab] at hy
    exact (InternalSec.mem_ker_autOnHom hKW k).mpr ((hαC k).mp hy)
  have habs : Function.Surjective ab := by
    intro y
    obtain ⟨k, rfl⟩ := hαs y
    exact ⟨φ k, hab k⟩
  exact ⟨MulEquiv.ofBijective ab ⟨habi, habs⟩, hab⟩

omit [Finite G] in
theorem exists_conj_form (hKW : K ≤ Subgroup.normalizer (W : Set G))
    {α : ↥K →* SpecialLinearGroup (Fin 4) (ZMod 2)} (hαs : Function.Surjective α)
    (hαC : ∀ k : ↥K, α k = 1 ↔ (k : G) ∈ Subgroup.centralizer (W : Set G))
    {ρ : SpecialLinearGroup (Fin 4) (ZMod 2) →* MulAut ↥W} (hρN : ∀ x, ρ x ∈ autOn K W)
    (hρs : ∀ n ∈ autOn K W, ∃ x, ρ x = n) (hρi : Function.Injective ρ) :
    ∃ g u : SpecialLinearGroup (Fin 4) (ZMod 2), u ∈ unitriangular 4 (ZMod 2) ∧
      ((∀ (x : SpecialLinearGroup (Fin 4) (ZMod 2)) (k : ↥K),
          ρ (g * x * g⁻¹) = ((InternalSec.autOnHom hKW k : ↥(autOn K W)) : MulAut ↥W) ↔
            α k = u * x * u⁻¹) ∨
        ∀ (x : SpecialLinearGroup (Fin 4) (ZMod 2)) (k : ↥K),
          ρ (g * x * g⁻¹) = ((InternalSec.autOnHom hKW k : ↥(autOn K W)) : MulAut ↥W) ↔
            α k = graphAut 4 (u * x * u⁻¹)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set φ := InternalSec.autOnHom hKW with hφ
  obtain ⟨e, he⟩ := exists_mulEquiv_autOn hKW hαs hαC
  set ab : ↥(autOn K W) →* SpecialLinearGroup (Fin 4) (ZMod 2) := e.toMonoidHom with hab_def
  have hab : ∀ k, ab (φ k) = α k := fun k => he k
  have habi : Function.Injective ab := e.injective
  set ρN : SpecialLinearGroup (Fin 4) (ZMod 2) →* ↥(autOn K W) := ρ.codRestrict _ hρN with hρN'
  set θ := ab.comp ρN with hθdef
  have hθ : ∀ x (k : ↥K), ρ x = ((φ k : ↥(autOn K W)) : MulAut ↥W) ↔ θ x = α k := by
    intro x k
    constructor
    · intro h
      have h1 : ρN x = φ k := Subtype.ext h
      show ab (ρN x) = α k
      rw [h1, hab]
    · intro h
      have h1 : ab (ρN x) = ab (φ k) := by rw [hab]; exact h
      exact congrArg Subtype.val (habi h1)
  have hθi : Function.Injective θ := fun x y h => hρi (congrArg Subtype.val (habi h))
  have hθs : Function.Surjective θ := by
    intro y
    obtain ⟨k, rfl⟩ := hαs y
    obtain ⟨x, hx⟩ := hρs _ (φ k).2
    exact ⟨x, (hθ x k).mp hx⟩
  have hsylU := Ln2P.isSylowTwoOf_unitriangular_four
  set P := (unitriangular 4 (ZMod 2)).comap θ with hP
  have hP2 : IsPGroup 2 ↥P := hsylU.2.1.comap_of_injective θ hθi
  have hPi : ¬ 2 ∣ P.index := by
    rw [hP, Subgroup.index_comap_of_surjective _ hθs]
    have h := hsylU.2.2
    rwa [show ((unitriangular 4 (ZMod 2)).subgroupOf ⊤).index =
      (unitriangular 4 (ZMod 2)).index from Subgroup.relIndex_top_right _] at h
  obtain ⟨g, hg⟩ := FLc.exists_conj_eq_unitriangular (n := 4) (by norm_num) (hP2.toSylow hPi)
  have hgP : ∀ x ∈ unitriangular 4 (ZMod 2), g * x * g⁻¹ ∈ P := by
    intro x hx
    have h1 : g * x * g⁻¹ ∈ (unitriangular 4 (ZMod 2)).map
        (MulAut.conj g :
          SpecialLinearGroup (Fin 4) (ZMod 2) →* SpecialLinearGroup (Fin 4) (ZMod 2)) :=
      ⟨x, hx, rfl⟩
    rw [← hg] at h1
    exact h1
  set θe := MulEquiv.ofBijective θ ⟨hθi, hθs⟩ with hθe
  set ψ : MulAut (SpecialLinearGroup (Fin 4) (ZMod 2)) := (MulAut.conj g).trans θe with hψdef
  have hψx : ∀ x, ψ x = θ (g * x * g⁻¹) := fun x => rfl
  have hψU : ∀ x ∈ unitriangular 4 (ZMod 2), ψ x ∈ unitriangular 4 (ZMod 2) := by
    intro x hx
    rw [hψx]
    exact hgP x hx
  rcases Ln2P.mulAut_cases (by norm_num) ψ hψU with ⟨u, hu, hcu⟩ | ⟨u, hu, hgu⟩
  · refine ⟨g, u, hu, Or.inl fun x k => ?_⟩
    rw [hθ, ← hψx, hcu, eq_comm]
  · refine ⟨g, u, hu, Or.inr fun x k => ?_⟩
    rw [hθ, ← hψx, hgu, eq_comm]

end Twist

namespace Setting

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting G T L V)

theorem unitriangular_le_map_centralizer_z {K : Subgroup G}
    {α : ↥K →* SpecialLinearGroup (Fin 4) (ZMod 2)}
    (hmapU : ((S.Tv ⊓ K).subgroupOf K).map α = unitriangular 4 (ZMod 2)) :
    unitriangular 4 (ZMod 2) ≤
      ((K ⊓ Subgroup.centralizer ({S.z} : Set G)).subgroupOf K).map α := by
  rw [← hmapU]
  refine Subgroup.map_mono fun k hk => ?_
  rw [Subgroup.mem_subgroupOf] at hk ⊢
  have hkT : (k : G) ∈ T := (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hk).1).1
  refine ⟨k.2, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
  have h := S.conj_z_of_mem_T hkT
  calc (k : G) * S.z = (k : G) * S.z * (k : G)⁻¹ * k := by group
    _ = S.z * k := by rw [h]

theorem fix_iff_centralizer_z {K : Subgroup G} (hKW : K ≤ Subgroup.normalizer (S.WK K : Set G))
    {u w : ↥(S.WK K)} (hzuw : S.z = (u : G) * w)
    (hw : ∀ k : ↥K,
      ((InternalSec.autOnHom hKW k : ↥(autOn K (S.WK K))) : MulAut ↥(S.WK K)) w = w)
    (k : ↥K) :
    ((InternalSec.autOnHom hKW k : ↥(autOn K (S.WK K))) : MulAut ↥(S.WK K)) u = u ↔
      (k : G) ∈ Subgroup.centralizer ({S.z} : Set G) := by
  have hcu := coe_autOnHom_apply hKW k u
  have hcw := coe_autOnHom_apply hKW k w
  have hw' : (k : G) * w * (k : G)⁻¹ = w := by
    rw [← hcw, hw k]
  rw [Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    have hu' : (k : G) * u * (k : G)⁻¹ = u := by rw [← hcu, h]
    calc (k : G) * S.z = ((k : G) * u * (k : G)⁻¹) * ((k : G) * w * (k : G)⁻¹) * k := by
          rw [hzuw]; group
      _ = S.z * k := by rw [hu', hw', hzuw]
  · intro h
    apply Subtype.ext
    rw [hcu]
    have e : (k : G) * S.z * (k : G)⁻¹ = S.z := by rw [h]; group
    rw [hzuw] at e
    have e2 : (k : G) * ((u : G) * w) * (k : G)⁻¹ =
        ((k : G) * u * (k : G)⁻¹) * ((k : G) * w * (k : G)⁻¹) := by group
    rw [e2, hw'] at e
    exact mul_right_cancel e

variable {K : Subgroup G} (hKW : K ≤ Subgroup.normalizer (S.WK K : Set G))
  {α : ↥K →* SpecialLinearGroup (Fin 4) (ZMod 2)}
  {ρ : SpecialLinearGroup (Fin 4) (ZMod 2) →* MulAut ↥(S.WK K)} {u : ↥(S.WK K)}
  {g u' : SpecialLinearGroup (Fin 4) (ZMod 2)}

include hKW

theorem conj_unitriangular_fix
    (hfix : ∀ k : ↥K,
      ((InternalSec.autOnHom hKW k : ↥(autOn K (S.WK K))) : MulAut ↥(S.WK K)) u = u ↔
        (k : G) ∈ Subgroup.centralizer ({S.z} : Set G))
    (hmapU : ((S.Tv ⊓ K).subgroupOf K).map α = unitriangular 4 (ZMod 2))
    (hu' : u' ∈ unitriangular 4 (ZMod 2))
    (hcase : (∀ (x : SpecialLinearGroup (Fin 4) (ZMod 2)) (k : ↥K),
          ρ (g * x * g⁻¹) =
              ((InternalSec.autOnHom hKW k : ↥(autOn K (S.WK K))) : MulAut ↥(S.WK K)) ↔
            α k = u' * x * u'⁻¹) ∨
        ∀ (x : SpecialLinearGroup (Fin 4) (ZMod 2)) (k : ↥K),
          ρ (g * x * g⁻¹) =
              ((InternalSec.autOnHom hKW k : ↥(autOn K (S.WK K))) : MulAut ↥(S.WK K)) ↔
            α k = graphAut 4 (u' * x * u'⁻¹)) :
    ∀ s ∈ unitriangular 4 (ZMod 2), ρ (g * s * g⁻¹) u = u := by
  intro s hs
  have hUH := S.unitriangular_le_map_centralizer_z hmapU
  have hs' : u' * s * u'⁻¹ ∈ unitriangular 4 (ZMod 2) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hu' hs) (Subgroup.inv_mem _ hu')
  have key : ∀ y ∈ unitriangular 4 (ZMod 2), ∃ t : ↥K, α t = y ∧
      (t : G) ∈ Subgroup.centralizer ({S.z} : Set G) := by
    intro y hy
    obtain ⟨t, ht, hty⟩ := hUH hy
    exact ⟨t, hty, (Subgroup.mem_subgroupOf.mp ht).2⟩
  rcases hcase with hc | hc
  · obtain ⟨t, hty, htz⟩ := key _ hs'
    rw [(hc s t).mpr hty]
    exact (hfix t).mpr htz
  · obtain ⟨t, hty, htz⟩ := key _ (graphFun_mem_unitriangular hs')
    rw [(hc s t).mpr hty]
    exact (hfix t).mpr htz

theorem reflection_mem_of_model (hαs : Function.Surjective α)
    (hfix : ∀ k : ↥K,
      ((InternalSec.autOnHom hKW k : ↥(autOn K (S.WK K))) : MulAut ↥(S.WK K)) u = u ↔
        (k : G) ∈ Subgroup.centralizer ({S.z} : Set G))
    (hmapU : ((S.Tv ⊓ K).subgroupOf K).map α = unitriangular 4 (ZMod 2))
    (hu' : u' ∈ unitriangular 4 (ZMod 2))
    (hcase : (∀ (x : SpecialLinearGroup (Fin 4) (ZMod 2)) (k : ↥K),
          ρ (g * x * g⁻¹) =
              ((InternalSec.autOnHom hKW k : ↥(autOn K (S.WK K))) : MulAut ↥(S.WK K)) ↔
            α k = u' * x * u'⁻¹) ∨
        ∀ (x : SpecialLinearGroup (Fin 4) (ZMod 2)) (k : ↥K),
          ρ (g * x * g⁻¹) =
              ((InternalSec.autOnHom hKW k : ↥(autOn K (S.WK K))) : MulAut ↥(S.WK K)) ↔
            α k = graphAut 4 (u' * x * u'⁻¹))
    {I : Set ℕ} (hI : ∀ i ∈ I, 4 - i ∈ I)
    (hmodel : ∀ i (hi : FLc.IsNode 4 i), i ∈ I →
      ρ (g * reflection 4 (ZMod 2) i hi.1 hi.2 * g⁻¹) u = u) :
    ∀ i (hi : FLc.IsNode 4 i), i ∈ I → reflection 4 (ZMod 2) i hi.1 hi.2 ∈
      ((K ⊓ Subgroup.centralizer ({S.z} : Set G)).subgroupOf K).map α := by
  set Hz := ((K ⊓ Subgroup.centralizer ({S.z} : Set G)).subgroupOf K).map α with hHz
  have hUH := S.unitriangular_le_map_centralizer_z hmapU
  have key : ∀ (x : SpecialLinearGroup (Fin 4) (ZMod 2)) (k : ↥K),
      ρ (g * x * g⁻¹) =
          ((InternalSec.autOnHom hKW k : ↥(autOn K (S.WK K))) : MulAut ↥(S.WK K)) →
      ρ (g * x * g⁻¹) u = u → α k ∈ Hz := by
    intro x k hk hx
    rw [hk] at hx
    exact ⟨k, Subgroup.mem_subgroupOf.mpr ⟨k.2, (hfix k).mp hx⟩, rfl⟩
  intro i hi hiI
  rcases hcase with hc | hc
  · obtain ⟨k, hk⟩ := hαs (u' * reflection 4 (ZMod 2) i hi.1 hi.2 * u'⁻¹)
    have h1 := key _ k ((hc _ k).mpr hk) (hmodel i hi hiI)
    rw [hk] at h1
    rw [show reflection 4 (ZMod 2) i hi.1 hi.2 =
      u'⁻¹ * (u' * reflection 4 (ZMod 2) i hi.1 hi.2 * u'⁻¹) * u' by group]
    exact Hz.mul_mem (Hz.mul_mem (Hz.inv_mem (hUH hu')) h1) (hUH hu')
  · have hj : FLc.IsNode 4 (4 - i) := ⟨by have := hi.2; omega, by have := hi.1; omega⟩
    obtain ⟨k, hk⟩ := hαs (graphAut 4 (u' * reflection 4 (ZMod 2) (4 - i) hj.1 hj.2 * u'⁻¹))
    have h1 := key _ k ((hc _ k).mpr hk) (hmodel (4 - i) hj (hI i hiI))
    rw [hk, map_mul, map_mul, map_inv, graphAut_apply (reflection 4 (ZMod 2) (4 - i) hj.1 hj.2),
      graphFun_reflection hj.1 hj.2,
      reflection_eq_of_eq (show 4 - (4 - i) = i by have := hi.2; omega) _ _ hi.1 hi.2] at h1
    have hγ : graphAut 4 u' ∈ unitriangular 4 (ZMod 2) := graphFun_mem_unitriangular hu'
    rw [show reflection 4 (ZMod 2) i hi.1 hi.2 = (graphAut 4 u')⁻¹ *
      (graphAut 4 u' * reflection 4 (ZMod 2) i hi.1 hi.2 * (graphAut 4 u')⁻¹) *
        graphAut 4 u' by group]
    exact Hz.mul_mem (Hz.mul_mem (Hz.inv_mem (hUH hγ)) h1) (hUH hγ)

theorem exists_conj_radical (hu' : u' ∈ unitriangular 4 (ZMod 2))
    (hcase : (∀ (x : SpecialLinearGroup (Fin 4) (ZMod 2)) (k : ↥K),
          ρ (g * x * g⁻¹) =
              ((InternalSec.autOnHom hKW k : ↥(autOn K (S.WK K))) : MulAut ↥(S.WK K)) ↔
            α k = u' * x * u'⁻¹) ∨
        ∀ (x : SpecialLinearGroup (Fin 4) (ZMod 2)) (k : ↥K),
          ρ (g * x * g⁻¹) =
              ((InternalSec.autOnHom hKW k : ↥(autOn K (S.WK K))) : MulAut ↥(S.WK K)) ↔
            α k = graphAut 4 (u' * x * u'⁻¹)) (k : ↥K)
    (hk : α k ∈ Ln2P.flagRadical 4 (ZMod 2) 2) :
    ∃ y ∈ Ln2P.flagRadical 4 (ZMod 2) 2, ρ (g * y * g⁻¹) =
      ((InternalSec.autOnHom hKW k : ↥(autOn K (S.WK K))) : MulAut ↥(S.WK K)) := by
  have hu'Q : u'⁻¹ ∈ stabilizer (flagSpace 4 (ZMod 2) 2) :=
    mem_flagStabilizer.mp (unitriangular_le_flagStabilizer {2} (Subgroup.inv_mem _ hu')) 2 rfl
  have hnorm := Ln2P.stabilizer_le_normalizer_flagRadical (n := 4) (K := ZMod 2) 2 hu'Q
  have hconj : ∀ y ∈ Ln2P.flagRadical 4 (ZMod 2) 2, u'⁻¹ * y * u' ∈ Ln2P.flagRadical 4 (ZMod 2) 2 :=
    fun y hy => by simpa using (Subgroup.mem_normalizer_iff.mp hnorm y).mp hy
  rcases hcase with hc | hc
  · exact ⟨u'⁻¹ * α k * u', hconj _ hk, (hc _ k).mpr (by group)⟩
  · refine ⟨u'⁻¹ * graphAut 4 (α k) * u', hconj _ (Ln2P.graphAut_mem_flagRadical hk),
      (hc _ k).mpr ?_⟩
    rw [show u' * (u'⁻¹ * graphAut 4 (α k) * u') * u'⁻¹ = graphAut 4 (α k) by group,
      graphAut_apply, graphAut_apply, graphFun_graphFun]

end Setting

end CFSG.Quasithin.H13.A5
