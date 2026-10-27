module

public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelTFrame
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelTwE6Val
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelModule
public import CFSG.Sporadic.Schreier.J4SProfileNode

public noncomputable section

namespace CFSG.StandardType.E6ThreeModel

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Exceptional CFSG.LieType.Universal
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Lang.E6Descent CFSG.StandardType.TableBExc.E6Three
  CFSG.RankThree.Classical2 CFSG.StandardType.NoOffTwE6Three CFSG.SeitzReduction.E6Pilot

private theorem card_mul_card_range_dvd_of_le_ker {G : Type*} [Group G] (N X : Subgroup G)
    {α : Type*} (ρ : N →* Equiv.Perm α) (hXN : X ≤ N) (hX : X.subgroupOf N ≤ ρ.ker) :
    Nat.card X * Nat.card ρ.range ∣ Nat.card N := by
  have hdvd : Nat.card (X.subgroupOf N) ∣ Nat.card ρ.ker := Subgroup.card_dvd_of_le hX
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXN).toEquiv] at hdvd
  rw [← Subgroup.card_ker_mul_card_range ρ]
  exact mul_dvd_mul_right hdvd _


variable {n : ℕ} (hn : 1 ≤ n) {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ n) ^ 2)
  (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ n) {Ω : Type} [Field Ω] [Algebra K Ω]
  [IsAlgClosure K Ω] (Fr : Ω →+* Ω) (hFr : ∀ c, Fr c = c ^ 2 ^ n)

private theorem weylElt_conj_rootDiagUnit_zetaVec {L : Type} [Field L] {ζ : Lˣ}
    (hζ : ζ ^ 3 = 1) (i : Fin Tag.E6.rank) (x : Fin Tag.E6.rank → ZMod 3) :
    weylElt Tag.E6 L i 1 * rootDiagUnit Tag.E6 (zetaVec ζ hζ x) *
        (weylElt Tag.E6 L i 1)⁻¹ =
      rootDiagUnit Tag.E6 (zetaVec ζ hζ (adRefl .E6 3 i x)) := by
  rw [monomial_conj_rootDiagUnit_weylTuple
      (weylElt_mem_monomialSubgroup (τ := Tag.E6) (R := L) i)
      (mapsRootLines_weylElt (τ := Tag.E6) (R := L) i),
    weylTuple_zetaVec]
  rw [show adAct Tag.E6 3 (simple Tag.E6 i) x = adRefl .E6 3 i x from
    adAct_simple (τ := Tag.E6) i x]

theorem langTorus_not_le_cgrp (h3 : 3 ∣ 2 ^ n + 1) {g : ModGL Tag.E6 Ω} (hL : IsLang Fr g)
    {ζ : Ωˣ} (hζ : ζ ^ 3 = 1) (hζo : orderOf ζ = 3)
    {D : FrameData ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom)}
    (hD : TSpec hn hK σ hσ Fr hFr g hζ D) :
    ¬ ∀ x ∈ TwistedDiag.thetaTorus Ω (2 ^ n), g * x * g⁻¹ ∈ TwistedDiag.Cgrp K σ.toRingHom Ω := by
  classical
  intro hXC
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := charP_two_of_card (m := n * 2) (by rw [hK, pow_mul])
  haveI : CharP Ω 2 := charP_of_injective_algebraMap (algebraMap K Ω).injective 2
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  have hq0 : ((2 ^ n : ℕ) : Ω) = 0 := by
    rw [Nat.cast_pow, CharP.cast_eq_zero Ω 2]
    exact zero_pow (by omega : n ≠ 0)
  obtain ⟨hfinR, hCR, hCnorm, hCidx, hRcard⟩ :=
    TwistedDiag.cgrp_facts hn K hK σ.toRingHom hσ h3 Ω Fr hFr
  have hC3 : Nat.card (TwistedDiag.Cgrp K σ.toRingHom Ω) * 3 =
      Nat.card (TwistedDiag.Rgrp Ω Fr) := by
    have h := Subgroup.relIndex_mul_card (TwistedDiag.Cgrp K σ.toRingHom Ω)
      (TwistedDiag.Rgrp Ω Fr)
    rw [hCidx, inf_of_le_left hCR] at h
    rw [← h]
    exact Nat.mul_comm _ _
  let X : Subgroup (ModGL Tag.E6 Ω) := TwistedDiag.thetaTorus Ω (2 ^ n)
  let X' : Subgroup (ModGL Tag.E6 Ω) := X.map (MulAut.conj g).toMonoidHom
  let nb : Fin Tag.E6.rank → ModGL Tag.E6 Ω := fun i => g * weylElt Tag.E6 Ω i 1 * g⁻¹
  have hXcard : Nat.card X = (2 ^ n + 1) ^ 6 := by
    show Nat.card (TwistedDiag.thetaTorus Ω (2 ^ n)) = _
    rw [TwistedDiag.natCard_thetaTorus (Ω := Ω) hq0]
  have hX'card : Nat.card X' = (2 ^ n + 1) ^ 6 := by
    show Nat.card (X.map (MulAut.conj g).toMonoidHom) = _
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hXcard]
  have hX'C : X' ≤ TwistedDiag.Cgrp K σ.toRingHom Ω := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
    change g * y * g⁻¹ ∈ TwistedDiag.Cgrp K σ.toRingHom Ω
    exact hXC y hy
  have hnbC : ∀ i, nb i ∈ TwistedDiag.Cgrp K σ.toRingHom Ω :=
    fun i => ⟨(D.nb i : ModGL TwistTag.E6.tag K), (D.nb i).2, hD.nb_eq i⟩
  let ψ : Multiplicative (Fin Tag.E6.rank → ZMod 3) →* ModGL Tag.E6 Ω :=
    MonoidHom.mk'
      (fun x => g * rootDiagUnit Tag.E6 (zetaVec ζ hζ (Multiplicative.toAdd x)) * g⁻¹)
      (by
        intro x y
        change g * rootDiagUnit Tag.E6
              (zetaVec ζ hζ (Multiplicative.toAdd x + Multiplicative.toAdd y)) * g⁻¹ =
            (g * rootDiagUnit Tag.E6 (zetaVec ζ hζ (Multiplicative.toAdd x)) * g⁻¹) *
              (g * rootDiagUnit Tag.E6 (zetaVec ζ hζ (Multiplicative.toAdd y)) * g⁻¹)
        rw [ExcFrames.zetaVec_add, rootDiagUnit_mul]
        group)
  have hψinj : Function.Injective ψ := by
    intro x y hxy
    have h2 : g⁻¹ * (g * rootDiagUnit Tag.E6 (zetaVec ζ hζ (Multiplicative.toAdd x)) * g⁻¹) * g =
        g⁻¹ * (g * rootDiagUnit Tag.E6 (zetaVec ζ hζ (Multiplicative.toAdd y)) * g⁻¹) * g := by
      change g⁻¹ * ψ x * g = g⁻¹ * ψ y * g
      rw [hxy]
    have key : ∀ z : ModGL Tag.E6 Ω, g⁻¹ * (g * z * g⁻¹) * g = z := fun z => by group
    rw [key, key] at h2
    exact Multiplicative.ext (zetaVec_injective (τ := Tag.E6) (p := 3) hζo hζ
      (rootDiagUnit_injective h2))
  let V : Subgroup (ModGL Tag.E6 Ω) := ψ.range
  let Vn : Subgroup (ModGL Tag.E6 Ω) := Subgroup.normalizer (V : Set (ModGL Tag.E6 Ω))
  let f : (Fin Tag.E6.rank → ZMod 3) → V :=
    fun x => ⟨ψ (Multiplicative.ofAdd x), ⟨Multiplicative.ofAdd x, rfl⟩⟩
  have hfinj : Function.Injective f := by
    intro x y hxy
    have h1 : ψ (Multiplicative.ofAdd x) = ψ (Multiplicative.ofAdd y) :=
      Subtype.ext_iff.mp hxy
    simpa using congrArg Multiplicative.toAdd (hψinj h1)
  have hfsurj : Function.Surjective f := by
    rintro ⟨v, hv⟩
    obtain ⟨y, rfl⟩ := hv
    exact ⟨Multiplicative.toAdd y, by apply Subtype.ext; rfl⟩
  let e : (Fin Tag.E6.rank → ZMod 3) ≃ V := Equiv.ofBijective f ⟨hfinj, hfsurj⟩
  haveI : Finite V := by
    show Finite ψ.range
    haveI := MonoidHom.fintypeRange ψ
    infer_instance
  have hX'cent : ∀ x ∈ X', ∀ v ∈ V, x * v * x⁻¹ = v := by
    intro x hx v hv
    obtain ⟨x₀, hx₀, hx₀eq⟩ := Subgroup.mem_map.1 hx
    obtain ⟨b, hb, rfl⟩ := TwistedDiag.mem_thetaTorus.1 hx₀
    obtain ⟨y, rfl⟩ := hv
    rw [← hx₀eq]
    change (g * rootDiagUnit Tag.E6 b * g⁻¹) *
          (g * rootDiagUnit Tag.E6 (zetaVec ζ hζ (Multiplicative.toAdd y)) * g⁻¹) *
          (g * rootDiagUnit Tag.E6 b * g⁻¹)⁻¹ =
        g * rootDiagUnit Tag.E6 (zetaVec ζ hζ (Multiplicative.toAdd y)) * g⁻¹
    rw [show (g * rootDiagUnit Tag.E6 b * g⁻¹) *
          (g * rootDiagUnit Tag.E6 (zetaVec ζ hζ (Multiplicative.toAdd y)) * g⁻¹) *
          (g * rootDiagUnit Tag.E6 b * g⁻¹)⁻¹ =
          g * (rootDiagUnit Tag.E6 b *
            rootDiagUnit Tag.E6 (zetaVec ζ hζ (Multiplicative.toAdd y)) *
            (rootDiagUnit Tag.E6 b)⁻¹) * g⁻¹ by group]
    have hcomm : rootDiagUnit Tag.E6 b *
          rootDiagUnit Tag.E6 (zetaVec ζ hζ (Multiplicative.toAdd y)) =
        rootDiagUnit Tag.E6 (zetaVec ζ hζ (Multiplicative.toAdd y)) *
          rootDiagUnit Tag.E6 b := by
      rw [← rootDiagUnit_mul, ← rootDiagUnit_mul, mul_comm]
    rw [hcomm]
    group
  have hconj : ∀ (i : Fin Tag.E6.rank) (y : Multiplicative (Fin Tag.E6.rank → ZMod 3)),
      nb i * ψ y * (nb i)⁻¹ =
        ψ (Multiplicative.ofAdd (adRefl .E6 3 i (Multiplicative.toAdd y))) := by
    intro i y
    change (g * weylElt Tag.E6 Ω i 1 * g⁻¹) *
          (g * rootDiagUnit Tag.E6 (zetaVec ζ hζ (Multiplicative.toAdd y)) * g⁻¹) *
          (g * weylElt Tag.E6 Ω i 1 * g⁻¹)⁻¹ =
        g * rootDiagUnit Tag.E6 (zetaVec ζ hζ (adRefl .E6 3 i (Multiplicative.toAdd y))) * g⁻¹
    rw [show (g * weylElt Tag.E6 Ω i 1 * g⁻¹) *
          (g * rootDiagUnit Tag.E6 (zetaVec ζ hζ (Multiplicative.toAdd y)) * g⁻¹) *
          (g * weylElt Tag.E6 Ω i 1 * g⁻¹)⁻¹ =
          g * (weylElt Tag.E6 Ω i 1 *
            rootDiagUnit Tag.E6 (zetaVec ζ hζ (Multiplicative.toAdd y)) *
            (weylElt Tag.E6 Ω i 1)⁻¹) * g⁻¹ by group,
      weylElt_conj_rootDiagUnit_zetaVec (L := Ω) hζ i (Multiplicative.toAdd y)]
  have hnbVnorm : ∀ i, nb i ∈ Vn := by
    intro i
    rw [Subgroup.mem_normalizer_iff]
    intro v
    constructor
    · intro hv
      obtain ⟨y, rfl⟩ := hv
      rw [hconj i y]
      exact ⟨Multiplicative.ofAdd (adRefl .E6 3 i (Multiplicative.toAdd y)), rfl⟩
    · intro hv
      have hmaple : V.map (MulAut.conj (nb i)).toMonoidHom ≤ V := by
        rintro _ ⟨w, hw, rfl⟩
        obtain ⟨y, rfl⟩ := hw
        change nb i * ψ y * (nb i)⁻¹ ∈ V
        rw [hconj i y]
        exact ⟨Multiplicative.ofAdd (adRefl .E6 3 i (Multiplicative.toAdd y)), rfl⟩
      have hcard : Nat.card (V.map (MulAut.conj (nb i)).toMonoidHom) = Nat.card V :=
        Subgroup.card_map_of_injective (MulAut.conj (nb i)).injective
      have hEq : V.map (MulAut.conj (nb i)).toMonoidHom = V :=
        Subgroup.eq_of_le_of_card_ge hmaple (le_of_eq hcard.symm)
      have hmem : (MulAut.conj (nb i)).toMonoidHom v ∈ V.map
          (MulAut.conj (nb i)).toMonoidHom := by
        rw [hEq]
        exact hv
      obtain ⟨u, hu, huv⟩ := Subgroup.mem_map.1 hmem
      have huv' : u = v := (MulAut.conj (nb i)).injective huv
      rwa [← huv']
  have hX'Vnorm : X' ≤ Vn :=
    Subgroup.le_normalizer_iff.2 (fun x hx v hv => by rw [hX'cent x hx v hv]; exact hv)
  let N : Subgroup (ModGL Tag.E6 Ω) := Subgroup.closure (↑X' ∪ Set.range nb)
  have hX'N : X' ≤ N := fun x hx => Subgroup.subset_closure (Or.inl hx)
  have hnbN : ∀ i, nb i ∈ N := fun i => Subgroup.subset_closure (Or.inr ⟨i, rfl⟩)
  have hNV : N ≤ Vn := by
    refine (Subgroup.closure_le Vn).2 ?_
    rintro z (hz | hz)
    · exact hX'Vnorm hz
    · obtain ⟨i, rfl⟩ := hz
      exact hnbVnorm i
  let ρ : N →* Equiv.Perm (Fin Tag.E6.rank → ZMod 3) :=
    (e.permCongrHom.symm).toMonoidHom.comp
      ((MulAut.toPerm V : MulAut V →* Equiv.Perm V).comp
        ((Subgroup.normalizerMonoidHom V).comp (Subgroup.inclusion hNV)))
  have hρapply : ∀ (n : N) (y : Fin Tag.E6.rank → ZMod 3),
      ρ n y = e.symm ((Subgroup.normalizerMonoidHom V (Subgroup.inclusion hNV n)) (e y)) := by
    intro n y
    rfl
  have hX'ker : X'.subgroupOf N ≤ ρ.ker := by
    intro n hn
    rw [MonoidHom.mem_ker]
    apply Equiv.ext
    intro y
    have hn' : (n : ModGL Tag.E6 Ω) ∈ X' := Subgroup.mem_subgroupOf.1 hn
    have hcy : (Subgroup.normalizerMonoidHom V (Subgroup.inclusion hNV n)) (e y) = e y := by
      apply Subtype.ext
      rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
      exact hX'cent (n : ModGL Tag.E6 Ω) hn' (e y) (e y).2
    rw [hρapply n y, hcy, Equiv.symm_apply_apply]
    rfl
  have hρnb : ∀ i, ρ ⟨nb i, hnbN i⟩ = adPerm .E6 3 (simple .E6 i) := by
    intro i
    apply Equiv.ext
    intro y
    have hcy : (Subgroup.normalizerMonoidHom V (Subgroup.inclusion hNV ⟨nb i, hnbN i⟩)) (e y) =
        e (adRefl .E6 3 i y) := by
      apply Subtype.ext
      rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
      change nb i * ψ (Multiplicative.ofAdd y) * (nb i)⁻¹ =
        ψ (Multiplicative.ofAdd (adRefl .E6 3 i y))
      simpa using hconj i (Multiplicative.ofAdd y)
    rw [hρapply ⟨nb i, hnbN i⟩ y, hcy, Equiv.symm_apply_apply, adPerm_apply, adAct_simple]
  have hWle : (adPerm .E6 3).range ≤ ρ.range := by
    rintro z ⟨w, rfl⟩
    refine weyl_induction (P := fun w => adPerm .E6 3 w ∈ ρ.range) ?_ ?_ w
    · exact ⟨1, by rw [map_one, map_one]⟩
    · intro i w hw
      obtain ⟨n, hn⟩ := hw
      refine ⟨⟨nb i, hnbN i⟩ * n, ?_⟩
      calc ρ (⟨nb i, hnbN i⟩ * n) = ρ ⟨nb i, hnbN i⟩ * ρ n := map_mul ρ _ _
        _ = adPerm .E6 3 (simple .E6 i) * adPerm .E6 3 w := by rw [hρnb i, hn]
        _ = adPerm .E6 3 (simple .E6 i * w) := (map_mul (adPerm .E6 3) _ _).symm
  have hInj : Function.Injective (adPerm .E6 3) := by
    intro w w' h
    have h1 : adPerm .E6 3 (w'⁻¹ * w) = 1 := by
      rw [map_mul, map_inv, h]
      exact inv_mul_cancel _
    have h2 : w'⁻¹ * w = 1 := by
      apply eq_one_of_adAct_eq_on_hypE6
      intro x hx
      rw [← adPerm_apply]
      exact Equiv.Perm.congr_fun h1 x
    exact (inv_mul_eq_one.mp h2).symm
  have hWcard : Nat.card (adPerm .E6 3).range = 51840 := by
    rw [MonoidHom.range_eq_map, Subgroup.card_map_of_injective hInj, Subgroup.card_top]
    exact CFSG.RankThree.E6.card_weylGroup_E6
  have hNleCg : N ≤ TwistedDiag.Cgrp K σ.toRingHom Ω := by
    refine (Subgroup.closure_le (TwistedDiag.Cgrp K σ.toRingHom Ω)).2 ?_
    rintro z (hz | hz)
    · exact hX'C hz
    · obtain ⟨i, rfl⟩ := hz
      exact hnbC i
  have hNcard_dvd : Nat.card N ∣ Nat.card (TwistedDiag.Cgrp K σ.toRingHom Ω) :=
    Subgroup.card_dvd_of_le hNleCg
  have hcount : Nat.card X' * Nat.card ρ.range ∣ Nat.card N :=
    card_mul_card_range_dvd_of_le_ker N X' ρ hX'N hX'ker
  have hWrange_dvd : 51840 ∣ Nat.card ρ.range := by
    have h := Subgroup.card_dvd_of_le hWle
    rwa [hWcard] at h
  have hNbig : (2 ^ n + 1) ^ 6 * 51840 ∣ Nat.card N := by
    rw [← hX'card]
    exact (mul_dvd_mul_left _ hWrange_dvd).trans hcount
  have hCg3 : Nat.card (TwistedDiag.Cgrp K σ.toRingHom Ω) * 3 = numTwistedE6 (2 ^ n) := by
    rw [hC3, hRcard]
  have hNum : (2 ^ n + 1) ^ 6 * 51840 * 3 ∣ numTwistedE6 (2 ^ n) := by
    rw [← hCg3]
    exact mul_dvd_mul_right (hNbig.trans hNcard_dvd) 3
  have h3pow : 3 ^ 5 ∣ 51840 * 3 := by norm_num
  have hfinal : (2 ^ n + 1) ^ 6 * 3 ^ 5 ∣ numTwistedE6 (2 ^ n) := by
    have h1 : (2 ^ n + 1) ^ 6 * 3 ^ 5 ∣ (2 ^ n + 1) ^ 6 * 51840 * 3 := by
      simpa only [Nat.mul_assoc] using Nat.mul_dvd_mul_left _ h3pow
    exact h1.trans hNum
  exact not_dvd_numTwistedE6 (q := 2 ^ n)
    (by have := Nat.one_lt_two_pow (n := n) (by omega); omega) h3 hfinal

end CFSG.StandardType.E6ThreeModel
