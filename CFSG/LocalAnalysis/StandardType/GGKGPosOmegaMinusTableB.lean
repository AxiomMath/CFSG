module

public import CFSG.LocalAnalysis.StandardType.GGKGPosOmegaMinusRankOne
public import CFSG.LocalAnalysis.StandardType.GGKGPosOmegaMinusStd
public import CFSG.LocalAnalysis.StandardType.GGF4QGeFourKGPos
public import CFSG.LocalAnalysis.StandardType.GGStdPosLocalDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveRankOneConj
public import CFSG.LocalAnalysis.StandardType.GGOTwoPrimeMap
import Mathlib.Tactic.Group

public section

namespace CFSG.StandardType.KGPosOm

open CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted CFSG.LieType.CurtisTits
  CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.LieType.Steinberg CFSG.Open

section Chart

variable {G : Type} [Group G] {p : ℕ} {Bs X : Subgroup G} {F : Type} [Field F] [Finite F]
  [CharP F 2] {b c : F} {hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0} {ζ : Fˣ} {hζ : ζ ^ p = 1}
  {ψ : spinGroup (quadMinus 4 F b c) →* G} (hψ : Function.Injective ψ)
  {v : ↥Bs →* (Fin 3 → Multiplicative (ZMod p))}
  (hact : ∀ (b' : ↥Bs) (u : spinGroup (quadMinus 4 F b c)),
    (b' : G)⁻¹ * ψ u * (b' : G) = ψ (omTorus hirr hζ (v b') * u * (omTorus hirr hζ (v b'))⁻¹))

include hψ hact in
theorem mem_ggHyperplane_omegaMinus {r : MulAut ↥Bs} {n : spinGroup (quadMinus 4 F b c)}
    (hr : ∀ b' : ↥Bs, ((r b' : ↥Bs) : G) = ψ n * b' * (ψ n)⁻¹) (y : G) :
    y ∈ ggHyperplane Bs r ↔
      ∃ b' : ↥Bs, (b' : G) = y ∧ omTorus hirr hζ (v b') * n = n * omTorus hirr hζ (v b') := by
  have key : ∀ b' : ↥Bs, r b' = b' ↔
      omTorus hirr hζ (v b') * n = n * omTorus hirr hζ (v b') := by
    intro b'
    set t := omTorus hirr hζ (v b')
    have h1 := hact b' n
    constructor
    · intro hb
      have h2 : ψ n * b' * (ψ n)⁻¹ = b' := by rw [← hr]; exact congrArg Subtype.val hb
      have h3 : (b' : G)⁻¹ * ψ n * b' = ψ n := by
        calc (b' : G)⁻¹ * ψ n * b' = (b' : G)⁻¹ * (ψ n * b' * (ψ n)⁻¹) * ψ n := by group
          _ = ψ n := by rw [h2]; group
      rw [h3] at h1
      have h4 : t * n * t⁻¹ = n := hψ h1.symm
      calc t * n = t * n * t⁻¹ * t := by group
        _ = n * t := by rw [h4]
    · intro htn
      apply Subtype.ext
      rw [hr]
      have h4 : t * n * t⁻¹ = n := by rw [htn]; group
      rw [h4] at h1
      calc ψ n * b' * (ψ n)⁻¹ = (b' : G) * ((b' : G)⁻¹ * ψ n * b') * (ψ n)⁻¹ := by group
        _ = b' := by rw [h1]; group
  constructor
  · rintro ⟨b', hb', rfl⟩
    exact ⟨b', rfl, (key b').mp hb'⟩
  · rintro ⟨b', rfl, htn⟩
    exact ⟨b', (key b').mpr htn, rfl⟩

include hψ hact in
theorem inf_centralizer_ggHyperplane_omegaMinus (hv : Function.Surjective v)
    (hrange : ψ.range = X) {r : MulAut ↥Bs} {n : spinGroup (quadMinus 4 F b c)}
    (hr : ∀ b' : ↥Bs, ((r b' : ↥Bs) : G) = ψ n * b' * (ψ n)⁻¹) :
    X ⊓ Subgroup.centralizer (ggHyperplane Bs r : Set G) =
      (Subgroup.centralizer (((omTorus hirr hζ).range ⊓ Subgroup.centralizer {n} :
        Subgroup (spinGroup (quadMinus 4 F b c))) : Set (spinGroup (quadMinus 4 F b c)))).map ψ := by
  have hH := mem_ggHyperplane_omegaMinus hψ hact hr
  have hcomm : ∀ (b' : ↥Bs) (z : spinGroup (quadMinus 4 F b c)),
      (b' : G) * ψ z = ψ z * b' ↔
        omTorus hirr hζ (v b') * z = z * omTorus hirr hζ (v b') := by
    intro b' z
    set t := omTorus hirr hζ (v b')
    have h1 := hact b' z
    constructor
    · intro hbz
      have h3 : (b' : G)⁻¹ * ψ z * b' = ψ z := by
        calc (b' : G)⁻¹ * ψ z * b' = (b' : G)⁻¹ * ((b' : G) * ψ z) := by rw [hbz]; group
          _ = ψ z := by group
      rw [h3] at h1
      have h4 : t * z * t⁻¹ = z := hψ h1.symm
      calc t * z = t * z * t⁻¹ * t := by group
        _ = z * t := by rw [h4]
    · intro htz
      have h4 : t * z * t⁻¹ = z := by rw [htz]; group
      rw [h4] at h1
      calc (b' : G) * ψ z = (b' : G) * ((b' : G)⁻¹ * ψ z * b') := by rw [h1]
        _ = ψ z * b' := by group
  ext y
  constructor
  · rintro ⟨hyX, hyC⟩
    rw [← hrange] at hyX
    obtain ⟨z, rfl⟩ := hyX
    refine ⟨z, Subgroup.mem_centralizer_iff.mpr ?_, rfl⟩
    rintro _ ⟨⟨x, rfl⟩, hx⟩
    obtain ⟨b', rfl⟩ := hv x
    have hxn := Subgroup.mem_centralizer_singleton_iff.mp hx
    have hb' : (b' : G) ∈ ggHyperplane Bs r := (hH _).mpr ⟨b', rfl, hxn⟩
    exact (hcomm b' z).mp (Subgroup.mem_centralizer_iff.mp hyC _ hb')
  · rintro ⟨z, hz, rfl⟩
    refine ⟨by rw [← hrange]; exact ⟨z, rfl⟩, Subgroup.mem_centralizer_iff.mpr ?_⟩
    rintro _ hh
    obtain ⟨b', rfl, htn⟩ := (hH _).mp hh
    exact (hcomm b' z).mpr (Subgroup.mem_centralizer_iff.mp hz _
      ⟨⟨v b', rfl⟩, Subgroup.mem_centralizer_singleton_iff.mpr htn⟩)

end Chart

section TableB


theorem ggRankOneIn_omegaMinus_of_chart {G : Type} [Group G] [Finite G] {p : ℕ}
    {Bs X : Subgroup G}
    {f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {ζ : (GaloisField 2 f)ˣ} (hζ : ζ ^ p = 1)
    (hζo : orderOf ζ = p) (ψ : (ggU .POmegaMinus 4 f).K →* G)
    (hker : ψ.ker ≤ Subgroup.center (ggU .POmegaMinus 4 f).K) (hrange : ψ.range = X)
    (v : ↥Bs →* (Fin 3 → Multiplicative (ZMod p))) (hv : Function.Surjective v)
    (hact : ∀ (b : ↥Bs)
      (u : spinGroup (quadMinus 4 (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2)),
      (b : G)⁻¹ * ψ u * (b : G) = ψ (omTorus (minusCoeffs_irr 2 f) hζ (v b) * u *
        (omTorus (minusCoeffs_irr 2 f) hζ (v b))⁻¹))
    {ν : GGWeyl (ggU .POmegaMinus 4 f).D →* (ggU .POmegaMinus 4 f).K}
    (hν : GGWeylLift (ggU .POmegaMinus 4 f).D ν)
    (ε : GGWeyl (ggU .POmegaMinus 4 f).D ≃* ↥(ggAutomizer X Bs))
    (hind : GGKGPosInduced Bs X .POmegaMinus 4 f ψ ν ε)
    (w : GGWeyl (ggU .POmegaMinus 4 f).D) (i : Fin (ggU .POmegaMinus 4 f).D.rank) :
    ggRankOneIn X Bs ((ε (w * (coxeterMatrix (ggU .POmegaMinus 4 f).D.isFiniteType).simple i *
        w⁻¹) : ↥(ggAutomizer X Bs)) : MulAut ↥Bs) =
      (ggRootLevi (ggU .POmegaMinus 4 f).D
        (weylAction (ggU .POmegaMinus 4 f).D.isFiniteType w (Pi.single i 1))).map ψ := by
  let ψn : spinGroup (quadMinus 4 (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2) →* G :=
    ψ
  have hψ : Function.Injective ψn := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    exact hker.trans (CFSG.RankThree.PartOne.CTP.center_spinGroup_quadMinus_eq_bot
      (by decide : 4 ≤ 4) (minusCoeffs_irr 2 f)).le
  let νn : GGWeyl (minusDatum 4 (minusCoeffs_irr 2 f)) →*
      spinGroup (quadMinus 4 (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2) := ν
  have hνn : GGWeylLift (minusDatum 4 (minusCoeffs_irr 2 f)) νn := hν
  set s := (coxeterMatrix (ggU .POmegaMinus 4 f).D.isFiniteType).simple i with hs
  have h1 : ggRankOneIn X Bs ((ε s : ↥(ggAutomizer X Bs)) : MulAut ↥Bs) =
      (ggRootLevi (ggU .POmegaMinus 4 f).D (Pi.single i 1)).map ψ := by
    rw [ggRankOneIn, inf_centralizer_ggHyperplane_omegaMinus (ψ := ψn) hψ hact hv hrange
      (n := νn s) (hind s), ← ggOTwoPrime_map_of_injective ψn hψ]
    exact congrArg (Subgroup.map ψn)
      (ggOTwoPrime_centralizer_omFix (minusCoeffs_irr 2 f) hζ hp hp2 hζo hνn i)
  have hX : X.map (MulAut.conj (ψ (ν w))).toMonoidHom = X :=
    map_conj_of_mem (by rw [← hrange]; exact ⟨ν w, rfl⟩)
  have hε : ((ε (w * s * w⁻¹) : ↥(ggAutomizer X Bs)) : MulAut ↥Bs) =
      (ε w : MulAut ↥Bs) * (ε s : MulAut ↥Bs) * (ε w : MulAut ↥Bs)⁻¹ := by
    rw [map_mul, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
  have hconj := ggRankOneIn_map_conj (X := X) (fun b' => hind w b') (ε s : MulAut ↥Bs)
  rw [hX, ← hε, h1] at hconj
  rw [← hconj]
  have hact' := ggStdPos_actsAs_weylLift hν w
  have hα : Pi.single i 1 ∈ (ggU .POmegaMinus 4 f).D.roots :=
    (isCTRootSystem (ggU .POmegaMinus 4 f).D.isFiniteType
      (ggU .POmegaMinus 4 f).D.divisible).single_mem i
  have hnα : -Pi.single i 1 ∈ (ggU .POmegaMinus 4 f).D.roots := by
    have h := weylAction_mem_roots (ggU .POmegaMinus 4 f).D.isFiniteType
      ((coxeterMatrix (ggU .POmegaMinus 4 f).D.isFiniteType).toCoxeterSystem.simple i) hα
    rwa [weylAction_simple_single] at h
  have hlevi : ggRootLevi (ggU .POmegaMinus 4 f).D
      (weylAction (ggU .POmegaMinus 4 f).D.isFiniteType w (Pi.single i 1)) =
      (ggRootLevi (ggU .POmegaMinus 4 f).D (Pi.single i 1)).map
        (MulAut.conj (ν w)).toMonoidHom := by
    rw [ggRootLevi, ggRootLevi, Subgroup.map_sup, hact' _ hα, hact' _ hnα, map_neg]
  rw [hlevi, Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext z
  simp


theorem ggKGPosOmegaMinus_tableBPos_torus {G : Type} [Group G] [Finite G] {p : ℕ}
    {Bs X : Subgroup G} {f : ℕ} (ψ₀ : (ggU .POmegaMinus 4 f).K →* G)
    (hloc : GGKGPosLocalHypTw p Bs X .POmegaMinus 4 f ψ₀) :
    ∃ (κ : (ggU .POmegaMinus 4 f).K ≃* (ggU .POmegaMinus 4 f).K)
      (ψ : (ggU .POmegaMinus 4 f).K →* G),
      ψ = ψ₀.comp κ.toMonoidHom ∧ ψ.ker ≤ Subgroup.center (ggU .POmegaMinus 4 f).K ∧
        ψ.range = X ∧ GGTableBPos p Bs X .POmegaMinus 4 f ψ ∧
        ∀ b ∈ Bs, ∃ t ∈ ggTorus (ggU .POmegaMinus 4 f).D,
          ∀ z, b * ψ z * b⁻¹ = ψ (t * z * t⁻¹) := by
  obtain ⟨ζ, hζ, hζo, κ, ψ, hψeq, hker, hrange, eX, v, heX, hv, hdata,
    hkerV, hcard, hCG, ν, hν, ε, hind, href⟩ :=
    F4KGPosition.exists_omegaMinus_weyl_chart_of_localHyp ψ₀ hloc
  have hp := hloc.1.1
  have hp2 := hloc.1.2.1
  have hact : ∀ (a : Bs)
      (u : spinGroup (quadMinus 4 (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2)),
      (a : G)⁻¹ * ψ u * (a : G) = ψ (omTorus (minusCoeffs_irr 2 f) hζ (v a) * u *
        (omTorus (minusCoeffs_irr 2 f) hζ (v a))⁻¹) := hdata.1
  have hpos : GGTableBPos p Bs X .POmegaMinus 4 f ψ := by
    refine ⟨ε, href, ?_, ?_⟩
    · intro w i
      exact ggRankOneIn_omegaMinus_of_chart hp hp2 hζ hζo ψ hker hrange v hv hact hν ε hind w i
    · change Nat.card Bs ≤ p ^ 3 * Nat.card ↥(Bs ⊓ Subgroup.centralizer (X : Set G))
      exact hcard.le
  refine ⟨κ, ψ, hψeq, hker, hrange, hpos, ?_⟩
  let T : (Fin 3 → Multiplicative (ZMod p)) →* (ggU .POmegaMinus 4 f).K :=
    omTorus (minusCoeffs_irr 2 f) hζ
  have hactG : ∀ (a : Bs) (z : (ggU .POmegaMinus 4 f).K),
      (a : G)⁻¹ * ψ z * (a : G) = ψ (T (v a) * z * (T (v a))⁻¹) := hdata.1
  intro b hb
  let a : Bs := ⟨b, hb⟩
  refine ⟨T (v a⁻¹), hdata.2.1 (v a⁻¹), ?_⟩
  intro z
  simpa only [a, Subgroup.coe_inv, inv_inv] using hactG a⁻¹ z

theorem ggTableBPosImage_POmegaMinus_of_localHypTw {G : Type} [Group G] [Finite G] {p : ℕ}
    {Bs X : Subgroup G} {f : ℕ} {ψ₀ : (ggU .POmegaMinus 4 f).K →* G}
    (hloc : GGKGPosLocalHypTw p Bs X .POmegaMinus 4 f ψ₀) :
    GGTableBPosImage p Bs .POmegaMinus 4 f X := by
  obtain ⟨κ, ψ, hψeq, hker, hrange, hpos, htor⟩ := ggKGPosOmegaMinus_tableBPos_torus ψ₀ hloc
  exact ⟨ψ, hker, hrange, hpos⟩

theorem ggKGPosTwInput_POmegaMinus_holds : GGKGPosTwInput .POmegaMinus 4 := by
  intro G _ _ p Bs X f ψ hloc
  exact ggTableBPosImage_POmegaMinus_of_localHypTw hloc

end TableB

end CFSG.StandardType.KGPosOm

end
