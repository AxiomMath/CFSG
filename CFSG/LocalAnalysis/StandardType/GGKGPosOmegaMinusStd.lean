module

public import CFSG.LocalAnalysis.StandardType.GGKGPosLocalHypTw
public import CFSG.LocalAnalysis.StandardType.GGKGPosOmegaMinusRoot
public import CFSG.LocalAnalysis.StandardType.GGKGPosOmegaMinusWeyl
public import CFSG.LocalAnalysis.StandardType.GGF4QGeFourSpinLifts
public import CFSG.LocalAnalysis.StandardType.GGOmegaMinusRootGenWeyl
import CFSG.LocalAnalysis.StandardType.GGTriD4NoneRank
import Mathlib.Tactic.Group

public noncomputable section

namespace CFSG.StandardType.F4KGPosition

open CFSG.Open CFSG.LieType.Universal


theorem exists_omegaMinus_rootTorus_chart_of_localHyp
    {G : Type} [Group G] [Finite G] {p : ℕ} {Bs X : Subgroup G} {f : ℕ}
    (ψ₀ : (ggU .POmegaMinus 4 f).K →* G)
    (hloc : GGKGPosLocalHypTw p Bs X .POmegaMinus 4 f ψ₀) :
    let Ω := ↥(StatedOmega (StatedQuadMinus 4 (GaloisField 2 f)
      (minusCoeffs 2 f).1 (minusCoeffs 2 f).2))
    let e : (ggU .POmegaMinus 4 f).K ≃* Ω :=
      CFSG.SeitzReduction.SymplecticPilot.peRhoMEquiv (by decide : 4 ≤ 4) (minusCoeffs_irr 2 f)
    ∃ (ζ : (GaloisField 2 f)ˣ) (hζ : ζ ^ p = 1), orderOf ζ = p ∧
      ∃ (κ : (ggU .POmegaMinus 4 f).K ≃* (ggU .POmegaMinus 4 f).K)
        (ψ : (ggU .POmegaMinus 4 f).K →* G),
        ψ = ψ₀.comp κ.toMonoidHom ∧
        ψ.ker ≤ Subgroup.center (ggU .POmegaMinus 4 f).K ∧ ψ.range = X ∧
        ∃ (eX : ↥X ≃* Ω) (v : ↥Bs →* (Fin 3 → Multiplicative (ZMod p))),
          (∀ u, (eX.symm (e u) : G) = ψ u) ∧ Function.Surjective v ∧
          (let T := e.symm.toMonoidHom.comp
            (omMinusTorus (minusCoeffs 2 f).1 (minusCoeffs 2 f).2 hζ)
           (∀ (b : ↥Bs) (u : (ggU .POmegaMinus 4 f).K),
             (b : G)⁻¹ * ψ u * (b : G) = ψ (T (v b) * u * (T (v b))⁻¹)) ∧
           (∀ u, T u ∈ ggTorus (ggU .POmegaMinus 4 f).D) ∧
           GGKGPosStdPos (ggU .POmegaMinus 4 f).D ψ Bs ∧
           T.range.map ψ = Bs ⊓ X) ∧
          v.ker.map Bs.subtype = Bs ⊓ Subgroup.centralizer (X : Set G) ∧
          Nat.card Bs = p ^ 3 * Nat.card ↥(Bs ⊓ Subgroup.centralizer (X : Set G)) ∧
          (Subgroup.centralizer (Bs : Set G)).comap ψ = ggTorus (ggU .POmegaMinus 4 f).D := by
  dsimp only
  obtain ⟨⟨hp, hp2, hf, hpf⟩, ⟨hker₀, hrange₀⟩, ⟨hBs, -, hmax⟩, hinner, hrank, -⟩ := hloc
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  let : IsMulCommutative ↥Bs := hBs.1
  let F := GaloisField 2 f
  let U := ↥(spinGroup (Spin.quadMinus 4 F (minusCoeffs 2 f).1 (minusCoeffs 2 f).2))
  let Ω := ↥(StatedOmega (StatedQuadMinus 4 F (minusCoeffs 2 f).1 (minusCoeffs 2 f).2))
  let ψn : ↥(spinGroup (Spin.quadMinus 4 F (minusCoeffs 2 f).1 (minusCoeffs 2 f).2)) →* G := ψ₀
  have hrank' : p ^ 3 * Nat.card ↥(Bs ⊓ Subgroup.centralizer (ψn.range : Set G)) ≤ Nat.card Bs := by
    rw [show ψn.range = X from hrange₀]
    exact hrank
  obtain ⟨ℓ, hℓ, hkerℓ, -, hcardℓ⟩ := exists_spinMinus_lift_kernel_rank
    4 (minusCoeffs_irr 2 f) (by decide : 4 ≤ 4) ψn hker₀ Bs hinner hBs.2 hrank'
  have hE : IsElemAbelian p ℓ.range := isElemAbelian_range_of_isElemAbelian hBs ℓ
  have hpF : p ∣ Nat.card F - 1 := by
    rw [show Nat.card F = 2 ^ f from GaloisField.card 2 f (by omega)]
    exact hpf
  obtain ⟨ζ, hζ, hζo, η, hη⟩ := ClassicalPosition.exists_spinMinus_splitTorus_equiv
    (minusCoeffs_irr 2 f) hp hp2 hpF ℓ.range hE hcardℓ
  let e : U ≃* Ω :=
    CFSG.SeitzReduction.SymplecticPilot.peRhoMEquiv (by decide : 4 ≤ 4) (minusCoeffs_irr 2 f)
  let κ : U ≃* U := e.trans η.symm
  let ψ := ψn.comp κ.toMonoidHom
  let T₀ : (Fin 3 → Multiplicative (ZMod p)) →* Ω :=
    omMinusTorus (minusCoeffs 2 f).1 (minusCoeffs 2 f).2 hζ
  let T := e.symm.toMonoidHom.comp T₀
  have hψ₀ : Function.Injective ψn := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    exact hker₀.trans (CFSG.RankThree.PartOne.CTP.center_spinGroup_quadMinus_eq_bot
      (by decide : 4 ≤ 4) (minusCoeffs_irr 2 f)).le
  have hψ : Function.Injective ψ := hψ₀.comp κ.injective
  have hker : ψ.ker ≤ Subgroup.center U := by
    rw [(MonoidHom.ker_eq_bot_iff ψ).mpr hψ]
    exact bot_le
  have hrange : ψ.range = X := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr κ.surjective, Subgroup.map_top]
    exact hrange₀
  let a := η.toMonoidHom.comp ℓ
  have ha : a.range = T₀.range := by rw [MonoidHom.range_comp]; exact hη
  have hT₀ : Function.Injective T₀ := by
    intro u w h
    apply omMinusTorusGL_injective (m := 3) hζ hζo
    exact congrArg (fun z : Ω => (z : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F)) h
  let aR : ↥Bs →* T₀.range := a.codRestrict _ (fun b => ha ▸ (show a b ∈ a.range from ⟨b, rfl⟩))
  have haR : Function.Surjective aR := by
    rintro ⟨z, hz⟩
    obtain ⟨b, hb⟩ : z ∈ a.range := ha.symm ▸ hz
    exact ⟨b, Subtype.ext hb⟩
  let tE : (Fin 3 → Multiplicative (ZMod p)) ≃* T₀.range := MonoidHom.ofInjective hT₀
  let v := tE.symm.toMonoidHom.comp aR
  have hv (b : ↥Bs) : T₀ (v b) = a b :=
    congrArg (fun z : T₀.range => (z : Ω)) (tE.apply_symm_apply (aR b))
  have hvs : Function.Surjective v := tE.symm.surjective.comp haR
  have hLift (b : ↥Bs) : κ (T (v b)) = ℓ b := by
    change η.symm (e (T (v b))) = ℓ b
    have he : e (T (v b)) = T₀ (v b) := e.apply_symm_apply _
    rw [he, hv]
    exact η.symm_apply_apply _
  have hact (b : ↥Bs) (u : U) :
      (b : G)⁻¹ * ψ u * (b : G) = ψ (T (v b) * u * (T (v b))⁻¹) := by
    have hprod : κ (T (v b) * u * (T (v b))⁻¹) = ℓ b * κ u * (ℓ b)⁻¹ := by
      rw [map_mul, map_mul, map_inv, hLift]
    change (b : G)⁻¹ * ψn (κ u) * (b : G) = ψn (κ (T (v b) * u * (T (v b))⁻¹))
    rw [hprod]
    exact hℓ b (κ u)
  have hT (u : Fin 3 → Multiplicative (ZMod p)) :
      T u ∈ ggTorus (Spin.Twisted.minusDatum 4 (minusCoeffs_irr 2 f)) :=
    ClassicalPosition.spinMinus_splitTorus_mem_ggTorus (by decide : 3 ≤ 3) (minusCoeffs_irr 2 f) hζ u
  have hstd : GGKGPosStdPos (Spin.Twisted.minusDatum 4 (minusCoeffs_irr 2 f)) ψ Bs := by
    intro b hb γ hγ
    let bB : ↥Bs := ⟨b, hb⟩
    refine ⟨T (v bB⁻¹), hT _, fun z _ => ?_⟩
    simpa only [Subgroup.coe_inv, inv_inv, bB] using hact bB⁻¹ z
  have hvker : v.ker = ℓ.ker := by
    ext b
    change v b = 1 ↔ ℓ b = 1
    constructor
    · intro h
      apply η.injective
      have h' := hv b
      rw [h, T₀.map_one] at h'
      exact h'.symm.trans (map_one η).symm
    · intro h
      apply hT₀
      rw [hv]
      change η (ℓ b) = T₀ 1
      rw [h, map_one, map_one]
  have hkerMap : v.ker.map Bs.subtype = Bs ⊓ Subgroup.centralizer (X : Set G) := by
    rw [hvker]
    simpa only [show ψn.range = X from hrange₀] using hkerℓ
  have hcardKer : Nat.card v.ker = Nat.card ↥(Bs ⊓ Subgroup.centralizer (X : Set G)) := by
    rw [← hkerMap]
    exact (Subgroup.card_map_of_injective (K := v.ker) (f := Bs.subtype) Bs.subtype_injective).symm
  have hcoord : Nat.card (Fin 3 → Multiplicative (ZMod p)) = p ^ 3 := by simp [Nat.card_eq_fintype_card]
  have hcard : Nat.card Bs = p ^ 3 * Nat.card ↥(Bs ⊓ Subgroup.centralizer (X : Set G)) := by
    rw [← Subgroup.card_ker_mul_card_of_surjective (f := v) hvs, hcardKer, hcoord, Nat.mul_comm]
  have hTcomm (u w : Fin 3 → Multiplicative (ZMod p)) : T u * T w = T w * T u := by
    rw [← map_mul, mul_comm u w, map_mul]
  have hmem (u : Fin 3 → Multiplicative (ZMod p)) : ψ (T u) ∈ Bs := by
    apply hmax
    · rw [Subgroup.mem_centralizer_iff]
      intro b hb
      let bB : ↥Bs := ⟨b, hb⟩
      have h := hact bB (T u)
      have he : T (v bB) * T u * (T (v bB))⁻¹ = T u := by rw [hTcomm]; group
      rw [he] at h
      have h' := congrArg (fun z : G => b * z) h
      simpa [bB, mul_assoc] using h'.symm
    · obtain ⟨b, rfl⟩ := hvs u
      have hb : b ^ p = 1 := Subtype.ext (by simpa using hBs.2 b b.property)
      simp only [← map_pow, hb, map_one]
  have hTor : T.range.map ψ = Bs ⊓ X := by
    apply le_antisymm
    · rintro z ⟨u, ⟨w, rfl⟩, rfl⟩
      exact ⟨hmem w, hrange ▸ ⟨T w, rfl⟩⟩
    · rintro b ⟨hb, hbX⟩
      obtain ⟨u, hu⟩ : b ∈ ψ.range := hrange.symm ▸ hbX
      let bB : ↥Bs := ⟨b, hb⟩
      have huniq : u⁻¹ = T (v bB) := ClassicalPosition.conj_eq_unique_POmegaMinus
        4 (minusCoeffs_irr 2 f) (by decide : 4 ≤ 4) ψ hker (fun z => by
          have hprod : ψ (u⁻¹ * z * u⁻¹⁻¹) = (ψ u)⁻¹ * ψ z * ψ u := by
            simp only [map_mul, map_inv, inv_inv]
          rw [hprod, hu]
          exact hact bB z)
      refine ⟨T ((v bB)⁻¹), ⟨(v bB)⁻¹, rfl⟩, ?_⟩
      rw [map_inv, ← huniq]
      exact (congrArg ψ (_root_.inv_inv u)).trans hu
  have hcomap : (Subgroup.centralizer (Bs : Set G)).comap ψ =
      ggTorus (ggU .POmegaMinus 4 f).D := by
    have hmodel := centralizer_spinMinus_splitPrimeTorus (minusCoeffs_irr 2 f) hp hp2 hζ hζo
    change Subgroup.centralizer (T.range : Set U) = ggTorus (ggU .POmegaMinus 4 f).D at hmodel
    rw [← hmodel]
    ext g
    rw [Subgroup.mem_comap, Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
    constructor
    · intro hg
      rintro _ ⟨u, rfl⟩
      obtain ⟨b, rfl⟩ := hvs u
      have hcomm := hg (b : G) b.property
      have hb : (b : G)⁻¹ * ψ g * (b : G) = ψ g := by rw [mul_assoc, ← hcomm]; group
      have he : T (v b) * g * (T (v b))⁻¹ = g := hψ ((hact b g).symm.trans hb)
      exact mul_inv_eq_iff_eq_mul.mp he
    · intro hg b hb
      let bB : ↥Bs := ⟨b, hb⟩
      have hcomm := hg (T (v bB)) ⟨v bB, rfl⟩
      have he : T (v bB) * g * (T (v bB))⁻¹ = g := by rw [hcomm]; group
      have h := hact bB g
      rw [he] at h
      have h' := congrArg (fun z : G => b * z) h
      simpa [bB, mul_assoc] using h'.symm
  let ψX := ψ.codRestrict X (fun u => hrange ▸ (show ψ u ∈ ψ.range from ⟨u, rfl⟩))
  have hψX : Function.Bijective ψX := by
    refine ⟨fun u w h => hψ (congrArg (fun z : X => (z : G)) h), ?_⟩
    rintro ⟨z, hz⟩
    obtain ⟨u, hu⟩ : z ∈ ψ.range := hrange.symm ▸ hz
    exact ⟨u, Subtype.ext hu⟩
  let γ : U ≃* X := MulEquiv.ofBijective ψX hψX
  let eX := γ.symm.trans e
  have hcompat (u : U) : (eX.symm (e u) : G) = ψ u := by
    change (γ (e.symm (e u)) : G) = ψ u
    exact congrArg (fun z : U => (γ z : G)) (e.symm_apply_apply u)
  exact ⟨ζ, hζ, hζo, κ, ψ, rfl, hker, hrange, eX, v, hcompat, hvs,
    ⟨hact, hT, hstd, hTor⟩, hkerMap, hcard, hcomap⟩


theorem exists_omegaMinus_weyl_chart_of_localHyp
    {G : Type} [Group G] [Finite G] {p : ℕ} {Bs X : Subgroup G} {f : ℕ}
    (ψ₀ : (ggU .POmegaMinus 4 f).K →* G)
    (hloc : GGKGPosLocalHypTw p Bs X .POmegaMinus 4 f ψ₀) :
    let Ω := ↥(StatedOmega (StatedQuadMinus 4 (GaloisField 2 f)
      (minusCoeffs 2 f).1 (minusCoeffs 2 f).2))
    let e : (ggU .POmegaMinus 4 f).K ≃* Ω :=
      CFSG.SeitzReduction.SymplecticPilot.peRhoMEquiv (by decide : 4 ≤ 4) (minusCoeffs_irr 2 f)
    ∃ (ζ : (GaloisField 2 f)ˣ) (hζ : ζ ^ p = 1), orderOf ζ = p ∧
      ∃ (κ : (ggU .POmegaMinus 4 f).K ≃* (ggU .POmegaMinus 4 f).K)
        (ψ : (ggU .POmegaMinus 4 f).K →* G),
        ψ = ψ₀.comp κ.toMonoidHom ∧
        ψ.ker ≤ Subgroup.center (ggU .POmegaMinus 4 f).K ∧ ψ.range = X ∧
        ∃ (eX : ↥X ≃* Ω) (v : ↥Bs →* (Fin 3 → Multiplicative (ZMod p))),
          (∀ u, (eX.symm (e u) : G) = ψ u) ∧ Function.Surjective v ∧
          (let T := e.symm.toMonoidHom.comp
            (omMinusTorus (minusCoeffs 2 f).1 (minusCoeffs 2 f).2 hζ)
           (∀ (b : ↥Bs) (u : (ggU .POmegaMinus 4 f).K),
             (b : G)⁻¹ * ψ u * (b : G) = ψ (T (v b) * u * (T (v b))⁻¹)) ∧
           (∀ u, T u ∈ ggTorus (ggU .POmegaMinus 4 f).D) ∧
           GGKGPosStdPos (ggU .POmegaMinus 4 f).D ψ Bs ∧
           T.range.map ψ = Bs ⊓ X) ∧
          v.ker.map Bs.subtype = Bs ⊓ Subgroup.centralizer (X : Set G) ∧
          Nat.card Bs = p ^ 3 * Nat.card ↥(Bs ⊓ Subgroup.centralizer (X : Set G)) ∧
          (Subgroup.centralizer (Bs : Set G)).comap ψ = ggTorus (ggU .POmegaMinus 4 f).D ∧
          ∃ ν : GGWeyl (ggU .POmegaMinus 4 f).D →* (ggU .POmegaMinus 4 f).K,
            GGWeylLift (ggU .POmegaMinus 4 f).D ν ∧
              ∃ ε : GGWeyl (ggU .POmegaMinus 4 f).D ≃* ↥(ggAutomizer X Bs),
                GGKGPosInduced Bs X .POmegaMinus 4 f ψ ν ε ∧
                ∀ i : Fin (ggU .POmegaMinus 4 f).D.rank,
                  GGIsReflection p (ε ((CFSG.LieType.RootSystem.coxeterMatrix
                    (ggU .POmegaMinus 4 f).D.isFiniteType).simple i) : MulAut ↥Bs) := by
  dsimp only
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨ζ, hζ, hζo, κ, ψ, hψeq, hker, hrange, eX, v, heX, hv, hdata,
    hkerV, hcard, hCG⟩ := exists_omegaMinus_rootTorus_chart_of_localHyp ψ₀ hloc
  obtain ⟨⟨hp, hp2, -, -⟩, -, ⟨hBs, -, -⟩, -, -, -⟩ := hloc
  let F := GaloisField 2 f
  let U : Type := spinGroup (Spin.quadMinus 4 F (minusCoeffs 2 f).1 (minusCoeffs 2 f).2)
  let Ω := ↥(StatedOmega (StatedQuadMinus 4 F (minusCoeffs 2 f).1 (minusCoeffs 2 f).2))
  let e : U ≃* Ω := CFSG.SeitzReduction.SymplecticPilot.peRhoMEquiv
    (by decide : 4 ≤ 4) (minusCoeffs_irr 2 f)
  let T := e.symm.toMonoidHom.comp
    (omMinusTorus (minusCoeffs 2 f).1 (minusCoeffs 2 f).2 hζ)
  let ψn : U →* G := ψ
  have hmatT (u : Fin 3 → Multiplicative (ZMod p)) :
      Spin.spinMatrix (Spin.quadMinus 4 F (minusCoeffs 2 f).1 (minusCoeffs 2 f).2) (T u) =
        omMinusTorusGL hζ u :=
    congrArg (fun A : Ω => (A : (Matrix (Fin 3 ⊕ Fin 3 ⊕ Fin 2)
      (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F)ˣ))
      (e.apply_symm_apply (omMinusTorus (minusCoeffs 2 f).1 (minusCoeffs 2 f).2 hζ u))
  have hactn : ∀ (a : Bs) (u : U), (a : G)⁻¹ * ψn u * (a : G) =
      ψn (T (v a) * u * (T (v a))⁻¹) := hdata.1
  have hTn : T.range.map ψn = Bs ⊓ X := hdata.2.2.2
  obtain ⟨ν, hν, ε, hε, href⟩ := exists_weyl_chart_of_omegaMinus_torusMatrix
    (minusCoeffs_irr 2 f) hp hp2 hζ hζo T hmatT ψn hker hrange hBs v hv hactn hTn
  refine ⟨ζ, hζ, hζo, κ, ψ, hψeq, hker, hrange, eX, v, heX, hv, hdata,
    hkerV, hcard, hCG, ν, hν, ε, ?_, href⟩
  exact hε


end CFSG.StandardType.F4KGPosition
