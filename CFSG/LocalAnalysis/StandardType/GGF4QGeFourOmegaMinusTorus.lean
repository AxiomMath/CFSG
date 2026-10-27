module

public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.SplitTorusSpinMinus
public import CFSG.LocalAnalysis.StandardType.GGF4QGeFourSpinLifts
public import CFSG.LocalAnalysis.StandardType.GGOmegaMinusRootGenWeyl
public import CFSG.LocalAnalysis.StandardType.GGTriD4NoneRank
public import CFSG.LocalAnalysis.StandardType.GGStdPosLocalDefs
public import CFSG.LocalAnalysis.StandardType.GGKGPosOmegaMinusStd
public import CFSG.LocalAnalysis.StandardType.StarFour.Dictionary
public import CFSG.RankThree.PartOne.K159.InnLayer
import Mathlib.Tactic.Group
public import CFSG.LocalAnalysis.StandardType.StarFour.CentralizerSL

public noncomputable section

namespace CFSG.StandardType.F4KGPosition

open CFSG.Assembly CFSG.Open CFSG.LieType.Universal

private theorem exists_omegaMinus_splitTorus_of_f4_member_holds
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K X : Subgroup G}
    (hcfg : GGF4QGeFourCfg p B Bs x L D J y K) (hX : X = L ∨ X = K) {f : ℕ}
    (hf : 2 ≤ f) (hpq : p ∣ 2 ^ f - 1) (hmark : GGCentralImage .POmegaMinus 4 f X) :
    let Ω := ↥(StatedOmega (StatedQuadMinus 4 (GaloisField 2 f)
      (minusCoeffs 2 f).1 (minusCoeffs 2 f).2))
    ∃ (ζ : (GaloisField 2 f)ˣ) (hζ : ζ ^ p = 1), orderOf ζ = p ∧
      ∃ ψ : (ggU .POmegaMinus 4 f).K →* G,
        ψ.ker ≤ Subgroup.center (ggU .POmegaMinus 4 f).K ∧ ψ.range = X ∧
        ∃ (η : (ggU .POmegaMinus 4 f).K ≃* Ω) (eX : ↥X ≃* Ω) (a : ↥Bs →* Ω),
          (∀ u, (eX.symm (η u) : G) = ψ u) ∧
          a.range = (omMinusTorus (minusCoeffs 2 f).1 (minusCoeffs 2 f).2 hζ).range ∧
          (∀ (b : ↥Bs) (u : Ω),
            (b : G)⁻¹ * (eX.symm u : G) * (b : G) =
              (eX.symm (a b * u * (a b)⁻¹) : G)) ∧
          a.ker.map Bs.subtype = Bs ⊓ Subgroup.centralizer (X : Set G) := by
  cases f with
  | zero => omega
  | succ t =>
    dsimp only
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨hp, hp2, _, _⟩ := hcfg.1.1.1.2.2.2.2.2.1
    have hBs : IsElemAbelian p Bs := hcfg.1.1.2.1.2.1
    obtain ⟨ψ, hker, hrange, ℓ, hℓ, hkerℓ, _, hcard⟩ :=
      exists_spinMinus_lifts_of_f4_member ggInnerDiagMpInput_holds hcfg hX hmark
    let F := GaloisField 2 (t + 1)
    let U := ↥(spinGroup (Spin.quadMinus 4 F (minusCoeffs 2 (t + 1)).1 (minusCoeffs 2 (t + 1)).2))
    let ψn : U →* G := ψ
    let ℓn : ↥Bs →* U := ℓ
    have hE : IsElemAbelian p ℓn.range := isElemAbelian_range_of_isElemAbelian hBs ℓn
    have hpF : p ∣ Nat.card F - 1 := by
      rw [show Nat.card F = 2 ^ (t + 1) from GaloisField.card 2 (t + 1) (by omega)]
      exact hpq
    obtain ⟨ζ, hζ, hζo, η, hη⟩ := ClassicalPosition.exists_spinMinus_splitTorus_equiv
      (minusCoeffs_irr 2 (t + 1)) hp hp2 hpF ℓn.range hE hcard
    have hc : Subgroup.center U = ⊥ :=
      CFSG.RankThree.PartOne.CTP.center_spinGroup_quadMinus_eq_bot
        (by decide : 4 ≤ 4) (minusCoeffs_irr 2 (t + 1))
    have hψinj : Function.Injective ψn := by
      rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      exact hker.trans hc.le
    let ψX : U →* ↥X := ψn.codRestrict X
      (fun u => hrange ▸ (show ψn u ∈ ψn.range from ⟨u, rfl⟩))
    have hψXinj : Function.Injective ψX := by
      intro u v h
      apply hψinj
      exact congrArg (fun z : X => (z : G)) h
    have hψXsurj : Function.Surjective ψX := by
      rintro ⟨z, hz⟩
      have hz' : z ∈ ψn.range := hrange.symm ▸ hz
      obtain ⟨u, hu⟩ := hz'
      exact ⟨u, Subtype.ext hu⟩
    let γ : U ≃* ↥X := MulEquiv.ofBijective ψX ⟨hψXinj, hψXsurj⟩
    let eX := γ.symm.trans η
    let a := η.toMonoidHom.comp ℓn
    have ha : a.range = (omMinusTorus (minusCoeffs 2 (t + 1)).1 (minusCoeffs 2 (t + 1)).2 hζ).range := by
      rw [show a = η.toMonoidHom.comp ℓn from rfl, MonoidHom.range_comp]
      exact hη
    have haKer : a.ker = ℓn.ker := by
      ext b
      change η (ℓn b) = 1 ↔ ℓn b = 1
      exact map_eq_one_iff η η.injective
    refine ⟨ζ, hζ, hζo, ψ, hker, hrange, η, eX, a, ?_, ha, ?_, ?_⟩
    · intro u
      change (γ (η.symm (η u)) : G) = ψn u
      exact congrArg (fun z : U => (γ z : G)) (η.symm_apply_apply u)
    · intro b u
      change (b : G)⁻¹ * ψn (η.symm u) * (b : G) =
        ψn (η.symm (a b * u * (a b)⁻¹))
      calc
        (b : G)⁻¹ * ψn (η.symm u) * (b : G) =
            ψn (ℓn b * η.symm u * (ℓn b)⁻¹) := hℓ b (η.symm u)
        _ = ψn (η.symm (a b * u * (a b)⁻¹)) := by
          congr 1
          simp only [a, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, map_mul, map_inv,
            η.symm_apply_apply]
    · rw [haKer]
      exact hkerℓ

private theorem exists_omegaMinus_coordinates_of_f4_member_holds
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K X : Subgroup G}
    (hcfg : GGF4QGeFourCfg p B Bs x L D J y K) (hX : X = L ∨ X = K) {f : ℕ}
    (hf : 2 ≤ f) (hpq : p ∣ 2 ^ f - 1) (hmark : GGCentralImage .POmegaMinus 4 f X) :
    let Ω := ↥(StatedOmega (StatedQuadMinus 4 (GaloisField 2 f)
      (minusCoeffs 2 f).1 (minusCoeffs 2 f).2))
    ∃ (ζ : (GaloisField 2 f)ˣ) (hζ : ζ ^ p = 1), orderOf ζ = p ∧
      ∃ ψ : (ggU .POmegaMinus 4 f).K →* G,
        ψ.ker ≤ Subgroup.center (ggU .POmegaMinus 4 f).K ∧ ψ.range = X ∧
        ∃ (η : (ggU .POmegaMinus 4 f).K ≃* Ω) (eX : ↥X ≃* Ω)
          (v : ↥Bs →* (Fin 3 → Multiplicative (ZMod p))),
          (∀ u, (eX.symm (η u) : G) = ψ u) ∧ Function.Surjective v ∧
          (∀ (b : ↥Bs) (u : Ω),
            (b : G)⁻¹ * (eX.symm u : G) * (b : G) =
              (eX.symm (omMinusTorus (minusCoeffs 2 f).1 (minusCoeffs 2 f).2 hζ (v b) * u *
                (omMinusTorus (minusCoeffs 2 f).1 (minusCoeffs 2 f).2 hζ (v b))⁻¹) : G)) ∧
          v.ker.map Bs.subtype = Bs ⊓ Subgroup.centralizer (X : Set G) ∧
          (∀ b : ↥Bs, X ⊓ Subgroup.centralizer ({(b : G)} : Set G) =
            (Subgroup.centralizer
              ({omMinusTorus (minusCoeffs 2 f).1 (minusCoeffs 2 f).2 hζ (v b)} : Set Ω)).map
                (X.subtype.comp eX.symm.toMonoidHom)) := by
  dsimp only
  obtain ⟨hp, _, _, _⟩ := hcfg.1.1.1.2.2.2.2.2.1
  have : NeZero p := ⟨hp.ne_zero⟩
  let Ω := ↥(StatedOmega (StatedQuadMinus 4 (GaloisField 2 f)
    (minusCoeffs 2 f).1 (minusCoeffs 2 f).2))
  obtain ⟨ζ, hζ, hζo, ψ, hker, hrange, η, eX, a, hback, ha, hact, hka⟩ :=
    exists_omegaMinus_splitTorus_of_f4_member_holds hcfg hX hf hpq hmark
  let T : (Fin 3 → Multiplicative (ZMod p)) →* Ω :=
    omMinusTorus (minusCoeffs 2 f).1 (minusCoeffs 2 f).2 hζ
  have hT : Function.Injective T := by
    intro u v huv
    apply omMinusTorusGL_injective (m := 3) hζ hζo
    exact congrArg (fun z : Ω =>
      (z : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (GaloisField 2 f))) huv
  let aR : ↥Bs →* T.range := a.codRestrict T.range
    (fun b => ha ▸ (show a b ∈ a.range from ⟨b, rfl⟩))
  have haRsurj : Function.Surjective aR := by
    rintro ⟨z, hz⟩
    have hz' : z ∈ a.range := ha.symm ▸ hz
    obtain ⟨b, hb⟩ := hz'
    exact ⟨b, Subtype.ext hb⟩
  let tE : (Fin 3 → Multiplicative (ZMod p)) ≃* T.range := MonoidHom.ofInjective hT
  let v := tE.symm.toMonoidHom.comp aR
  have hv (b : ↥Bs) : T (v b) = a b :=
    congrArg (fun z : T.range => (z : Ω)) (tE.apply_symm_apply (aR b))
  have hvs : Function.Surjective v := tE.symm.surjective.comp haRsurj
  have hvker : v.ker = a.ker := by
    ext b
    change v b = 1 ↔ a b = 1
    constructor
    · intro hb
      rw [← hv b, hb, T.map_one]
    · intro hb
      apply hT
      rw [hv b, hb, T.map_one]
  let ρ := X.subtype.comp eX.symm.toMonoidHom
  have hρ : Function.Injective ρ := X.subtype_injective.comp eX.symm.injective
  have hρrange : ρ.range = X := by
    ext z
    constructor
    · rintro ⟨u, rfl⟩
      exact (eX.symm u).property
    · intro hz
      exact ⟨eX ⟨z, hz⟩, congrArg (fun z : X => (z : G)) (eX.symm_apply_apply ⟨z, hz⟩)⟩
  refine ⟨ζ, hζ, hζo, ψ, hker, hrange, η, eX, v, hback, hvs, ?_, ?_, ?_⟩
  · intro b u
    change (b : G)⁻¹ * (eX.symm u : G) * (b : G) =
      (eX.symm (T (v b) * u * (T (v b))⁻¹) : G)
    rw [hv b]
    exact hact b u
  · rw [hvker]
    exact hka
  · intro b
    have hρact : ∀ z ∈ ({(b : G)⁻¹} : Set G), ∀ u : Ω,
        z * ρ u * z⁻¹ = ρ (T (v b) * u * (T (v b))⁻¹) := by
      intro z hz u
      have hz' : z = (b : G)⁻¹ := Set.mem_singleton_iff.mp hz
      subst z
      rw [hv b]
      change (b : G)⁻¹ * (eX.symm u : G) * ((b : G)⁻¹)⁻¹ =
        (eX.symm (a b * u * (a b)⁻¹) : G)
      simpa only [inv_inv] using hact b u
    have hC := StarFour.inf_centralizer_eq_map_centralizer ρ hρ
      ({(b : G)⁻¹} : Set G) (fun _ => T (v b)) hρact
    have hCinv : Subgroup.centralizer ({(b : G)⁻¹} : Set G) =
        Subgroup.centralizer ({(b : G)} : Set G) := by
      ext z
      simp only [Subgroup.mem_centralizer_singleton_iff]
      constructor
      · intro h
        simpa [mul_assoc] using (congrArg (fun z : G => (b : G) * z * (b : G)) h).symm
      · intro h
        simpa [mul_assoc] using (congrArg (fun z : G => (b : G)⁻¹ * z * (b : G)⁻¹) h).symm
    simpa only [hρrange, hCinv, Set.image_singleton] using hC

theorem exists_omegaMinus_position_of_f4_member_holds
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K X : Subgroup G}
    (hcfg : GGF4QGeFourCfg p B Bs x L D J y K) (hX : X = L ∨ X = K) {f : ℕ}
    (hf : 2 ≤ f) (hpq : p ∣ 2 ^ f - 1) (hmark : GGCentralImage .POmegaMinus 4 f X) :
    let Ω := ↥(StatedOmega (StatedQuadMinus 4 (GaloisField 2 f)
      (minusCoeffs 2 f).1 (minusCoeffs 2 f).2))
    ∃ (ζ : (GaloisField 2 f)ˣ) (hζ : ζ ^ p = 1), orderOf ζ = p ∧
      ∃ ψ : (ggU .POmegaMinus 4 f).K →* G,
        ψ.ker ≤ Subgroup.center (ggU .POmegaMinus 4 f).K ∧ ψ.range = X ∧
        ∃ (η : (ggU .POmegaMinus 4 f).K ≃* Ω) (eX : ↥X ≃* Ω)
          (v : ↥Bs →* (Fin 3 → Multiplicative (ZMod p))),
          (∀ u, (eX.symm (η u) : G) = ψ u) ∧ Function.Surjective v ∧
          (∀ (b : ↥Bs) (u : Ω),
            (b : G)⁻¹ * (eX.symm u : G) * (b : G) =
              (eX.symm (omMinusTorus (minusCoeffs 2 f).1 (minusCoeffs 2 f).2 hζ (v b) * u *
                (omMinusTorus (minusCoeffs 2 f).1 (minusCoeffs 2 f).2 hζ (v b))⁻¹) : G)) ∧
          v.ker.map Bs.subtype = Bs ⊓ Subgroup.centralizer (X : Set G) ∧
          (∀ b : ↥Bs, X ⊓ Subgroup.centralizer ({(b : G)} : Set G) =
            (Subgroup.centralizer
              ({omMinusTorus (minusCoeffs 2 f).1 (minusCoeffs 2 f).2 hζ (v b)} : Set Ω)).map
                (X.subtype.comp eX.symm.toMonoidHom)) ∧
          (omMinusTorus (minusCoeffs 2 f).1 (minusCoeffs 2 f).2 hζ).range.map
            (X.subtype.comp eX.symm.toMonoidHom) = Bs ⊓ X ∧
          Bs = (Bs ⊓ X) ⊔ (Bs ⊓ Subgroup.centralizer (X : Set G)) ∧
          Disjoint (Bs ⊓ X) (Bs ⊓ Subgroup.centralizer (X : Set G)) := by
  dsimp only
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hp, _, _, _⟩ := hcfg.1.1.1.2.2.2.2.2.1
  have hBs : IsElemAbelian p Bs := hcfg.1.1.2.1.2.1
  let Ω := ↥(StatedOmega (StatedQuadMinus 4 (GaloisField 2 f)
    (minusCoeffs 2 f).1 (minusCoeffs 2 f).2))
  obtain ⟨ζ, hζ, hζo, ψ, hker, hrange, η, eX, v, hback, hvs, hact, hvker, hcent⟩ :=
    exists_omegaMinus_coordinates_of_f4_member_holds hcfg hX hf hpq hmark
  let T : (Fin 3 → Multiplicative (ZMod p)) →* Ω :=
    omMinusTorus (minusCoeffs 2 f).1 (minusCoeffs 2 f).2 hζ
  let ρ := X.subtype.comp eX.symm.toMonoidHom
  have hρrange : ρ.range = X := by
    ext z
    constructor
    · rintro ⟨u, rfl⟩
      exact (eX.symm u).property
    · intro hz
      exact ⟨eX ⟨z, hz⟩, congrArg (fun z : X => (z : G)) (eX.symm_apply_apply ⟨z, hz⟩)⟩
  have hactρ (b : ↥Bs) (u : Ω) :
      (b : G)⁻¹ * ρ u * (b : G) = ρ (T (v b) * u * (T (v b))⁻¹) := by
    change (b : G)⁻¹ * (eX.symm u : G) * (b : G) =
      (eX.symm (T (v b) * u * (T (v b))⁻¹) : G)
    exact hact b u
  have hcomm (b c : ↥Bs) : T (v b) * T (v c) = T (v c) * T (v b) := by
    calc
      T (v b) * T (v c) = T (v b * v c) := (map_mul T (v b) (v c)).symm
      _ = T (v c * v b) := congrArg T (mul_comm (v b) (v c))
      _ = T (v c) * T (v b) := map_mul T (v c) (v b)
  have hpow (b : ↥Bs) : (ρ (T (v b))) ^ p = 1 := by
    have hbp : b ^ p = 1 := Subtype.ext (by simpa using hBs.2 b b.property)
    simp only [← map_pow, hbp, map_one]
  have hct (b : ↥Bs) : ρ (T (v b)) ∈ Subgroup.centralizer (Bs : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro c hc
    let cB : ↥Bs := ⟨c, hc⟩
    have h := hactρ cB (T (v b))
    have hprod : T (v cB) * T (v b) * (T (v cB))⁻¹ = T (v b) :=
      (congrArg (fun z : Ω => z * (T (v cB))⁻¹) (hcomm cB b)).trans
        (mul_inv_cancel_right (T (v b)) (T (v cB)))
    rw [hprod] at h
    have h' := congrArg (fun z : G => c * z) h
    simpa [cB, mul_assoc] using h'.symm
  have hmem (b : ↥Bs) : ρ (T (v b)) ∈ Bs :=
    hcfg.1.1.2.1.2.2.2 _ (hct b) (hpow b)
  have hTorLe : T.range.map ρ ≤ Bs ⊓ X := by
    rintro z ⟨u, ⟨w, rfl⟩, rfl⟩
    obtain ⟨b, rfl⟩ := hvs w
    exact ⟨hmem b, (eX.symm (T (v b))).property⟩
  have hbc (b : ↥Bs) : ρ (T (v b)) * (b : G) ∈ Subgroup.centralizer (X : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have hz' : z ∈ ρ.range := hρrange.symm ▸ hz
    obtain ⟨u, rfl⟩ := hz'
    have hbt : ρ (T (v b)) * (b : G) = (b : G) * ρ (T (v b)) :=
      hBs.comm (hmem b) b.property
    calc
      ρ u * (ρ (T (v b)) * (b : G)) =
          (b : G) * ((b : G)⁻¹ * ρ u * (b : G)) * ρ (T (v b)) := by rw [hbt]; group
      _ = (b : G) * ρ (T (v b) * u * (T (v b))⁻¹) * ρ (T (v b)) := by rw [hactρ]
      _ = (ρ (T (v b)) * (b : G)) * ρ u := by rw [map_mul, map_mul, map_inv, hbt]; group
  let e : ↥(spinGroup (Spin.quadMinus 4 (GaloisField 2 f)
      (minusCoeffs 2 f).1 (minusCoeffs 2 f).2)) ≃* ↥X :=
    (CFSG.SeitzReduction.SymplecticPilot.peRhoMEquiv (by decide : 4 ≤ 4)
      (minusCoeffs_irr 2 f)).trans eX.symm
  have hZX : Subgroup.center ↥X = ⊥ := by
    rw [← Subgroup.map_center_eq e,
      CFSG.RankThree.PartOne.CTP.center_spinGroup_quadMinus_eq_bot
        (by decide : 4 ≤ 4) (minusCoeffs_irr 2 f), Subgroup.map_bot]
  have hcap : X ⊓ Subgroup.centralizer (X : Set G) = ⊥ := by
    apply le_antisymm _ bot_le
    intro z hz
    have hzX : (⟨z, hz.1⟩ : X) ∈ Subgroup.center ↥X := by
      rw [Subgroup.mem_center_iff]
      intro u
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hz.2 u u.property)
    rw [hZX] at hzX
    exact congrArg Subtype.val (Subgroup.mem_bot.mp hzX)
  have hTorEq : T.range.map ρ = Bs ⊓ X := by
    apply le_antisymm hTorLe
    intro z hz
    let b : ↥Bs := ⟨z, hz.1⟩
    have hzb : ρ (T (v b)) * z = 1 := by
      have hC : ρ (T (v b)) * z ∈ X ⊓ Subgroup.centralizer (X : Set G) :=
        ⟨X.mul_mem (eX.symm (T (v b))).property hz.2, hbc b⟩
      rw [hcap] at hC
      exact Subgroup.mem_bot.mp hC
    have hz' : z = (ρ (T (v b)))⁻¹ := by
      calc z = (ρ (T (v b)))⁻¹ * (ρ (T (v b)) * z) := by group
        _ = (ρ (T (v b)))⁻¹ := by rw [hzb, mul_one]
    rw [hz']
    exact (T.range.map ρ).inv_mem ⟨T (v b), ⟨v b, rfl⟩, rfl⟩
  have hinn : ∀ b ∈ Bs, ∃ a ∈ X, ∃ c ∈ Subgroup.centralizer (X : Set G), b = a * c := by
    intro b hb
    let bB : ↥Bs := ⟨b, hb⟩
    refine ⟨(ρ (T (v bB)))⁻¹, X.inv_mem (eX.symm (T (v bB))).property,
      ρ (T (v bB)) * b, hbc bB, ?_⟩
    group
  have hmax : ∀ F : Subgroup G, (∀ f ∈ F, ∀ g ∈ F, f * g = g * f) →
      (∀ f ∈ F, f ^ p = 1) → (∀ f ∈ F, ∀ b ∈ Bs, f * b = b * f) → Bs ≤ F → F ≤ Bs := by
    intro F _ hFpow hc _ z hz
    exact hcfg.1.1.2.1.2.2.2 z
      (Subgroup.mem_centralizer_iff.mpr (fun b hb => (hc z hz b hb).symm)) (hFpow z hz)
  have hZp : ¬ p ∣ Nat.card ↥(X ⊓ Subgroup.centralizer (X : Set G)) := by
    rw [hcap, Subgroup.card_bot]
    exact hp.not_dvd_one
  have hprod := CFSG.RankThree.PartOne.K159.inf_mul_inf_of_inner hp
    (fun a ha b hb => hBs.comm ha hb) hBs.2 hmax hinn hZp
  have hsplit : Bs = (Bs ⊓ X) ⊔ (Bs ⊓ Subgroup.centralizer (X : Set G)) := by
    apply le_antisymm _ (sup_le inf_le_left inf_le_left)
    intro b hb
    obtain ⟨l, hl, c, hc, rfl⟩ := hprod b hb
    exact ((Bs ⊓ X) ⊔ (Bs ⊓ Subgroup.centralizer (X : Set G))).mul_mem
      ((le_sup_left : Bs ⊓ X ≤ (Bs ⊓ X) ⊔ (Bs ⊓ Subgroup.centralizer (X : Set G))) hl)
      ((le_sup_right : Bs ⊓ Subgroup.centralizer (X : Set G) ≤
        (Bs ⊓ X) ⊔ (Bs ⊓ Subgroup.centralizer (X : Set G))) hc)
  have hdisj : Disjoint (Bs ⊓ X) (Bs ⊓ Subgroup.centralizer (X : Set G)) := by
    apply disjoint_iff_inf_le.mpr
    exact (inf_le_inf inf_le_right inf_le_right).trans hcap.le
  exact ⟨ζ, hζ, hζo, ψ, hker, hrange, η, eX, v, hback, hvs, hact, hvker,
    hcent, hTorEq, hsplit, hdisj⟩

end CFSG.StandardType.F4KGPosition
