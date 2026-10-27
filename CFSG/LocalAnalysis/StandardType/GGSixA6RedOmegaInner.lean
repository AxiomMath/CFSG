module

public import CFSG.LocalAnalysis.StandardType.GGSixA6RedDefs
public import CFSG.LieType.BorelTits.OrthogonalForm
public import CFSG.LocalAnalysis.StandardType.GGPsiDiagInnerMinus
public import CFSG.LocalAnalysis.StandardType.GGRootCentralizerOmegaSpin

public section

namespace CFSG.StandardType.A6Red

open CFSG.Assembly CFSG.Blueprint CFSG.Assembly.LowTwoRank

section Genuine

private theorem omegaInner_aux
    (t : StatedLieTag) (ht : t = .POmegaPlus ∨ t = .POmegaMinus) (n f : ℕ) (X : Type)
    [Group X] [Finite X] (ψ : (ggU t n f).K →* X) (p : ℕ) (G₀ D : Subgroup X)
    (hrange : ψ.range = G₀) (hker : ψ.ker ≤ Subgroup.center (ggU t n f).K)
    (hLie : LieModel (↥G₀ ⧸ Subgroup.center ↥G₀) t n 2 f) (hp : p.Prime) (hp2 : p ≠ 2)
    (hDN : D ≤ Subgroup.normalizer (G₀ : Set X))
    (hdiag : ∀ d ∈ D, GGPsiInnerDiag (ggU t n f).D ψ d) (hab : IsElemAbelian p D)
    (hcard : Nat.card D = p ^ 2) (hZK : Subgroup.center (ggU t n f).K = ⊥)
    (hpres : GGPresentsG0 G₀ (ggU t n f).D t n f ψ) :
    Subgroup.center ↥G₀ = ⊥ ∧ ∃ P₀ : Subgroup X, P₀ ≤ G₀ ∧ IsPGroup p ↥P₀ ∧
      G₀ ⊓ Subgroup.centralizer (D : Set X) = G₀ ⊓ Subgroup.centralizer (P₀ : Set X) := by
  have hinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    exact hker.trans hZK.le
  have hZG : Subgroup.center ↥G₀ = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨a, ha⟩ : (x : X) ∈ ψ.range := by rw [hrange]; exact x.2
    rw [Subgroup.mem_bot]
    apply Subtype.ext
    have hza : a ∈ Subgroup.center (ggU t n f).K := by
      rw [Subgroup.mem_center_iff]
      intro b
      apply hinj
      have h1 := Subgroup.mem_center_iff.mp hx ⟨ψ b, hrange ▸ ⟨b, rfl⟩⟩
      have h2 := congrArg Subtype.val h1
      simpa only [Subgroup.coe_mul, ha, map_mul] using h2
    rw [hZK, Subgroup.mem_bot] at hza
    rw [← ha, hza, map_one]
    rfl
  refine ⟨hZG, ?_⟩
  have htag : GGInnerTag t := by rcases ht with rfl | rfl <;> simp [GGInnerTag]
  have hinAt : GGPsiDiagInnerAt t := ggPsiDiagInnerAt_of_ggInnerTag t htag
  have hexists : ∀ d : ↥D, ∃ g : ↥G₀, (d : X) * (g : X) ∈
      Subgroup.centralizer (G₀ : Set X) := by
    intro d
    obtain ⟨g, hg, hcg⟩ := hinAt X n f ψ G₀ hpres (d : X) (hDN d.2) (hdiag d d.2)
    exact ⟨⟨g, hg⟩, by simpa using hcg⟩
  let gd : ↥D → ↥G₀ := fun d => (hexists d).choose
  have hgd : ∀ d : ↥D, (d : X) * (gd d : X) ∈
      Subgroup.centralizer (G₀ : Set X) := fun d => (hexists d).choose_spec
  have huniq : ∀ (d : X) (hd : d ∈ D) (g g' : ↥G₀),
      d * (g : X) ∈ Subgroup.centralizer (G₀ : Set X) →
      d * (g' : X) ∈ Subgroup.centralizer (G₀ : Set X) → g = g' := by
    intro d hd g g' hg hg'
    have hcent : (g⁻¹ * g' : ↥G₀) ∈ Subgroup.center ↥G₀ := by
      rw [Subgroup.mem_center_iff]
      intro y
      apply Subtype.ext
      show (y : X) * ((g⁻¹ * g' : ↥G₀) : X) =
        ((g⁻¹ * g' : ↥G₀) : X) * (y : X)
      have hz : ((g⁻¹ * g' : ↥G₀) : X) =
          (d * (g : X))⁻¹ * (d * (g' : X)) := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        group
      rw [hz]
      exact Subgroup.mem_centralizer_iff.mp
        ((Subgroup.centralizer (G₀ : Set X)).mul_mem
          ((Subgroup.centralizer (G₀ : Set X)).inv_mem hg) hg') (y : X) y.2
    have h1 : g⁻¹ * g' = 1 := by
      rw [hZG, Subgroup.mem_bot] at hcent
      exact hcent
    have h2 : g' = g := by
      calc g' = g * (g⁻¹ * g') := by group
        _ = g * 1 := by rw [h1]
        _ = g := by group
    exact h2.symm
  have hanti : ∀ x y : ↥D, gd (x * y) = gd y * gd x := by
    intro x y
    apply huniq ((x : X) * (y : X)) (D.mul_mem x.2 y.2) (gd (x * y)) (gd y * gd x)
    · exact hgd (x * y)
    · have hx := hgd x
      have hy := hgd y
      have hcomm : ((y : X) * (gd y : X)) * (gd x : X) =
          (gd x : X) * ((y : X) * (gd y : X)) :=
        (Subgroup.mem_centralizer_iff.mp hy (gd x : X) (gd x).2).symm
      have hprod : ((x : X) * (y : X)) * (((gd y * gd x : ↥G₀) : X)) =
          ((x : X) * (gd x : X)) * ((y : X) * (gd y : X)) := by
        simp only [Subgroup.coe_mul]
        calc ((x : X) * (y : X)) * ((gd y : X) * (gd x : X))
            = (x : X) * (((y : X) * (gd y : X)) * (gd x : X)) := by group
          _ = (x : X) * ((gd x : X) * ((y : X) * (gd y : X))) := by rw [hcomm]
          _ = ((x : X) * (gd x : X)) * ((y : X) * (gd y : X)) := by group
      rw [hprod]
      exact Subgroup.mul_mem _ hx hy
  let φ : ↥D →* ↥G₀ :=
    { toFun := fun d => gd d⁻¹
      map_one' := by
        have h1 : gd (1 : ↥D) = 1 := by
          apply huniq (1 : X) D.one_mem (gd 1) 1
          · simpa using hgd (1 : ↥D)
          · simp
        simpa using h1
      map_mul' := by
        intro x y
        change gd (x * y)⁻¹ = gd x⁻¹ * gd y⁻¹
        rw [mul_inv_rev, hanti (y⁻¹) (x⁻¹)] }
  let P₀ : Subgroup X := Subgroup.map (G₀.subtype.comp φ) ⊤
  have hP₀le : P₀ ≤ G₀ := by
    rintro x hx
    simp only [P₀, Subgroup.mem_map] at hx
    obtain ⟨d, -, rfl⟩ := hx
    exact (φ d).2
  have hPp : IsPGroup p ↥P₀ := by
    have hDp : IsPGroup p ↥(⊤ : Subgroup ↥D) := by
      refine IsPGroup.of_card (n := 2) ?_
      simpa [Subgroup.card_top] using hcard
    have := hDp.map (G₀.subtype.comp φ)
    simpa [P₀] using this
  refine ⟨P₀, hP₀le, hPp, le_antisymm ?_ ?_⟩
  ·
    intro h hh
    obtain ⟨hhG, hhD⟩ := Subgroup.mem_inf.mp hh
    refine Subgroup.mem_inf.mpr ⟨hhG, ?_⟩
    have hgd_comm : ∀ e : ↥D, (gd e : X) * (h : X) = (h : X) * (gd e : X) := by
      intro e
      have heh : (e : X) * (h : X) = (h : X) * (e : X) :=
        Subgroup.mem_centralizer_iff.mp hhD (e : X) e.2
      have hc : (e : X) * (gd e : X) ∈ Subgroup.centralizer (G₀ : Set X) := hgd e
      have hch : ((e : X) * (gd e : X)) * (h : X) =
          (h : X) * ((e : X) * (gd e : X)) :=
        (Subgroup.mem_centralizer_iff.mp hc (h : X) hhG).symm
      apply mul_left_cancel (a := (e : X))
      calc (e : X) * ((gd e : X) * (h : X))
          = ((e : X) * (gd e : X)) * (h : X) := by group
        _ = (h : X) * ((e : X) * (gd e : X)) := hch
        _ = ((h : X) * (e : X)) * (gd e : X) := by group
        _ = ((e : X) * (h : X)) * (gd e : X) := by rw [← heh]
        _ = (e : X) * ((h : X) * (gd e : X)) := by group
    rw [Subgroup.mem_centralizer_iff]
    intro p hp
    simp only [P₀, Subgroup.mem_map] at hp
    obtain ⟨d, -, rfl⟩ := hp
    simpa [φ] using hgd_comm d⁻¹
  ·
    intro h hh
    obtain ⟨hhG, hhP⟩ := Subgroup.mem_inf.mp hh
    refine Subgroup.mem_inf.mpr ⟨hhG, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro d hd
    let e : ↥D := ⟨d, hd⟩
    change (e : X) * (h : X) = (h : X) * (e : X)
    have hmemP : (gd e : X) ∈ P₀ := by
      refine Subgroup.mem_map.mpr ⟨e⁻¹, Subgroup.mem_top _, ?_⟩
      simp [φ]
    have hgh : (gd e : X) * (h : X) = (h : X) * (gd e : X) :=
      Subgroup.mem_centralizer_iff.mp hhP (gd e : X) hmemP
    have hginv : ((gd e : X))⁻¹ * (h : X) = (h : X) * ((gd e : X))⁻¹ := by
      calc ((gd e : X))⁻¹ * (h : X)
          = ((gd e : X))⁻¹ * ((h : X) * (gd e : X)) * ((gd e : X))⁻¹ := by group
        _ = ((gd e : X))⁻¹ * (((gd e : X)) * (h : X)) * ((gd e : X))⁻¹ := by
              rw [← hgh]
        _ = (h : X) * ((gd e : X))⁻¹ := by group
    have hc : (e : X) * (gd e : X) ∈ Subgroup.centralizer (G₀ : Set X) := hgd e
    have hch : ((e : X) * (gd e : X)) * (h : X) =
        (h : X) * ((e : X) * (gd e : X)) :=
      (Subgroup.mem_centralizer_iff.mp hc (h : X) hhG).symm
    calc (e : X) * (h : X)
        = (((e : X) * (gd e : X)) * ((gd e : X))⁻¹) * (h : X) := by group
      _ = ((e : X) * (gd e : X)) * (((gd e : X))⁻¹ * (h : X)) := by group
      _ = ((e : X) * (gd e : X)) * ((h : X) * ((gd e : X))⁻¹) := by rw [hginv]
      _ = (((e : X) * (gd e : X)) * (h : X)) * ((gd e : X))⁻¹ := by group
      _ = (((h : X) * ((e : X) * (gd e : X)))) * ((gd e : X))⁻¹ := by rw [hch]
      _ = (h : X) * (((e : X) * (gd e : X)) * ((gd e : X))⁻¹) := by group
      _ = (h : X) * (e : X) := by group

theorem ggA6_omega_inner
    (t : StatedLieTag) (ht : t = .POmegaPlus ∨ t = .POmegaMinus) (n f : ℕ) (X : Type) [Group X]
    [Finite X] (ψ : (ggU t n f).K →* X) (p : ℕ) (G₀ D : Subgroup X) :
    ψ.range = G₀ → ψ.ker ≤ Subgroup.center (ggU t n f).K →
    LieModel (↥G₀ ⧸ Subgroup.center ↥G₀) t n 2 f → p.Prime → p ≠ 2 →
    D ≤ Subgroup.normalizer (G₀ : Set X) → (∀ d ∈ D, GGPsiInnerDiag (ggU t n f).D ψ d) →
    IsElemAbelian p D → Nat.card D = p ^ 2 →
    Subgroup.center ↥G₀ = ⊥ ∧ ∃ P₀ : Subgroup X, P₀ ≤ G₀ ∧ IsPGroup p ↥P₀ ∧
      G₀ ⊓ Subgroup.centralizer (D : Set X) = G₀ ⊓ Subgroup.centralizer (P₀ : Set X) := by
  intro hrange hker hLie hp hp2 hDN hdiag hab hcard
  have hadm : StatedLieAdmissible t n 2 f := LieModel.admissible hLie
  rcases ht with rfl | rfl
  ·
    have hn3 : 3 ≤ n := by have := hadm.2.2; omega
    have hU : ggU .POmegaPlus n f = ⟨spinGroup (CFSG.LieType.Universal.Spin.quadPlus n
        (GaloisField 2 f)), CFSG.LieType.Universal.Spin.plusDatum n (GaloisField 2 f) hn3⟩ := by
      simp only [ggU, CFSG.LieType.Universal.lieUniversal, hn3, ↓reduceDIte]
    have hZK : Subgroup.center (ggU .POmegaPlus n f).K = ⊥ := by
      rw [hU]
      exact RootCentOmega.center_spinGroup_quadPlus_eq_bot_charTwo hn3
    have hperfK : Group.IsPerfect (ggU .POmegaPlus n f).K := by
      rw [hU]
      exact CFSG.LieType.Universal.Spin.isPerfect_spinGroup_quadPlus hn3
    have hperfG : commutator ↥G₀ = ⊤ := by
      have hsurj : Function.Surjective
          (ψ.codRestrict G₀ (fun a => hrange ▸ ⟨a, rfl⟩)) := by
        intro g
        have hg : (g : X) ∈ ψ.range := by rw [hrange]; exact g.2
        obtain ⟨a, ha⟩ := hg
        exact ⟨a, Subtype.ext ha⟩
      haveI : Group.IsPerfect (ggU .POmegaPlus n f).K := hperfK
      exact Group.isPerfect_def.mp (Group.IsPerfect.ofSurjective
        (f := ψ.codRestrict G₀ (fun a => hrange ▸ ⟨a, rfl⟩)) hsurj)
    have hrank : 2 ≤ (ggU .POmegaPlus n f).D.rank := by
      rw [hU]
      show 2 ≤ (CFSG.LieType.Universal.Spin.plusDatum n (GaloisField 2 f) hn3).rank
      simp only [CFSG.LieType.Universal.Spin.plusDatum]
      omega
    have hpres : GGPresentsG0 G₀ (ggU .POmegaPlus n f).D .POmegaPlus n f ψ :=
      ⟨⟨hadm, hrank⟩, ⟨hrange, hker⟩, hperfG, hLie⟩
    exact omegaInner_aux .POmegaPlus (Or.inl rfl) n f X ψ p G₀ D hrange hker hLie hp hp2
      hDN hdiag hab hcard hZK hpres
  ·
    have hn : 4 ≤ n := hadm.2.2
    have hU : ggU .POmegaMinus n f = ⟨spinGroup (CFSG.LieType.Universal.Spin.quadMinus n
        (GaloisField 2 f) (CFSG.LieType.Universal.minusCoeffs 2 f).1
        (CFSG.LieType.Universal.minusCoeffs 2 f).2),
        CFSG.LieType.Universal.Spin.Twisted.minusDatum n
          (CFSG.LieType.Universal.minusCoeffs_irr 2 f)⟩ := rfl
    have hZK : Subgroup.center (ggU .POmegaMinus n f).K = ⊥ := by
      rw [hU]
      exact PsiDiag.SpinM.center_eq_bot (CFSG.LieType.Universal.minusCoeffs_irr 2 f) hn
    have hperfK : Group.IsPerfect (ggU .POmegaMinus n f).K := by
      rw [hU]
      exact CFSG.LieType.Universal.Spin.isPerfect_spinGroup_quadMinus hn
        (CFSG.LieType.Universal.minusCoeffs_irr 2 f)
    have hperfG : commutator ↥G₀ = ⊤ := by
      have hsurj : Function.Surjective
          (ψ.codRestrict G₀ (fun a => hrange ▸ ⟨a, rfl⟩)) := by
        intro g
        have hg : (g : X) ∈ ψ.range := by rw [hrange]; exact g.2
        obtain ⟨a, ha⟩ := hg
        exact ⟨a, Subtype.ext ha⟩
      haveI : Group.IsPerfect (ggU .POmegaMinus n f).K := hperfK
      exact Group.isPerfect_def.mp (Group.IsPerfect.ofSurjective
        (f := ψ.codRestrict G₀ (fun a => hrange ▸ ⟨a, rfl⟩)) hsurj)
    have hrank : 2 ≤ (ggU .POmegaMinus n f).D.rank := by
      rw [hU]
      show 2 ≤ (CFSG.LieType.Universal.Spin.Twisted.minusDatum n
        (CFSG.LieType.Universal.minusCoeffs_irr 2 f)).rank
      simp only [CFSG.LieType.Universal.Spin.Twisted.minusDatum]
      omega
    have hpres : GGPresentsG0 G₀ (ggU .POmegaMinus n f).D .POmegaMinus n f ψ :=
      ⟨⟨hadm, hrank⟩, ⟨hrange, hker⟩, hperfG, hLie⟩
    exact omegaInner_aux .POmegaMinus (Or.inr rfl) n f X ψ p G₀ D hrange hker hLie hp hp2
      hDN hdiag hab hcard hZK hpres

end Genuine

end CFSG.StandardType.A6Red
