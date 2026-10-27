module

public import CFSG.Quasithin.Vol2.Ch8Sec2L828UTh
public import CFSG.Quasithin.Vol2.Ch8Sec2L828TRho
public import CFSG.Quasithin.Vol2.Ch8Sec2L828TMBApp
public import CFSG.Quasithin.Vol2.Ch8Sec2L828UMod2

public section

namespace CFSG.Quasithin.H13

open scoped IsMulCommutative
open CFSG.Open
open CFSG.Quasithin.H13.L828T
open CFSG.Quasithin.H

section Nt

variable {G : Type} [Group G] [Finite G] {T L I H : Subgroup G} {h : G} {k : ℕ}
  [IsMulCommutative ↥(fsuV T I)]

theorem ob5_rho_unique (c : S828Ctx T L I H h k)
    [PtActCentralAbelian (pCoreOf 2 (ch82I (fsuV T I) h)) (ch82U (fsuV T I) h)]
    (ρ : ↥(ob5N0 T I h) →* AddMonoid.End (QB (fsuV T I) (ch82B (fsuV T I) h) (ch82U (fsuV T I) h) ×
      QB (fsuV T I) (ch82B (fsuV T I) h) (ch82U (fsuV T I) h)))
    (htot : ∀ (g : ↥(ob5N0 T I h)) (b₁ b₂ : ↥((ch82B (fsuV T I) h).subgroupOf (fsuV T I))),
      ∃ β₁ β₂ : ↥((ch82B (fsuV T I) h).subgroupOf (fsuV T I)),
        PtCong (fsuV T I) (ch82B (fsuV T I) h) (ch82U (fsuV T I) h) h g b₁ b₂ β₁ β₂)
    (hspec : ∀ (g : ↥(ob5N0 T I h)) (b₁ b₂ β₁ β₂ : ↥((ch82B (fsuV T I) h).subgroupOf (fsuV T I))),
      PtCong (fsuV T I) (ch82B (fsuV T I) h) (ch82U (fsuV T I) h) h g b₁ b₂ β₁ β₂ →
        ρ g (qb (fsuV T I) (ch82B (fsuV T I) h) (ch82U (fsuV T I) h) b₁,
            qb (fsuV T I) (ch82B (fsuV T I) h) (ch82U (fsuV T I) h) b₂) =
          (qb (fsuV T I) (ch82B (fsuV T I) h) (ch82U (fsuV T I) h) β₁,
            qb (fsuV T I) (ch82B (fsuV T I) h) (ch82U (fsuV T I) h) β₂)) :
    ρ = ob5rho c := by
  refine MonoidHom.ext fun g => AddMonoidHom.ext fun x => ?_
  obtain ⟨x₁, x₂⟩ := x
  obtain ⟨b₁, hb₁⟩ : ∃ b, qb (fsuV T I) (ch82B (fsuV T I) h) (ch82U (fsuV T I) h) b = x₁ :=
    QMod.mk_surjective _ _ x₁
  obtain ⟨b₂, hb₂⟩ : ∃ b, qb (fsuV T I) (ch82B (fsuV T I) h) (ch82U (fsuV T I) h) b = x₂ :=
    QMod.mk_surjective _ _ x₂
  subst hb₁ hb₂
  obtain ⟨β₁, β₂, hc⟩ := htot g b₁ b₂
  exact (hspec g b₁ b₂ β₁ β₂ hc).trans
    (ptActRho_of_cong (ob5_ptActSetup c) g.1 g.2 b₁ b₂ β₁ β₂ hc).symm

theorem ob5_diag_rho (c : S828Ctx T L I H h k)
    [PtActCentralAbelian (pCoreOf 2 (ch82I (fsuV T I) h)) (ch82U (fsuV T I) h)]
    {y₀ : ↥(Subgroup.normalizer (fsuV T I : Set G))}
    (hy : (y₀ : G) ∈ ch82LU L (ch82U (fsuV T I) h))
    {γ : AddMonoid.End (QMod ((ch82B (fsuV T I) h).subgroupOf (fsuV T I))
      ((ch82U (fsuV T I) h).subgroupOf (fsuV T I)))}
    (hγ : Induces γ (⇑(conjAct (fsuV T I) y₀))) :
    diagEnd γ = ob5rho c ⟨(y₀ : G), s828_LU_norm_P c hy, s828_LU_norm_U T L I h hy⟩ := by
  obtain ⟨ρ, -, htot, hspec, -, hdiag, -⟩ := s828_rho c
  have hρ : ρ = ob5rho c := ob5_rho_unique c ρ htot hspec
  have hd := hdiag y₀ hy γ hγ
  rw [hρ] at hd
  exact hd

theorem ob5_indSet_one (c : S828Ctx T L I H h k)
    [PtActCentralAbelian (pCoreOf 2 (ch82I (fsuV T I) h)) (ch82U (fsuV T I) h)]
    (hcon : ∀ (l : G) (hl : l ∈ ob5N0 T I h), l ∈ ch82LU L (ch82U (fsuV T I) h) →
      ob5rho c ⟨l, hl⟩ = 1)
    {γ : AddMonoid.End (QMod ((ch82B (fsuV T I) h).subgroupOf (fsuV T I))
      ((ch82U (fsuV T I) h).subgroupOf (fsuV T I)))}
    (hγ : γ ∈ indSet ((ch82B (fsuV T I) h).subgroupOf (fsuV T I))
      ((ch82U (fsuV T I) h).subgroupOf (fsuV T I))
      ((autOn (ch82LU L (ch82U (fsuV T I) h)) (fsuV T I) : Subgroup (MulAut ↥(fsuV T I))) :
        Set (MulAut ↥(fsuV T I)))) :
    γ = 1 := by
  obtain ⟨g, hg, hγg⟩ := hγ
  obtain ⟨x, hxN, hxL, hxg⟩ := AutOn.mem_autOn_iff_exists.mp hg
  have hγx : Induces γ (⇑(conjAct (fsuV T I) (⟨x, hxN⟩ : ↥(Subgroup.normalizer (fsuV T I : Set G))))) := by
    rw [hxg]
    exact hγg
  have hxN' : x ∈ ob5N0 T I h :=
    Subgroup.mem_inf.mpr ⟨s828_LU_norm_P c hxL, s828_LU_norm_U T L I h hxL⟩
  have hd : diagEnd γ = ob5rho c ⟨x, hxN'⟩ := ob5_diag_rho (y₀ := ⟨x, hxN⟩) c hxL hγx
  have h1 : ob5rho c ⟨x, hxN'⟩ = 1 := hcon x hxN' hxL
  rw [h1] at hd
  ext a
  have h2 := congrArg (fun f : AddMonoid.End (QB (fsuV T I) (ch82B (fsuV T I) h)
      (ch82U (fsuV T I) h) × QB (fsuV T I) (ch82B (fsuV T I) h) (ch82U (fsuV T I) h)) =>
      (f (a, 0)).1) hd
  simpa [diagEnd_apply] using h2

theorem ob5_zero_div_contra (c : S828Ctx T L I H h k)
    [PtActCentralAbelian (pCoreOf 2 (ch82I (fsuV T I) h)) (ch82U (fsuV T I) h)]
    (hQB16 : Nat.card (QB (fsuV T I) (ch82B (fsuV T I) h) (ch82U (fsuV T I) h)) = 16)
    (htop : commutant ((ch82B (fsuV T I) h).subgroupOf (fsuV T I))
      ((ch82U (fsuV T I) h).subgroupOf (fsuV T I))
      ((autOn (ch82LU L (ch82U (fsuV T I) h)) (fsuV T I) : Subgroup (MulAut ↥(fsuV T I))) :
        Set (MulAut ↥(fsuV T I))) = ⊤)
    {F : Type} [Field F]
    (e : ↥(commutant ((ch82B (fsuV T I) h).subgroupOf (fsuV T I))
      ((ch82U (fsuV T I) h).subgroupOf (fsuV T I))
      ((autOn (ch82LU L (ch82U (fsuV T I) h)) (fsuV T I) : Subgroup (MulAut ↥(fsuV T I))) :
        Set (MulAut ↥(fsuV T I)))) ≃+* F) : False := by
  letI := ob5QBModule c
  have hfr : Module.finrank (ZMod 2)
      (QB (fsuV T I) (ch82B (fsuV T I) h) (ch82U (fsuV T I) h)) = 4 := by
    have hpow := Module.natCard_eq_pow_finrank (K := ZMod 2)
      (V := QB (fsuV T I) (ch82B (fsuV T I) h) (ch82U (fsuV T I) h))
    rw [Nat.card_zmod, hQB16] at hpow
    have h' : (2 : ℕ) ^ Module.finrank (ZMod 2)
        (QB (fsuV T I) (ch82B (fsuV T I) h) (ch82U (fsuV T I) h)) = 2 ^ 4 := by
      rw [← hpow]
      norm_num
    exact Nat.pow_right_injective (le_refl 2) h'
  let bas := Module.finBasis (ZMod 2)
    (QB (fsuV T I) (ch82B (fsuV T I) h) (ch82U (fsuV T I) h))
  have hij : (⟨0, by omega⟩ : Fin (Module.finrank (ZMod 2)
      (QB (fsuV T I) (ch82B (fsuV T I) h) (ch82U (fsuV T I) h)))) ≠ ⟨1, by omega⟩ := by
    simp [Fin.ext_iff]
  obtain ⟨p, q, hp, hq, hpq⟩ := ob5_zero_div_end bas hij
  have hpc : p ∈ commutant ((ch82B (fsuV T I) h).subgroupOf (fsuV T I))
      ((ch82U (fsuV T I) h).subgroupOf (fsuV T I))
      ((autOn (ch82LU L (ch82U (fsuV T I) h)) (fsuV T I) : Subgroup (MulAut ↥(fsuV T I))) :
        Set (MulAut ↥(fsuV T I))) := by
    rw [htop]
    exact Subring.mem_top _
  have hqc : q ∈ commutant ((ch82B (fsuV T I) h).subgroupOf (fsuV T I))
      ((ch82U (fsuV T I) h).subgroupOf (fsuV T I))
      ((autOn (ch82LU L (ch82U (fsuV T I) h)) (fsuV T I) : Subgroup (MulAut ↥(fsuV T I))) :
        Set (MulAut ↥(fsuV T I))) := by
    rw [htop]
    exact Subring.mem_top _
  have hprod : (⟨p, hpc⟩ : ↥(commutant ((ch82B (fsuV T I) h).subgroupOf (fsuV T I))
      ((ch82U (fsuV T I) h).subgroupOf (fsuV T I))
      ((autOn (ch82LU L (ch82U (fsuV T I) h)) (fsuV T I) : Subgroup (MulAut ↥(fsuV T I))) :
        Set (MulAut ↥(fsuV T I))))) * ⟨q, hqc⟩ = 0 := Subtype.ext hpq
  have h1 := congrArg e hprod
  rw [map_mul, map_zero] at h1
  rcases mul_eq_zero.mp h1 with h2 | h2
  · apply hp
    have h3 := e.injective (h2.trans (map_zero e).symm)
    exact congrArg Subtype.val h3
  · apply hq
    have h3 := e.injective (h2.trans (map_zero e).symm)
    exact congrArg Subtype.val h3

theorem ob5_LU_nontriv (c : S828Ctx T L I H h k)
    [PtActCentralAbelian (pCoreOf 2 (ch82I (fsuV T I) h)) (ch82U (fsuV T I) h)]
    (hMB2 : MB2_828) (hcard : Mathieu.StmtH13Card)
    (hrow : ∃ n : ℕ, Row711L3Nine T L I n)
    (hQB16 : Nat.card (QB (fsuV T I) (ch82B (fsuV T I) h) (ch82U (fsuV T I) h)) = 16) :
    ∃ (l : G) (hl : l ∈ ob5N0 T I h), l ∈ ch82LU L (ch82U (fsuV T I) h) ∧
      ob5rho c ⟨l, hl⟩ ≠ 1 := by
  by_contra hcon
  push Not at hcon
  have htop : commutant ((ch82B (fsuV T I) h).subgroupOf (fsuV T I))
      ((ch82U (fsuV T I) h).subgroupOf (fsuV T I))
      ((autOn (ch82LU L (ch82U (fsuV T I) h)) (fsuV T I) : Subgroup (MulAut ↥(fsuV T I))) :
        Set (MulAut ↥(fsuV T I))) = ⊤ := by
    rw [eq_top_iff]
    intro φ _
    rw [mem_commutant_iff]
    intro γ hγ
    rw [ob5_indSet_one c hcon hγ, one_mul, mul_one]
  obtain ⟨F, hF, hFin, -, ⟨e⟩⟩ := s828_mb2_field4_G hMB2 hcard c (Or.inl hrow)
  exact ob5_zero_div_contra c hQB16 htop e

end Nt

end CFSG.Quasithin.H13
