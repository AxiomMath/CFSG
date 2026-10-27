module

public import CFSG.Quasithin.EmptyFaithful.S146zUEDlt

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7

namespace S146zU

section Pkg

variable {G : Type} [Group G]

structure GeomPkg (T M A D A₁ : Subgroup G) : Prop where
  le_mcOf : A ≤ mcOf T
  isElemAbelian : IsElemAbelian 2 A
  not_le_pCoreOf : ¬ A ≤ pCoreOf 2 (mcOf T)
  mIdx_pos : 0 < mIdx A (A ⊓ pCoreOf 2 (mcOf T))
  kernel_eq : centralizerMod (quasithinOmegaOneCenter T) A (uOfL22 T M) =
    A ⊓ pCoreOf 2 (mcOf T)
  commutator_le_self : ⁅uOfL22 T M, A⁆ ≤ A
  quadratic : ⁅⁅uOfL22 T M, A⁆, A⁆ ≤ quasithinOmegaOneCenter T
  rank_le : mIdx (uOfL22 T M) (centralizerMod (quasithinOmegaOneCenter T) (uOfL22 T M) A) ≤
    2 * mIdx A (A ⊓ pCoreOf 2 (mcOf T))
  qcrit : QCrit (quasithinOmegaOneCenter T) (VZ T M) (mcOf T) A
  D_eq : D = centralizerMod A₁ (uOfL22 T M) A
  D_le : D ≤ uOfL22 T M
  Z_le_D : quasithinOmegaOneCenter T ≤ D
  normalizes_D : ∀ a ∈ A, ∀ d ∈ D, a * d * a⁻¹ ∈ D
  conj_of_U : ∃ x : G, A = conjSub x (uOfL22 T M) ∧ A₁ = conjSub x (quasithinOmegaOneCenter T)
  A₁_le : A₁ ≤ A
  card_A₁ : Nat.card A₁ = 2
  A₁_inf : A₁ ⊓ quasithinOmegaOneCenter T = ⊥
  commutator_D_le : ⁅A, D⁆ ≤ A₁
  mIdx_D_le : mIdx (uOfL22 T M) D ≤ mIdx A (A ⊓ pCoreOf 2 (mcOf T))
  eq_case : mIdx (uOfL22 T M) (centralizerMod (quasithinOmegaOneCenter T) (uOfL22 T M) A) =
      2 * mIdx A (A ⊓ pCoreOf 2 (mcOf T)) →
    mIdx (uOfL22 T M) D = mIdx A (A ⊓ pCoreOf 2 (mcOf T)) ∧ ⁅A, D⁆ = A₁ ∧ A₁ ≤ uOfL22 T M

end Pkg

section Main

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G}

theorem geom_package_of_lt (S : Setting146 G T M)
    {γ γ' : F8.Geom T (yOfL22 T M) (mcOf T)} {g : ↥(((yOfL22 T M) ⊔ T) ⊔ mcOf T)}
    (s : F8Setup T (VZ T M) (yOfL22 T M) (mcOf T) γ γ' g)
    (hlt : F8.Dγ (VZ T M) (quasithinOmegaOneCenter T) (mcOf T) (g : G) <
      F8.Uγ (VZ T M) (mcOf T) (g : G)) :
    ∃ A D A₁ : Subgroup G, GeomPkg T M A D A₁ := by
  classical
  have hG : IsHTM T M (mcOf T) := S.isHTM_mcOf
  obtain ⟨-, hF98⟩ := S.lemma_14_5_14 (S.isHz_iff.mpr hG)
  obtain ⟨δ, δ', k, sk, hpos, hle⟩ := hF98.exists_setup_of_lt s hlt
  obtain ⟨hq, hr⟩ := hF98.F916_2_aux sk hpos hle
  have hUA : F8.Uγ (VZ T M) (mcOf T) (k : G) ≤ mcOf T := hF98.Uγ_le_H sk
  have hAel : IsElemAbelian 2 (F8.Uγ (VZ T M) (mcOf T) (k : G)) := hF98.isElemAbelian_Uγ
  have h3 := hF98.F913_3 sk (X := VZ T M) (Y := VZ T M) (Or.inl rfl) (Or.inl rfl)
  have hDγ := hF98.Dγ_eq_inf_pCoreOf sk
  have hcard := hF98.card_A₁ (g := k)
  have hA₁A := hF98.A₁_le_Uγ (g := k)
  have h5b := hF98.F913_5b sk
  have hcommA : ∀ a ∈ F8.Uγ (VZ T M) (mcOf T) (k : G), ∀ b ∈ F8.Uγ (VZ T M) (mcOf T) (k : G),
      a * b = b * a := fun a ha b hb => isElemAbelian_comm hAel ha hb
  have hHZ : ∀ x ∈ mcOf T, ∀ z ∈ quasithinOmegaOneCenter T, x * z = z * x := fun x hx z hz =>
    (Subgroup.mem_centralizer_iff.mp hx z hz).symm
  set A := F8.Uγ (VZ T M) (mcOf T) (k : G) with hA
  set D := F8.DH (VZ T M) (quasithinOmegaOneCenter T) (mcOf T) (k : G) with hD
  set A₁ := F8.A₁ (quasithinOmegaOneCenter T) (k : G) with hA₁
  set U := conjClosure (VZ T M) (mcOf T) with hU
  set Z := quasithinOmegaOneCenter T with hZ
  set Q := pCoreOf 2 (mcOf T) with hQ
  have hpU : IsPGroup 2 U := hF98.toHypF91.isPGroup_conjClosure
  have hpA : IsPGroup 2 A := isPGroup_of_isElemAbelian hAel
  have hUN : ∀ x ∈ mcOf T, ∀ u ∈ U, x * u * x⁻¹ ∈ U := fun x hx u hu =>
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure (VZ T M) (mcOf T) hx) u).mp hu
  have hAN₁ : ∀ a ∈ A, a ∈ Subgroup.normalizer (A₁ : Set G) := fun a ha =>
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun x hx =>
      (hcommA a ha x (hA₁A hx)).symm)
  have hUAA : ⁅U, A⁆ ≤ A := h3.trans inf_le_right
  have hAA : ⁅A, A⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr fun a ha =>
    Subgroup.mem_centralizer_iff.mpr fun b hb => (hcommA b hb a ha)
  have hpos' : 0 < mIdx A (A ⊓ Q) := by rw [← hDγ]; exact hpos
  have hrank : mIdx U (centralizerMod Z U A) ≤ 2 * mIdx A (A ⊓ Q) := by
    have hr' := hq.2.2.2.2
    rw [HypF98.relIndex_eq_two_pow_mIdx (Y := centralizerMod Z U A) hpU,
      HypF98.relIndex_eq_two_pow_mIdx (Y := A ⊓ Q) hpA, ← pow_mul] at hr'
    have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hr'
    omega
  have hZD : Z ≤ D := by
    intro z hz
    refine ⟨hF98.V₁_le_Vp.trans (le_conjClosure (VZ T M) (mcOf T)) hz, ?_, fun u hu => ?_⟩
    · rw [normalizer_eq_centralizer_of_card_eq_two hcard]
      exact Subgroup.mem_centralizer_iff.mpr fun a ha => (hHZ a (hUA (hA₁A ha)) z hz)
    · have := hHZ u (hUA hu) z hz
      have e : z * u * z⁻¹ * u⁻¹ = 1 := by
        rw [← this]; group
      rw [e]; exact A₁.one_mem
  have hDnorm : ∀ a ∈ A, ∀ d ∈ D, a * d * a⁻¹ ∈ D := by
    intro a ha d hd
    obtain ⟨hdU, hdN, hdc⟩ := hd
    refine ⟨hUN a (hUA ha) d hdU, ?_, fun u hu => ?_⟩
    · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (hAN₁ a ha) hdN)
        (Subgroup.inv_mem _ (hAN₁ a ha))
    · have key : a * u * a⁻¹ = u := by rw [hcommA a ha u hu]; group
      have e : (a * d * a⁻¹) * u * (a * d * a⁻¹)⁻¹ * u⁻¹ = a * (d * u * d⁻¹ * u⁻¹) * a⁻¹ := by
        calc (a * d * a⁻¹) * u * (a * d * a⁻¹)⁻¹ * u⁻¹
            = (a * d * a⁻¹) * (a * u * a⁻¹) * (a * d * a⁻¹)⁻¹ * (a * u * a⁻¹)⁻¹ := by
              rw [key]
          _ = a * (d * u * d⁻¹ * u⁻¹) * a⁻¹ := by group
      rw [e]
      exact (Subgroup.mem_normalizer_iff.mp (hAN₁ a ha) _).mp (hdc u hu)
  refine ⟨A, D, A₁, ?_⟩
  refine ⟨hUA, hAel, hq.2.2.1, hpos', hDγ, hUAA, ?_, hrank, hq, rfl,
    centralizerMod_le_left _ _ _, hZD, hDnorm, ⟨(k : G), rfl, rfl⟩, hA₁A, hcard,
    by rw [inf_comm]; exact h5b,
    (F8.F87_6 (VZ T M) Z (mcOf T) (k : G)).1, ?_, ?_⟩
  · exact (Subgroup.commutator_mono hUAA le_rfl).trans (hAA ▸ bot_le)
  · rw [hDγ] at hle
    exact hle
  · intro heq
    have heq' : 2 * mIdx A (F8.Dγ (VZ T M) Z (mcOf T) (k : G)) =
        mIdx U (centralizerMod Z U A) := by
      rw [hDγ]; exact heq.symm
    obtain ⟨e1, e2, e3, -, -, e6⟩ := hr heq'
    rw [hDγ] at e1
    have hne : ⁅A, D⁆ ≠ ⊥ := by
      intro hbot
      have hAc : A ≤ centralizerMod Z A D := by
        intro x hx
        refine ⟨hx, hF98.H_normalizes_V₁ (hUA hx), fun d hd => ?_⟩
        have : x * d * x⁻¹ * d⁻¹ ∈ ⁅A, D⁆ := Subgroup.commutator_mem_commutator hx hd
        rw [hbot] at this
        have h1 : x * d * x⁻¹ * d⁻¹ = 1 := by simpa using this
        rw [h1]; exact Z.one_mem
      rw [e2] at hAc
      exact absurd e6 (not_lt_of_ge hAc)
    have hAD : ⁅A, D⁆ = A₁ := (HypF98.eq_bot_or_eq_of_card_eq_two hcard e3).resolve_left hne
    refine ⟨e1.symm, hAD, hAD ▸ ?_⟩
    have h1 : ⁅A, D⁆ ≤ ⁅A, U⁆ := Subgroup.commutator_mono le_rfl (centralizerMod_le_left _ _ _)
    rw [Subgroup.commutator_comm A U] at h1
    exact h1.trans (h3.trans inf_le_left)

theorem geom_package (S : Setting146 G T M)
    (hNT : ∀ b ∈ mcOf T, b ∉ pCoreOf 2 (mcOf T) →
      2 ≤ mIdx (⁅uOfL22 T M, Subgroup.zpowers b⁆ ⊔ quasithinOmegaOneCenter T)
        (quasithinOmegaOneCenter T)) :
    ∃ A D A₁ : Subgroup G, GeomPkg T M A D A₁ := by
  obtain ⟨γ, γ', g, s, hlt⟩ := exists_setup_Dlt S hNT
  exact geom_package_of_lt S s hlt

end Main

end S146zU

end CFSG.Quasithin
