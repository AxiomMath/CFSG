module

public import CFSG.Quasithin.Background.B15P4Layer2Final
public import CFSG.Quasithin.EmptyFaithful.S153LComp
public import CFSG.Quasithin.H13.A5X1367d

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model
open scoped IsMulCommutative

namespace Setting

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting G T L V)

theorem autOn_thompsonJ_le_normalizer (h1222 : Stmt12_2_2)
    (h517 : Stmt5_1_7_one) (hF : CharTwo (Subgroup.centralizer ({S.v12} : Set G)))
    {K : Subgroup (MulAut ↥S.Uv)}
    (hK : IsComponentOf K (autOn (Subgroup.centralizer ({S.v12} : Set G)) S.Uv)) :
    autOn (thompsonJ S.Tv) S.Uv ≤ Subgroup.normalizer (K : Set (MulAut ↥S.Uv)) := by
  have hUe := S.elemAbelian_Uv h1222 h517 hF
  have : IsMulCommutative ↥S.Uv := hUe.1
  have hV : ∀ v : ↥S.Uv, v ^ 2 = 1 := fun v =>
    Subtype.ext (by rw [Subgroup.coe_pow, hUe.2 _ v.2, Subgroup.coe_one])
  set P : Subgroup G := ((Subgroup.normalizer (K : Set (MulAut ↥S.Uv))).comap
    (conjAct S.Uv)).map (Subgroup.normalizer (S.Uv : Set G)).subtype with hP
  have hJP : thompsonJ S.Tv ≤ P := by
    refine iSup₂_le fun A hA => ?_
    intro a ha
    have haN : a ∈ Subgroup.normalizer (S.Uv : Set G) :=
      (hA.1.trans (S.Tv_le_Gv.trans S.Gv_le_normalizer_Uv)) ha
    refine ⟨⟨a, haN⟩, ?_, rfl⟩
    show conjAct S.Uv ⟨a, haN⟩ ∈ Subgroup.normalizer (K : Set (MulAut ↥S.Uv))
    by_cases hAc : A ≤ Subgroup.centralizer (S.Uv : Set G)
    · rw [S.conjAct_Uv_eq_one haN (hAc ha)]
      exact Subgroup.one_mem _
    · have hoff := S.isFFStarOffender_of_mem h1222 h517 hF ⟨hA, hAc⟩
      exact B15P4.asB15Part4 ↥S.Uv hV _ _ hoff K hK
        ⟨⟨a, haN⟩, Subgroup.mem_subgroupOf.mpr ha, rfl⟩
  intro x hx
  obtain ⟨⟨g, hgN⟩, hg, rfl⟩ := hx
  obtain ⟨⟨g', hg'N⟩, hg'P, hg'g⟩ := hJP (Subgroup.mem_subgroupOf.mp hg)
  have : (⟨g', hg'N⟩ : ↥(Subgroup.normalizer (S.Uv : Set G))) = ⟨g, hgN⟩ := Subtype.ext hg'g
  rw [← this]
  exact hg'P

theorem isComponentOf_conj {X K : Subgroup (MulAut ↥S.Uv)} (hK : IsComponentOf K X)
    {g : MulAut ↥S.Uv} (hg : g ∈ X) : IsComponentOf (B6.conjSub g K) X := by
  obtain ⟨hKX, hsn, hq⟩ := hK
  have hXg : B6.conjSub g X = X := by
    ext x
    simp only [B6.conjSub, MulEquiv.mapSubgroup_apply, Subgroup.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩
      show g * y * g⁻¹ ∈ X
      exact X.mul_mem (X.mul_mem hg hy) (X.inv_mem hg)
    · intro hx
      refine ⟨g⁻¹ * x * g, X.mul_mem (X.mul_mem (X.inv_mem hg) hx) hg, ?_⟩
      show g * (g⁻¹ * x * g) * g⁻¹ = x
      group
  refine ⟨?_, ?_, ?_⟩
  · rw [← hXg]
    exact (B6.conjSub g).monotone hKX
  · have h := A3.subnormal_map (MulAut.conj g).toMonoidHom hsn
    rwa [show X.map (MulAut.conj g).toMonoidHom = X from hXg] at h
  · exact (CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (K.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective)
      (B1Red.isQuasisimple_of_open hq)) |> B1Red.isQuasisimple_to_open

theorem JGv_le_centralizer
    (hcent : ∀ K, IsComponentOf K (autOn (Subgroup.centralizer ({S.v12} : Set G)) S.Uv) →
      autOn (thompsonJ S.Tv) S.Uv ≤ Subgroup.centralizer (K : Set (MulAut ↥S.Uv)))
    {K : Subgroup (MulAut ↥S.Uv)}
    (hK : IsComponentOf K (autOn (Subgroup.centralizer ({S.v12} : Set G)) S.Uv)) :
    S.JGv ≤ Subgroup.centralizer (K : Set (MulAut ↥S.Uv)) := by
  refine iSup₂_le fun A hA => iSup₂_le fun g hg => ?_
  have hAJ : autOn A S.Uv ≤ autOn (thompsonJ S.Tv) S.Uv := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := hx
    exact ⟨a, Subgroup.mem_subgroupOf.mpr
      (le_iSup₂_of_le (f := fun B (_ : IsMaxElemAbelian S.Tv B) => B) A hA.1 le_rfl
        (Subgroup.mem_subgroupOf.mp ha)), rfl⟩
  have hK' := S.isComponentOf_conj hK (Subgroup.inv_mem _ hg)
  have hc := hAJ.trans (hcent _ hK')
  rintro _ ⟨x, hx, rfl⟩
  rw [Subgroup.mem_centralizer_iff]
  intro k hk
  have hk' : g⁻¹ * k * g⁻¹⁻¹ ∈ B6.conjSub g⁻¹ K := ⟨k, hk, by simp⟩
  have h1 := Subgroup.mem_centralizer_iff.mp (hc hx) _ hk'
  show k * (MulAut.conj g x) = MulAut.conj g x * k
  rw [MulAut.conj_apply]
  rw [inv_inv] at h1
  calc k * (g * x * g⁻¹) = g * ((g⁻¹ * k * g) * x) * g⁻¹ := by group
    _ = g * (x * (g⁻¹ * k * g)) * g⁻¹ := by rw [h1]
    _ = g * x * g⁻¹ * k := by group

theorem false_of_qs_normal_JGv
    (hcent : ∀ K, IsComponentOf K (autOn (Subgroup.centralizer ({S.v12} : Set G)) S.Uv) →
      autOn (thompsonJ S.Tv) S.Uv ≤ Subgroup.centralizer (K : Set (MulAut ↥S.Uv)))
    {N : Subgroup (MulAut ↥S.Uv)} (hNJ : N ≤ S.JGv) (hNn : ∀ x ∈ S.JGv, ∀ n ∈ N, x * n * x⁻¹ ∈ N)
    (hq : CFSG.IsQuasisimple ↥N) : False := by
  have hNcomp : IsComponentOf N (autOn (Subgroup.centralizer ({S.v12} : Set G)) S.Uv) := by
    refine ⟨hNJ.trans S.JGv_le_GvS, ?_, B1Red.isQuasisimple_to_open hq⟩
    have hJn : (N.subgroupOf S.JGv).Normal :=
      (Subgroup.normal_subgroupOf_iff hNJ).2 fun h k hh hk => hNn k hk h hh
    refine IsSubnormal.step hNJ hJn ?_
    exact IsSubnormal.step S.JGv_le_GvS
      ((Subgroup.normal_subgroupOf_iff_le_normalizer S.JGv_le_GvS).2 S.GvS_le_normalizer_JGv)
      (IsSubnormal.refl _)
  have hc := S.JGv_le_centralizer hcent hNcomp
  have hab : ⁅N, N⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact hNJ.trans hc
  have hperf := S153L.comp_perfect_of_isQuasisimple hq
  rw [hab] at hperf
  exact SBc3.ne_bot_of_isQuasisimple hq hperf.symm

end Setting

end CFSG.Quasithin.H13.A5
