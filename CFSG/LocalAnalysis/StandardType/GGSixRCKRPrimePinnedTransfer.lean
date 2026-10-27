module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeReturnSpecs
import CFSG.LocalAnalysis.SeitzReduction.SeitzQ2OddSplit
import CFSG.LocalAnalysis.StandardType.GGSixRCKC1Helpers

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.StandardType CFSG.StandardType.GGFinModel
  CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.LieCore
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.Open (StatedLieTag)

theorem rootGroup_isPGroup_of_standardReturnAt
    {M : LieUniversal} {g : ℕ} (hM : StandardReturnAt M g) {γ : Fin M.D.rank → ℤ}
    (hγ : γ ∈ M.D.roots) : IsPGroup 2 (M.D.rootGroup γ) := by
  rcases hM with ⟨t, n, ht, hadm, rfl⟩ | ⟨F, hF, hFin, σ, htri, rfl⟩
  · have h := CFSG.StandardType.RCKC1.rckGH_ggU_ggRootSub_isPGroup t n g ht hadm.2.1 γ hγ 1
    exact h.to_le fun x hx => ⟨x, ⟨x, hx, by simp⟩, rfl⟩
  · exact CFSG.StandardType.RCKC1.rckGH_triD4_rootGroup_isPGroup F σ g htri hγ

private lemma d4_eq_one_of_odd_order_of_pow_two
    {H : Type*} [Group H] {c : H} {k : ℕ}
    (hodd : Odd (orderOf c)) (hpow : c ^ 2 ^ k = 1) : c = 1 := by
  have hdvd : orderOf c ∣ 2 ^ k := orderOf_dvd_iff_pow_eq_one.mpr hpow
  have hcop : Nat.Coprime (orderOf c) (2 ^ k) := hodd.coprime_two_right.pow_right k
  exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd hcop hdvd)

private lemma d4_eq_of_mul_inv_mem_center_of_pow_two
    {H : Type*} [Group H] {y₁ y₂ : H} {k : ℕ}
    (hc : y₁ * y₂⁻¹ ∈ Subgroup.center H) (hodd : Odd (orderOf (y₁ * y₂⁻¹)))
    (h₁ : y₁ ^ 2 ^ k = 1) (h₂ : y₂ ^ 2 ^ k = 1) : y₁ = y₂ := by
  have hcent : Commute (y₁ * y₂⁻¹) y₂ := (Subgroup.mem_center_iff.mp hc y₂).symm
  have hceq : (y₁ * y₂⁻¹) * y₂ = y₁ := by group
  have hpow : (y₁ * y₂⁻¹) ^ 2 ^ k = 1 := by
    have h : ((y₁ * y₂⁻¹) * y₂) ^ 2 ^ k = 1 := by rw [hceq, h₁]
    rw [hcent.mul_pow (2 ^ k), h₂, mul_one] at h
    exact h
  exact mul_inv_eq_one.mp (d4_eq_one_of_odd_order_of_pow_two hodd hpow)

theorem rckPinnedOfFrameCover_holds :
    RCKPinnedOfFrameCover := by
  intro X _ _ τ G₀ K B hK η p₀ S a i h Mod hηker hmap hKq hoddK hBnorm hpartners hcover
  obtain ⟨M, φ, hMod, hstd, hrange, hφker, hfin, hperf, hsplit, ⟨β, hβ, hlong⟩, hdiag⟩ :=
    hcover
  let ηK : ↥K →* ModGL τ GGL := η.comp (Subgroup.inclusion hK)
  have hmapr : (K.subgroupOf G₀).map η = φ.range := hmap.trans hrange.symm
  have hmem : ∀ k : ↥K, ηK k ∈ φ.range := by
    intro k
    have hk : (⟨(k : X), hK k.2⟩ : ↥G₀) ∈ K.subgroupOf G₀ := Subgroup.mem_subgroupOf.mpr k.2
    have h := Subgroup.mem_map_of_mem η (K := K.subgroupOf G₀) hk
    rw [hmapr] at h
    exact h
  let η' : ↥K →* ↥φ.range := ηK.codRestrict φ.range hmem
  have hη'surj : Function.Surjective η' := by
    intro y
    have hy : (y : ModGL τ GGL) ∈ (K.subgroupOf G₀).map η := by
      rw [hmapr]
      exact y.2
    obtain ⟨x, hx, hxη⟩ := Subgroup.mem_map.mp hy
    refine ⟨⟨(x : X), Subgroup.mem_subgroupOf.mp hx⟩, ?_⟩
    apply Subtype.ext
    change η (Subgroup.inclusion hK ⟨(x : X), Subgroup.mem_subgroupOf.mp hx⟩) =
      (y : ModGL τ GGL)
    rw [show Subgroup.inclusion hK ⟨(x : X), Subgroup.mem_subgroupOf.mp hx⟩ = x from
      Subtype.ext rfl, hxη]
  have hη'ker : η'.ker ≤ Subgroup.center ↥K := by
    intro k hk
    rw [Subgroup.mem_center_iff]
    intro m
    have hk1 : ηK k = 1 := congrArg (Subtype.val) hk
    have hkG : Subgroup.inclusion hK k ∈ η.ker := by
      rw [MonoidHom.mem_ker]
      exact hk1
    have hkZ : Subgroup.inclusion hK k ∈ Subgroup.center ↥G₀ := hηker hkG
    have hcomm := (Subgroup.mem_center_iff.mp hkZ) (Subgroup.inclusion hK m)
    exact Subgroup.inclusion_injective hK (by simpa using hcomm)
  have hoddη' : Odd (Nat.card η'.ker) :=
    hoddK.of_dvd_nat (Subgroup.card_dvd_of_le hη'ker)
  have hperfK : Group.IsPerfect ↥K := hKq.1
  obtain ⟨α, hα, hαsurj, -⟩ :=
    @CFSG.SeitzReduction.SeitzQ2.exists_surjective_of_oddCentralSplit
      M.K ↥φ.range ↥K _ _ _ φ.rangeRestrict η' hfin _ hperfK
      hsplit φ.rangeRestrict_surjective hη'surj hη'ker hoddη'
  have hαK : ∀ s : M.K, ηK (α s) = φ s := by
    intro s
    simpa [η'] using congrArg (Subtype.val) (hα s)
  have hαkerZ : α.ker ≤ Subgroup.center M.K := by
    intro s hs
    rw [MonoidHom.mem_ker] at hs
    have hφs : φ s = 1 := by
      have h1 := hαK s
      rw [hs, map_one] at h1
      exact h1.symm
    exact hφker (MonoidHom.mem_ker.mpr hφs)
  refine ⟨M, (M.D.rootGroup β).map (ηK.comp α), (M.D.rootGroup (-β)).map (ηK.comp α),
    ⟨hstd, β, hβ, hlong, α, hαsurj, hαkerZ, rfl, rfl⟩, hMod, ?_⟩
  intro b hb
  obtain ⟨a', ha', hpart⟩ := hpartners b hb
  obtain ⟨g, hg, hdiag'⟩ := hdiag a' ha'
  obtain ⟨u, rfl⟩ := MonoidHom.mem_range.mp hg
  refine ⟨((α u : ↥K) : X), ⟨u, rfl⟩, ?_⟩
  intro γ hγroot
  obtain ⟨hh, hhh, hz⟩ := hdiag' γ hγroot
  refine ⟨hh, hhh, ?_⟩
  intro z hzmem
  have hxK : b⁻¹ * ((α z : ↥K) : X) * b ∈ K :=
    (Subgroup.mem_normalizer_iff''.mp (hBnorm hb) ((α z : ↥K) : X)).mp (α z).2
  let x : ↥K := ⟨b⁻¹ * ((α z : ↥K) : X) * b, hxK⟩
  have hxval : (x : X) = b⁻¹ * ((α z : ↥K) : X) * b := rfl
  have hmemG : b * (x : X) * b⁻¹ ∈ G₀ := by
    have he : b * (x : X) * b⁻¹ = ((α z : ↥K) : X) := by
      rw [hxval]
      group
    rw [he]
    exact hK (α z).2
  have hsub : (⟨b * (x : X) * b⁻¹, hmemG⟩ : ↥G₀) = ⟨((α z : ↥K) : X), hK (α z).2⟩ := by
    apply Subtype.ext
    change b * (x : X) * b⁻¹ = ((α z : ↥K) : X)
    rw [hxval]
    group
  have hηαz : η ⟨((α z : ↥K) : X), hK (α z).2⟩ = a' * η ⟨x, hK hxK⟩ * a'⁻¹ :=
    hsub ▸ hpart ⟨x, hK hxK⟩ hmemG
  have hηx : ηK x = a'⁻¹ * φ z * a' := by
    have h3 : η ⟨x, hK hxK⟩ =
        a'⁻¹ * η ⟨((α z : ↥K) : X), hK (α z).2⟩ * a' := by
      rw [hηαz]
      group
    calc ηK x = η ⟨x, hK hxK⟩ := rfl
      _ = a'⁻¹ * η ⟨((α z : ↥K) : X), hK (α z).2⟩ * a' := h3
      _ = a'⁻¹ * φ z * a' := by
        rw [show η ⟨((α z : ↥K) : X), hK (α z).2⟩ = ηK (α z) from rfl, hαK z]
  let y₁ : ↥K := (α u)⁻¹ * x * α u
  let y₂ : ↥K := α (hh * z * hh⁻¹)
  have hy₁X : (y₁ : X) =
      (b * ((α u : ↥K) : X))⁻¹ * ((α z : ↥K) : X) * (b * ((α u : ↥K) : X)) := by
    simp only [y₁, x, Subgroup.coe_mul, Subgroup.coe_inv]
    group
  have hηy₁ : ηK y₁ = (a' * φ u)⁻¹ * φ z * (a' * φ u) := by
    simp only [y₁, map_mul, map_inv, hηx, hαK u]
    group
  have hηy₂ : ηK y₂ = (a' * φ u)⁻¹ * φ z * (a' * φ u) := by
    simp only [y₂]
    rw [hαK (hh * z * hh⁻¹), ← hz z hzmem]
  have hcker : y₁ * y₂⁻¹ ∈ η'.ker := by
    rw [MonoidHom.mem_ker]
    apply Subtype.ext
    change ηK (y₁ * y₂⁻¹) = 1
    rw [map_mul, map_inv, show ηK y₁ = ηK y₂ from by rw [hηy₁, hηy₂], mul_inv_cancel]
  have hcZ : y₁ * y₂⁻¹ ∈ Subgroup.center ↥K := hη'ker hcker
  have hcodd : Odd (orderOf (y₁ * y₂⁻¹)) :=
    hoddK.of_dvd_nat (Subgroup.orderOf_dvd_natCard (Subgroup.center ↥K) hcZ)
  obtain ⟨k, hk⟩ :=
    (IsPGroup.iff_orderOf.mp (rootGroup_isPGroup_of_standardReturnAt hstd hγroot))
      ⟨z, hzmem⟩
  have hzord : orderOf z = 2 ^ k := by
    rw [← hk]
    exact orderOf_injective (Subgroup.subtype (M.D.rootGroup γ)) Subtype.coe_injective
      ⟨z, hzmem⟩
  have hαzpow : (α z) ^ (2 ^ k) = 1 := by
    rw [← orderOf_dvd_iff_pow_eq_one]
    calc orderOf (α z) ∣ orderOf z := orderOf_map_dvd α z
      _ = 2 ^ k := hzord
  have hαzpowX : (((α z : ↥K) : X)) ^ (2 ^ k) = 1 := by
    rw [← Subgroup.coe_pow, hαzpow, Subgroup.coe_one]
  have hy₁pow : y₁ ^ (2 ^ k) = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one, hy₁X]
    rw [show (b * ((α u : ↥K) : X))⁻¹ * ((α z : ↥K) : X) * (b * ((α u : ↥K) : X)) =
      (b * ((α u : ↥K) : X))⁻¹ * ((α z : ↥K) : X) *
        ((b * ((α u : ↥K) : X))⁻¹)⁻¹ by rw [inv_inv]]
    rw [conj_pow, hαzpowX, mul_one, mul_inv_cancel]
  have hy₂pow : y₂ ^ (2 ^ k) = 1 := by
    rw [← orderOf_dvd_iff_pow_eq_one]
    simp only [y₂]
    calc orderOf (α (hh * z * hh⁻¹)) ∣ orderOf (hh * z * hh⁻¹) := orderOf_map_dvd α _
      _ = orderOf z := by
        rw [← MulAut.conj_apply hh z]
        exact orderOf_injective (MulAut.conj hh).toMonoidHom (MulAut.conj hh).injective z
      _ = 2 ^ k := hzord
  have hfinal : y₁ = y₂ :=
    d4_eq_of_mul_inv_mem_center_of_pow_two hcZ hcodd hy₁pow hy₂pow
  calc (b * ((α u : ↥K) : X))⁻¹ * ((α z : ↥K) : X) * (b * ((α u : ↥K) : X))
      = (y₁ : X) := hy₁X.symm
    _ = (y₂ : X) := by rw [hfinal]
    _ = ((α (hh * z * hh⁻¹) : ↥K) : X) := rfl

end CFSG.StandardType.RCKRP
