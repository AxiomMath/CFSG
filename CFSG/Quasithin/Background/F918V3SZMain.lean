module

public import CFSG.Quasithin.Background.F918V3Stmt
public import CFSG.Quasithin.Background.F918V3S3Aux
public import CFSG.Quasithin.Background.F918V3SZA
public import CFSG.Quasithin.Background.F918V3SZB
public import CFSG.Quasithin.Background.F918V3SZC2
public import CFSG.Quasithin.Background.F918V3SZD

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique
open scoped Pointwise

theorem d392Suzuki_of_d38 (h38 : D38Top) : D392Suzuki := by
  intro W _ _ M Mp T L V hD hMp hqM _hcase A hA hAT _hunf K hK hKsz hKL a haA x hxK
  subst hMp
  by_contra hne
  have hKA : ¬ A ≤ Subgroup.centralizer (K : Set (MulAut W)) := fun h =>
    hne ((Subgroup.mem_centralizer_iff.mp (h haA) x hxK).symm)
  have hKc : K ∈ cComp M := F918V3S3.mem_cComp_of_isComponentOf hK
  have hKq : CFSG.IsQuasisimple ↥K := A3.isQuasisimple_iff_open.mpr hK.2.2
  obtain ⟨r, hr, hr2, ⟨⟨hA2, -⟩, -⟩, -⟩ := QhatStar_spec hA
  obtain ⟨I, hI, hUA, hKnot⟩ := H13.sz_core h38 hD.hyp.exp hD.hyp.qsqtk hr hr2 hA hD.hyp.sylow hAT
    hKc hKq hKsz hKA
  set U := orbSup T I with hUdef
  set Y := conjClosure K T with hYdef
  have hKM : K ≤ M := hK.1
  have hTM : T ≤ M := hD.hyp.sylow.1
  have hTY : T ≤ Subgroup.normalizer (Y : Set (MulAut W)) := le_normalizer_conjClosure K T
  have hKY : K ≤ Y := le_conjClosure K T
  have hIY : ∀ y ∈ Y, ∀ w ∈ I, y w ∈ I := fun y hy w hw => hI.1.2.1 ⟨y, hy⟩ w hw
  have hYs : Y ≤ stabSub U := H13.le_stabSub_orbSup hTY hIY
  have hTs : T ≤ stabSub U :=
    le_stabSub_of_forall_mem fun t ht w hw => mem_orbSup_of_mem_map ht hw
  have hKs : K ≤ stabSub U := hKY.trans hYs
  have hAk : ∀ a ∈ A, ∀ w : W, a w * w⁻¹ ∈ U := by
    intro a ha w
    obtain ⟨u, hu, c, hc, rfl⟩ := Subgroup.mem_sup.mp (hUA ▸ Subgroup.mem_top w)
    have hac : a c = c := hc a ha
    have hau : a u ∈ U := (hTs (hAT ha) u).mpr hu
    rw [map_mul, hac]
    have e : a u * c * (u * c)⁻¹ = a u * u⁻¹ := by group
    rw [e]
    exact U.mul_mem hau (U.inv_mem hu)
  have hKker := sz_ker_of_not_centralizes hKc hKq hA2.1 hKs (hAT.trans hTs) hAk hKA
  have hYker := sz_ker_conjClosure hKs hTs hKker
  have hUcomm : orbSup T I = commV Y := sz_orbSup_eq_commV hTY hI.1.2 hYker
  have hMn : ∀ m ∈ M, ∀ l ∈ Mp, m * l * m⁻¹ ∈ Mp := fun m hm l hl =>
    ((Subgroup.mem_normalizer_iff.1 (hD.hyp.Mp_normal hm)) l).1 hl
  have hTL : ∀ t ∈ T, ∀ l ∈ Mp, t * l * t⁻¹ ∈ Mp := fun t ht => hMn t (hTM ht)
  have hYC : Y ≤ Subgroup.centralizer (Mp : Set (MulAut W)) := by
    refine conjClosure_le fun t ht k hk => ?_
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have hl' : t⁻¹ * l * t ∈ Mp := by
      have := hTL t⁻¹ (T.inv_mem ht) l hl
      simpa using this
    have h1 := hKL k hk _ hl'
    calc l * (t * k * t⁻¹) = t * ((t⁻¹ * l * t) * k) * t⁻¹ := by group
      _ = t * (k * (t⁻¹ * l * t)) * t⁻¹ := by rw [← h1]
      _ = t * k * t⁻¹ * l := by group
  have hLY : ∀ l ∈ Mp, ∀ y ∈ Y, l * y = y * l := fun l hl y hy =>
    Subgroup.mem_centralizer_iff.mp (hYC hy) l hl
  have hUL : ∀ l ∈ Mp, ∀ u ∈ U, l u ∈ U := by
    intro l hl u hu
    have h1 : u ∈ commV Y := hUcomm ▸ hu
    have h2 := sz_commV_inv hLY l hl u h1
    rwa [← hUcomm] at h2
  have hperfL : ⁅Mp, Mp⁆ = Mp := hD.hyp.comp.2.1
  have hLtriv := sz_L_triv hD.hyp.exp hTY hLY hTL hperfL hI hUL
  have hLU : ∀ l ∈ Mp, ∀ u ∈ U, l u * u⁻¹ ∈ fixV K := fun l hl u hu =>
    fixV_anti hKY (hLtriv l hl u hu)
  have hKperf : ⁅K, K⁆ = K := Subgroup.isPerfect_iff.mp hKq.1
  exact sz_final hD hKM hKL hKperf (ne_bot_of_mem_cComp hKc) hKker hLU

end CFSG.Quasithin
