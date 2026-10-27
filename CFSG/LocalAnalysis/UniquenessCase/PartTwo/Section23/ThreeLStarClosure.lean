module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P20b
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22rj
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22uc
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I142Abs
public import CFSG.GroupTheory.PerfectCoreSup

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC CFSG.Quasithin Subgroup

section NoFinite

variable {G : Type} [Group G]

theorem calC_of_calC_of_isSubnormal {K H L : Subgroup G} (hL : L ∈ calC K)
    (hKH : CFSG.Open.IsSubnormal K H) : L ∈ calC H :=
  ⟨CFSG.Quasithin.A3.subnormal_trans hL.1 hKH, hL.2.1, hL.2.2⟩

theorem barImage_iSup {H : Subgroup G} {ι : Type} (L : ι → Subgroup G) (hLH : ∀ i, L i ≤ H) :
    barImage H (⨆ i, L i) = ⨆ i, barImage H (L i) := by
  have hsub : (⨆ i, L i).subgroupOf H = ⨆ i, (L i).subgroupOf H := by
    apply Subgroup.map_injective H.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le (iSup_le hLH), Subgroup.map_iSup]
    exact iSup_congr fun i => (Subgroup.map_subgroupOf_eq_of_le (hLH i)).symm
  unfold barImage
  rw [hsub, Subgroup.map_iSup]

private theorem conjClosure_le_of_le {M L : Subgroup G} (hLM : L ≤ M) : conjClosure M L ≤ M := by
  unfold conjClosure
  refine iSup_le fun K => iSup_le fun hK => ?_
  obtain ⟨m, hm, rfl⟩ := hK
  calc L.map (MulAut.conj m).toMonoidHom ≤ M.map (MulAut.conj m).toMonoidHom :=
        Subgroup.map_mono hLM
    _ = M := Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hm)

end NoFinite

section Finite

variable {G : Type} [Group G] [Finite G]

theorem calC_map_conj_of_mem_normalizer {X K : Subgroup G} (hK : K ∈ calC X) {m : G}
    (hm : m ∈ Subgroup.normalizer (X : Set G)) :
    K.map (MulAut.conj m).toMonoidHom ∈ calC X := by
  have h := uc22p22u_calC_conj (X := X) (M := Subgroup.normalizer (X : Set G))
    le_rfl hK ((Subgroup.normalizer (X : Set G)).inv_mem hm)
  simpa [CFSG.Open.uniqueFourConj] using h

theorem isComponentOf_barImage_of_mem_calC {H K : Subgroup G} (hK : K ∈ calC H) :
    CFSG.Open.IsComponentOf (barImage H K) ⊤ := by
  obtain ⟨K', hK', -, -, hqs, hsub⟩ := uc22p22r_bar2_quasisimple_iso hK
  rw [hK'] at hqs hsub
  exact ⟨le_top, hsub, hqs⟩

theorem component_le_normalizer_iSup_of_isComponentOf {X : Type} [Group X] [Finite X]
    {C : Subgroup X} (hC : CFSG.Open.IsComponentOf C ⊤) {ι : Type} {B : ι → Subgroup X}
    (hB : ∀ i, CFSG.Open.IsComponentOf (B i) ⊤) :
    C ≤ Subgroup.normalizer ((⨆ i, B i : Subgroup X) : Set X) := by
  refine uc22p20b_le_normalizer_iSup B C fun i => ?_
  by_cases hCB : C = B i
  · rw [hCB]
    exact Subgroup.le_normalizer
  · have hcomm :=
      CFSG.LocalAnalysis.GLTheoremA.I142.components_commute_of_ne hC (hB i) hCB
    have hcent : C ≤ Subgroup.centralizer (B i : Set X) := by
      intro c hc
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      exact (hcomm c hc b hb).symm
    exact hcent.trans (Subgroup.centralizer_le_normalizer (B i : Set X))

private theorem barPreimage_barImage_eq {H K : Subgroup G} (hKH : K ≤ H) :
    barPreimage H (barImage H K) = K ⊔ pCoreOf 2 H := by
  unfold barPreimage barImage
  rw [QuotientGroup.comap_map_mk', Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hKH,
    sup_comm]
  rfl

private theorem map_conj_le_perfectCore_of_barImage_le_normalizer {H K L : Subgroup G}
    (hKH : K ≤ H) (hperf : ⁅K, K⁆ = K) (hLH : L ≤ H)
    (hbar : barImage H L ≤ Subgroup.normalizer (barImage H K : Set (Bar2 H))) {z : G}
    (hz : z ∈ L) :
    K.map (MulAut.conj z).toMonoidHom ≤ CFSG.Quasithin.perfectCore (K ⊔ pCoreOf 2 H) := by
  have hzH : z ∈ H := hLH hz
  have hzbar : uc22p21cPi H ⟨z, hzH⟩ ∈
      Subgroup.normalizer (barImage H K : Set (Bar2 H)) :=
    hbar (Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 hz))
  have hleP : K.map (MulAut.conj z).toMonoidHom ≤ K ⊔ pCoreOf 2 H := by
    rintro _ ⟨y, hy, rfl⟩
    have hyH : y ∈ H := hKH hy
    have hybar : uc22p21cPi H ⟨y, hyH⟩ ∈ barImage H K :=
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 hy)
    have hzyH : z * y * z⁻¹ ∈ H := H.mul_mem (H.mul_mem hzH hyH) (H.inv_mem hzH)
    have hzybar : uc22p21cPi H ⟨z * y * z⁻¹, hzyH⟩ ∈ barImage H K := by
      have h1 : (⟨z * y * z⁻¹, hzyH⟩ : ↥H) =
          ⟨z, hzH⟩ * ⟨y, hyH⟩ * (⟨z, hzH⟩ : ↥H)⁻¹ :=
        Subtype.ext (by simp [mul_assoc])
      rw [h1]
      exact (Subgroup.mem_normalizer_iff.mp hzbar _).1 hybar
    have hzy : z * y * z⁻¹ ∈ barPreimage H (barImage H K) :=
      (uc22p21c_mem_barPreimage).2 ⟨hzyH, hzybar⟩
    rwa [barPreimage_barImage_eq hKH] at hzy
  have hconjperf : ⁅K.map (MulAut.conj z).toMonoidHom,
      K.map (MulAut.conj z).toMonoidHom⁆ = K.map (MulAut.conj z).toMonoidHom := by
    rw [← Subgroup.map_commutator, hperf]
  exact CFSG.Quasithin.le_perfectCore_of_perfect hleP hconjperf

theorem le_normalizer_of_barImage_le_normalizer {H K L : Subgroup G} (hKH : K ≤ H)
    (hsub : CFSG.Open.IsSubnormal K H) (hperf : ⁅K, K⁆ = K) (hLH : L ≤ H)
    (hbar : barImage H L ≤ Subgroup.normalizer (barImage H K : Set (Bar2 H))) :
    L ≤ Subgroup.normalizer (K : Set G) := by
  have hcore : CFSG.Quasithin.perfectCore (K ⊔ pCoreOf 2 H) = K :=
    CFSG.GroupTheory.perfectCore_sup_pCoreOf_eq hKH hsub hperf
  have hkey : ∀ z ∈ L, K.map (MulAut.conj z).toMonoidHom ≤ K := by
    intro z hz
    calc K.map (MulAut.conj z).toMonoidHom
        ≤ CFSG.Quasithin.perfectCore (K ⊔ pCoreOf 2 H) :=
          map_conj_le_perfectCore_of_barImage_le_normalizer hKH hperf hLH hbar hz
      _ = K := hcore
  intro x hx
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  refine le_antisymm (hkey x hx) ?_
  have hcomp : ((MulAut.conj x).toMonoidHom.comp (MulAut.conj x⁻¹).toMonoidHom) =
      MonoidHom.id G := by
    ext y
    simp [MulAut.conj_apply, mul_assoc]
  calc K = (K.map (MulAut.conj x⁻¹).toMonoidHom).map (MulAut.conj x).toMonoidHom := by
        rw [Subgroup.map_map, hcomp, Subgroup.map_id]
    _ ≤ K.map (MulAut.conj x).toMonoidHom := Subgroup.map_mono (hkey x⁻¹ (L.inv_mem hx))

private theorem barImage_conj_le_normalizer_of_calLOf {T M H K : Subgroup G}
    (hK : K ∈ calLOf T M H) {h : G} (hh : h ∈ H) :
    barImage H (K.map (MulAut.conj h).toMonoidHom) ≤
      Subgroup.normalizer (barImage H K : Set (Bar2 H)) := by
  obtain ⟨⟨hTN, -, -, K₀, hK₀, hKsup⟩, hKsub⟩ := hK
  set Kt : T → Subgroup G := fun t => K₀.map (MulAut.conj (t : G)).toMonoidHom with hKt
  have hKH : K ≤ H := CFSG.Quasithin.A3.subnormal_le hKsub
  have hKtH : ∀ t : T, Kt t ∈ calC H := fun t =>
    calC_of_calC_of_isSubnormal (calC_map_conj_of_mem_normalizer hK₀ (hTN t.2)) hKsub
  have hKth : ∀ t : T, (Kt t).map (MulAut.conj h).toMonoidHom ∈ calC H := fun t =>
    calC_map_conj_of_mem_normalizer (hKtH t) (Subgroup.le_normalizer hh)
  have hKt_le_H : ∀ t : T, (Kt t).map (MulAut.conj h).toMonoidHom ≤ H := by
    intro t
    calc (Kt t).map (MulAut.conj h).toMonoidHom ≤ H.map (MulAut.conj h).toMonoidHom :=
          Subgroup.map_mono (((le_iSup Kt t).trans hKsup.ge).trans hKH)
      _ = H := Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hh)
  have hsup : K.map (MulAut.conj h).toMonoidHom =
      ⨆ t : T, (Kt t).map (MulAut.conj h).toMonoidHom := by
    rw [hKsup, Subgroup.map_iSup]
  have hbar : barImage H (K.map (MulAut.conj h).toMonoidHom) =
      ⨆ t : T, barImage H ((Kt t).map (MulAut.conj h).toMonoidHom) := by
    rw [hsup]
    exact barImage_iSup _ hKt_le_H
  have hbarK : barImage H K = ⨆ t : T, barImage H (Kt t) := by
    rw [hKsup]
    exact barImage_iSup _ fun t => ((le_iSup Kt t).trans hKsup.ge).trans hKH
  rw [hbar, hbarK]
  exact iSup_le fun t =>
    component_le_normalizer_iSup_of_isComponentOf
      (isComponentOf_barImage_of_mem_calC (hKth t))
      (fun s => isComponentOf_barImage_of_mem_calC (hKtH s))

theorem conjClosure_le_normalizer_of_calLOf {T M H K : Subgroup G}
    (hK : K ∈ calLOf T M H) :
    conjClosure H K ≤ Subgroup.normalizer (K : Set G) := by
  have hKsub : CFSG.Open.IsSubnormal K H := hK.2
  have hKperf : ⁅K, K⁆ = K := hK.1.2.1
  have hKH : K ≤ H := CFSG.Quasithin.A3.subnormal_le hKsub
  have hconjNorm : ∀ h ∈ H, K.map (MulAut.conj h).toMonoidHom ≤
      Subgroup.normalizer (K : Set G) := by
    intro h hh
    have hKhH : K.map (MulAut.conj h).toMonoidHom ≤ H := by
      calc K.map (MulAut.conj h).toMonoidHom ≤ H.map (MulAut.conj h).toMonoidHom :=
            Subgroup.map_mono hKH
        _ = H := Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hh)
    exact le_normalizer_of_barImage_le_normalizer hKH hKsub hKperf hKhH
      (barImage_conj_le_normalizer_of_calLOf hK hh)
  unfold conjClosure
  refine iSup_le fun K' => iSup_le fun hK' => ?_
  obtain ⟨h, hh, rfl⟩ := hK'
  exact hconjNorm h hh

theorem inf_conjClosure_le_normalizer_of_calLOf {T M H K : Subgroup G}
    (hK : K ∈ calLOf T M H) :
    M ⊓ conjClosure H K ≤ H ⊓ Subgroup.normalizer (K : Set G) := by
  refine le_inf ?_ ?_
  · exact inf_le_right.trans
      (conjClosure_le_of_le (CFSG.Quasithin.A3.subnormal_le hK.2))
  · exact inf_le_right.trans (conjClosure_le_normalizer_of_calLOf hK)

end Finite

end CFSG.LocalAnalysis.UniquenessCase.UC22
