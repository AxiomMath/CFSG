module

public import CFSG.LocalAnalysis.StandardType.GGTorusGenRDefs
public import CFSG.LocalAnalysis.StandardType.GGLinTwoCent
public import CFSG.LocalAnalysis.StandardType.GGLinTwoComp
public import CFSG.LocalAnalysis.StandardType.GGTableBLinTwoTBFrame
public import CFSG.LocalAnalysis.StandardType.GGTableBLinTwoTBAlg
public import CFSG.LocalAnalysis.StandardType.GGTypeANbrTableBPSL

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB Matrix CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag

theorem ggTorusGenR_linTwo {d : ℕ} {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2)
    (hd : 6 ≤ d) : GGTorusGenR 3 (d / 2) (projectiveSL d K) := by
  classical
  intro E hE hcard hsc x hx hx1 J hJ c hcE hcP
  have hcenter : Subgroup.center (SpecialLinearGroup (Fin d) K) = ⊥ :=
    LineL2.center_eq_bot_two hK
  have hscalars : LinearFlag.scalars d K = ⊥ := by
    rw [LinearFlag.scalars_eq_center, hcenter]
  have hinj : Function.Injective (LinearFlag.proj d K) := by
    rw [injective_iff_map_eq_one]
    intro A hA
    rw [LinearFlag.proj_eq_one_iff] at hA
    rw [hscalars, Subgroup.mem_bot] at hA
    exact hA
  let φ : SpecialLinearGroup (Fin d) K ≃* projectiveSL d K :=
    MulEquiv.ofBijective (LinearFlag.proj d K) ⟨hinj, LinearFlag.proj_surjective d K⟩
  let E' : Subgroup (SpecialLinearGroup (Fin d) K) := E.map φ.symm.toMonoidHom
  have mem_E' : ∀ a : SpecialLinearGroup (Fin d) K, a ∈ E' ↔ φ a ∈ E := by
    intro a
    constructor
    · rintro ⟨y, hy, hay⟩
      rw [← hay]
      simpa using hy
    · intro ha
      exact ⟨φ a, ha, by simp⟩
  have hE' : IsElemAbelian 3 E' := CFSG.Open.IsElemAbelian.map hE φ.symm.toMonoidHom
  have hcard' : 3 ^ (d / 2) ≤ Nat.card E' := by
    rw [Subgroup.card_map_of_injective φ.symm.injective]
    exact hcard
  let ψ : GL (Fin d) K ≃* projectiveSL d K := (LinTwoTB.glEquivSL hK).trans φ
  let E₀ : Subgroup (GL (Fin d) K) := E.map ψ.symm.toMonoidHom
  have mem_E₀ : ∀ g : GL (Fin d) K, g ∈ E₀ ↔ ψ g ∈ E := by
    intro g
    constructor
    · rintro ⟨y, hy, hgy⟩
      rw [← hgy]
      simpa using hy
    · intro hg
      exact ⟨ψ g, hg, by simp⟩
  have hE₀ : IsElemAbelian 3 E₀ := CFSG.Open.IsElemAbelian.map hE ψ.symm.toMonoidHom
  have hcard₀ : 3 ^ (d / 2) ≤ Nat.card E₀ := by
    rw [Subgroup.card_map_of_injective ψ.symm.injective]
    exact hcard
  obtain ⟨t, e₀, D₀, hD₀range, he₀, hD₀wt⟩ := LinTwoTB.exists_torusData hK hE₀ hcard₀
  have hD₀tor : D₀.tor = E₀ := hD₀range
  let D : LinTwoTB.TorusData (projectiveSL d K) t := D₀.map ψ
  have hDel : ∀ v, D.el v = ψ (D₀.el v) := fun v => D₀.el_map ψ v
  have hDtor : D.tor = E := by
    ext y
    constructor
    · intro hy
      obtain ⟨v, hv⟩ := D.mem_tor.mp hy
      rw [hv, hDel]
      exact (mem_E₀ _).mp (by rw [← hD₀tor]; exact D₀.mem_tor.mpr ⟨v, rfl⟩)
    · intro hy
      have h1 : ψ.symm y ∈ E₀ := (mem_E₀ _).mpr (by rw [ψ.apply_symm_apply]; exact hy)
      obtain ⟨v, hv⟩ := D₀.mem_tor.mp (by rw [hD₀tor]; exact h1)
      exact D.mem_tor.mpr ⟨v, by rw [hDel, ← hv, ψ.apply_symm_apply]⟩
  have hc'cent : ∀ e ∈ E', (φ.symm c) * e = e * (φ.symm c) := by
    intro e he
    have h1 : φ e * c = c * φ e :=
      Subgroup.mem_centralizer_iff.mp hcE (φ e) ((mem_E' e).mp he)
    apply φ.injective
    rw [map_mul, map_mul, φ.apply_symm_apply]
    exact h1.symm
  have hc' : φ.symm c ∈ E' := LinTwoGen.cent_le_of_maxRank hK hd hE' hcard' _ hc'cent
  have hcE_mem : c ∈ E := by
    have h := (mem_E' (φ.symm c)).mp hc'
    rwa [φ.apply_symm_apply] at h
  have hx' : φ.symm x ∈ E' := (mem_E' _).mpr (by rw [φ.apply_symm_apply]; exact hx)
  have hx1' : φ.symm x ≠ 1 := by
    intro h
    apply hx1
    have h2 : φ (φ.symm x) = φ 1 := by rw [h]
    rwa [φ.apply_symm_apply, map_one] at h2
  have hJ' : IsComponentOf (J.map φ.symm.toMonoidHom)
      (Subgroup.centralizer ({φ.symm x} : Set (SpecialLinearGroup (Fin d) K))) := by
    have h := isComponentOf_map_mulEquiv' φ.symm hJ
    rwa [CFSG.Fischer.Classification.Recognition.map_centralizer_singleton φ.symm x] at h
  obtain ⟨y, hyJ, hyE, hy1⟩ :=
    LinTwoGen.component_meets_of_maxRank hK hd hE' hcard' hx' hx1' hJ'
  have hyJ' : φ y ∈ J := by
    obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.mp hyJ
    have hzy' : φ y = z := by
      rw [← hzy]
      simp
    rwa [hzy']
  have hyE' : φ y ∈ E := (mem_E' y).mp hyE
  have hy1' : φ y ≠ 1 := by
    intro h
    apply hy1
    apply φ.injective
    rw [h, map_one]
  let S : Subgroup (projectiveSL d K) := J ⊓ E
  have hS_J : S ≤ J := inf_le_left
  have hS_cent : S ≤ Subgroup.centralizer (E : Set (projectiveSL d K)) := by
    intro s hs
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    exact CFSG.Open.IsElemAbelian.comm hE he hs.2
  have hS_pgroup : IsPGroup 3 S := by
    intro s
    refine ⟨1, Subtype.ext ?_⟩
    show (s : projectiveSL d K) ^ 3 = 1
    exact hE.2 (s : projectiveSL d K) s.2.2
  have hW_nrm : (D.wsub : Set (projectiveSL d K)) ⊆
      Subgroup.normalizer (E : Set (projectiveSL d K)) := by
    intro n hn
    have h : n ∈ Subgroup.normalizer (D.tor : Set (projectiveSL d K)) := D.wsub_le_nrm hn
    rwa [hDtor] at h
  let Kgens : Set (projectiveSL d K) :=
    ⋃ n ∈ (D.wsub : Set (projectiveSL d K)),
      (fun s => n * s * n⁻¹) '' (S : Set (projectiveSL d K))
  let H : Subgroup (projectiveSL d K) := Subgroup.closure Kgens
  have hS_le_H : S ≤ H := by
    intro s hs
    apply Subgroup.subset_closure
    change s ∈ ⋃ n ∈ (D.wsub : Set (projectiveSL d K)),
      (fun s => n * s * n⁻¹) '' (S : Set (projectiveSL d K))
    rw [Set.mem_iUnion₂]
    exact ⟨1, D.wsub.one_mem, s, hs, by simp⟩
  have hH_le_E : H ≤ E := by
    change Subgroup.closure (⋃ n ∈ (D.wsub : Set (projectiveSL d K)),
      (fun s => n * s * n⁻¹) '' (S : Set (projectiveSL d K))) ≤ E
    rw [Subgroup.closure_le]
    intro u hu
    simp only [Set.mem_iUnion, Set.mem_image, exists_prop] at hu
    obtain ⟨n, hn, s, hs, rfl⟩ := hu
    exact (Subgroup.mem_normalizer_iff.mp (hW_nrm hn) s).mp hs.2
  have hconj : ∀ n ∈ D.wsub, ∀ h ∈ H, n * h * n⁻¹ ∈ H := by
    intro n hn
    have hmap : H.map (MulAut.conj n).toMonoidHom ≤ H := by
      change (Subgroup.closure Kgens).map (MulAut.conj n).toMonoidHom ≤
        Subgroup.closure Kgens
      rw [MonoidHom.map_closure]
      apply Subgroup.closure_mono
      rintro g ⟨k, hk, rfl⟩
      simp only [Kgens, Set.mem_iUnion, Set.mem_image, exists_prop] at hk ⊢
      obtain ⟨m, hm, s, hs, rfl⟩ := hk
      exact ⟨n * m, D.wsub.mul_mem hn hm, s, hs, by
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group⟩
    intro h hh
    simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using hmap ⟨h, hh, rfl⟩
  let F : AddSubgroup (Fin t → ZMod 3) :=
    { carrier := {v | D.el v ∈ H}
      add_mem' := by
        intro v w hv hw
        change D.el v ∈ H at hv
        change D.el w ∈ H at hw
        change D.el (v + w) ∈ H
        rw [D.el_add]
        exact H.mul_mem hv hw
      zero_mem' := by
        change D.el (0 : Fin t → ZMod 3) ∈ H
        rw [D.el_zero]
        exact H.one_mem
      neg_mem' := by
        intro v hv
        change D.el v ∈ H at hv
        change D.el (-v) ∈ H
        rw [D.el_neg]
        exact H.inv_mem hv }
  have hFsg : ∀ i v, v ∈ F → LinTwoTB.signV i v ∈ F := by
    intro i v hv
    change D.el v ∈ H at hv
    change D.el (LinTwoTB.signV i v) ∈ H
    rw [← D.sg_conj i v]
    exact hconj (D.sg i) (D.sg_mem_wsub i) (D.el v) hv
  have hFsw : ∀ i j v, v ∈ F → LinTwoTB.swapV i j v ∈ F := by
    intro i j v hv
    change D.el v ∈ H at hv
    change D.el (LinTwoTB.swapV i j v) ∈ H
    rw [← D.sw_conj i j v]
    exact hconj (D.sw i j) (D.sw_mem_wsub i j) (D.el v) hv
  have hy_mem_S : φ y ∈ S := ⟨hyJ', hyE'⟩
  have hy_mem_H : φ y ∈ H := hS_le_H hy_mem_S
  have hy_mem_tor : φ y ∈ D.tor := by rw [hDtor]; exact hyE'
  obtain ⟨v, hv⟩ := D.mem_tor.mp hy_mem_tor
  have hvF : v ∈ F := by
    change D.el v ∈ H
    rw [← hv]
    exact hy_mem_H
  have hv0 : v ≠ 0 := by
    intro h0
    apply hy1'
    rw [hv, h0, D.el_zero]
  have hFtop : F = ⊤ := LinTwoTB.eq_top_of_signed F hFsg hFsw ⟨v, hvF, hv0⟩
  have hE_le_H : E ≤ H := by
    intro e he
    have he_tor : e ∈ D.tor := by rw [hDtor]; exact he
    obtain ⟨w, hw⟩ := D.mem_tor.mp he_tor
    have hwtop : w ∈ F := by
      rw [hFtop]
      exact AddSubgroup.mem_top w
    change D.el w ∈ H at hwtop
    rw [hw]
    exact hwtop
  refine ⟨S, (D.wsub : Set (projectiveSL d K)), hS_pgroup, hS_cent, hS_J, hW_nrm, ?_⟩
  show c ∈ H
  exact hE_le_H hcE_mem

end CFSG.StandardType
