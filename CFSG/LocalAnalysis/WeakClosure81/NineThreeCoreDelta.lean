module

public import CFSG.LocalAnalysis.WeakClosure81.NineThreeFibreIota

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.CGT.Timmesfeld75 Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G] {V T A K S X : Subgroup G} {p : ℕ} {g x : G}

private theorem nine3_conjSubgroup_iSup {ι : Sort*} (B : ι → Subgroup G) (g : G) :
    conjSubgroup (⨆ i, B i) g = ⨆ i, conjSubgroup (B i) g := by
  simp only [CFSG.Quasithin.conjSubgroup]
  exact Subgroup.map_iSup _ _

private theorem nine3_conj_iSup₂ {ι : Type*} (S : Set ι) (B : ι → Subgroup G) (g : G) :
    conjSubgroup (⨆ i ∈ S, B i) g = ⨆ i ∈ S, conjSubgroup (B i) g := by
  apply le_antisymm
  · rw [nine3_conjSubgroup_iSup]
    refine iSup_le fun i => ?_
    rw [nine3_conjSubgroup_iSup]
    refine iSup_le fun hi => ?_
    exact le_iSup₂_of_le i hi le_rfl
  · refine iSup₂_le fun i hi => ?_
    exact E3.conjSubgroup_mono_left g (le_iSup₂_of_le i hi le_rfl)

private theorem nine3_commutator_mem_nineI_aux {i w : G} (hi : i ∈ nineI V K) (hw : w ∈ K) :
    ⁅i, w⁆ ∈ nineI V K := by
  have hwi : w * i * w⁻¹ ∈ nineI V K := by
    have hconj := Nine3Core.conjSubgroup_nineI (V := V) (K := K) (K.inv_mem hw)
    rw [← hconj]
    exact mem_conjSubgroup_iff.mpr (by
      have h1 : w⁻¹ * (w * i * w⁻¹) * (w⁻¹)⁻¹ = i := by group
      rw [h1]
      exact hi)
  have hcomm : ⁅w, i⁆ ∈ nineI V K := (nineI V K).mul_mem hwi ((nineI V K).inv_mem hi)
  have heq : ⁅i, w⁆ = ⁅w, i⁆⁻¹ := (commutatorElement_inv (g₁ := w) (g₂ := i)).symm
  rw [heq]
  exact (nineI V K).inv_mem hcomm

private theorem nine3_delta_mul (hI : Nine3IFacts V K S) {c : G} (hcK : c ∈ K) {x y : G}
    (hx : x ∈ nineI V K) (hy : y ∈ nineI V K) :
    ⁅x * y, c⁆ = ⁅x, c⁆ * ⁅y, c⁆ := by
  have hx' : ⁅x, c⁆ ∈ nineI V K := nine3_commutator_mem_nineI_aux hx hcK
  have hy' : ⁅y, c⁆ ∈ nineI V K := nine3_commutator_mem_nineI_aux hy hcK
  rw [commutatorElement_mul_left_eq_conj_mul]
  have hconj : x * ⁅y, c⁆ * x⁻¹ = ⁅y, c⁆ := by
    rw [CFSG.Open.IsElemAbelian.comm hI.abelian hx hy']
    group
  rw [hconj]
  exact (CFSG.Open.IsElemAbelian.comm hI.abelian hx' hy').symm

private theorem nine3_delta_inv (hI : Nine3IFacts V K S) {c : G} (hcK : c ∈ K) {x : G}
    (hx : x ∈ nineI V K) : ⁅x⁻¹, c⁆ = ⁅x, c⁆⁻¹ := by
  have hx' : ⁅x, c⁆ ∈ nineI V K := nine3_commutator_mem_nineI_aux hx hcK
  rw [commutatorElement_inv_left]
  have hcx : ⁅c, x⁆ = ⁅x, c⁆⁻¹ := (commutatorElement_inv (g₁ := x) (g₂ := c)).symm
  rw [hcx, CFSG.Open.IsElemAbelian.comm hI.abelian ((nineI V K).inv_mem hx)
    ((nineI V K).inv_mem hx')]
  group

private theorem nine3_delta_conj (hc : Nine3Choice V T A K S X p g x) (hI : Nine3IFacts V K S)
    {c : G} (hcK : c ∈ K) (hcH : ∀ h ∈ nineH V K, ⁅c, h⁆ ∈ nineI V K) {h i : G}
    (hh : h ∈ nineH V K) (hi : i ∈ nineI V K) :
    ⁅h * i * h⁻¹, c⁆ = h * ⁅i, c⁆ * h⁻¹ := by
  have hι : ⁅h⁻¹, c⁆ ∈ nineI V K := by
    have h1 : ⁅c, h⁻¹⁆ ∈ nineI V K := hcH h⁻¹ ((nineH V K).inv_mem hh)
    have h2 : ⁅h⁻¹, c⁆ = ⁅c, h⁻¹⁆⁻¹ := (commutatorElement_inv (g₁ := c) (g₂ := h⁻¹)).symm
    rw [h2]
    exact (nineI V K).inv_mem h1
  have hkey : h⁻¹ * c * h = ⁅h⁻¹, c⁆ * c := by
    rw [commutatorElement_def]
    group
  have hstep : h * ⁅i, h⁻¹ * c * h⁆ * h⁻¹ = ⁅h * i * h⁻¹, c⁆ := by
    rw [conjugate_commutatorElement]
    congr 1
    group
  have hcomm : ⁅i, ⁅h⁻¹, c⁆ * c⁆ = ⁅i, c⁆ := by
    rw [commutatorElement_mul_right_eq_mul_conj]
    have h1 : ⁅i, ⁅h⁻¹, c⁆⁆ = 1 :=
      commutatorElement_eq_one_iff_mul_comm.mpr
        (CFSG.Open.IsElemAbelian.comm hI.abelian hi hι)
    rw [h1, one_mul, CFSG.Open.IsElemAbelian.comm hI.abelian hι
      (nine3_commutator_mem_nineI_aux hi hcK)]
    group
  calc ⁅h * i * h⁻¹, c⁆ = h * ⁅i, h⁻¹ * c * h⁆ * h⁻¹ := hstep.symm
    _ = h * ⁅i, ⁅h⁻¹, c⁆ * c⁆ * h⁻¹ := by rw [hkey]
    _ = h * ⁅i, c⁆ * h⁻¹ := by rw [hcomm]

private theorem nine3_delta_comm (hc : Nine3Choice V T A K S X p g x) (hI : Nine3IFacts V K S)
    {c : G} (hcK : c ∈ K) (hcH : ∀ h ∈ nineH V K, ⁅c, h⁆ ∈ nineI V K) {i u : G}
    (hi : i ∈ nineI V K) (hu : u ∈ nineH V K) :
    ⁅⁅i, u⁆, c⁆ = ⁅⁅i, c⁆, u⁆ := by
  have huK : u ∈ K := Nine3Choice.nineH_le_K hu
  have ha : u * i * u⁻¹ ∈ nineI V K := by
    have hmem' : u * i * u⁻¹ ∈ conjSubgroup (nineI V K) u⁻¹ :=
      mem_conjSubgroup_iff.mpr (by
        have h1 : u⁻¹ * (u * i * u⁻¹) * (u⁻¹)⁻¹ = i := by group
        rw [h1]
        exact hi)
    rwa [Nine3Core.conjSubgroup_nineI (V := V) (K := K) (K.inv_mem huK)] at hmem'
  have hdecomp : ⁅i, u⁆ = i * (u * i * u⁻¹)⁻¹ := by
    rw [commutatorElement_def]
    group
  have hconj := nine3_delta_conj hc hI hcK hcH hu hi
  calc ⁅⁅i, u⁆, c⁆ = ⁅i * (u * i * u⁻¹)⁻¹, c⁆ := by rw [hdecomp]
    _ = ⁅i, c⁆ * ⁅(u * i * u⁻¹)⁻¹, c⁆ :=
        nine3_delta_mul hI hcK hi ((nineI V K).inv_mem ha)
    _ = ⁅i, c⁆ * ⁅u * i * u⁻¹, c⁆⁻¹ := by rw [nine3_delta_inv hI hcK ha]
    _ = ⁅i, c⁆ * (u * ⁅i, c⁆ * u⁻¹)⁻¹ := by rw [hconj]
    _ = ⁅⁅i, c⁆, u⁆ := by
        rw [commutatorElement_def]
        group

private def nine3_deltaHom (hI : Nine3IFacts V K S) {c : G} (hcK : c ∈ K) :
    ↥(nineI V K) →* ↥(nineI V K) where
  toFun i := ⟨⁅(i : G), c⁆, nine3_commutator_mem_nineI_aux i.2 hcK⟩
  map_one' := by
    apply Subtype.ext
    simp [commutatorElement_def]
  map_mul' := fun i j => Subtype.ext (nine3_delta_mul hI hcK i.2 j.2)

theorem nine3_delta_zero (hc : Nine3Choice V T A K S X p g x) (hI : Nine3IFacts V K S) {c : G}
    (hcK : c ∈ K) (hcH : ∀ h ∈ nineH V K, ⁅c, h⁆ ∈ nineI V K)
    (hcJ : ∀ i ∈ nineI V K, ⁅i, c⁆ ∈ ⨆ B ∈ nineOmegaIn V K S, B ⊓ pCoreOf 2 K) :
    ∀ i ∈ nineI V K, ⁅i, c⁆ = 1 := by
  haveI : Fact p.Prime := ⟨hc.core.hyp.base.prime⟩
  let δ : ↥(nineI V K) →* ↥(nineI V K) := nine3_deltaHom hI hcK
  let N : Subgroup G := δ.range.map (nineI V K).subtype
  have hδ_apply : ∀ i : ↥(nineI V K), ((δ i : ↥(nineI V K)) : G) = ⁅(i : G), c⁆ := fun _ => rfl
  have hN_gen : ∀ i : ↥(nineI V K), ((δ i : ↥(nineI V K)) : G) ∈ N := fun i =>
    Subgroup.mem_map_of_mem (nineI V K).subtype (MonoidHom.mem_range.mpr ⟨i, rfl⟩)
  have hN_le_J : N ≤ ⨆ B ∈ nineOmegaIn V K S, B ⊓ pCoreOf 2 K := by
    rintro x ⟨y, hy, rfl⟩
    obtain ⟨i, rfl⟩ := MonoidHom.mem_range.mp hy
    change ((δ i : ↥(nineI V K)) : G) ∈ ⨆ B ∈ nineOmegaIn V K S, B ⊓ pCoreOf 2 K
    exact hcJ (i : G) i.2
  have hN_inv_conj : ∀ h ∈ nineH V K, ∀ n ∈ N, h⁻¹ * n * h ∈ N := by
    intro h hh n hn
    obtain ⟨y, hy, rfl⟩ := hn
    obtain ⟨i, rfl⟩ := MonoidHom.mem_range.mp hy
    have hmemI : h⁻¹ * (i : G) * h ∈ nineI V K := by
      have hmem' : h⁻¹ * (i : G) * h ∈ conjSubgroup (nineI V K) h :=
        mem_conjSubgroup_iff.mpr (by
          have h1 : h * (h⁻¹ * (i : G) * h) * h⁻¹ = (i : G) := by group
          rw [h1]
          exact i.2)
      rwa [Nine3Core.conjSubgroup_nineI (V := V) (K := K)
        (Nine3Choice.nineH_le_K hh)] at hmem'
    have hval : h⁻¹ * ((δ i : ↥(nineI V K)) : G) * h =
        ((δ ⟨h⁻¹ * (i : G) * h, hmemI⟩ : ↥(nineI V K)) : G) := by
      rw [hδ_apply, hδ_apply]
      simpa only [inv_inv] using
        (nine3_delta_conj hc hI hcK hcH ((nineH V K).inv_mem hh) i.2).symm
    change h⁻¹ * ((δ i : ↥(nineI V K)) : G) * h ∈ N
    rw [hval]
    exact hN_gen ⟨h⁻¹ * (i : G) * h, hmemI⟩
  have hN_conj_le : ∀ h ∈ nineH V K, conjSubgroup N h ≤ N := by
    intro h hh x hx
    rw [mem_conjSubgroup_iff] at hx
    have h1 := hN_inv_conj h hh (h * x * h⁻¹) hx
    rwa [show h⁻¹ * (h * x * h⁻¹) * h = x by group] at h1
  have hN_conj_eq : ∀ h ∈ nineH V K, conjSubgroup N h = N := by
    intro h hh
    refine le_antisymm (hN_conj_le h hh) ?_
    have h1 := hN_conj_le h⁻¹ ((nineH V K).inv_mem hh)
    have h2 : conjSubgroup (conjSubgroup N h⁻¹) h ≤ conjSubgroup N h :=
      E3.conjSubgroup_mono_left h h1
    rwa [CFSG.Quasithin.conjSubgroup_conjSubgroup, inv_mul_cancel,
      CFSG.Quasithin.conjSubgroup_one] at h2
  have hN_le_conjJ : ∀ h ∈ nineH V K,
      N ≤ conjSubgroup (⨆ B ∈ nineOmegaIn V K S, B ⊓ pCoreOf 2 K) h := by
    intro h hh
    rw [← hN_conj_eq h hh]
    exact E3.conjSubgroup_mono_left h hN_le_J
  obtain ⟨ρ, hρ⟩ := nine3_exists_fibreAct hc
  have hN_inf_U : ∀ U ∈ omegaIn V K (nineE V K), N ⊓ U = ⊥ := by
    intro U hU
    obtain ⟨cU, hcU⟩ := nine3_exists_fib hc hρ hU
    let c' : ZMod p := cU + 1
    have hc'ne : c' ≠ cU := by
      intro h
      have h' : cU + 1 = cU := h
      have h1 : cU + (1 : ZMod p) = cU + 0 := by rw [h', add_zero]
      exact one_ne_zero (add_left_cancel_iff.mp h1)
    obtain ⟨U'', hU''Ω, hU''fib⟩ := nine3_exists_fib_over hc hρ c'
    obtain ⟨h, hhH, hU''eq⟩ := hc.nineH_transitive hU''Ω
    have hhK : h ∈ K := Nine3Choice.nineH_le_K hhH
    let Y : Subgroup G :=
      ⨆ U₁ ∈ ({U₁ : Subgroup G | U₁ ∈ omegaIn V K (nineE V K) ∧
        Nine3Fib K p ρ U₁ c'} : Set (Subgroup G)), U₁
    have hJ_le_Y : conjSubgroup (⨆ B ∈ nineOmegaIn V K S, B ⊓ pCoreOf 2 K) h ≤ Y := by
      rw [nine3_conj_iSup₂ (nineOmegaIn V K S) (fun B => B ⊓ pCoreOf 2 K) h]
      refine iSup₂_le fun B hB => ?_
      obtain ⟨r, hr, hBr⟩ := (hc.core.mem_nineOmegaIn_iff).mp hB
      have hkR : h⁻¹ * r * h ∈ pCoreOf 2 K := by
        simpa only [inv_inv] using
          (Nine3Core.mem_pCoreOf_conj_iff K (K.inv_mem hhK)).mp hr
      have hkK : h⁻¹ * r * h ∈ K := CFSG.LieType.BorelTits.pCoreOf_le 2 K hkR
      have hBeq : conjSubgroup B h = conjSubgroup U'' (h⁻¹ * r * h) := by
        rw [hBr, hU''eq, CFSG.Quasithin.conjSubgroup_conjSubgroup,
          CFSG.Quasithin.conjSubgroup_conjSubgroup]
        congr 1
        group
      have hk0 : ∀ i : ZMod p, ρ ⟨h⁻¹ * r * h, hkK⟩ i = i + 0 := by
        intro i
        rw [hρ.le_ker ⟨h⁻¹ * r * h, hkK⟩ hkR]
        simp
      have hfib' : Nine3Fib K p ρ (conjSubgroup U'' (h⁻¹ * r * h)) c' := by
        have h1 := nine3_fib_conj hU''fib hk0
        have h2 : c' - 0 = c' := by ring
        rwa [h2] at h1
      have hΩ' : conjSubgroup U'' (h⁻¹ * r * h) ∈ omegaIn V K (nineE V K) :=
        conjSubgroup_mem_omegaIn hU''Ω hkK
      calc conjSubgroup (B ⊓ pCoreOf 2 K) h ≤ conjSubgroup B h :=
            E3.conjSubgroup_mono_left h inf_le_left
        _ = conjSubgroup U'' (h⁻¹ * r * h) := hBeq
        _ ≤ Y := le_iSup₂_of_le _ ⟨hΩ', hfib'⟩ le_rfl
    have hY_le_cent : Y ≤ Subgroup.centralizer (U'' : Set G) := by
      refine iSup₂_le fun U₁ hU₁ => ?_
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact (nine3_fib_comm hc hρ hU₁.1 hU''Ω hU₁.2 hU''fib x hx y hy).symm
    have hN_le_cent : N ≤ Subgroup.centralizer (U'' : Set G) :=
      (hN_le_conjJ h hhH).trans (hJ_le_Y.trans hY_le_cent)
    have hbot : U ⊓ Subgroup.centralizer (U'' : Set G) = ⊥ :=
      nine3_fib_inf_centralizer hc hρ hU''Ω hU hU''fib hcU hc'ne
    refine le_bot_iff.mp ?_
    calc N ⊓ U ≤ Subgroup.centralizer (U'' : Set G) ⊓ U :=
          le_inf (le_trans inf_le_left hN_le_cent) inf_le_right
      _ = U ⊓ Subgroup.centralizer (U'' : Set G) := inf_comm _ _
      _ = ⊥ := hbot
  have hI_le_ker : nineI V K ≤ δ.ker.map (nineI V K).subtype := by
    unfold nineI
    refine iSup₂_le fun U hU => ?_
    rw [← nine3_comm_of_mem_omegaIn hc hI hU]
    refine Subgroup.commutator_le.mpr fun i hi u hu => ?_
    have hui : ⁅i, u⁆ ∈ nineI V K := nine3_commutator_mem_nineI_aux hi (hU.2 hu)
    have hδ : δ ⟨⁅i, u⁆, hui⟩ = 1 := by
      apply Subtype.ext
      have hmemN : ((δ ⟨⁅i, u⁆, hui⟩ : ↥(nineI V K)) : G) ∈ N := hN_gen ⟨⁅i, u⁆, hui⟩
      have hmemU : ((δ ⟨⁅i, u⁆, hui⟩ : ↥(nineI V K)) : G) ∈ U := by
        have huH : u ∈ nineH V K := (le_iSup₂_of_le U hU le_rfl : U ≤ nineH V K) hu
        have hcomm := nine3_delta_comm hc hI hcK hcH hi huH
        rw [hδ_apply, hcomm]
        have hmem : ⁅((δ ⟨i, hi⟩ : ↥(nineI V K)) : G), u⁆ ∈ ⁅nineI V K, U⁆ :=
          Subgroup.commutator_mem_commutator (δ ⟨i, hi⟩).2 hu
        rw [nine3_comm_of_mem_omegaIn hc hI hU] at hmem
        exact hmem.1
      have hmem : ((δ ⟨⁅i, u⁆, hui⟩ : ↥(nineI V K)) : G) ∈ N ⊓ U := ⟨hmemN, hmemU⟩
      rw [hN_inf_U U hU] at hmem
      simpa using hmem
    exact ⟨⟨⁅i, u⁆, hui⟩, MonoidHom.mem_ker.mpr hδ, rfl⟩
  intro i hi
  have hmem : i ∈ δ.ker.map (nineI V K).subtype := hI_le_ker hi
  rw [Subgroup.mem_map] at hmem
  obtain ⟨y, hy, hyi⟩ := hmem
  have hy1 : δ y = 1 := MonoidHom.mem_ker.mp hy
  have hy_eq : y = ⟨i, hi⟩ := Subtype.ext hyi
  rw [hy_eq] at hy1
  have h2 : ((δ ⟨i, hi⟩ : ↥(nineI V K)) : G) = 1 := by rw [hy1]; rfl
  simpa only [hδ_apply] using h2

end CFSG.LocalAnalysis.WeakClosure81
