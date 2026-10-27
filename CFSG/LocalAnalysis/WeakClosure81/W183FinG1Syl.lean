module

public import CFSG.LocalAnalysis.WeakClosure81.W183FinL34Ti
public import CFSG.LocalAnalysis.WeakClosure81.W183FinL34Cfg
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallL34Out

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Open
open CFSG.Blueprint (LieModel)

namespace W183L34

open CFSG.PSL3Four CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
open CFSG.ComponentClassification.GrSLit.L34Facts

@[expose] def hW : List ℕ := [1]

@[expose] def gAW : List ℕ := [1, 0, 1, 0, 0]

@[expose] def gAiW : List ℕ := [0, 1, 0, 0, 1]

@[expose] def gSW : List ℕ := [1]

@[expose] def yW : List ℕ := [1, 0, 2, 0, 2, 0, 0, 2, 0, 0, 1]

@[expose] def conjN (g gi x : Nat) : Nat := compN (compN g x) gi

@[expose] def memN (x : Nat) (L : List Nat) : Bool := L.any (eqN x)

@[expose] def inP (x : Nat) : Bool := memN (compN x (wN hW)) (c1N.map (compN (wN hW)))

private def A'N : List Nat := z0N.map (conjN (wN gAW) (wN gAiW))

private def XN : List Nat := z0N.map (conjN (wN gSW) (wN gSW))

private theorem w183finL34_repConjN {gp gx gi : Equiv.Perm (Fin 42)} {p x i : Nat}
    (hp : RepN p gp) (hx : RepN x gx) (hi : RepN i gi) :
    RepN (conjN p i x) (gp * gx * gi) := by
  unfold conjN
  exact (hp.comp hx).comp hi

private theorem w183finL34_commN_imp {a b : Nat} {ga gb : Equiv.Perm (Fin 42)}
    (ha : RepN a ga) (hb : RepN b gb) (h : commN a b = true) : ga * gb = gb * ga := by
  rw [commN] at h
  exact (RepN.eq_iff (ha.comp hb) (hb.comp ha)).1 h

private theorem w183finL34_all_false {L : List Nat} {p : Nat → Bool} (h : L.all p = false) :
    ∃ x ∈ L, p x = false := by
  obtain ⟨x, hx, hpx⟩ := List.all_eq_false.mp h
  exact ⟨x, hx, by simpa using hpx⟩

private theorem w183finL34_z0W_sq {w : List ℕ} (hw : w ∈ z0W) :
    wordPerm w * wordPerm w = 1 := by
  have h := List.all_eq_true.1 z0_inv (wN w) (List.mem_map.2 ⟨w, hw, rfl⟩)
  exact (RepN.eq_iff ((repN_wN w).comp (repN_wN w)) RepN.one).1 h

private theorem w183finL34_inP_imp {x : Nat}
    {g : Equiv.Perm (Fin 42)} (hx : RepN x g) (h : inP x = true) :
    g ∈ C₁.map (MulAut.conj (wordPerm hW)).toMonoidHom := by
  rw [inP, memN, List.any_eq_true] at h
  obtain ⟨y, hy, hxy⟩ := h
  obtain ⟨cN, hcN, rfl⟩ := List.mem_map.1 hy
  obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hcN
  have hxy' : g * wordPerm hW = wordPerm hW * wordPerm w :=
    (RepN.eq_iff (hx.comp (repN_wN hW)) ((repN_wN hW).comp (repN_wN w))).1 hxy
  refine Subgroup.mem_map.2 ⟨wordPerm w, wordPerm_mem_c1 hw, ?_⟩
  change wordPerm hW * wordPerm w * (wordPerm hW)⁻¹ = g
  rw [← hxy']
  group

theorem witness_Z0 :
    ∃ P : Subgroup (Equiv.Perm (Fin 42)), P ≤ S ∧ IsPGroup 2 P ∧
      ∃ gA ∈ S, ∃ gS ∈ S, ∃ y ∈ S, CfgData Z0 P gA gS y := by
  have hzP : z0N.all inP = true := by decide +kernel
  have hA'P : A'N.all inP = true := by decide +kernel
  have hXP : XN.all inP = true := by decide +kernel
  have hyP : inP (wN yW) = true := by decide +kernel
  have hgAinv : eqN (compN (wN gAW) (wN gAiW)) idN = true := by decide +kernel
  have hy2 : eqN (compN (wN yW) (wN yW)) idN = true := by decide +kernel
  have hgS2 : eqN (compN (wN gSW) (wN gSW)) idN = true := by decide +kernel
  have hyne : (z0N.all fun a => memN (conjN (wN yW) (wN yW) a) z0N) = false := by
    decide +kernel
  have hcomm : (z0N.all fun s => XN.any fun z =>
      eqN (conjN (wN yW) (wN yW) s) (compN s z)) = true := by decide +kernel
  have hnorm : (z0N.all fun a => A'N.all fun x => memN (conjN a a x) A'N) = false := by
    decide +kernel
  have hcommAX : (A'N.all fun a => XN.all fun x => commN a x) = true := by decide +kernel
  have hgi : wordPerm gAiW = (wordPerm gAW)⁻¹ :=
    eq_inv_of_mul_eq_one_right
      ((RepN.eq_iff ((repN_wN gAW).comp (repN_wN gAiW)) RepN.one).1 hgAinv)
  have hyinv : wordPerm yW = (wordPerm yW)⁻¹ :=
    eq_inv_of_mul_eq_one_right
      ((RepN.eq_iff ((repN_wN yW).comp (repN_wN yW)) RepN.one).1 hy2)
  have hgsinv : wordPerm gSW = (wordPerm gSW)⁻¹ :=
    eq_inv_of_mul_eq_one_right
      ((RepN.eq_iff ((repN_wN gSW).comp (repN_wN gSW)) RepN.one).1 hgS2)
  refine ⟨C₁.map (MulAut.conj (wordPerm hW)).toMonoidHom, ?_, ?_,
    wordPerm gAW, wordPerm_mem gAW, wordPerm gSW, wordPerm_mem gSW,
    wordPerm yW, wordPerm_mem yW, ?_⟩
  · intro x hx
    obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.1 hx
    have hcS : c ∈ S := (Subgroup.mem_inf.1 hc).2
    change wordPerm hW * c * (wordPerm hW)⁻¹ ∈ S
    exact S.mul_mem (S.mul_mem (wordPerm_mem hW) hcS) (S.inv_mem (wordPerm_mem hW))
  · have hC1 : IsPGroup 2 C₁ := IsPGroup.of_card (n := 6) (by rw [card_C₁]; norm_num)
    exact hC1.of_equiv (Subgroup.equivMapOfInjective C₁
      (MulAut.conj (wordPerm hW)).toMonoidHom (MulAut.conj (wordPerm hW)).injective)
  · unfold CfgData
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro z hz
      obtain ⟨w, hw, rfl⟩ := mem_Z0_iff.1 hz
      exact w183finL34_inP_imp (repN_wN w)
        (List.all_eq_true.1 hzP (wN w) (List.mem_map.2 ⟨w, hw, rfl⟩))
    · intro a ha
      obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.1 ha
      obtain ⟨w, hw, rfl⟩ := mem_Z0_iff.1 hz
      have hxmem : conjN (wN gAW) (wN gAiW) (wN w) ∈ A'N :=
        List.mem_map.2 ⟨wN w, List.mem_map.2 ⟨w, hw, rfl⟩, rfl⟩
      have hrep : RepN (conjN (wN gAW) (wN gAiW) (wN w))
          (wordPerm gAW * wordPerm w * (wordPerm gAW)⁻¹) := by
        exact congrArg (fun z => wordPerm gAW * wordPerm w * z) hgi ▸
          w183finL34_repConjN (repN_wN gAW) (repN_wN w) (repN_wN gAiW)
      have hgoal := w183finL34_inP_imp hrep (List.all_eq_true.1 hA'P _ hxmem)
      change wordPerm gAW * wordPerm w * (wordPerm gAW)⁻¹ ∈
        C₁.map (MulAut.conj (wordPerm hW)).toMonoidHom
      exact hgoal
    · intro a ha
      obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.1 ha
      obtain ⟨w, hw, rfl⟩ := mem_Z0_iff.1 hz
      have hxmem : conjN (wN gSW) (wN gSW) (wN w) ∈ XN :=
        List.mem_map.2 ⟨wN w, List.mem_map.2 ⟨w, hw, rfl⟩, rfl⟩
      have hrep : RepN (conjN (wN gSW) (wN gSW) (wN w))
          (wordPerm gSW * wordPerm w * (wordPerm gSW)⁻¹) := by
        exact congrArg (fun z => wordPerm gSW * wordPerm w * z) hgsinv ▸
          w183finL34_repConjN (repN_wN gSW) (repN_wN w) (repN_wN gSW)
      have hgoal := w183finL34_inP_imp hrep (List.all_eq_true.1 hXP _ hxmem)
      change wordPerm gSW * wordPerm w * (wordPerm gSW)⁻¹ ∈
        C₁.map (MulAut.conj (wordPerm hW)).toMonoidHom
      exact hgoal
    · exact w183finL34_inP_imp (repN_wN yW) hyP
    · intro heq
      obtain ⟨aN, haN, hne⟩ := w183finL34_all_false hyne
      obtain ⟨w, hw, rfl⟩ := List.mem_map.1 haN
      have hzw : (MulAut.conj (wordPerm yW)).toMonoidHom (wordPerm w) ∈ Z0 := by
        rw [← heq]
        exact Subgroup.mem_map.2 ⟨wordPerm w, ⟨w, hw, rfl⟩, rfl⟩
      obtain ⟨w', hw', hw'eq⟩ := hzw
      have hmem : memN (conjN (wN yW) (wN yW) (wN w)) z0N = true := by
        rw [memN, List.any_eq_true]
        refine ⟨wN w', List.mem_map.2 ⟨w', hw', rfl⟩, ?_⟩
        have hrep : RepN (conjN (wN yW) (wN yW) (wN w))
            (wordPerm yW * wordPerm w * (wordPerm yW)⁻¹) := by
          exact congrArg (fun z => wordPerm yW * wordPerm w * z) hyinv ▸
            w183finL34_repConjN (repN_wN yW) (repN_wN w) (repN_wN yW)
        have heq' : wordPerm yW * wordPerm w * (wordPerm yW)⁻¹ = wordPerm w' := by
          rw [hw'eq]
          simp [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        exact (RepN.eq_iff hrep (repN_wN w')).2 heq'
      rw [hne] at hmem
      exact Bool.false_ne_true hmem
    · intro s hs
      obtain ⟨w, hw, rfl⟩ := mem_Z0_iff.1 hs
      have h := List.all_eq_true.1 hcomm (wN w) (List.mem_map.2 ⟨w, hw, rfl⟩)
      rw [List.any_eq_true] at h
      obtain ⟨z, hz, hzeq⟩ := h
      obtain ⟨zN, hzN, rfl⟩ := List.mem_map.1 hz
      obtain ⟨w', hw', rfl⟩ := List.mem_map.1 hzN
      refine ⟨wordPerm gSW * wordPerm w' * (wordPerm gSW)⁻¹, ?_, ?_⟩
      · exact Subgroup.mem_map.2 ⟨wordPerm w', ⟨w', hw', rfl⟩, by
          simp [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]⟩
      · have hrepL : RepN (conjN (wN yW) (wN yW) (wN w))
            (wordPerm yW * wordPerm w * (wordPerm yW)⁻¹) := by
          exact congrArg (fun z => wordPerm yW * wordPerm w * z) hyinv ▸
            w183finL34_repConjN (repN_wN yW) (repN_wN w) (repN_wN yW)
        have hrepR : RepN (compN (wN w) (conjN (wN gSW) (wN gSW) (wN w')))
            (wordPerm w * (wordPerm gSW * wordPerm w' * (wordPerm gSW)⁻¹)) := by
          have h1 : RepN (conjN (wN gSW) (wN gSW) (wN w'))
              (wordPerm gSW * wordPerm w' * (wordPerm gSW)⁻¹) := by
            exact congrArg (fun z => wordPerm gSW * wordPerm w' * z) hgsinv ▸
              w183finL34_repConjN (repN_wN gSW) (repN_wN w') (repN_wN gSW)
          exact (repN_wN w).comp h1
        exact (RepN.eq_iff hrepL hrepR).1 hzeq
    · intro hle
      obtain ⟨aN, haN, hne⟩ := w183finL34_all_false hnorm
      obtain ⟨w, hw, rfl⟩ := List.mem_map.1 haN
      obtain ⟨xN, hxN, hneX⟩ := w183finL34_all_false hne
      obtain ⟨zN, hzN, rfl⟩ := List.mem_map.1 hxN
      obtain ⟨w', hw', rfl⟩ := List.mem_map.1 hzN
      have hw2 : wordPerm w * wordPerm w = 1 := w183finL34_z0W_sq hw
      have hwinv : (wordPerm w)⁻¹ = wordPerm w := inv_eq_of_mul_eq_one_right hw2
      have htA' : (MulAut.conj (wordPerm gAW)).toMonoidHom (wordPerm w') ∈
          Z0.map (MulAut.conj (wordPerm gAW)).toMonoidHom :=
        Subgroup.mem_map.2 ⟨wordPerm w', ⟨w', hw', rfl⟩, rfl⟩
      have hmem := Subgroup.le_normalizer_iff.1 hle (wordPerm w) ⟨w, hw, rfl⟩
        ((MulAut.conj (wordPerm gAW)).toMonoidHom (wordPerm w')) htA'
      obtain ⟨z₂, hz₂, hz₂eq⟩ := Subgroup.mem_map.1 hmem
      obtain ⟨w'', hw'', hw''eq⟩ := mem_Z0_iff.1 hz₂
      have hz₂eq' : wordPerm gAW * z₂ * (wordPerm gAW)⁻¹ =
          wordPerm w * (wordPerm gAW * wordPerm w' * (wordPerm gAW)⁻¹) * (wordPerm w)⁻¹ := by
        simpa [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using hz₂eq
      have heq2 : wordPerm gAW * wordPerm w'' * (wordPerm gAW)⁻¹ =
          wordPerm w * (wordPerm gAW * wordPerm w' * (wordPerm gAW)⁻¹) * wordPerm w := by
        simp only [hw''eq, hz₂eq', hwinv]
      have hmemN : memN (conjN (wN w) (wN w) (conjN (wN gAW) (wN gAiW) (wN w'))) A'N =
          true := by
        rw [memN, List.any_eq_true]
        refine ⟨conjN (wN gAW) (wN gAiW) (wN w''), ?_, ?_⟩
        · exact List.mem_map.2 ⟨wN w'', List.mem_map.2 ⟨w'', hw'', rfl⟩, rfl⟩
        · have hx : RepN (conjN (wN gAW) (wN gAiW) (wN w'))
              (wordPerm gAW * wordPerm w' * (wordPerm gAW)⁻¹) := by
            exact congrArg (fun z => wordPerm gAW * wordPerm w' * z) hgi ▸
              w183finL34_repConjN (repN_wN gAW) (repN_wN w') (repN_wN gAiW)
          have hL : RepN (conjN (wN w) (wN w) (conjN (wN gAW) (wN gAiW) (wN w')))
              (wordPerm w * (wordPerm gAW * wordPerm w' * (wordPerm gAW)⁻¹) * wordPerm w) :=
            w183finL34_repConjN (repN_wN w) hx (repN_wN w)
          have hR : RepN (conjN (wN gAW) (wN gAiW) (wN w''))
              (wordPerm w * (wordPerm gAW * wordPerm w' * (wordPerm gAW)⁻¹) * wordPerm w) := by
            have h := w183finL34_repConjN (repN_wN gAW) (repN_wN w'') (repN_wN gAiW)
            have h' : RepN (conjN (wN gAW) (wN gAiW) (wN w''))
                (wordPerm gAW * wordPerm w'' * (wordPerm gAW)⁻¹) :=
              congrArg (fun z => wordPerm gAW * wordPerm w'' * z) hgi ▸ h
            exact heq2 ▸ h'
          exact (RepN.eq_iff hL hR).2 rfl
      rw [hneX] at hmemN
      exact Bool.false_ne_true hmemN
    · right
      intro a ha x hx
      obtain ⟨wa, hwa, rfl⟩ := Subgroup.mem_map.1 ha
      obtain ⟨w₂, hw₂, rfl⟩ := mem_Z0_iff.1 hwa
      obtain ⟨wx, hwx, rfl⟩ := Subgroup.mem_map.1 hx
      obtain ⟨w₃, hw₃, rfl⟩ := mem_Z0_iff.1 hwx
      have haN : conjN (wN gAW) (wN gAiW) (wN w₂) ∈ A'N :=
        List.mem_map.2 ⟨wN w₂, List.mem_map.2 ⟨w₂, hw₂, rfl⟩, rfl⟩
      have hxN : conjN (wN gSW) (wN gSW) (wN w₃) ∈ XN :=
        List.mem_map.2 ⟨wN w₃, List.mem_map.2 ⟨w₃, hw₃, rfl⟩, rfl⟩
      have hcomm' := List.all_eq_true.1 (List.all_eq_true.1 hcommAX _ haN) _ hxN
      have hrepA : RepN (conjN (wN gAW) (wN gAiW) (wN w₂))
          (wordPerm gAW * wordPerm w₂ * (wordPerm gAW)⁻¹) := by
        exact congrArg (fun z => wordPerm gAW * wordPerm w₂ * z) hgi ▸
          w183finL34_repConjN (repN_wN gAW) (repN_wN w₂) (repN_wN gAiW)
      have hrepX : RepN (conjN (wN gSW) (wN gSW) (wN w₃))
          (wordPerm gSW * wordPerm w₃ * (wordPerm gSW)⁻¹) := by
        exact congrArg (fun z => wordPerm gSW * wordPerm w₃ * z) hgsinv ▸
          w183finL34_repConjN (repN_wN gSW) (repN_wN w₃) (repN_wN gSW)
      exact w183finL34_commN_imp hrepA hrepX hcomm'

end W183L34

open CFSG.PSL3Four CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
open W183L34

theorem finG1Syl_holds :
    FinG1Syl := by
  intro G₀ _ hL A₀ hcard hel hTI
  obtain ⟨ψ⟩ :=
    CFSG.ComponentClassification.CatFactsSmall.nonempty_equiv_psl34_of_lieModel hL
  let ι : G₀ →* Equiv.Perm (Fin 42) := S.subtype.comp ψ.toMonoidHom
  have hι : Function.Injective ι := by
    intro a b h
    exact ψ.injective (Subtype.coe_injective h)
  have hιS : ∀ a : G₀, ι a ∈ S := fun a => (ψ a).2
  have hAS : A₀.map ι ≤ S := by
    intro x hx
    obtain ⟨a, _, rfl⟩ := Subgroup.mem_map.1 hx
    exact hιS a
  have hcardA : Nat.card (A₀.map ι) = 4 := by
    rw [Subgroup.card_map_of_injective hι, hcard]
  have helA : IsElemAbelian 2 (A₀.map ι) := W183L34.isElemAbelian_map ι hel
  have hrange : ι.range = S := by
    ext g
    constructor
    · rintro ⟨a, rfl⟩
      exact hιS a
    · intro hg
      refine ⟨ψ.symm ⟨g, hg⟩, ?_⟩
      exact congrArg Subtype.val (ψ.apply_symm_apply ⟨g, hg⟩)
  have hTI_A : ∀ t ∈ A₀.map ι, t ≠ 1 → ∀ g ∈ S, g * t = t * g →
      g ∈ Subgroup.normalizer ((A₀.map ι : Subgroup (Equiv.Perm (Fin 42))) : Set _) := by
    intro t ht ht1 g hg hgt
    have hg' : g ∈ ι.range := by rwa [hrange]
    exact W183L34.tiS_map ι hι hTI t ht ht1 g hg' hgt
  obtain ⟨k, hkS, hk⟩ := W183L34.exists_conj_Z0 hAS hcardA helA hTI_A
  let f : Equiv.Perm (Fin 42) →* Equiv.Perm (Fin 42) := (MulAut.conj k⁻¹).toMonoidHom
  let φ : G₀ →* Equiv.Perm (Fin 42) := f.comp ι
  have hφinj : Function.Injective φ := (MulAut.conj k⁻¹).injective.comp hι
  have hf_apply : ∀ x : Equiv.Perm (Fin 42), f x = k⁻¹ * x * k := by
    intro x
    simp [f, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  have hφA : A₀.map φ = Z0 := by
    change A₀.map (f.comp ι) = Z0
    rw [← Subgroup.map_map A₀ f ι]
    exact hk
  have hφrange : φ.range = S := by
    ext g
    constructor
    · rintro ⟨a, rfl⟩
      change f (ι a) ∈ S
      rw [hf_apply]
      exact S.mul_mem (S.mul_mem (S.inv_mem hkS) (hιS a)) hkS
    · intro hg
      let t : S := ⟨k * g * k⁻¹, S.mul_mem (S.mul_mem hkS hg) (S.inv_mem hkS)⟩
      refine ⟨ψ.symm t, ?_⟩
      have h1 : ι (ψ.symm t) = (t : Equiv.Perm (Fin 42)) :=
        congrArg Subtype.val (ψ.apply_symm_apply t)
      change f (ι (ψ.symm t)) = g
      rw [h1, hf_apply]
      change k⁻¹ * (k * g * k⁻¹) * k = g
      group
  obtain ⟨P, hPS, hP2, gA, hgAS, gS, hgSS, y, hyS, hcfg⟩ := witness_Z0
  have hcfg' : CfgData (A₀.map φ) P gA gS y := by rwa [hφA]
  have hPφ : P ≤ φ.range := by rwa [hφrange]
  have hgAφ : gA ∈ φ.range := by rwa [hφrange]
  have hgSφ : gS ∈ φ.range := by rwa [hφrange]
  have hyφ : y ∈ φ.range := by rwa [hφrange]
  obtain ⟨P₀, gA₀, gS₀, y₀, hP₀, hcfg₀⟩ :=
    W183L34.cfgData_of_map φ hφinj A₀ P gA gS y hPφ hgAφ hgSφ hyφ hcfg'
  refine ⟨P₀, ?_, hcfg₀.1, W183L34.corConfigIn_of_cfgData hcfg₀⟩
  have hP2' : IsPGroup 2 (P₀.map φ) := by rw [hP₀]; exact hP2
  exact hP2'.of_equiv (Subgroup.equivMapOfInjective P₀ φ hφinj).symm

theorem finG1_holds : FinG1 :=
  finG1_of_finG1Syl finG1Syl_holds

end CFSG.LocalAnalysis.WeakClosure81

end
