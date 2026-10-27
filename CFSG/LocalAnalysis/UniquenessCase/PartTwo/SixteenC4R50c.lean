module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC4FrameM
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC4E9Point
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC4E9Form
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSpLift

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.ClassicalGroups.Unitary CFSG.LocalAnalysis.RankThreeUC Matrix
open CFSG.LieType.Universal.Unitary (SUid)

variable {G : Type} [Group G] [Finite G]

namespace UFrame

variable {V₀ V : Subgroup G} {hV : IsElemAbelian 2 V} {L : Subgroup G}
  (F : UFrame V₀ V hV L)

@[expose] def subOfAdd (A : AddSubgroup (Fin 4 → F.K)) : Subgroup (Vtil V₀ V hV) :=
  (AddSubgroup.toSubgroup A).comap F.β.toMonoidHom

theorem mem_subOfAdd (A : AddSubgroup (Fin 4 → F.K)) (w : Vtil V₀ V hV) :
    w ∈ F.subOfAdd A ↔ F.vec w ∈ A := Iff.rfl

theorem addSub_subOfAdd (A : AddSubgroup (Fin 4 → F.K)) : F.addSub (F.subOfAdd A) = A := by
  ext x
  simp [mem_addSub, mem_subOfAdd]

theorem card_addSub (S : Subgroup (Vtil V₀ V hV)) : Nat.card (F.addSub S) = Nat.card S := by
  refine Nat.card_congr ?_
  exact
    { toFun := fun x => ⟨F.ofVec x, (F.vec_mem_addSub S (F.ofVec x)).1 (by simpa using x.2)⟩
      invFun := fun w => ⟨F.vec w, (F.vec_mem_addSub S w).2 w.2⟩
      left_inv := fun x => Subtype.ext (F.vec_ofVec x)
      right_inv := fun w => Subtype.ext (F.ofVec_vec w) }

end UFrame

theorem s16_C4R50c_mkTil_injective {V : Subgroup G} (hV : IsElemAbelian 2 V) :
    Function.Injective (mkTil ⊥ V hV) := by
  rw [← MonoidHom.ker_eq_bot_iff]
  ext x
  rw [MonoidHom.mem_ker, Subgroup.mem_bot]
  constructor
  · intro h
    have hx : x ∈ modNull ⊥ V hV := (QuotientGroup.eq_one_iff (N := modNull ⊥ V hV) x).1 h
    rw [mem_modNull] at hx
    exact IntMod.val_injective (by simpa using hx)
  · rintro rfl
    exact map_one _

theorem s16_C4R50c_sing_of_mem_addSub {V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (F : UFrame ⊥ V hV L) {U : Subgroup G}
    (hts : ∀ x : IntMod V hV, x.val ∈ U → F.Sing (mkTil ⊥ V hV x))
    {y : Fin 4 → F.K} (hy : y ∈ F.addSub (imgTil ⊥ V hV U)) :
    herm F.σ y y = 0 := by
  obtain ⟨x, hxU, hxeq⟩ :=
    (mem_imgTil ⊥ V hV U (F.ofVec y)).1 ((F.mem_addSub (imgTil ⊥ V hV U) y).1 hy)
  have hs := hts x hxU
  simpa [UFrame.Sing, hxeq] using hs

theorem s16c4_normalizer_le_of_bar (D : Data G) (h61 : UC6.R6_1 D) (h3 : 3 ∈ D.sig)
    {V : Subgroup G} {hV : IsElemAbelian 2 V} (hP : PairFacts D.M ⊥ V) {Q : Subgroup G}
    (hQV : Q ≤ V) (hQ1 : Q ≠ ⊥) {E : Subgroup (MulAut (Vtil ⊥ V hV))}
    (hE : E ≤ Mbar D.M ⊥ V hV) (hEp : IsPGroup 3 E) (hEc : ¬ IsCyclic E)
    (hEQ : ∀ φ ∈ E, ∀ w ∈ imgTil ⊥ V hV Q, φ w ∈ imgTil ⊥ V hV Q) :
    normalizer (Q : Set G) ≤ D.M := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let C : Subgroup G := preBarSub D.M ⊥ V hV E
  have hCM : C ≤ D.M := fun g hg => ((mem_preBarSub D.M ⊥ V hV E).1 hg).1
  have hCs : C ≤ stabTil ⊥ V := fun g hg => ((mem_preBarSub D.M ⊥ V hV E).1 hg).2.choose
  let f : ↥C →* MulAut (Vtil ⊥ V hV) := (actTil ⊥ V hV).comp (Subgroup.inclusion hCs)
  have hfE : ∀ c : ↥C, f c ∈ E := by
    intro c
    obtain ⟨-, hcs, hE'⟩ := (mem_preBarSub D.M ⊥ V hV E).1 c.2
    change actTil ⊥ V hV (Subgroup.inclusion hCs c) ∈ E
    have hsub : (Subgroup.inclusion hCs c : ↥(stabTil ⊥ V)) = ⟨(c : G), hcs⟩ := by
      apply Subtype.ext
      exact Subgroup.coe_inclusion hCs c
    rw [hsub]
    exact hE'
  let gg : ↥C →* ↥E := f.codRestrict E hfE
  have hgg : Function.Surjective gg := by
    rintro ⟨φ, hφ⟩
    obtain ⟨m, hmM, hmφ⟩ := (mem_barSub ⊥ V hV D.M φ).1 (hE hφ)
    have hmC : (m : G) ∈ C := by
      refine (mem_preBarSub D.M ⊥ V hV E).2 ⟨hmM, ⟨m.2, ?_⟩⟩
      change actTil ⊥ V hV m ∈ E
      rw [hmφ]
      exact hφ
    refine ⟨⟨(m : G), hmC⟩, Subtype.ext ?_⟩
    have hsub : (Subgroup.inclusion hCs ⟨(m : G), hmC⟩ : ↥(stabTil ⊥ V)) = m := by
      apply Subtype.ext
      exact Subgroup.coe_inclusion hCs _
    change actTil ⊥ V hV (Subgroup.inclusion hCs ⟨(m : G), hmC⟩) = φ
    rw [hsub, hmφ]
  have htop : (⊤ : Subgroup ↥E) ≃* ↥E := Subgroup.topEquiv
  obtain ⟨X, -, hXp, hXc⟩ :=
    SpLift.exists_noncyclic_pSubgroup_le gg hgg (p := 3) (K := ⊤) (E := ⊤)
      (by rw [Subgroup.index_top]; norm_num)
      (hEp.of_equiv htop.symm)
      (fun hc => hEc ((MulEquiv.isCyclic htop).mp hc))
  let X' : Subgroup G := X.map C.subtype
  have hX'M : X' ≤ D.M := by
    rintro _ ⟨x, -, rfl⟩
    simpa using hCM x.2
  have hX'p : IsPGroup 3 X' := hXp.map C.subtype
  have hX'c : ¬ IsCyclic X' := SpLift.not_isCyclic_map C.subtype (Subgroup.subtype_injective C) hXc
  have hstep : ∀ c ∈ X', ∀ q ∈ Q, c * q * c⁻¹ ∈ Q := by
    intro c hc q hq
    obtain ⟨x, -, rfl⟩ := hc
    change (x : G) * q * (x : G)⁻¹ ∈ Q
    obtain ⟨-, hxs, hxE⟩ := (mem_preBarSub D.M ⊥ V hV E).1 x.2
    have hqV : q ∈ V := hQV hq
    have hcqV : (x : G) * q * (x : G)⁻¹ ∈ V :=
      ((Subgroup.mem_normalizer_iff.1 hxs.1) q).1 hqV
    let xq : IntMod V hV := IntMod.mk hV ⟨q, hqV⟩
    let y : IntMod V hV := IntMod.mk hV ⟨(x : G) * q * (x : G)⁻¹, hcqV⟩
    have hxq_img : mkTil ⊥ V hV xq ∈ imgTil ⊥ V hV Q :=
      (mem_imgTil ⊥ V hV Q _).2 ⟨xq, hq, rfl⟩
    have hkey : actTil ⊥ V hV ⟨(x : G), hxs⟩ (mkTil ⊥ V hV xq) = mkTil ⊥ V hV y := by
      rw [actTil_mk]
      congr 1
    have hmem : actTil ⊥ V hV ⟨(x : G), hxs⟩ (mkTil ⊥ V hV xq) ∈ imgTil ⊥ V hV Q :=
      hEQ _ hxE _ hxq_img
    rw [hkey] at hmem
    obtain ⟨x', hx'Q, hx'eq⟩ := (mem_imgTil ⊥ V hV Q _).1 hmem
    have hval : x'.val = y.val :=
      congrArg IntMod.val (s16_C4R50c_mkTil_injective hV hx'eq)
    have hmemQ : y.val ∈ Q := hval ▸ hx'Q
    have hyval : y.val = (x : G) * q * (x : G)⁻¹ := rfl
    rwa [hyval] at hmemQ
  have hX'Q : X' ≤ normalizer (Q : Set G) := by
    intro c hc
    rw [Subgroup.mem_normalizer_iff]
    intro q
    constructor
    · exact hstep c hc q
    · intro hq
      have h := hstep c⁻¹ (X'.inv_mem hc) (c * q * c⁻¹) hq
      have h' : c⁻¹ * (c * q * c⁻¹) * (c⁻¹)⁻¹ = q := by group
      rwa [h'] at h
  have hQ2 : IsPGroup 2 Q := (hV.isPGroup).to_le hQV
  exact normalizer_le_of_noncyclic D h61 h3 hX'M hX'p hX'c hQ1 hQ2 hX'Q

theorem s16_C4R50c_centralizer_le_of_stab (D : Data G) (h61 : UC6.R6_1 D) (h3 : 3 ∈ D.sig)
    {V : Subgroup G} {hV : IsElemAbelian 2 V} (hP : PairFacts D.M ⊥ V)
    {U Q : Subgroup G} (hQU : Q ≤ U) (hQV : Q ≤ V) (hQ1 : Q ≠ ⊥)
    {E' : Subgroup (MulAut (Vtil ⊥ V hV))} (hE'M : E' ≤ Mbar D.M ⊥ V hV)
    (hE'p : IsPGroup 3 E') (hE'c : ¬ IsCyclic E')
    (hE'Q : ∀ φ ∈ E', ∀ w ∈ imgTil ⊥ V hV Q, φ w ∈ imgTil ⊥ V hV Q) :
    centralizer (U : Set G) ≤ D.M :=
  (Subgroup.centralizer_le hQU).trans <|
    (Subgroup.centralizer_le_normalizer (Q : Set G)).trans
      (s16c4_normalizer_le_of_bar D h61 h3 hP hQV hQ1 hE'M hE'p hE'c hE'Q)

theorem s16c4_centralizer_le_of_ts_four (D : Data G) (h61 : UC6.R6_1 D) {V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (hS : Sect16 D ⊥ V L hV) (h4 : Case167_4 D ⊥ V hV L)
    (F : UFrame ⊥ V hV L) {U : Subgroup G} (hUV : U ≤ V)
    (hts : ∀ x : IntMod V hV, x.val ∈ U → F.Sing (mkTil ⊥ V hV x))
    (hrk : rk ↥(imgTil ⊥ V hV U) = 4) : centralizer (U : Set G) ≤ D.M := by
  classical
  have hP : PairFacts D.M ⊥ V := hS.setting.hyp16.hyp125.pairFacts
  have h3 : 3 ∈ D.sig := by rw [h4.2.2]; exact Set.mem_singleton 3
  let S : AddSubgroup (Fin 4 → F.K) := F.addSub (imgTil ⊥ V hV U)
  have hcardS : Nat.card S = 16 := by
    have hVtil : IsPGroup 2 (Vtil ⊥ V hV) := by
      intro v
      obtain ⟨x, rfl⟩ := mkTil_surjective ⊥ V hV v
      exact ⟨1, by rw [pow_one, ← map_pow, IntMod.sq_eq_one, map_one]⟩
    have hImg2 : IsPGroup 2 ↥(imgTil ⊥ V hV U) := hVtil.to_subgroup (imgTil ⊥ V hV U)
    have hcardImg : Nat.card ↥(imgTil ⊥ V hV U) = 16 := by
      rw [card_eq_two_pow_of_isPGroup hImg2, hrk]
      norm_num
    calc Nat.card S = Nat.card ↥(imgTil ⊥ V hV U) := F.card_addSub _
      _ = 16 := hcardImg
  have htsS : ∀ y ∈ S, herm F.σ y y = 0 := fun y hy => s16_C4R50c_sing_of_mem_addSub F hts hy
  by_cases hcaseA : ∃ x ∈ S, x ≠ 0 ∧ ∀ c : F.K, c • x ∈ S
  · obtain ⟨x, hxS, hx0, hxline⟩ := hcaseA
    have hxsing : herm F.σ x x = 0 := htsS x hxS
    let A : AddSubgroup (Fin 4 → F.K) := (Submodule.span F.K {x}).toAddSubgroup
    have hA : A = (Submodule.span F.K {x}).toAddSubgroup := rfl
    have hA_le_S : A ≤ S := by
      intro y hy
      have hy' : y ∈ Submodule.span F.K {x} := by
        rw [hA] at hy
        rwa [Submodule.mem_toAddSubgroup] at hy
      obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 hy'
      rw [← ha]
      exact hxline a
    let S_P : Subgroup (Vtil ⊥ V hV) := F.subOfAdd A
    have hSP : S_P = F.subOfAdd A := rfl
    have hadd : F.addSub S_P = A := F.addSub_subOfAdd A
    obtain ⟨E, hE_SU, hEp, hEc, hEstab⟩ := F.exists_E9_stab_point hx0 hxsing
    have hstab : ∀ g ∈ E, ∀ y ∈ F.addSub S_P,
        (((g : GL (Fin 4) F.K) : Matrix (Fin 4) (Fin 4) F.K) *ᵥ y ∈ F.addSub S_P) := by
      intro g hg y hy
      have hy' : y ∈ Submodule.span F.K {x} := by
        rw [hadd] at hy
        rw [hA] at hy
        rwa [Submodule.mem_toAddSubgroup] at hy
      have h := hEstab g hg y hy'
      simpa [hadd, hA, Submodule.mem_toAddSubgroup] using h
    obtain ⟨E', hE'lbar, hE'stab, hE'equiv⟩ :=
      F.exists_subgroup_normalizer E hE_SU S_P hstab
    have hE'M : E' ≤ Mbar D.M ⊥ V hV := hE'lbar.trans (lBar_le_Mbar hS)
    obtain ⟨e⟩ := hE'equiv
    have hE'p : IsPGroup 3 E' := hEp.of_equiv e
    have hE'c : ¬ IsCyclic E' := fun hc => hEc ((MulEquiv.isCyclic e).mpr hc)
    have hQU : preTil ⊥ V hV S_P ≤ U := by
      intro q hq
      obtain ⟨xq, hxqval, hxqSP⟩ := (mem_preTil ⊥ V hV S_P).1 hq
      rw [hSP] at hxqSP
      have hxA : F.vec (mkTil ⊥ V hV xq) ∈ A :=
        (F.mem_subOfAdd A (mkTil ⊥ V hV xq)).1 hxqSP
      have hxS : F.vec (mkTil ⊥ V hV xq) ∈ S := hA_le_S hxA
      have hxU : mkTil ⊥ V hV xq ∈ imgTil ⊥ V hV U :=
        (F.vec_mem_addSub (imgTil ⊥ V hV U) (mkTil ⊥ V hV xq)).1 hxS
      obtain ⟨x', hx'U, hx'eq⟩ := (mem_imgTil ⊥ V hV U _).1 hxU
      have hxx' : x' = xq := s16_C4R50c_mkTil_injective hV hx'eq
      rw [← hxqval, ← hxx']
      exact hx'U
    have hQ1 : preTil ⊥ V hV S_P ≠ ⊥ := by
      intro hbot
      have hSPx : F.ofVec x ∈ S_P := by
        rw [hSP, F.mem_subOfAdd, F.vec_ofVec, hA]
        exact (Submodule.mem_toAddSubgroup (Submodule.span F.K {x})).2
          (Submodule.subset_span (Set.mem_singleton x))
      have hne1 : F.ofVec x ≠ 1 := by
        intro h
        apply hx0
        have := congrArg F.vec h
        simpa using this
      obtain ⟨z, hz⟩ := mkTil_surjective ⊥ V hV (F.ofVec x)
      have hzQ : z.val ∈ preTil ⊥ V hV S_P :=
        (mem_preTil ⊥ V hV S_P).2 ⟨z, rfl, by rw [hz]; exact hSPx⟩
      have hzv : z.val ≠ 1 := by
        intro h
        apply hne1
        have hz1 : z = 1 := IntMod.val_injective (by rw [h]; rfl)
        rw [← hz, hz1, map_one]
      have hmem : z.val ∈ (⊥ : Subgroup G) := by rw [hbot] at hzQ; exact hzQ
      exact hzv (Subgroup.mem_bot.1 hmem)
    have hE'Q : ∀ φ ∈ E', ∀ w ∈ imgTil ⊥ V hV (preTil ⊥ V hV S_P),
        φ w ∈ imgTil ⊥ V hV (preTil ⊥ V hV S_P) := by
      intro φ hφ w hw
      rw [imgTil_preTil] at hw
      have h := hE'stab φ hφ w hw
      rwa [imgTil_preTil]
    exact s16_C4R50c_centralizer_le_of_stab D h61 h3 hP hQU (preTil_le ⊥ V hV S_P) hQ1
      hE'M hE'p hE'c hE'Q
  · have hcore : ∀ x ∈ S, x ≠ 0 → ∃ c : F.K, c • x ∉ S := by
      intro x hxS hx0
      by_contra h
      exact hcaseA ⟨x, hxS, hx0, fun c => not_not.mp (not_exists.mp h c)⟩
    obtain ⟨E, hE_SU, hEp, hEc, hEstab⟩ := F.exists_E9_stab_form S hcardS htsS hcore
    obtain ⟨E', hE'lbar, hE'stab, hE'equiv⟩ :=
      F.exists_subgroup_normalizer E hE_SU (imgTil ⊥ V hV U) hEstab
    have hE'M : E' ≤ Mbar D.M ⊥ V hV := hE'lbar.trans (lBar_le_Mbar hS)
    obtain ⟨e⟩ := hE'equiv
    have hE'p : IsPGroup 3 E' := hEp.of_equiv e
    have hE'c : ¬ IsCyclic E' := fun hc => hEc ((MulEquiv.isCyclic e).mpr hc)
    have hU1 : U ≠ ⊥ := by
      intro hUbot
      have hImgBot : imgTil ⊥ V hV U = ⊥ := by
        rw [hUbot, imgTil]
        rw [show intSub V hV (⊥ : Subgroup G) = ⊥ from Subgroup.bot_subgroupOf V]
        exact Subgroup.map_bot _
      have hrkbot : rk ↥(⊥ : Subgroup (Vtil ⊥ V hV)) = 4 := by
        rw [← hImgBot]
        exact hrk
      rw [rk_bot] at hrkbot
      exact (by norm_num : (0 : ℕ) ≠ 4) hrkbot
    exact s16_C4R50c_centralizer_le_of_stab (U := U) (Q := U) D h61 h3 hP le_rfl hUV hU1
      hE'M hE'p hE'c hE'stab

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
