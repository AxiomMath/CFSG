module

public import CFSG.GH74.GLS.IVK.Lifted.SL2KGroup
public import CFSG.LocalAnalysis.QuasithinUnique.CatalogBridgeLinear
public import CFSG.SignalizerFunctorTheorem.McBride.Models.PSL2Even.Aut
public import CFSG.RankThree.PartTwo.Sec4.ProjSLEquiv

public section

namespace CFSG.RankThree.PartTwo.Sec15.SimsBaumann

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.GH74.GLS
open CFSG.GH74.GLS.IVK.Lifted (not_isSolvable_of_simple_nonabelian injective_of_surjective_simple
  isSolvable_of_card_two_three psl2_subgroup_dichotomy)
open scoped MatrixGroups

variable {X : Type} [Group X] [Finite X]

private theorem sbkgrp_ker_le {K S : Type} [Group K] [Group S] [IsSimpleGroup S]
    (hab : ∃ a b : S, a * b ≠ b * a) (φ : K →* S) (hφ : Function.Surjective φ)
    (N : Subgroup K) [N.Normal] [Group.IsSolvable N] : N ≤ φ.ker := by
  have hn : (N.map φ).Normal := Subgroup.Normal.map inferInstance φ hφ
  rcases hn.eq_bot_or_eq_top with h | h
  · exact (Subgroup.map_eq_bot_iff _).mp h
  · exfalso
    have hsurj : Function.Surjective (φ.comp N.subtype) := by
      rw [← MonoidHom.range_eq_top, MonoidHom.range_comp, Subgroup.range_subtype, h]
    exact not_isSolvable_of_simple_nonabelian hab (Group.isSolvable_of_surjective hsurj)

private theorem sbkgrp_isSolvable_of_ker_le {G H S : Type} [Group G] [Group H] [Group S]
    (g : G →* H) (φ : G →* S) (hφ : Function.Surjective φ) (h : g.ker ≤ φ.ker)
    [Group.IsSolvable H] : Group.IsSolvable S := by
  have h1 : Group.IsSolvable (G ⧸ g.ker) :=
    Group.isSolvable_of_isSolvable_injective (QuotientGroup.kerLift_injective g)
  refine Group.isSolvable_of_surjective (f := QuotientGroup.lift g.ker φ h) fun s => ?_
  obtain ⟨x, rfl⟩ := hφ s
  exact ⟨x, rfl⟩

private theorem sbkgrp_isKGroup_of_solvable_ker {G Y : Type} [Group G] [Group Y] (f : G →* Y)
    [Group.IsSolvable f.ker] (hY : CFSG.Open.IsKGroup Y) : CFSG.Open.IsKGroup G := by
  intro K L _ _ _ hnonab
  let φ : K →* K ⧸ L.subgroupOf K := QuotientGroup.mk' (L.subgroupOf K)
  have hφ : Function.Surjective φ := QuotientGroup.mk'_surjective _
  let g : K →* ↥(K.map f) := f.subgroupMap K
  have hg : Function.Surjective g := f.subgroupMap_surjective K
  have hsolv : Group.IsSolvable g.ker := by
    have hmem : ∀ x : g.ker, (K.subtype.comp g.ker.subtype) x ∈ f.ker := fun x =>
      MonoidHom.mem_ker.mpr (congrArg Subtype.val (MonoidHom.mem_ker.mp x.2))
    refine Group.isSolvable_of_isSolvable_injective
      (f := (K.subtype.comp g.ker.subtype).codRestrict f.ker hmem) fun a b hab => ?_
    exact Subtype.ext (Subtype.ext (congrArg (fun z : f.ker => (z : G)) hab))
  have hle : g.ker ≤ φ.ker := sbkgrp_ker_le hnonab φ hφ g.ker
  let ψ : ↥(K.map f) →* K ⧸ L.subgroupOf K := (g.liftOfSurjective hg) ⟨φ, hle⟩
  have hψ : Function.Surjective ψ := fun s => by
    obtain ⟨k, rfl⟩ := hφ s
    exact ⟨g k, MonoidHom.liftOfRightInverse_comp_apply g _ _ ⟨φ, hle⟩ k⟩
  exact hY.isCatalogGroup_of_surjective (K.map f) hnonab ψ hψ

private theorem sbkgrp_isKGroup_of_normal {G : Type} [Group G] (N : Subgroup G) [N.Normal]
    [Group.IsSolvable (G ⧸ N)] (hN : CFSG.Open.IsKGroup N) : CFSG.Open.IsKGroup G := by
  intro K L _ _ _ hnonab
  let φ : K →* K ⧸ L.subgroupOf K := QuotientGroup.mk' (L.subgroupOf K)
  have hφ : Function.Surjective φ := QuotientGroup.mk'_surjective _
  let T : Subgroup K := N.subgroupOf K
  have hTn : (T.map φ).Normal := Subgroup.Normal.map inferInstance φ hφ
  rcases hTn.eq_bot_or_eq_top with h | h
  · exfalso
    let g : K →* G ⧸ N := (QuotientGroup.mk' N).comp K.subtype
    have hle : g.ker ≤ φ.ker := fun x hx => by
      have hxT : x ∈ T := (QuotientGroup.eq_one_iff (x : G)).mp (MonoidHom.mem_ker.mp hx)
      exact (Subgroup.map_eq_bot_iff _).mp h hxT
    exact not_isSolvable_of_simple_nonabelian hnonab (sbkgrp_isSolvable_of_ker_le g φ hφ hle)
  · let j : ↥T →* ↥N := (K.subtype.comp T.subtype).codRestrict N fun x => x.2
    have hj : Function.Injective j := fun a b hab =>
      Subtype.ext (Subtype.ext (congrArg (fun z : N => (z : G)) hab))
    let ψ : ↥j.range →* K ⧸ L.subgroupOf K :=
      (φ.comp T.subtype).comp (MonoidHom.ofInjective hj).symm.toMonoidHom
    have hψ : Function.Surjective ψ := fun s => by
      have hs : s ∈ T.map φ := by rw [h]; trivial
      obtain ⟨t, ht, rfl⟩ := hs
      refine ⟨MonoidHom.ofInjective hj ⟨t, ht⟩, ?_⟩
      show φ (T.subtype ((MonoidHom.ofInjective hj).symm (MonoidHom.ofInjective hj ⟨t, ht⟩))) = φ t
      rw [MulEquiv.symm_apply_apply]
      rfl
    exact hN.isCatalogGroup_of_surjective j.range hnonab ψ hψ

private theorem sbkgrp_catalog_of_quotient_psl2 {m : ℕ} (hm : m ≠ 0) {S : Type} [Group S]
    [IsSimpleGroup S] (hab : ∃ a b : S, a * b ≠ b * a)
    (σ : PSL(2, GaloisField 2 m) →* S) (hσ : Function.Surjective σ) :
    CFSG.Open.IsCatalogGroup S := by
  have hcard : Nat.card (GaloisField 2 m) = 2 ^ m := GaloisField.card 2 m hm
  by_cases h1 : m = 1
  · exfalso
    subst h1
    apply not_isSolvable_of_simple_nonabelian hab
    have hc : Nat.card (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 1)) = 2 ^ 1 * 3 ^ 1 := by
      rw [CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hcard]
      norm_num
    have hsl := isSolvable_of_card_two_three hc
    have hpsl : Group.IsSolvable (PSL(2, GaloisField 2 1)) :=
      Group.isSolvable_of_surjective (QuotientGroup.mk'_surjective
        (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 1))))
    exact Group.isSolvable_of_surjective hσ
  · have h2 : 2 ≤ m := by omega
    have h4 : 4 ≤ 2 ^ m :=
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) h2
    have hsimple : IsSimpleGroup (PSL(2, GaloisField 2 m)) :=
      Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by rw [hcard]; exact h4)
    have hinj := injective_of_surjective_simple σ hσ
    let e : PSL(2, GaloisField 2 m) ≃* S := MulEquiv.ofBijective σ ⟨hinj, hσ⟩
    have : Finite S := Finite.of_surjective σ hσ
    exact CFSG.QuasithinUnique.inCatalog_of_mulEquiv_psl_two_galoisField_two h2 e.symm

private theorem sbkgrp_catalog_of_subgroup_quotient {n : ℕ}
    (hn : n ≠ 0) (Hb : Subgroup PSL(2, GaloisField 2 n)) {S : Type} [Group S] [IsSimpleGroup S]
    (hab : ∃ a b : S, a * b ≠ b * a) (ρ : ↥Hb →* S) (hρ : Function.Surjective ρ) :
    CFSG.Open.IsCatalogGroup S := by
  have hF : Nat.card (GaloisField 2 n) = 2 ^ n := GaloisField.card 2 n hn
  have hne : ∀ {m : ℕ}, m ∣ n → m ≠ 0 := fun {m} hm h0 => hn (by
    rw [h0] at hm
    exact zero_dvd_iff.1 hm)
  rcases psl2_subgroup_dichotomy hF Hb with hsolv | hA5 | ⟨m, hm, hPSL⟩ | ⟨m, hm, hPGL⟩
  · exact absurd (Group.isSolvable_of_surjective hρ) (not_isSolvable_of_simple_nonabelian hab)
  · obtain ⟨e⟩ := hA5
    have : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
    have hs : Function.Surjective (ρ.comp e.symm.toMonoidHom) := hρ.comp e.symm.surjective
    have hinj := injective_of_surjective_simple (ρ.comp e.symm.toMonoidHom) hs
    exact ⟨.alternating 5 le_rfl,
      ⟨(MulEquiv.ofBijective (ρ.comp e.symm.toMonoidHom) ⟨hinj, hs⟩).symm⟩⟩
  · obtain ⟨e⟩ := hPSL
    exact sbkgrp_catalog_of_quotient_psl2 (hne hm) hab (ρ.comp e.symm.toMonoidHom)
      (hρ.comp e.symm.surjective)
  · obtain ⟨e⟩ := hPGL
    have hm0 : m ≠ 0 := hne (Dvd.dvd.trans (dvd_mul_left m 2) hm)
    let σ : PSL(2, GaloisField 2 m) →* S :=
      (ρ.comp e.symm.toMonoidHom).comp
        (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := GaloisField 2 m))
    have hσ : Function.Surjective σ :=
      (hρ.comp e.symm.surjective).comp
        (CFSG.SignalizerFunctorTheorem.McBride.PSL2Even.toPGL_surjective (GaloisField 2 m))
    exact sbkgrp_catalog_of_quotient_psl2 hm0 hab σ hσ

private theorem sbkgrp_isKGroup_psl2 {n : ℕ} (hn : n ≠ 0) :
    CFSG.Open.IsKGroup PSL(2, GaloisField 2 n) := by
  intro K L _ _ _ hnonab
  exact sbkgrp_catalog_of_subgroup_quotient hn K hnonab (QuotientGroup.mk' (L.subgroupOf K))
    (QuotientGroup.mk'_surjective _)

private instance sbkgrp_normal_oResidual (Y : Type) [Group Y] : (oResidual 2 Y).Normal := by
  refine ⟨fun n hn g => ?_⟩
  unfold oResidual at hn ⊢
  have key : Subgroup.map (MulAut.conj g).toMonoidHom
      (Subgroup.closure {x : Y | Nat.Coprime (orderOf x) 2}) ≤
      Subgroup.closure {x : Y | Nat.Coprime (orderOf x) 2} := by
    rw [MonoidHom.map_closure]
    apply Subgroup.closure_mono
    rintro _ ⟨x, hx, rfl⟩
    show Nat.Coprime (orderOf (MulAut.conj g x)) 2
    rwa [MulEquiv.orderOf_eq]
  exact key ⟨n, hn, rfl⟩

private theorem sbkgrp_exists_pow_mem_oResidual {Y : Type} [Group Y] [Finite Y] (x : Y) :
    ∃ k : ℕ, x ^ 2 ^ k ∈ oResidual 2 Y := by
  obtain ⟨k, m, hm, hn⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos x).ne'
  refine ⟨k, Subgroup.subset_closure ?_⟩
  show Nat.Coprime (orderOf (x ^ 2 ^ k)) 2
  rw [orderOf_pow_of_dvd (pow_ne_zero _ two_ne_zero) ⟨m, hn⟩, hn,
    Nat.mul_div_cancel_left _ (by positivity)]
  exact hm.coprime_two_right

private theorem sbkgrp_isSolvable_quotient {Y : Type} [Group Y] [Finite Y] :
    Group.IsSolvable (Y ⧸ oResidual 2 Y) := by
  have hp : IsPGroup 2 (Y ⧸ oResidual 2 Y) := by
    intro g
    induction g using QuotientGroup.induction_on with
    | H x =>
      obtain ⟨k, hk⟩ := sbkgrp_exists_pow_mem_oResidual x
      exact ⟨k, by rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]; exact hk⟩
  have := hp.isNilpotent
  infer_instance

theorem isKGroup_of_typeL2 {n : ℕ} (hn : 2 ≤ n)
    (e : ↥(oResidual 2 (X ⧸ CFSG.pCore 2 X)) ≃*
      CFSG.Assembly.RankThreeEven.projSL 2 (GaloisField 2 n)) :
    CFSG.Open.IsKGroup X := by
  have hpsl : CFSG.Open.IsKGroup PSL(2, GaloisField 2 n) := sbkgrp_isKGroup_psl2 (by omega)
  let eP : ↥(oResidual 2 (X ⧸ CFSG.pCore 2 X)) ≃* PSL(2, GaloisField 2 n) :=
    e.trans (CFSG.RankThree.PartTwo.Sec4.projSLEquivPSL (GaloisField 2 n))
  have hL : CFSG.Open.IsKGroup ↥(oResidual 2 (X ⧸ CFSG.pCore 2 X)) :=
    hpsl.of_injective eP.toMonoidHom eP.injective
  have : Group.IsSolvable ((X ⧸ CFSG.pCore 2 X) ⧸ oResidual 2 (X ⧸ CFSG.pCore 2 X)) :=
    sbkgrp_isSolvable_quotient
  have hbar : CFSG.Open.IsKGroup (X ⧸ CFSG.pCore 2 X) :=
    sbkgrp_isKGroup_of_normal (oResidual 2 (X ⧸ CFSG.pCore 2 X)) hL
  have : Group.IsSolvable (QuotientGroup.mk' (CFSG.pCore 2 X)).ker := by
    rw [QuotientGroup.ker_mk']
    have := CFSG.pCore_isNilpotent (p := 2) (G := X)
    infer_instance
  exact sbkgrp_isKGroup_of_solvable_ker (QuotientGroup.mk' (CFSG.pCore 2 X)) hbar

end CFSG.RankThree.PartTwo.Sec15.SimsBaumann
