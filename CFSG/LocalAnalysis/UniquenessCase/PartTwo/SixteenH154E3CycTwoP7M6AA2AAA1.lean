module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeCycBasic
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeCycSevenBlocks
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeCycSevenCent

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup
open scoped commutatorElement Pointwise

variable {W : Type} [CommGroup W] [Finite W]

private theorem s16h_e3_CycTwoP7M6AA2AAA1_rank_two_of_card {X : Type} [Group X] [Finite X]
    (hcomm : ∀ a b : X, a * b = b * a) (hpow : ∀ a : X, a ^ 7 = 1)
    (hcard : Nat.card X = 7 ^ 2) : IsElemAbelianOfRank 7 2 X := by
  let _ : CommGroup X := { (inferInstance : Group X) with mul_comm := hcomm }
  let _ : Module (ZMod 7) (Additive X) := AddCommGroup.zmodModule (n := 7) fun x => by
    rw [← ofMul_toMul x, ← ofMul_pow, hpow, ofMul_one]
  have hF : Module.Finite (ZMod 7) (Additive X) := Module.Finite.of_finite
  have hFr : Module.Free (ZMod 7) (Additive X) := Module.Free.of_divisionRing _ _
  have h := @Module.natCard_eq_pow_finrank (ZMod 7) (Additive X) _ _ _ hF
  have hfin : Module.finrank (ZMod 7) (Additive X) =
      Module.finrank (ZMod 7) (Fin 2 → ZMod 7) := by
    rw [Nat.card_zmod] at h
    rw [Module.finrank_fin_fun]
    exact Nat.pow_right_injective (by norm_num : 2 ≤ 7) (h.symm.trans hcard)
  exact ⟨AddEquiv.toMultiplicativeRight
    (@LinearEquiv.ofFinrankEq (ZMod 7) (Additive X) (Fin 2 → ZMod 7) _ _ _ hFr _ _ _ _ hF _
      hfin).toAddEquiv⟩

theorem s16h_e3_CycTwoP7M6AA2AAA1_cyc7_structure
    (hW : ∀ w : W, w ^ 2 = 1) (hcard : Nat.card W = 2 ^ 6)
    {A L : Subgroup (MulAut W)} {t x : MulAut W}
    (hLx : L = Subgroup.zpowers x) (hxo : orderOf x = 7)
    (hLn : ∀ g ∈ A, L.map (MulAut.conj g).toMonoidHom = L)
    (hfpf : ∀ w : W, x w = w → w = 1) (ht : t ∈ A) (hinv : t * x * t⁻¹ = x⁻¹)
    (hLA : L ≤ A) (h7 : 2 ≤ CFSG.Open.pRank 7 A) :
    Nat.card ↥A ∣ 294 ∧
      IsElemAbelianOfRank 7 2 ↥(A ⊓ Subgroup.centralizer (L : Set (MulAut W))) ∧
      ((A ⊓ Subgroup.centralizer (L : Set (MulAut W))).subgroupOf A).Normal ∧
      Subgroup.centralizer
          ((A ⊓ Subgroup.centralizer (L : Set (MulAut W))) : Set (MulAut W)) ⊓ A ≤
        A ⊓ Subgroup.centralizer (L : Set (MulAut W)) := by
  classical
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hx7 : x ^ 7 = 1 := by
    have h := pow_orderOf_eq_one x
    rwa [hxo] at h
  have hxL : x ∈ L := by rw [hLx]; exact Subgroup.mem_zpowers x
  have hLcard : Nat.card ↥L = 7 := by rw [hLx, Nat.card_zpowers, hxo]
  obtain ⟨W₁, W₂, hW₁, hW₂, hinf, hsup, ht₁, ht₂, hclass, hstab⟩ :=
    s168e3_cyc7_blocks hW hcard hx7 hfpf hinv
  set C : Subgroup (MulAut W) := A ⊓ Subgroup.centralizer (L : Set (MulAut W)) with hCdef
  have hCx : ∀ c ∈ C, c * x = x * c := by
    intro c hc
    exact (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hc).2 x hxL).symm
  have hC₁ : C ≤ stabSub W₁ := by
    intro c hc
    rw [mem_stabSub]
    have hmap := (hstab c (hCx c hc)).1
    intro u
    constructor
    · intro hu
      exact (Subgroup.mem_map_iff_mem (f := c.toMonoidHom) c.injective).mp (hmap.symm ▸ hu)
    · intro hu
      exact hmap ▸ (Subgroup.mem_map_iff_mem (f := c.toMonoidHom) c.injective).mpr hu
  have hC₂ : C ≤ stabSub W₂ := by
    intro c hc
    rw [mem_stabSub]
    have hmap := (hstab c (hCx c hc)).2
    intro u
    constructor
    · intro hu
      exact (Subgroup.mem_map_iff_mem (f := c.toMonoidHom) c.injective).mp (hmap.symm ▸ hu)
    · intro hu
      exact hmap ▸ (Subgroup.mem_map_iff_mem (f := c.toMonoidHom) c.injective).mpr hu
  have hx₁ : x ∈ stabSub W₁ := by
    rw [mem_stabSub]
    have hmap := (hstab x rfl).1
    intro u
    constructor
    · intro hu
      exact (Subgroup.mem_map_iff_mem (f := x.toMonoidHom) x.injective).mp (hmap.symm ▸ hu)
    · intro hu
      exact hmap ▸ (Subgroup.mem_map_iff_mem (f := x.toMonoidHom) x.injective).mpr hu
  have hx₂ : x ∈ stabSub W₂ := by
    rw [mem_stabSub]
    have hmap := (hstab x rfl).2
    intro u
    constructor
    · intro hu
      exact (Subgroup.mem_map_iff_mem (f := x.toMonoidHom) x.injective).mp (hmap.symm ▸ hu)
    · intro hu
      exact hmap ▸ (Subgroup.mem_map_iff_mem (f := x.toMonoidHom) x.injective).mpr hu
  have hn₁ : ∃ y ∈ W₁, x y ≠ y := by
    by_contra h
    push Not at h
    have hbot : W₁ = ⊥ := (Subgroup.eq_bot_iff_forall W₁).mpr fun y hy => hfpf y (h y hy)
    rw [hbot, Subgroup.card_bot] at hW₁
    norm_num at hW₁
  have hn₂ : ∃ y ∈ W₂, x y ≠ y := by
    by_contra h
    push Not at h
    have hbot : W₂ = ⊥ := (Subgroup.eq_bot_iff_forall W₂).mpr fun y hy => hfpf y (h y hy)
    rw [hbot, Subgroup.card_bot] at hW₂
    norm_num at hW₂
  have hfac₁ : Nat.card ↥(autSub C W₁) ∣ 7 :=
    s168e3_cyc7_card_autSub_dvd hW hW₁ hx₁ hx7 hn₁ hC₁ hCx
  have hfac₂ : Nat.card ↥(autSub C W₂) ∣ 7 :=
    s168e3_cyc7_card_autSub_dvd hW hW₂ hx₂ hx7 hn₂ hC₂ hCx
  have hdiv := s168e3_cyc7_card_dvd (W := W) hW hW₁ hW₂ hsup hx₁ hx₂ hx7 hn₁ hn₂ hC₁ hC₂ hCx
  have hcardC_eq : Nat.card ↥(autSub C W₂) * Nat.card ↥(C ⊓ centSub W₂) = Nat.card ↥C :=
    card_autSub_mul hC₂
  have hC_dvd : Nat.card ↥C ∣ 49 := by
    have h := mul_dvd_mul hdiv.1 hdiv.2
    rw [hcardC_eq] at h
    norm_num at h ⊢
    exact h
  have hA_dvd : Nat.card ↥A ∣ 6 * Nat.card ↥C := by
    have h := s168e3_cyc_card_dvd (p := 7) (by norm_num) hLcard hLn
    rw [hCdef]
    norm_num at h
    exact h
  have h49A : 49 ∣ Nat.card ↥A := by
    obtain ⟨E, hEA, hEab, hEcard⟩ :=
      CFSG.SectionRank.exists_pRank (p := 7) (by norm_num) A
    have hpow : 7 ^ 2 ∣ Nat.card ↥E := by
      rw [hEcard]
      exact pow_dvd_pow 7 h7
    exact hpow.trans (Subgroup.card_dvd_of_le hEA)
  have h49C : 49 ∣ Nat.card ↥C := by
    have h : 49 ∣ 6 * Nat.card ↥C := h49A.trans hA_dvd
    exact (show Nat.Coprime 49 6 by norm_num).dvd_of_dvd_mul_left h
  have hCcard : Nat.card ↥C = 49 := (Nat.dvd_antisymm h49C hC_dvd).symm
  have hCp : IsPGroup 7 ↥C := IsPGroup.of_card (n := 2) (by rw [hCcard]; norm_num)
  have hCcomm : ∀ a b : ↥C, a * b = b * a :=
    commutative_of_card_le_prime_sq hCp (by rw [hCcard]; norm_num)
  let ψ : ↥C →* MulAut W₁ × MulAut W₂ :=
    ((resHom W₁).comp (Subgroup.inclusion hC₁)).prod
      ((resHom W₂).comp (Subgroup.inclusion hC₂))
  have hkerψ : ∀ a : ↥C, ψ a = 1 → a = 1 := by
    intro a ha
    have ha' : (((resHom W₁).comp (Subgroup.inclusion hC₁)) a,
        ((resHom W₂).comp (Subgroup.inclusion hC₂)) a) = 1 := by
      simpa [ψ] using ha
    have ha₁ : resHom W₁ (Subgroup.inclusion hC₁ a) = 1 := by
      simpa using congrArg Prod.fst ha'
    have ha₂ : resHom W₂ (Subgroup.inclusion hC₂ a) = 1 := by
      simpa using congrArg Prod.snd ha'
    have hfix₁ : ∀ u ∈ W₁, (a : MulAut W) u = u := by
      intro u hu
      have hφ : resHom W₁ (Subgroup.inclusion hC₁ a) ⟨u, hu⟩ =
          (1 : MulAut W₁) ⟨u, hu⟩ := by rw [ha₁]
      have h := congrArg (fun z : W₁ => (z : W)) hφ
      simpa [resHom_apply] using h
    have hfix₂ : ∀ u ∈ W₂, (a : MulAut W) u = u := by
      intro u hu
      have hφ : resHom W₂ (Subgroup.inclusion hC₂ a) ⟨u, hu⟩ =
          (1 : MulAut W₂) ⟨u, hu⟩ := by rw [ha₂]
      have h := congrArg (fun z : W₂ => (z : W)) hφ
      simpa [resHom_apply] using h
    refine Subtype.ext (MulEquiv.ext fun w => ?_)
    show (a : MulAut W) w = w
    have hw : w ∈ W₁ ⊔ W₂ := by rw [hsup]; exact Subgroup.mem_top w
    rw [Subgroup.mem_sup] at hw
    obtain ⟨u₁, hu₁, u₂, hu₂, hu₁₂⟩ := hw
    rw [← hu₁₂, map_mul, hfix₁ u₁ hu₁, hfix₂ u₂ hu₂]
  have hpow₁ : ∀ a : ↥C, (resHom W₁ (Subgroup.inclusion hC₁ a)) ^ 7 = 1 := by
    intro a
    have hauto : resHom W₁ (Subgroup.inclusion hC₁ a) ∈ autSub C W₁ :=
      mem_autSub.mpr ⟨Subgroup.inclusion hC₁ a, a.2, rfl⟩
    exact orderOf_dvd_iff_pow_eq_one.mp
      ((Subgroup.orderOf_dvd_natCard (autSub C W₁) hauto).trans hfac₁)
  have hpow₂ : ∀ a : ↥C, (resHom W₂ (Subgroup.inclusion hC₂ a)) ^ 7 = 1 := by
    intro a
    have hauto : resHom W₂ (Subgroup.inclusion hC₂ a) ∈ autSub C W₂ :=
      mem_autSub.mpr ⟨Subgroup.inclusion hC₂ a, a.2, rfl⟩
    exact orderOf_dvd_iff_pow_eq_one.mp
      ((Subgroup.orderOf_dvd_natCard (autSub C W₂) hauto).trans hfac₂)
  have hCpow : ∀ a : ↥C, a ^ 7 = 1 := by
    intro a
    refine hkerψ (a ^ 7) ?_
    rw [map_pow]
    simpa [ψ, MonoidHom.prod_apply, hpow₁ a, hpow₂ a]
  have hCnormal : (C.subgroupOf A).Normal := by
    have hAN : A ≤ Subgroup.normalizer (L : Set (MulAut W)) := fun g hg =>
      Subgroup.mem_normalizer_iff_map_conj_eq.mpr (hLn g hg)
    haveI : ((Subgroup.centralizer (L : Set (MulAut W))).subgroupOf
        (Subgroup.normalizer (L : Set (MulAut W)))).Normal :=
      Subgroup.normal_subgroupOf_centralizer_normalizer (L : Set (MulAut W))
    have hcomap : (((Subgroup.centralizer (L : Set (MulAut W))).subgroupOf
        (Subgroup.normalizer (L : Set (MulAut W)))).comap
        (Subgroup.inclusion hAN : ↥A →* ↥(Subgroup.normalizer (L : Set (MulAut W))))) =
        C.subgroupOf A := by
      ext a
      simp only [Subgroup.mem_comap, Subgroup.mem_subgroupOf, hCdef, Subgroup.mem_inf,
        Subgroup.coe_inclusion]
      constructor
      · intro h
        exact ⟨a.2, h⟩
      · rintro ⟨-, h⟩
        exact h
    rw [← hcomap]
    infer_instance
  have hLC : L ≤ C := by
    rw [hCdef]
    refine le_inf hLA ?_
    haveI : IsCyclic ↥L := isCyclic_of_prime_card hLcard
    letI : CommGroup ↥L := IsCyclic.commGroup
    exact Subgroup.le_centralizer_iff_isMulCommutative.mpr inferInstance
  have hcent : Subgroup.centralizer (C : Set (MulAut W)) ⊓ A ≤ C := by
    intro g hg
    have hgA : g ∈ A := (Subgroup.mem_inf.mp hg).2
    have hgC : g ∈ Subgroup.centralizer (C : Set (MulAut W)) := (Subgroup.mem_inf.mp hg).1
    have hgcent : g ∈ Subgroup.centralizer (L : Set (MulAut W)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro l hl
      exact Subgroup.mem_centralizer_iff.mp hgC l (hLC hl)
    exact Subgroup.mem_inf.mpr ⟨hgA, hgcent⟩
  refine ⟨?_, ?_, hCnormal, hcent⟩
  · have h := hA_dvd.trans (mul_dvd_mul_left 6 hC_dvd)
    norm_num at h
    exact h
  · exact s16h_e3_CycTwoP7M6AA2AAA1_rank_two_of_card hCcomm hCpow (by rw [hCcard]; norm_num)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
