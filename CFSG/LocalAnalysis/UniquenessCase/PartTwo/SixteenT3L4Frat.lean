module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3Close16Frat
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3Close16KitAlt
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenT3L4Cover

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]
variable {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}

theorem s16t_l4_barSub_normalizer {D : Data G} {V₀ V : Subgroup G} {hV : IsElemAbelian 2 V}
    (hM : D.M ≤ stabTil V₀ V) {Y A : Subgroup G} (hYM : Y ≤ D.M)
    (hYn : (Y.subgroupOf D.M).Normal) (hAY : A ≤ Y) {p : ℕ} (hp : p.Prime) (hA : Nat.card A = p)
    (hker : ¬ p ∣ Nat.card ↥(Y ⊓ F11.CTilde D.M V₀ V)) {q : MulAut (Vtil V₀ V hV)}
    (hqM : q ∈ Mbar D.M V₀ V hV)
    (hq : q ∈ normalizer ((barSub V₀ V hV A : Subgroup (MulAut (Vtil V₀ V hV))) :
      Set (MulAut (Vtil V₀ V hV)))) :
    ∃ n : G, n ∈ normalizer (A : Set G) ∧ n ∈ D.M ∧
      ∃ h : n ∈ stabTil V₀ V, actTil V₀ V hV ⟨n, h⟩ = q := by
  classical
  have hMn : D.M ≤ normalizer (V : Set G) := hM.trans (stabTil_le_normalizer V₀ V)
  have hADM : A ≤ D.M := hAY.trans hYM
  let φ : ↥D.M →* MulAut (Vtil V₀ V hV) :=
    (actTil V₀ V hV).comp (Subgroup.inclusion hM)
  have hφker : φ.ker = (F11.CTilde D.M V₀ V).subgroupOf D.M := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, mem_cTilde_iff hV hMn]
    constructor
    · rintro h1
      exact ⟨x.2, ⟨hM x.2, h1⟩⟩
    · rintro ⟨-, h, h1⟩
      have hx : (⟨(x : G), hM x.2⟩ : ↥(stabTil V₀ V)) = ⟨(x : G), h⟩ := Subtype.ext rfl
      show actTil V₀ V hV ⟨(x : G), hM x.2⟩ = 1
      rw [hx]
      exact h1
  have hYker : (Y.subgroupOf D.M) ⊓ φ.ker =
      (Y ⊓ F11.CTilde D.M V₀ V).subgroupOf D.M := by
    rw [hφker]
    simp only [Subgroup.subgroupOf, Subgroup.comap_inf]
  have hkercard : Nat.card ↥((Y.subgroupOf D.M) ⊓ φ.ker) =
      Nat.card ↥(Y ⊓ F11.CTilde D.M V₀ V) := by
    rw [hYker]
    exact Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (inf_le_left.trans hYM)).toEquiv
  have hA'card : Nat.card ↥(A.subgroupOf D.M) = p := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hADM).toEquiv]
    exact hA
  have hA'Y' : A.subgroupOf D.M ≤ Y.subgroupOf D.M := fun x hx => hAY hx
  have hmapA : (A.subgroupOf D.M).map φ = barSub V₀ V hV A := by
    ext ψ
    constructor
    · intro hψ
      rw [Subgroup.mem_map] at hψ
      obtain ⟨x, hx, rfl⟩ := hψ
      exact actTil_mem_barSub V₀ V hV hx (hM x.2)
    · intro hψ
      obtain ⟨g, hgA, hgψ⟩ := (mem_barSub V₀ V hV A ψ).1 hψ
      refine Subgroup.mem_map.2 ⟨⟨(g : G), hADM hgA⟩, hgA, ?_⟩
      change actTil V₀ V hV ⟨(g : G), hM (hADM hgA)⟩ = ψ
      rw [show (⟨(g : G), hM (hADM hgA)⟩ : ↥(stabTil V₀ V)) = g from Subtype.ext rfl]
      exact hgψ
  have hrange : φ.range = Mbar D.M V₀ V hV := by
    ext ψ
    rw [MonoidHom.mem_range, mem_barSub]
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨⟨(x : G), hM x.2⟩, x.2, rfl⟩
    · rintro ⟨g, hg, rfl⟩
      exact ⟨⟨(g : G), hg⟩, congrArg (actTil V₀ V hV) (Subtype.ext rfl)⟩
  have hq' : q ∈ normalizer (((A.subgroupOf D.M).map φ : Subgroup
      (MulAut (Vtil V₀ V hV))) : Set (MulAut (Vtil V₀ V hV))) := by
    rw [hmapA]
    exact hq
  have hqrange : q ∈ φ.range := by
    rw [hrange]
    exact hqM
  obtain ⟨x, hxN, hxq⟩ :=
    close16_frattini_lift (M := ↥D.M) (Q := MulAut (Vtil V₀ V hV)) φ hYn hA'Y' hp hA'card
      (by rw [hkercard]; exact hker) hq' hqrange
  have hxnorm : (x : G) ∈ normalizer (A : Set G) := by
    have h1 : x ∈ (normalizer (A : Set G)).subgroupOf D.M := by
      rw [Subgroup.subgroupOf_normalizer_eq hADM]
      exact hxN
    exact h1
  exact ⟨(x : G), hxnorm, x.2, hM x.2, hxq⟩

theorem s16t_l4_exists_lift_barSub {D : Data G} {V₀ V : Subgroup G} {hV : IsElemAbelian 2 V}
    (hM : D.M ≤ stabTil V₀ V) {J : Subgroup G} (hJ : J ≤ D.M)
    {E : Subgroup (MulAut (Vtil V₀ V hV))} (hE : E ≤ barSub V₀ V hV J) {p : ℕ} (hp : p.Prime)
    (hEp : IsPGroup p E) :
    ∃ P : Subgroup G, P ≤ J ∧ IsPGroup p P ∧ barSub V₀ V hV P = E := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  let φ : ↥J →* ↥(barSub V₀ V hV J) :=
    MonoidHom.codRestrict ((actTil V₀ V hV).comp (Subgroup.inclusion (hJ.trans hM)))
      (barSub V₀ V hV J)
      (fun g => (mem_barSub V₀ V hV J _).2 ⟨⟨(g : G), (hJ.trans hM) g.2⟩, g.2, rfl⟩)
  have hφsurj : Function.Surjective φ := by
    rintro ⟨ψ, hψ⟩
    obtain ⟨g, hg, hgψ⟩ := (mem_barSub V₀ V hV J ψ).1 hψ
    refine ⟨⟨(g : G), hg⟩, ?_⟩
    refine Subtype.ext ?_
    show actTil V₀ V hV ⟨(g : G), (hJ.trans hM) hg⟩ = ψ
    rw [show (⟨(g : G), (hJ.trans hM) hg⟩ : ↥(stabTil V₀ V)) = g from Subtype.ext rfl]
    exact hgψ
  let E' : Subgroup ↥(barSub V₀ V hV J) := E.subgroupOf (barSub V₀ V hV J)
  have hE'p : IsPGroup p E' :=
    hEp.of_equiv (Subgroup.subgroupOfEquivOfLe hE).symm
  let Ppre : Subgroup ↥J := E'.comap φ
  let π : ↥Ppre →* ↥E' :=
    (φ.comp Ppre.subtype).codRestrict E' (fun x => x.2)
  have hπsurj : Function.Surjective π := by
    intro y
    obtain ⟨x, hx⟩ := hφsurj (y : ↥(barSub V₀ V hV J))
    refine ⟨⟨x, ?_⟩, Subtype.ext hx⟩
    show φ x ∈ E'
    rw [hx]
    exact y.2
  obtain ⟨T, hT⟩ :=
    CFSG.SignalizerFunctor.Helpers.surjective_pgroup_sylow_lift p hp π hπsurj hE'p
  let R : Subgroup ↥J := (T : Subgroup ↥Ppre).map Ppre.subtype
  let P : Subgroup G := R.map J.subtype
  have hPJ : P ≤ J := Subgroup.map_subtype_le _
  have hPp : IsPGroup p P := (T.isPGroup'.map Ppre.subtype).map J.subtype
  have hRφ : R.map φ = E' := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      obtain ⟨y, hyT, rfl⟩ := Subgroup.mem_map.1 hx
      exact y.2
    · intro z hz
      let w : ↥E' := ⟨z, hz⟩
      have hzT : w ∈ (T : Subgroup ↥Ppre).map π := by
        rw [hT]
        exact Subgroup.mem_top w
      obtain ⟨y, hyT, hyz⟩ := Subgroup.mem_map.1 hzT
      refine Subgroup.mem_map.2 ⟨Ppre.subtype y, ⟨y, hyT, rfl⟩, ?_⟩
      have h2 : (π y : ↥(barSub V₀ V hV J)) = z := by
        simpa [w] using congrArg Subtype.val hyz
      exact (show (φ (Ppre.subtype y) : ↥(barSub V₀ V hV J)) = π y from rfl).trans h2
  refine ⟨P, hPJ, hPp, ?_⟩
  apply le_antisymm
  · intro ψ hψ
    obtain ⟨g, hgP, hgψ⟩ := (mem_barSub V₀ V hV P ψ).1 hψ
    obtain ⟨x, hxR, hxg⟩ := Subgroup.mem_map.1 hgP
    obtain ⟨y, hyT, hyx⟩ := Subgroup.mem_map.1 hxR
    have hyE : (φ (Ppre.subtype y) : MulAut (Vtil V₀ V hV)) ∈ E :=
      Subgroup.mem_subgroupOf.1 y.2
    have hg_eq : g = ⟨(Ppre.subtype y : G), hM (hJ (Ppre.subtype y).2)⟩ := by
      apply Subtype.ext
      rw [show (g : G) = (x : G) from hxg.symm,
        show (x : G) = (Ppre.subtype y : G) from (congrArg Subtype.val hyx).symm]
    rw [← hgψ, hg_eq]
    have hArg : (Subgroup.inclusion (hJ.trans hM) (Ppre.subtype y) : ↥(stabTil V₀ V)) =
        ⟨(Ppre.subtype y : G), hM (hJ (Ppre.subtype y).2)⟩ := Subtype.ext rfl
    have hφy : (φ (Ppre.subtype y) : MulAut (Vtil V₀ V hV)) =
        actTil V₀ V hV ⟨(Ppre.subtype y : G), hM (hJ (Ppre.subtype y).2)⟩ := by
      show actTil V₀ V hV (Subgroup.inclusion (hJ.trans hM) (Ppre.subtype y)) =
        actTil V₀ V hV ⟨(Ppre.subtype y : G), hM (hJ (Ppre.subtype y).2)⟩
      exact congrArg (actTil V₀ V hV) hArg
    rwa [hφy] at hyE
  · intro ψ hψ
    have hψE' : (⟨ψ, hE hψ⟩ : ↥(barSub V₀ V hV J)) ∈ E' :=
      Subgroup.mem_subgroupOf.2 hψ
    let w : ↥E' := ⟨⟨ψ, hE hψ⟩, hψE'⟩
    have hwT : w ∈ (T : Subgroup ↥Ppre).map π := by
      rw [hT]
      exact Subgroup.mem_top w
    obtain ⟨y, hyT, hyeq⟩ := Subgroup.mem_map.1 hwT
    have hxR : Ppre.subtype y ∈ R := ⟨y, hyT, rfl⟩
    have hgP : ((Ppre.subtype y : ↥J) : G) ∈ P := ⟨Ppre.subtype y, hxR, rfl⟩
    refine (mem_barSub V₀ V hV P ψ).2
      ⟨⟨(Ppre.subtype y : G), hM (hJ (Ppre.subtype y).2)⟩, hgP, ?_⟩
    have h1 : actTil V₀ V hV ⟨(Ppre.subtype y : G), hM (hJ (Ppre.subtype y).2)⟩ =
        (φ (Ppre.subtype y) : MulAut (Vtil V₀ V hV)) := rfl
    rw [h1]
    have h2 : (φ (Ppre.subtype y) : ↥(barSub V₀ V hV J)) = w := by
      have hπ : (φ (Ppre.subtype y) : ↥(barSub V₀ V hV J)) =
          (π y : ↥(barSub V₀ V hV J)) := rfl
      exact hπ.trans (congrArg Subtype.val hyeq)
    exact congrArg Subtype.val h2

theorem s16t_l4_not_isCyclic_of_barSub {D : Data G} {V₀ V : Subgroup G} {hV : IsElemAbelian 2 V}
    (hM : D.M ≤ stabTil V₀ V) {P : Subgroup G} (hP : P ≤ D.M)
    (hnc : ¬ IsCyclic ↥(barSub V₀ V hV P)) : ¬ IsCyclic ↥P := by
  obtain ⟨φ, hφsurj, -⟩ := s16t_l4_exists_hom_barSub hM hP
  intro hcyc
  exact hnc (isCyclic_of_surjective φ hφsurj)

theorem s16t_l4_card_barSub {D : Data G} {V₀ V : Subgroup G} {hV : IsElemAbelian 2 V}
    (hM : D.M ≤ stabTil V₀ V) {Y A : Subgroup G} (hYM : Y ≤ D.M) (hAY : A ≤ Y) {p : ℕ}
    (hp : p.Prime) (hA : IsPGroup p A)
    (hker : ¬ p ∣ Nat.card ↥(Y ⊓ F11.CTilde D.M V₀ V)) :
    Nat.card ↥(barSub V₀ V hV A) = Nat.card ↥A := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨φ, hφsurj, hφker⟩ := s16t_l4_exists_hom_barSub hM (hAY.trans hYM)
  have hAKbot : A ⊓ F11.CTilde D.M V₀ V = ⊥ := by
    have hKp : IsPGroup p ↥(A ⊓ F11.CTilde D.M V₀ V) :=
      IsPGroup.to_le (H := A ⊓ F11.CTilde D.M V₀ V) (K := A) hA inf_le_left
    have hle : A ⊓ F11.CTilde D.M V₀ V ≤ Y ⊓ F11.CTilde D.M V₀ V :=
      inf_le_inf hAY le_rfl
    rcases hKp.card_eq_or_dvd with h1 | hpd
    · exact Subgroup.eq_bot_of_card_eq (H := A ⊓ F11.CTilde D.M V₀ V) h1
    · exact absurd (hpd.trans (Subgroup.card_dvd_of_le hle)) hker
  have hkerbot : φ.ker = ⊥ := by
    rw [hφker, hAKbot]
    simp
  have hinj : Function.Injective φ := φ.ker_eq_bot_iff.mp hkerbot
  exact (Nat.card_congr (Equiv.ofBijective φ ⟨hinj, hφsurj⟩)).symm

theorem s16t_l4_exists_three_normalizing (hS : S16tL4Setting D V₀ V L hV)
    {B : Subgroup (MulAut (Vtil V₀ V hV))} (hBL : B ≤ lBar V₀ V hV L) (hB : Nat.card B = 7) :
    ∃ y ∈ lBar V₀ V hV L, orderOf y = 3 ∧ y ∈ normalizer (B : Set (MulAut (Vtil V₀ V hV))) ∧
      ∃ a ∈ B, y * a * y⁻¹ ≠ a := by
  have hcard : Nat.card ↥(B.subgroupOf (lBar V₀ V hV L)) = 7 := by
    rw [← hB]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBL).toEquiv
  obtain ⟨y, hy3, hyN, a, haB, hya⟩ :=
    close16_alt_eight_normalizer_three (s16t_l4_lbar_isAlt hS) hcard
  refine ⟨(y : MulAut (Vtil V₀ V hV)), y.2, ?_, ?_, (a : MulAut (Vtil V₀ V hV)), haB, ?_⟩
  · rw [← Subgroup.orderOf_coe] at hy3
    exact hy3
  · rw [Subgroup.mem_normalizer_iff]
    intro g
    constructor
    · intro hg
      have := (Subgroup.mem_normalizer_iff.1 hyN ⟨g, hBL hg⟩).1 hg
      exact this
    · intro hg
      have hgL : g ∈ lBar V₀ V hV L := by
        have h1 : (y : MulAut (Vtil V₀ V hV))⁻¹ * ((y : MulAut (Vtil V₀ V hV)) * g *
            (y : MulAut (Vtil V₀ V hV))⁻¹) * (y : MulAut (Vtil V₀ V hV)) ∈ lBar V₀ V hV L :=
          (lBar V₀ V hV L).mul_mem ((lBar V₀ V hV L).mul_mem ((lBar V₀ V hV L).inv_mem y.2)
            (hBL hg)) y.2
        simpa [mul_assoc] using h1
      exact (Subgroup.mem_normalizer_iff.1 hyN ⟨g, hgL⟩).2 hg
  · intro h
    exact hya (Subtype.ext h)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
