module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264SevenSq
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DataThree
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsComp
public import CFSG.Quasithin.Background.Asc81cTenFourA

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LocalAnalysis.UniquenessCase CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.Quasithin
  CFSG.Open Subgroup
open scoped commutatorElement

variable {W : Type} [CommGroup W] [Finite W]

private theorem w16g_card_mulAut_dvd_six {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1) (hrk : rk ↥(⊤ : Subgroup W) ≤ 2) :
    Nat.card (MulAut W) ∣ 6 := by
  have hcardW : Nat.card W = 2 ^ rk ↥(⊤ : Subgroup W) := by
    rw [← Subgroup.card_top]
    exact card_eq_two_pow hW ⊤
  obtain ⟨e⟩ := CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary (p := 2) (W := W)
    (fun a b => mul_comm a b) hW hcardW
  rw [CFSG.SectionRank.Ccomm.card_mulAut_eq_card_GL e, CFSG.SectionRank.Ccomm.card_GL_zmod]
  set n := rk ↥(⊤ : Subgroup W) with hn
  have hnle : n ≤ 2 := by omega
  interval_cases n <;> decide +kernel

theorem w16f_perfect_gl_three (hW : ∀ w : W, w ^ 2 = 1) (hrk : rk ↥(⊤ : Subgroup W) ≤ 3)
    (X : Subgroup (MulAut W)) (hperf : ⁅X, X⁆ = X) (hne : X ≠ ⊥) :
    rk ↥(⊤ : Subgroup W) = 3 ∧ X = ⊤ := by
  haveI : Group.IsPerfect ↥X := Subgroup.isPerfect_iff.mpr hperf
  haveI : Nontrivial ↥X := (Subgroup.nontrivial_iff_ne_bot X).mpr hne
  by_cases h2 : rk ↥(⊤ : Subgroup W) ≤ 2
  · exfalso
    have hdvd6 : Nat.card (MulAut W) ∣ 6 := w16g_card_mulAut_dvd_six hW h2
    have hdvdX : Nat.card ↥X ∣ 2 ^ 1 * 3 ^ 1 := by
      simpa using (Subgroup.card_subgroup_dvd_card X).trans hdvd6
    have hsol : Group.IsSolvable ↥X := by
      obtain ⟨y, z, hy, hz, hyz⟩ := Nat.dvd_mul.1 hdvdX
      obtain ⟨i, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hy
      obtain ⟨j, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hz
      have : Fintype ↥X := Fintype.ofFinite ↥X
      exact CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow
        Nat.prime_two Nat.prime_three (by norm_num)
        (by rw [← Nat.card_eq_fintype_card, ← hyz])
    exact (Group.IsPerfect.not_isSolvable ↥X) hsol
  · have hrk3 : rk ↥(⊤ : Subgroup W) = 3 := by omega
    have hcardW8 : Nat.card W = 8 := by
      have h := card_eq_two_pow hW ⊤
      rw [hrk3] at h
      simpa using h
    have hcard168 : Nat.card (MulAut W) = 168 :=
      (CFSG.Walter.card_mulAut_of_elementary (Q := W) hW).2 hcardW8
    have hdvd168 : Nat.card ↥X ∣ 168 := by
      rw [← hcard168]
      exact Subgroup.card_subgroup_dvd_card X
    obtain ⟨_, hcardX⟩ := CFSG.LocalAnalysis.GLTheoremA.KD264Gen.Seven.perfect_dvd_168
      (Group.IsPerfect.commutator_eq_top (G := ↥X)) inferInstance hdvd168
    refine ⟨hrk3, Subgroup.eq_top_of_card_eq X ?_⟩
    rw [hcardX, hcard168]

theorem w16f_diag_dichotomy (hW : ∀ w : W, w ^ 2 = 1) {Y K : Subgroup (MulAut W)}
    (hK : IsComponentOf K Y) {t : MulAut W} (ht : t ∈ Y) (ht2 : orderOf t = 2)
    (hrk : rk ↥(commSub ⊤ (Subgroup.zpowers t)) ≤ 3)
    (hmove : K.map (MulAut.conj t).toMonoidHom ≠ K) :
    (∀ a ∈ K, ∀ u ∈ commSub ⊤ (Subgroup.zpowers t), (a * (t * a * t⁻¹)) u = u) ∨
      ((¬ ∀ a ∈ K, ∀ u ∈ commSub ⊤ (Subgroup.zpowers t), (a * (t * a * t⁻¹)) u = u) ∧
        rk ↥(commSub ⊤ (Subgroup.zpowers t)) = 3 ∧
        ∃ f : ↥K →* Matrix.GeneralLinearGroup (Fin 3) (ZMod 2), Function.Surjective f) := by
  classical
  let T : Subgroup W := commSub ⊤ (Subgroup.zpowers t)
  have hKt : IsComponentOf (K.map (MulAut.conj t).toMonoidHom) Y :=
    isComponentOf_map_conj_of_mem hK ht
  have hcomm : ∀ k ∈ K.map (MulAut.conj t).toMonoidHom, ∀ l ∈ K, k * l = l * k := by
    rcases eq_or_commute_of_isComponentOf hK hKt with hEq | hcom
    · exact absurd hEq.symm hmove
    · intro k hk l hl
      exact (hcom l hl k hk).symm
  have hmemKt : ∀ a : ↥K,
      t * (a : MulAut W) * t⁻¹ ∈ K.map (MulAut.conj t).toMonoidHom := by
    intro a
    refine Subgroup.mem_map.mpr ⟨a, a.2, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  have htt : t * t = 1 := by rw [← pow_two, ← ht2]; exact pow_orderOf_eq_one t
  let δ : ↥K →* MulAut W :=
    { toFun := fun a => (a : MulAut W) * (t * (a : MulAut W) * t⁻¹)
      map_one' := by simp
      map_mul' := fun a b => by
        have hCB : (t * (a : MulAut W) * t⁻¹) * (b : MulAut W) =
            (b : MulAut W) * (t * (a : MulAut W) * t⁻¹) :=
          hcomm _ (hmemKt a) b b.2
        change (↑(a * b) : MulAut W) * (t * ↑(a * b) * t⁻¹) =
          ((a : MulAut W) * (t * (a : MulAut W) * t⁻¹)) *
            ((b : MulAut W) * (t * (b : MulAut W) * t⁻¹))
        rw [Subgroup.coe_mul]
        have hconj : t * ((a : MulAut W) * (b : MulAut W)) * t⁻¹ =
            (t * (a : MulAut W) * t⁻¹) * (t * (b : MulAut W) * t⁻¹) := by group
        rw [hconj]
        calc ((a : MulAut W) * (b : MulAut W)) *
              ((t * (a : MulAut W) * t⁻¹) * (t * (b : MulAut W) * t⁻¹))
            = (a : MulAut W) * ((b : MulAut W) *
                ((t * (a : MulAut W) * t⁻¹) * (t * (b : MulAut W) * t⁻¹))) := by
                group
          _ = (a : MulAut W) * (((b : MulAut W) * (t * (a : MulAut W) * t⁻¹)) *
                (t * (b : MulAut W) * t⁻¹)) := by group
          _ = (a : MulAut W) * (((t * (a : MulAut W) * t⁻¹) * (b : MulAut W)) *
                (t * (b : MulAut W) * t⁻¹)) := by rw [hCB]
          _ = (a : MulAut W) * ((t * (a : MulAut W) * t⁻¹) * ((b : MulAut W) *
                (t * (b : MulAut W) * t⁻¹))) := by group
          _ = ((a : MulAut W) * (t * (a : MulAut W) * t⁻¹)) *
                ((b : MulAut W) * (t * (b : MulAut W) * t⁻¹)) := by group }
  have hδconj : ∀ a : ↥K, t * δ a * t⁻¹ = δ a := by
    intro a
    have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
    have hCB : (t * (a : MulAut W) * t) * (a : MulAut W) =
        (a : MulAut W) * (t * (a : MulAut W) * t) := by
      simpa only [htinv] using hcomm _ (hmemKt a) a a.2
    change t * ((a : MulAut W) * (t * (a : MulAut W) * t⁻¹)) * t⁻¹ =
      (a : MulAut W) * (t * (a : MulAut W) * t⁻¹)
    rw [htinv]
    calc t * ((a : MulAut W) * (t * (a : MulAut W) * t)) * t
        = t * (a : MulAut W) * t * (a : MulAut W) * (t * t) := by group
      _ = t * (a : MulAut W) * t * (a : MulAut W) := by rw [htt, mul_one]
      _ = (t * (a : MulAut W) * t) * (a : MulAut W) := by group
      _ = (a : MulAut W) * (t * (a : MulAut W) * t) := hCB
  have hδcomm : ∀ a : ↥K, δ a * t = t * δ a := by
    intro a
    calc δ a * t = (t * δ a * t⁻¹) * t := by rw [hδconj a]
      _ = t * δ a := by group
  have hzp : ∀ a : ↥K, (Subgroup.zpowers t).map (MulAut.conj (δ a)).toMonoidHom =
      Subgroup.zpowers t := by
    intro a
    have h1 : (MulAut.conj (δ a)).toMonoidHom t = t := by
      show MulAut.conj (δ a) t = t
      rw [MulAut.conj_apply, hδcomm a]
      group
    rw [MonoidHom.map_zpowers, h1]
  have hTmap : ∀ a : ↥K, T.map (δ a).toMonoidHom = T := by
    intro a
    have h := Asc81c.commSub_map_conj (Subgroup.zpowers t) (δ a)
    rw [hzp a] at h
    exact h.symm
  have hstab : ∀ a : ↥K, δ a ∈ stabSub T := by
    intro a
    rw [mem_stabSub]
    intro u
    constructor
    · intro hfu
      have h2 : δ a u ∈ T.map (δ a).toMonoidHom := by rw [hTmap a]; exact hfu
      obtain ⟨w, hw, hwu⟩ := Subgroup.mem_map.mp h2
      rwa [(δ a).injective hwu] at hw
    · intro hu
      have h2 : δ a u ∈ T.map (δ a).toMonoidHom := Subgroup.mem_map_of_mem _ hu
      rwa [hTmap a] at h2
  let δ'' : ↥K →* stabSub T :=
    { toFun := fun a => ⟨δ a, hstab a⟩
      map_one' := Subtype.ext (map_one δ)
      map_mul' := fun a b => Subtype.ext (map_mul δ a b) }
  let δ' : ↥K →* MulAut ↥T := (resHom T).comp δ''
  let X : Subgroup (MulAut ↥T) := δ'.range
  haveI : Group.IsPerfect ↥K := Group.isPerfect_def.mpr hK.2.2.1
  haveI : Group.IsPerfect ↥X := Group.IsPerfect.range δ'
  have hperf : ⁅X, X⁆ = X := Subgroup.commutator_eq_self
  have hT2 : ∀ u : ↥T, u ^ 2 = 1 := fun u =>
    Subtype.ext (by simpa [Subgroup.coe_pow] using hW (u : W))
  have hrkT3 : rk ↥(⊤ : Subgroup ↥T) ≤ 3 := by
    have h : rk ↥(⊤ : Subgroup ↥T) = rk ↥T := by
      unfold rk
      rw [Subgroup.card_top]
    rw [h]
    exact hrk
  by_cases hXbot : X = ⊥
  · left
    intro a ha u hu
    have hmem : δ' ⟨a, ha⟩ ∈ X := by
      change δ' ⟨a, ha⟩ ∈ δ'.range
      exact MonoidHom.mem_range.mpr ⟨⟨a, ha⟩, rfl⟩
    rw [hXbot] at hmem
    have hδ'a : δ' ⟨a, ha⟩ = 1 := by simpa using hmem
    have hcongr := congrArg (fun f : MulAut ↥T => ((f ⟨u, hu⟩ : ↥T) : W)) hδ'a
    simpa [δ, δ', δ'', MonoidHom.comp_apply, resHom_apply] using hcongr
  · right
    obtain ⟨hrk3top, hXtop⟩ := w16f_perfect_gl_three hT2 hrkT3 X hperf hXbot
    have hT3 : rk ↥T = 3 := by
      have h2 : rk ↥(⊤ : Subgroup ↥T) = rk ↥T := by
        unfold rk
        rw [Subgroup.card_top]
      rwa [h2] at hrk3top
    refine ⟨?_, ?_, ?_⟩
    · intro hall
      apply hXbot
      change δ'.range = ⊥
      rw [Subgroup.eq_bot_iff_forall]
      intro φ hφ
      obtain ⟨a, rfl⟩ := MonoidHom.mem_range.mp hφ
      ext u
      simpa [δ, δ', δ'', MonoidHom.comp_apply, resHom_apply]
        using hall (a : MulAut W) a.2 (u : W) u.2
    · exact hT3
    · have hcardT : Nat.card ↥T = 2 ^ 3 := by
        rw [card_eq_two_pow hW T, hT3]
      obtain ⟨e⟩ := CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary (p := 2)
        (W := ↥T) (fun a b => mul_comm a b) hT2 (n := 3) hcardT
      refine ⟨(CFSG.SectionRank.Ccomm.elemAutEquivGL e).toMonoidHom.comp δ', ?_⟩
      have hsurj : Function.Surjective δ' := by
        rw [← MonoidHom.range_eq_top]
        change X = ⊤
        exact hXtop
      intro y
      obtain ⟨x, hx⟩ := hsurj ((CFSG.SectionRank.Ccomm.elemAutEquivGL e).symm y)
      exact ⟨x, by
        rw [MonoidHom.comp_apply, hx]
        exact (CFSG.SectionRank.Ccomm.elemAutEquivGL e).apply_symm_apply y⟩

end CFSG.LocalAnalysis.WeakClosure81
