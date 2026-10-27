module

public import CFSG.RankThree.PartTwo.Sec12.Item125NonCentralTools
public import CFSG.RankThree.PartTwo.KFacts.KS12ClassSL
public import CFSG.RankThree.PartTwo.KFacts.KS12MovesM22
public import CFSG.RankThree.PartTwo.Sec4.Item45Closed
import CFSG.GroupTheory.ABGLocalTools.CoreLemmas
import CFSG.RankThree.PartTwo.Sec13.Item13Theta
public import CFSG.RankThree.PartTwo.Sec12.Item128Bar125

public section

namespace CFSG.RankThree.PartTwo.Sec12.Gap125NonCentralBar

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.ABGLocalTools (IsSylowOf)

variable {G : Type} [Group G] [Finite G]

theorem exists_mem_normalizer_not_mem {R M : Subgroup G} (hR : IsPGroup 3 R) (hMR : M ≤ R)
    (hne : M ≠ R) : ∃ r ∈ R, r ∉ M ∧ r ∈ Subgroup.normalizer (M : Set G) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hnil : Group.IsNilpotent R := hR.isNilpotent
  have hcond := Group.normalizerCondition_of_isNilpotent (G := R)
  set M' := M.subgroupOf R with hM'
  have hlt : M' < ⊤ := by
    refine lt_top_iff_ne_top.mpr fun htop => hne (le_antisymm hMR fun x hx => ?_)
    have h1 : (⟨x, hx⟩ : R) ∈ M' := by
      rw [htop]
      exact Subgroup.mem_top _
    exact h1
  obtain ⟨r, hrN, hrM⟩ := IsConcreteLE.exists_of_lt (hcond M' hlt)
  refine ⟨r, r.2, hrM, Subgroup.mem_normalizer_fintype fun m hm => ?_⟩
  have h1 : (⟨m, hMR hm⟩ : R) ∈ M' := hm
  exact (Subgroup.mem_normalizer_iff.mp hrN _).mp h1

theorem exists_sylow (h45 : Sec4.Item4_5) (hK2 : KFacts.KS12NormalizerMoves)
    (hCT : KFacts.KS12ClassT) {A L : Subgroup G} {c : G} (h : Sec12StdBar G A c L)
    (hty : Sec4.IsSLThreePi (L ⧸ aschbacherSolvableCore 3 L) ∨
      Sec4.IsTripleCover (L ⧸ aschbacherSolvableCore 3 L) (alternatingGroup (Fin 6)) ∨
      Sec4.IsTripleCover (L ⧸ aschbacherSolvableCore 3 L) (alternatingGroup (Fin 7)) ∨
      Sec4.IsTripleCover (L ⧸ aschbacherSolvableCore 3 L) CFSG.Blueprint.NativeSporadic.M22)
    {E : Subgroup G} (hE : Late.IsE27 E) (hcE : c ∈ E)
    (hB9 : Nat.card (E ⊓ Sec4.thetaQuotCentralizer L : Subgroup G) = 9)
    (hEL9 : Nat.card (E ⊓ L : Subgroup G) = 9)
    (hN : ¬ Subgroup.normalizer (E : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G)) :
    ∃ P : Subgroup G, IsSylowOf 3 P
        (Subgroup.normalizer (E : Set G) ⊓ Subgroup.normalizer (Subgroup.zpowers c : Set G)) ∧
      ¬ E ⊓ Sec4.thetaQuotCentralizer L ≤ (Subgroup.center P).map P.subtype := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hL := h.mem_thetaComponentsAt
  have hX := isQuasisimple_thetaQuot_of_mem hL
  have hZ : Nat.card (Subgroup.center (L ⧸ aschbacherSolvableCore 3 L)) = 3 := by
    rcases hty with hSL | hA6 | hA7 | hM22
    · exact card_center_eq_three_of_isSLThreePi hSL
    · exact hA6.1
    · exact hA7.1
    · exact hM22.1
  have hperf : commutator (L ⧸ aschbacherSolvableCore 3 L) = ⊤ := by
    have h1 := hX.1
    rwa [Group.isPerfect_def] at h1
  have hev := KFacts.two_dvd_card_of_item122_type hty
  have hLc : L ≤ Subgroup.centralizer ({c} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt hL
  have hcommE : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hE.1.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hexpE : ∀ x ∈ E, x ^ 3 = 1 := hE.1.2
  set T := E ⊓ L with hTdef
  set BE := E ⊓ Sec4.thetaQuotCentralizer L with hBEdef
  have hTe : CFSG.Assembly.IsElemAbelian 3 T :=
    ⟨⟨⟨fun a b => Subtype.ext (hcommE _ a.2.1 _ b.2.1)⟩⟩, fun x hx => hexpE x hx.1⟩
  have hBEe : CFSG.Assembly.IsElemAbelian 3 BE :=
    ⟨⟨⟨fun a b => Subtype.ext (hcommE _ a.2.1 _ b.2.1)⟩⟩, fun x hx => hexpE x hx.1⟩
  have hT3 : IsPGroup 3 T := fun x => ⟨1, Subtype.ext (by simpa using hTe.2 x x.2)⟩
  have hBE3 : IsPGroup 3 BE := fun x => ⟨1, Subtype.ext (by simpa using hBEe.2 x x.2)⟩
  have hcT : c ∈ T := ⟨hcE, h.mem_L⟩
  have hEsup : BE ⊔ T = E := sup_eq_of_card_inf_nine hE hZ hB9 hEL9
  have hCTL : ∀ σ : MulAut (L ⧸ aschbacherSolvableCore 3 L), (∃ k : ℕ, σ ^ 3 ^ k = 1) →
      ∀ Tb : Subgroup (L ⧸ aschbacherSolvableCore 3 L), CFSG.Assembly.IsElemAbelian 3 Tb →
        Nat.card Tb = 9 → Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) ≤ Tb →
          ∃ x : L ⧸ aschbacherSolvableCore 3 L,
            Tb.map σ.toMonoidHom = Tb.map (MulAut.conj x).toMonoidHom :=
    fun σ hσ Tb hTbe hTb9 hZT => hCT _ hX hty σ hσ Tb hTbe hTb9 hZT
  obtain ⟨y, ⟨k, hyk⟩, hyN, hyH, hyB, b, hb, hyb⟩ := exists_moving h45 h
  set B₀ := A ⊓ Sec4.thetaQuotCentralizer L with hB₀def
  have hcommA : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (h.isE27.1.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hB₀3 : IsPGroup 3 B₀ := fun x => ⟨1, Subtype.ext (by simpa using h.isE27.1.2 x x.2.1)⟩
  obtain ⟨w, hwL, hw⟩ := exists_conj_commute hB₀3 inf_le_right (inf_le_right : T ≤ L) hT3
  have hwN : w ∈ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer hwL
  have hwH : w ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G) :=
    Sec13.le_normalizer_zpowers_of_mem hL hwL
  have hwc : w * c * w⁻¹ = c := by
    rw [(Subgroup.mem_centralizer_singleton_iff.mp (hLc hwL)), mul_inv_cancel_right]
  set B := B₀.map (MulAut.conj w).toMonoidHom with hBdef
  have hBe : CFSG.Assembly.IsElemAbelian 3 B := by
    refine ⟨⟨⟨fun u v => ?_⟩⟩, ?_⟩
    · obtain ⟨_, u', hu', rfl⟩ := u
      obtain ⟨_, v', hv', rfl⟩ := v
      apply Subtype.ext
      change w * u' * w⁻¹ * (w * v' * w⁻¹) = w * v' * w⁻¹ * (w * u' * w⁻¹)
      have := hcommA u' hu'.1 v' hv'.1
      calc w * u' * w⁻¹ * (w * v' * w⁻¹) = w * (u' * v') * w⁻¹ := by group
        _ = w * (v' * u') * w⁻¹ := by rw [this]
        _ = w * v' * w⁻¹ * (w * u' * w⁻¹) := by group
    · rintro _ ⟨u', hu', rfl⟩
      change (w * u' * w⁻¹) ^ 3 = 1
      rw [conj_pow, h.isE27.1.2 u' hu'.1, mul_one, mul_inv_cancel]
  have hB9' : Nat.card B = 9 := by
    rw [hBdef, Subgroup.card_map_of_injective (MulAut.conj w).injective, h.card_B]
  have hcB : c ∈ B :=
    ⟨c, ⟨h.mem_A, mem_thetaQuotCentralizer_of_central h.mem_L hLc⟩, by
      change w * c * w⁻¹ = c
      exact hwc⟩
  have hBC : B ≤ Sec4.thetaQuotCentralizer L := by
    rintro _ ⟨u', hu', rfl⟩
    exact conj_mem_thetaQuotCentralizer hwN hu'.2
  have hBT : ∀ b' ∈ B, ∀ t ∈ T, b' * t = t * b' := by
    rintro _ ⟨u', hu', rfl⟩ t ht
    exact hw u' hu' t ht
  have hB3 : IsPGroup 3 B := fun x => ⟨1, Subtype.ext (by simpa using hBe.2 x x.2)⟩
  set y' := w * y * w⁻¹ with hy'def
  have hy'3 : ∃ k : ℕ, y' ^ 3 ^ k = 1 := ⟨k, by rw [hy'def, conj_pow, hyk, mul_one,
    mul_inv_cancel]⟩
  have hy'N : y' ∈ Subgroup.normalizer (L : Set G) := mul_mem (mul_mem hwN hyN) (inv_mem hwN)
  have hy'H : y' ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G) :=
    mul_mem (mul_mem hwH hyH) (inv_mem hwH)
  have hy'B : y' ∈ Subgroup.normalizer (B : Set G) := by
    refine Subgroup.mem_normalizer_fintype fun x hx => ?_
    obtain ⟨u', hu', rfl⟩ := hx
    refine ⟨y * u' * y⁻¹, (Subgroup.mem_normalizer_iff.mp hyB u').mp hu', ?_⟩
    change w * (y * u' * y⁻¹) * w⁻¹ = y' * (w * u' * w⁻¹) * y'⁻¹
    rw [hy'def]
    group
  have hb' : w * b * w⁻¹ ∈ B := ⟨b, hb, rfl⟩
  have hy'b : y' * (w * b * w⁻¹) * y'⁻¹ ≠ w * b * w⁻¹ := by
    intro he
    apply hyb
    have e : y' * (w * b * w⁻¹) * y'⁻¹ = w * (y * b * y⁻¹) * w⁻¹ := by rw [hy'def]; group
    rw [e] at he
    have := congrArg (fun x => w⁻¹ * x * w) he
    simpa [mul_assoc] using this
  have hA' := sec12StdBar_sup h hZ hCTL hBe hB9' hcB hBC hBT hTe hEL9 inf_le_right hcT hy'3 hy'N
    hy'H hy'B hb' hy'b
  have hNA' := normalizer_le_of_sec12StdBar_of_list h45 hK2 hA' hty
  set D := Sec4.thetaQuotCentralizer L ⊓ Subgroup.centralizer (T : Set G) with hDdef
  have hBED : BE ≤ D := le_inf inf_le_right fun x hx =>
    Subgroup.mem_centralizer_iff.mpr fun t ht => hcommE t ht.1 x hx.1
  have hBD : B ≤ D := le_inf hBC fun x hx =>
    Subgroup.mem_centralizer_iff.mpr fun t ht => (hBT x hx t ht).symm
  have hrank : ∀ x ∈ D, x ∈ Subgroup.centralizer (BE : Set G) → x ^ 3 = 1 → x ∈ BE := by
    intro x hxD hxc hx3
    by_contra hxBE
    have hx1 : x ≠ 1 := fun h1 => hxBE (h1 ▸ one_mem _)
    have hxo : orderOf x = 3 := orderOf_eq_prime hx3 hx1
    obtain ⟨hcard, hc, he⟩ := card_sup_zpowers_of_disjoint hxc hBEe.1 hBEe.2 hxo
      (inf_zpowers_eq_bot_of_not_mem hxo hxBE)
    exact false_of_E27_le_thetaQuotCentralizer h.partTwoF_eq hperf hZ hev ⟨hc, he⟩
      (by rw [hcard, hB9]) (sup_le inf_le_right (Subgroup.zpowers_le.mpr hxD.1))
  obtain ⟨R, hR, hBER⟩ := exists_isSylowOf_le hBED hBE3
  by_cases hmove : ∃ r ∈ R, r ∈ Subgroup.normalizer (BE : Set G) ∧ ∃ b₁ ∈ BE, r * b₁ * r⁻¹ ≠ b₁
  ·
    obtain ⟨r, hrR, hrN, b₁, hb₁, hrb⟩ := hmove
    have hrD : r ∈ D := hR.le hrR
    have hrT : ∀ t ∈ T, r * t * r⁻¹ = t := fun t ht => by
      rw [← Subgroup.mem_centralizer_iff.mp hrD.2 t ht, mul_inv_cancel_right]
    have hrTN : r ∈ Subgroup.normalizer (T : Set G) :=
      Subgroup.mem_normalizer_fintype fun t ht => by rw [hrT t ht]; exact ht
    have hrE : r ∈ Subgroup.normalizer (E : Set G) := by
      have h1 := Subgroup.mem_normalizer_iff_map_conj_eq.mp hrN
      have h2 := Subgroup.mem_normalizer_iff_map_conj_eq.mp hrTN
      rw [Subgroup.mem_normalizer_iff_map_conj_eq, ← hEsup, Subgroup.map_sup, h1, h2]
    have hrH : r ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G) := by
      refine mem_normalizer_zpowers_of_commute ?_
      have h1 := hrT c hcT
      calc r * c = (r * c * r⁻¹) * r := by group
        _ = c * r := by rw [h1]
    have hr3 : IsPGroup 3 (Subgroup.zpowers r) :=
      hR.isPGroup.to_le (Subgroup.zpowers_le.mpr hrR)
    obtain ⟨P, hP, hrP⟩ := exists_isSylowOf_le
      (Subgroup.zpowers_le.mpr (Subgroup.mem_inf.mpr ⟨hrE, hrH⟩)) hr3
    refine ⟨P, hP, fun hle => hrb ?_⟩
    obtain ⟨zb, hzb, hzbe⟩ := hle hb₁
    have hc := Subgroup.mem_center_iff.mp hzb ⟨r, hrP (Subgroup.mem_zpowers r)⟩
    have h1 : r * b₁ = b₁ * r := by
      have := congrArg Subtype.val hc
      simp only [Subgroup.coe_mul] at this
      rw [← hzbe]
      exact this
    rw [h1, mul_inv_cancel_right]
  ·
    push Not at hmove
    exfalso
    apply hN
    have hRN : R ≤ Subgroup.normalizer (BE : Set G) := by
      by_contra hcon
      set N₀ := R ⊓ Subgroup.normalizer (BE : Set G) with hN₀
      have hne : N₀ ≠ R := fun heq => hcon (by rw [← heq]; exact inf_le_right)
      obtain ⟨r, hrR, hrN₀, hrnorm⟩ :=
        exists_mem_normalizer_not_mem hR.isPGroup inf_le_left hne
      apply hrN₀
      refine ⟨hrR, Subgroup.mem_normalizer_fintype fun b₂ hb₂ => ?_⟩
      have hbN₀ : b₂ ∈ N₀ := ⟨hBER hb₂, Subgroup.le_normalizer hb₂⟩
      have h1 : r * b₂ * r⁻¹ ∈ N₀ := (Subgroup.mem_normalizer_iff.mp hrnorm b₂).mp hbN₀
      refine hrank _ (hR.le h1.1) (Subgroup.mem_centralizer_iff.mpr fun b' hb' => ?_) ?_
      · have h2 := hmove _ h1.1 h1.2 b' hb'
        calc b' * (r * b₂ * r⁻¹) = (r * b₂ * r⁻¹) * b' * (r * b₂ * r⁻¹)⁻¹ *
              (r * b₂ * r⁻¹) := by rw [h2]
          _ = (r * b₂ * r⁻¹) * b' := by group
      · rw [conj_pow, hBEe.2 b₂ hb₂, mul_one, mul_inv_cancel]
    have h3R : ∀ x ∈ R, x ^ 3 = 1 → x ∈ BE := fun x hx hx3 =>
      hrank x (hR.le hx) (Subgroup.mem_centralizer_iff.mpr fun b' hb' => by
        have h2 := hmove x hx (hRN hx) b' hb'
        calc b' * x = x * b' * x⁻¹ * x := by rw [h2]
          _ = x * b' := by group) hx3
    obtain ⟨R', hR', hBR'⟩ := exists_isSylowOf_le hBD hB3
    obtain ⟨d, hdD, hd⟩ := CFSG.ABGLocalTools.IsSylowOf.exists_mem_conj hR hR'
    have hBBE : ∀ x ∈ B, d⁻¹ * x * d ∈ BE := fun x hx => h3R _ ((hd x).mp (hBR' hx)) (by
      have h0 := conj_pow (a := d⁻¹) (b := x) (i := 3)
      rw [inv_inv] at h0
      rw [h0, hBe.2 x hx, mul_one, inv_mul_cancel])
    have hdT : ∀ t ∈ T, d * t * d⁻¹ = t := fun t ht => by
      rw [← Subgroup.mem_centralizer_iff.mp hdD.2 t ht, mul_inv_cancel_right]
    have hS : B ⊔ T = E.map (MulAut.conj d).toMonoidHom := by
      refine Subgroup.eq_of_le_of_card_ge (sup_le ?_ ?_) ?_
      · intro x hx
        refine ⟨d⁻¹ * x * d, (hBBE x hx).1, ?_⟩
        change d * (d⁻¹ * x * d) * d⁻¹ = x
        group
      · intro t ht
        exact ⟨t, ht.1, hdT t ht⟩
      · rw [Subgroup.card_map_of_injective (MulAut.conj d).injective, hE.2, hA'.isE27.2]
    have hdH : d ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G) := by
      refine mem_normalizer_zpowers_of_commute ?_
      have h1 := hdT c hcT
      calc d * c = (d * c * d⁻¹) * d := by group
        _ = c * d := by rw [h1]
    intro g hg
    have h1 : d * g * d⁻¹ ∈ Subgroup.normalizer ((B ⊔ T : Subgroup G) : Set G) := by
      rw [hS]
      refine Subgroup.mem_normalizer_fintype fun x hx => ?_
      obtain ⟨e, he, rfl⟩ := hx
      refine ⟨g * e * g⁻¹, (Subgroup.mem_normalizer_iff.mp hg e).mp he, ?_⟩
      change d * (g * e * g⁻¹) * d⁻¹ = d * g * d⁻¹ * (d * e * d⁻¹) * (d * g * d⁻¹)⁻¹
      group
    have h2 := hNA' h1
    have e : g = d⁻¹ * (d * g * d⁻¹) * d := by group
    rw [e]
    exact mul_mem (mul_mem (inv_mem hdH) h2) hdH

end CFSG.RankThree.PartTwo.Sec12.Gap125NonCentralBar

namespace CFSG.RankThree.PartTwo.Sec12

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

theorem gap125NonCentralBar_of (h45 : Sec4.Item4_5) (hK2 : KFacts.KS12NormalizerMoves)
    (hCT : KFacts.KS12ClassT) : Gap125NonCentralBar := by
  intro G _ _ A c L h hty E hE _ hcE hB9 hEL9 hN
  exact Gap125NonCentralBar.exists_sylow h45 hK2 hCT h hty hE hcE hB9 hEL9 hN

section Unconditional

theorem gap125NonCentralBar
    : Gap125NonCentralBar :=
  gap125NonCentralBar_of Sec4.rank3II_4_5 KFacts.ks12NormalizerMoves KFacts.ks12ClassT

end Unconditional

end CFSG.RankThree.PartTwo.Sec12
