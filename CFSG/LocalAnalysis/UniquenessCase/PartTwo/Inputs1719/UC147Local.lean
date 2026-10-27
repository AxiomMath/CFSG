module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UC147LocalAb
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UC147LocalNonab

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open Subgroup CFSG.Open CFSG.LocalAnalysis.RankThreeUC CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

variable {G : Type} [Group G] [Finite G]

def secTorsion (V V₀ : Subgroup G) (q : ℕ) (hV₀V : V₀ ≤ V)
    (hVV₀ : V ≤ normalizer (V₀ : Set G))
    (hab : ∀ v ∈ V, ∀ w ∈ V, v * w * v⁻¹ * w⁻¹ ∈ V₀) : Subgroup G where
  carrier := {u : G | u ∈ V ∧ u ^ q ∈ V₀}
  one_mem' := ⟨V.one_mem, by simp⟩
  mul_mem' := by
    intro u w hu hw
    obtain ⟨huV, huq⟩ := hu
    obtain ⟨hwV, hwq⟩ := hw
    refine ⟨V.mul_mem huV hwV, ?_⟩
    have hKn : (V₀.subgroupOf V).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hV₀V).mpr hVV₀
    have hcomm : ∀ x y : (↥V ⧸ V₀.subgroupOf V), x * y = y * x := by
      intro x y
      obtain ⟨v, rfl⟩ := QuotientGroup.mk'_surjective (N := V₀.subgroupOf V) x
      obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective (N := V₀.subgroupOf V) y
      rw [← map_mul, ← map_mul]
      have hmem : (v * w) * (w * v)⁻¹ ∈ V₀.subgroupOf V := by
        have h := hab (v : G) v.2 (w : G) w.2
        simpa [Subgroup.mem_subgroupOf, mul_inv_rev, mul_assoc] using h
      have h1 : (QuotientGroup.mk' (V₀.subgroupOf V)) ((v * w) * (w * v)⁻¹) = 1 :=
        (QuotientGroup.eq_one_iff (N := V₀.subgroupOf V) _).mpr hmem
      rw [map_mul, map_inv] at h1
      exact mul_inv_eq_one.mp h1
    have hu' : (QuotientGroup.mk' (V₀.subgroupOf V)) ⟨u, huV⟩ ^ q = 1 := by
      rw [← map_pow]
      exact (QuotientGroup.eq_one_iff (N := V₀.subgroupOf V) _).mpr
        (by simpa [Subgroup.mem_subgroupOf] using huq)
    have hw' : (QuotientGroup.mk' (V₀.subgroupOf V)) ⟨w, hwV⟩ ^ q = 1 := by
      rw [← map_pow]
      exact (QuotientGroup.eq_one_iff (N := V₀.subgroupOf V) _).mpr
        (by simpa [Subgroup.mem_subgroupOf] using hwq)
    have hcomm' : Commute ((QuotientGroup.mk' (V₀.subgroupOf V)) ⟨u, huV⟩)
        ((QuotientGroup.mk' (V₀.subgroupOf V)) ⟨w, hwV⟩) := hcomm _ _
    have hprod : (QuotientGroup.mk' (V₀.subgroupOf V))
        ⟨u * w, V.mul_mem huV hwV⟩ ^ q = 1 := by
      have hsplit : (⟨u * w, V.mul_mem huV hwV⟩ : ↥V) = ⟨u, huV⟩ * ⟨w, hwV⟩ := rfl
      rw [hsplit, map_mul, hcomm'.mul_pow, hu', hw', mul_one]
    rw [← map_pow] at hprod
    have hmem : (⟨u * w, V.mul_mem huV hwV⟩ : ↥V) ^ q ∈ V₀.subgroupOf V :=
      (QuotientGroup.eq_one_iff (N := V₀.subgroupOf V) _).mp hprod
    simpa [Subgroup.mem_subgroupOf] using hmem
  inv_mem' := by
    intro u hu
    obtain ⟨huV, huq⟩ := hu
    exact ⟨V.inv_mem huV, by rw [inv_pow]; exact V₀.inv_mem huq⟩

omit [Finite G] in
theorem le_normalizer_secTorsion {V V₀ W : Subgroup G} {q : ℕ} (hV₀V : V₀ ≤ V)
    (hVV₀ : V ≤ normalizer (V₀ : Set G))
    (hab : ∀ v ∈ V, ∀ w ∈ V, v * w * v⁻¹ * w⁻¹ ∈ V₀)
    (hWV : W ≤ normalizer (V : Set G)) (hWV₀ : W ≤ normalizer (V₀ : Set G)) :
    W ≤ normalizer (secTorsion V V₀ q hV₀V hVV₀ hab : Set G) := by
  have hfwd : ∀ w ∈ W, ∀ u ∈ secTorsion V V₀ q hV₀V hVV₀ hab,
      w * u * w⁻¹ ∈ secTorsion V V₀ q hV₀V hVV₀ hab := by
    intro w hw u hu
    exact ⟨(Subgroup.mem_set_normalizer_iff.mp (hWV hw) u).mp hu.1, by
      rw [conj_pow]
      exact (Subgroup.mem_set_normalizer_iff.mp (hWV₀ hw) (u ^ q)).mp hu.2⟩
  intro w hw
  rw [Subgroup.mem_set_normalizer_iff]
  intro u
  constructor
  · exact hfwd w hw u
  · intro hu
    have h1 := hfwd w⁻¹ (W.inv_mem hw) (w * u * w⁻¹) hu
    simpa [mul_assoc] using h1

theorem secTorsion_ne_of_dvd_index {V V₀ : Subgroup G} {q : ℕ} (hV₀V : V₀ ≤ V)
    (hVV₀ : V ≤ normalizer (V₀ : Set G))
    (hab : ∀ v ∈ V, ∀ w ∈ V, v * w * v⁻¹ * w⁻¹ ∈ V₀) (hq : q.Prime)
    (hdvd : q ∣ (V₀.subgroupOf V).index) :
    secTorsion V V₀ q hV₀V hVV₀ hab ≠ V₀ := by
  classical
  have hfact : Fact q.Prime := ⟨hq⟩
  have hKn : (V₀.subgroupOf V).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hV₀V).mpr hVV₀
  intro hUV₀
  have hindex : q ∣ Nat.card (↥V ⧸ V₀.subgroupOf V) := by
    rw [← Subgroup.index_eq_card]
    exact hdvd
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' q hindex
  obtain ⟨y, hyx⟩ := QuotientGroup.mk'_surjective (N := V₀.subgroupOf V) x
  have hyK : y ∉ V₀.subgroupOf V := by
    intro hy
    have h1 : x = 1 := by
      rw [← hyx]
      exact (QuotientGroup.eq_one_iff (N := V₀.subgroupOf V) _).mpr hy
    rw [h1] at hx
    exact hq.ne_one (by rw [← hx]; exact orderOf_one)
  have hyU : (y : G) ∈ secTorsion V V₀ q hV₀V hVV₀ hab := by
    refine ⟨y.2, ?_⟩
    have h2 : (QuotientGroup.mk' (V₀.subgroupOf V)) (y ^ q) = 1 := by
      rw [map_pow, hyx, ← hx]
      exact pow_orderOf_eq_one x
    have hmem : y ^ q ∈ V₀.subgroupOf V :=
      (QuotientGroup.eq_one_iff (N := V₀.subgroupOf V) _).mp h2
    simpa [Subgroup.mem_subgroupOf] using hmem
  exact hyK (hUV₀ ▸ hyU)

theorem pow_mem_of_prime_dvd_index {V V₀ B R : Subgroup G} (hV₀V : V₀ ≤ V)
    (hVV₀ : V ≤ normalizer (V₀ : Set G)) (hBV : B ≤ normalizer (V : Set G))
    (hRV : R ≤ normalizer (V : Set G)) (hBV₀ : B ≤ normalizer (V₀ : Set G))
    (hRV₀ : R ≤ normalizer (V₀ : Set G))
    (hab : ∀ v ∈ V, ∀ w ∈ V, v * w * v⁻¹ * w⁻¹ ∈ V₀) {q : ℕ} (hq : q.Prime)
    (hdvd : q ∣ (V₀.subgroupOf V).index)
    (hmin : ∀ U : Subgroup G, V₀ ≤ U → U ≤ V → V ≤ normalizer (U : Set G) →
      B ≤ normalizer (U : Set G) → R ≤ normalizer (U : Set G) → U = V₀ ∨ U = V) :
    ∀ v ∈ V, v ^ q ∈ V₀ := by
  have hUne : secTorsion V V₀ q hV₀V hVV₀ hab ≠ V₀ :=
    secTorsion_ne_of_dvd_index hV₀V hVV₀ hab hq hdvd
  have hV₀U : V₀ ≤ secTorsion V V₀ q hV₀V hVV₀ hab := fun x hx =>
    ⟨hV₀V hx, by simpa using V₀.pow_mem hx q⟩
  have hUle : secTorsion V V₀ q hV₀V hVV₀ hab ≤ V := fun _ hu => hu.1
  rcases hmin (secTorsion V V₀ q hV₀V hVV₀ hab) hV₀U hUle
      (le_normalizer_secTorsion hV₀V hVV₀ hab Subgroup.le_normalizer hVV₀)
      (le_normalizer_secTorsion hV₀V hVV₀ hab hBV hBV₀)
      (le_normalizer_secTorsion hV₀V hVV₀ hab hRV hRV₀) with h | h
  · exact absurd h hUne
  · intro v hv
    have hvU : v ∈ secTorsion V V₀ q hV₀V hVV₀ hab := by rw [h]; exact hv
    exact hvU.2

omit [Finite G] in
theorem isPGroup_quotient_of_pow_mem {V V₀ E H : Subgroup G} [hKn : (V₀.subgroupOf H).Normal]
    (hVH : V ≤ H) (hEH : E ≤ H) (hH : H = V ⊔ E) (hHV : H ≤ normalizer (V : Set G))
    (hexp : ∀ v ∈ V, v ^ 7 ∈ V₀) (hE : IsPGroup 7 E) :
    IsPGroup 7 (↥H ⧸ V₀.subgroupOf H) := by
  classical
  have hfact7 : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hVn : (V.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hVH).mpr hHV
  let f := QuotientGroup.mk' (V₀.subgroupOf H)
  have hVp : IsPGroup 7 ↥((V.subgroupOf H).map f) := by
    rintro ⟨x, hx⟩
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
    refine ⟨1, ?_⟩
    have h1 : (x : ↥H ⧸ V₀.subgroupOf H) ^ 7 = 1 := by
      rw [← hyx, ← map_pow]
      exact (QuotientGroup.eq_one_iff (N := V₀.subgroupOf H) _).mpr (hexp (y : G) hy)
    simpa using h1
  have hEp : IsPGroup 7 ↥((E.subgroupOf H).map f) := (hE.comap_subtype (K := H)).map f
  have hsup : V.subgroupOf H ⊔ E.subgroupOf H = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hVH hEH, ← hH, Subgroup.subgroupOf_self]
  have hsup' : (V.subgroupOf H).map f ⊔ (E.subgroupOf H).map f = ⊤ := by
    rw [← Subgroup.map_sup, hsup,
      Subgroup.map_top_of_surjective f (QuotientGroup.mk'_surjective (N := V₀.subgroupOf H))]
  have hnorm : ((V.subgroupOf H).map f).Normal :=
    hVn.map f (QuotientGroup.mk'_surjective (N := V₀.subgroupOf H))
  have htop : IsPGroup 7 ↥((V.subgroupOf H).map f ⊔ (E.subgroupOf H).map f) :=
    IsPGroup.to_sup_of_normal_left hVp hEp
  intro g
  have hg : g ∈ ((V.subgroupOf H).map f ⊔ (E.subgroupOf H).map f) := by
    rw [hsup']
    simp
  obtain ⟨k, hk⟩ := htop ⟨g, hg⟩
  exact ⟨k, by simpa using hk⟩

namespace Ctx147

variable {D : Data G} {L : Fin 2 → Subgroup G} {n : Fin 2 → ℕ} {r p : ℕ} {A X B R : Subgroup G}

theorem le_M_of_section_seven (c : Ctx147 D L n r p A X B R)
    (hRi : ∀ i, R ⊓ L i ∈ uniqueSet D.M) {V V₀ : Subgroup G} (s : Sec147 D B R V V₀)
    (hexp : ∀ v ∈ V, v ^ 7 ∈ V₀) : V ≤ D.M := by
  classical
  have hfact7 : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  let E : Subgroup G := R ⊓ L 0
  let H : Subgroup G := V ⊔ E
  have hVH : V ≤ H := le_sup_left
  have hEH : E ≤ H := le_sup_right
  have hV₀H : V₀ ≤ H := s.hle.trans hVH
  have hHH : H ≤ normalizer (V₀ : Set G) := sup_le s.hVV₀ (inf_le_left.trans s.hRV₀)
  have hHV : H ≤ normalizer (V : Set G) :=
    sup_le Subgroup.le_normalizer (inf_le_left.trans s.hRV)
  have hEcard : Nat.card E = 7 := ((c.frame).2.2.1 0).1
  have hE7 : IsPGroup 7 E := IsPGroup.of_card (G := ↥E) (n := 1) (by rw [hEcard, pow_one])
  have hKn : (V₀.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hV₀H).mpr hHH
  have hQp : IsPGroup 7 (↥H ⧸ V₀.subgroupOf H) :=
    isPGroup_quotient_of_pow_mem (V := V) (V₀ := V₀) (E := E) (H := H) hVH hEH rfl hHV hexp hE7
  have hEp : IsPGroup 7 ↥(E.subgroupOf H) := hE7.comap_subtype
  obtain ⟨Y, hEY⟩ := hEp.exists_le_sylow
  have hsupY : V₀.subgroupOf H ⊔ (Y : Subgroup ↥H) = ⊤ := by
    rw [sup_comm]
    exact CFSG.section10_sylow_sup_normal_of_p_quotient_eq_top hQp Y
  have hYgM : Y.map H.subtype ≤ D.M := by
    have hYgp : IsPGroup 7 ↥(Y.map H.subtype) := Y.isPGroup'.map H.subtype
    have hEY' : E ≤ Y.map H.subtype := by
      intro x hx
      exact Subgroup.mem_map.mpr ⟨⟨x, hEH hx⟩, hEY hx, rfl⟩
    exact (le_and_normalizer_le_of_isPGroup D.maxLocal (hRi 0) hEY' hYgp).1
  have hVle : V ≤ V₀ ⊔ Y.map H.subtype := by
    have h1 : V.subgroupOf H ≤ V₀.subgroupOf H ⊔ (Y : Subgroup ↥H) := hsupY ▸ le_top
    have h2 := Subgroup.map_mono (f := H.subtype) h1
    rwa [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hVH,
      Subgroup.map_subgroupOf_eq_of_le hV₀H] at h2
  exact hVle.trans (sup_le s.hV₀M hYgM)

theorem le_M_of_section_abelian (c : Ctx147 D L n r p A X B R)
    (hsp3 : IsStronglyPEmbedded 3 D.M) (hRi : ∀ i, R ⊓ L i ∈ uniqueSet D.M)
    {V V₀ : Subgroup G} (s : Sec147 D B R V V₀) (hV₀ne : V₀ ≠ V)
    (hmin : ∀ U : Subgroup G, V₀ ≤ U → U ≤ V → V ≤ normalizer (U : Set G) →
      B ≤ normalizer (U : Set G) → R ≤ normalizer (U : Set G) → U = V₀ ∨ U = V)
    (hab : ∀ v ∈ V, ∀ w ∈ V, v * w * v⁻¹ * w⁻¹ ∈ V₀) : V ≤ D.M := by
  classical
  have hne_top : V₀.subgroupOf V ≠ ⊤ := by
    rw [Ne, Subgroup.subgroupOf_eq_top]
    exact fun h => hV₀ne (le_antisymm h s.hle).symm
  have hidx : 1 < (V₀.subgroupOf V).index := Subgroup.one_lt_index_of_ne_top hne_top
  obtain ⟨q, hq, hdvd⟩ := Nat.exists_prime_and_dvd (n := (V₀.subgroupOf V).index) (by omega)
  have hexp : ∀ v ∈ V, v ^ q ∈ V₀ :=
    pow_mem_of_prime_dvd_index s.hle s.hVV₀ s.hBV s.hRV s.hBV₀ s.hRV₀ hab hq hdvd hmin
  have hqV : q ∣ Nat.card V := hdvd.trans (Subgroup.index_dvd_card (H := V₀.subgroupOf V))
  have hq3 : q ≠ 3 := by
    rintro rfl
    have h1 : 3 = 1 := Nat.eq_one_of_dvd_coprimes s.hV (dvd_refl 3) hqV
    omega
  by_cases hq7 : q = 7
  · subst hq7
    exact le_M_of_section_seven c hRi s hexp
  · exact le_M_of_section_elemAbelian c hsp3 hRi s hq hq3 hq7 hab hexp

theorem le_M_of_coprime_three (c : Ctx147 D L n r p A X B R)
    (hsp3 : IsStronglyPEmbedded 3 D.M) (hRi : ∀ i, R ⊓ L i ∈ uniqueSet D.M)
    (hSz : CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.KFactSuzukiThreeFree)
    {V : Subgroup G} (hBV : B ≤ normalizer (V : Set G)) (hRV : R ≤ normalizer (V : Set G))
    (hV : Nat.Coprime 3 (Nat.card V)) : V ≤ D.M := by
  classical
  suffices key : ∀ m : ℕ, ∀ V : Subgroup G, Nat.card V = m →
      B ≤ normalizer (V : Set G) → R ≤ normalizer (V : Set G) →
      Nat.Coprime 3 (Nat.card V) → V ≤ D.M by
    exact key _ V rfl hBV hRV hV
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro V hcard hBV hRV hVcop
    by_cases hbot : V = ⊥
    · rw [hbot]
      exact bot_le
    have hfinSub : Finite (Subgroup G) :=
      Finite.of_injective (fun K : Subgroup G => (K : Set G)) SetLike.coe_injective
    let S : Set (Subgroup G) :=
      {U | U ≤ V ∧ U ≠ V ∧ V ≤ normalizer (U : Set G) ∧
        B ≤ normalizer (U : Set G) ∧ R ≤ normalizer (U : Set G)}
    have hbotn : ∀ W : Subgroup G, W ≤ normalizer (⊥ : Subgroup G) := fun W => by
      rw [Subgroup.normalizer_eq_top]
      exact le_top
    have hSne : S.Nonempty :=
      ⟨⊥, bot_le, fun h => hbot h.symm, hbotn V, hbotn B, hbotn R⟩
    obtain ⟨V₀, hV₀S, hmax⟩ := (Set.toFinite S).exists_maximal hSne
    obtain ⟨hV₀V, hV₀ne, hVV₀, hBV₀, hRV₀⟩ := hV₀S
    have hcardvd : Nat.card V₀ ∣ Nat.card V := by
      have hbridge : Nat.card (V₀.subgroupOf V) = Nat.card V₀ := by
        have h := Subgroup.card_subtype (V : Subgroup G) (V₀.subgroupOf V)
        rw [Subgroup.map_subgroupOf_eq_of_le hV₀V] at h
        exact h.symm
      rw [← Subgroup.index_mul_card (V₀.subgroupOf V), hbridge]
      exact dvd_mul_left _ _
    have hcardlt : Nat.card V₀ < m := by
      rw [← hcard]
      exact Subgroup.card_lt_of_lt (lt_of_le_of_ne hV₀V hV₀ne)
    have hV₀M : V₀ ≤ D.M := ih _ hcardlt V₀ rfl hBV₀ hRV₀ (hVcop.of_dvd_right hcardvd)
    have s : Sec147 D B R V V₀ := ⟨hBV, hRV, hVcop, hV₀V, hVV₀, hBV₀, hRV₀, hV₀M⟩
    have hmin : ∀ U : Subgroup G, V₀ ≤ U → U ≤ V → V ≤ normalizer (U : Set G) →
        B ≤ normalizer (U : Set G) → R ≤ normalizer (U : Set G) → U = V₀ ∨ U = V := by
      intro U hV₀U hUV hVU hBU hRU
      by_cases hUV' : U = V
      · exact Or.inr hUV'
      · exact Or.inl (le_antisymm (hmax ⟨hUV, hUV', hVU, hBU, hRU⟩ hV₀U) hV₀U)
    by_cases hab : ∀ v ∈ V, ∀ w ∈ V, v * w * v⁻¹ * w⁻¹ ∈ V₀
    · exact le_M_of_section_abelian c hsp3 hRi s hV₀ne hmin hab
    · push Not at hab
      exact le_M_of_section_nonabelian c hsp3 hRi hSz s hmin hab

end Ctx147

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
