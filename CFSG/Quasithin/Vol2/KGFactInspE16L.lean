module

public import CFSG.Quasithin.Vol2.KGFactInspE16Base
public import CFSG.Quasithin.Vol2.KGFactInspL2U3
public import CFSG.Quasithin.Vol2.KGFactL3EvenConf
public import CFSG.Quasithin.Vol2.KGFactInsp4316Props

public section

namespace CFSG.Quasithin.H13.KGInsp4316

open CFSG.Open hiding StatedSL StatedSp StatedClassicalModel StatedLieTag StatedProj StatedSU
  StatedScalars
open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.Quasithin.H13.KGL3Even CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.Quasithin.H13.Ch4.KGSL3 (uSub)
open scoped MatrixGroups

namespace E16Cfg

variable {X : Type} [Group X] [Finite X] {S R K : Subgroup X}

theorem core (h : E16Cfg S R K) : ∀ N : Subgroup X, N ≤ K →
    K ≤ Subgroup.normalizer (N : Set X) → IsPGroup 2 N → N ≤ R := fun _ hNK hKN hN2 =>
  h.eq_core ▸ CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hNK hKN hN2

theorem K_ne_bot (h : E16Cfg S R K) : K ≠ ⊥ := by
  intro hb
  obtain ⟨F, _, _, hF, χ, hχ, -⟩ := h.chi
  have h60 : Nat.card SL(2, F) = 60 := by
    rw [CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, Nat.card_eq_fintype_card, hF]
    norm_num
  have hK : 60 ∣ Nat.card ↥K := h60 ▸ Subgroup.card_dvd_of_surjective hχ
  rw [hb, Subgroup.card_bot] at hK
  norm_num at hK

theorem false_of_psl3_two (h : E16Cfg S R K) {e : ℕ} (he : e ≠ 2)
    (hm : StatedClassicalModel ↥S .PSL 3 2 e) : False := by
  obtain ⟨-, F, _, _, hF, ⟨e₁⟩⟩ := hm
  have : Fintype F := Fintype.ofFinite F
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := e)
    (by rw [← Nat.card_eq_fintype_card]; exact hF)
  let φ : ↥S ≃* projectiveSL 3 F :=
    e₁.trans (CFSG.QuasithinUnique.Setup.X7a.statedSLEquivProjectiveSL 3 F)
  have hc₁ := (lconf_subgroupOf h.R_le_S h.le h.le_normalizer h.normalizer_le h.core).map φ
  have hR₁2 : IsPGroup 2 ((R.subgroupOf S).map φ.toMonoidHom) :=
    (h.isPGroup.comap_of_injective S.subtype S.subtype_injective).map _
  obtain ⟨g, hg⟩ := exists_conj_le hR₁2
  have hc₂ := hc₁.map (MulAut.conj g)
  set R₂ := ((R.subgroupOf S).map φ.toMonoidHom).map (MulAut.conj g).toMonoidHom with hR₂
  set K₂ := ((K.subgroupOf S).map φ.toMonoidHom).map (MulAut.conj g).toMonoidHom with hK₂
  obtain ⟨hc₀, hmapR, hmapK⟩ := lconf_lift hc₂ hg
  obtain ⟨hcard, hsqT, hcommT⟩ := lift_props (R := R₂)
  set R₀ := R₂.comap (proj 3 F) ⊓ unitriangular 3 F with hR₀
  have hR₂card : Nat.card R₂ = 16 := by
    rw [hR₂, Subgroup.card_map_of_injective (MulAut.conj g).injective,
      Subgroup.card_map_of_injective φ.injective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.R_le_S).toEquiv, h.card]
    norm_num
  have hR₀card : Nat.card R₀ = 16 := by rw [hcard, hmapR, hR₂card]
  have hsqR : ∀ r ∈ R, r * r = 1 := fun r hr => by rw [← sq]; exact h.elem.2 r hr
  have hcommR : ∀ r ∈ R, ∀ s ∈ R, r * s = s * r := by
    have := h.elem.1
    exact fun r hr s hs => setLike_mul_comm hr hs
  have hsq₂ : ∀ r ∈ R₂, r * r = 1 := by
    rintro _ ⟨_, ⟨r, hr, rfl⟩, rfl⟩
    rw [← map_mul, ← map_mul,
      show r * r = 1 from Subtype.ext (hsqR _ (Subgroup.mem_subgroupOf.mp hr)), map_one, map_one]
  have hcomm₂ : ∀ r ∈ R₂, ∀ s ∈ R₂, r * s = s * r := by
    rintro _ ⟨_, ⟨r, hr, rfl⟩, rfl⟩ _ ⟨_, ⟨s, hs, rfl⟩, rfl⟩
    rw [← map_mul, ← map_mul, ← map_mul, ← map_mul,
      show r * s = s * r from Subtype.ext (hcommR _ (Subgroup.mem_subgroupOf.mp hr) _
        (Subgroup.mem_subgroupOf.mp hs))]
  have hR₀1 : R₀ ≠ ⊥ := by
    intro hb
    rw [hb, Subgroup.card_bot] at hR₀card
    norm_num at hR₀card
  have hq : ∀ H : Subgroup (Matrix.SpecialLinearGroup (Fin 3) F), H = uSub →
      Nat.card H = 16 → False := by
    intro H hH hH16
    rw [hH, card_uSub, hF, ← pow_mul] at hH16
    have : e * 2 = 4 := Nat.pow_right_injective le_rfl (hH16.trans (by norm_num))
    omega
  rcases unitri_case hc₀ inf_le_right hR₀1 (hsqT hsq₂) (hcommT hcomm₂) with h1 | h1 | h1
  · exact hq _ h1 hR₀card
  · refine hq _ h1 ?_
    rw [Subgroup.card_map_of_injective theta.injective, hR₀card]
  · have h2 : Comm2 K₂ := hmapK ▸ h1.map (proj 3 F)
    have h3 : Comm2 (K.subgroupOf S) :=
      Comm2.of_map φ (Comm2.of_map (MulAut.conj g) h2)
    have h4 : Comm2 K := by
      have := h3.map S.subtype
      rwa [Subgroup.map_subgroupOf_eq_of_le h.le] at this
    exact not_comm2_of_perfect h.perfect h.K_ne_bot h4

end E16Cfg

theorem insp4316E16L_holds : Insp4316E16L := by
  intro X _ _ S R K hN hsimp hnc hlist hC F _ _ hF hle hperf hKN hNK hchi hL hcore helem hcard _
  have h : E16Cfg S R K := ⟨hN, hsimp, hnc, hlist, hC, hle, hperf, hKN, hNK,
    ⟨F, inferInstance, inferInstance, hF, hchi⟩, hcore, helem, hcard⟩
  obtain ⟨s, q, -, p, e, hp, -, rfl, hm⟩ := hL
  by_cases hp2 : p = 2
  · subst hp2
    cases s
    · exfalso
      have hm' : StatedClassicalModel ↥S .PSU 3 2 e := hm
      obtain ⟨-, he1, -, hne⟩ := hm'.1
      have he2 : 2 ≤ e := by
        by_contra hlt
        have : e = 1 := by omega
        subst this
        exact hne rfl
      exact h.cfg.false_of_psu3_two h.R_le_S he2 hm'
    · have hm' : StatedClassicalModel ↥S .PSL 3 2 e := hm
      by_cases he : e = 2
      · subst he
        exact Or.inl hm'
      · exact (h.false_of_psl3_two he hm').elim
  · exfalso
    cases s
    · exact h.false_of_pRank_two_le (pRank_two_le_two_of_psu3_odd hp hp2 hm)
    · exact h.false_of_pRank_two_le (pRank_two_le_two_of_psl3_odd hp hp2 hm)

end CFSG.Quasithin.H13.KGInsp4316
