module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148HA5Data
public import CFSG.RankThree.PartTwo.Sec4.Ronan148RH1Mathieu
public import CFSG.RankThree.PartTwo.Sec21.Item22Res4ProofNarrow
public import CFSG.RankThree.PartTwo.KFacts.KS14MathieuAutCore
public import CFSG.RankThree.PartTwo.Sec14.Item148PtResProofA6Aut
public import CFSG.LargeExtraspecial.S12Seven
public import CFSG.RankThree.PartTwo.Sec14.Ronan148HCensusE16Alt
public import CFSG.RankThree.PartTwo.Sec14.Ronan148HCensusSpor

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148H

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.LocalRank CFSG.GH74.GLS
open CFSG.RankThree.PartTwo.Sec4
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)
open CFSG.Assembly.LowTwoRank (StatedSL StatedSU)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

theorem a5Row_of_cardRow {Φ : (T : Type) → [Group T] → Prop} (h : CardRow Φ) : A5Row Φ :=
  fun T _ _ hd hΦ => h T hΦ hd.dvd

theorem exists_E16_of_isExtOf {T S : Type} [Group T] [Group S] [Finite T]
    (hext : IsExtOf T S (Multiplicative (ZMod 3)))
    (hE : ∃ E : Subgroup S, CFSG.Assembly.IsElemAbelian 2 E ∧ Nat.card E = 16) :
    ∃ E : Subgroup T, CFSG.Assembly.IsElemAbelian 2 E ∧ Nat.card E = 16 := by
  obtain ⟨K, hKn, ⟨eK⟩, ⟨eS⟩⟩ := hext
  obtain ⟨E, hE, hE16⟩ := hE
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK3 : Nat.card K = 3 := by
    rw [Nat.card_congr eK.toEquiv, Nat.card_eq_fintype_card, Fintype.card_multiplicative,
      ZMod.card]
  let ψ : T →* S := eS.toMonoidHom.comp (QuotientGroup.mk' K)
  have hψs : Function.Surjective ψ := eS.surjective.comp (QuotientGroup.mk'_surjective K)
  have hker : ∀ l : T, ψ l = 1 → l ∈ K := by
    intro l hl
    have h1 : (QuotientGroup.mk' K) l = 1 := eS.injective (by rw [map_one]; exact hl)
    exact (QuotientGroup.eq_one_iff _).mp h1
  have : Finite S := Finite.of_surjective ψ hψs
  let W := E.comap ψ
  have hWcard : Nat.card W = 48 := by
    have h1 := Subgroup.card_mul_index W
    have h2 := Subgroup.card_mul_index E
    have h3 : W.index = E.index := Subgroup.index_comap_of_surjective E hψs
    have h4 : Nat.card T = Nat.card S * 3 := by
      rw [← hK3, ← Nat.card_congr eS.toEquiv]
      exact Subgroup.card_eq_card_quotient_mul_card_subgroup K
    rw [h4, ← h2, hE16, h3] at h1
    have hpos : 0 < E.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
    exact Nat.eq_of_mul_eq_mul_right hpos (by rw [h1]; ring)
  obtain ⟨T2⟩ : Nonempty (Sylow 2 W) := inferInstance
  have hT2card : Nat.card T2 = 16 := by
    rw [Sylow.card_eq_multiplicity, hWcard]
    have : (48 : ℕ).factorization 2 = 4 := by
      rw [show (48 : ℕ) = 2 ^ 4 * 3 by norm_num, Nat.factorization_mul (by norm_num) (by norm_num),
        Finsupp.add_apply, Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
        Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
    rw [this]
    norm_num
  let g : ↥(T2 : Subgroup W) →* S := ψ.comp (W.subtype.comp (T2 : Subgroup W).subtype)
  have hginj : Function.Injective g := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hxK : ((x : W) : T) ∈ K := hker _ hx
    obtain ⟨n, hn⟩ := (IsPGroup.iff_orderOf.mp T2.isPGroup') x
    have h1 : orderOf ((x : W) : T) = 2 ^ n := by
      rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hn]
    have h2 : orderOf ((x : W) : T) ∣ 3 := hK3 ▸ Subgroup.orderOf_dvd_natCard K hxK
    rw [h1] at h2
    have hn0 : n = 0 := by
      by_contra hn0
      have : 2 ∣ 3 := (dvd_pow_self 2 hn0).trans h2
      omega
    rw [hn0, pow_zero, orderOf_eq_one_iff] at hn
    exact hn
  have hgE : ∀ t : ↥(T2 : Subgroup W), g t ∈ E := fun t => (t : W).2
  have hcommT : ∀ t t' : ↥(T2 : Subgroup W), t * t' = t' * t := by
    intro t t'
    apply hginj
    rw [map_mul, map_mul]
    exact congrArg Subtype.val (hE.1.is_comm.comm ⟨g t, hgE t⟩ ⟨g t', hgE t'⟩)
  have hsqT : ∀ t : ↥(T2 : Subgroup W), t ^ 2 = 1 := by
    intro t
    apply hginj
    rw [map_pow, map_one]
    exact hE.2 _ (hgE t)
  let f : ↥(T2 : Subgroup W) →* T := W.subtype.comp (T2 : Subgroup W).subtype
  have hfinj : Function.Injective f := W.subtype_injective.comp (T2 : Subgroup W).subtype_injective
  refine ⟨f.range, ⟨⟨⟨fun a b => ?_⟩⟩, fun a ha => ?_⟩, ?_⟩
  · obtain ⟨t, ht⟩ := a.2
    obtain ⟨t', ht'⟩ := b.2
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← ht, ← ht', ← map_mul, ← map_mul, hcommT]
  · obtain ⟨t, rfl⟩ := ha
    rw [← map_pow, hsqT, map_one]
  · rw [← hT2card]
    exact Nat.card_congr (MonoidHom.ofInjective hfinj).toEquiv.symm

namespace A5Data

variable {T : Type} [Group T] [Finite T]

theorem false_of_iso_not_five (h : A5Data T) {S : Type} [Group S] (φ : T ≃* S)
    (h5 : ¬ 5 ∣ Nat.card S) : False :=
  h.false_of_not_five (by rwa [Nat.card_congr φ.toEquiv])

theorem false_of_iso_card_dvd_sixty (h : A5Data T) {S : Type} [Group S] (φ : T ≃* S)
    (h60 : Nat.card S ∣ 60) : False :=
  h.false_of_card_dvd_sixty (by rwa [Nat.card_congr φ.toEquiv])

theorem false_of_iso_E16 (h : A5Data T) {S : Type} [Group S] (φ : T ≃* S)
    (hE : ∃ E : Subgroup S, CFSG.Assembly.IsElemAbelian 2 E ∧ Nat.card E = 16) : False := by
  obtain ⟨E, hE, h16⟩ := hE
  set f : S →* T := φ.symm.toMonoidHom with hf
  have hinj : Function.Injective f := φ.symm.injective
  refine h.false_of_E16 (E := E.map f) ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩ ?_
  · obtain ⟨u, hu, hux⟩ := Subgroup.mem_map.mp x.2
    obtain ⟨v, hv, hvy⟩ := Subgroup.mem_map.mp y.2
    apply Subtype.ext
    change (x : T) * y = y * x
    rw [← hux, ← hvy, ← map_mul, ← map_mul]
    exact congrArg f (congrArg Subtype.val (hE.1.is_comm.comm (⟨u, hu⟩ : E) ⟨v, hv⟩))
  · obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hx
    rw [← map_pow, hE.2 u hu, map_one]
  · rw [Subgroup.card_map_of_injective hinj, h16]

theorem false_of_iso_orderOf_nine (h : A5Data T) {S : Type} [Group S] [IsSimpleGroup S]
    (φ : T ≃* S) {x : S} (hx : orderOf x = 9) : False :=
  h.false_of_orderOf_nine (Sec4.center_eq_bot_of_mulEquiv_isSimpleGroup h.qs φ)
    (x := φ.symm x) (by rw [MulEquiv.orderOf_eq]; exact hx)

theorem false_of_iso_inner (h : A5Data T) {S : Type} [Group S] [IsSimpleGroup S] (φ : T ≃* S)
    (hinn : InnerThree S) (h15 : ∀ x : S, orderOf x ≠ 15) : False := by
  have hZ := Sec4.center_eq_bot_of_mulEquiv_isSimpleGroup h.qs φ
  refine h.false_of_inner (quotCenterEquivOfBot hZ φ) (fun σ hσ => ?_)
    (by rw [hZ, Subgroup.card_bot]; norm_num) h15
  obtain ⟨s, hs⟩ := InnerThree.of_mulEquiv φ hinn σ hσ
  exact ⟨s, hs.symm⟩

theorem false_of_iso_inner_nine (h : A5Data T) {S : Type} [Group S] [IsSimpleGroup S]
    (φ : T ≃* S) (hinn : InnerThree S) (h9 : ¬ 9 ∣ Nat.card S) : False := by
  have hZ := Sec4.center_eq_bot_of_mulEquiv_isSimpleGroup h.qs φ
  refine h.false_of_inner_nine hZ (fun σ hσ => ?_) (by rwa [Nat.card_congr φ.toEquiv])
  obtain ⟨s, hs⟩ := InnerThree.of_mulEquiv φ hinn σ hσ
  exact ⟨s, hs.symm⟩

theorem false_of_iso_outer (h : A5Data T) {S : Type} [Group S] [IsSimpleGroup S] (φ : T ≃* S)
    (hY : ¬ 3 ∣ Nat.card (Outer S)) (h15 : ∀ x : S, orderOf x ≠ 15) : False := by
  have hZ := Sec4.center_eq_bot_of_mulEquiv_isSimpleGroup h.qs φ
  exact h.false_of_inner (quotCenterEquivOfBot hZ φ)
    (fun σ hσ => Sec13.Res5Proof.mem_range_conj_of_not_three_dvd_outer h.qs.1
      (quotCenterEquivOfBot hZ φ) hY hσ)
    (by rw [hZ, Subgroup.card_bot]; norm_num) h15

theorem false_of_iso_outer_nine (h : A5Data T) {S : Type} [Group S] [IsSimpleGroup S]
    (φ : T ≃* S) (hY : ¬ 3 ∣ Nat.card (Outer S)) (h9 : ¬ 9 ∣ Nat.card S) : False := by
  have hZ := Sec4.center_eq_bot_of_mulEquiv_isSimpleGroup h.qs φ
  exact h.false_of_inner_nine hZ
    (fun σ hσ => Sec13.Res5Proof.mem_range_conj_of_not_three_dvd_outer h.qs.1
      (quotCenterEquivOfBot hZ φ) hY hσ)
    (by rwa [Nat.card_congr φ.toEquiv])

end A5Data

theorem a5Row_alt_le_four {n : ℕ} (hn : n ≤ 4) :
    A5Row (fun T _ => Nonempty (T ≃* alternatingGroup (Fin n))) := by
  intro T _ _ hd ⟨φ⟩
  have hsol : Group.IsSolvable (alternatingGroup (Fin n)) :=
    alternatingGroup.isSolvable (by simpa using hn)
  exact Sec4.false_of_isQuasisimple_of_isSolvable hd.qs
    (Group.isSolvable_of_surjective (f := φ.symm.toMonoidHom) φ.symm.surjective)

theorem a5Row_alt_five : A5Row (fun T _ => Nonempty (T ≃* alternatingGroup (Fin 5))) :=
  fun T _ _ hd ⟨φ⟩ => hd.false_of_iso_card_dvd_sixty φ (by
    rw [nat_card_alternatingGroup, Nat.card_fin]; decide)

theorem innerThree_alt_six : InnerThree (alternatingGroup (Fin 6)) := fun σ hσ => by
  obtain ⟨s, hs⟩ := Sec14.Item148PtRes.mem_inner_of_pow_three hσ
  exact ⟨s, hs.symm⟩

theorem a5Row_alt_six : A5Row (fun T _ => Nonempty (T ≃* alternatingGroup (Fin 6))) := by
  intro T _ _ hd ⟨φ⟩
  haveI : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  exact hd.false_of_iso_inner φ innerThree_alt_six
    (Sec21.Item22Res4Proof.orderOf_alternating_ne_fifteen (by norm_num))

theorem a5Row_alt_seven : A5Row (fun T _ => Nonempty (T ≃* alternatingGroup (Fin 7))) := by
  intro T _ _ hd ⟨φ⟩
  obtain ⟨-, hZ, hinn, -, -⟩ := KFacts.KS14.a7_facts T ⟨φ⟩
  refine hd.false_of_inner (quotCenterEquivOfBot hZ φ) (fun σ hσ => ?_)
    (by rw [hZ, Subgroup.card_bot]; norm_num)
    (Sec21.Item22Res4Proof.orderOf_alternating_ne_fifteen (by norm_num))
  obtain ⟨x, hx⟩ := hinn σ ⟨1, by rw [pow_one]; exact hσ⟩
  exact ⟨x, hx.symm⟩

theorem a5Row_four_alt (n : ℕ) (hn : n ≤ 9) :
    A5Row (fun T _ => Nonempty (T ≃* alternatingGroup (Fin n))) := by
  rcases (by omega : n ≤ 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 ∨ n = 9) with
    h | rfl | rfl | rfl | rfl | rfl
  · exact a5Row_alt_le_four h
  · exact a5Row_alt_five
  · exact a5Row_alt_six
  · exact a5Row_alt_seven
  · exact fun T _ _ hd ⟨φ⟩ => hd.false_of_iso_E16 φ exists_E16_alt_eight
  · exact fun T _ _ hd ⟨φ⟩ => hd.false_of_iso_E16 φ exists_E16_alt_nine

section Cover


theorem a5Row_four_A6 :
    A5Row (fun T _ => IsExtOf T (alternatingGroup (Fin 6)) (Multiplicative (ZMod 3))) := by
  intro T _ _ hd hext
  have hZS : Subgroup.center (alternatingGroup (Fin 6)) = ⊥ :=
    alternatingGroup.center_eq_bot (by rw [Nat.card_fin]; norm_num)
  obtain ⟨hc3, ⟨e⟩⟩ := (Sec4.isTripleCover_iff_isExtOf hd.qs hZS).mpr hext
  exact hd.false_of_inner e
    (fun σ hσ => Sec12.KS128NotHJTC.mem_range_conj_of_isTripleCover hd.qs.1
      (Or.inl ⟨hc3, ⟨e⟩⟩) hσ)
    (by rw [hc3]; norm_num) (Sec21.Item22Res4Proof.orderOf_alternating_ne_fifteen (by norm_num))

theorem a5Row_four_A7 :
    A5Row (fun T _ => IsExtOf T (alternatingGroup (Fin 7)) (Multiplicative (ZMod 3))) := by
  intro T _ _ hd hext
  have hZS : Subgroup.center (alternatingGroup (Fin 7)) = ⊥ :=
    alternatingGroup.center_eq_bot (by rw [Nat.card_fin]; norm_num)
  obtain ⟨hc3, ⟨e⟩⟩ := (Sec4.isTripleCover_iff_isExtOf hd.qs hZS).mpr hext
  exact hd.false_of_inner e
    (fun σ hσ => Sec12.KS128NotHJTC.mem_range_conj_of_isTripleCover hd.qs.1
      (Or.inr (Or.inl ⟨hc3, ⟨e⟩⟩)) hσ)
    (by rw [hc3]; norm_num) (Sec21.Item22Res4Proof.orderOf_alternating_ne_fifteen (by norm_num))

end Cover

section L2


theorem a5Row_one_inner (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p)
    (h9 : ¬ 9 ∣ Nat.card (projSL 2 (GaloisField p 1))) :
    A5Row (fun T _ => Nonempty (T ≃* projSL 2 (GaloisField p 1))) := by
  intro T _ _ hd ⟨φ⟩
  have hK : Nat.card (GaloisField p 1) = p := by rw [GaloisField.card p 1 one_ne_zero, pow_one]
  haveI : IsSimpleGroup (projSL 2 (GaloisField p 1)) :=
    CFSG.PGLModel.isSimpleGroup_projSL_of_two_le (GaloisField p 1) le_rfl
      (Or.inr (by rw [hK]; omega)) (Or.inr (by rw [hK]; omega))
  exact hd.false_of_iso_inner_nine φ (innerThree_projSL_two p) h9

theorem a5Row_one (p e : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (he : 1 ≤ e) :
    A5Row (fun T _ => Nonempty (T ≃* projSL 2 (GaloisField p e))) := by
  intro T _ _ hd ⟨φ⟩
  have hp : p.Prime := Fact.out
  have hK : Nat.card (GaloisField p e) = p ^ e := GaloisField.card p e (by omega)
  have hLN : Nat.card (projSL 2 (GaloisField p e)) ∣ 1382446517760 := by
    rw [← Nat.card_congr φ.toEquiv]
    exact hd.dvd
  have hc := Sec11.KSListsProof.card_projSL_two_mul (GaloisField p e)
  rw [hK] at hc
  have hodd : Odd (p ^ e) := (hp.odd_of_ne_two hp2).pow
  have hg : Nat.gcd 2 (p ^ e - 1) = 2 := by
    obtain ⟨k, hk⟩ := hodd
    rw [hk, Nat.add_sub_cancel]
    exact Nat.gcd_eq_left (dvd_mul_right 2 k)
  rw [hg] at hc
  have hcontra : p ^ e * ((p ^ e) ^ 2 - 1) ∣ 1382446517760 * 2 := by
    rw [← hc]
    exact Nat.mul_dvd_mul_right hLN 2
  have hq : p ^ e ∣ Nat.card (projSL 2 (GaloisField p e)) := by
    have h' : p ^ e ∣ Nat.card (projSL 2 (GaloisField p e)) * 2 := by
      rw [hc]; exact dvd_mul_right _ _
    exact (coprime_pow_of_dvd hp (dvd_refl 2) (fun h =>
      hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h))).dvd_of_dvd_mul_right h'
  have hqN := hq.trans hLN
  have hpN : p ∣ 1382446517760 := (dvd_pow_self p (by omega)).trans hqN
  rcases prime_of_dvd_N hp hpN with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hp2 rfl
  ·
    have he5 := three_pow_dvd_N hqN
    interval_cases e
    · exact Sec13.Res5Proof.false_of_projSL_two_small (Or.inr (by rw [hK]; norm_num)) hd.qs φ
    · obtain ⟨ψ⟩ := CFSG.Open.StatedAPI.nonempty_mulEquiv_alternating_six_of_statedProj
        (by rw [hK]; norm_num) (CFSG.PGLModel.projSLEquivStatedProj 2 (GaloisField 3 2))
      exact a5Row_alt_six T hd ⟨φ.trans ψ⟩
    all_goals norm_num at hcontra
  ·
    rcases pow_dvd_N hp (by norm_num) hqN with h1 | ⟨h7, -⟩
    · obtain rfl : e = 1 := by omega
      norm_num at hc
      have h60 : Nat.card (projSL 2 (GaloisField 5 1)) = 60 := by omega
      exact hd.false_of_iso_card_dvd_sixty φ (by rw [h60])
    · norm_num at h7
  ·
    rcases pow_dvd_N hp (by norm_num) hqN with h1 | ⟨-, h3⟩
    · obtain rfl : e = 1 := by omega
      norm_num at hc
      exact hd.false_of_iso_not_five φ (by omega)
    · interval_cases e
      · norm_num at hc
        exact hd.false_of_iso_not_five φ (by omega)
      all_goals norm_num at hcontra
  ·
    rcases pow_dvd_N hp (by norm_num) hqN with h1 | ⟨h7, -⟩
    · obtain rfl : e = 1 := by omega
      norm_num at hc
      exact a5Row_one_inner 11 (by norm_num) (by omega) T hd ⟨φ⟩
    · norm_num at h7
  ·
    rcases pow_dvd_N hp (by norm_num) hqN with h1 | ⟨h7, -⟩
    · obtain rfl : e = 1 := by omega
      have hK19 : Nat.card (GaloisField 19 1) = 19 := by rw [hK]; norm_num
      haveI : IsSimpleGroup (projSL 2 (GaloisField 19 1)) :=
        CFSG.PGLModel.isSimpleGroup_projSL_of_two_le (GaloisField 19 1) le_rfl
          (Or.inr (by rw [hK19]; norm_num)) (Or.inr (by rw [hK19]; norm_num))
      obtain ⟨g, hg9⟩ := CFSG.AGLEmbedding.exists_orderOf_nine_psl_nineteen hK19
      set ψ := (CFSG.PGLModel.projSLEquivStatedProj 2 (GaloisField 19 1)).symm
      exact hd.false_of_iso_orderOf_nine φ (x := ψ g) (by rw [MulEquiv.orderOf_eq, hg9])
    · norm_num at h7
  ·
    rcases pow_dvd_N hp (by norm_num) hqN with h1 | ⟨h7, -⟩
    · obtain rfl : e = 1 := by omega
      norm_num at hc
      exact a5Row_one_inner 31 (by norm_num) (by omega) T hd ⟨φ⟩
    · norm_num at h7

end L2

theorem a5Row_two_SL (p e : ℕ) [Fact p.Prime] (hp3 : 3 < p) (he1 : 1 ≤ e) (he2 : e ≤ 2) :
    A5Row (fun T _ => Nonempty (T ≃* projSL 3 (GaloisField p e))) := by
  intro T _ _ hd ⟨φ⟩
  have hp : p.Prime := Fact.out
  have hLN : Nat.card (projSL 3 (GaloisField p e)) ∣ 1382446517760 := by
    rw [← Nat.card_congr φ.toEquiv]
    exact hd.dvd
  have hc := KFacts.KS14.card_projSL_three_mul_gcd (GaloisField p e)
  rw [GaloisField.card p e (by omega)] at hc
  have h3 : (p ^ e) ^ 3 ∣ Nat.card (projSL 3 (GaloisField p e)) := by
    have h' : (p ^ e) ^ 3 ∣ Nat.card (projSL 3 (GaloisField p e)) * Nat.gcd 3 (p ^ e - 1) := by
      rw [hc]; exact dvd_mul_right _ _
    have hcop : Nat.Coprime ((p ^ e) ^ 3) (Nat.gcd 3 (p ^ e - 1)) := by
      rw [← pow_mul]
      exact coprime_pow_of_dvd hp (Nat.gcd_dvd_left 3 _) (fun h => by
        have := Nat.le_of_dvd (by norm_num) h; omega)
    exact hcop.dvd_of_dvd_mul_right h'
  obtain ⟨rfl, rfl⟩ := eq_seven_of_cube_dvd hp hp3 he1 (h3.trans hLN)
  norm_num at hc
  exact hd.false_of_iso_not_five φ (by omega)

theorem a5Row_two_eps (p e : ℕ) [Fact p.Prime] (hp3 : 3 < p) (he1 : 1 ≤ e) (he2 : e ≤ 2) :
    A5Row (fun T _ => IsSLThreeEpsAt T (p ^ e)) := by
  intro T _ _ hd ⟨K, _, _, h⟩
  have hp : p.Prime := Fact.out
  rcases h with ⟨hK, ⟨φ⟩⟩ | ⟨hK, ⟨φ⟩⟩
  · have hLN : Nat.card (StatedSL 3 K) ∣ 1382446517760 := by
      rw [← Nat.card_congr φ.toEquiv]
      exact hd.dvd
    have hc := CFSG.Open.StatedAPI.card_statedSL_eq_prod (K := K) (d := 3) (by norm_num)
    rw [hK, show Finset.Icc 2 3 = ({2, 3} : Finset ℕ) by decide,
      Finset.prod_pair (by norm_num)] at hc
    have h3 : (p ^ e) ^ 3 ∣ 1382446517760 := by
      have : (p ^ e) ^ 3 ∣ Nat.card (StatedSL 3 K) := by
        rw [hc]; exact dvd_mul_right _ _
      exact this.trans hLN
    obtain ⟨rfl, rfl⟩ := eq_seven_of_cube_dvd hp hp3 he1 h3
    norm_num at hc
    exact hd.false_of_iso_not_five φ (by rw [hc]; norm_num)
  · have hLN : Nat.card (StatedSU 3 (p ^ e) K) ∣ 1382446517760 := by
      rw [← Nat.card_congr φ.toEquiv]
      exact hd.dvd
    have hu : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData p e K :=
      ⟨hp, he1, by rw [hK, ← pow_mul, mul_comm]⟩
    have hc := CFSG.GH74.GLS.Stage2.Final.ModelOrd.card_statedSU_int hu (n := 3) (by norm_num)
    rw [show Finset.Icc 2 3 = ({2, 3} : Finset ℕ) by decide, Finset.prod_pair (by norm_num)] at hc
    have h3 : (p ^ e) ^ 3 ∣ 1382446517760 := by
      have : (((p ^ e) ^ 3 : ℕ) : ℤ) ∣ (Nat.card (StatedSU 3 (p ^ e) K) : ℤ) := by
        rw [hc]; push_cast; exact dvd_mul_right _ _
      exact (Int.natCast_dvd_natCast.mp this).trans hLN
    obtain ⟨rfl, rfl⟩ := eq_seven_of_cube_dvd hp hp3 he1 h3
    have h43 : ((43 : ℕ) : ℤ) ∣ (Nat.card (StatedSU 3 (7 ^ 1) K) : ℤ) := by
      rw [hc]; norm_num
    have := (Int.natCast_dvd_natCast.mp h43).trans hLN
    norm_num at this

section Spor

set_option linter.unusedSectionVars false


theorem a5Row_spor_M11 :
    A5Row (fun T _ => Nonempty (T ≃* Blueprint.NativeSporadic.Carrier .M11)) := by
  intro T _ _ hd ⟨φ⟩
  haveI : IsSimpleGroup (Blueprint.NativeSporadic.Carrier .M11) :=
    CFSG.ClassicalInvolution.Q3.isSimpleGroup_m11_kernel
  haveI : Finite (Blueprint.NativeSporadic.Carrier .M11) :=
    inferInstanceAs (Finite Blueprint.NativeSporadic.M11)
  haveI : Finite (Outer (Blueprint.NativeSporadic.Carrier .M11)) :=
    Sec13.Res5Proof.finite_outer _
  exact hd.false_of_iso_outer φ (Sec13.Res5Proof.not_three_dvd_of_card_le_two
    CFSG.Sporadic.Schreier.at_m11_schreier.1) fun x => Sec4.Ronan148R.orderOf_ne_fifteen_m11 x

theorem a5Row_spor_J1 :
    A5Row (fun T _ => Nonempty (T ≃* Blueprint.NativeSporadic.Carrier .J1)) := by
  intro T _ _ hd ⟨φ⟩
  haveI : IsSimpleGroup (Blueprint.NativeSporadic.Carrier .J1) := CFSG.Sporadic.J1.isSimpleGroup_J1
  refine hd.false_of_iso_outer_nine φ ?_ ?_
  · change ¬ 3 ∣ Nat.card (Outer Blueprint.NativeSporadic.J1)
    rw [CFSG.Sporadic.Schreier.at_j1_schreier.1]
    norm_num
  · change ¬ 9 ∣ Nat.card Blueprint.NativeSporadic.J1
    rw [CFSG.Sporadic.J1.card_J1]
    norm_num

theorem a5Row_spor_M12 :
    A5Row (fun T _ => Nonempty (T ≃* Blueprint.NativeSporadic.Carrier .M12)) := by
  intro T _ _ hd ⟨e⟩
  haveI : IsSimpleGroup (Blueprint.NativeSporadic.Carrier .M12) :=
    CFSG.Sporadic.Co1Schreier.m12_simple
  have hZ := Sec4.center_eq_bot_of_mulEquiv_isSimpleGroup hd.qs e
  let f : Blueprint.NativeSporadic.M12 →* T := e.symm.toMonoidHom
  have hT : IsPGroup 3 (Subgroup.closure ({f Sec4.RonanK432.m12Sx,
      f Sec4.RonanK432.m12Sy} : Set T)) := by
    have h := isPGroup_m12S.map f
    rwa [MonoidHom.map_closure, Set.image_pair] at h
  refine hd.false_of_nonabelian_three hZ hT (Subgroup.subset_closure (Or.inl rfl))
    (Subgroup.subset_closure (Or.inr rfl)) fun h => m12S_noncomm ?_
  apply e.symm.injective
  have h' : f (Sec4.RonanK432.m12Sx * Sec4.RonanK432.m12Sy) =
      f (Sec4.RonanK432.m12Sy * Sec4.RonanK432.m12Sx) := by rw [map_mul, map_mul]; exact h
  exact h'

theorem a5Row_spor_M22 :
    A5Row (fun T _ => Nonempty (T ≃* Blueprint.NativeSporadic.Carrier .M22)) :=
  fun T _ _ hd ⟨φ⟩ => hd.false_of_iso_E16 φ CFSG.GH74.Uniqueness.SU.K.R3.exists_E16_M22

theorem a5Row_cover_M22 :
    A5Row (fun T _ => IsExtOf T (Blueprint.NativeSporadic.Carrier .M22)
      (Multiplicative (ZMod 3))) := by
  intro T _ _ hd hext
  obtain ⟨E, hE, h16⟩ := exists_E16_of_isExtOf hext CFSG.GH74.Uniqueness.SU.K.R3.exists_E16_M22
  exact hd.false_of_E16 hE h16

theorem a5Row_cover_ON :
    A5Row (fun T _ => IsExtOf T (Blueprint.NativeSporadic.Carrier .ONan)
      (Multiplicative (ZMod 3))) := by
  intro T _ _ hd hext
  apply hd.ne
  rw [card_of_isExtOf_three hext]
  change Nat.card Blueprint.NativeSporadic.ON * 3 = _
  rw [CFSG.Sporadic.ON.card_ON]

end Spor

end CFSG.RankThree.PartTwo.Sec14.Ronan148H
