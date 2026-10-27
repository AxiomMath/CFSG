module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Rank13
public import CFSG.LocalAnalysis.UniquenessCase.UCFront13
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21a
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846a

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.UC22.F13
open CFSG.RankThree.PartOne (pElementSubgroup)

variable {G : Type} [Group G] [Finite G]

theorem s13_Bar13_opp_le (p : ℕ) (X : Subgroup G) : Opp p X ≤ X :=
  (Subgroup.closure_le X).2 fun _ hx => hx.1

theorem s13_Bar13_opp_conjInv (p : ℕ) {M X : Subgroup G}
    (hX : ∀ g ∈ M, ∀ x ∈ X, g * x * g⁻¹ ∈ X) :
    ∀ g ∈ M, ∀ x ∈ Opp p X, g * x * g⁻¹ ∈ Opp p X := by
  intro g hg x hx
  have hgen : ∀ y ∈ ({y : G | y ∈ X ∧ ∃ k : ℕ, orderOf y = p ^ k} : Set G),
      (MulAut.conj g) y ∈ ({y : G | y ∈ X ∧ ∃ k : ℕ, orderOf y = p ^ k} : Set G) := by
    rintro y ⟨hyX, k, hk⟩
    refine ⟨?_, k, ?_⟩
    · simpa only [MulAut.conj_apply] using hX g hg y hyX
    · have hc : orderOf (g * y * g⁻¹) = orderOf y := by
        simpa only [MulAut.conj_apply] using (MulAut.conj g).orderOf_eq y
      rw [MulAut.conj_apply, hc, hk]
  have hsub : (MulAut.conj g) '' ({y : G | y ∈ X ∧ ∃ k : ℕ, orderOf y = p ^ k} : Set G)
      ⊆ ({y : G | y ∈ X ∧ ∃ k : ℕ, orderOf y = p ^ k} : Set G) := by
    rintro _ ⟨y, hy, rfl⟩
    exact hgen y hy
  have hmap : (Opp p X).map (MulAut.conj g).toMonoidHom ≤ Opp p X := by
    change (Subgroup.closure {y : G | y ∈ X ∧ ∃ k : ℕ, orderOf y = p ^ k}).map
        (MulAut.conj g).toMonoidHom
      ≤ Subgroup.closure {y : G | y ∈ X ∧ ∃ k : ℕ, orderOf y = p ^ k}
    rw [MonoidHom.map_closure]
    exact Subgroup.closure_mono hsub
  simpa [MulAut.conj_apply] using hmap ⟨x, hx, rfl⟩

theorem s13_Bar13_barPreimage_conjInv {M : Subgroup G} {Y : Subgroup (Bar2 M)} (hY : Y.Normal) :
    ∀ g ∈ M, ∀ x ∈ barPreimage M Y, g * x * g⁻¹ ∈ barPreimage M Y := by
  intro g hg x hx
  obtain ⟨x', hx', rfl⟩ := hx
  refine ⟨⟨g, hg⟩ * x' * ⟨g, hg⟩⁻¹, ?_, ?_⟩
  · show (QuotientGroup.mk' (CFSG.pCore 2 ↥M)) (⟨g, hg⟩ * x' * ⟨g, hg⟩⁻¹) ∈ Y
    have hxY : (QuotientGroup.mk' (CFSG.pCore 2 ↥M)) x' ∈ Y := hx'
    have hconj := hY.conj_mem _ hxY ((QuotientGroup.mk' (CFSG.pCore 2 ↥M)) ⟨g, hg⟩)
    simpa only [map_mul, map_inv] using hconj
  · rfl

theorem s13_barPreimage_le (M : Subgroup G) (Y : Subgroup (Bar2 M)) : barPreimage M Y ≤ M := by
  exact Subgroup.map_subtype_le _

theorem s13_barImage_barPreimage (M : Subgroup G) (Y : Subgroup (Bar2 M)) :
    barImage M (barPreimage M Y) = Y := by
  show ((((Y.comap (QuotientGroup.mk' (CFSG.pCore 2 ↥M))).map M.subtype).subgroupOf M).map
      (QuotientGroup.mk' (CFSG.pCore 2 ↥M))) = Y
  rw [show ((Y.comap (QuotientGroup.mk' (CFSG.pCore 2 ↥M))).map M.subtype).subgroupOf M
      = Y.comap (QuotientGroup.mk' (CFSG.pCore 2 ↥M)) from
        Subgroup.comap_map_eq_self_of_injective M.subtype_injective _,
    Subgroup.map_comap_eq_self_of_surjective
      (QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥M)) Y]

theorem s13_barImage_self (M : Subgroup G) : barImage M M = ⊤ := by
  show ((M.subgroupOf M).map (QuotientGroup.mk' (CFSG.pCore 2 ↥M))) = ⊤
  rw [Subgroup.subgroupOf_self,
    Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥M))]

theorem s13_barImage_sup {M A B : Subgroup G} (hA : A ≤ M) (hB : B ≤ M) :
    barImage M (A ⊔ B) = barImage M A ⊔ barImage M B := by
  show (((A ⊔ B).subgroupOf M).map (QuotientGroup.mk' (CFSG.pCore 2 ↥M))) = _
  rw [Subgroup.subgroupOf_sup hA hB, Subgroup.map_sup]
  rfl

theorem s13_barImage_cMStar (M X : Subgroup G) :
    barImage M (cMStar M X) = Subgroup.centralizer (barImage M X : Set (Bar2 M)) :=
  s13_barImage_barPreimage M _

theorem s13_barImage_opp {p : ℕ} (hp : p.Prime) {M P : Subgroup G} (hP : P ≤ M) :
    barImage M (Opp p P) = pElementSubgroup p (barImage M P) := by
  have h1 : (pElementSubgroup p (P.subgroupOf M)).map M.subtype = pElementSubgroup p P := by
    have h := s13_pElementSubgroup_map (p := p) hp M.subtype (P.subgroupOf M)
    rwa [Subgroup.subgroupOf_map_subtype, inf_of_le_left hP] at h
  have h2 : (pElementSubgroup p P).subgroupOf M = pElementSubgroup p (P.subgroupOf M) := by
    rw [← h1]
    exact Subgroup.comap_map_eq_self_of_injective M.subtype_injective _
  show ((pElementSubgroup p P).subgroupOf M).map
      (QuotientGroup.mk' (CFSG.pCore 2 ↥M)) = pElementSubgroup p (barImage M P)
  rw [h2, s13_pElementSubgroup_map (p := p) hp]
  rfl

theorem s13_barImage_Lp (M : Subgroup G) {p : ℕ} (hp : p.Prime) :
    barImage M (Lp M p) = pElementSubgroup p (CFSG.layer (Bar2 M)) := by
  have hle : OTwoEIn M ≤ M := s13_barPreimage_le M _
  rw [show Lp M p = Opp p (OTwoEIn M) from rfl,
    s13_barImage_opp (M := M) (P := OTwoEIn M) hp hle,
    show OTwoEIn M = barPreimage M (CFSG.layer (Bar2 M)) from rfl,
    s13_barImage_barPreimage M (CFSG.layer (Bar2 M))]

theorem s13_barImage_Sp (M : Subgroup G) {p : ℕ} (hp : p.Prime) :
    barImage M (Sp M p) =
      pElementSubgroup p (Subgroup.centralizer
        (pElementSubgroup p (CFSG.layer (Bar2 M)) : Set (Bar2 M))) := by
  have hle : cMStar M (Lp M p) ≤ M := s13_barPreimage_le M _
  rw [show Sp M p = Opp p (cMStar M (Lp M p)) from rfl,
    s13_barImage_opp (M := M) (P := cMStar M (Lp M p)) hp hle,
    s13_barImage_cMStar M (Lp M p), s13_barImage_Lp M hp]

theorem s13_Lp_le (M : Subgroup G) (p : ℕ) : Lp M p ≤ M :=
  (s13_Bar13_opp_le p (OTwoEIn M)).trans (s13_barPreimage_le M _)

theorem s13_Sp_le (M : Subgroup G) (p : ℕ) : Sp M p ≤ M :=
  (s13_Bar13_opp_le p (cMStar M (Lp M p))).trans (s13_barPreimage_le M _)

theorem s13_Lp_normal (M : Subgroup G) (p : ℕ) : ((Lp M p).subgroupOf M).Normal := by
  haveI hchar : (CFSG.layer (Bar2 M)).Characteristic := CFSG.LocalCores.layer_characteristic
  have hconj := s13_Bar13_barPreimage_conjInv (M := M) (Y := CFSG.layer (Bar2 M)) inferInstance
  have hOpp := s13_Bar13_opp_conjInv p hconj
  show (((Opp p (barPreimage M (CFSG.layer (Bar2 M)))).subgroupOf M)).Normal
  exact ⟨fun n hn g => hOpp g.1 g.2 n.1 hn⟩

theorem s13_Sp_normal (M : Subgroup G) (p : ℕ) : ((Sp M p).subgroupOf M).Normal := by
  haveI hLp : (barImage M (Lp M p)).Normal :=
    (s13_Lp_normal M p).map (QuotientGroup.mk' (CFSG.pCore 2 ↥M))
      (QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥M))
  haveI hcent : (Subgroup.centralizer (barImage M (Lp M p) : Set (Bar2 M))).Normal :=
    Subgroup.normal_centralizer
  have hconj := s13_Bar13_barPreimage_conjInv (M := M)
    (Y := Subgroup.centralizer (barImage M (Lp M p) : Set (Bar2 M))) hcent
  have hOpp := s13_Bar13_opp_conjInv p hconj
  show (((Opp p (barPreimage M (Subgroup.centralizer
    (barImage M (Lp M p) : Set (Bar2 M))))).subgroupOf M)).Normal
  exact ⟨fun n hn g => hOpp g.1 g.2 n.1 hn⟩

theorem s13_barImage_Lp_le_layer (M : Subgroup G) (p : ℕ) :
    barImage M (Lp M p) ≤ CFSG.layer (Bar2 M) := by
  calc barImage M (Lp M p)
      ≤ barImage M (OTwoEIn M) :=
        Subgroup.map_mono (Subgroup.subgroupOf_mono M (s13_Bar13_opp_le p (OTwoEIn M)))
    _ = CFSG.layer (Bar2 M) := by
        rw [show OTwoEIn M = barPreimage M (CFSG.layer (Bar2 M)) from rfl]
        exact s13_barImage_barPreimage M (CFSG.layer (Bar2 M))

theorem s13_mem_of_barImage_of_pPart {M N : Subgroup G} (hNM : N ≤ M)
    (hN : (N.subgroupOf M).Normal) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {x : G} (hxM : x ∈ M)
    (hx : ∃ k : ℕ, x ^ p ^ k = 1)
    (hbar : (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨x, hxM⟩ : Bar2 M) ∈ barImage M N) : x ∈ N := by
  classical
  let π : ↥M →* Bar2 M := QuotientGroup.mk' (CFSG.pCore 2 ↥M)
  letI : (N.subgroupOf M).Normal := hN
  let φ : ↥M →* ↥M ⧸ (N.subgroupOf M) := QuotientGroup.mk' (N.subgroupOf M)
  change π ⟨x, hxM⟩ ∈ (N.subgroupOf M).map π at hbar
  obtain ⟨n, hnN, hnπ⟩ := hbar
  obtain ⟨k, hk⟩ := hx
  have htker : n⁻¹ * ⟨x, hxM⟩ ∈ π.ker := by
    rw [MonoidHom.mem_ker]
    simp [map_mul, map_inv, hnπ]
  rw [show π.ker = CFSG.pCore 2 ↥M from QuotientGroup.ker_mk' (CFSG.pCore 2 ↥M)] at htker
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, ha⟩ := (IsPGroup.iff_orderOf.mp CFSG.pCore_isPGroup)
    (⟨n⁻¹ * ⟨x, hxM⟩, htker⟩ : ↥(CFSG.pCore 2 ↥M))
  have hord : orderOf (n⁻¹ * ⟨x, hxM⟩) = 2 ^ a :=
    (Subgroup.orderOf_coe (⟨n⁻¹ * ⟨x, hxM⟩, htker⟩ : ↥(CFSG.pCore 2 ↥M))).trans ha
  have hxpow : (⟨x, hxM⟩ : ↥M) ^ p ^ k = 1 := by
    apply Subtype.ext
    simpa using hk
  have hdvd1 : orderOf (φ ⟨x, hxM⟩) ∣ p ^ k := by
    apply orderOf_dvd_of_pow_eq_one
    rw [← map_pow, hxpow, map_one]
  have hφn : φ n = 1 := (QuotientGroup.eq_one_iff (N := N.subgroupOf M) n).2 hnN
  have hφx : φ ⟨x, hxM⟩ = φ (n⁻¹ * ⟨x, hxM⟩) := by
    simp [map_mul, map_inv, hφn]
  have hdvd2 : orderOf (φ ⟨x, hxM⟩) ∣ 2 ^ a := by
    apply orderOf_dvd_of_pow_eq_one
    have ht2 : (n⁻¹ * ⟨x, hxM⟩) ^ (2 ^ a) = 1 := by
      rw [← hord]
      exact pow_orderOf_eq_one _
    rw [hφx, ← map_pow, ht2, map_one]
  have hcop : Nat.Coprime (p ^ k) (2 ^ a) :=
    Nat.Coprime.pow _ _ ((Nat.coprime_primes hp Nat.prime_two).2 hp2)
  have h1 : orderOf (φ ⟨x, hxM⟩) ∣ 1 := by
    rw [← hcop.gcd_eq_one]
    exact Nat.dvd_gcd hdvd1 hdvd2
  have hφx1 : φ ⟨x, hxM⟩ = 1 := orderOf_eq_one_iff.1 (Nat.dvd_one.1 h1)
  have hxN : (⟨x, hxM⟩ : ↥M) ∈ N.subgroupOf M :=
    (QuotientGroup.eq_one_iff (N := N.subgroupOf M) (⟨x, hxM⟩ : ↥M)).1 hφx1
  exact hxN

theorem s13_pRank_barImage {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {M P : Subgroup G}
    (hPM : P ≤ M) : CFSG.Open.pRank p (barImage M P) = CFSG.Open.pRank p P := by
  have hker : IsPGroup 2 (QuotientGroup.mk' (CFSG.pCore 2 ↥M)).ker := by
    rw [show (QuotientGroup.mk' (CFSG.pCore 2 ↥M)).ker = CFSG.pCore 2 ↥M from
      QuotientGroup.ker_mk' (CFSG.pCore 2 ↥M)]
    exact CFSG.pCore_isPGroup
  have h1 : CFSG.Open.pRank p ((P.subgroupOf M).map (QuotientGroup.mk' (CFSG.pCore 2 ↥M)))
      = CFSG.Open.pRank p (P.subgroupOf M) :=
    s13_pRank_map_eq (p := p) hp hp2 (QuotientGroup.mk' (CFSG.pCore 2 ↥M)) hker (P.subgroupOf M)
  have hinj : ∀ x ∈ P.subgroupOf M, M.subtype x = 1 → x = 1 := fun x _ h => Subtype.ext h
  have h2 : CFSG.Open.pRank p ((P.subgroupOf M).map M.subtype)
      = CFSG.Open.pRank p (P.subgroupOf M) :=
    CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7L710.pRank_map_eq
      (f := M.subtype) (T₁ := P.subgroupOf M) hinj hp.one_lt
  have hmap : (P.subgroupOf M).map M.subtype = P := by
    rw [Subgroup.subgroupOf_map_subtype, inf_of_le_left hPM]
  show CFSG.Open.pRank p ((P.subgroupOf M).map (QuotientGroup.mk' (CFSG.pCore 2 ↥M)))
      = CFSG.Open.pRank p P
  rw [h1, ← h2, hmap]

theorem s13_pRank_bar_top {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (M : Subgroup G) :
    CFSG.Open.pRank p (⊤ : Subgroup (Bar2 M)) = CFSG.Open.pRank p M := by
  rw [← s13_barImage_self M]
  exact s13_pRank_barImage hp hp2 le_rfl

theorem s13_cop {M Y : Subgroup G} {p r : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hr : r.Prime)
    (hr2 : r ≠ 2) (hYM : Y ≤ M) (hY : IsPGroup r Y) {s : Bar2 M} (hs : orderOf s = p)
    (hcent : barImage M Y ≤ Subgroup.centralizer ({s} : Set (Bar2 M))) :
    p ∣ Nat.card ↥(M ⊓ Subgroup.centralizer (Y : Set G)) := by
  classical
  let π : ↥M →* Bar2 M := QuotientGroup.mk' (CFSG.pCore 2 ↥M)
  have hker : IsPGroup 2 π.ker := by
    rw [show π.ker = CFSG.pCore 2 ↥M from QuotientGroup.ker_mk' (CFSG.pCore 2 ↥M)]
    exact CFSG.pCore_isPGroup
  let Qb : Subgroup (Bar2 M) := Subgroup.zpowers s
  have hQb : IsPGroup p Qb := by
    haveI : Fact p.Prime := ⟨hp⟩
    refine IsPGroup.of_card (n := 1) ?_
    rw [show Nat.card Qb = orderOf s from Nat.card_zpowers s, hs, pow_one]
  obtain ⟨A₀, hA₀, hA₀map, hdisj⟩ :=
    UC6S846.exists_lift_pGroup π (show Function.Surjective π from
      QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥M)) hker hp hp2 Qb hQb
  let A : Subgroup G := A₀.map M.subtype
  let O : Subgroup G := (CFSG.pCore 2 ↥M).map M.subtype
  have hO : IsPGroup 2 O := CFSG.pCore_isPGroup.map M.subtype
  have hA : IsPGroup p A := hA₀.map M.subtype
  have hOM : O ≤ M := Subgroup.map_subtype_le _
  have hOsub : O.subgroupOf M = CFSG.pCore 2 ↥M :=
    Subgroup.comap_map_eq_self_of_injective M.subtype_injective _
  have hOnorm : (O.subgroupOf M).Normal := by
    rw [hOsub]
    exact CFSG.pCore_normal
  have hMN : M ≤ Subgroup.normalizer (O : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hOM).1 hOnorm
  have hAO : A ≤ Subgroup.normalizer (O : Set G) :=
    (Subgroup.map_subtype_le A₀).trans hMN
  have hEO : Y ≤ Subgroup.normalizer (O : Set G) := hYM.trans hMN
  have hcomm : ∀ e ∈ Y, ∀ a ∈ A, e * a * e⁻¹ * a⁻¹ ∈ O := by
    intro e he a ha
    obtain ⟨a', ha', rfl⟩ := ha
    let e' : ↥M := ⟨e, hYM he⟩
    have he'Y : e' ∈ Y.subgroupOf M := he
    have hbar_e : π e' ∈ barImage M Y := ⟨e', he'Y, rfl⟩
    have hcent_e : π e' ∈ Subgroup.centralizer ({s} : Set (Bar2 M)) := hcent hbar_e
    have hs_comm : π e' * s = s * π e' :=
      ((Subgroup.mem_centralizer_iff.1 hcent_e) s (by simp)).symm
    have ha'zp : π a' ∈ Qb := by
      have h := Subgroup.mem_map_of_mem π ha'
      rwa [hA₀map] at h
    have hs_mem : s ∈ Subgroup.centralizer ({π e'} : Set (Bar2 M)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro m hm
      rw [Set.mem_singleton_iff] at hm
      subst hm
      exact hs_comm
    have hQb_le : Qb ≤ Subgroup.centralizer ({π e'} : Set (Bar2 M)) :=
      Subgroup.zpowers_le.2 hs_mem
    have ha'_cent : π a' ∈ Subgroup.centralizer ({π e'} : Set (Bar2 M)) := hQb_le ha'zp
    have hcomm_a : π a' * π e' = π e' * π a' :=
      ((Subgroup.mem_centralizer_iff.1 ha'_cent) (π e') (by simp)).symm
    have hker' : e' * a' * e'⁻¹ * a'⁻¹ ∈ π.ker := by
      rw [MonoidHom.mem_ker]
      simp only [map_mul, map_inv]
      rw [← hcomm_a]
      group
    rw [show π.ker = CFSG.pCore 2 ↥M from QuotientGroup.ker_mk' (CFSG.pCore 2 ↥M)] at hker'
    have hmem : M.subtype (e' * a' * e'⁻¹ * a'⁻¹) ∈ O :=
      Subgroup.mem_map_of_mem M.subtype hker'
    change M.subtype e' * M.subtype a' * (M.subtype e')⁻¹ * (M.subtype a')⁻¹ ∈ O
    simpa only [map_mul, map_inv] using hmem
  obtain ⟨A', hA'cent, hA'AO, hA'iso⟩ :=
    UC6S846.exists_centralizing_copy hr hr2 hp hp2 O A Y hO hAO hEO hA hY hcomm
  obtain ⟨e⟩ := hA'iso
  have hcardA' : Nat.card A' = Nat.card A := Nat.card_congr e.toEquiv
  have hcardA : Nat.card A = Nat.card A₀ := by
    change Nat.card (A₀.map M.subtype) = Nat.card A₀
    rw [Subgroup.card_map_of_injective M.subtype_injective]
  have hcardA₀ : Nat.card A₀ = p := by
    have hcard : Nat.card (A₀.map π) = Nat.card A₀ := by
      refine CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7L710.card_map_of_le
        (f := π) (T₁ := A₀) ?_ (E := A₀) le_rfl
      intro x hx hx1
      have : x ∈ A₀ ⊓ π.ker := ⟨hx, hx1⟩
      rw [show A₀ ⊓ π.ker = ⊥ from hdisj.eq_bot] at this
      exact this
    rw [← hcard, hA₀map, show Nat.card Qb = orderOf s from Nat.card_zpowers s, hs]
  have hle : A' ≤ M ⊓ Subgroup.centralizer (Y : Set G) := by
    refine le_inf ?_ hA'cent
    exact hA'AO.trans (sup_le (Subgroup.map_subtype_le A₀) (Subgroup.map_subtype_le _))
  have hdvd : Nat.card A' ∣ Nat.card ↥(M ⊓ Subgroup.centralizer (Y : Set G)) :=
    Subgroup.card_dvd_of_le hle
  rwa [hcardA', hcardA, hcardA₀] at hdvd

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
