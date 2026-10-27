module

public import CFSG.RankThree.PartTwo.Sec21.FF79Sec3L4Lift2
import CFSG.RankThree.PartTwo.Sec21.FF79ThmAOdd
import CFSG.LocalAnalysis.SignalizerFunctor.InvariantSylowAmbient

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79

open CFSG CFSG.RankThree.PartTwo.Sec21
open CFSG.Assembly.RankThreeEven (localRank)

section Abstract

variable {G : Type} [Group G]

theorem rank2_elem_intro {p : ℕ} {S : Subgroup G} (hc : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x)
    (hp : ∀ x ∈ S, x ^ p = 1) : IsElementaryAbelian p S := by
  refine { is_comm := ⟨fun a b => Subtype.ext (hc a a.2 b b.2)⟩, exponent_dvd_p := ?_ }
  exact Monoid.exponent_dvd_iff_forall_pow_eq_one.2 fun x => Subtype.ext (hp x x.2)

theorem rank2_elem_comm {p : ℕ} {S : Subgroup G} (h : IsElementaryAbelian p S) :
    ∀ x ∈ S, ∀ y ∈ S, x * y = y * x := fun x hx y hy =>
  congrArg Subtype.val (h.toIsMulCommutative.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)

theorem rank2_elemAb_sup [Finite G] {p k l : ℕ} {X Y : Subgroup G} (hX : IsElemAb p k X)
    (hY : IsElemAb p l Y) (hc : ∀ x ∈ X, ∀ y ∈ Y, x * y = y * x) (hi : X ⊓ Y = ⊥) :
    IsElemAb p (k + l) (X ⊔ Y) := by
  let μ : X × Y →* G := MonoidHom.noncommCoprod X.subtype Y.subtype
    fun a b => show Commute (X.subtype a) (Y.subtype b) from hc a a.2 b b.2
  have hrange : μ.range = X ⊔ Y := by
    rw [MonoidHom.noncommCoprod_range, Subgroup.range_subtype, Subgroup.range_subtype]
  have hμ : ∀ x : X × Y, μ x = (x.1 : G) * x.2 := fun _ => rfl
  have hinj : Function.Injective μ := by
    rintro ⟨a1, b1⟩ ⟨a2, b2⟩ h
    have h' : (a1 : G) * b1 = a2 * b2 := h
    have hab : (a2 : G)⁻¹ * a1 = b2 * (b1 : G)⁻¹ := by
      calc (a2 : G)⁻¹ * a1 = (a2 : G)⁻¹ * (a1 * b1) * (b1 : G)⁻¹ := by group
        _ = (a2 : G)⁻¹ * (a2 * b2) * (b1 : G)⁻¹ := by rw [h']
        _ = b2 * (b1 : G)⁻¹ := by group
    have hmem : (a2 : G)⁻¹ * a1 ∈ X ⊓ Y :=
      ⟨X.mul_mem (X.inv_mem a2.2) a1.2, hab ▸ Y.mul_mem b2.2 (Y.inv_mem b1.2)⟩
    rw [hi, Subgroup.mem_bot] at hmem
    have ha : a1 = a2 := Subtype.ext (inv_mul_eq_one.mp hmem |>.symm)
    have hb : b1 = b2 := by
      apply Subtype.ext
      have : (a1 : G) * b1 = a1 * b2 := by rw [h', ← ha]
      exact mul_left_cancel this
    rw [ha, hb]
  have hX1 := hX.1
  have hY1 := hY.1
  have hsup : ∀ x ∈ X ⊔ Y, ∃ a ∈ X, ∃ b ∈ Y, x = a * b := by
    intro x hx
    rw [← hrange] at hx
    obtain ⟨⟨a, b⟩, rfl⟩ := hx
    exact ⟨a, a.2, b, b.2, rfl⟩
  refine ⟨?_, ?_⟩
  · refine rank2_elem_intro ?_ ?_
    · intro x hx y hy
      obtain ⟨a, ha, b, hb, rfl⟩ := hsup x hx
      obtain ⟨a', ha', b', hb', rfl⟩ := hsup y hy
      have c1 : Commute a a' := rank2_elem_comm hX1 a ha a' ha'
      have c2 : Commute a b' := hc a ha b' hb'
      have c3 : Commute b a' := (hc a' ha' b hb).symm
      have c4 : Commute b b' := rank2_elem_comm hY1 b hb b' hb'
      exact ((c1.mul_right c2).mul_left (c3.mul_right c4)).eq
    · intro x hx
      obtain ⟨a, ha, b, hb, rfl⟩ := hsup x hx
      have c : Commute a b := hc a ha b hb
      rw [c.mul_pow, elemPow_eq_one_of_isElementaryAbelian (A := X) a ha,
        elemPow_eq_one_of_isElementaryAbelian (A := Y) b hb, one_mul]
  · have h1 : Nat.card ↥(X ⊔ Y) = Nat.card (X × Y) := by
      rw [← hrange]
      exact Nat.card_range_of_injective hinj
    rw [h1, Nat.card_prod, hX.2, hY.2, pow_add]

end Abstract

section Lift

variable {C : Type} [Group C] [Finite C]

theorem rank2_lift_T (Q : Subgroup C) [Q.Normal] (hQ : Nat.Coprime 3 (Nat.card Q))
    (T : Subgroup (C ⧸ Q)) {k : ℕ} (hT : IsElemAb 3 k T) :
    ∃ T' : Subgroup C, IsElemAb 3 k T' ∧ T'.map (QuotientGroup.mk' Q) = T ∧ T' ⊓ Q = ⊥ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI := hT.1
  have hT3 : IsPGroup 3 T := IsElementaryAbelian.isPGroup 3 T
  have h1 : IsPGroup 3 (Subgroup.zpowers (1 : C)) := by
    refine IsPGroup.of_card (n := 0) ?_
    rw [Nat.card_zpowers]; simp
  obtain ⟨T', hT'D, -, hT'3, hcard, hmap⟩ := sylow_lift_pgroup Q hQ T hT3
    (T.comap (QuotientGroup.mk' Q))
    (fun t ht => by
      obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective t
      exact ⟨c, ht, rfl⟩)
    (fun c hc => hc) 1 (Subgroup.one_mem _) h1
  have hinf : T' ⊓ Q = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxT, hxQ⟩
    exact (Subgroup.mem_bot).2 (eq_one_of_pgroup_of_coprime hT'3 hQ hxT hxQ)
  have hTmem : ∀ x ∈ T', (QuotientGroup.mk x : C ⧸ Q) ∈ T := fun x hx => hT'D hx
  have hcomm : ∀ x ∈ T', ∀ y ∈ T', x * y = y * x := by
    intro x hx y hy
    have hxy : (QuotientGroup.mk (x * y * (y * x)⁻¹) : C ⧸ Q) = 1 := by
      have := rank2_elem_comm hT.1 _ (hTmem x hx) _ (hTmem y hy)
      simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv, this, mul_inv_cancel]
    have hQm : x * y * (y * x)⁻¹ ∈ Q := (QuotientGroup.eq_one_iff _).1 hxy
    have hTm : x * y * (y * x)⁻¹ ∈ T' :=
      T'.mul_mem (T'.mul_mem hx hy) (T'.inv_mem (T'.mul_mem hy hx))
    have : x * y * (y * x)⁻¹ = 1 :=
      (Subgroup.mem_bot).1 (hinf ▸ (⟨hTm, hQm⟩ : _ ∈ T' ⊓ Q))
    exact mul_inv_eq_one.1 this
  have hpow : ∀ x ∈ T', x ^ 3 = 1 := by
    intro x hx
    have hx3 : (QuotientGroup.mk (x ^ 3) : C ⧸ Q) = 1 := by
      rw [QuotientGroup.mk_pow]
      exact elemPow_eq_one_of_isElementaryAbelian (A := T) _ (hTmem x hx)
    have hQm : x ^ 3 ∈ Q := (QuotientGroup.eq_one_iff _).1 hx3
    exact (Subgroup.mem_bot).1 (hinf ▸ (⟨T'.pow_mem hx 3, hQm⟩ : _ ∈ T' ⊓ Q))
  exact ⟨T', ⟨rank2_elem_intro hcomm hpow, hcard.trans hT.2⟩, hmap, hinf⟩

theorem rank2_lift (Q : Subgroup C) [Q.Normal] (hQ : Nat.Coprime 3 (Nat.card Q))
    (P T : Subgroup (C ⧸ Q)) (hP : IsPGroup 2 P) (hPne : P ≠ ⊥) (hT : IsElemAb 3 2 T)
    (hTN : T ≤ Nor P) :
    ∃ P' T' : Subgroup C, IsPGroup 2 P' ∧ P' ≠ ⊥ ∧ IsElemAb 3 2 T' ∧ T' ≤ Nor P' ∧
      T'.map (QuotientGroup.mk' Q) = T ∧ T' ⊓ Q = ⊥ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨T', hT', hmap, hinf⟩ := rank2_lift_T Q hQ T hT
  have hT'3 : IsPGroup 3 T' := by
    haveI := hT'.1
    exact IsElementaryAbelian.isPGroup 3 T'
  set Pt : Subgroup C := P.comap (QuotientGroup.mk' Q) with hPt
  have hmemPt : ∀ x : C, x ∈ Pt ↔ (QuotientGroup.mk x : C ⧸ Q) ∈ P := fun x => Iff.rfl
  have hTmem : ∀ x ∈ T', (QuotientGroup.mk x : C ⧸ Q) ∈ T := fun x hx =>
    hmap ▸ Subgroup.mem_map_of_mem _ hx
  have hnor : T' ≤ Nor Pt := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro h
    rw [hmemPt, hmemPt, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    exact (Subgroup.mem_normalizer_iff.1 (hTN (hTmem x hx)) _)
  let f : ↥Pt →* C ⧸ Q := (QuotientGroup.mk' Q).comp Pt.subtype
  have hker : f.ker = Q.comap Pt.subtype := by
    ext x
    simp [f, MonoidHom.mem_ker, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  have hrange : f.range = P := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact x.2
    · intro hy
      obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective y
      exact ⟨⟨c, hy⟩, rfl⟩
  have hcardPt : Nat.card f.ker * Nat.card P = Nat.card Pt := by
    have := Subgroup.card_ker_mul_card_range f
    rw [hrange] at this
    simpa using this
  have hkerdvd : Nat.card f.ker ∣ Nat.card Q := by
    rw [hker]
    exact Subgroup.card_comap_dvd_of_injective Q Pt.subtype Subtype.coe_injective
  obtain ⟨n, hn⟩ := hP.exists_card_eq
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hPne (Subgroup.card_eq_one.1 (by simpa using hn))
  have hcop : Nat.Coprime 3 (Nat.card Pt) := by
    rw [← hcardPt, hn]
    exact (hQ.coprime_dvd_right hkerdvd).mul_right (Nat.Coprime.pow_right n (by norm_num))
  have h2 : 2 ∣ Nat.card Pt := by
    rw [← hcardPt, hn]
    exact Dvd.dvd.mul_left (dvd_pow_self 2 hn0) _
  obtain ⟨S, hSn, hSne⟩ :=
    CFSG.SignalizerFunctor.Helpers.normalized_subgroup_invariant_sylow_nontrivial 3 2
      Nat.prime_three Nat.prime_two T' Pt hT'3 hnor hcop h2
  exact ⟨S.map Pt.subtype, T', (S.isPGroup').map _, hSne, hT', hSn, hmap, hinf⟩

end Lift

section Main

variable {G : Type} [Group G] [Finite G]
variable {b : G} {J B A P D : Subgroup G} {a : G}

theorem rank2_main {U : Subgroup G} (hUe : IsElemAb 3 2 U) (hr : localRank 3 G = 3) :
    ∀ P T : Subgroup (CQ U), IsPGroup 2 P → P ≠ ⊥ → IsElemAb 3 2 T →
      T ⊓ cqImg U U = ⊥ → T ≤ Nor P → False := by
  intro P T hP hPne hT hTZ hTN
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : (pPrimeCore 3 ↥(CenS U)).Normal := pPrimeCore_normal
  obtain ⟨P', T', hP', hP'ne, hT', hT'N, hmap, hinf⟩ :=
    rank2_lift (pPrimeCore 3 ↥(CenS U)) pPrimeCore_coprime_card P T hP hPne hT hTN
  have hcen : ∀ c : ↥(CenS U), ∀ u ∈ U, u * (c : G) = c * u := fun c u hu =>
    Subgroup.mem_centralizer_iff.1 c.2 u hu
  have hP''2 : IsPGroup 2 ↥(P'.map (CenS U).subtype) := hP'.map (CenS U).subtype
  have hP''ne : P'.map (CenS U).subtype ≠ ⊥ := fun hb =>
    hP'ne ((Subgroup.map_eq_bot_iff_of_injective P' (CenS U).subtype_injective).1 hb)
  have hT''N : T'.map (CenS U).subtype ≤ Nor (P'.map (CenS U).subtype) := by
    rintro _ ⟨y, hy, rfl⟩
    apply Subgroup.mem_normalizer_fintype
    rintro _ ⟨p, hp, rfl⟩
    exact ⟨y * p * y⁻¹, (Subgroup.mem_normalizer_iff.1 (hT'N hy) p).1 hp, rfl⟩
  have hUN : U ≤ Nor (P'.map (CenS U).subtype) := by
    intro u hu
    apply Subgroup.mem_normalizer_fintype
    rintro _ ⟨p, hp, rfl⟩
    have : u * ((CenS U).subtype p) * u⁻¹ = (CenS U).subtype p := by
      change u * (p : G) * u⁻¹ = p
      rw [hcen p u hu]; group
    rw [this]
    exact ⟨p, hp, rfl⟩
  have hcomm : ∀ x ∈ U, ∀ y ∈ T'.map (CenS U).subtype, x * y = y * x := by
    rintro x hx _ ⟨c, -, rfl⟩
    exact hcen c x hx
  have hUT : U ⊓ T'.map (CenS U).subtype = ⊥ := by
    rw [eq_bot_iff]
    rintro t ⟨htU, c, hcT, rfl⟩
    have hZ : (QuotientGroup.mk c : CQ U) ∈ cqImg U U :=
      ⟨c, Subgroup.mem_subgroupOf.2 htU, rfl⟩
    have hTm : (QuotientGroup.mk c : CQ U) ∈ T := hmap ▸ Subgroup.mem_map_of_mem _ hcT
    have h1 : (QuotientGroup.mk c : CQ U) = 1 :=
      (Subgroup.mem_bot).1 (hTZ ▸ (⟨hTm, hZ⟩ : _ ∈ T ⊓ cqImg U U))
    have hQc : c ∈ pPrimeCore 3 ↥(CenS U) := (QuotientGroup.eq_one_iff _).1 h1
    have : c = 1 := (Subgroup.mem_bot).1 (hinf ▸ (⟨hcT, hQc⟩ : _ ∈ T' ⊓ pPrimeCore 3 ↥(CenS U)))
    simp [this]
  have hT''el : IsElemAb 3 2 (T'.map (CenS U).subtype) := by
    haveI := hT'.1
    exact ⟨IsElementaryAbelian.map_subtype, by
      rw [Subgroup.card_map_of_injective (CenS U).subtype_injective]; exact hT'.2⟩
  have hA4 := rank2_elemAb_sup hUe hT''el hcomm hUT
  exact ff79_no_rank_four_in_two_local hP''ne hP''2 hA4 hr (sup_le hUN hT''N)

theorem sec34_ap_rank2 (hs : FF79Sec3 b J) (h : FF79Sec34In b J B A P D)
    (hU : FF79Sec34UFacts b a J A) :
    ∀ P T : Subgroup (CQ (U34 b a J A)), IsPGroup 2 P → P ≠ ⊥ → IsElemAb 3 2 T →
      T ⊓ cqImg (U34 b a J A) (U34 b a J A) = ⊥ → T ≤ Nor P → False :=
  rank2_main hU.elemU hs.rank3

end Main

end CFSG.RankThree.PartTwo.Sec21.FF79
