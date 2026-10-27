module

public import CFSG.Sporadic.Recognition.JankoWongCover
public import CFSG.GH74.GLS.Classes
public import CFSG.Adapters.Involutions

public section

namespace CFSG.Sporadic.Recognition.JankoWong

open Equiv Equiv.Perm Subgroup CFSG.GH74 CFSG.GH74.GLS

theorem isCover8_of_isDoubleCoverOfAlt {K : Type} [Group K] (hK : IsDoubleCoverOfAlt K 8)
    {z : K} (hzc : z ∈ Subgroup.center K) (hz1 : z ≠ 1) :
    ∃ ρ : K →* Perm (Fin 8), IsCover8 ρ z := by
  obtain ⟨⟨hperf, -⟩, hcard, ⟨e⟩⟩ := hK
  let ρ : K →* Perm (Fin 8) := (alternatingGroup (Fin 8)).subtype.comp
    (e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K)))
  have hker : ρ.ker = Subgroup.center K := by
    ext k
    simp only [MonoidHom.mem_ker, ρ, MonoidHom.comp_apply, Subgroup.coe_subtype,
      MulEquiv.coe_toMonoidHom, QuotientGroup.mk'_apply]
    constructor
    · intro h1
      have h2 : e (k : K ⧸ Subgroup.center K) = 1 := Subtype.ext h1
      rw [map_eq_one_iff _ e.injective] at h2
      exact (QuotientGroup.eq_one_iff k).mp h2
    · intro h1
      have h2 : (k : K ⧸ Subgroup.center K) = 1 := (QuotientGroup.eq_one_iff k).mpr h1
      rw [h2, map_one]; rfl
  have hord : orderOf z = 2 := by
    have hd : orderOf z ∣ Nat.card (Subgroup.center K) := by
      have := orderOf_dvd_natCard (⟨z, hzc⟩ : Subgroup.center K)
      rwa [Subgroup.orderOf_mk] at this
    rw [hcard] at hd
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with h1 | h1
    · exact absurd (orderOf_eq_one_iff.mp h1) hz1
    · exact h1
  have hzp : Subgroup.zpowers z = Subgroup.center K := by
    have : Finite (Subgroup.center K) := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
    apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hzc)
    rw [Nat.card_zpowers, hord, hcard]
  refine ⟨ρ, ⟨hz1, ?_, hzc, by rw [hker, hzp], ?_, hperf⟩⟩
  · rw [← hord]; exact pow_orderOf_eq_one z
  · ext x
    constructor
    · rintro ⟨k, rfl⟩
      exact (e (k : K ⧸ Subgroup.center K)).2
    · intro hx
      obtain ⟨k, hk⟩ := QuotientGroup.mk_surjective (e.symm ⟨x, hx⟩)
      refine ⟨k, ?_⟩
      have : e (k : K ⧸ Subgroup.center K) = ⟨x, hx⟩ := by
        rw [hk]; exact e.apply_symm_apply _
      exact congrArg Subtype.val this


section Sylow

variable {G : Type} [Group G] [Finite G]

@[expose] def zIn (z : G) : ↥(centralizer ({z} : Set G)) :=
  ⟨z, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩

theorem exists_sylow_central_of_cover8 {z : G} (hz : orderOf z = 2)
    {ρ : ↥(centralizer ({z} : Set G)) →* Perm (Fin 8)} (h : IsCover8 ρ (zIn z)) :
    ∃ S : Sylow 2 G, z ∈ (S : Subgroup G) ∧ ∀ s ∈ (S : Subgroup G), s * z = z * s := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := centralizer ({z} : Set G) with hH
  obtain ⟨S_E⟩ : Nonempty (Sylow 2 ↥H) := inferInstance
  have hP : IsPGroup 2 ↥((S_E : Subgroup ↥H).map H.subtype) := S_E.isPGroup'.map H.subtype
  obtain ⟨S, hPS⟩ := hP.exists_le_sylow
  have hzE_ord : orderOf (zIn z) = 2 := by
    rw [← Subgroup.orderOf_coe]; exact hz
  have hzpow : IsPGroup 2 ↥(zpowers (zIn z)) := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_zpowers, hzE_ord, pow_one]
  have hN_le : zpowers (zIn z) ≤ Subgroup.center ↥H := Subgroup.zpowers_le.mpr h.central
  have : (zpowers (zIn z)).Normal := Subgroup.normal_of_le_center hN_le
  have hzSE : zIn z ∈ (S_E : Subgroup ↥H) := hzpow.le_sylow_of_normal S_E (Subgroup.mem_zpowers _)
  have hzP : z ∈ (S_E : Subgroup ↥H).map H.subtype := ⟨zIn z, hzSE, rfl⟩
  have hzS : z ∈ (S : Subgroup G) := hPS hzP
  have : Nontrivial ↥(S : Subgroup G) := ⟨⟨⟨z, hzS⟩, 1, fun e => by
    have := congrArg Subtype.val e
    simp only [OneMemClass.coe_one] at this
    rw [this, orderOf_one] at hz
    exact absurd hz (by norm_num)⟩⟩
  have hcen := (S.isPGroup').center_nontrivial
  obtain ⟨⟨y', hy'c⟩, hy'1⟩ := exists_ne (1 : ↥(Subgroup.center ↥(S : Subgroup G)))
  set y : G := (y' : G) with hy
  have hyS : y ∈ (S : Subgroup G) := y'.2
  have hy1 : y ≠ 1 := fun e => hy'1 (Subtype.ext (Subtype.ext e))
  have hyc : ∀ s ∈ (S : Subgroup G), s * y = y * s := by
    intro s hs
    have := Subgroup.mem_center_iff.mp hy'c ⟨s, hs⟩
    exact congrArg Subtype.val this
  have hyz : y * z = z * y := (hyc z hzS).symm
  set yE : ↥H := ⟨y, Subgroup.mem_centralizer_singleton_iff.mpr hyz⟩ with hyE
  have hcommE : ∀ e ∈ (S_E : Subgroup ↥H), e * yE = yE * e := by
    intro e he
    apply Subtype.ext
    have : (e : G) ∈ (S : Subgroup G) := hPS ⟨e, he, rfl⟩
    exact hyc _ this
  have hord : ∃ k : ℕ, orderOf yE = 2 ^ k := by
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp S.isPGroup') ⟨y, hyS⟩
    refine ⟨k, ?_⟩
    rw [← Subgroup.orderOf_coe yE]
    exact (Subgroup.orderOf_coe (⟨y, hyS⟩ : (S : Subgroup G))).trans hk
  have hzp2 : IsPGroup 2 ↥(zpowers yE) := by
    obtain ⟨k, hk⟩ := hord
    apply IsPGroup.of_card (n := k)
    rw [Nat.card_zpowers, hk]
  have hnorm : yE ∈ normalizer ((S_E : Subgroup ↥H) : Set ↥H) := by
    rw [Subgroup.mem_normalizer_iff]
    intro e
    constructor
    · intro he
      have : yE * e * yE⁻¹ = e := by rw [← hcommE e he]; group
      rw [this]; exact he
    · intro he
      have h2 : yE⁻¹ * (yE * e * yE⁻¹) * yE = yE * e * yE⁻¹ := by
        have := hcommE _ he
        calc yE⁻¹ * (yE * e * yE⁻¹) * yE = yE⁻¹ * ((yE * e * yE⁻¹) * yE) := by group
          _ = yE⁻¹ * (yE * (yE * e * yE⁻¹)) := by rw [this]
          _ = yE * e * yE⁻¹ := by group
      have h3 : e = yE⁻¹ * (yE * e * yE⁻¹) * yE := by group
      rw [h3, h2]; exact he
  have hyE_SE : yE ∈ (S_E : Subgroup ↥H) := by
    have h1 := hzp2.inf_normalizer_sylow S_E
    have h2 : yE ∈ zpowers yE ⊓ normalizer (S_E : Set ↥H) :=
      ⟨Subgroup.mem_zpowers yE, hnorm⟩
    rw [h1] at h2
    exact h2.2
  have hyzE : y = z := by
    rcases h.eq_one_or_eq_z_of_central S_E hyE_SE hcommE with h1 | h1
    · exact absurd (congrArg Subtype.val h1) hy1
    · exact congrArg Subtype.val h1
  refine ⟨S, hzS, fun s hs => ?_⟩
  rw [← hyzE]
  exact hyc s hs

end Sylow



section OneClass

variable {G : Type} [Group G] [Finite G]

theorem isConj_of_involutions_of_cover8 (hs : IsSimpleGroup G) (hnab : ∃ a b : G, a * b ≠ b * a)
    {z : G} (hz : orderOf z = 2) {ρ : ↥(centralizer ({z} : Set G)) →* Perm (Fin 8)}
    (h : IsCover8 ρ (zIn z)) :
    ∀ u v : G, orderOf u = 2 → orderOf v = 2 → IsConj u v := by
  classical
  have hz1 : z ≠ 1 := fun e => by
    rw [e, orderOf_one] at hz; exact absurd hz (by norm_num)
  have hz2 : z ^ 2 = 1 := by rw [← hz]; exact pow_orderOf_eq_one z
  obtain ⟨S, hzS, hzcent⟩ := exists_sylow_central_of_cover8 hz h
  have hiso : ∃ g : G, g⁻¹ * z * g ∈ (S : Subgroup G) ∧ g⁻¹ * z * g ≠ z := by
    by_contra hno
    push Not at hno
    have hzS' : (⟨z, hzS⟩ : ↥(S : Subgroup G)) ∈ Subgroup.center ↥(S : Subgroup G) := by
      rw [Subgroup.mem_center_iff]
      intro s
      exact Subtype.ext (hzcent s.1 s.2)
    have hord' : orderOf (⟨z, hzS⟩ : ↥(S : Subgroup G)) = 2 := by
      rw [← Subgroup.orderOf_coe]; exact hz
    obtain ⟨-, hcen⟩ := CFSG.Adapters.glauberman_zStar S ⟨z, hzS⟩ hzS' hord' hno
    have hbot : CFSG.oddCore G = ⊥ := by
      rcases hs.eq_bot_or_eq_top_of_normal (CFSG.oddCore G) with h1 | h1
      · exact h1
      · exfalso
        apply CFSG.Adapters.not_mem_oddCore_of_orderOf_eq_two hz
        rw [h1]; exact Subgroup.mem_top z
    have hcom : ∀ g : G, g * z = z * g := by
      intro g
      have h1 := Subgroup.mem_center_iff.mp hcen (QuotientGroup.mk g)
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, hbot,
        Subgroup.mem_bot, inv_mul_eq_one] at h1
      exact h1
    have hzc : z ∈ Subgroup.center G := Subgroup.mem_center_iff.mpr fun g => hcom g
    rcases hs.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h1 | h1
    · rw [h1, Subgroup.mem_bot] at hzc; exact hz1 hzc
    · obtain ⟨a, b, hab⟩ := hnab
      apply hab
      have : a ∈ Subgroup.center G := by rw [h1]; exact Subgroup.mem_top a
      exact (Subgroup.mem_center_iff.mp this b).symm
  obtain ⟨g, hgS, hgz⟩ := hiso
  have hguH : g⁻¹ * z * g ∈ centralizer ({z} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (hzcent _ hgS)
  set uE : ↥(centralizer ({z} : Set G)) := ⟨g⁻¹ * z * g, hguH⟩ with huE
  have huE2 : uE ^ 2 = 1 := by
    apply Subtype.ext
    show (g⁻¹ * z * g) ^ 2 = 1
    have : (g⁻¹ * z * g) ^ 2 = g⁻¹ * z ^ 2 * g := by
      rw [pow_two, pow_two]; simp [mul_assoc]
    rw [this, hz2]; simp
  have huE1 : uE ≠ 1 := fun e => hz1 (by
    have h1 : g⁻¹ * z * g = 1 := congrArg Subtype.val e
    have h2 : z = g * (g⁻¹ * z * g) * g⁻¹ := by group
    rw [h2, h1]; group)
  have huEz : uE ≠ zIn z := fun e => hgz (congrArg Subtype.val e)
  have key : ∀ v : G, orderOf v = 2 → IsConj v z := by
    intro v hv
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hvp : IsPGroup 2 ↥(zpowers v) := by
      apply IsPGroup.of_card (n := 1)
      rw [Nat.card_zpowers, hv, pow_one]
    obtain ⟨S', hS'⟩ := hvp.exists_le_sylow
    obtain ⟨x, hx⟩ := MulAction.exists_smul_eq G S' S
    have hmem : MulAut.conj x • v ∈ ((x • S' : Sylow 2 G) : Subgroup G) := by
      rw [Sylow.coe_subgroup_smul]
      exact Subgroup.smul_mem_pointwise_smul _ _ _ (hS' (Subgroup.mem_zpowers v))
    rw [hx] at hmem
    have hmem' : x * v * x⁻¹ ∈ (S : Subgroup G) := by simpa using hmem
    have hv2 : v ^ 2 = 1 := by rw [← hv]; exact pow_orderOf_eq_one v
    have hv'2 : (x * v * x⁻¹) ^ 2 = 1 := by
      have : (x * v * x⁻¹) ^ 2 = x * v ^ 2 * x⁻¹ := by
        rw [pow_two, pow_two]; simp [mul_assoc]
      rw [this, hv2]; simp
    have hv1 : v ≠ 1 := fun e => by rw [e, orderOf_one] at hv; exact absurd hv (by norm_num)
    have hv'H : x * v * x⁻¹ ∈ centralizer ({z} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr (hzcent _ hmem')
    have hv'conj : IsConj (x * v * x⁻¹) z := by
      by_cases hvz : x * v * x⁻¹ = z
      · rw [hvz]
      · set vE : ↥(centralizer ({z} : Set G)) := ⟨x * v * x⁻¹, hv'H⟩ with hvE
        have hvE2 : vE ^ 2 = 1 := Subtype.ext hv'2
        have hvE1 : vE ≠ 1 := fun e => hv1 (by
          have h1 : x * v * x⁻¹ = 1 := congrArg Subtype.val e
          have h2 : v = x⁻¹ * (x * v * x⁻¹) * x := by group
          rw [h2, h1]; group)
        have hvEz : vE ≠ zIn z := fun e => hvz (congrArg Subtype.val e)
        obtain ⟨c, hc⟩ := h.exists_conj_of_involutions huE2 huE1 huEz hvE2 hvE1 hvEz
        have hc' : (c : G) * (g⁻¹ * z * g) * (c : G)⁻¹ = x * v * x⁻¹ := congrArg Subtype.val hc
        exact isConj_iff.mpr ⟨g * (c : G)⁻¹, by
          calc g * (c : G)⁻¹ * (x * v * x⁻¹) * (g * (c : G)⁻¹)⁻¹
              = g * (c : G)⁻¹ * ((c : G) * (g⁻¹ * z * g) * (c : G)⁻¹) * (g * (c : G)⁻¹)⁻¹ := by
                rw [hc']
            _ = z := by group⟩
    exact (isConj_iff.mpr ⟨x, rfl⟩ : IsConj v (x * v * x⁻¹)).trans hv'conj
  intro u v hu hv
  exact (key u hu).trans (key v hv).symm

end OneClass


section Assembly

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem zIn_mem_center (z : G) : zIn z ∈ Subgroup.center ↥(centralizer ({z} : Set G)) :=
  Subgroup.mem_center_iff.mpr fun g =>
    Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp g.2)

omit [Finite G] in
instance normal_zpowers_zIn (z : G) : (zpowers (zIn z)).Normal :=
  Subgroup.normal_of_le_center (Subgroup.zpowers_le.mpr (zIn_mem_center z))

theorem alternatingGroup_fin_eight_nonabelian :
    ∃ a b : alternatingGroup (Fin 8), a * b ≠ b * a := by
  by_contra hcon
  push Not at hcon
  have : IsMulCommutative (alternatingGroup (Fin 8)) := ⟨⟨fun a b => hcon a b⟩⟩
  have h8 := (alternatingGroup.isMulCommutative_iff_card_le_three (α := Fin 8)).mp this
  simp at h8

theorem isCentralInvolution_and_oneClass_of_doubleCover (hs : IsSimpleGroup G)
    (hnab : ∃ a b : G, a * b ≠ b * a) {z : G} (hz : orderOf z = 2)
    (hH : IsDoubleCoverOfAlt ↥(centralizer ({z} : Set G)) 8) :
    IsCentralInvolution z ∧ ∀ u v : G, orderOf u = 2 → orderOf v = 2 → IsConj u v := by
  have hz1 : z ≠ 1 := fun e => by
    rw [e, orderOf_one] at hz; exact absurd hz (by norm_num)
  obtain ⟨ρ, hρ⟩ := isCover8_of_isDoubleCoverOfAlt hH (zIn_mem_center z)
    (fun e => hz1 (congrArg Subtype.val e))
  exact ⟨⟨hz, exists_sylow_central_of_cover8 hz hρ⟩,
    isConj_of_involutions_of_cover8 hs hnab hz hρ⟩

omit [Finite G] in
theorem isDoubleCoverOfAlt_of_perfect_centralizer {t : G} (ht : orderOf t = 2)
    (hperf : Group.IsPerfect ↥(centralizer ({t} : Set G)))
    (hcen : Subgroup.center ↥(centralizer ({t} : Set G)) = zpowers (zIn t))
    (hquot : Nonempty (↥(centralizer ({t} : Set G)) ⧸ zpowers (zIn t) ≃*
      alternatingGroup (Fin 8))) :
    IsDoubleCoverOfAlt ↥(centralizer ({t} : Set G)) 8 := by
  obtain ⟨e⟩ := hquot
  have hnc : Subgroup.center ↥(centralizer ({t} : Set G)) = zpowers (zIn t) := hcen
  let e' : ↥(centralizer ({t} : Set G)) ⧸ Subgroup.center ↥(centralizer ({t} : Set G)) ≃*
      alternatingGroup (Fin 8) := (QuotientGroup.quotientMulEquivOfEq hnc).trans e
  have : IsSimpleGroup (alternatingGroup (Fin 8)) := alternatingGroup.isSimpleGroup (by simp)
  refine ⟨⟨hperf, e'.isSimpleGroup, ?_⟩, ?_, ⟨e'⟩⟩
  · obtain ⟨a, b, hab⟩ := alternatingGroup_fin_eight_nonabelian
    refine ⟨e'.symm a, e'.symm b, fun hc => hab ?_⟩
    have := congrArg e' hc
    simpa using this
  · rw [hnc, Nat.card_zpowers]; exact (Subgroup.orderOf_coe (zIn t)).symm.trans ht

theorem oneClassDoubleCover_of_perfect_centralizer (hs : IsSimpleGroup G)
    (hnab : ∃ a b : G, a * b ≠ b * a) {t : G} (ht : orderOf t = 2)
    (hperf : Group.IsPerfect ↥(centralizer ({t} : Set G)))
    (hcen : Subgroup.center ↥(centralizer ({t} : Set G)) = zpowers (zIn t))
    (hquot : Nonempty (↥(centralizer ({t} : Set G)) ⧸ zpowers (zIn t) ≃*
      alternatingGroup (Fin 8))) :
    IsCentralInvolution t ∧ (∀ u v : G, orderOf u = 2 → orderOf v = 2 → IsConj u v) ∧
      IsDoubleCoverOfAlt ↥(centralizer ({t} : Set G)) 8 := by
  have hH := isDoubleCoverOfAlt_of_perfect_centralizer ht hperf hcen hquot
  obtain ⟨h1, h2⟩ := isCentralInvolution_and_oneClass_of_doubleCover hs hnab ht hH
  exact ⟨h1, h2, hH⟩

end Assembly

end CFSG.Sporadic.Recognition.JankoWong
