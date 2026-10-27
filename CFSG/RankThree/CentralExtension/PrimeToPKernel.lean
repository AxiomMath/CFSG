module

public import CFSG.RankThree.CentralExtension.ScalarNormalizerKernel
public import CFSG.RankThree.CentralExtension.InvariantFormComplement

public section

namespace CFSG.RankThree.CentralExtension

open Subgroup
open scoped commutatorElement

section Defs

variable {S : Type*} [Group S] {H Q : Subgroup S}

theorem mem_normalizer_of_subgroupOf_normal (hQH : Q ≤ H) [hn : (Q.subgroupOf H).Normal]
    {h : S} (hh : h ∈ H) : h ∈ normalizer (Q : Set S) := by
  rw [mem_normalizer_iff]
  intro q
  have hconj := (normal_subgroupOf_iff hQH).1 hn
  constructor
  · intro hq
    exact hconj q h hq hh
  · intro hq
    have h1 := hconj _ h⁻¹ hq (H.inv_mem hh)
    rwa [inv_inv, show h⁻¹ * (h * q * h⁻¹) * h = q by group] at h1

@[expose] def conjOnNormal (hQH : Q ≤ H) [(Q.subgroupOf H).Normal] (h : H) : MulAut Q :=
  Q.normalizerMonoidHom ⟨h, mem_normalizer_of_subgroupOf_normal hQH h.2⟩

theorem conjOnNormal_apply (hQH : Q ≤ H) [(Q.subgroupOf H).Normal] (h : H) (q : Q) :
    (conjOnNormal hQH h q : S) = h * q * (h : S)⁻¹ :=
  rfl

@[expose] def conjInvariantAltForms (p : ℕ) [Module (ZMod p) (Additive (Abelianization Q))]
    (hQH : Q ≤ H) [(Q.subgroupOf H).Normal] (R : Subgroup (H ⧸ Q.subgroupOf H)) :
    Submodule (ZMod p) (LinearMap.BilinForm (ZMod p) (Additive (Abelianization Q))) where
  carrier := {β | (∀ v, β v v = 0) ∧ ∀ h : H, (h : H ⧸ Q.subgroupOf H) ∈ R → ∀ q q' : Q,
    β (Additive.ofMul (Abelianization.of (conjOnNormal hQH h q)))
        (Additive.ofMul (Abelianization.of (conjOnNormal hQH h q'))) =
      β (Additive.ofMul (Abelianization.of q)) (Additive.ofMul (Abelianization.of q'))}
  add_mem' := by
    rintro β β' ⟨hβ, hβi⟩ ⟨hβ', hβ'i⟩
    refine ⟨fun v => ?_, fun h hh q q' => ?_⟩
    · rw [LinearMap.add_apply, LinearMap.add_apply, hβ v, hβ' v, add_zero]
    · rw [LinearMap.add_apply, LinearMap.add_apply, LinearMap.add_apply, LinearMap.add_apply,
        hβi h hh, hβ'i h hh]
  zero_mem' := ⟨fun _ => rfl, fun _ _ _ _ => rfl⟩
  smul_mem' := by
    rintro c β ⟨hβ, hβi⟩
    refine ⟨fun v => ?_, fun h hh q q' => ?_⟩
    · rw [LinearMap.smul_apply, LinearMap.smul_apply, hβ v, smul_zero]
    · rw [LinearMap.smul_apply, LinearMap.smul_apply, LinearMap.smul_apply,
        LinearMap.smul_apply, hβi h hh]

theorem mem_conjInvariantAltForms {p : ℕ} [Module (ZMod p) (Additive (Abelianization Q))]
    {hQH : Q ≤ H} [(Q.subgroupOf H).Normal] {R : Subgroup (H ⧸ Q.subgroupOf H)}
    {β : LinearMap.BilinForm (ZMod p) (Additive (Abelianization Q))} :
    β ∈ conjInvariantAltForms p hQH R ↔ (∀ v, β v v = 0) ∧
      ∀ h : H, (h : H ⧸ Q.subgroupOf H) ∈ R → ∀ q q' : Q,
        β (Additive.ofMul (Abelianization.of (conjOnNormal hQH h q)))
            (Additive.ofMul (Abelianization.of (conjOnNormal hQH h q'))) =
          β (Additive.ofMul (Abelianization.of q)) (Additive.ofMul (Abelianization.of q')) :=
  Iff.rfl

end Defs

theorem central_cover_extraspecial_normal_prime_to_p_kernel_trivial {p : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) {S : Type*} [Group S] [Finite S] {H Q : Subgroup S}
    (hHsyl : ∃ P : Sylow p S, (P : Subgroup S) ≤ H) (hQH : Q ≤ H) [(Q.subgroupOf H).Normal]
    (hQexp : ∀ q ∈ Q, q ^ p = 1) (hZQ : center Q = commutator Q)
    (hZcard : Nat.card (center Q) = p) (hcyc : ∀ P : Sylow p (H ⧸ Q.subgroupOf H), IsCyclic P)
    [Module (ZMod p) (Additive (Abelianization Q))] (R : Subgroup (H ⧸ Q.subgroupOf H))
    [R.Normal] (hR : (Nat.card R).Coprime p)
    (hRZ : ∀ h : H, (h : H ⧸ Q.subgroupOf H) ∈ R → ∀ z ∈ center Q, conjOnNormal hQH h z = z)
    (hRneg : ∃ h : H, (h : H ⧸ Q.subgroupOf H) ∈ R ∧
      ∀ q : Q, Abelianization.of (conjOnNormal hQH h q) = (Abelianization.of q)⁻¹)
    (hRdim : Module.finrank (ZMod p) (conjInvariantAltForms p hQH R) = 1)
    {X : Type*} [Group X] [Finite X] [Group.IsPerfect X] (π : X →* S)
    (hπ : Function.Surjective π) (hC : π.ker ≤ center X) (hCp : IsPGroup p π.ker) :
    π.ker = ⊥ := by
  classical
  have hQexp' : ∀ q : Q, q ^ p = 1 := fun q => Subtype.ext (by simpa using hQexp q q.2)
  have hQp : IsPGroup p Q := fun q => ⟨1, by rw [pow_one]; exact hQexp' q⟩
  set L : Subgroup X := H.comap π with hLdef
  set U : Subgroup X := Q.comap π with hUdef
  have hUL : U ≤ L := comap_mono hQH
  have hUp : IsPGroup p U := hQp.comap_of_ker_isPGroup π hCp
  have hQnorm : ∀ q ∈ Q, ∀ h ∈ H, h * q * h⁻¹ ∈ Q := fun q hq h hh =>
    (normal_subgroupOf_iff hQH).1 inferInstance q h hq hh
  have hLnorm : ∀ g ∈ L, g ∈ normalizer (U : Set X) := by
    intro g hg
    rw [mem_normalizer_iff]
    intro u
    constructor
    · intro hu
      rw [hUdef, mem_comap, map_mul, map_mul, map_inv]
      exact hQnorm _ hu _ hg
    · intro hu
      have h1 := hQnorm _ hu _ (H.inv_mem (show π g ∈ H from hg))
      rw [map_mul, map_mul, map_inv, inv_inv,
        show (π g)⁻¹ * (π g * π u * (π g)⁻¹) * π g = π u by group] at h1
      exact h1
  let ρ : L →* H ⧸ Q.subgroupOf H := (QuotientGroup.mk' _).comp (π.subgroupComap H)
  have hρ : ∀ x : L, ρ x = ((⟨π x, x.2⟩ : H) : H ⧸ Q.subgroupOf H) := fun _ => rfl
  have hρsurj : Function.Surjective ρ := by
    intro x
    obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨e, he⟩ := hπ h
    refine ⟨⟨e, by rw [hLdef, mem_comap, he]; exact h.2⟩, ?_⟩
    rw [hρ]
    congr 1
    exact Subtype.ext he
  have hρU : ∀ x : L, ρ x = 1 ↔ (x : X) ∈ U := fun x => by
    rw [hρ, QuotientGroup.eq_one_iff, mem_subgroupOf]
    rfl
  have hLp : L.index.Coprime p := by
    obtain ⟨P, hPH⟩ := hHsyl
    rw [hLdef, index_comap_of_surjective H hπ]
    have h2 : ¬ p ∣ (P : Subgroup S).index := P.not_dvd_index
    exact Nat.Coprime.coprime_dvd_left (index_dvd_of_le hPH)
      ((Nat.Prime.coprime_iff_not_dvd hp.out).2 h2).symm
  set ER : Subgroup X := (R.comap ρ).map L.subtype with hERdef
  have hERL : ER ≤ L := map_subtype_le _
  have hmemER : ∀ x (hx : x ∈ L), x ∈ ER ↔ ρ ⟨x, hx⟩ ∈ R := by
    intro x hx
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro h
      exact ⟨⟨x, hx⟩, h, rfl⟩
  have hUER : U ≤ ER := fun u hu => (hmemER u (hUL hu)).2 (by
    rw [(hρU ⟨u, hUL hu⟩).2 hu]; exact R.one_mem)
  have hLER : ∀ g ∈ L, ∀ x ∈ ER, g * x * g⁻¹ ∈ ER := by
    intro g hg x hx
    have hxL := hERL hx
    rw [hmemER _ (L.mul_mem (L.mul_mem hg hxL) (L.inv_mem hg))]
    have h1 := (hmemER x hxL).1 hx
    have h2 : ρ ⟨g * x * g⁻¹, L.mul_mem (L.mul_mem hg hxL) (L.inv_mem hg)⟩ =
        ρ ⟨g, hg⟩ * ρ ⟨x, hxL⟩ * (ρ ⟨g, hg⟩)⁻¹ := by
      rw [← map_inv, ← map_mul, ← map_mul]
      rfl
    rw [h2]
    exact (inferInstance : R.Normal).conj_mem _ h1 _
  set N : Subgroup ER := U.subgroupOf ER with hNdef
  have hNnorm : N.Normal := ⟨fun n hn g => by
    rw [hNdef, mem_subgroupOf] at hn ⊢
    exact (mem_normalizer_iff.1 (hLnorm _ (hERL g.2)) n).1 hn⟩
  let ψ : ER →* R :=
    { toFun := fun x => ⟨ρ ⟨x, hERL x.2⟩, (hmemER x (hERL x.2)).1 x.2⟩
      map_one' := Subtype.ext (map_one ρ)
      map_mul' := fun x y => Subtype.ext (map_mul ρ ⟨x, hERL x.2⟩ ⟨y, hERL y.2⟩) }
  have hψker : ψ.ker = N := by
    ext x
    rw [MonoidHom.mem_ker, hNdef, mem_subgroupOf, ← hρU ⟨x, hERL x.2⟩]
    exact Subtype.ext_iff
  have hψsurj : Function.Surjective ψ := by
    rintro ⟨r, hr⟩
    obtain ⟨e, he⟩ := hρsurj r
    exact ⟨⟨e, (hmemER e e.2).2 (he ▸ hr)⟩, Subtype.ext he⟩
  have hindex : N.index = Nat.card R := by
    rw [← hψker, index_ker, MonoidHom.range_eq_top.2 hψsurj, card_top]
  have hNcard : Nat.card N = Nat.card U := Nat.card_congr (subgroupOfEquivOfLe hUER).toEquiv
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hUp
  have hcop : (Nat.card N).Coprime N.index := by
    rw [hNcard, hk, hindex]
    exact (hR.pow_right k).symm
  obtain ⟨A', hA'⟩ := exists_right_complement'_of_coprime hcop
  set A : Subgroup X := A'.map ER.subtype with hAdef
  have hAER : A ≤ ER := map_subtype_le _
  have hAL : A ≤ L := hAER.trans hERL
  have hAcard : (Nat.card A).Coprime p := by
    have h1 := hA'.card_mul_card
    have h2 := N.card_mul_index
    have h3 : Nat.card A' = N.index := Nat.eq_of_mul_eq_mul_left Nat.card_pos (h1.trans h2.symm)
    rw [hAdef, card_map_of_injective ER.subtype_injective, h3, hindex]
    exact hR
  have hERdec : ∀ x ∈ ER, ∃ u ∈ U, ∃ a ∈ A, x = u * a := by
    intro x hx
    obtain ⟨⟨n, a⟩, hna⟩ := hA'.2 ⟨x, hx⟩
    refine ⟨n, mem_subgroupOf.1 n.2, a, ⟨a, a.2, rfl⟩, ?_⟩
    have h1 := congrArg Subtype.val hna
    simp only [Subgroup.coe_mul] at h1
    exact h1.symm
  have hAR : ∀ a (ha : a ∈ A), ρ ⟨a, hAL ha⟩ ∈ R := fun a ha => (hmemER a (hAL ha)).1 (hAER ha)
  have hRA : ∀ h : H, (h : H ⧸ Q.subgroupOf H) ∈ R →
      ∃ a, ∃ ha : a ∈ A, ∃ q₀ ∈ Q, (h : S) = π a * q₀ := by
    intro h hh
    obtain ⟨e, he⟩ := hπ h
    have heL : e ∈ L := by rw [hLdef, mem_comap, he]; exact h.2
    have heER : e ∈ ER := (hmemER e heL).2 (by
      rw [hρ]
      convert hh using 2
      exact Subtype.ext he)
    obtain ⟨u, hu, a, ha, rfl⟩ := hERdec e heER
    refine ⟨a, ha, (π a)⁻¹ * π u * π a, ?_, ?_⟩
    · have h1 := hQnorm _ hu _ (H.inv_mem (show π a ∈ H from hAL ha))
      rwa [inv_inv] at h1
    · rw [← he, map_mul]
      group
  let φ : A →* MulAut U :=
    (U.normalizerMonoidHom).comp (inclusion fun a ha => hLnorm a (hAL ha))
  have hφapp : ∀ (a : A) (u : U), (φ a u : X) = a * u * (a : X)⁻¹ := fun _ _ => rfl
  let πU : U →* Q := π.subgroupComap Q
  have hπU : ∀ u : U, (πU u : S) = π u := fun _ => rfl
  have hπUsurj : Function.Surjective πU := fun q => by
    obtain ⟨e, he⟩ := hπ q
    exact ⟨⟨e, by rw [hUdef, mem_comap, he]; exact q.2⟩, Subtype.ext he⟩
  have hπUker : ∀ u : U, u ∈ πU.ker ↔ (u : X) ∈ π.ker := fun u => by
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, ← hπU, OneMemClass.coe_eq_one]
  have hCU : πU.ker ≤ center U := fun u hu =>
    mem_center_iff.2 fun g => Subtype.ext (mem_center_iff.1 (hC ((hπUker u).1 hu)) g)
  have hCpU : IsPGroup p πU.ker := by
    intro c
    obtain ⟨j, hj⟩ := hCp ⟨(c : X), (hπUker c).1 c.2⟩
    exact ⟨j, Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val hj))⟩
  have hπφ : ∀ (a : A) (u : U), πU (φ a u) = conjOnNormal hQH ⟨π a, hAL a.2⟩ (πU u) :=
    fun a u => Subtype.ext (by rw [conjOnNormal_apply, hπU, hπU, hφapp, map_mul, map_mul, map_inv])
  have hφC : ∀ a, ∀ c ∈ πU.ker, φ a c = c := fun a c hc => Subtype.ext (by
    rw [hφapp, mem_center_iff.1 (hC ((hπUker c).1 hc)) (a : X), mul_inv_cancel_right])
  have hφZ : ∀ a u, πU u ∈ center Q → πU (φ a u) = πU u := fun a u hu => by
    rw [hπφ]
    exact hRZ _ (hAR a a.2) _ hu
  obtain ⟨h₀, hh₀R, hh₀⟩ := hRneg
  obtain ⟨b, hbA, q₀, hq₀, hb⟩ := hRA h₀ hh₀R
  have hbneg : ∀ u : U, Abelianization.of (πU (φ ⟨b, hbA⟩ u)) =
      (Abelianization.of (πU u))⁻¹ := by
    intro u
    rw [hπφ]
    have e1 : conjOnNormal hQH ⟨π b, hAL hbA⟩ (πU u) =
        conjOnNormal hQH h₀ ((⟨q₀, hq₀⟩ : Q)⁻¹ * πU u * (⟨q₀, hq₀⟩ : Q)) := by
      apply Subtype.ext
      rw [conjOnNormal_apply, conjOnNormal_apply]
      simp only [Subgroup.coe_mul, InvMemClass.coe_inv]
      rw [hb]
      group
    rw [e1, hh₀, map_mul Abelianization.of, map_mul Abelianization.of,
      map_inv Abelianization.of, inv_mul_cancel_comm]
  have hforms : invariantAltForms p πU φ = conjInvariantAltForms p hQH R := by
    ext β
    rw [mem_invariantAltForms, mem_conjInvariantAltForms]
    constructor
    · rintro ⟨hβa, hβi⟩
      refine ⟨hβa, fun h hh q q' => ?_⟩
      obtain ⟨a, ha, q₁, hq₁, hha⟩ := hRA h hh
      obtain ⟨u, hu⟩ := hπUsurj ((⟨q₁, hq₁⟩ : Q) * q * (⟨q₁, hq₁⟩ : Q)⁻¹)
      obtain ⟨u', hu'⟩ := hπUsurj ((⟨q₁, hq₁⟩ : Q) * q' * (⟨q₁, hq₁⟩ : Q)⁻¹)
      have h1 := hβi ⟨a, ha⟩ u u'
      rw [hπφ, hπφ, hu, hu'] at h1
      have e1 : ∀ x : Q, conjOnNormal hQH ⟨π a, hAL ha⟩
          ((⟨q₁, hq₁⟩ : Q) * x * (⟨q₁, hq₁⟩ : Q)⁻¹) = conjOnNormal hQH h x := fun x => by
        apply Subtype.ext
        rw [conjOnNormal_apply, conjOnNormal_apply]
        simp only [Subgroup.coe_mul, InvMemClass.coe_inv]
        rw [hha]
        group
      have hof : ∀ x y : Q, Abelianization.of (x * y * x⁻¹) = Abelianization.of y := by
        intro x y
        rw [map_mul Abelianization.of, map_mul Abelianization.of, map_inv Abelianization.of,
          mul_inv_cancel_comm]
      rw [e1, e1, hof, hof] at h1
      exact h1
    · rintro ⟨hβa, hβi⟩
      refine ⟨hβa, fun a u u' => ?_⟩
      rw [hπφ, hπφ]
      exact hβi ⟨π a, hAL a.2⟩ (hAR a a.2) (πU u) (πU u')
  obtain ⟨-, D₀, ⟨hinv, hsup, hinf⟩, huniq, -, hD₀norm, -, -⟩ :=
    extraspecial_coprime_invariant_form_central_extension_unique_complement hp2 πU hπUsurj hCU
      hCpU hQexp' hZQ hZcard hAcard φ hφC hφZ ⟨b, hbA⟩ hbneg (by rw [hforms]; exact hRdim)
  have hERD : ∀ x (hx : x ∈ ER), ∀ d ∈ D₀,
      U.normalizerMonoidHom ⟨x, hLnorm x (hERL hx)⟩ d ∈ D₀ := by
    intro x hx d hd
    obtain ⟨u, hu, a, ha, rfl⟩ := hERdec x hx
    have h2 := hD₀norm.conj_mem _ (hinv ⟨a, ha⟩ d hd) ⟨u, hu⟩
    convert h2 using 1
    apply Subtype.ext
    change (u * a) * (d : X) * (u * a)⁻¹ = u * (a * d * a⁻¹) * u⁻¹
    group
  have hconjD : ∀ g (hg : g ∈ L), ∀ d ∈ D₀, U.normalizerMonoidHom ⟨g, hLnorm g hg⟩ d ∈ D₀ := by
    intro g hg
    set φg : MulAut U := U.normalizerMonoidHom ⟨g, hLnorm g hg⟩ with hφg
    have hφgapp : ∀ u : U, (φg u : X) = g * u * g⁻¹ := fun _ => rfl
    have hφgC : ∀ c ∈ πU.ker, φg c = c := fun c hc => Subtype.ext (by
      rw [hφgapp, mem_center_iff.1 (hC ((hπUker c).1 hc)) g, mul_inv_cancel_right])
    have hkerφ : πU.ker.map φg.toMonoidHom = πU.ker := by
      ext x
      constructor
      · rintro ⟨c, hc, rfl⟩
        change φg c ∈ πU.ker
        rw [hφgC c hc]
        exact hc
      · intro hx
        exact ⟨x, hx, hφgC x hx⟩
    have hsupg : πU.ker ⊔ D₀.map φg.toMonoidHom = ⊤ := by
      rw [← hkerφ, ← Subgroup.map_sup, hsup, map_top_of_surjective φg.toMonoidHom φg.surjective]
    have hinfg : πU.ker ⊓ D₀.map φg.toMonoidHom = ⊥ := by
      rw [← hkerφ, ← Subgroup.map_inf_eq _ _ φg.toMonoidHom φg.injective, hinf, Subgroup.map_bot]
    have hinvg : ∀ a, ∀ x ∈ D₀.map φg.toMonoidHom, φ a x ∈ D₀.map φg.toMonoidHom := by
      rintro a _ ⟨d, hd, rfl⟩
      have hx : g⁻¹ * a * g ∈ ER := by
        have h1 := hLER g⁻¹ (L.inv_mem hg) a (hAER a.2)
        rwa [inv_inv] at h1
      refine ⟨U.normalizerMonoidHom ⟨g⁻¹ * a * g, hLnorm _ (hERL hx)⟩ d, hERD _ hx d hd, ?_⟩
      apply Subtype.ext
      change g * ((g⁻¹ * a * g) * (d : X) * (g⁻¹ * a * g)⁻¹) * g⁻¹ =
        a * (g * d * g⁻¹) * (a : X)⁻¹
      group
    have hDg := huniq _ hinvg hsupg hinfg
    intro d hd
    rw [← hDg]
    exact ⟨d, hd, rfl⟩
  set D : Subgroup X := D₀.map U.subtype with hDdef
  have hDU : D ≤ U := map_subtype_le D₀
  have hLD : ∀ g ∈ L, ∀ x ∈ D, g * x * g⁻¹ ∈ D := by
    rintro g hg _ ⟨d, hd, rfl⟩
    exact ⟨_, hconjD g hg d hd, rfl⟩
  have hCU' : ∀ u ∈ U, ∃ c ∈ π.ker, c⁻¹ * u ∈ D := by
    intro u hu
    have hu' : (⟨u, hu⟩ : U) ∈ πU.ker ⊔ D₀ := by rw [hsup]; exact mem_top _
    have : πU.ker.Normal := inferInstance
    obtain ⟨c, hc, d, hd, hcd⟩ := mem_sup_of_normal_left.1 hu'
    refine ⟨c, (hπUker c).1 hc, d, hd, ?_⟩
    have h1 := congrArg Subtype.val hcd
    simp only [Subgroup.coe_mul] at h1
    rw [coe_subtype, ← h1, inv_mul_cancel_left]
  have hCD : π.ker ⊓ D = ⊥ := by
    refine eq_bot_iff.2 fun x hx => ?_
    obtain ⟨hxC, d, hd, rfl⟩ := hx
    have h1 : d ∈ πU.ker ⊓ D₀ := ⟨(hπUker d).2 hxC, hd⟩
    rw [hinf, mem_bot] at h1
    rw [h1]
    exact one_mem _
  exact pKernel_eq_bot_of_normalized_complement π hC hCp hcyc hLp D hDU hCD hCU' hLD

end CFSG.RankThree.CentralExtension
