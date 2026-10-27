module

public import CFSG.RankThree.PartTwo.Sec14.Item14Res2ProofPGL
import CFSG.RankThree.PartOne.S11d.BenderLemma
import CFSG.RankThree.GroupTheory.SteinbergBYRelativeCores
import CFSG.RankThree.PartTwo.Sec14.Item142ResProofCore
import CFSG.RankThree.PartTwo.Sec16.Item1613StepsProofTrans

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
  CFSG.RankThree.LocalRank CFSG.GH74.GLS

namespace Res3PGL

open Subgroup
open scoped commutatorElement

section Bender

variable {X : Type*} [Group X] [Finite X]

omit [Finite X] in
theorem eq_one_of_mem_coprime {p : ℕ} (hp : p.Prime) {S Y : Subgroup X}
    (hS : ¬ p ∣ Nat.card S) (hY : IsPGroup p Y) {g : X} (hgS : g ∈ S) (hgY : g ∈ Y) : g = 1 := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨m, hm⟩ := hY ⟨g, hgY⟩
  have h2 : g ^ (p ^ m) = 1 := by simpa using congrArg Subtype.val hm
  have h3 : orderOf g ∣ Nat.card S := Subgroup.orderOf_dvd_natCard S hgS
  have h4 : orderOf g ∣ p ^ m := orderOf_dvd_of_pow_eq_one h2
  have hcop : Nat.Coprime (Nat.card S) (p ^ m) :=
    Nat.Coprime.pow_right _ ((Nat.Prime.coprime_iff_not_dvd hp).mpr hS).symm
  have h5 : orderOf g ∣ Nat.gcd (Nat.card S) (p ^ m) := Nat.dvd_gcd h3 h4
  rw [hcop.gcd_eq_one] at h5
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h5)

theorem commutator_pCore_eq_bot {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {A S : Subgroup X}
    (hA : IsPGroup p A) (hS : ¬ p ∣ Nat.card S) (hAS : A ≤ normalizer (S : Set X))
    (hF3 : ∀ d : X, d ^ p = 1 → (∀ a ∈ A, a * d = d * a) → d ∈ A) :
    ⁅S, CFSG.pCore p X⁆ = ⊥ := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  set Y := CFSG.pCore p X with hYdef
  have hYn : Y.Normal := CFSG.pCore_normal
  have hYp : IsPGroup p Y := CFSG.pCore_isPGroup
  by_cases hY : Y = ⊥
  · rw [hY, Subgroup.commutator_bot_right]
  have : Nontrivial ↥Y := (Subgroup.nontrivial_iff_ne_bot Y).mpr hY
  obtain ⟨D, hDchar, -, hDcl, hDexp, hDfix⟩ :=
    CFSG.SectionRank.Ccomm.odd_critical_exponent_subgroup (P := ↥Y) hp2 hYp
  set D' : Subgroup X := D.map Y.subtype with hD'
  have hD'norm : ∀ g : X, ∀ x : X, x ∈ D' → g * x * g⁻¹ ∈ D' := by
    intro g x hx
    obtain ⟨d, hd, rfl⟩ := Subgroup.mem_map.mp hx
    have hfix := hDchar.fixed (MulAut.conjNormal (H := Y) g)
    have hd' : (MulAut.conjNormal (H := Y) g) d ∈ D := by
      have : d ∈ D.comap (MulAut.conjNormal (H := Y) g).toMonoidHom := by rw [hfix]; exact hd
      exact this
    exact Subgroup.mem_map.mpr ⟨_, hd', by simp [MulAut.conjNormal_apply]⟩
  have hD'N : ∀ H : Subgroup X, H ≤ normalizer (D' : Set X) := by
    intro H g _
    rw [mem_normalizer_iff]
    intro x
    refine ⟨hD'norm g x, fun hx => ?_⟩
    have := hD'norm g⁻¹ _ hx
    simpa [mul_assoc] using this
  have hD'exp : ∀ x ∈ D', x ^ p = 1 := by
    intro x hx
    obtain ⟨d, hd, rfl⟩ := Subgroup.mem_map.mp hx
    have := congrArg Subtype.val (show d ^ p = 1 from hDexp d hd)
    simpa using this
  have hD'cl : ∀ x ∈ D', ∀ y ∈ D', ∀ z ∈ D', ⁅x, y⁆ * z = z * ⁅x, y⁆ := by
    intro x₀ hx₀ y₀ hy₀ z₀ hz₀
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hx₀
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hy₀
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hz₀
    have h1 : ⁅x, y⁆ ∈ ⁅D, (⊤ : Subgroup ↥Y)⁆ := Subgroup.commutator_mem_commutator hx trivial
    have h2 := (hDcl h1).2
    have h3 : z * ⁅x, y⁆ = ⁅x, y⁆ * z := Subgroup.mem_centralizer_iff.mp h2 z hz
    have := congrArg Subtype.val h3.symm
    simpa [commutatorElement_def] using this
  have hSD' : ∀ s ∈ S, ∀ d ∈ D', s * d * s⁻¹ = d := by
    by_contra hno
    push Not at hno
    obtain ⟨d, hdD, hdfix, s, hs, hmove⟩ :=
      CFSG.RankThree.PartOne.S11d.exists_fixed_moved hp hp2 hD'exp hD'cl hA hS
        (hD'N A) (hD'N S) hAS hno
    have hdY : d ∈ Y := by
      obtain ⟨y, -, rfl⟩ := Subgroup.mem_map.mp hdD
      exact y.2
    have hdA : d ∈ A := hF3 d (hD'exp d hdD) (fun a ha => by
      have := hdfix a ha
      calc a * d = a * d * a⁻¹ * a := by group
        _ = d * a := by rw [this])
    apply hmove
    have h1 : s * d * s⁻¹ * d⁻¹ ∈ Y := Y.mul_mem (hYn.conj_mem d hdY s) (Y.inv_mem hdY)
    have h2 : s * d * s⁻¹ * d⁻¹ ∈ S := by
      have : s * d * s⁻¹ * d⁻¹ = s * (d * s⁻¹ * d⁻¹) := by group
      rw [this]
      exact S.mul_mem hs ((mem_normalizer_iff.mp (hAS hdA) s⁻¹).mp (S.inv_mem hs))
    have h3 := eq_one_of_mem_coprime hp hS hYp h2 h1
    calc s * d * s⁻¹ = (s * d * s⁻¹ * d⁻¹) * d := by group
      _ = d := by rw [h3, one_mul]
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro s hs
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have hσ : MulAut.conjNormal (H := Y) s ∈ fixingSubgroup (MulAut ↥Y) (D : Set ↥Y) := by
    rw [mem_fixingSubgroup_iff]
    intro d hd
    apply Subtype.ext
    change ((MulAut.conjNormal (H := Y) s d : ↥Y) : X) = d
    rw [MulAut.conjNormal_apply]
    exact hSD' s hs d (Subgroup.mem_map.mpr ⟨d, hd, rfl⟩)
  have hord2 : orderOf (MulAut.conjNormal (H := Y) s) ∣ orderOf s := orderOf_map_dvd _ s
  have hsS : orderOf s ∣ Nat.card S := Subgroup.orderOf_dvd_natCard S hs
  obtain ⟨m, hm⟩ := hDfix ⟨_, hσ⟩
  have hσp : orderOf (MulAut.conjNormal (H := Y) s) ∣ p ^ m := by
    have : (⟨_, hσ⟩ : ↥(fixingSubgroup (MulAut ↥Y) (D : Set ↥Y))) ^ (p ^ m) = 1 := hm
    have h1 : (MulAut.conjNormal (H := Y) s) ^ (p ^ m) = 1 := by
      simpa using congrArg Subtype.val this
    exact orderOf_dvd_of_pow_eq_one h1
  have hcop : Nat.Coprime (Nat.card S) (p ^ m) :=
    Nat.Coprime.pow_right _ ((Nat.Prime.coprime_iff_not_dvd hp).mpr hS).symm
  have h5 : orderOf (MulAut.conjNormal (H := Y) s) ∣ Nat.gcd (Nat.card S) (p ^ m) :=
    Nat.dvd_gcd (hord2.trans hsS) hσp
  rw [hcop.gcd_eq_one] at h5
  have h6 : MulAut.conjNormal (H := Y) s = 1 := orderOf_eq_one_iff.mp (Nat.dvd_one.mp h5)
  have h7 := congrArg (fun φ : MulAut ↥Y => ((φ ⟨y, hy⟩ : ↥Y) : X)) h6
  simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h7
  have h7' : s * y * s⁻¹ = y := h7
  calc y * s = (s * y * s⁻¹) * s := by rw [h7']
    _ = s * y := by group

end Bender

section Maximal

variable {G : Type*} [Group G]

theorem mem_of_commute_of_maximal {A : Subgroup G} (hAel : CFSG.Assembly.IsElemAbelian 3 A)
    (hAmax : ∀ B : Subgroup G, CFSG.Assembly.IsElemAbelian 3 B → A ≤ B → B = A) {z : G}
    (hz3 : z ^ 3 = 1) (hzA : ∀ x ∈ A, z * x = x * z) : z ∈ A := by
  set D := Subgroup.zpowers z with hD
  have hDN : D ≤ Subgroup.normalizer (A : Set G) := by
    rw [hD, Subgroup.zpowers_le]
    exact Subgroup.centralizer_le_normalizer _
      (Subgroup.mem_centralizer_iff.mpr fun g hg => (hzA g hg).symm)
  have hdecomp : ∀ y ∈ A ⊔ D, ∃ w ∈ D, ∃ u ∈ A, w * u = y := by
    intro y hy
    rw [sup_comm, ← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right D A hDN] at hy
    obtain ⟨w, hw, u, hu, rfl⟩ := hy
    exact ⟨w, hw, u, hu, rfl⟩
  have hcommD : ∀ w ∈ D, ∀ u ∈ A, w * u = u * w := by
    intro w hw u hu
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    exact ((show Commute z u from hzA u hu).zpow_left k).eq
  have hDexp : ∀ w ∈ D, w ^ 3 = 1 := by
    intro w hw
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hz3, one_zpow]
  have hDcomm : ∀ w ∈ D, ∀ w' ∈ D, w * w' = w' * w := by
    intro w hw w' hw'
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    obtain ⟨k', rfl⟩ := Subgroup.mem_zpowers_iff.mp hw'
    exact (Commute.zpow_zpow_self z k k').eq
  have hAcomm : ∀ u ∈ A, ∀ u' ∈ A, u * u' = u' * u := fun u hu u' hu' =>
    congrArg Subtype.val (hAel.1.is_comm.comm ⟨u, hu⟩ ⟨u', hu'⟩)
  have hel : CFSG.Assembly.IsElemAbelian 3 (A ⊔ D) := by
    refine ⟨⟨⟨fun y y' => Subtype.ext ?_⟩⟩, fun y hy => ?_⟩
    · obtain ⟨w, hw, u, hu, hwu⟩ := hdecomp y y.2
      obtain ⟨w', hw', u', hu', hwu'⟩ := hdecomp y' y'.2
      rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hwu, ← hwu']
      have h1 : Commute (w * u) (w' * u') := by
        apply Commute.mul_left
        · exact Commute.mul_right (hDcomm w hw w' hw') (hcommD w hw u' hu')
        · exact Commute.mul_right (hcommD w' hw' u hu).symm (hAcomm u hu u' hu')
      exact h1.eq
    · obtain ⟨w, hw, u, hu, rfl⟩ := hdecomp y hy
      rw [(show Commute w u from hcommD w hw u hu).mul_pow, hDexp w hw, hAel.2 u hu, one_mul]
  have hAD : A ⊔ D = A := hAmax _ hel le_sup_left
  exact hAD ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers z)

end Maximal

section Lift

variable {C : Type*} [Group C] [Finite C] {p : ℕ} [Fact p.Prime]

theorem exists_pSubgroup_lift (N : Subgroup C) [N.Normal] {A₀ : Subgroup C}
    (hA₀ : IsPGroup p A₀) {E : Subgroup (C ⧸ N)} (hE : IsPGroup p E)
    (hAE : A₀.map (QuotientGroup.mk' N) ≤ E) :
    ∃ P : Subgroup C, IsPGroup p P ∧ A₀ ≤ P ∧ P.map (QuotientGroup.mk' N) = E := by
  classical
  set π := QuotientGroup.mk' N with hπ
  set M : Subgroup C := E.comap π with hM
  have hA₀M : A₀ ≤ M := fun a ha => hAE ⟨a, ha, rfl⟩
  let f : ↥M →* C ⧸ N := π.comp M.subtype
  have hfrange : f.range = E := by
    ext e
    constructor
    · rintro ⟨m, rfl⟩
      exact m.2
    · intro he
      obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective e
      exact ⟨⟨c, he⟩, rfl⟩
  have hA₀' : IsPGroup p (A₀.subgroupOf M) := hA₀.comap_subtype
  obtain ⟨P₀, hP₀⟩ := hA₀'.exists_le_sylow
  set Q₀ : Subgroup ↥M := (P₀ : Subgroup ↥M) with hQ₀
  refine ⟨Q₀.map M.subtype, P₀.2.map _, ?_, ?_⟩
  · intro a ha
    exact ⟨⟨a, hA₀M ha⟩, hP₀ (Subgroup.mem_subgroupOf.mpr ha), rfl⟩
  · have hpf : IsPGroup p f.range := by
      intro x
      obtain ⟨k, hk⟩ := hE ⟨x.1, by rw [← hfrange]; exact x.2⟩
      exact ⟨k, Subtype.ext (by simpa using congrArg Subtype.val hk)⟩
    have hf' : Function.Surjective f.rangeRestrict := MonoidHom.rangeRestrict_surjective f
    have hT := (P₀.mapSurjective hf').is_maximal' (Q := ⊤) (hpf.to_subgroup ⊤) le_top
    have hmap : Q₀.map f.rangeRestrict = ⊤ := hT.symm
    have hf'' : f = f.range.subtype.comp f.rangeRestrict := by ext; rfl
    have key : Q₀.map f = f.range := by
      calc Q₀.map f = (Q₀.map f.rangeRestrict).map f.range.subtype := by
            rw [Subgroup.map_map, ← hf'']
        _ = (⊤ : Subgroup f.range).map f.range.subtype := by rw [hmap]
        _ = f.range := by rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
    calc (Q₀.map M.subtype).map π = Q₀.map f := by rw [Subgroup.map_map]
      _ = f.range := key
      _ = E := hfrange

end Lift

section F3

variable {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

omit [Finite G] [Fact p.Prime] in
theorem exists_eq_mul_zpow_of_mem_sup {H : Type*} [Group H] {B : Subgroup H} {c : H}
    (h : ∀ β ∈ B, Commute β c) {a : H} (ha : a ∈ B ⊔ Subgroup.zpowers c) :
    ∃ β ∈ B, ∃ j : ℤ, a = β * c ^ j := by
  have hDN : Subgroup.zpowers c ≤ Subgroup.normalizer (B : Set H) := by
    rw [Subgroup.zpowers_le]
    exact Subgroup.centralizer_le_normalizer _
      (Subgroup.mem_centralizer_iff.mpr fun g hg => (h g hg).eq)
  rw [sup_comm, ← SetLike.mem_coe,
    Subgroup.coe_mul_of_left_le_normalizer_right (Subgroup.zpowers c) B hDN] at ha
  obtain ⟨w, hw, u, hu, rfl⟩ := ha
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
  exact ⟨u, hu, j, ((h u hu).zpow_right j).eq.symm⟩

theorem mem_image_of_centralizes {C : Subgroup G} (N : Subgroup ↥C) [N.Normal]
    (hN : ¬ p ∣ Nat.card N) {A : Subgroup G} (hAC : A ≤ C) [hA : IsElementaryAbelian p A]
    (hF3 : ∀ u : G, u ∈ Subgroup.centralizer (A : Set G) → u ^ p = 1 → u ∈ A)
    {d : ↥C ⧸ N} (hd : d ^ p = 1)
    (hcomm : ∀ a ∈ (A.subgroupOf C).map (QuotientGroup.mk' N), a * d = d * a) :
    d ∈ (A.subgroupOf C).map (QuotientGroup.mk' N) := by
  classical
  set π := QuotientGroup.mk' N with hπ
  set AC : Subgroup ↥C := A.subgroupOf C with hAC'
  set AX : Subgroup (↥C ⧸ N) := AC.map π with hAX
  have hACcomm : ∀ x ∈ AC, ∀ y ∈ AC, x * y = y * x := by
    intro x hx y hy
    have h := congrArg Subtype.val (hA.is_comm.comm
      (⟨(x : G), Subgroup.mem_subgroupOf.mp hx⟩ : A) ⟨(y : G), Subgroup.mem_subgroupOf.mp hy⟩)
    exact Subtype.ext h
  have hApow : ∀ x ∈ AC, x ^ p = 1 := by
    intro x hx
    have h := elemPow_eq_one_of_isElementaryAbelian (p := p) (A := A) (x : G)
      (Subgroup.mem_subgroupOf.mp hx)
    exact Subtype.ext (by simpa using h)
  have hAXcomm : ∀ β ∈ AX, ∀ β' ∈ AX, β * β' = β' * β := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, hACcomm x hx y hy]
  have hAXpow : ∀ β ∈ AX, β ^ p = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, hApow x hx, map_one]
  have hAXd : ∀ β ∈ AX, Commute β d := fun β hβ => hcomm β hβ
  set E : Subgroup (↥C ⧸ N) := AX ⊔ Subgroup.zpowers d with hE
  have hEel : ∀ e ∈ E, ∃ β ∈ AX, ∃ j : ℤ, e = β * d ^ j := fun e he =>
    exists_eq_mul_zpow_of_mem_sup hAXd he
  have hEcomm : ∀ e ∈ E, ∀ e' ∈ E, e * e' = e' * e := by
    intro e he e' he'
    obtain ⟨β, hβ, j, rfl⟩ := hEel e he
    obtain ⟨β', hβ', j', rfl⟩ := hEel e' he'
    have h1 : Commute β β' := hAXcomm β hβ β' hβ'
    have h2 : Commute β (d ^ j') := (hAXd β hβ).zpow_right j'
    have h3 : Commute (d ^ j) β' := ((hAXd β' hβ').symm).zpow_left j
    have h4 : Commute (d ^ j) (d ^ j') := Commute.zpow_zpow_self d j j'
    exact ((h1.mul_left h3).mul_right (h2.mul_left h4)).eq
  have hEpow : ∀ e ∈ E, e ^ p = 1 := by
    intro e he
    obtain ⟨β, hβ, j, rfl⟩ := hEel e he
    have hc : Commute β (d ^ j) := (hAXd β hβ).zpow_right j
    have hdj : (d ^ j) ^ p = 1 := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hd, one_zpow]
    rw [hc.mul_pow, hAXpow β hβ, hdj, one_mul]
  have hEp : IsPGroup p E := fun x => ⟨1, Subtype.ext (by simpa using hEpow x x.2)⟩
  have hACp : IsPGroup p AC := (IsElementaryAbelian.isPGroup p A).comap_subtype
  obtain ⟨P, hPp, hAP, hPE⟩ := exists_pSubgroup_lift N hACp hEp (le_sup_left : AX ≤ E)
  have hinj : ∀ x ∈ P, π x = 1 → x = 1 := by
    intro x hx h1
    have hxN : x ∈ N := (QuotientGroup.eq_one_iff x).mp h1
    obtain ⟨k, hk⟩ := hPp ⟨x, hx⟩
    have h2 : x ^ (p ^ k) = 1 := by simpa using congrArg Subtype.val hk
    have h3 : orderOf x ∣ p ^ k := orderOf_dvd_of_pow_eq_one h2
    have h4 : orderOf x ∣ Nat.card N := by
      have := orderOf_dvd_natCard (⟨x, hxN⟩ : N)
      rwa [Subgroup.orderOf_mk] at this
    have hcop : Nat.Coprime (p ^ k) (Nat.card N) :=
      Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hN)
    have h5 : orderOf x ∣ Nat.gcd (p ^ k) (Nat.card N) := Nat.dvd_gcd h3 h4
    rw [hcop.gcd_eq_one] at h5
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h5)
  have hπP : ∀ x ∈ P, π x ∈ E := fun x hx => hPE ▸ Subgroup.mem_map_of_mem π hx
  have hPcomm : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x := by
    intro x hx y hy
    have hz : x * y * (y * x)⁻¹ ∈ P := P.mul_mem (P.mul_mem hx hy) (P.inv_mem (P.mul_mem hy hx))
    have h1 : π (x * y * (y * x)⁻¹) = 1 := by
      rw [map_mul, map_mul, map_inv, map_mul, hEcomm _ (hπP x hx) _ (hπP y hy), mul_inv_cancel]
    have := hinj _ hz h1
    exact mul_inv_eq_one.mp this
  have hPpow : ∀ x ∈ P, x ^ p = 1 := by
    intro x hx
    apply hinj _ (P.pow_mem hx p)
    rw [map_pow, hEpow _ (hπP x hx)]
  have hPA : P ≤ AC := by
    intro x hx
    rw [hAC', Subgroup.mem_subgroupOf]
    apply hF3
    · rw [Subgroup.mem_centralizer_iff]
      intro a ha
      have hmem : (⟨a, hAC ha⟩ : ↥C) ∈ P := hAP (Subgroup.mem_subgroupOf.mpr ha)
      exact congrArg Subtype.val (hPcomm _ hmem x hx)
    · simpa using congrArg Subtype.val (hPpow x hx)
  have hEA : E ≤ AX := by
    rw [← hPE]
    exact Subgroup.map_mono hPA
  exact hEA (Subgroup.mem_sup_right (Subgroup.mem_zpowers d))

end F3

end Res3PGL

open Res3PGL

theorem step142PGLCentO3 : Step142PGLCentO3 := by
  intro G _ _ A c L h hPGL W hWC hW3 hAW
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set M := Subgroup.centralizer ({c} : Set G) with hM
  set T := thetaQuotCentralizer L with hT
  set N := CFSG.pPrimeCore 3 ↥M with hN
  set ψ := QuotientGroup.mk' N with hψ
  have hD := h.toSec13Data
  have hAM : A ≤ M := hD.A_le_centralizer
  have hAel : CFSG.Assembly.IsElemAbelian 3 A := hD.isElemAbelian
  have hAcomm : IsMulCommutative ↥A := hAel.1
  have hAinst : CFSG.IsElementaryAbelian 3 ↥A :=
    { toIsMulCommutative := hAcomm
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x =>
        Subtype.ext (by simpa using hAel.2 x x.2) }
  have hF3G : ∀ u : G, u ∈ Subgroup.centralizer (A : Set G) → u ^ 3 = 1 → u ∈ A := by
    intro u hu hu3
    refine mem_of_commute_of_maximal hAel (fun B hB hAB => hD.eq_of_le hB hAB) hu3 ?_
    intro x hx
    exact (Subgroup.mem_centralizer_iff.mp hu x hx).symm
  have hN3 : ¬ 3 ∣ Nat.card N := fun h3 =>
    Nat.Prime.not_coprime_iff_dvd.mpr ⟨3, Nat.prime_three, dvd_rfl, h3⟩
      (CFSG.pPrimeCore_coprime_card (p := 3) (G := ↥M))
  have hF3 : ∀ d : ↥M ⧸ N, d ^ 3 = 1 → (∀ a ∈ aStar142 c A, a * d = d * a) →
      d ∈ aStar142 c A := fun d hd hcomm =>
    mem_image_of_centralizes N hN3 hAM hF3G hd hcomm
  have hApg : IsPGroup 3 (aStar142 c A) := by
    have h1 : IsPGroup 3 (A.subgroupOf M) :=
      (CFSG.IsElementaryAbelian.isPGroup 3 ↥A).comap_subtype
    exact h1.map _
  have hB := commutator_pCore_eq_bot Nat.prime_three (by norm_num) hApg hW3 hAW hF3
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at hB
  have h3L : 3 ∣ Nat.card L := by
    have h1 := Sec16.Proof1614Trans.card_inf_eq_three_of_pgl hD hPGL
    exact h1 ▸ Subgroup.card_dvd_of_le inf_le_right
  have hML : M ≤ Subgroup.normalizer (L : Set G) := centralizer_le_normalizer_of_three_dvd h h3L
  have hMT : M ≤ Subgroup.normalizer (T : Set G) :=
    hML.trans (Proof142Res.normalizer_le_normalizer_thetaQuotCentralizer L)
  have hCn : (cStar142 c L).Normal := by
    have h1 : ((M ⊓ T).subgroupOf M).Normal := by
      rw [Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left]
      intro m hm
      exact Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hm, hMT hm⟩
    exact h1.map ψ (QuotientGroup.mk'_surjective N)
  have hle : inSubgroup (CFSG.pCore 3) (cStar142 c L) ≤ CFSG.pCore 3 (↥M ⧸ N) := by
    have hnorm : (inSubgroup (CFSG.pCore 3) (cStar142 c L)).Normal := by
      have h1 := CFSG.RankThree.GroupTheory.SteinbergBY.normalizer_le_normalizer_inSubgroup_pCore
        3 (cStar142 c L)
      rw [Subgroup.normalizer_eq_top_iff.mpr hCn] at h1
      exact Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp h1)
    exact le_sSup ⟨hnorm,
      CFSG.RankThree.GroupTheory.SteinbergBY.isPGroup_inSubgroup_pCore 3 (cStar142 c L)⟩
  exact hB.trans (Subgroup.centralizer_le hle)

theorem step142PGLKer_of_res3 (hSz : KFacts.KPSz) :
    Step142PGLKer :=
  step142PGLKer_of_centO3 hSz step142PGLCentO3

end CFSG.RankThree.PartTwo.Sec14
