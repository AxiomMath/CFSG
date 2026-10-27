module

public import CFSG.RankThree.PartTwo.Sec15.Liebeck155R1T150Defs
import CFSG.RankThree.PartTwo.Sec4.RonanK429RowHComp
public import CFSG.RankThree.PartTwo.Sec4.Item47Kinds

public section

namespace CFSG.RankThree.PartTwo.Sec15.Liebeck155R1T150

open CFSG CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

structure K150sTgt (J : Type) [Group J] : Prop where
  simple : IsSimpleGroup J
  card : Nat.card J = 2520 ∨ Nat.card J = 443520

theorem K150sTgt.not_dvd {J : Type} [Group J] (h : K150sTgt J) {n : ℕ} (h1 : ¬ 2520 ∣ n)
    (h2 : ¬ 443520 ∣ n) : ¬ Nat.card J ∣ n := by
  rcases h.card with hc | hc <;> rw [hc] <;> assumption

theorem K150sTgt.seven_dvd {J : Type} [Group J] (h : K150sTgt J) : 7 ∣ Nat.card J := by
  rcases h.card with hc | hc <;> rw [hc] <;> norm_num

theorem K150sTgt.not_isPGroup {J : Type} [Group J] (h : K150sTgt J) : ¬ IsPGroup 3 J := by
  intro hp
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Finite J := Nat.finite_of_card_ne_zero (by
    rcases h.card with hc | hc <;> rw [hc] <;> norm_num)
  obtain ⟨n, hn⟩ := hp.exists_card_eq
  have h2 : 2 ∣ 3 ^ n := by
    rw [← hn]
    rcases h.card with hc | hc <;> rw [hc] <;> norm_num
  exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_two h2) (by norm_num)

section Transport

variable {J : Type} [Group J] {S G' : Type} [Group S] [Group G']

theorem k150s_goodFor_of_map {C : Subgroup S} (f : S →* G') (hf : Function.Injective f)
    (h : GoodFor J (C.map f)) : GoodFor J C := by
  intro P hPC hPs hPp hZ N hN
  have := hPp
  let eP : P ≃* P.map f := P.equivMapOfInjective f hf
  have : (N.map (eP : P →* P.map f)).Normal := hN.map _ eP.surjective
  have : Group.IsPerfect (P.map f) := Group.IsPerfect.map f
  let eC : C ≃* C.map f := C.equivMapOfInjective f hf
  have heC : ∀ x : C, ((eC x : C.map f) : G') = f x := fun x =>
    Subgroup.coe_equivMapOfInjective_apply C f hf x
  have hsurj : Function.Surjective (eC : C →* C.map f) := eC.surjective
  have hmap := hPs.map hsurj
  have heq : (P.subgroupOf C).map (eC : C →* C.map f) = (P.map f).subgroupOf (C.map f) := by
    ext ⟨y, hy⟩
    simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf, MonoidHom.coe_coe]
    constructor
    · rintro ⟨x, hxP, hxy⟩
      refine ⟨x, hxP, ?_⟩
      rw [← heC x, hxy]
    · rintro ⟨x, hxP, rfl⟩
      refine ⟨⟨x, hPC hxP⟩, hxP, Subtype.ext ?_⟩
      rw [heC]
  rw [heq] at hmap
  have hZ' : ¬ 3 ∣ Nat.card (Subgroup.center ↥(P.map f)) := by
    rwa [← Nat.card_congr (Subgroup.centerCongr eP).toEquiv]
  exact ⟨fun e => (h (P.map f) (Subgroup.map_mono hPC) hmap inferInstance hZ'
    (N.map (eP : P →* P.map f))).false ((QuotientGroup.congr N _ eP rfl).symm.trans e)⟩

theorem k150s_goodFor_map_mulEquiv {C : Subgroup S} (φ : S ≃* G') (h : GoodFor J C) :
    GoodFor J (C.map φ.toMonoidHom) := by
  refine k150s_goodFor_of_map φ.symm.toMonoidHom φ.symm.injective ?_
  have : (C.map φ.toMonoidHom).map φ.symm.toMonoidHom = C := by
    rw [Subgroup.map_map]
    convert Subgroup.map_id C
    ext x
    simp
  rw [this]
  exact h

theorem k150s_goodFor_conj {P : Subgroup S} {y k : S} (hk : k ∈ P) (hy : y ^ 3 = 1) {e : ℕ}
    (he : e = 1 ∨ e = 2) (h : GoodFor J (Subgroup.centralizer ({y} : Set S) ⊓ P)) :
    GoodFor J (Subgroup.centralizer ({k * y ^ e * k⁻¹} : Set S) ⊓ P) := by
  have hmap : (Subgroup.centralizer ({y} : Set S) ⊓ P).map (MulAut.conj k).toMonoidHom =
      Subgroup.centralizer ({k * y ^ e * k⁻¹} : Set S) ⊓ P := by
    rw [← RonanK429H.centralizer_pow_of_pow_three hy he]
    ext w
    simp only [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff,
      MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    constructor
    · rintro ⟨z, ⟨hzc, hzP⟩, rfl⟩
      refine ⟨?_, P.mul_mem (P.mul_mem hk hzP) (P.inv_mem hk)⟩
      calc k * z * k⁻¹ * (k * y ^ e * k⁻¹) = k * (z * y ^ e) * k⁻¹ := by group
        _ = k * (y ^ e * z) * k⁻¹ := by rw [hzc]
        _ = k * y ^ e * k⁻¹ * (k * z * k⁻¹) := by group
    · rintro ⟨hwc, hwP⟩
      refine ⟨k⁻¹ * w * k, ⟨?_, P.mul_mem (P.mul_mem (P.inv_mem hk) hwP) hk⟩, by group⟩
      calc k⁻¹ * w * k * y ^ e = k⁻¹ * (w * (k * y ^ e * k⁻¹)) * k := by group
        _ = k⁻¹ * ((k * y ^ e * k⁻¹) * w) * k := by rw [hwc]
        _ = y ^ e * (k⁻¹ * w * k) := by group
  rw [← hmap]
  exact k150s_goodFor_map_mulEquiv (MulAut.conj k) h

theorem k150s_goodFor_of_isConj {a b : S} (hab : IsConj a b)
    (h : GoodFor J (Subgroup.centralizer ({a} : Set S))) :
    GoodFor J (Subgroup.centralizer ({b} : Set S)) := by
  obtain ⟨c, rfl⟩ := isConj_iff.mp hab
  have hmap : (Subgroup.centralizer ({a} : Set S)).map (MulAut.conj c).toMonoidHom =
      Subgroup.centralizer ({c * a * c⁻¹} : Set S) := by
    ext w
    simp only [Subgroup.mem_map, Subgroup.mem_centralizer_singleton_iff,
      MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    constructor
    · rintro ⟨z, hz, rfl⟩
      calc c * z * c⁻¹ * (c * a * c⁻¹) = c * (z * a) * c⁻¹ := by group
        _ = c * (a * z) * c⁻¹ := by rw [hz]
        _ = c * a * c⁻¹ * (c * z * c⁻¹) := by group
    · intro hw
      refine ⟨c⁻¹ * w * c, ?_, by group⟩
      calc c⁻¹ * w * c * a = c⁻¹ * (w * (c * a * c⁻¹)) * c := by group
        _ = c⁻¹ * ((c * a * c⁻¹) * w) * c := by rw [hw]
        _ = a * (c⁻¹ * w * c) := by group
  rw [← hmap]
  exact k150s_goodFor_map_mulEquiv (MulAut.conj c) h

theorem k150s_goodFor_of_mulEquiv_centralizer (e : S ≃* G') {s : S}
    (h : GoodFor J (Subgroup.centralizer ({e s} : Set G'))) :
    GoodFor J (Subgroup.centralizer ({s} : Set S)) := by
  refine k150s_goodFor_of_map e.toMonoidHom e.injective ?_
  have hm := RonanK429H.map_centralizer_singleton e.toMonoidHom e.injective s
  rw [MonoidHom.range_eq_top_of_surjective _ e.surjective, inf_top_eq] at hm
  rw [hm]
  exact h

end Transport

section Inner

variable {J : Type} [Group J] {S G' : Type} [Group S] [Group G']

theorem k150s_noCfg_of_inner (hZ : Subgroup.center S = ⊥) (hout : ¬ 3 ∣ Nat.card (Outer S))
    (hgood : ∀ s : S, orderOf s = 3 → GoodFor J (Subgroup.centralizer ({s} : Set S))) :
    NoCfgFor J S := by
  intro σ h3 h1
  obtain ⟨s, rfl⟩ := cubeInner_of_not_three_dvd_card_outer hout σ h3
  have hs3 : s ^ 3 = 1 := by
    have h' : MulAut.conj (s ^ 3) = 1 := by rw [map_pow, h3]
    have hz : s ^ 3 ∈ Subgroup.center S := by
      rw [Subgroup.mem_center_iff]
      intro g
      have := congrArg (fun φ : MulAut S => φ g) h'
      simp only [MulAut.conj_apply, MulAut.one_apply] at this
      calc g * s ^ 3 = s ^ 3 * g * (s ^ 3)⁻¹ * s ^ 3 := by rw [this]
        _ = s ^ 3 * g := by group
    rw [hZ, Subgroup.mem_bot] at hz
    exact hz
  have hs1 : s ≠ 1 := by
    rintro rfl
    exact h1 (map_one _)
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hso : orderOf s = 3 := orderOf_eq_prime hs3 hs1
  rw [RonanK429H.autFix_conj]
  exact hgood s hso

theorem k150s_noCfg_of_subgroupModel {P : Subgroup G'} (e : S ≃* P)
    (hZ : Subgroup.center S = ⊥) (hout : ¬ 3 ∣ Nat.card (Outer S))
    (h : ∀ x ∈ P, orderOf x = 3 → GoodFor J (Subgroup.centralizer ({x} : Set G') ⊓ P)) :
    NoCfgFor J S := by
  refine k150s_noCfg_of_inner hZ hout fun s hs => ?_
  let f : S →* G' := P.subtype.comp e.toMonoidHom
  have hf : Function.Injective f := Subtype.val_injective.comp e.injective
  have hr : f.range = P := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact (e x).2
    · intro hy
      exact ⟨e.symm ⟨y, hy⟩, by simp [f]⟩
  refine k150s_goodFor_of_map f hf ?_
  rw [RonanK429H.map_centralizer_singleton f hf s, hr]
  exact h (f s) (e s).2 (by rw [orderOf_injective f hf s]; exact hs)

theorem k150s_noCfg_of_model (e : S ≃* G') (hZ : Subgroup.center S = ⊥)
    (hout : ¬ 3 ∣ Nat.card (Outer S))
    (h : ∀ y : G', orderOf y = 3 → GoodFor J (Subgroup.centralizer ({y} : Set G'))) :
    NoCfgFor J S :=
  k150s_noCfg_of_inner hZ hout fun s hs =>
    k150s_goodFor_of_mulEquiv_centralizer e (h (e s) (by rw [MulEquiv.orderOf_eq]; exact hs))

theorem k150s_row_of_native {s : TauCeti.SporadicName}
    (hb : Nonempty (Blueprint.NativeSporadic.Carrier s ≃* Spor s))
    (h : ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
      Nonempty (S ≃* Blueprint.NativeSporadic.Carrier s) → NoCfgFor J S) :
    RowOfK150 J (Spor s) := by
  intro S _ _ hs hna ⟨e⟩
  obtain ⟨b⟩ := hb
  exact h S hs hna ⟨e.trans b.symm⟩

end Inner

section Criteria

variable {J : Type} [Group J]

theorem k150s_card_dvd_of_quotEquiv {P : Type*} [Group P] (N : Subgroup P) [N.Normal]
    (e : P ⧸ N ≃* J) : Nat.card J ∣ Nat.card P := by
  rw [← Nat.card_congr e.toEquiv]
  exact Subgroup.card_quotient_dvd_card N

theorem k150s_goodFor_of_card_dvd {S : Type} [Group S] {C : Subgroup S} {M : ℕ}
    (hC : Nat.card C ∣ M) (h : ¬ Nat.card J ∣ M) : GoodFor J C := by
  intro P hPC _ _ _ N _
  exact ⟨fun e => h ((k150s_card_dvd_of_quotEquiv N e).trans
    ((Subgroup.card_dvd_of_le hPC).trans hC))⟩

theorem k150s_goodFor_of_not_dvd {S : Type} [Group S] {C : Subgroup S}
    (h : ¬ Nat.card J ∣ Nat.card C) : GoodFor J C :=
  k150s_goodFor_of_card_dvd dvd_rfl h

theorem k150s_goodFor_of_prime_not_dvd {S : Type} [Group S] {C : Subgroup S} {d : ℕ}
    (hd : d ∣ Nat.card J) (h : ¬ d ∣ Nat.card C) : GoodFor J C :=
  k150s_goodFor_of_not_dvd fun h' => h (hd.trans h')

theorem k150s_row_of_not_dvd {X : Type} [Group X] (h : ¬ Nat.card J ∣ Nat.card X) :
    RowOfK150 J X := by
  intro S _ _ _ _ ⟨e⟩ σ _ _
  refine k150s_goodFor_of_card_dvd (M := Nat.card S) (Subgroup.card_subgroup_dvd_card _) ?_
  rwa [Nat.card_congr e.toEquiv]

theorem k150s_goodFor_of_isQuasisimple [Nontrivial J] {S : Type} [Group S] {C : Subgroup S}
    (hC : CFSG.IsQuasisimple C) (h3 : 3 ∣ Nat.card (Subgroup.center C)) : GoodFor J C := by
  intro P hPC hPs hPp hZ N hN
  have := hPp
  refine ⟨fun e => ?_⟩
  have : Nontrivial (P ⧸ N) := e.toEquiv.nontrivial
  have : Nontrivial P := (QuotientGroup.mk'_surjective N).nontrivial
  rcases Res429.eq_top_or_le_center_of_isSubnormal hC hPs with htop | hcen
  · have hPeq : P = C := le_antisymm hPC (Subgroup.subgroupOf_eq_top.mp htop)
    subst hPeq
    exact hZ h3
  · have hab : ∀ a b : P, a * b = b * a := by
      intro a b
      have ha : (⟨a, hPC a.2⟩ : C) ∈ Subgroup.center C := hcen a.2
      have h' := Subgroup.mem_center_iff.mp ha ⟨b, hPC b.2⟩
      exact Subtype.ext (congrArg Subtype.val h').symm
    exact Group.IsPerfect.not_isSolvable P (Group.isSolvable_of_comm hab)

theorem k150s_goodFor_of_simple_normal {S : Type} [Group S] [Finite S] {C E : Subgroup S}
    (hEC : E ≤ C) (hEn : (E.subgroupOf C).Normal) (hEs : IsSimpleGroup E)
    (hlt : Nat.card C < Nat.card J * Nat.card E) (hdvd : ¬ Nat.card E ∣ Nat.card J) :
    GoodFor J C := by
  intro P hPC hPs _ _ N hN
  refine ⟨fun e => ?_⟩
  have hJP : Nat.card J ∣ Nat.card P := k150s_card_dvd_of_quotEquiv N e
  have hEpos : 0 < Nat.card E := Nat.card_pos
  have : Finite J := Finite.of_equiv _ e.toEquiv
  have hJpos : 0 < Nat.card J := Nat.card_pos
  set E' : Subgroup C := E.subgroupOf C with hE'
  have hCE : Nat.card C = Nat.card (C ⧸ E') * Nat.card E :=
    (Subgroup.card_eq_card_quotient_mul_card_subgroup E').trans
      (congrArg _ (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEC).toEquiv))
  have hqpos : 0 < Nat.card (C ⧸ E') := Nat.card_pos
  have hqlt : Nat.card (C ⧸ E') < Nat.card J := by
    by_contra hge
    have hge' := not_lt.mp hge
    have : Nat.card J * Nat.card E ≤ Nat.card (C ⧸ E') * Nat.card E :=
      Nat.mul_le_mul_right _ hge'
    omega
  have : IsSimpleGroup E' := (Subgroup.subgroupOfEquivOfLe hEC).isSimpleGroup
  have hsubC : ((P ⊓ E).subgroupOf C).IsSubnormal := by
    have h1 : (P ⊓ E).subgroupOf C = P.subgroupOf C ⊓ E' := by
      ext x
      simp [Subgroup.mem_subgroupOf, hE']
    rw [h1]
    exact hPs.inf hEn.isSubnormal
  have hsubE : (((P ⊓ E).subgroupOf C).subgroupOf E').IsSubnormal := hsubC.subgroupOf
  rcases hsubE.eq_bot_or_top_of_isSimpleGroup inferInstance with hbot | htop
  ·
    have hPE : ∀ x ∈ P, x ∈ E → x = 1 := by
      intro x hxP hxE
      have hxC : x ∈ C := hPC hxP
      have : (⟨⟨x, hxC⟩, hxE⟩ : E') ∈ ((P ⊓ E).subgroupOf C).subgroupOf E' := by
        simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
        exact ⟨hxP, hxE⟩
      rw [hbot, Subgroup.mem_bot] at this
      simpa using congrArg (fun y : E' => ((y : C) : S)) this
    let ψ : P →* C ⧸ E' := (QuotientGroup.mk' E').comp (Subgroup.inclusion hPC)
    have hψ : Function.Injective ψ := by
      rw [injective_iff_map_eq_one]
      intro x hx
      have hx' : (Subgroup.inclusion hPC x : C) ∈ E' := (QuotientGroup.eq_one_iff _).mp hx
      have hxE : (x : S) ∈ E := hx'
      have := hPE x x.2 hxE
      exact Subtype.ext this
    have hdvd1 : Nat.card P ∣ Nat.card (C ⧸ E') := Subgroup.card_dvd_of_injective ψ hψ
    have := Nat.le_of_dvd hqpos (hJP.trans hdvd1)
    omega
  ·
    have hEP : E ≤ P := by
      intro y hy
      have hyC : y ∈ C := hEC hy
      have : (⟨⟨y, hyC⟩, hy⟩ : E') ∈ ((P ⊓ E).subgroupOf C).subgroupOf E' := by
        rw [htop]
        trivial
      have h2 := this
      simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf] at h2
      exact h2.1
    set EP : Subgroup P := E.subgroupOf P with hEP'
    have : EP.Normal := ⟨fun x hx g => by
      have hxE : (x : S) ∈ E := hx
      have hxC : (x : S) ∈ C := hPC x.2
      have hgC : (g : S) ∈ C := hPC g.2
      exact hEn.conj_mem ⟨x, hxC⟩ hxE ⟨g, hgC⟩⟩
    have hEPE : EP ≃* E := Subgroup.subgroupOfEquivOfLe hEP
    have : IsSimpleGroup EP := hEPE.isSimpleGroup
    have : (N.subgroupOf EP).Normal := Subgroup.Normal.subgroupOf inferInstance EP
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.subgroupOf EP) with hNbot | hNtop
    ·
      have hdis : Disjoint N EP := Subgroup.subgroupOf_eq_bot.mp hNbot
      let ι : EP →* P ⧸ N := (QuotientGroup.mk' N).comp EP.subtype
      have hι : Function.Injective ι := by
        rw [injective_iff_map_eq_one]
        intro x hx
        have hxN : (x : P) ∈ N := (QuotientGroup.eq_one_iff _).mp hx
        have h1 : (x : P) = 1 := Subgroup.disjoint_def.mp hdis hxN x.2
        exact Subtype.ext h1
      have h2 : Nat.card EP ∣ Nat.card (P ⧸ N) := Subgroup.card_dvd_of_injective ι hι
      rw [Nat.card_congr hEPE.toEquiv, Nat.card_congr e.toEquiv] at h2
      exact hdvd h2
    ·
      have hEPN : EP ≤ N := Subgroup.subgroupOf_eq_top.mp hNtop
      have h1 : N.index ∣ EP.index := Subgroup.index_dvd_of_le hEPN
      have h2 : EP.index ≤ E'.index := by
        have : E.relIndex C ≠ 0 := Subgroup.index_ne_zero_of_finite
        exact Subgroup.relIndex_le_of_le_right hPC this
      have h3 : N.index = Nat.card J := by
        rw [Subgroup.index, Nat.card_congr e.toEquiv]
      have h4 : E'.index = Nat.card (C ⧸ E') := rfl
      have h5 : 0 < EP.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
      have h6 := Nat.le_of_dvd h5 (h3 ▸ h1)
      omega

theorem k150s_goodFor_of_normal_three {S : Type} [Group S] [Finite S] {C R : Subgroup S}
    (hRC : R ≤ C) (hRn : ∀ g ∈ C, ∀ r ∈ R, g * r * g⁻¹ ∈ R) (hR3 : IsPGroup 3 R)
    (hJs : IsSimpleGroup J) (hJ3 : ¬ IsPGroup 3 J) {M : ℕ} (hM : Nat.card C ∣ M)
    (h : ¬ Nat.card J * Nat.card R ∣ M) : GoodFor J C := by
  intro P hPC _ _ _ N hN
  refine ⟨fun e => h ?_⟩
  have : Finite J := Finite.of_equiv _ e.toEquiv
  set RP : Subgroup P := R.subgroupOf P with hRP
  have : RP.Normal := ⟨fun x hx g => by
    have hxR : (x : S) ∈ R := hx
    exact hRn g (hPC g.2) x hxR⟩
  have hRP3 : IsPGroup 3 RP := fun x => by
    obtain ⟨k, hk⟩ := hR3 ⟨(x.1 : S), x.2⟩
    refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
    simpa using congrArg Subtype.val hk
  let π : P →* J := e.toMonoidHom.comp (QuotientGroup.mk' N)
  have hπ : Function.Surjective π := e.surjective.comp (QuotientGroup.mk'_surjective N)
  have hRPN : RP ≤ N := by
    have : (RP.map π).Normal := Subgroup.Normal.map inferInstance π hπ
    have hT3 : IsPGroup 3 (RP.map π) := hRP3.map π
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (RP.map π) with hT | hT
    · intro x hx
      have : π x ∈ RP.map π := ⟨x, hx, rfl⟩
      rw [hT, Subgroup.mem_bot] at this
      have h1 : (QuotientGroup.mk' N) x = 1 := e.injective (by simpa [π] using this)
      exact (QuotientGroup.eq_one_iff _).mp h1
    · exfalso
      rw [hT] at hT3
      exact hJ3 (hT3.of_equiv Subgroup.topEquiv)
  set R' : Subgroup C := R.subgroupOf C with hR'
  have : R'.Normal := ⟨fun x hx g => by
    have hxR : ((x : C) : S) ∈ R := hx
    exact hRn g g.2 x hxR⟩
  let φ : P →* C ⧸ R' := (QuotientGroup.mk' R').comp (Subgroup.inclusion hPC)
  have hker : φ.ker ≤ N := by
    intro x hx
    have hx' : (Subgroup.inclusion hPC x : C) ∈ R' := (QuotientGroup.eq_one_iff _).mp hx
    exact hRPN hx'
  have h1 : N.index ∣ φ.ker.index := Subgroup.index_dvd_of_le hker
  have h2 : φ.ker.index = Nat.card φ.range := by
    rw [Subgroup.index, Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv]
  have h3 : Nat.card φ.range ∣ Nat.card (C ⧸ R') := Subgroup.card_subgroup_dvd_card _
  have h4 : N.index = Nat.card J := by
    rw [Subgroup.index, Nat.card_congr e.toEquiv]
  have h5 : Nat.card C = Nat.card (C ⧸ R') * Nat.card R :=
    (Subgroup.card_eq_card_quotient_mul_card_subgroup R').trans
      (congrArg _ (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRC).toEquiv))
  have h6 : Nat.card J ∣ Nat.card (C ⧸ R') := by
    rw [← h4]
    exact h1.trans (h2 ▸ h3)
  have h7 : Nat.card J * Nat.card R ∣ Nat.card C := by
    rw [h5]
    exact Nat.mul_dvd_mul_right h6 _
  exact h7.trans hM

theorem k150s_goodFor_of_isQuasisimple_of_central [Nontrivial J] {S : Type} [Group S]
    {C : Subgroup S} {x : S} (hC : CFSG.IsQuasisimple C) (hxC : x ∈ C) (hx : orderOf x = 3)
    (hcomm : ∀ g ∈ C, g * x = x * g) : GoodFor J C := by
  refine k150s_goodFor_of_isQuasisimple hC ?_
  have hmem : (⟨x, hxC⟩ : C) ∈ Subgroup.center C :=
    Subgroup.mem_center_iff.2 fun g => Subtype.ext (hcomm g g.2)
  have h := Subgroup.orderOf_dvd_natCard _ hmem
  rwa [Subgroup.orderOf_mk, hx] at h

theorem k150s_goodFor_of_isQuasisimple_centralizer [Nontrivial J] {S : Type} [Group S] {x : S}
    (hx : orderOf x = 3) (hC : CFSG.IsQuasisimple (Subgroup.centralizer ({x} : Set S))) :
    GoodFor J (Subgroup.centralizer ({x} : Set S)) :=
  k150s_goodFor_of_isQuasisimple_of_central hC (Subgroup.mem_centralizer_singleton_iff.2 rfl) hx
    fun _ hg => Subgroup.mem_centralizer_singleton_iff.1 hg

theorem k150s_goodFor_of_perfect_le_simple [Nontrivial J] {S : Type} [Group S] {C E : Subgroup S}
    (hEC : E ≤ C) (hEs : IsSimpleGroup E)
    (hper : ∀ P : Subgroup S, P ≤ C → Group.IsPerfect P → P ≤ E)
    (hdvd : ¬ Nat.card E ∣ Nat.card J) : GoodFor J C := by
  intro P hPC hPs hPp _ N hN
  refine ⟨fun e => ?_⟩
  have hPE : P ≤ E := hper P hPC hPp
  have : Nontrivial (P ⧸ N) := e.toEquiv.nontrivial
  have : Nontrivial P := (QuotientGroup.mk'_surjective N).nontrivial
  set E' : Subgroup C := E.subgroupOf C with hE'
  have : IsSimpleGroup E' := (Subgroup.subgroupOfEquivOfLe hEC).isSimpleGroup
  have hsub : ((P.subgroupOf C).subgroupOf E').IsSubnormal := hPs.subgroupOf
  rcases hsub.eq_bot_or_top_of_isSimpleGroup inferInstance with hbot | htop
  ·
    have hP1 : ∀ x : P, x = 1 := by
      intro x
      have hxE : (x : S) ∈ E := hPE x.2
      have hxC : (x : S) ∈ C := hPC x.2
      have : (⟨⟨x, hxC⟩, hxE⟩ : E') ∈ (P.subgroupOf C).subgroupOf E' := by
        simp only [Subgroup.mem_subgroupOf]
        exact x.2
      rw [hbot, Subgroup.mem_bot] at this
      exact Subtype.ext (by simpa using congrArg (fun y : E' => ((y : C) : S)) this)
    obtain ⟨a, b, hab⟩ := exists_pair_ne P
    exact hab ((hP1 a).trans (hP1 b).symm)
  ·
    have hEP : E ≤ P := by
      intro y hy
      have hyC : y ∈ C := hEC hy
      have : (⟨⟨y, hyC⟩, hy⟩ : E') ∈ (P.subgroupOf C).subgroupOf E' := by
        rw [htop]
        trivial
      simpa only [Subgroup.mem_subgroupOf] using this
    have hPeq : P = E := le_antisymm hPE hEP
    subst hPeq
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with hN1 | hN1
    · apply hdvd
      have h1 : Nat.card P = Nat.card (P ⧸ N) * Nat.card N :=
        Subgroup.card_eq_card_quotient_mul_card_subgroup N
      have h2 : Nat.card (P ⧸ N) = Nat.card J := Nat.card_congr e.toEquiv
      have h3 : Nat.card N = 1 := by
        rw [hN1]
        exact Subgroup.card_bot
      rw [h2, h3, mul_one] at h1
      exact h1 ▸ dvd_rfl
    · have : Subsingleton (P ⧸ N) := by
        rw [hN1]
        exact QuotientGroup.subsingleton_quotient_top
      exact not_nontrivial (P ⧸ N) ‹_›

end Criteria

end CFSG.RankThree.PartTwo.Sec15.Liebeck155R1T150
