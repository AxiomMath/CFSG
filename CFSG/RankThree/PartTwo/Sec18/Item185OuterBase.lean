module

public import CFSG.RankThree.PartTwo.Sec18.Item185InnerBase
public import CFSG.RankThree.PartTwo.Sec19.SimsC198Descent

public section

namespace CFSG.RankThree.PartTwo.Sec18.Item185Proof

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.Assembly (IsElemAbelian)
open CFSG.RankThree.PartTwo.Sec19.SimsC198 (RankHyp)
open CFSG.RankThree.PartTwo.Sec4.RonanK429 (NoE27 AutNoE27)
open CFSG.ComponentClassification
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

@[expose] def NoOuterData (S : Type) [Group S] [Finite S] : Prop :=
  ∀ (P A B : Subgroup (MulAut S)) (c : MulAut S), OuterData S P A B c → False

@[expose] def OuterCase (P : (S : Type) → [Group S] → Prop) : Prop :=
  ∀ (X : Type) [Group X] [Finite X], RankHyp X → ∀ (P' A B : Subgroup (MulAut X)) (c : MulAut X),
    OuterData X P' A B c → P (X ⧸ Subgroup.center X) → False

theorem leafOuter_of_data
    (h : ∀ (X : Type) [Group X] [Finite X], RankHyp X → ∀ (P A B : Subgroup (MulAut X))
      (c : MulAut X), OuterData X P A B c → False) : LeafOuter := h

section Transport

variable {G H : Type} [Group G] [Group H]

private theorem commute_of_isElemAbelian {p : ℕ} {E : Subgroup H} (hE : IsElemAbelian p E)
    {a b : H} (ha : a ∈ E) (hb : b ∈ E) : a * b = b * a :=
  congrArg Subtype.val (hE.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)

private theorem isElemAbelian_of_le {p : ℕ} {E F : Subgroup H} (hE : IsElemAbelian p E)
    (hF : F ≤ E) : IsElemAbelian p F :=
  ⟨⟨⟨fun a b => Subtype.ext (commute_of_isElemAbelian hE (hF a.2) (hF b.2))⟩⟩,
    fun x hx => hE.2 x (hF hx)⟩

private theorem isElemAbelian_map_of_hom {p : ℕ} {E : Subgroup G} (hE : IsElemAbelian p E)
    (f : G →* H) : IsElemAbelian p (E.map f) := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun a ha => ?_⟩
  · obtain ⟨x, hx, hxa⟩ := Subgroup.mem_map.mp a.2
    obtain ⟨y, hy, hyb⟩ := Subgroup.mem_map.mp b.2
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [← hxa, ← hyb, ← map_mul, ← map_mul, commute_of_isElemAbelian hE hx hy]
  · obtain ⟨x, hx, hxa⟩ := Subgroup.mem_map.mp ha
    rw [← hxa, ← map_pow, hE.2 x hx, map_one]

private theorem isElemAbelian_comap_of_injective {f : G →* H} (hf : Function.Injective f)
    {E : Subgroup H} (hE : IsElemAbelian 3 E) : IsElemAbelian 3 (E.comap f) := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
  · apply Subtype.ext
    apply hf
    simp only [Subgroup.coe_mul, map_mul]
    exact commute_of_isElemAbelian hE (Subgroup.mem_comap.mp a.2) (Subgroup.mem_comap.mp b.2)
  · apply hf
    rw [map_pow, map_one]
    exact hE.2 (f x) (Subgroup.mem_comap.mp hx)

private theorem card_le_map_of_injective {f : G →* H} (hf : Function.Injective f) {P : Subgroup G}
    {n : ℕ} (hP : ∀ E ≤ P, IsElemAbelian 3 E → Nat.card E ≤ n) :
    ∀ E ≤ P.map f, IsElemAbelian 3 E → Nat.card E ≤ n := by
  intro E hE hEa
  have hEr : E ≤ f.range := fun y hy => by
    obtain ⟨z, -, hz⟩ := Subgroup.mem_map.mp (hE hy)
    exact MonoidHom.mem_range.mpr ⟨z, hz⟩
  have hle : E.comap f ≤ P := fun x hx => by
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp (hE (Subgroup.mem_comap.mp hx))
    rw [← hf hyx]
    exact hy
  have hcard : Nat.card E = Nat.card (E.comap f) := by
    have h1 := Subgroup.card_map_of_injective (K := E.comap f) hf
    rwa [Subgroup.map_comap_eq_self hEr] at h1
  rw [hcard]
  exact hP _ hle (isElemAbelian_comap_of_injective hf hEa)

private theorem isSylowOf_map_of_hom {G' : Type} [Group G'] [Finite G] {p : ℕ} [Fact p.Prime]
    (φ : G →* G') {P K : Subgroup G} (h : IsSylowOf p P K) :
    IsSylowOf p (P.map φ) (K.map φ) := by
  obtain ⟨Q, rfl⟩ := h
  refine ⟨Q.mapSurjective (φ.subgroupMap_surjective K), ?_⟩
  rw [Sylow.coe_mapSurjective, Subgroup.map_map, Subgroup.map_map]
  rfl

private theorem dichotomy_map_of_injective {φ : G →* H} (hφ : Function.Injective φ)
    {P A B : Subgroup G} {c : G}
    (hd : (∀ x ∈ P, x * c = c * x) ∨
      ((∀ x ∈ P, (∀ a ∈ A, x * a = a * x) → x ∈ A) ∧
        ∀ b ∈ B, ∃ x ∈ P ⊓ Subgroup.centralizer (B : Set G), x * c * x⁻¹ = b * c)) :
    (∀ x ∈ P.map φ, x * φ c = φ c * x) ∨
      ((∀ x ∈ P.map φ, (∀ a ∈ A.map φ, x * a = a * x) → x ∈ A.map φ) ∧
        ∀ b ∈ B.map φ, ∃ x ∈ P.map φ ⊓ Subgroup.centralizer ((B.map φ : Subgroup H) : Set H),
          x * φ c * x⁻¹ = b * φ c) := by
  rcases hd with h1 | ⟨h2, h3⟩
  · left
    rintro _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, h1 y hy]
  · right
    refine ⟨?_, ?_⟩
    · rintro _ ⟨y, hy, rfl⟩ hcomm
      have hyA : y ∈ A := h2 y hy (fun a ha => hφ (by
        have := hcomm (φ a) (Subgroup.mem_map_of_mem φ ha)
        simpa only [map_mul] using this))
      exact Subgroup.mem_map_of_mem φ hyA
    · intro b hb
      obtain ⟨b', hb', rfl⟩ := Subgroup.mem_map.mp hb
      obtain ⟨x, ⟨hxP, hxC⟩, hxc⟩ := h3 b' hb'
      refine ⟨φ x, Subgroup.mem_inf.mpr ⟨Subgroup.mem_map_of_mem φ hxP, ?_⟩, ?_⟩
      · rw [Subgroup.mem_centralizer_iff]
        intro h hh
        have hh' : h ∈ B.map φ := hh
        obtain ⟨b'', hb'', rfl⟩ := Subgroup.mem_map.mp hh'
        have hc := Subgroup.mem_centralizer_iff.mp hxC b'' hb''
        rw [← map_mul, ← map_mul, hc]
      · have := congrArg φ hxc
        simpa only [map_mul, map_inv] using this

end Transport

section CenterQuot

variable {X : Type} [Group X]

private theorem conj_eq_one_iff_mem_center (x : X) :
    MulAut.conj x = 1 ↔ x ∈ Subgroup.center X := by
  rw [Subgroup.mem_center_iff]
  constructor
  · intro h g
    have hg : MulAut.conj x g = g := by rw [h, MulAut.one_apply]
    rw [MulAut.conj_apply] at hg
    calc g * x = x * g * x⁻¹ * x := by rw [hg]
      _ = x * g := by group
  · intro h
    ext g
    rw [MulAut.conj_apply, MulAut.one_apply, ← h g]
    group

private theorem map_innerAut_centerQuotAut :
    (innerAut X).map (Sec19.SimsC198.centerQuotAut X) = innerAut (X ⧸ Subgroup.center X) := by
  ext φ
  constructor
  · intro hφ
    obtain ⟨ψ, hψ, rfl⟩ := Subgroup.mem_map.mp hφ
    obtain ⟨x, rfl⟩ := MonoidHom.mem_range.mp hψ
    exact MonoidHom.mem_range.mpr
      ⟨(x : X ⧸ Subgroup.center X), (Sec19.SimsC198.centerQuotAut_conj x).symm⟩
  · intro hφ
    obtain ⟨y, rfl⟩ := MonoidHom.mem_range.mp hφ
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center X) y
    exact Subgroup.mem_map.mpr
      ⟨MulAut.conj x, MonoidHom.mem_range.mpr ⟨x, rfl⟩, Sec19.SimsC198.centerQuotAut_conj x⟩

private theorem mem_fixedSubgroup_iff (σ : MulAut X) (x : X) :
    x ∈ fixedSubgroup σ ↔ σ x = x := Iff.rfl

private theorem fixed_conj_mem (c : MulAut X) {y : X}
    (hy : Sec19.SimsC198.centerQuotAut X c (y : X ⧸ Subgroup.center X) =
      (y : X ⧸ Subgroup.center X))
    {x : X} (hx : x ∈ fixedSubgroup c) : y * x * y⁻¹ ∈ fixedSubgroup c := by
  rw [mem_fixedSubgroup_iff] at hx ⊢
  have hw : (c y)⁻¹ * y ∈ Subgroup.center X :=
    QuotientGroup.eq.mp ((Sec19.SimsC198.centerQuotAut_mk c y).symm.trans hy)
  obtain ⟨w, hwdef⟩ : ∃ w, w = (c y)⁻¹ * y := ⟨_, rfl⟩
  rw [← hwdef] at hw
  have hcy : c y = y * w⁻¹ := by
    rw [hwdef]
    group
  have hwx : x * w = w * x := Subgroup.mem_center_iff.mp hw x
  have hwconj : w⁻¹ * x * w = x := by
    calc w⁻¹ * x * w = w⁻¹ * (x * w) := by group
      _ = w⁻¹ * (w * x) := by rw [hwx]
      _ = x := by group
  rw [map_mul, map_mul, map_inv, hx, hcy]
  calc y * w⁻¹ * x * (y * w⁻¹)⁻¹ = y * (w⁻¹ * x * w) * y⁻¹ := by group
    _ = y * x * y⁻¹ := by rw [hwconj]

private theorem fixed_map_conj_mem (c : MulAut X)
    {s : X ⧸ Subgroup.center X} (hs : Sec19.SimsC198.centerQuotAut X c s = s)
    {t : X ⧸ Subgroup.center X}
    (ht : t ∈ (fixedSubgroup c).map (QuotientGroup.mk' (Subgroup.center X))) :
    s * t * s⁻¹ ∈ (fixedSubgroup c).map (QuotientGroup.mk' (Subgroup.center X)) := by
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center X) s
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp ht
  exact Subgroup.mem_map.mpr
    ⟨y * x * y⁻¹, fixed_conj_mem c (y := y) hs hx, by simp only [map_mul, map_inv]⟩

private noncomputable abbrev fixedQuotSub (c : MulAut X) :
    Subgroup ↥(fixedSubgroup (Sec19.SimsC198.centerQuotAut X c)) :=
  ((fixedSubgroup c).map (QuotientGroup.mk' (Subgroup.center X))).subgroupOf
    (fixedSubgroup (Sec19.SimsC198.centerQuotAut X c))

private theorem fixedQuotSub_normal (c : MulAut X) : (fixedQuotSub c).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  have hg : Sec19.SimsC198.centerQuotAut X c (g : X ⧸ Subgroup.center X) =
      (g : X ⧸ Subgroup.center X) :=
    (mem_fixedSubgroup_iff _ _).mp g.2
  have := fixed_map_conj_mem c hg hn
  simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using this

private theorem fixed_map_le (c : MulAut X) :
    (fixedSubgroup c).map (QuotientGroup.mk' (Subgroup.center X)) ≤
      fixedSubgroup (Sec19.SimsC198.centerQuotAut X c) := by
  rintro _ ⟨x, hx, rfl⟩
  have hx' : c x = x := hx
  rw [mem_fixedSubgroup_iff]
  rw [QuotientGroup.mk'_apply, Sec19.SimsC198.centerQuotAut_mk, hx']

private theorem oTwoP_fixed_map_mem [Finite X] (c : MulAut X)
    (o : fixedSubgroup c) (ho : o ∈ Sec4.oTwoP 3 ↥(fixedSubgroup c)) :
    (QuotientGroup.mk' (Subgroup.center X) (o : X)) ∈
      (Sec4.oTwoP 3 ↥(fixedSubgroup (Sec19.SimsC198.centerQuotAut X c))).map
        (fixedSubgroup (Sec19.SimsC198.centerQuotAut X c)).subtype := by
  haveI := fixedQuotSub_normal c
  let g : ↥(fixedSubgroup c) →* ↥(fixedQuotSub c) :=
    { toFun := fun x =>
        ⟨⟨QuotientGroup.mk' (Subgroup.center X) (x : X),
            fixed_map_le c
              (Subgroup.mem_map_of_mem (QuotientGroup.mk' (Subgroup.center X)) x.2)⟩,
          Subgroup.mem_subgroupOf.mpr
            (Subgroup.mem_map_of_mem (QuotientGroup.mk' (Subgroup.center X)) x.2)⟩
      map_one' := Subtype.ext (Subtype.ext (by simp))
      map_mul' := fun x y => Subtype.ext (Subtype.ext (by simp)) }
  have hg_surj : Function.Surjective g := by
    rintro ⟨⟨s, hs⟩, hsN⟩
    obtain ⟨x, hx, hxs⟩ := Subgroup.mem_map.mp (Subgroup.mem_subgroupOf.mp hsN)
    exact ⟨⟨x, hx⟩, Subtype.ext (Subtype.ext hxs)⟩
  have hmap := oTwoP_map_le_of_surjective g hg_surj
  have hN2 := oTwoP_normal_le (fixedQuotSub c)
  have hgo : g o ∈ Sec4.oTwoP 3 ↥(fixedQuotSub c) := hmap (Subgroup.mem_map_of_mem g ho)
  have hz := hN2 (Subgroup.mem_map_of_mem (fixedQuotSub c).subtype hgo)
  exact Subgroup.mem_map.mpr ⟨_, hz, rfl⟩

private theorem oTwoThreeFixed_map_congr {S T : Type} [Group S] [Group T] [Finite S]
    (e : S ≃* T) (σ : MulAut S) :
    (oTwoThreeFixed σ).map e.toMonoidHom = oTwoThreeFixed (MulAut.congr e σ) := by
  have hfix : fixedSubgroup (MulAut.congr e σ) = (fixedSubgroup σ).map e.toMonoidHom := by
    ext t
    rw [mem_fixedSubgroup_iff, Subgroup.mem_map]
    constructor
    · intro ht
      refine ⟨e.symm t, ?_, e.apply_symm_apply t⟩
      rw [mem_fixedSubgroup_iff]
      have h1 : e (σ (e.symm t)) = t := ht
      apply e.injective
      rw [h1, e.apply_symm_apply]
    · rintro ⟨s, hs, rfl⟩
      rw [mem_fixedSubgroup_iff] at hs
      show e (σ (e.symm (e s))) = e s
      rw [e.symm_apply_apply, hs]
  unfold oTwoThreeFixed
  rw [hfix, ← oTwoP_map_mulEquiv
    (Subgroup.equivMapOfInjective (fixedSubgroup σ) e.toMonoidHom e.injective),
    Subgroup.map_map, Subgroup.map_map]
  congr 1

end CenterQuot

section Reduction

variable {X : Type} [Group X] [Finite X]

theorem OuterData.quotient (hX : RankHyp X) {P A B : Subgroup (MulAut X)} {c : MulAut X}
    (h : OuterData X P A B c) :
    OuterData (X ⧸ Subgroup.center X) (P.map (Sec19.SimsC198.centerQuotAut X))
      (A.map (Sec19.SimsC198.centerQuotAut X)) (B.map (Sec19.SimsC198.centerQuotAut X))
      (Sec19.SimsC198.centerQuotAut X c) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hperf : Group.IsPerfect X := hX.quasisimple.1
  have hinj : Function.Injective (Sec19.SimsC198.centerQuotAut X) :=
    Sec19.SimsC198.centerQuotAut_injective hperf
  have hinn := map_innerAut_centerQuotAut (X := X)
  exact
    { isPGroup := h.isPGroup.map _
      sylow := by
        have h1 := isSylowOf_map_of_hom (Sec19.SimsC198.centerQuotAut X) h.sylow
        rw [Subgroup.map_sup, hinn] at h1
        exact h1
      card_le := card_le_map_of_injective hinj h.card_le
      isElemAbelian := isElemAbelian_map_of_hom h.isElemAbelian _
      card_A := by rw [Subgroup.card_map_of_injective hinj]; exact h.card_A
      le_P := Subgroup.map_mono h.le_P
      le_B := Subgroup.map_mono h.le_B
      card_B := by rw [Subgroup.card_map_of_injective hinj]; exact h.card_B
      eq_sup := by
        have h1 := congrArg (Subgroup.map (Sec19.SimsC198.centerQuotAut X)) h.eq_sup
        rw [Subgroup.map_sup, MonoidHom.map_zpowers] at h1
        exact h1
      not_mem := fun hm => h.not_mem ((Subgroup.mem_map_iff_mem hinj).mp hm)
      le_inner := (Subgroup.map_mono h.le_inner).trans hinn.le
      dichotomy := dichotomy_map_of_injective hinj h.dichotomy
      omega := by
        intro bf hbf
        obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hbf
        obtain ⟨σo, hσo, hσb⟩ := Subgroup.mem_map.mp (h.omega hb)
        unfold oTwoThreeFixed at hσo
        obtain ⟨o, ho, rfl⟩ := Subgroup.mem_map.mp hσo
        refine Subgroup.mem_map.mpr ⟨_, oTwoP_fixed_map_mem c o ho, ?_⟩
        rw [← hσb]
        exact (Sec19.SimsC198.centerQuotAut_conj (o : X)).symm
      outer := fun hm => h.outer (Sec19.SimsC198.mem_inner_of_centerQuotAut hperf hm) }

end Reduction

theorem OuterCase.of_noOuterData {P : (S : Type) → [Group S] → Prop}
    (h : ∀ (S : Type) [Group S] [Finite S], P S → NoOuterData S) : OuterCase P :=
  fun X _ _ hX _ _ _ _ hd hP => h _ hP _ _ _ _ (hd.quotient hX)

theorem OuterCase.of_rankHyp {P : (S : Type) → [Group S] → Prop}
    (h : ∀ (X : Type) [Group X] [Finite X], RankHyp X → P (X ⧸ Subgroup.center X) → False) :
    OuterCase P :=
  fun X _ _ hX _ _ _ _ _ hP => h X hX hP

private theorem outerData_map_congr {S T : Type} [Group S] [Group T] [Finite S] [Finite T]
    (e : S ≃* T) {P A B : Subgroup (MulAut S)} {c : MulAut S} (h : OuterData S P A B c) :
    OuterData T (P.map (MulAut.congr e).toMonoidHom) (A.map (MulAut.congr e).toMonoidHom)
      (B.map (MulAut.congr e).toMonoidHom) (MulAut.congr e c) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hinj : Function.Injective (MulAut.congr e).toMonoidHom := (MulAut.congr e).injective
  have hinn : (innerAut S).map (MulAut.congr e).toMonoidHom = innerAut T :=
    CFSG.ComponentClassification.OuterAutomorphisms.inner_map_congr e
  exact
    { isPGroup := h.isPGroup.map _
      sylow := by
        have h1 := isSylowOf_map_of_hom (MulAut.congr e).toMonoidHom h.sylow
        rw [Subgroup.map_sup, hinn] at h1
        exact h1
      card_le := card_le_map_of_injective hinj h.card_le
      isElemAbelian := isElemAbelian_map_of_hom h.isElemAbelian _
      card_A := by rw [Subgroup.card_map_of_injective hinj]; exact h.card_A
      le_P := Subgroup.map_mono h.le_P
      le_B := Subgroup.map_mono h.le_B
      card_B := by rw [Subgroup.card_map_of_injective hinj]; exact h.card_B
      eq_sup := by
        have h1 := congrArg (Subgroup.map (MulAut.congr e).toMonoidHom) h.eq_sup
        rw [Subgroup.map_sup, MonoidHom.map_zpowers] at h1
        exact h1
      not_mem := fun hm => h.not_mem ((Subgroup.mem_map_iff_mem hinj).mp hm)
      le_inner := (Subgroup.map_mono h.le_inner).trans hinn.le
      dichotomy := dichotomy_map_of_injective hinj h.dichotomy
      omega := by
        intro bf hbf
        obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hbf
        obtain ⟨σo, hσo, hσb⟩ := Subgroup.mem_map.mp (h.omega hb)
        have hmem : e σo ∈ oTwoThreeFixed (MulAut.congr e c) := by
          rw [← oTwoThreeFixed_map_congr e c]
          exact Subgroup.mem_map_of_mem e.toMonoidHom hσo
        refine Subgroup.mem_map.mpr ⟨e σo, hmem, ?_⟩
        rw [← hσb]
        exact (CFSG.ComponentClassification.OuterAutomorphisms.congr_conj e σo).symm
      outer := fun hm =>
        h.outer ((Subgroup.mem_map_iff_mem hinj).mp (by rw [hinn]; exact hm)) }

theorem noOuterData_of_autNoE27 {S : Type} [Group S] [Finite S] (h : AutNoE27 S) :
    NoOuterData S :=
  fun _ A _ _ hd => h A ⟨hd.isElemAbelian, hd.card_A⟩

theorem noOuterData_of_not_three_dvd_outer {S : Type} [Group S] [Finite S]
    (h : ¬ 3 ∣ Nat.card (Outer S)) : NoOuterData S := by
  intro P A B c hd
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcA : c ∈ A := by rw [hd.eq_sup]; exact Subgroup.mem_sup_left (Subgroup.mem_zpowers c)
  have hc3 : c ^ 3 = 1 := hd.isElemAbelian.2 c hcA
  have hq3 : (QuotientGroup.mk c : Outer S) ^ 3 = 1 := by
    rw [← QuotientGroup.mk_pow, hc3]; rfl
  have hq1 : (QuotientGroup.mk c : Outer S) ≠ 1 := fun h1 =>
    hd.outer ((@QuotientGroup.eq_one_iff _ _ (OuterAutomorphisms.inner S)
      (OuterAutomorphisms.inner_normal S) c).mp h1)
  have hord : orderOf (QuotientGroup.mk c : Outer S) = 3 := orderOf_eq_prime hq3 hq1
  exact h (hord ▸ orderOf_dvd_natCard _)

theorem not_three_dvd_outer_of_mulEquiv {S T : Type} [Group S] [Group T] (e : S ≃* T)
    (h : ¬ 3 ∣ Nat.card (Outer T)) : ¬ 3 ∣ Nat.card (Outer S) := by
  rwa [Nat.card_congr (OuterAutomorphisms.equivalence e).toEquiv]

@[expose] def NoOmega (S : Type) [Group S] : Prop :=
  ∀ σ : MulAut S, σ ∉ innerAut S → σ ^ 3 = 1 → ∀ B : Subgroup S, IsElemAbelian 3 B →
    Nat.card B = 9 → B ≤ oTwoThreeFixed σ → False

theorem NoOmega.of_mulEquiv {S T : Type} [Group S] [Group T] [Finite S] [Finite T] (e : S ≃* T)
    (h : NoOmega T) : NoOmega S := by
  intro σ hσ hσ3 B hB hBc hBO
  have hinj : Function.Injective (MulAut.congr e).toMonoidHom := (MulAut.congr e).injective
  have hinn : (innerAut S).map (MulAut.congr e).toMonoidHom = innerAut T :=
    CFSG.ComponentClassification.OuterAutomorphisms.inner_map_congr e
  refine h (MulAut.congr e σ) ?_ ?_ (B.map e.toMonoidHom)
    (isElemAbelian_map_of_hom hB e.toMonoidHom) ?_ ?_
  · intro hm
    apply hσ
    exact (Subgroup.mem_map_iff_mem hinj).mp (by rw [hinn]; exact hm)
  · rw [← map_pow, hσ3, map_one]
  · rw [Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective]
    exact hBc
  · rw [← oTwoThreeFixed_map_congr e σ]
    exact Subgroup.map_mono hBO

theorem NoOuterData.of_mulEquiv {S T : Type} [Group S] [Group T] [Finite S] [Finite T]
    (e : S ≃* T) (h : NoOuterData T) : NoOuterData S :=
  fun _ _ _ _ hd => h _ _ _ _ (outerData_map_congr e hd)

theorem noOuterData_of_noOmega {S : Type} [Group S] [Finite S] (hZ : Subgroup.center S = ⊥)
    (h : NoOmega S) : NoOuterData S := by
  intro P A B c hd
  have hκ : Function.Injective (MulAut.conj : S →* MulAut S) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hxZ : x ∈ (⊥ : Subgroup S) := by
      rw [← hZ]
      exact (conj_eq_one_iff_mem_center x).mp hx
    exact Subgroup.mem_bot.mp hxZ
  have hBle : B ≤ (MulAut.conj : S →* MulAut S).range := hd.le_inner
  have hB'map : (B.comap (MulAut.conj : S →* MulAut S)).map (MulAut.conj : S →* MulAut S) = B :=
    Subgroup.map_comap_eq_self hBle
  have hcardB' : Nat.card (B.comap (MulAut.conj : S →* MulAut S)) = 9 := by
    have h1 := Subgroup.card_map_of_injective (K := B.comap (MulAut.conj : S →* MulAut S)) hκ
    rw [hB'map, hd.card_B] at h1
    exact h1.symm
  have hcA : c ∈ A := by rw [hd.eq_sup]; exact Subgroup.mem_sup_left (Subgroup.mem_zpowers c)
  have hc3 : c ^ 3 = 1 := hd.isElemAbelian.2 c hcA
  have hsub : B.comap (MulAut.conj : S →* MulAut S) ≤ oTwoThreeFixed c := by
    intro x hx
    obtain ⟨o, ho, hoe⟩ := Subgroup.mem_map.mp (hd.omega (Subgroup.mem_comap.mp hx))
    have hox : o = x := hκ hoe
    rw [hox] at ho
    exact ho
  exact h c hd.outer hc3 _ (isElemAbelian_comap_of_injective hκ
    (isElemAbelian_of_le hd.isElemAbelian hd.le_B)) hcardB' hsub

theorem OuterCase.of_autNoE27 {P : (S : Type) → [Group S] → Prop}
    (h : ∀ (S : Type) [Group S] [Finite S], P S → AutNoE27 S) : OuterCase P :=
  OuterCase.of_noOuterData fun S _ _ hP => noOuterData_of_autNoE27 (h S hP)

theorem OuterCase.of_not_three_dvd_outer {P : (S : Type) → [Group S] → Prop}
    (h : ∀ (S : Type) [Group S] [Finite S], P S → ¬ 3 ∣ Nat.card (Outer S)) : OuterCase P :=
  OuterCase.of_noOuterData fun S _ _ hP => noOuterData_of_not_three_dvd_outer (h S hP)

theorem noOmega_of_fixed_facts {S : Type} [Group S] [Finite S]
    (h : ∀ σ : MulAut S, σ ∉ innerAut S → σ ^ 3 = 1 →
      (∃ N : Subgroup (fixedSubgroup σ), N.Normal ∧ IsSimpleGroup N ∧
          ¬ (∀ x y : N, x * y = y * x) ∧ Subgroup.centralizer (N : Set (fixedSubgroup σ)) = ⊥) ∨
        ¬ 9 ∣ Nat.card (fixedSubgroup σ)) : NoOmega S := by
  intro σ hσ hσ3 B _ hBc hBO
  rcases h σ hσ hσ3 with ⟨N, hN, hsimp, hna, hcent⟩ | hnd
  · haveI := hN
    have hO := oTwoP_le_centralizer_of_simple_normal N hsimp hna
    rw [hcent] at hO
    have hB0 : B ≤ ⊥ := by
      intro b hb
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp (hBO hb)
      have hx1 : x = 1 := Subgroup.mem_bot.mp (hO hx)
      rw [Subgroup.mem_bot]
      simp [hx1]
    have hBbot : B = ⊥ := le_bot_iff.mp hB0
    rw [hBbot, Subgroup.card_bot] at hBc
    omega
  · apply hnd
    have hBH : B ≤ fixedSubgroup σ := fun b hb => Subgroup.map_subtype_le _ (hBO hb)
    have hdvd := Subgroup.card_dvd_of_le hBH
    rw [hBc] at hdvd
    exact hdvd

end CFSG.RankThree.PartTwo.Sec18.Item185Proof
