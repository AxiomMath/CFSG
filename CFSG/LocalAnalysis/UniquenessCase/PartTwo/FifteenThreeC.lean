module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThreeS
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThreeY

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

section Generic

private theorem s15_Three_commSub_conj {V : Type} [CommGroup V] (K : Subgroup (MulAut V))
    (ν : MulAut V) :
    commSub ⊤ (K.map (MulAut.conj ν).toMonoidHom) = (commSub ⊤ K).map ν.toMonoidHom := by
  have key : ∀ (x : MulAut V) (w : V),
      (MulAut.conj ν) x w * w⁻¹ = ν (x (ν⁻¹ w) * (ν⁻¹ w)⁻¹) := by
    intro x w
    rw [MulAut.conj_apply]
    simp only [MulAut.mul_apply, map_mul, map_inv]
    simp
  have key' : ∀ (x : MulAut V) (w : V),
      ν (x w * w⁻¹) = (MulAut.conj ν) x (ν w) * (ν w)⁻¹ := by
    intro x w
    rw [MulAut.conj_apply]
    simp only [MulAut.mul_apply, map_mul, map_inv]
    simp
  apply le_antisymm
  · rw [commSub, Subgroup.closure_le]
    rintro _ ⟨x, hx, w, -, rfl⟩
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.1 hx
    exact Subgroup.mem_map.2 ⟨k (ν⁻¹ w) * (ν⁻¹ w)⁻¹,
      Subgroup.subset_closure ⟨k, hk, ν⁻¹ w, trivial, rfl⟩, (key k w).symm⟩
  · rw [Subgroup.map_le_iff_le_comap, commSub, Subgroup.closure_le]
    rintro _ ⟨k, hk, w, -, rfl⟩
    change ν (k w * w⁻¹) ∈ commSub ⊤ (K.map (MulAut.conj ν).toMonoidHom)
    rw [key' k w]
    exact Subgroup.subset_closure
      ⟨(MulAut.conj ν) k, Subgroup.mem_map.2 ⟨k, hk, rfl⟩, ν w, trivial, rfl⟩

private theorem s15_Three_stab_conj {V : Type} [CommGroup V] [Finite V] {E : Subgroup (MulAut V)}
    (ν : MulAut V) {z : V} (h : ∀ e ∈ E, e z = z) :
    ∀ e ∈ E.map (MulAut.conj ν).toMonoidHom, e (ν z) = ν z := by
  rintro e ⟨e', he', rfl⟩
  show (MulAut.conj ν) e' (ν z) = ν z
  rw [MulAut.conj_apply]
  simp only [MulAut.mul_apply]
  rw [show (ν⁻¹ : MulAut V) (ν z) = z by simp, h e' he']

private theorem s15_Three_table_conj (hT : RTable137) {V : Type} [CommGroup V] [Finite V]
    (hV2 : ∀ v : V, v ^ 2 = 1) {X : Type} [Group X] {K : Subgroup (MulAut V)}
    (hK : s15KNatPerf X K (commSub ⊤ K)) (ν : MulAut V) :
    ∀ z ∈ (commSub ⊤ K).map ν.toMonoidHom, ∃ E : Subgroup (MulAut V),
      E ≤ K.map (MulAut.conj ν).toMonoidHom ∧ CFSG.Open.IsElemAbelian 3 E ∧ Nat.card E = 3 ∧
        ∀ e ∈ E, e z = z := by
  intro z hz
  obtain ⟨z', hz', rfl⟩ := Subgroup.mem_map.1 hz
  have hrank : 1 ≤ CFSG.Open.pRank 3 (K ⊓ MulAction.stabilizer (MulAut V) z') :=
    (hT V hV2 K (commSub ⊤ K) X hK).1 z' hz'
  obtain ⟨E', hE'le, hE'elem, hE'card⟩ :=
    CFSG.SectionRank.exists_isElemAbelian_card_of_le_pRank (p := 3)
      (H := K ⊓ MulAction.stabilizer (MulAut V) z') (k := 1) hrank
  refine ⟨E'.map (MulAut.conj ν).toMonoidHom, Subgroup.map_mono (hE'le.trans inf_le_left),
    ?_, ?_, ?_⟩
  · exact CFSG.SectionRank.isElemAbelian_map hE'elem (MulAut.conj ν).toMonoidHom
  · rw [Subgroup.card_map_of_injective (MulAut.conj ν).injective, hE'card]
    norm_num
  · have hfix : ∀ e ∈ E', e z' = z' := fun e he =>
      MulAction.mem_stabilizer_iff.1 (hE'le he).2
    simpa using s15_Three_stab_conj (E := E') ν hfix

private theorem s15_Three_trivial_on_conj (hAbs : RAbsIrr153) {V : Type} [CommGroup V] [Finite V]
    (hV2 : ∀ v : V, v ^ 2 = 1) {X : Type} [Group X] {K : Subgroup (MulAut V)}
    (hK : s15KNatPerf X K (commSub ⊤ K)) (ν : MulAut V) {a : MulAut V}
    (hcomm : ∀ k ∈ K.map (MulAut.conj ν).toMonoidHom, a * k = k * a) :
    ∀ z ∈ (commSub ⊤ K).map ν.toMonoidHom, a z = z := by
  have hcomm' : ∀ k ∈ K, (ν⁻¹ * a * ν) * k = k * (ν⁻¹ * a * ν) := by
    intro k hk
    have hk' : (MulAut.conj ν) k ∈ K.map (MulAut.conj ν).toMonoidHom :=
      Subgroup.mem_map.2 ⟨k, hk, rfl⟩
    have h1 := hcomm ((MulAut.conj ν) k) hk'
    rw [MulAut.conj_apply] at h1
    calc (ν⁻¹ * a * ν) * k = ν⁻¹ * (a * (ν * k * ν⁻¹)) * ν := by group
      _ = ν⁻¹ * ((ν * k * ν⁻¹) * a) * ν := by rw [h1]
      _ = k * (ν⁻¹ * a * ν) := by group
  have hKmap : K.map (MulAut.conj (ν⁻¹ * a * ν)).toMonoidHom = K := by
    ext x
    constructor
    · rintro ⟨k, hk, rfl⟩
      change (MulAut.conj (ν⁻¹ * a * ν)) k ∈ K
      rw [MulAut.conj_apply]
      have h1 := hcomm' k hk
      rw [h1, show (k * (ν⁻¹ * a * ν)) * (ν⁻¹ * a * ν)⁻¹ = k by group]
      exact hk
    · intro hx
      refine ⟨x, hx, ?_⟩
      change (MulAut.conj (ν⁻¹ * a * ν)) x = x
      rw [MulAut.conj_apply]
      have h1 := hcomm' x hx
      rw [h1]
      group
  have hZmap : (commSub ⊤ K).map (ν⁻¹ * a * ν).toMonoidHom = commSub ⊤ K := by
    rw [← s15_Three_commSub_conj K (ν⁻¹ * a * ν), hKmap]
  have hstab : (ν⁻¹ * a * ν) ∈ stabSub (commSub ⊤ K) := by
    rw [mem_stabSub]
    intro u
    constructor
    · intro hu
      have h1 : (ν⁻¹ * a * ν) u ∈ (commSub ⊤ K).map (ν⁻¹ * a * ν).toMonoidHom := by
        rw [hZmap]; exact hu
      obtain ⟨w, hw, hwu⟩ := Subgroup.mem_map.1 h1
      rwa [(ν⁻¹ * a * ν).injective hwu] at hw
    · intro hu
      have h1 : (ν⁻¹ * a * ν) u ∈ (commSub ⊤ K).map (ν⁻¹ * a * ν).toMonoidHom :=
        Subgroup.mem_map_of_mem (ν⁻¹ * a * ν).toMonoidHom hu
      rwa [hZmap] at h1
  have hfix := hAbs V hV2 X K (commSub ⊤ K) hK (ν⁻¹ * a * ν) hstab hcomm'
  intro z hz
  obtain ⟨z', hz', rfl⟩ := Subgroup.mem_map.1 hz
  have hgz : (ν⁻¹ * a * ν) z' = z' := hfix z' hz'
  have h1 : ν ((ν⁻¹ * a * ν) z') = a (ν z') := by
    simp only [MulAut.mul_apply]
    simp
  change a (ν z') = ν z'
  rw [← h1, hgz]

private theorem s15_Three_split_family {V : Type} [CommGroup V] {𝒵 : Set (Subgroup V)}
    {Z : Subgroup V} (hZ : Z ∈ 𝒵) {z : V} (hz : z ∈ sSup 𝒵) :
    ∃ z₁ ∈ Z, ∃ r ∈ sSup (𝒵 \ {Z}), z = z₁ * r := by
  have hins : insert Z (𝒵 \ {Z}) = 𝒵 := by
    ext X
    constructor
    · rintro (rfl | ⟨hX, -⟩)
      · exact hZ
      · exact hX
    · intro hX
      by_cases h : X = Z
      · exact Or.inl h
      · exact Or.inr ⟨hX, by simpa using h⟩
  have hsup : sSup 𝒵 = Z ⊔ sSup (𝒵 \ {Z}) := by
    conv_lhs => rw [← hins, sSup_insert]
  have hz' : z ∈ Z ⊔ sSup (𝒵 \ {Z}) := by rw [← hsup]; exact hz
  obtain ⟨z₁, hz₁, r, hr, hzr⟩ := Subgroup.mem_sup.1 hz'
  exact ⟨z₁, hz₁, r, hr, hzr.symm⟩

private theorem s15_Three_eq_one_of_fixes {V : Type} [CommGroup V] {𝒳 : Set (Subgroup V)}
    (hsup : sSup 𝒳 = ⊤) {g : MulAut V} (hfix : ∀ Z ∈ 𝒳, ∀ u ∈ Z, g u = u) : g = 1 := by
  have htop : fixV (Subgroup.zpowers g) = ⊤ := by
    refine top_le_iff.1 (hsup ▸ sSup_le ?_)
    intro Z hZ u hu
    rw [mem_fixV]
    intro x hx
    have hle : Subgroup.zpowers g ≤ MulAction.stabilizer (MulAut V) u := by
      rw [Subgroup.zpowers_le]
      simpa [MulAction.mem_stabilizer_iff] using hfix Z hZ u hu
    exact MulAction.mem_stabilizer_iff.1 (hle hx)
  ext u
  exact (mem_fixV.1 (by rw [htop]; trivial)) g (Subgroup.mem_zpowers g)

private theorem s15_Three_pGroup_not_cyclic_of_card_nine {A : Type} [Group A] [Finite A]
    {E : Subgroup A} (hpow : ∀ x ∈ E, x ^ 3 = 1) (hcard : Nat.card E = 3 ^ 2) :
    IsPGroup 3 ↥E ∧ ¬ IsCyclic ↥E := by
  constructor
  · exact IsPGroup.of_card hcard
  · intro hcyc
    haveI := hcyc
    have hexp : Monoid.exponent ↥E = 9 := by
      rw [IsCyclic.exponent_eq_card, hcard]
      norm_num
    have hdvd : Monoid.exponent ↥E ∣ 3 :=
      Monoid.exponent_dvd_iff_forall_pow_eq_one.2 fun g => Subtype.ext (hpow g g.2)
    rw [hexp] at hdvd
    have := Nat.le_of_dvd (by norm_num) hdvd
    omega

private theorem s15_Three_sup_noncyclic {A : Type} [Group A] [Finite A] {E₁ E₂ : Subgroup A}
    (h₁ : Nat.card E₁ = 3) (h₂ : Nat.card E₂ = 3) (hne : E₁ ≠ E₂)
    (hcomm : ∀ x ∈ E₁, ∀ y ∈ E₂, x * y = y * x) :
    IsPGroup 3 ↥(E₁ ⊔ E₂) ∧ ¬ IsCyclic ↥(E₁ ⊔ E₂) := by
  have hle₁ : E₁ ≤ E₁ ⊔ E₂ := le_sup_left
  have hle₂ : E₂ ≤ E₁ ⊔ E₂ := le_sup_right
  have hnecyc : ¬ IsCyclic ↥(E₁ ⊔ E₂) := by
    intro hcyc
    haveI := hcyc
    have hc₁ : Nat.card ↥(E₁.subgroupOf (E₁ ⊔ E₂)) = 3 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle₁).toEquiv, h₁]
    have hc₂ : Nat.card ↥(E₂.subgroupOf (E₁ ⊔ E₂)) = 3 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle₂).toEquiv, h₂]
    have heq : E₁.subgroupOf (E₁ ⊔ E₂) = E₂.subgroupOf (E₁ ⊔ E₂) :=
      (IsCyclic.subgroup_eq_iff_card_eq).2 (by rw [hc₁, hc₂])
    have hinf := Subgroup.subgroupOf_inj.1 heq
    rw [inf_eq_left.2 hle₁, inf_eq_left.2 hle₂] at hinf
    exact hne hinf
  refine ⟨?_, hnecyc⟩
  let f : ↥E₁ × ↥E₂ →* A :=
    { toFun := fun p => (p.1 : A) * (p.2 : A)
      map_one' := by simp
      map_mul' := by
        rintro ⟨a₁, a₂⟩ ⟨b₁, b₂⟩
        have h : (b₁ : A) * (a₂ : A) = (a₂ : A) * (b₁ : A) := hcomm b₁ b₁.2 a₂ a₂.2
        show ((a₁ : A) * (b₁ : A)) * ((a₂ : A) * (b₂ : A)) =
          ((a₁ : A) * (a₂ : A)) * ((b₁ : A) * (b₂ : A))
        calc ((a₁ : A) * (b₁ : A)) * ((a₂ : A) * (b₂ : A))
            = (a₁ : A) * ((b₁ : A) * (a₂ : A)) * (b₂ : A) := by group
          _ = (a₁ : A) * ((a₂ : A) * (b₁ : A)) * (b₂ : A) := by rw [h]
          _ = ((a₁ : A) * (a₂ : A)) * ((b₁ : A) * (b₂ : A)) := by group }
  have hrange : f.range = E₁ ⊔ E₂ := by
    apply le_antisymm
    · rintro x ⟨p, rfl⟩
      exact mul_mem (Subgroup.mem_sup_left p.1.2) (Subgroup.mem_sup_right p.2.2)
    · refine sup_le ?_ ?_
      · intro x hx
        exact ⟨(⟨x, hx⟩, 1), by simp [f]⟩
      · intro y hy
        exact ⟨(1, ⟨y, hy⟩), by simp [f]⟩
  have hprod : IsPGroup 3 (↥E₁ × ↥E₂) := by
    have hc : Nat.card (↥E₁ × ↥E₂) = 3 ^ 2 := by
      rw [Nat.card_prod, h₁, h₂]; norm_num
    exact IsPGroup.of_card hc
  have hmap : IsPGroup 3 ↥f.range := by
    rw [MonoidHom.range_eq_map]
    exact IsPGroup.map (hprod.to_subgroup ⊤) f
  rwa [hrange] at hmap

end Generic


section Components

variable {D : Data G} {V₀ V L K₀ : Subgroup G}

private theorem s15_Three_conjSubgroup_le {K M : Subgroup G} (hK : K ≤ M) {m : G} (hm : m ∈ M) :
    conjSubgroup K m ≤ M := by
  intro x hx
  rw [mem_conjSubgroup_iff] at hx
  have h1 := M.mul_mem (M.mul_mem (M.inv_mem hm) (hK hx)) hm
  rwa [show m⁻¹ * (m * x * m⁻¹) * m = x by group] at h1

private theorem s15_ThreeC_barSub_conj_eq {W₀ : Subgroup G} (hV : IsElemAbelian 2 V)
    (hMs : D.M ≤ stabTil W₀ V) (hK : K₀ ≤ D.M) {m : G} (hm : m ∈ D.M) :
    barSub W₀ V hV (conjSubgroup K₀ m) =
      (barSub W₀ V hV K₀).map
        (MulAut.conj (actTil W₀ V hV ⟨m⁻¹, hMs (D.M.inv_mem hm)⟩)).toMonoidHom :=
  TwelveTwentyThree.barSub_map_conj (V₀ := W₀) (V := V) hV (hK.trans hMs) (hMs (D.M.inv_mem hm))

private theorem s15_Three_commute_star (D : Data G) (h1217 : R1217 D) (h : Hyp151 D V₀ V L)
    (hV : IsElemAbelian 2 V) {a b : G} (ha : a ∈ D.M) (hb : b ∈ D.M)
    (ha0 : a ∈ stabTil V₀ V) (hb0 : b ∈ stabTil V₀ V)
    (ha1 : a ∈ stabTil (v1Sub D.M V₀ V hV L) V) (hb1 : b ∈ stabTil (v1Sub D.M V₀ V hV L) V)
    (hab : actTil V₀ V hV ⟨a, ha0⟩ * actTil V₀ V hV ⟨b, hb0⟩ =
      actTil V₀ V hV ⟨b, hb0⟩ * actTil V₀ V hV ⟨a, ha0⟩) :
    actTil (v1Sub D.M V₀ V hV L) V hV ⟨a, ha1⟩ * actTil (v1Sub D.M V₀ V hV L) V hV ⟨b, hb1⟩ =
      actTil (v1Sub D.M V₀ V hV L) V hV ⟨b, hb1⟩ *
        actTil (v1Sub D.M V₀ V hV L) V hV ⟨a, ha1⟩ := by
  have hM := h.hyp125.pairFacts.le_normalizer
  have hc := fifteen_two_cent D h1217 h hV
  have hs0 : a * b * a⁻¹ * b⁻¹ ∈ stabTil V₀ V :=
    (stabTil V₀ V).mul_mem ((stabTil V₀ V).mul_mem ((stabTil V₀ V).mul_mem ha0 hb0)
      ((stabTil V₀ V).inv_mem ha0)) ((stabTil V₀ V).inv_mem hb0)
  have hmem : a * b * a⁻¹ * b⁻¹ ∈ F11.CTilde D.M V₀ V := by
    rw [mem_cTilde_iff hV hM]
    refine ⟨D.M.mul_mem (D.M.mul_mem (D.M.mul_mem ha hb) (D.M.inv_mem ha)) (D.M.inv_mem hb),
      hs0, ?_⟩
    have : (⟨a * b * a⁻¹ * b⁻¹, hs0⟩ : stabTil V₀ V) =
        ⁅(⟨a, ha0⟩ : stabTil V₀ V), ⟨b, hb0⟩⁆ := rfl
    rw [this, map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.2 hab
  rw [← hc, mem_cTilde_iff hV hM] at hmem
  obtain ⟨-, hs1, h1⟩ := hmem
  have : (⟨a * b * a⁻¹ * b⁻¹, hs1⟩ : stabTil (v1Sub D.M V₀ V hV L) V) =
      ⁅(⟨a, ha1⟩ : stabTil (v1Sub D.M V₀ V hV L) V),
        ⟨b, hb1⟩⁆ := rfl
  rw [this, map_commutatorElement] at h1
  exact commutatorElement_eq_one_iff_mul_comm.1 h1

private theorem s15_Three_star_comm_or_eq (h1217 : R1217 D) (h : Hyp151 D V₀ V L)
    (hV : IsElemAbelian 2 V) (hshape : s15Shape D V₀ V hV L K₀) {m₁ m₂ : G}
    (hm₁ : m₁ ∈ D.M) (hm₂ : m₂ ∈ D.M) :
    barSub (v1Sub D.M V₀ V hV L) V hV (conjSubgroup K₀ m₁) =
      barSub (v1Sub D.M V₀ V hV L) V hV (conjSubgroup K₀ m₂) ∨
      ∀ x ∈ barSub (v1Sub D.M V₀ V hV L) V hV (conjSubgroup K₀ m₁),
        ∀ y ∈ barSub (v1Sub D.M V₀ V hV L) V hV (conjSubgroup K₀ m₂), x * y = y * x := by
  have hK0M : K₀ ≤ D.M := hshape.1.trans h.le
  have hc₁ : conjSubgroup K₀ m₁ ≤ D.M := s15_Three_conjSubgroup_le hK0M hm₁
  have hc₂ : conjSubgroup K₀ m₂ ≤ D.M := s15_Three_conjSubgroup_le hK0M hm₂
  have hMs0 : D.M ≤ stabTil V₀ V :=
    le_stabTil h.hyp125.pairFacts.le_normalizer h.hyp125.pairFacts.le_normalizer₀
  rcases s15_Three_xbar_comm h hV hshape hm₁ hm₂ with heq | hcomm
  · exact Or.inl ((s15_Three_barSub_star_iff D h1217 h hc₁ hc₂).1 heq)
  · refine Or.inr ?_
    intro x hx y hy
    obtain ⟨g, hgX, rfl⟩ :=
      (mem_barSub (v1Sub D.M V₀ V hV L) V hV (conjSubgroup K₀ m₁) x).1 hx
    obtain ⟨g', hg'X, rfl⟩ :=
      (mem_barSub (v1Sub D.M V₀ V hV L) V hV (conjSubgroup K₀ m₂) y).1 hy
    have hgM : (g : G) ∈ D.M := hc₁ hgX
    have hg'M : (g' : G) ∈ D.M := hc₂ hg'X
    have h0 : actTil V₀ V hV ⟨(g : G), hMs0 hgM⟩ * actTil V₀ V hV ⟨(g' : G), hMs0 hg'M⟩ =
        actTil V₀ V hV ⟨(g' : G), hMs0 hg'M⟩ * actTil V₀ V hV ⟨(g : G), hMs0 hgM⟩ :=
      hcomm _ (actTil_mem_barSub V₀ V hV hgX (hMs0 hgM)) _
        (actTil_mem_barSub V₀ V hV hg'X (hMs0 hg'M))
    exact s15_Three_commute_star D h1217 h hV hgM hg'M (hMs0 hgM) (hMs0 hg'M) g.2 g'.2 h0

theorem s15_Three_two_components (h1217 : R1217 D) (h : Hyp151 D V₀ V L)
    (hV : IsElemAbelian 2 V) (hshape : s15Shape D V₀ V hV L K₀)
    (hrs : s15Rs D V₀ V hV L K₀ ≠ 1) :
    ∃ m₁ ∈ D.M, ∃ m₂ ∈ D.M,
      barSub (v1Sub D.M V₀ V hV L) V hV (conjSubgroup K₀ m₁) ≠
        barSub (v1Sub D.M V₀ V hV L) V hV (conjSubgroup K₀ m₂) := by
  by_contra hcon
  push Not at hcon
  have hK0M : K₀ ≤ D.M := hshape.1.trans h.le
  have hMs0 : D.M ≤ stabTil V₀ V :=
    le_stabTil h.hyp125.pairFacts.le_normalizer h.hyp125.pairFacts.le_normalizer₀
  have hbar0 : ∀ m ∈ D.M, barSub V₀ V hV (conjSubgroup K₀ m) = barSub V₀ V hV K₀ := by
    intro m hm
    rw [s15_Three_barSub_star_iff D h1217 h (s15_Three_conjSubgroup_le hK0M hm) hK0M]
    rw [hcon m hm 1 (Subgroup.one_mem _), conjSubgroup_one]
  have hconjK : ∀ {m : G} (hm : m ∈ D.M),
      (barSub V₀ V hV K₀).map (MulAut.conj (actTil V₀ V hV ⟨m, hMs0 hm⟩)).toMonoidHom =
        barSub V₀ V hV K₀ := by
    intro m hm
    have h : conjSubgroup K₀ m⁻¹ = K₀.map (MulAut.conj m).toMonoidHom := by
      rw [conjSubgroup, inv_inv]
    rw [← TwelveTwentyThree.barSub_map_conj (V₀ := V₀) (V := V) hV
      (hK0M.trans hMs0) (hMs0 hm), ← h]
    exact hbar0 m⁻¹ (D.M.inv_mem hm)
  have hconjSet : conjSet (barSub V₀ V hV K₀) (s15NBar D V₀ V hV L) =
      {barSub V₀ V hV K₀} := by
    apply le_antisymm
    · rintro Y ⟨n, hn, rfl⟩
      rw [Set.mem_singleton_iff]
      obtain ⟨g, hgM, hgn⟩ := (mem_barSub V₀ V hV D.M n).1 hn.1
      rw [← hgn]
      rw [show actTil V₀ V hV g = actTil V₀ V hV ⟨(g : G), hMs0 hgM⟩ from
        congrArg (actTil V₀ V hV) (Subtype.ext rfl)]
      exact hconjK hgM
    · rintro Y rfl
      exact ⟨1, Subgroup.one_mem _, by ext x; simp⟩
  have hr : (conjSet (barSub V₀ V hV K₀) (s15NBar D V₀ V hV L)).ncard = 1 := by
    rw [hconjSet, Set.ncard_singleton]
  have hLK : barSub V₀ V hV L = barSub V₀ V hV K₀ :=
    s15_Three_eq_of_ncard_conjSet hshape.2.2.1 hr
  have hs : s15 D.M V₀ V hV L = 1 := by
    unfold s15
    rw [Set.ncard_eq_one]
    refine ⟨barSub V₀ V hV L, ?_⟩
    ext Y
    constructor
    · rintro ⟨φ, hφ, rfl⟩
      rw [Set.mem_singleton_iff]
      obtain ⟨g, hgM, hgφ⟩ := (mem_barSub V₀ V hV D.M φ).1 hφ
      rw [← hgφ]
      rw [show actTil V₀ V hV g = actTil V₀ V hV ⟨(g : G), hMs0 hgM⟩ from
        congrArg (actTil V₀ V hV) (Subtype.ext rfl)]
      rw [hLK]
      exact hconjK hgM
    · rintro rfl
      exact ⟨1, Subgroup.one_mem _, by ext x; simp⟩
  exact hrs ((s15_Three_rs_eq_one_iff D V₀ V hV L K₀).2 ⟨hr, hs⟩)

theorem s15_Three_stab_two (hT : RTable137) (hAbs : RAbsIrr153) (h1217 : R1217 D)
    (h : Hyp151 D V₀ V L) (hV : IsElemAbelian 2 V) (hshape : s15Shape D V₀ V hV L K₀)
    (hperf : s15KNatPerf ↥(barSub V₀ V hV K₀) (barSub (v1Sub D.M V₀ V hV L) V hV K₀)
      (commSub ⊤ (barSub (v1Sub D.M V₀ V hV L) V hV K₀)))
    {m₁ m₂ : G} (hm₁ : m₁ ∈ D.M) (hm₂ : m₂ ∈ D.M)
    (hne : barSub (v1Sub D.M V₀ V hV L) V hV (conjSubgroup K₀ m₁) ≠
      barSub (v1Sub D.M V₀ V hV L) V hV (conjSubgroup K₀ m₂))
    (z : vStar D.M V₀ V hV L) :
    ∃ E : Subgroup (MulAut (vStar D.M V₀ V hV L)), E ≤ s15XStar D V₀ V hV L K₀ ∧
      IsPGroup 3 E ∧ ¬ IsCyclic E ∧ ∀ e ∈ E, e z = z := by
  classical
  have hV2 : ∀ v : vStar D.M V₀ V hV L, v ^ 2 = 1 :=
    s15_Infra_vtil_sq_eq_one (v1Sub D.M V₀ V hV L) V hV
  have hMs1 : D.M ≤ stabTil (v1Sub D.M V₀ V hV L) V :=
    le_stabTil h.hyp125.pairFacts.le_normalizer (s15_Infra_le_normalizer_v1Sub h.hyp125 hV)
  let ν : (m : G) → m ∈ D.M → MulAut (vStar D.M V₀ V hV L) :=
    fun m hm => actTil (v1Sub D.M V₀ V hV L) V hV ⟨m⁻¹, hMs1 (D.M.inv_mem hm)⟩
  have hbar1 : ∀ {m : G} (hm : m ∈ D.M),
      barSub (v1Sub D.M V₀ V hV L) V hV (conjSubgroup K₀ m) =
        (barSub (v1Sub D.M V₀ V hV L) V hV K₀).map (MulAut.conj (ν m hm)).toMonoidHom := by
    intro m hm
    exact s15_ThreeC_barSub_conj_eq (W₀ := v1Sub D.M V₀ V hV L) hV hMs1
      (hshape.1.trans h.le) hm
  have hZm : ∀ {m : G} (hm : m ∈ D.M),
      commSub ⊤ (barSub (v1Sub D.M V₀ V hV L) V hV (conjSubgroup K₀ m)) =
        (commSub ⊤ (barSub (v1Sub D.M V₀ V hV L) V hV K₀)).map (ν m hm).toMonoidHom := by
    intro m hm
    rw [hbar1 hm, s15_Three_commSub_conj]
  let Zof : G → Subgroup (vStar D.M V₀ V hV L) :=
    fun m => commSub ⊤ (barSub (v1Sub D.M V₀ V hV L) V hV (conjSubgroup K₀ m))
  have htriv : ∀ {i m : G} (hi : i ∈ D.M) (hm : m ∈ D.M),
      barSub (v1Sub D.M V₀ V hV L) V hV (conjSubgroup K₀ m) ≠
        barSub (v1Sub D.M V₀ V hV L) V hV (conjSubgroup K₀ i) →
      ∀ z ∈ commSub ⊤ (barSub (v1Sub D.M V₀ V hV L) V hV (conjSubgroup K₀ m)),
        ∀ a ∈ barSub (v1Sub D.M V₀ V hV L) V hV (conjSubgroup K₀ i), a z = z := by
    intro i m hi hm hne' u hu a ha
    rcases s15_Three_star_comm_or_eq h1217 h hV hshape hi hm with heq | hcomm
    · exact absurd heq.symm hne'
    · have hcomm' : ∀ k ∈ (barSub (v1Sub D.M V₀ V hV L) V hV K₀).map
          (MulAut.conj (ν m hm)).toMonoidHom, a * k = k * a := by
        intro k hk
        have hk' : k ∈ barSub (v1Sub D.M V₀ V hV L) V hV (conjSubgroup K₀ m) := by
          rw [hbar1 hm]; exact hk
        exact hcomm a ha k hk'
      have hu' : u ∈ (commSub ⊤ (barSub (v1Sub D.M V₀ V hV L) V hV K₀)).map
          (ν m hm).toMonoidHom := by rw [← hZm hm]; exact hu
      exact s15_Three_trivial_on_conj hAbs hV2 hperf (ν m hm) hcomm' u hu'
  let 𝒵 : Set (Subgroup (vStar D.M V₀ V hV L)) :=
    {Z | ∃ m ∈ D.M, Z = commSub ⊤
      (barSub (v1Sub D.M V₀ V hV L) V hV (conjSubgroup K₀ m))}
  have hZ₁ : commSub ⊤ (barSub (v1Sub D.M V₀ V hV L) V hV (conjSubgroup K₀ m₁)) ∈ 𝒵 :=
    ⟨m₁, hm₁, rfl⟩
  have hZ₂ : commSub ⊤ (barSub (v1Sub D.M V₀ V hV L) V hV (conjSubgroup K₀ m₂)) ∈ 𝒵 :=
    ⟨m₂, hm₂, rfl⟩
  have hind : sSupIndep 𝒵 := hshape.2.2.2.2.1
  have hsup : sSup 𝒵 = ⊤ := hshape.2.2.2.2.2
  have hfixsup : ∀ {i : G} (hi : i ∈ D.M),
      ∀ a ∈ barSub (v1Sub D.M V₀ V hV L) V hV (conjSubgroup K₀ i),
      ∀ w ∈ sSup (𝒵 \ {Zof i}), a w = w := by
    intro i hi a ha w hw
    have hle : sSup (𝒵 \ {Zof i}) ≤
        fixV (barSub (v1Sub D.M V₀ V hV L) V hV (conjSubgroup K₀ i)) := by
      refine sSup_le fun Z hZ => ?_
      obtain ⟨hZ𝒵, hZne⟩ := hZ
      obtain ⟨m, hm, rfl⟩ := hZ𝒵
      have hne' : barSub (v1Sub D.M V₀ V hV L) V hV (conjSubgroup K₀ m) ≠
          barSub (v1Sub D.M V₀ V hV L) V hV (conjSubgroup K₀ i) := by
        intro heq
        exact hZne (by simpa only [Set.mem_singleton_iff] using congrArg (commSub ⊤) heq)
      intro u hu
      rw [mem_fixV]
      intro a ha
      exact htriv hi hm hne' u hu a ha
    exact (mem_fixV.1 (hle hw)) a ha
  obtain ⟨z₁, hz₁, w₁, hw₁, hz₁w₁⟩ :=
    s15_Three_split_family (z := z) hZ₁ (by rw [hsup]; trivial)
  obtain ⟨z₂, hz₂, w₂, hw₂, hz₂w₂⟩ :=
    s15_Three_split_family (z := z) hZ₂ (by rw [hsup]; trivial)
  obtain ⟨E₁, hE₁le, hE₁elem, hE₁card, hE₁fix⟩ :=
    s15_Three_table_conj hT hV2 hperf (ν m₁ hm₁) z₁ (by rw [← hZm hm₁]; exact hz₁)
  obtain ⟨E₂, hE₂le, hE₂elem, hE₂card, hE₂fix⟩ :=
    s15_Three_table_conj hT hV2 hperf (ν m₂ hm₂) z₂ (by rw [← hZm hm₂]; exact hz₂)
  have hE₁le' : E₁ ≤ barSub (v1Sub D.M V₀ V hV L) V hV (conjSubgroup K₀ m₁) := by
    rw [hbar1 hm₁]; exact hE₁le
  have hE₂le' : E₂ ≤ barSub (v1Sub D.M V₀ V hV L) V hV (conjSubgroup K₀ m₂) := by
    rw [hbar1 hm₂]; exact hE₂le
  have hcommE : ∀ x ∈ E₁, ∀ y ∈ E₂, x * y = y * x := by
    intro x hx y hy
    rcases s15_Three_star_comm_or_eq h1217 h hV hshape hm₁ hm₂ with heq | hcomm
    · exact absurd heq hne
    · exact hcomm x (hE₁le' hx) y (hE₂le' hy)
  have hneE : E₁ ≠ E₂ := by
    intro hEq
    haveI : Fintype ↥E₁ := Fintype.ofFinite _
    haveI : Nontrivial ↥E₁ := by
      rw [← Fintype.one_lt_card_iff_nontrivial, ← Nat.card_eq_fintype_card, hE₁card]
      norm_num
    obtain ⟨g, hg_ne⟩ := exists_ne (1 : ↥E₁)
    have hg1 : (g : MulAut (vStar D.M V₀ V hV L)) ∈ E₁ := g.2
    have hg2 : (g : MulAut (vStar D.M V₀ V hV L)) ∈ E₂ := by rw [← hEq]; exact g.2
    have hfixall : ∀ Z ∈ 𝒵, ∀ u ∈ Z, (g : MulAut (vStar D.M V₀ V hV L)) u = u := by
      intro Z hZ u hu
      obtain ⟨m, hm, rfl⟩ := hZ
      by_cases hAm : barSub (v1Sub D.M V₀ V hV L) V hV (conjSubgroup K₀ m) =
          barSub (v1Sub D.M V₀ V hV L) V hV (conjSubgroup K₀ m₁)
      · exact htriv hm₂ hm (by rw [hAm]; exact hne) u hu _ (hE₂le' hg2)
      · exact htriv hm₁ hm hAm u hu _ (hE₁le' hg1)
    have hone : (g : MulAut (vStar D.M V₀ V hV L)) = 1 :=
      s15_Three_eq_one_of_fixes hsup hfixall
    exact hg_ne (Subtype.ext hone)
  have hE₁stab : E₁ ≤ MulAction.stabilizer (MulAut (vStar D.M V₀ V hV L)) z := by
    intro e he
    rw [MulAction.mem_stabilizer_iff]
    show e z = z
    rw [hz₁w₁, map_mul, hE₁fix e he, hfixsup hm₁ e (hE₁le' he) w₁ hw₁]
  have hE₂stab : E₂ ≤ MulAction.stabilizer (MulAut (vStar D.M V₀ V hV L)) z := by
    intro e he
    rw [MulAction.mem_stabilizer_iff]
    show e z = z
    rw [hz₂w₂, map_mul, hE₂fix e he, hfixsup hm₂ e (hE₂le' he) w₂ hw₂]
  have hleX₁ : barSub (v1Sub D.M V₀ V hV L) V hV (conjSubgroup K₀ m₁) ≤
      s15XStar D V₀ V hV L K₀ := le_iSup₂_of_le m₁ hm₁ le_rfl
  have hleX₂ : barSub (v1Sub D.M V₀ V hV L) V hV (conjSubgroup K₀ m₂) ≤
      s15XStar D V₀ V hV L K₀ := le_iSup₂_of_le m₂ hm₂ le_rfl
  refine ⟨E₁ ⊔ E₂, sup_le (hE₁le'.trans hleX₁) (hE₂le'.trans hleX₂), ?_, ?_, ?_⟩
  · exact (s15_Three_sup_noncyclic hE₁card hE₂card hneE hcommE).1
  · exact (s15_Three_sup_noncyclic hE₁card hE₂card hneE hcommE).2
  · intro e he
    exact MulAction.mem_stabilizer_iff.1 (sup_le hE₁stab hE₂stab he)

theorem s15_Three_perf_star (h1217 : R1217 D) (h : Hyp151 D V₀ V L) (hV : IsElemAbelian 2 V)
    (hshape : s15Shape D V₀ V hV L K₀) (hrs : s15Rs D V₀ V hV L K₀ = 1)
    (hperf : s15KNatPerf ↥(barSub V₀ V hV K₀) (barSub (v1Sub D.M V₀ V hV L) V hV K₀)
      (commSub ⊤ (barSub (v1Sub D.M V₀ V hV L) V hV K₀))) :
    s15KNatPerf ↥(lBar V₀ V hV L) (lStar D.M V₀ V hV L) (wStar D.M V₀ V hV L) := by
  have hLK := s15_Three_lBar_eq hshape hrs
  have hstar : lStar D.M V₀ V hV L = barSub (v1Sub D.M V₀ V hV L) V hV K₀ :=
    (s15_Three_barSub_star_iff D h1217 h h.le (hshape.1.trans h.le)).1 hLK
  have hW : commSub ⊤ (barSub (v1Sub D.M V₀ V hV L) V hV K₀) = wStar D.M V₀ V hV L := by
    rw [← hstar]
    exact s15_Three_commSub_top_lStar h hV
  rw [hW, ← hstar, ← hLK] at hperf
  exact hperf

private theorem s15_Three_star_equiv (D : Data G) (h1217 : R1217 D) (h : Hyp151 D V₀ V L)
    {X : Subgroup G} (hX : X ≤ D.M) :
    Nonempty (↥(barSub V₀ V h.isElemAbelian X) ≃*
      ↥(barSub (v1Sub D.M V₀ V h.isElemAbelian L) V h.isElemAbelian X)) := by
  have hM : D.M ≤ normalizer (V : Set G) := h.hyp125.pairFacts.le_normalizer
  have hMs0 : D.M ≤ stabTil V₀ V :=
    le_stabTil h.hyp125.pairFacts.le_normalizer h.hyp125.pairFacts.le_normalizer₀
  have hMs1 : D.M ≤ stabTil (v1Sub D.M V₀ V h.isElemAbelian L) V :=
    le_stabTil h.hyp125.pairFacts.le_normalizer
      (s15_Infra_le_normalizer_v1Sub h.hyp125 h.isElemAbelian)
  let f₀ : ↥X →* MulAut (Vtil V₀ V h.isElemAbelian) :=
    (actTil V₀ V h.isElemAbelian).comp (Subgroup.inclusion (hX.trans hMs0))
  let f₁ : ↥X →* MulAut (Vtil (v1Sub D.M V₀ V h.isElemAbelian L) V h.isElemAbelian) :=
    (actTil (v1Sub D.M V₀ V h.isElemAbelian L) V h.isElemAbelian).comp
      (Subgroup.inclusion (hX.trans hMs1))
  have hrange₀ : f₀.range = barSub V₀ V h.isElemAbelian X := by
    ext φ
    rw [MonoidHom.mem_range]
    constructor
    · rintro ⟨x, rfl⟩
      exact (mem_barSub V₀ V h.isElemAbelian X _).2
        ⟨Subgroup.inclusion (hX.trans hMs0) x, x.2, rfl⟩
    · intro hφ
      obtain ⟨g, hgX, hg⟩ := (mem_barSub V₀ V h.isElemAbelian X φ).1 hφ
      refine ⟨⟨(g : G), hgX⟩, ?_⟩
      change actTil V₀ V h.isElemAbelian
        (Subgroup.inclusion (hX.trans hMs0) ⟨(g : G), hgX⟩) = φ
      rw [show Subgroup.inclusion (hX.trans hMs0) (⟨(g : G), hgX⟩ : ↥X) = g from
        Subtype.ext rfl, hg]
  have hrange₁ : f₁.range = barSub (v1Sub D.M V₀ V h.isElemAbelian L) V h.isElemAbelian X := by
    ext φ
    rw [MonoidHom.mem_range]
    constructor
    · rintro ⟨x, rfl⟩
      exact (mem_barSub _ V h.isElemAbelian X _).2
        ⟨Subgroup.inclusion (hX.trans hMs1) x, x.2, rfl⟩
    · intro hφ
      obtain ⟨g, hgX, hg⟩ := (mem_barSub _ V h.isElemAbelian X φ).1 hφ
      refine ⟨⟨(g : G), hgX⟩, ?_⟩
      change actTil (v1Sub D.M V₀ V h.isElemAbelian L) V h.isElemAbelian
        (Subgroup.inclusion (hX.trans hMs1) ⟨(g : G), hgX⟩) = φ
      rw [show Subgroup.inclusion (hX.trans hMs1) (⟨(g : G), hgX⟩ : ↥X) = g from
        Subtype.ext rfl, hg]
  have hker₀ : f₀.ker = (F11.CTilde D.M V₀ V).subgroupOf X := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, mem_cTilde_iff h.isElemAbelian hM]
    constructor
    · intro hx
      refine ⟨hX x.2, (hX.trans hMs0) x.2, ?_⟩
      change actTil V₀ V h.isElemAbelian
        (Subgroup.inclusion (hX.trans hMs0) x) = 1
      rw [show Subgroup.inclusion (hX.trans hMs0) x =
        (⟨(x : G), (hX.trans hMs0) x.2⟩ : stabTil V₀ V) from Subtype.ext rfl]
      exact hx
    · rintro ⟨-, hst, h1⟩
      change actTil V₀ V h.isElemAbelian (Subgroup.inclusion (hX.trans hMs0) x) = 1
      rw [show Subgroup.inclusion (hX.trans hMs0) x =
        (⟨(x : G), hst⟩ : stabTil V₀ V) from Subtype.ext rfl]
      exact h1
  have hker₁ : f₁.ker = (F11.CTilde D.M (v1Sub D.M V₀ V h.isElemAbelian L) V).subgroupOf X := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf,
      mem_cTilde_iff h.isElemAbelian hM]
    constructor
    · intro hx
      refine ⟨hX x.2, (hX.trans hMs1) x.2, ?_⟩
      change actTil (v1Sub D.M V₀ V h.isElemAbelian L) V h.isElemAbelian
        (Subgroup.inclusion (hX.trans hMs1) x) = 1
      rw [show Subgroup.inclusion (hX.trans hMs1) x =
        (⟨(x : G), (hX.trans hMs1) x.2⟩ :
          stabTil (v1Sub D.M V₀ V h.isElemAbelian L) V) from Subtype.ext rfl]
      exact hx
    · rintro ⟨-, hst, h1⟩
      change actTil (v1Sub D.M V₀ V h.isElemAbelian L) V h.isElemAbelian
        (Subgroup.inclusion (hX.trans hMs1) x) = 1
      rw [show Subgroup.inclusion (hX.trans hMs1) x =
        (⟨(x : G), hst⟩ : stabTil (v1Sub D.M V₀ V h.isElemAbelian L) V) from Subtype.ext rfl]
      exact h1
  have hker_eq : f₀.ker = f₁.ker := by
    rw [hker₀, hker₁, fifteen_two_cent D h1217 h h.isElemAbelian]
  have e₀ : ↥X ⧸ f₀.ker ≃* ↥(barSub V₀ V h.isElemAbelian X) :=
    (QuotientGroup.quotientKerEquivRange f₀).trans (MulEquiv.subgroupCongr hrange₀)
  have e₁ : ↥X ⧸ f₁.ker ≃*
      ↥(barSub (v1Sub D.M V₀ V h.isElemAbelian L) V h.isElemAbelian X) :=
    (QuotientGroup.quotientKerEquivRange f₁).trans (MulEquiv.subgroupCongr hrange₁)
  exact ⟨e₀.symm.trans ((QuotientGroup.quotientMulEquivOfEq hker_eq).trans e₁)⟩

theorem s15_Three_stab_one (hT : RTable137) (hRk : RRank3List153)
    (h1217 : R1217 D) (h : Hyp151 D V₀ V L) (hV : IsElemAbelian 2 V)
    (hL : barSub V₀ V hV L ≠ ⊥) (hshape : s15Shape D V₀ V hV L K₀)
    (hperf : s15KNatPerf ↥(barSub V₀ V hV K₀) (barSub (v1Sub D.M V₀ V hV L) V hV K₀)
      (commSub ⊤ (barSub (v1Sub D.M V₀ V hV L) V hV K₀)))
    (hrs : s15Rs D V₀ V hV L K₀ = 1) (hnot : ¬ s15ExcList ↥(lBar V₀ V hV L))
    (z : vStar D.M V₀ V hV L) :
    ∃ E : Subgroup (MulAut (vStar D.M V₀ V hV L)), E ≤ s15XStar D V₀ V hV L K₀ ∧
      IsPGroup 3 E ∧ ¬ IsCyclic E ∧ ∀ e ∈ E, e z = z := by
  classical
  have hV2 : ∀ v : vStar D.M V₀ V hV L, v ^ 2 = 1 :=
    s15_Infra_vtil_sq_eq_one (v1Sub D.M V₀ V hV L) V hV
  have hperf' := s15_Three_perf_star h1217 h hV hshape hrs hperf
  have hs : s15 D.M V₀ V hV L = 1 := ((s15_Three_rs_eq_one_iff D V₀ V hV L K₀).1 hrs).2
  have hLK : lBar V₀ V hV L = barSub V₀ V hV K₀ := s15_Three_lBar_eq hshape hrs
  have hstar : lStar D.M V₀ V hV L = barSub (v1Sub D.M V₀ V hV L) V hV K₀ :=
    (s15_Three_barSub_star_iff D h1217 h h.le (hshape.1.trans h.le)).1 hLK
  have hW : wStar D.M V₀ V hV L = ⊤ := s15_Three_wStar_eq_top D h1217 h hV hL hs
  have hXK : barSub (v1Sub D.M V₀ V hV L) V hV K₀ ≤ s15XStar D V₀ V hV L K₀ := by
    rw [s15XStar]
    exact le_iSup₂_of_le (f := fun m (_ : m ∈ D.M) =>
      barSub (v1Sub D.M V₀ V hV L) V hV (conjSubgroup K₀ m)) 1 (Subgroup.one_mem _)
      (le_of_eq (by rw [conjSubgroup_one]))
  by_cases hz : z = 1
  ·
    have h2L : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup ↥(lBar V₀ V hV L)) := by
      by_contra hle
      rw [not_le] at hle
      have hlist := (hRk (vStar D.M V₀ V hV L) ↥(lBar V₀ V hV L)
        (lStar D.M V₀ V hV L) (wStar D.M V₀ V hV L) hperf').2 (by omega)
      exact hnot ((s15ExcList_iff _).2 (Or.inl hlist))
    have h2Kb : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup ↥(barSub V₀ V hV K₀)) := by
      rw [← hLK]; exact h2L
    obtain ⟨E', hE'le, hE'elem, hE'card⟩ :=
      CFSG.SectionRank.exists_isElemAbelian_card_of_le_pRank (p := 3)
        (H := (⊤ : Subgroup ↥(barSub V₀ V hV K₀))) (k := 2) h2Kb
    obtain ⟨e⟩ := s15_Three_star_equiv D h1217 h (hshape.1.trans h.le)
    let E : Subgroup (MulAut (vStar D.M V₀ V hV L)) :=
      (E'.map e.toMonoidHom).map (barSub (v1Sub D.M V₀ V hV L) V hV K₀).subtype
    have hEle : E ≤ s15XStar D V₀ V hV L K₀ :=
      (Subgroup.map_subtype_le _).trans hXK
    have hEelem : CFSG.Open.IsElemAbelian 3 E :=
      CFSG.SectionRank.isElemAbelian_map
        (CFSG.SectionRank.isElemAbelian_map hE'elem e.toMonoidHom)
        (barSub (v1Sub D.M V₀ V hV L) V hV K₀).subtype
    have hEcard : Nat.card E = 3 ^ 2 := by
      rw [Subgroup.card_map_of_injective Subtype.val_injective,
        Subgroup.card_map_of_injective e.injective, hE'card]
    refine ⟨E, hEle, ?_, ?_, ?_⟩
    · exact (s15_Three_pGroup_not_cyclic_of_card_nine hEelem.2 hEcard).1
    · exact (s15_Three_pGroup_not_cyclic_of_card_nine hEelem.2 hEcard).2
    · intro x _
      rw [hz]; exact map_one x
  ·
    have hzW : z ∈ wStar D.M V₀ V hV L := by rw [hW]; trivial
    have hnot' : ¬ (∃ w ∈ wStar D.M V₀ V hV L, w ≠ 1 ∧
        CFSG.Open.pRank 3 (lStar D.M V₀ V hV L ⊓
          MulAction.stabilizer (MulAut (vStar D.M V₀ V hV L)) w) ≤ 1) :=
      fun hex => hnot ((hT (vStar D.M V₀ V hV L) hV2 (lStar D.M V₀ V hV L)
        (wStar D.M V₀ V hV L) ↥(lBar V₀ V hV L) hperf').2 hex)
    have h2 : 2 ≤ CFSG.Open.pRank 3 (lStar D.M V₀ V hV L ⊓
        MulAction.stabilizer (MulAut (vStar D.M V₀ V hV L)) z) := by
      by_contra hle
      rw [not_le] at hle
      exact hnot' ⟨z, hzW, hz, by omega⟩
    obtain ⟨E, hEle, hEelem, hEcard⟩ :=
      CFSG.SectionRank.exists_isElemAbelian_card_of_le_pRank (p := 3)
        (H := lStar D.M V₀ V hV L ⊓
          MulAction.stabilizer (MulAut (vStar D.M V₀ V hV L)) z) (k := 2) h2
    have hEleX : E ≤ s15XStar D V₀ V hV L K₀ :=
      (hEle.trans inf_le_left).trans (hstar.le.trans hXK)
    refine ⟨E, hEleX, ?_, ?_, ?_⟩
    · exact (s15_Three_pGroup_not_cyclic_of_card_nine hEelem.2 hEcard).1
    · exact (s15_Three_pGroup_not_cyclic_of_card_nine hEelem.2 hEcard).2
    · intro x hx
      exact MulAction.mem_stabilizer_iff.1 (hEle hx).2

theorem s15_Three_stab_rank (hT : RTable137) (hRk : RRank3List153) (hAbs : RAbsIrr153)
    (h1217 : R1217 D) (h : Hyp151 D V₀ V L) (hV : IsElemAbelian 2 V)
    (hL : barSub V₀ V hV L ≠ ⊥) (hshape : s15Shape D V₀ V hV L K₀)
    (hperf : s15KNatPerf ↥(barSub V₀ V hV K₀) (barSub (v1Sub D.M V₀ V hV L) V hV K₀)
      (commSub ⊤ (barSub (v1Sub D.M V₀ V hV L) V hV K₀)))
    (hnot : ¬ (s15Rs D V₀ V hV L K₀ = 1 ∧ s15ExcList ↥(lBar V₀ V hV L)))
    (z : vStar D.M V₀ V hV L) :
    ∃ E : Subgroup (MulAut (vStar D.M V₀ V hV L)), E ≤ s15XStar D V₀ V hV L K₀ ∧
      IsPGroup 3 E ∧ ¬ IsCyclic E ∧ ∀ e ∈ E, e z = z := by
  by_cases hrs : s15Rs D V₀ V hV L K₀ = 1
  · exact s15_Three_stab_one hT hRk h1217 h hV hL hshape hperf hrs
      (fun hex => hnot ⟨hrs, hex⟩) z
  · obtain ⟨m₁, hm₁, m₂, hm₂, hne⟩ := s15_Three_two_components h1217 h hV hshape hrs
    exact s15_Three_stab_two hT hAbs h1217 h hV hshape hperf hm₁ hm₂ hne z

end Components

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
