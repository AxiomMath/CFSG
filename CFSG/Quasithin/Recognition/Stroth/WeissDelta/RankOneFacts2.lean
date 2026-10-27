module

public import CFSG.Quasithin.Recognition.Stroth.WeissDelta.RankOneFacts

public section

open scoped Pointwise

namespace CFSG.Quasithin.Stroth.WeissDelta

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.Stroth CFSG.Geometry.GeneralizedPolygons
  CFSG.GH74.GLS.SP CFSG.GH74.BNPair CFSG.QuasithinUnique
  CFSG.Quasithin.H13.F431.TwoF4 CFSG.Quasithin.H13.F431.Un
  CFSG.LieType.Ree.ReeTag CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits

private lemma sup_transitive_of_compl {X Ω : Type*} [Group X] [MulAction X Ω]
    {ω ω' : Ω} (hne : ω ≠ ω') (h3 : ∃ α : Ω, α ≠ ω ∧ α ≠ ω')
    {R R' : Subgroup X} (hR : R ≤ MulAction.stabilizer X ω)
    (hR' : R' ≤ MulAction.stabilizer X ω')
    (hRt : ∀ α β : Ω, α ≠ ω → β ≠ ω → ∃ r ∈ R, (r : X) • α = β)
    (hR't : ∀ α β : Ω, α ≠ ω' → β ≠ ω' → ∃ r ∈ R', (r : X) • α = β) :
    ∀ α β : Ω, ∃ m ∈ R ⊔ R', (m : X) • α = β := by
  intro α β
  by_cases hαβ : α = β
  · exact ⟨1, (R ⊔ R').one_mem, by rw [hαβ]; simp⟩
  by_cases hαω : α = ω
  · by_cases hβω' : β = ω'
    · obtain ⟨γ, hγω, hγω'⟩ := h3
      obtain ⟨r', hr'R', hr'⟩ := hR't ω γ hne hγω'
      obtain ⟨r, hrR, hr⟩ := hRt γ ω' hγω hne.symm
      refine ⟨r * r', (R ⊔ R').mul_mem (Subgroup.mem_sup_left hrR)
        (Subgroup.mem_sup_right hr'R'), ?_⟩
      rw [mul_smul, hαω, hr', hr, hβω']
    · obtain ⟨r', hr'R', hr'⟩ := hR't ω β hne hβω'
      exact ⟨r', Subgroup.mem_sup_right hr'R', by rw [hαω]; exact hr'⟩
  · by_cases hβω : β = ω
    · obtain ⟨γ, hγω, hγω'⟩ := h3
      obtain ⟨r, hrR, hr⟩ := hRt α γ hαω hγω
      obtain ⟨r', hr'R', hr'⟩ := hR't γ ω hγω' hne
      refine ⟨r' * r, (R ⊔ R').mul_mem (Subgroup.mem_sup_right hr'R')
        (Subgroup.mem_sup_left hrR), ?_⟩
      rw [mul_smul, hr, hr', hβω]
    · obtain ⟨r, hrR, hr⟩ := hRt α β hαω hβω
      exact ⟨r, Subgroup.mem_sup_left hrR, hr⟩

namespace RankOneLocal

theorem le_socle {X Ω : Type*} [Group X] [Finite X] [MulAction X Ω]
    {N : Subgroup X} (hN : N.Normal) (h : RankOneLocal X Ω N) {ω : Ω} (hω : ∃ ω' : Ω, ω' ≠ ω)
    {R : Subgroup X} (hR : R ≤ MulAction.stabilizer X ω)
    (hRn : (R.subgroupOf (MulAction.stabilizer X ω)).Normal) (hR2 : IsPGroup 2 R)
    (hreg : ∀ α β : Ω, α ≠ ω → β ≠ ω → ∃! r : R, (r : X) • α = β) : R ≤ N := by
  classical
  obtain ⟨ω', hω'⟩ := hω
  let Gω : Subgroup X := MulAction.stabilizer X ω
  let Gω' : Subgroup X := MulAction.stabilizer X ω'
  let T : Subgroup X := N ⊓ Gω ⊓ Gω'
  let R₀ : Subgroup X := R ⊓ N
  let H : Subgroup X := R₀ ⊔ T
  have hR₀_le : R₀ ≤ R := inf_le_left
  have hR₀_H : R₀ ≤ H := le_sup_left
  have hT_H : T ≤ H := le_sup_right
  have hR₀2 : IsPGroup 2 R₀ := hR2.to_le hR₀_le
  have hTnormR₀ : T ≤ Subgroup.normalizer R₀ := by
    rw [Subgroup.le_normalizer_iff]
    intro t ht m hm
    exact ⟨(Subgroup.normal_subgroupOf_iff hR).mp hRn m t hm.1 ht.1.2,
      N.mul_mem (N.mul_mem ht.1.1 hm.2) (N.inv_mem ht.1.1)⟩
  have hR₀normalH : (R₀.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hR₀_H).mpr
      (sup_le Subgroup.le_normalizer hTnormR₀)
  have hcop : Nat.Coprime (Nat.card R₀) (Nat.card T) := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨k, hk⟩ := hR₀2.exists_card_eq
    rw [hk]
    exact (Nat.coprime_two_left.mpr
      (by simpa [T, Gω, Gω'] using h.torus_odd ω ω' hω'.symm)).pow_left k
  have hdisj : Disjoint R₀ T := Subgroup.disjoint_of_coprime_natCard hcop
  have hsup : (R₀.subgroupOf H) ⊔ (T.subgroupOf H) = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hR₀_H hT_H]
    change (R₀ ⊔ T).subgroupOf (R₀ ⊔ T) = ⊤
    rw [Subgroup.subgroupOf_self]
  have hdisjH : Disjoint (R₀.subgroupOf H) (T.subgroupOf H) := by
    rw [disjoint_iff]
    ext x
    constructor
    · rintro ⟨hxR, hxT⟩
      have hx : (x : X) ∈ R₀ ⊓ T := ⟨hxR, hxT⟩
      rw [disjoint_iff.mp hdisj] at hx
      rw [Subgroup.mem_bot]
      exact Subtype.ext (Subgroup.mem_bot.mp hx)
    · intro hx
      rw [Subgroup.mem_bot] at hx
      subst hx
      exact ⟨(R₀.subgroupOf H).one_mem, (T.subgroupOf H).one_mem⟩
  have hmul : (R₀.subgroupOf H : Set H) * (T.subgroupOf H : Set H) = Set.univ := by
    haveI : (R₀.subgroupOf H).Normal := hR₀normalH
    rw [← Subgroup.normal_mul (R₀.subgroupOf H) (T.subgroupOf H), hsup]
    rfl
  have hcompRT : (R₀.subgroupOf H).IsComplement' (T.subgroupOf H) :=
    Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdisjH hmul
  by_contra hRle
  obtain ⟨r₀, hr₀R, hr₀N⟩ := Set.not_subset.mp hRle
  have hr₀ne1 : r₀ ≠ 1 := by
    intro h1
    exact hr₀N (h1 ▸ N.one_mem)
  let α : Ω := (r₀ : X) • ω'
  have hαω : α ≠ ω := by
    intro h1
    have hr₀ω : (r₀ : X) • ω = ω := hR hr₀R
    have h2 : ω' = ω := by
      calc ω' = (r₀ : X)⁻¹ • ((r₀ : X) • ω') := (inv_smul_smul (r₀ : X) ω').symm
        _ = (r₀ : X)⁻¹ • ω := by
          rw [show ((r₀ : X) • ω') = ω from h1]
        _ = ω := by
          conv_lhs => rw [← hr₀ω]
          exact inv_smul_smul (r₀ : X) ω
    exact hω' h2
  have hαω' : α ≠ ω' := by
    intro h1
    have h2 : (⟨(r₀ : X), hr₀R⟩ : R) = 1 := by
      apply (hreg ω' ω' hω' hω').unique
      · show ((⟨(r₀ : X), hr₀R⟩ : R) : X) • ω' = ω'
        simpa using h1
      · simp
    exact hr₀ne1 (congrArg Subtype.val h2)
  have hO_avoid_ω : ∀ c : R₀, (c : X) • α ≠ ω := by
    intro c h1
    have hcR : (c : X) ∈ R := hR₀_le c.2
    have hcr : ((c : X) * (r₀ : X)) ∈ R := R.mul_mem hcR hr₀R
    have h2 : ((c : X) * (r₀ : X)) • ω' = ω := by
      rw [mul_smul]
      exact h1
    have h3 : ω' = ω := by
      calc ω' = ((c : X) * (r₀ : X))⁻¹ • (((c : X) * (r₀ : X)) • ω') :=
            (inv_smul_smul _ ω').symm
        _ = ((c : X) * (r₀ : X))⁻¹ • ω := by rw [h2]
        _ = ω := by
          conv_lhs => rw [← hR hcr]
          exact inv_smul_smul _ ω
    exact hω' h3
  have hO_avoid_ω' : ∀ c : R₀, (c : X) • α ≠ ω' := by
    intro c h1
    have hcR : (c : X) ∈ R := hR₀_le c.2
    have hcr : ((c : X) * (r₀ : X)) ∈ R := R.mul_mem hcR hr₀R
    have h2 : ((c : X) * (r₀ : X)) • ω' = ω' := by
      rw [mul_smul]
      exact h1
    have h3 : (⟨(c : X) * (r₀ : X), hcr⟩ : R) = 1 :=
      (hreg ω' ω' hω' hω').unique (by simpa using h2) (by simp)
    have h4 : (c : X) * (r₀ : X) = 1 := congrArg Subtype.val h3
    have h5 : (r₀ : X) = (c : X)⁻¹ := by
      calc (r₀ : X) = (c : X)⁻¹ * ((c : X) * (r₀ : X)) := by group
        _ = (c : X)⁻¹ * 1 := by rw [h4]
        _ = (c : X)⁻¹ := mul_one _
    have h6 : (r₀ : X) ∈ N := by
      rw [h5]
      exact N.inv_mem c.2.2
    exact hr₀N h6
  have hTpres : ∀ t : T.subgroupOf H, ∃ c : R₀, (c : X) • α = ((t : H) : X) • α := by
    intro t
    have htT : ((t : H) : X) ∈ T := t.2
    have htGω : ((t : H) : X) ∈ Gω := htT.1.2
    have htGω' : ((t : H) : X) ∈ Gω' := htT.2
    let u : X := ((t : H) : X) * (r₀ : X) * ((t : H) : X)⁻¹
    have huR : u ∈ R :=
      (Subgroup.normal_subgroupOf_iff hR).mp hRn (r₀ : X) ((t : H) : X) hr₀R htGω
    have huN : u * (r₀ : X)⁻¹ ∈ N := by
      have h1 : u * (r₀ : X)⁻¹ =
          ((t : H) : X) * ((r₀ : X) * ((t : H) : X)⁻¹ * (r₀ : X)⁻¹) := by
        simp [u]
        group
      rw [h1]
      exact N.mul_mem htT.1.1
        (hN.conj_mem ((t : H) : X)⁻¹ (N.inv_mem htT.1.1) (r₀ : X))
    have hcR₀ : u * (r₀ : X)⁻¹ ∈ R₀ :=
      ⟨R.mul_mem huR (R.inv_mem hr₀R), huN⟩
    refine ⟨⟨u * (r₀ : X)⁻¹, hcR₀⟩, ?_⟩
    have htfix : ((t : H) : X) • ω' = ω' := MulAction.mem_stabilizer_iff.mp htGω'
    have htinvfix : ((t : H) : X)⁻¹ • ω' = ω' := by
      have h1 : ((t : H) : X)⁻¹ • (((t : H) : X) • ω') = ω' := inv_smul_smul _ _
      rwa [htfix] at h1
    have htα : ((t : H) : X) • α = u • ω' := by
      calc ((t : H) : X) • ((r₀ : X) • ω')
          = (((t : H) : X) * (r₀ : X)) • ω' := (mul_smul _ _ _).symm
        _ = (((t : H) : X) * (r₀ : X)) • (((t : H) : X)⁻¹ • ω') := by rw [htinvfix]
        _ = (((t : H) : X) * (r₀ : X) * ((t : H) : X)⁻¹) • ω' :=
            (mul_smul _ _ _).symm
        _ = u • ω' := rfl
    have hcα : ((⟨u * (r₀ : X)⁻¹, hcR₀⟩ : R₀) : X) • α = u • ω' := by
      calc ((⟨u * (r₀ : X)⁻¹, hcR₀⟩ : R₀) : X) • α
          = (u * (r₀ : X)⁻¹) • ((r₀ : X) • ω') := rfl
        _ = ((u * (r₀ : X)⁻¹) * (r₀ : X)) • ω' := (mul_smul _ _ _).symm
        _ = u • ω' := by
            congr 1
            group
    exact hcα.trans htα.symm
  have hfreeX : ∀ r : R₀, (r : X) • α = α → r = 1 := by
    intro r hr
    have hrR : (r : X) ∈ R := hR₀_le r.2
    have h1 : (⟨(r : X), hrR⟩ : R) = 1 :=
      (hreg α α hαω hαω).unique (by simpa using hr) (by simp)
    have h3 : (r : X) = 1 := congrArg Subtype.val h1
    exact Subtype.ext h3
  have hfree : ∀ r : R₀.subgroupOf H, r • α = α → r = 1 := by
    intro r hr
    have hrX : (r : X) • α = α := hr
    have hrR₀ : (r : X) ∈ R₀ := Subgroup.mem_subgroupOf.mp r.2
    have h2 : (⟨(r : X), hrR₀⟩ : R₀) = 1 :=
      hfreeX ⟨(r : X), hrR₀⟩ hrX
    have h3 : (r : X) = 1 := congrArg Subtype.val h2
    apply Subtype.ext
    apply Subtype.ext
    exact h3
  have hmove : ∀ g : H, ∃ r : R₀.subgroupOf H, ((r : X) * (g : X)) • α = α := by
    intro g
    have hgmem : (g : H) ∈ (R₀.subgroupOf H : Set H) * (T.subgroupOf H : Set H) := by
      haveI : (R₀.subgroupOf H).Normal := hR₀normalH
      rw [← Subgroup.normal_mul (R₀.subgroupOf H) (T.subgroupOf H), hsup]
      exact Subgroup.mem_top g
    obtain ⟨c, hc, t, ht, hct⟩ := Set.mem_mul.mp hgmem
    let cR : R₀.subgroupOf H := ⟨c, hc⟩
    obtain ⟨cX, hcX_eq⟩ := hTpres ⟨t, ht⟩
    let cXH : R₀.subgroupOf H :=
      ⟨⟨cX, hR₀_H cX.2⟩, by
        rw [Subgroup.mem_subgroupOf]
        exact cX.2⟩
    refine ⟨(cR * cXH)⁻¹, ?_⟩
    have hcXH_eq : (cXH : X) • α = (t : X) • α := hcX_eq
    have hgα : (g : X) • α = ((cR * cXH : R₀.subgroupOf H) : X) • α := by
      rw [← hct]
      change ((c : X) * (t : X)) • α = ((cR : X) * (cXH : X)) • α
      calc ((c : X) * (t : X)) • α = (c : X) • ((t : X) • α) := mul_smul _ _ _
        _ = (c : X) • ((cXH : X) • α) := by rw [hcXH_eq]
        _ = ((cR : X) * (cXH : X)) • α := (mul_smul _ _ _).symm
    calc ((((cR * cXH)⁻¹ : R₀.subgroupOf H) : X) * (g : X)) • α
        = (((cR * cXH)⁻¹ : R₀.subgroupOf H) : X) • ((g : X) • α) := mul_smul _ _ _
      _ = (((cR * cXH)⁻¹ : R₀.subgroupOf H) : X) •
            (((cR * cXH : R₀.subgroupOf H) : X) • α) := by rw [hgα]
      _ = ((((cR * cXH)⁻¹ : R₀.subgroupOf H) : X) *
            ((cR * cXH : R₀.subgroupOf H) : X)) • α := (mul_smul _ _ _).symm
      _ = α := by
          have h1 : (((cR * cXH)⁻¹ : R₀.subgroupOf H) : X) *
              ((cR * cXH : R₀.subgroupOf H) : X) = 1 := by
            simpa [Subgroup.coe_inv] using
              inv_mul_cancel ((cR * cXH : R₀.subgroupOf H) : X)
          rw [h1, one_smul]
  have hcompRL : (R₀.subgroupOf H).IsComplement' (MulAction.stabilizer H α) :=
    Subgroup.isComplement'_stabilizer α hfree (fun g => by
      obtain ⟨r, hr⟩ := hmove g
      exact ⟨r, by
        simpa [Subgroup.smul_def, Subgroup.coe_mul, mul_smul] using hr⟩)
  have hcopIdx : Nat.Coprime (Nat.card (R₀.subgroupOf H)) (R₀.subgroupOf H).index := by
    have hcardR₀ : Nat.card (R₀.subgroupOf H) = Nat.card R₀ :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hR₀_H).toEquiv
    have hcardT : Nat.card (T.subgroupOf H) = Nat.card T :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hT_H).toEquiv
    rw [hcompRT.symm.index_eq_card, hcardR₀, hcardT]
    exact hcop
  obtain ⟨n, hn⟩ := CFSG.GorensteinWalter.SchurZassenhaus.exists_mem_normal_conjugator_of_coprime
    (R₀.subgroupOf H) (T.subgroupOf H) (MulAction.stabilizer H α)
    hR₀normalH hcompRT hcompRL hcopIdx
  let ω'' : Ω := (n : H)⁻¹ • α
  have htfix : ∀ t : T.subgroupOf H,
      ((n : H) * (t : H) * (n : H)⁻¹) ∈
        MulAction.stabilizer H α := by
    intro t
    rw [hn]
    exact Subgroup.mem_map_of_mem (MulAut.conj (n : H)).toMonoidHom t.2
  have hfixT : ∀ t ∈ T, (t : X) • ω'' = ω'' := by
    intro t ht
    let t' : T.subgroupOf H := ⟨⟨t, hT_H ht⟩, ht⟩
    have h1 : ((n : H) * (t' : H) *
        (n : H)⁻¹) ∈ MulAction.stabilizer H α := htfix t'
    have h2 : ((n : H) * (t' : H) *
        (n : H)⁻¹) • α = α :=
      MulAction.mem_stabilizer_iff.mp h1
    have hnω'' : (n : H) • ω'' = α := by
      rw [show ω'' = (n : H)⁻¹ • α from rfl, ← mul_smul, mul_inv_cancel, one_smul]
    have h3 : (n : H) • ((t' : H) • ω'') = (n : H) • ω'' := by
      have hcoef : ((n : H) * (t' : H) * (n : H)⁻¹) * (n : H) = (n : H) * (t' : H) := by
        group
      calc (n : H) • ((t' : H) • ω'')
          = ((n : H) * (t' : H)) • ω'' := (mul_smul _ _ _).symm
        _ = ((n : H) * (t' : H) * (n : H)⁻¹) • ((n : H) • ω'') := by
            conv_rhs => rw [← mul_smul, hcoef]
        _ = ((n : H) * (t' : H) * (n : H)⁻¹) • α := by rw [hnω'']
        _ = α := h2
        _ = (n : H) • ω'' := hnω''.symm
    have h4 := congrArg (fun x => (n : H)⁻¹ • x) h3
    have h5 : (t' : H) • ω'' = ω'' := by
      simpa [smul_smul] using h4
    simpa [t'] using h5
  have hω''mem : ∃ c : R₀, (c : X) • α = ω'' := by
    refine ⟨⟨(n : X)⁻¹, R₀.inv_mem (Subgroup.mem_subgroupOf.mp n.2)⟩, rfl⟩
  rcases h.torus_fix ω ω' ω'' hω'.symm (fun t ht => hfixT t ht) with h | h
  · obtain ⟨c, hc⟩ := hω''mem
    exact hO_avoid_ω c (hc.trans h)
  · obtain ⟨c, hc⟩ := hω''mem
    exact hO_avoid_ω' c (hc.trans h)

theorem le_sup_root {X Ω : Type*} [Group X] [Finite X] [MulAction X Ω]
    {N : Subgroup X} (hN : N.Normal) (hNs : IsSimpleGroup ↥N)
    (h : RankOneLocal X Ω N) (hA7 : RankOneRoot X Ω N) {ω ω' : Ω} (hne : ω ≠ ω')
    (h3 : ∃ α : Ω, α ≠ ω ∧ α ≠ ω') {R R' : Subgroup X} (hR : R ≤ MulAction.stabilizer X ω)
    (hR' : R' ≤ MulAction.stabilizer X ω') (hR2 : IsPGroup 2 R) (hR'2 : IsPGroup 2 R')
    (hRt : ∀ α β : Ω, α ≠ ω → β ≠ ω → ∃ r ∈ R, r • α = β)
    (hR't : ∀ α β : Ω, α ≠ ω' → β ≠ ω' → ∃ r ∈ R', r • α = β)
    (hRn : ∀ t ∈ N ⊓ MulAction.stabilizer X ω ⊓ MulAction.stabilizer X ω', ∀ x ∈ R,
      t * x * t⁻¹ ∈ R)
    (hR'n : ∀ t ∈ N ⊓ MulAction.stabilizer X ω ⊓ MulAction.stabilizer X ω', ∀ x ∈ R',
      t * x * t⁻¹ ∈ R') :
    N ≤ R ⊔ R' := by
  classical
  obtain ⟨Rω, hRω, hRωn, hRω2, hRωreg⟩ := h.root ω
  obtain ⟨Rω', hRω', hRω'n, hRω'2, hRω'reg⟩ := h.root ω'
  have hRleRω : R ≤ Rω :=
    hA7.le_root ω ω' hne R Rω hR hRω hRωn hR2 hRω2 hRωreg hRn
  have hR'n' : ∀ t ∈ N ⊓ MulAction.stabilizer X ω' ⊓ MulAction.stabilizer X ω,
      ∀ x ∈ R', t * x * t⁻¹ ∈ R' := by
    intro t ht x hx
    exact hR'n t (by simpa [inf_assoc, inf_comm, inf_left_comm] using ht) x hx
  have hR'leRω' : R' ≤ Rω' :=
    hA7.le_root ω' ω hne.symm R' Rω' hR' hRω' hRω'n hR'2 hRω'2 hRω'reg hR'n'
  have hReq : R = Rω := by
    apply le_antisymm hRleRω
    intro r hr
    have hr_ne : (r : X) • ω' ≠ ω := by
      intro h1
      have hrω : (r : X) • ω = ω := hRω hr
      have h2 : ω' = ω := by
        calc ω' = (r : X)⁻¹ • ((r : X) • ω') := (inv_smul_smul (r : X) ω').symm
          _ = (r : X)⁻¹ • ω := by rw [h1]
          _ = ω := by
            conv_lhs => rw [← hrω]
            exact inv_smul_smul (r : X) ω
      exact hne h2.symm
    obtain ⟨q, hqR, hq⟩ := hRt ω' ((r : X) • ω') hne.symm hr_ne
    have h1 : (⟨(q : X), hRleRω hqR⟩ : Rω) = ⟨(r : X), hr⟩ :=
      (hRωreg ω' ((r : X) • ω') hne.symm hr_ne).unique (by simpa using hq) rfl
    have h2 : (r : X) = (q : X) := congrArg Subtype.val h1.symm
    rw [h2]
    exact hqR
  have hR'eq : R' = Rω' := by
    apply le_antisymm hR'leRω'
    intro r hr
    have hr_ne : (r : X) • ω ≠ ω' := by
      intro h1
      have hrω' : (r : X) • ω' = ω' := hRω' hr
      have h2 : ω = ω' := by
        calc ω = (r : X)⁻¹ • ((r : X) • ω) := (inv_smul_smul (r : X) ω).symm
          _ = (r : X)⁻¹ • ω' := by rw [h1]
          _ = ω' := by
            conv_lhs => rw [← hrω']
            exact inv_smul_smul (r : X) ω'
      exact hne h2
    obtain ⟨q, hqR, hq⟩ := hR't ω ((r : X) • ω) hne hr_ne
    have h1 : (⟨(q : X), hR'leRω' hqR⟩ : Rω') = ⟨(r : X), hr⟩ :=
      (hRω'reg ω ((r : X) • ω) hne hr_ne).unique (by simpa using hq) rfl
    have h2 : (r : X) = (q : X) := congrArg Subtype.val h1.symm
    rw [h2]
    exact hqR
  have hRleN : R ≤ N := by
    rw [hReq]
    exact le_socle hN h ⟨ω', hne.symm⟩ hRω hRωn hRω2 hRωreg
  have hR'leN : R' ≤ N := by
    rw [hR'eq]
    exact le_socle hN h ⟨ω, hne⟩ hRω' hRω'n hRω'2 hRω'reg
  let M : Subgroup X := R ⊔ R'
  let Gω : Subgroup X := MulAction.stabilizer X ω
  let Gω' : Subgroup X := MulAction.stabilizer X ω'
  let T : Subgroup X := N ⊓ Gω ⊓ Gω'
  let Nω : Subgroup X := N ⊓ Gω
  have hMleN : M ≤ N := sup_le hRleN hR'leN
  have hMtrans : ∀ α β : Ω, ∃ m ∈ M, (m : X) • α = β :=
    sup_transitive_of_compl hne h3 hR hR' hRt hR't
  have hNω_eq : Nω = R ⊔ T := by
    apply le_antisymm
    · intro g hg
      have hgGω : g ∈ Gω := hg.2
      have hgω' : g • ω' ≠ ω := by
        intro h1
        have h2 : ω' = ω := by
          calc ω' = g⁻¹ • (g • ω') := (inv_smul_smul g ω').symm
            _ = g⁻¹ • ω := by rw [h1]
            _ = ω := by
              conv_lhs => rw [← hgGω]
              exact inv_smul_smul g ω
        exact hne h2.symm
      obtain ⟨r, hrR, hr⟩ := hRt ω' (g • ω') hne.symm hgω'
      have hmem : r⁻¹ * g ∈ T := by
        refine ⟨⟨?_, ?_⟩, ?_⟩
        · exact N.mul_mem (N.inv_mem (hRleN hrR)) hg.1
        · exact Gω.mul_mem (Gω.inv_mem (hR hrR)) hgGω
        · change (r⁻¹ * g) • ω' = ω'
          rw [mul_smul, ← hr, inv_smul_smul]
      have hg_eq : g = r * (r⁻¹ * g) := by group
      rw [hg_eq]
      exact (R ⊔ T).mul_mem (Subgroup.mem_sup_left hrR) (Subgroup.mem_sup_right hmem)
    · refine sup_le (le_inf hRleN hR) ?_
      exact le_inf (le_trans inf_le_left inf_le_left) (le_trans inf_le_left inf_le_right)
  have hN_eq : N = M ⊔ T := by
    apply le_antisymm
    · intro n hn
      obtain ⟨m, hmM, hm⟩ := hMtrans ω (n • ω)
      have hmem : m⁻¹ * n ∈ Nω := by
        refine ⟨N.mul_mem (N.inv_mem (hMleN hmM)) hn, ?_⟩
        change (m⁻¹ * n) • ω = ω
        rw [mul_smul, ← hm, inv_smul_smul]
      have hmem2 : m⁻¹ * n ∈ R ⊔ T := hNω_eq ▸ hmem
      have hn_eq : n = m * (m⁻¹ * n) := by group
      rw [hn_eq]
      have hle : R ⊔ T ≤ M ⊔ T :=
        sup_le (le_trans le_sup_left le_sup_left) le_sup_right
      exact (M ⊔ T).mul_mem (Subgroup.mem_sup_left hmM) (hle hmem2)
    · exact sup_le hMleN (le_trans inf_le_left inf_le_left)
  have hTnormR : T ≤ Subgroup.normalizer R := Subgroup.le_normalizer_iff.mpr hRn
  have hTnormR' : T ≤ Subgroup.normalizer R' := Subgroup.le_normalizer_iff.mpr hR'n
  have hTnormM : T ≤ Subgroup.normalizer M :=
    le_trans (le_inf hTnormR hTnormR')
      (Subgroup.inf_normalizer_le_normalizer_sup R R')
  have hNnormM : N ≤ Subgroup.normalizer M := by
    rw [hN_eq]
    exact sup_le Subgroup.le_normalizer hTnormM
  have hMnormal : (M.subgroupOf N).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hMleN).mpr hNnormM
  obtain ⟨γ, hγω, hγω'⟩ := h3
  have hRne : R ≠ ⊥ := by
    intro hbot
    obtain ⟨r, hrR, hr⟩ := hRt γ ω' hγω hne.symm
    have hr1 : r = 1 := by
      rw [hbot] at hrR
      rwa [Subgroup.mem_bot] at hrR
    rw [hr1, one_smul] at hr
    exact hγω' hr
  have hMne : M ≠ ⊥ := by
    intro hMbot
    apply hRne
    rw [eq_bot_iff]
    intro r hr
    have h1 : r ∈ M := Subgroup.mem_sup_left hr
    rw [hMbot] at h1
    rwa [Subgroup.mem_bot] at h1
  have hMsubne : (M.subgroupOf N) ≠ ⊥ := by
    intro hbot
    apply hMne
    rw [eq_bot_iff]
    intro m hm
    have h1 : (⟨m, hMleN hm⟩ : ↥N) ∈ M.subgroupOf N := hm
    rw [hbot] at h1
    rw [Subgroup.mem_bot] at h1
    exact Subtype.ext_iff.mp h1
  haveI : IsSimpleGroup ↥N := hNs
  haveI : (M.subgroupOf N).Normal := hMnormal
  rcases Subgroup.Normal.eq_bot_or_eq_top (M.subgroupOf N) with hbot | htop
  · exact absurd hbot hMsubne
  · exact Subgroup.subgroupOf_eq_top.mp htop

theorem rankOneCenter_of_zassenhaus {X Ω : Type*} [Group X] [Finite X]
    [MulAction X Ω] [FaithfulSMul X Ω] {N : Subgroup X} (hN : N.Normal)
    (h : RankOneLocal X Ω N) (hZ : RankOneZassenhaus X Ω N)
    (hcard : ∀ ω ω' : Ω, ω ≠ ω' → ∀ R : Subgroup X, R ≤ MulAction.stabilizer X ω →
      (R.subgroupOf (MulAction.stabilizer X ω)).Normal → IsPGroup 2 R →
      (∀ α β : Ω, α ≠ ω → β ≠ ω → ∃! r : R, (r : X) • α = β) →
      Nat.card ↥(R ⊓ Subgroup.centralizer (R : Set X)) =
        Nat.card ↥(N ⊓ MulAction.stabilizer X ω ⊓ MulAction.stabilizer X ω') + 1) :
    RankOneCenter X Ω N 1 := by
  classical
  have hA7 : RankOneRoot X Ω N := h.rankOneRoot_of_zassenhaus hZ
  refine ⟨?centralizer_le, ?center_le, ?centralizer_center⟩
  · intro ω R hR hRn hR2 hreg g hg hgcomm
    exact hA7.centralizer_le ω R hR hRn hR2 hreg g hg hgcomm
  · intro ω ω' hne R Z hR hRn hR2 hreg hZleR hZcent hZn hZne y hyR hycent
    let Gω : Subgroup X := MulAction.stabilizer X ω
    let Gω' : Subgroup X := MulAction.stabilizer X ω'
    let T : Subgroup X := N ⊓ Gω ⊓ Gω'
    let ZR : Subgroup X := R ⊓ Subgroup.centralizer (R : Set X)
    have hcardZR : Nat.card ↥ZR = Nat.card ↥T + 1 := by
      have h1 := hcard ω ω' hne R hR hRn hR2 hreg
      simpa [ZR, T, Gω, Gω'] using h1
    obtain ⟨z₁, hz₁ne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hZne
    have hz₁Z : (z₁ : X) ∈ Z := z₁.2
    have hz₁R : (z₁ : X) ∈ R := hZleR hz₁Z
    have hz₁ZR : (z₁ : X) ∈ ZR := by
      refine ⟨hz₁R, ?_⟩
      change (z₁ : X) ∈ Subgroup.centralizer (R : Set X)
      rw [Subgroup.mem_centralizer_iff]
      intro r hr
      exact hZcent r hr (z₁ : X) hz₁Z
    have hz₁neX : (z₁ : X) ≠ 1 := fun h1 => hz₁ne (Subtype.ext h1)
    have hTnormZR : T ≤ Subgroup.normalizer ZR := by
      rw [Subgroup.le_normalizer_iff]
      intro t ht z hz
      refine ⟨(Subgroup.normal_subgroupOf_iff hR).mp hRn z t hz.1 ht.1.2, ?_⟩
      have hzcentX : (z : X) ∈ Subgroup.centralizer (R : Set X) := hz.2
      change (t * z * t⁻¹) ∈ Subgroup.centralizer (R : Set X)
      rw [Subgroup.mem_centralizer_iff] at hzcentX ⊢
      intro r hr
      have htr : t⁻¹ * r * t ∈ R := by
        simpa using
          (Subgroup.normal_subgroupOf_iff hR).mp hRn r t⁻¹ hr (Gω.inv_mem ht.1.2)
      have hcomm := hzcentX (t⁻¹ * r * t) htr
      calc r * (t * z * t⁻¹) = t * ((t⁻¹ * r * t) * z) * t⁻¹ := by group
        _ = t * (z * (t⁻¹ * r * t)) * t⁻¹ := by rw [hcomm]
        _ = (t * z * t⁻¹) * r := by group
    have hz₁ω'_ne_ω : (z₁ : X) • ω' ≠ ω := by
      intro h1
      have hz₁ω : (z₁ : X) • ω = ω := hR hz₁R
      have h2 : ω' = ω := by
        calc ω' = (z₁ : X)⁻¹ • ((z₁ : X) • ω') := (inv_smul_smul (z₁ : X) ω').symm
          _ = (z₁ : X)⁻¹ • ω := by rw [h1]
          _ = ω := by
            conv_lhs => rw [← hz₁ω]
            exact inv_smul_smul (z₁ : X) ω
      exact hne h2.symm
    have hz₁ω'_ne_ω' : (z₁ : X) • ω' ≠ ω' := by
      intro h1
      have h2 : (⟨(z₁ : X), hz₁R⟩ : R) = 1 := by
        apply (hreg ω' ω' hne.symm hne.symm).unique
        · show ((⟨(z₁ : X), hz₁R⟩ : R) : X) • ω' = ω'
          simpa using h1
        · simp
      exact hz₁neX (congrArg Subtype.val h2)
    have hconj_mem : ∀ t : T, (t : X) * (z₁ : X) * (t : X)⁻¹ ∈ ZR := by
      intro t
      exact (Subgroup.le_normalizer_iff.mp hTnormZR) t t.2 z₁ hz₁ZR
    have hconj_ne : ∀ t : T, (t : X) * (z₁ : X) * (t : X)⁻¹ ≠ 1 := by
      intro t h1
      apply hz₁neX
      calc (z₁ : X) = (t : X)⁻¹ * ((t : X) * (z₁ : X) * (t : X)⁻¹) * (t : X) := by
            group
        _ = 1 := by rw [h1]; group
    let F : T → {z : ZR // z ≠ 1} := fun t =>
      ⟨⟨(t : X) * (z₁ : X) * (t : X)⁻¹, hconj_mem t⟩, by
        intro h1
        exact hconj_ne t (congrArg Subtype.val h1)⟩
    have hSubCard : Nat.card {z : ZR // z ≠ 1} = Nat.card T := by
      haveI : Fintype ZR := Fintype.ofFinite ZR
      have h1 : Nat.card {z : ZR // z ≠ 1} = Nat.card ZR - 1 := by
        rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
          Fintype.card_subtype_compl (fun z : ZR => z = 1)]
        simp
      omega
    have hFinj : Function.Injective F := by
      intro t₁ t₂ h
      have hconj : (t₁ : X) * (z₁ : X) * (t₁ : X)⁻¹ =
          (t₂ : X) * (z₁ : X) * (t₂ : X)⁻¹ :=
        congrArg (fun z : {z : ZR // z ≠ 1} => ((z : ZR) : X)) h
      by_contra hneq
      have hu_ne : (t₂⁻¹ * t₁ : T) ≠ 1 := by
        intro hu
        apply hneq
        calc t₁ = t₂ * (t₂⁻¹ * t₁) := by group
          _ = t₂ * 1 := by rw [hu]
          _ = t₂ := mul_one t₂
      have hu_neX : ((t₂⁻¹ * t₁ : T) : X) ≠ 1 := fun h1 => hu_ne (Subtype.ext h1)
      have hcomm : ((t₂⁻¹ * t₁ : T) : X) * (z₁ : X) =
          (z₁ : X) * ((t₂⁻¹ * t₁ : T) : X) := by
        have hcommX : (t₂ : X)⁻¹ * (t₁ : X) * (z₁ : X) =
            (z₁ : X) * ((t₂ : X)⁻¹ * (t₁ : X)) := by
          have h1 : (t₂ : X)⁻¹ * (t₁ : X) * (z₁ : X) *
              ((t₂ : X)⁻¹ * (t₁ : X))⁻¹ = (z₁ : X) := by
            calc (t₂ : X)⁻¹ * (t₁ : X) * (z₁ : X) *
                ((t₂ : X)⁻¹ * (t₁ : X))⁻¹
                = (t₂ : X)⁻¹ * ((t₁ : X) * (z₁ : X) * (t₁ : X)⁻¹) * (t₂ : X) := by
                  group
              _ = (t₂ : X)⁻¹ * ((t₂ : X) * (z₁ : X) * (t₂ : X)⁻¹) * (t₂ : X) := by
                  rw [hconj]
              _ = (z₁ : X) := by group
          calc (t₂ : X)⁻¹ * (t₁ : X) * (z₁ : X)
              = ((t₂ : X)⁻¹ * (t₁ : X) * (z₁ : X) *
                  ((t₂ : X)⁻¹ * (t₁ : X))⁻¹) * ((t₂ : X)⁻¹ * (t₁ : X)) := by group
            _ = (z₁ : X) * ((t₂ : X)⁻¹ * (t₁ : X)) := by rw [h1]
        simpa [Subgroup.coe_mul, Subgroup.coe_inv] using hcommX
      have hfix : ((t₂⁻¹ * t₁ : T) : X) • ((z₁ : X) • ω') = (z₁ : X) • ω' := by
        rw [← mul_smul, hcomm, mul_smul]
        congr 1
        exact MulAction.mem_stabilizer_iff.mp (t₂⁻¹ * t₁ : T).2.2
      rcases hZ.fix_two ω ω' hne ((t₂⁻¹ * t₁ : T) : X) (t₂⁻¹ * t₁ : T).2 hu_neX
        ((z₁ : X) • ω') hfix with h1 | h1
      · exact hz₁ω'_ne_ω h1
      · exact hz₁ω'_ne_ω' h1
    have hFsurj : Function.Surjective F := by
      have hbij : Function.Bijective F :=
        (Nat.bijective_iff_injective_and_card F).mpr ⟨hFinj, hSubCard.symm⟩
      exact hbij.2
    have hZRleZ : ZR ≤ Z := by
      intro z hzZR
      by_cases hz1 : z = 1
      · rw [hz1]
        exact Z.one_mem
      · have hz1' : (⟨z, hzZR⟩ : ZR) ≠ 1 := fun h1 => hz1 (congrArg Subtype.val h1)
        obtain ⟨t, ht⟩ := hFsurj ⟨⟨z, hzZR⟩, hz1'⟩
        have hconj : (t : X) * (z₁ : X) * (t : X)⁻¹ = (z : X) := by
          simpa [F] using congrArg (fun z : {z : ZR // z ≠ 1} => ((z : ZR) : X)) ht
        rw [← hconj]
        exact hZn t t.2 z₁ hz₁Z
    have hyZR : (y : X) ∈ ZR := by
      refine ⟨hyR, ?_⟩
      change (y : X) ∈ Subgroup.centralizer (R : Set X)
      rw [Subgroup.mem_centralizer_iff]
      intro r hr
      exact hycent r hr
    exact hZRleZ hyZR
  · intro ω ω' hne R hR hRn hR2 hreg g hg hodd hgcent
    let Gω : Subgroup X := MulAction.stabilizer X ω
    let Gω' : Subgroup X := MulAction.stabilizer X ω'
    let T : Subgroup X := N ⊓ Gω ⊓ Gω'
    let ZR : Subgroup X := R ⊓ Subgroup.centralizer (R : Set X)
    have hcardZR : Nat.card ↥ZR = Nat.card ↥T + 1 := by
      have h1 := hcard ω ω' hne R hR hRn hR2 hreg
      simpa [ZR, T, Gω, Gω'] using h1
    have hZRne : ZR ≠ ⊥ := by
      intro hbot
      have h1 : Nat.card ↥ZR = 1 := by
        rw [hbot]
        simp
      haveI : Nonempty ↥T := ⟨1⟩
      have hTpos : 0 < Nat.card ↥T := Nat.card_pos
      omega
    have hTnormZR : T ≤ Subgroup.normalizer ZR := by
      rw [Subgroup.le_normalizer_iff]
      intro t ht z hz
      refine ⟨(Subgroup.normal_subgroupOf_iff hR).mp hRn z t hz.1 ht.1.2, ?_⟩
      have hzcentX : (z : X) ∈ Subgroup.centralizer (R : Set X) := hz.2
      change (t * z * t⁻¹) ∈ Subgroup.centralizer (R : Set X)
      rw [Subgroup.mem_centralizer_iff] at hzcentX ⊢
      intro r hr
      have htr : t⁻¹ * r * t ∈ R := by
        simpa using
          (Subgroup.normal_subgroupOf_iff hR).mp hRn r t⁻¹ hr (Gω.inv_mem ht.1.2)
      have hcomm := hzcentX (t⁻¹ * r * t) htr
      calc r * (t * z * t⁻¹) = t * ((t⁻¹ * r * t) * z) * t⁻¹ := by group
        _ = t * (z * (t⁻¹ * r * t)) * t⁻¹ := by rw [hcomm]
        _ = (t * z * t⁻¹) * r := by group
    have hCT : ∀ t ∈ T, (∀ z ∈ ZR, t * z = z * t) → t = 1 := by
      intro t ht hcomm
      by_contra htne
      obtain ⟨z, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hZRne
      have hzR : (z : X) ∈ R := z.2.1
      have hzω'_ne_ω : (z : X) • ω' ≠ ω := by
        intro h1
        have hzω : (z : X) • ω = ω := hR hzR
        have h2 : ω' = ω := by
          calc ω' = (z : X)⁻¹ • ((z : X) • ω') := (inv_smul_smul (z : X) ω').symm
            _ = (z : X)⁻¹ • ω := by rw [h1]
            _ = ω := by
              conv_lhs => rw [← hzω]
              exact inv_smul_smul (z : X) ω
        exact hne h2.symm
      have hzω'_ne_ω' : (z : X) • ω' ≠ ω' := by
        intro h1
        have h2 : (⟨(z : X), hzR⟩ : R) = 1 := by
          apply (hreg ω' ω' hne.symm hne.symm).unique
          · show ((⟨(z : X), hzR⟩ : R) : X) • ω' = ω'
            simpa using h1
          · simp
        have h3 : (z : X) = 1 := congrArg Subtype.val h2
        exact hz1 (Subtype.ext h3)
      have htneX : (t : X) ≠ 1 := htne
      have hfix : (t : X) • ((z : X) • ω') = (z : X) • ω' := by
        rw [← mul_smul, hcomm (z : X) z.2, mul_smul]
        congr 1
        exact MulAction.mem_stabilizer_iff.mp ht.2
      rcases hZ.fix_two ω ω' hne (t : X) ht htneX ((z : X) • ω') hfix with h1 | h1
      · exact hzω'_ne_ω h1
      · exact hzω'_ne_ω' h1
    have hcommT : ∀ t ∈ T, g * t = t * g := by
      intro t ht
      let tT : T := ⟨t, ht⟩
      change g * (tT : X) = (tT : X) * g
      have hcT : g * (tT : X) * g⁻¹ * (tT : X)⁻¹ ∈ T := by
        refine ⟨⟨?_, ?_⟩, ?_⟩
        · have h1 : g * (tT : X) * g⁻¹ ∈ N := hN.conj_mem (tT : X) tT.2.1.1 g
          exact N.mul_mem h1 (N.inv_mem tT.2.1.1)
        · exact Gω.mul_mem (Gω.mul_mem (Gω.mul_mem hg.1 tT.2.1.2) (Gω.inv_mem hg.1))
            (Gω.inv_mem tT.2.1.2)
        · exact Gω'.mul_mem (Gω'.mul_mem (Gω'.mul_mem hg.2 tT.2.2) (Gω'.inv_mem hg.2))
            (Gω'.inv_mem tT.2.2)
      have hcZ : ∀ z ∈ ZR,
          (g * (tT : X) * g⁻¹ * (tT : X)⁻¹) * z =
            z * (g * (tT : X) * g⁻¹ * (tT : X)⁻¹) := by
        intro z hzZR
        have htinz : (tT : X)⁻¹ * z * (tT : X) ∈ ZR := by
          simpa using
            (Subgroup.le_normalizer_iff.mp hTnormZR) (((tT)⁻¹ : T) : X) (T.inv_mem tT.2) z hzZR
        have hzcent : ∀ r ∈ R, r * z = z * r :=
          Subgroup.mem_centralizer_iff.mp hzZR.2
        have hgcentZ : g * z = z * g := hgcent z hzZR.1 hzcent
        have hginv : g⁻¹ * ((tT : X)⁻¹ * z * (tT : X)) =
            ((tT : X)⁻¹ * z * (tT : X)) * g⁻¹ := by
          have hgcentIn : g * ((tT : X)⁻¹ * z * (tT : X)) =
              ((tT : X)⁻¹ * z * (tT : X)) * g :=
            hgcent ((tT : X)⁻¹ * z * (tT : X)) htinz.1
              (Subgroup.mem_centralizer_iff.mp htinz.2)
          calc g⁻¹ * ((tT : X)⁻¹ * z * (tT : X))
              = g⁻¹ * (((tT : X)⁻¹ * z * (tT : X)) * g) * g⁻¹ := by group
            _ = g⁻¹ * (g * ((tT : X)⁻¹ * z * (tT : X))) * g⁻¹ := by rw [← hgcentIn]
            _ = ((tT : X)⁻¹ * z * (tT : X)) * g⁻¹ := by group
        have hczconj : (g * (tT : X) * g⁻¹ * (tT : X)⁻¹) * z *
            (g * (tT : X) * g⁻¹ * (tT : X)⁻¹)⁻¹ = z := by
          calc (g * (tT : X) * g⁻¹ * (tT : X)⁻¹) * z *
                (g * (tT : X) * g⁻¹ * (tT : X)⁻¹)⁻¹
              = g * (tT : X) *
                  (g⁻¹ * ((tT : X)⁻¹ * z * (tT : X)) * g) *
                  (tT : X)⁻¹ * g⁻¹ := by group
            _ = g * (tT : X) *
                  (((tT : X)⁻¹ * z * (tT : X)) * g⁻¹ * g) *
                  (tT : X)⁻¹ * g⁻¹ := by rw [hginv]
            _ = g * (tT : X) * ((tT : X)⁻¹ * z * (tT : X)) * (tT : X)⁻¹ * g⁻¹ := by
                group
            _ = g * z * g⁻¹ := by group
            _ = z := by
                rw [hgcentZ]
                group
        calc (g * (tT : X) * g⁻¹ * (tT : X)⁻¹) * z
            = ((g * (tT : X) * g⁻¹ * (tT : X)⁻¹) * z *
                (g * (tT : X) * g⁻¹ * (tT : X)⁻¹)⁻¹) *
                (g * (tT : X) * g⁻¹ * (tT : X)⁻¹) := by group
          _ = z * (g * (tT : X) * g⁻¹ * (tT : X)⁻¹) := by rw [hczconj]
      have hc1 : g * (tT : X) * g⁻¹ * (tT : X)⁻¹ = 1 :=
        hCT (g * (tT : X) * g⁻¹ * (tT : X)⁻¹) hcT hcZ
      calc g * (tT : X) = (g * (tT : X) * g⁻¹ * (tT : X)⁻¹) * ((tT : X) * g) := by
            group
        _ = 1 * ((tT : X) * g) := by rw [hc1]
        _ = (tT : X) * g := one_mul _
    have hgN : g ∈ N := hZ.centralizer_le ω ω' hne g hg hcommT
    have hgT : g ∈ T := ⟨⟨hgN, hg.1⟩, hg.2⟩
    have hg1 : g = 1 :=
      hCT g hgT (fun z hz => hgcent z hz.1 (Subgroup.mem_centralizer_iff.mp hz.2))
    simpa [hg1]

end RankOneLocal

end CFSG.Quasithin.Stroth.WeissDelta
