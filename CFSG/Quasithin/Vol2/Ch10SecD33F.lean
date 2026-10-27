module

public import CFSG.Quasithin.Vol2.Ch10SecD33D
public import CFSG.Quasithin.Vol2.Ch10SecD33B

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecD

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G]

abbrev barSub (K₁ Y : Subgroup G) : Subgroup (↥K₁ ⧸ CFSG.pCore 2 ↥K₁) :=
  (Y.subgroupOf K₁).map (QuotientGroup.mk' (CFSG.pCore 2 ↥K₁))

theorem isSolvable_of_barSub {K₁ Y : Subgroup G} (hY : Y ≤ K₁)
    (h : Group.IsSolvable ↥(barSub K₁ Y)) : Group.IsSolvable ↥Y := by
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥K₁) with hπ
  set Y' := Y.subgroupOf K₁ with hY'
  let g : ↥Y' →* ↥(Y'.map π) := π.subgroupMap Y'
  have hker : IsPGroup 2 g.ker := by
    intro x
    have hx : (x : ↥Y') ∈ g.ker := x.2
    have hx1 : ((x : ↥Y') : ↥K₁) ∈ CFSG.pCore 2 ↥K₁ := by
      rw [MonoidHom.mem_ker] at hx
      have := congrArg Subtype.val hx
      simpa [g, π, QuotientGroup.eq_one_iff] using this
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥K₁)) ⟨_, hx1⟩
    refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
    have := congrArg (fun u : ↥(CFSG.pCore 2 ↥K₁) => (u : ↥K₁)) hk
    simpa using this
  have : Group.IsSolvable ↥g.ker := E1.isSolvable_of_isPGroup_two hker
  have : Group.IsSolvable ↥(Y'.map π) := h
  have : Group.IsSolvable ↥Y' := Group.isSolvable_of_ker_le_range g.ker.subtype g (by simp)
  exact Group.isSolvable_of_surjective (f := (Subgroup.subgroupOfEquivOfLe hY).toMonoidHom)
    (MulEquiv.surjective _)

theorem not_isSolvable_barSub_proj (hK : LocalSQTK G) (h37 : Vol2Native.A37ForSQTKCat)
    {X K₁ H T : Subgroup G} (hX : pCoreOf 2 X ≠ ⊥) (hK₁ : K₁ ∈ cComp X) {s : G} (hs : s ∈ X)
    (hsn : s ∉ Subgroup.normalizer (K₁ : Set G))
    (hsK : s ∈ Subgroup.normalizer ((K₁ ⊔ CFSG.conjugate K₁ s : Subgroup G) : Set G))
    (hTs : IsSylowTwoOf T H) (hsH : s ∈ H) (hO : oTwoUpper H ≤ K₁ ⊔ CFSG.conjugate K₁ s)
    (hHns : ¬ Group.IsSolvable ↥H) :
    ¬ Group.IsSolvable ↥(barSub K₁ (K₁ ⊓ ((H ⊓ (K₁ ⊔ CFSG.conjugate K₁ s)) ⊔
      CFSG.conjugate K₁ s))) := by
  intro hsol
  have hP := isSolvable_of_barSub inf_le_left hsol
  have hY := isSolvable_of_inf_sup hK h37 hX hK₁ hs hsn hsK
    (Y := H ⊓ (K₁ ⊔ CFSG.conjugate K₁ s)) inf_le_right
    (mem_normalizer_inf (Subgroup.le_normalizer hsH) hsK) hP
  have hOs : Group.IsSolvable ↥(oTwoUpper H) :=
    Group.isSolvable_of_isSolvable_injective
      (Subgroup.inclusion_injective (le_inf (oTwoUpper_le H) hO))
  have hT2 : Group.IsSolvable ↥T := E1.isSolvable_of_isPGroup_two hTs.2.1
  have hall : Group.IsSolvable ↥(oTwoUpper H ⊔ T) :=
    A3.isSolvable_sup_of_le_normalizer (hTs.1.trans (le_normalizer_oTwoUpper H))
  rw [oTwoUpper_sup_eq hTs] at hall
  exact hHns hall

theorem conj_mem_barSub_inf (hK : LocalSQTK G) (h37 : Vol2Native.A37ForSQTKCat)
    {X K₁ H : Subgroup G} (hX : pCoreOf 2 X ≠ ⊥) (hK₁ : K₁ ∈ cComp X) {s : G} (hs : s ∈ X)
    (hsn : s ∉ Subgroup.normalizer (K₁ : Set G)) {q a : ↥K₁ ⧸ CFSG.pCore 2 ↥K₁}
    (hq : q ∈ barSub K₁ (K₁ ⊓ ((H ⊓ (K₁ ⊔ CFSG.conjugate K₁ s)) ⊔ CFSG.conjugate K₁ s)))
    (ha : a ∈ barSub K₁ (H ⊓ K₁)) : q * a * q⁻¹ ∈ barSub K₁ (H ⊓ K₁) := by
  set K₂ := CFSG.conjugate K₁ s with hK₂def
  have hK₂ : K₂ ∈ cComp X := conjugate_mem_cComp hK₁ hs
  have h12 : K₁ ≤ Subgroup.normalizer (K₂ : Set G) := le_normalizer_of_mem_cComp hK₂ hK₁
  have h21 : K₂ ≤ Subgroup.normalizer (K₁ : Set G) := le_normalizer_of_mem_cComp hK₁ hK₂
  have hKN1 : K₁ ⊔ K₂ ≤ Subgroup.normalizer (K₁ : Set G) := sup_le Subgroup.le_normalizer h21
  have hKN2 : K₁ ⊔ K₂ ≤ Subgroup.normalizer (K₂ : Set G) := sup_le h12 Subgroup.le_normalizer
  have hcomm := commutator_cComp_le hK h37 hX hK₁ hs hsn
  obtain ⟨p, hp, rfl⟩ := hq
  obtain ⟨a', ha', rfl⟩ := ha
  rw [← map_inv, ← map_mul, ← map_mul]
  have hp' : (p : G) ∈ (H ⊓ (K₁ ⊔ K₂)) ⊔ K₂ := (Subgroup.mem_subgroupOf.mp hp).2
  obtain ⟨h, hh, k₂, hk₂, hpe⟩ :=
    exists_mul_of_mem_sup_of_le_normalizer (inf_le_right.trans hKN2) hp'
  have ha'G : (a' : G) ∈ H ⊓ K₁ := Subgroup.mem_subgroupOf.mp ha'
  have hc : (a' : G)⁻¹ * k₂ * a' * k₂⁻¹ ∈ pCoreOf 2 K₁ := by
    have := Subgroup.commutator_mem_commutator (K₁.inv_mem a'.2) hk₂
    rw [commutatorElement_def, inv_inv] at this
    exact (hcomm this).1
  have hhN : h ∈ Subgroup.normalizer (K₁ : Set G) := hKN1 hh.2
  have ha'' : h * a' * h⁻¹ ∈ H ⊓ K₁ :=
    ⟨H.mul_mem (H.mul_mem hh.1 ha'G.1) (H.inv_mem hh.1),
      (Subgroup.mem_normalizer_iff.mp hhN _).mp a'.2⟩
  have hc' : h * ((a' : G)⁻¹ * k₂ * a' * k₂⁻¹) * h⁻¹ ∈ pCoreOf 2 K₁ :=
    (Subgroup.mem_normalizer_iff.mp (mem_normalizer_pCoreOf hhN) _).mp hc
  have hc'K : h * ((a' : G)⁻¹ * k₂ * a' * k₂⁻¹) * h⁻¹ ∈ K₁ := Subgroup.map_subtype_le _ hc'
  have he : (p : G) * a' * (p : G)⁻¹ =
      (h * a' * h⁻¹) * (h * ((a' : G)⁻¹ * k₂ * a' * k₂⁻¹) * h⁻¹) := by
    rw [hpe]
    group
  refine ⟨⟨h * a' * h⁻¹, ha''.2⟩, Subgroup.mem_subgroupOf.mpr ha'', ?_⟩
  have hpc : (⟨h * ((a' : G)⁻¹ * k₂ * a' * k₂⁻¹) * h⁻¹, hc'K⟩ : ↥K₁) ∈ CFSG.pCore 2 ↥K₁ := by
    obtain ⟨y, hy, hye⟩ := hc'
    have : y = ⟨h * ((a' : G)⁻¹ * k₂ * a' * k₂⁻¹) * h⁻¹, hc'K⟩ := Subtype.ext hye
    rw [← this]
    exact hy
  have hpa : p * a' * p⁻¹ = (⟨h * a' * h⁻¹, ha''.2⟩ : ↥K₁) *
      ⟨h * ((a' : G)⁻¹ * k₂ * a' * k₂⁻¹) * h⁻¹, hc'K⟩ := Subtype.ext he
  have hpc1 : QuotientGroup.mk' (CFSG.pCore 2 ↥K₁)
      (⟨h * ((a' : G)⁻¹ * k₂ * a' * k₂⁻¹) * h⁻¹, hc'K⟩ : ↥K₁) = 1 := by
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hpc
  rw [hpa, map_mul, hpc1, mul_one]

theorem exists_sylow_barSub {X K₁ T : Subgroup G} (hK₁ : K₁ ∈ cComp X) (hT : IsSylowTwoOf T X) :
    ∃ U : Sylow 2 (↥K₁ ⧸ CFSG.pCore 2 ↥K₁), (U : Subgroup _) = barSub K₁ (T ⊓ K₁) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTK := A312.isSylowTwoOf_inf_of_subnormal (subnormal_of_mem_cComp hK₁) hT
  exact ⟨(A4.toSylow hTK).mapSurjective (QuotientGroup.mk'_surjective _), rfl⟩

theorem le_of_barSub_inf_eq_top {X K₁ H T : Subgroup G} (hK₁ : K₁ ∈ cComp X)
    (hT : IsSylowTwoOf T X) (hTH : T ≤ H) (htop : barSub K₁ (H ⊓ K₁) = ⊤) : K₁ ≤ H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro k hk
  have hmem : QuotientGroup.mk' (CFSG.pCore 2 ↥K₁) ⟨k, hk⟩ ∈ barSub K₁ (H ⊓ K₁) := by
    rw [htop]
    trivial
  obtain ⟨a, ha, hae⟩ := hmem
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hae
  have hO : ((a⁻¹ * ⟨k, hk⟩ : ↥K₁) : G) ∈ pCoreOf 2 K₁ := ⟨_, hae, rfl⟩
  have hOT : ((a⁻¹ * ⟨k, hk⟩ : ↥K₁) : G) ∈ T :=
    IsSylowTwoOf.pCoreOf_le hT (A4.pCoreOf_le_of_subnormal 2 (subnormal_of_mem_cComp hK₁) hO)
  have e : k = (a : G) * ((a⁻¹ * ⟨k, hk⟩ : ↥K₁) : G) := by simp
  rw [e]
  exact H.mul_mem (Subgroup.mem_subgroupOf.mp ha).1 (hTH hOT)

theorem le_of_barSub_proj_eq_top (hK : LocalSQTK G) (h37 : Vol2Native.A37ForSQTKCat)
    {X K₁ H T : Subgroup G} (hX : pCoreOf 2 X ≠ ⊥) (hK₁ : K₁ ∈ cComp X) {s : G} (hs : s ∈ X)
    (hsn : s ∉ Subgroup.normalizer (K₁ : Set G)) (hT : IsSylowTwoOf T X) (hTH : T ≤ H)
    (hsimp : IsSimpleGroup (↥K₁ ⧸ CFSG.pCore 2 ↥K₁))
    (heven : 2 ∣ Nat.card (↥K₁ ⧸ CFSG.pCore 2 ↥K₁))
    (htop : barSub K₁ (K₁ ⊓ ((H ⊓ (K₁ ⊔ CFSG.conjugate K₁ s)) ⊔ CFSG.conjugate K₁ s)) = ⊤) :
    K₁ ≤ H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine le_of_barSub_inf_eq_top hK₁ hT hTH ?_
  have hN : (barSub K₁ (H ⊓ K₁)).Normal := ⟨fun a ha g => by
    have := conj_mem_barSub_inf hK h37 hX hK₁ hs hsn (H := H) (q := g) (a := a)
      (by rw [htop]; trivial) ha
    exact this⟩
  have := hsimp
  rcases hN.eq_bot_or_eq_top with hbot | htop'
  · exfalso
    obtain ⟨U, hU⟩ := exists_sylow_barSub hK₁ hT
    apply Sylow.ne_bot_of_dvd_card U heven
    rw [hU, eq_bot_iff, ← hbot]
    exact Subgroup.map_mono fun x hx => Subgroup.mem_subgroupOf.mpr
      ⟨hTH (Subgroup.mem_subgroupOf.mp hx).1, (Subgroup.mem_subgroupOf.mp hx).2⟩
  · exact htop'

end CFSG.Quasithin.Vol2.Ch10.SecD
