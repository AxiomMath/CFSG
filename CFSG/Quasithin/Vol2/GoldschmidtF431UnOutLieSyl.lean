module

public import CFSG.Quasithin.Vol2.GoldschmidtF431UnOutLieLev
public import CFSG.Quasithin.Vol2.GoldschmidtF431UnOutLieSub
public import CFSG.Quasithin.Vol2.GoldschmidtF431UnOutDatum
public import CFSG.Quasithin.Vol2.GoldschmidtF431UnOutLieBar

public noncomputable section

namespace CFSG.Quasithin.H13.F431.Un.OL

set_option linter.unusedSectionVars false

open Matrix Subgroup CFSG.LocalAnalysis CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.EvenBN.U4 CFSG.QuasithinUnique CFSG.Quasithin.H13.F431.Un

section Field

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)

theorem exists_F2 (Fk : Subgroup (K ≃+* K)) (hev : ¬ Odd (Nat.card Fk)) :
    ∃ F₂ : Subgroup (K ≃+* K), IsSylowTwoOf F₂ Fk ∧ barE h ∈ F₂ ∧
      ∃ φ₀ ∈ F₂, F₂ = Subgroup.zpowers φ₀ := by
  have := finite_aut h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P⟩ : Nonempty (Sylow 2 ↥Fk) := ⟨default⟩
  set F₂ : Subgroup (K ≃+* K) := (P : Subgroup ↥Fk).map Fk.subtype with hF₂
  have hsub : F₂.subgroupOf Fk = (P : Subgroup ↥Fk) := by
    ext x
    rw [Subgroup.mem_subgroupOf, hF₂]
    exact Subgroup.mem_map_iff_mem Fk.subtype_injective
  have hSyl : IsSylowTwoOf F₂ Fk := by
    refine ⟨Subgroup.map_subtype_le _, ?_, ?_⟩
    · exact P.isPGroup'.of_equiv ((P : Subgroup ↥Fk).equivMapOfInjective Fk.subtype
        Fk.subtype_injective)
    · rw [hsub]
      exact P.not_dvd_index
  have hne : F₂ ≠ ⊥ := by
    intro e
    have h1 : (F₂.subgroupOf Fk).index = Nat.card Fk := by
      rw [e, Subgroup.bot_subgroupOf, Subgroup.index_bot]
    apply hSyl.2.2
    rw [h1]
    exact even_iff_two_dvd.1 (Nat.not_odd_iff_even.1 hev)
  have h2 : 2 ∣ Nat.card ↥F₂ := by
    rcases hSyl.2.1.card_eq_or_dvd with hc | hc
    · exact absurd (Subgroup.card_eq_one.1 hc) hne
    · exact hc
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥F₂) 2 h2
  have hxx : (x : K ≃+* K) * x = 1 := by
    have e := pow_orderOf_eq_one x
    rw [hx, sq] at e
    exact congrArg Subtype.val e
  have hx1 : (x : K ≃+* K) ≠ 1 := fun e => by
    have : x = 1 := Subtype.ext e
    rw [this, orderOf_one] at hx
    exact absurd hx (by norm_num)
  have hbar : barE h ∈ F₂ := by
    rw [← eq_barE_of_mul_self h hxx hx1]
    exact x.2
  have : IsCyclic (K ≃+* K) := isCyclic_aut h
  have : IsCyclic ↥F₂ := inferInstance
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥F₂)
  refine ⟨F₂, hSyl, hbar, g, g.2, ?_⟩
  ext y
  constructor
  · intro hy
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hg ⟨y, hy⟩)
    exact Subgroup.mem_zpowers_iff.2 ⟨k, by simpa using congrArg Subtype.val hk⟩
  · intro hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    exact F₂.zpow_mem g.2 k

end Field

section Sylow

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K) [CharP K 2]

theorem Ssd_conj_bot_mem {B : Subgroup (Xg h)} {hB : FStab h B} {F : Subgroup (K ≃+* K)}
    {α y : MulAut (Xg h)} (hα : α ∈ Ssd h B hB F) (hy : y ∈ Ssd h B hB ⊥) :
    α * y * α⁻¹ ∈ Ssd h B hB ⊥ := by
  obtain ⟨u, hu, φ, hφ, rfl⟩ := hα
  obtain ⟨s, hs, ψ, hψ, rfl⟩ := hy
  rw [Subgroup.mem_bot] at hψ
  subst hψ
  rw [fa_one, mul_one]
  have e : cj h u * fa h φ * cj h s * (cj h u * fa h φ)⁻¹ = cj h (u * fa h φ s * u⁻¹) := by
    have e1 := fa_mul_cj_mul_inv h φ s
    rw [cj_mul, cj_mul, cj_inv, ← e1]
    group
  rw [e]
  exact ⟨u * fa h φ s * u⁻¹, B.mul_mem (B.mul_mem hu ((hB φ s).2 hs)) (B.inv_mem hu), 1,
    Subgroup.one_mem _, by rw [fa_one, mul_one]⟩

theorem Ssd_le_normalizer_bot (B : Subgroup (Xg h)) (hB : FStab h B) (F : Subgroup (K ≃+* K)) :
    Ssd h B hB F ≤ Subgroup.normalizer (Ssd h B hB ⊥ : Set (MulAut (Xg h))) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    exact Ssd_conj_bot_mem h hx hy
  · intro hy
    have := Ssd_conj_bot_mem h ((Ssd h B hB F).inv_mem hx) hy
    simpa [mul_assoc] using this

theorem Ssd_eq_sup_zpowers (B : Subgroup (Xg h)) (hB : FStab h B) {F₂ : Subgroup (K ≃+* K)}
    {φ₀ : K ≃+* K} (hφ₀ : F₂ = Subgroup.zpowers φ₀) :
    Ssd h B hB F₂ = Ssd h B hB ⊥ ⊔ Subgroup.zpowers (fa h φ₀) := by
  apply le_antisymm
  · rintro _ ⟨s, hs, φ, hφ, rfl⟩
    rw [hφ₀] at hφ
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hφ
    refine mul_mem (Subgroup.mem_sup_left (cj_mem_Ssd h hs)) (Subgroup.mem_sup_right ?_)
    have : fa h (φ₀ ^ k) = fa h φ₀ ^ k := map_zpow (miyamotoFieldHom h) φ₀ k
    rw [this]
    exact Subgroup.zpow_mem_zpowers _ _
  · refine sup_le (Ssd_mono h le_rfl bot_le) ?_
    rw [Subgroup.zpowers_le]
    exact fa_mem_Ssd h (hφ₀ ▸ Subgroup.mem_zpowers φ₀)

theorem isSylowTwoOf_Ssd_Psy {K₀ : Subgroup (MulAut (Xg h))}
    (hinn : (MulAut.conj : Xg h →* MulAut (Xg h)).range ≤ K₀) {F₂ : Subgroup (K ≃+* K)}
    (hF : IsSylowTwoOf F₂ (FK h K₀)) :
    IsSylowTwoOf (Ssd h (Psy h) (fStab_Psy h) F₂) K₀ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := finite_aut h
  set T := Ssd h (Psy h) (fStab_Psy h) F₂ with hT
  have hTK : T ≤ K₀ := Ssd_le h hinn hF.1
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.1 (isSylowTwoOf_Psy h).2.1
  obtain ⟨b, hb⟩ := IsPGroup.iff_card.1 hF.2.1
  have hcT : Nat.card T = 2 ^ (a + b) := by
    rw [hT, card_Ssd, ha, hb, pow_add]
  have hX : Nat.card (Psy h) * (Psy h).index = Nat.card (Xg h) := Subgroup.card_mul_index _
  have hFk : Nat.card F₂ * (F₂.subgroupOf (FK h K₀)).index = Nat.card (FK h K₀) := by
    have := Subgroup.card_mul_index (F₂.subgroupOf (FK h K₀))
    rwa [sub_card (FK h K₀) hF.1] at this
  have hK₀ := Subgroup.card_mul_index (T.subgroupOf K₀)
  rw [sub_card K₀ hTK, card_eq_mul_FK h hinn, ← hX, ← hFk] at hK₀
  rw [hT, card_Ssd] at hK₀
  have hpos : 0 < Nat.card (Psy h) * Nat.card F₂ := Nat.mul_pos Nat.card_pos Nat.card_pos
  have hidx : (T.subgroupOf K₀).index = (Psy h).index * (F₂.subgroupOf (FK h K₀)).index := by
    apply Nat.eq_of_mul_eq_mul_left hpos
    rw [hK₀]
    ring
  refine ⟨hTK, IsPGroup.of_card hcT, ?_⟩
  rw [hidx]
  intro hd
  rcases (Nat.Prime.dvd_mul Nat.prime_two).1 hd with h1 | h1
  · have e : ((Psy h).subgroupOf ⊤).index = (Psy h).index := Subgroup.relIndex_top_right _
    exact (isSylowTwoOf_Psy h).2.2 (e ▸ h1)
  · exact hF.2.2 h1

theorem fbar_mem_Ssd {B : Subgroup (Xg h)} {hB : FStab h B} {F : Subgroup (K ≃+* K)}
    (hF : barE h ∈ F) : fbar h ∈ Ssd h B hB F := fa_mem_Ssd h hF

theorem fbar_not_mem_Ssd_bot {B : Subgroup (Xg h)} {hB : FStab h B} : fbar h ∉ Ssd h B hB ⊥ := by
  rintro ⟨s, -, φ, hφ, e⟩
  rw [Subgroup.mem_bot] at hφ
  subst hφ
  rw [fa_one, mul_one] at e
  have e' : cj h 1 * fa h (barE h) = cj h s * fa h 1 := by
    rw [cj_one, one_mul, fa_one, mul_one]
    exact e
  exact barE_ne_one h ((conj_mul_fieldAut_inj h).1 e').2

theorem fbar_sq : fbar h ^ 2 = 1 := by
  rw [sq, fa_mul, barE_mul_self, fa_one]

end Sylow

end CFSG.Quasithin.H13.F431.Un.OL
