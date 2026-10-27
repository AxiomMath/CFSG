module

public import CFSG.Quasithin.Background.B4L3FactA
public import CFSG.Quasithin.Background.B4L3Key
public import CFSG.Quasithin.Background.B4L3Off
public import CFSG.Quasithin.Background.B4L3Syl

public section

namespace CFSG.Quasithin

variable {V : Type*} [CommGroup V] [Finite V]

@[expose] def IsAxisTransvGroup (G B : Subgroup (MulAut V)) : Prop :=
  ∃ H : Subgroup V, H ≤ commV G ∧ Nat.card H = 4 ∧ B = G ⊓ centSub H

theorem isPlane_fixS {γ : L3.Γ} (hγ : L3.IsInvol γ) : L3.IsPlane (L3.fixS γ) := by
  refine ⟨L3.invol_fixS_card γ hγ, ?_, ?_⟩
  · simp [L3.fixS, L3.act_zero]
  · intro x hx y hy
    simp only [L3.fixS, Finset.mem_filter, Finset.mem_univ, true_and] at hx hy ⊢
    rw [L3.act_add, hx, hy]

theorem fixS_zero_mem (γ : L3.Γ) : (0 : L3.Vec) ∈ L3.fixS γ := by
  simp [L3.fixS, L3.act_zero]

theorem fixS_add_mem (γ : L3.Γ) : ∀ x ∈ L3.fixS γ, ∀ y ∈ L3.fixS γ, x + y ∈ L3.fixS γ := by
  intro x hx y hy
  simp only [L3.fixS, Finset.mem_filter, Finset.mem_univ, true_and] at hx hy ⊢
  rw [L3.act_add, hx, hy]

@[expose] def fixSub (γ : L3.Γ) : Subgroup (Multiplicative L3.Vec) :=
  SubOf (L3.fixS γ) (fixS_zero_mem γ) (fixS_add_mem γ)

theorem card_fixSub {γ : L3.Γ} (hγ : L3.IsInvol γ) : Nat.card (fixSub γ) = 4 := by
  unfold fixSub
  rw [card_SubOf]
  exact L3.invol_fixS_card γ hγ

theorem fixSub_injective {γ δ : L3.Γ} (h : fixSub γ = fixSub δ) : L3.fixS γ = L3.fixS δ := by
  ext x
  have h1 : Multiplicative.ofAdd x ∈ fixSub γ ↔ Multiplicative.ofAdd x ∈ fixSub δ := by rw [h]
  exact h1

@[expose] def BSsub (S : Finset L3.Vec) (hS : L3.IsPlane S) : Subgroup L3.Γ where
  carrier := {δ | δ ∈ L3.BS S}
  one_mem' := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun v _ => ?_⟩
    exact L3.act_one v
  mul_mem' := fun {x y} hx hy => by
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun v hv => ?_⟩
    exact L3.BS_mul S hS x hx y hy v hv
  inv_mem' := fun {x} hx => by
    have h := (L3.BS_elem S hS x hx x hx).2
    have : x⁻¹ = x := inv_eq_of_mul_eq_one_right h
    rw [this]
    exact hx

theorem card_BSsub {S : Finset L3.Vec} (hS : L3.IsPlane S) : Nat.card (BSsub S hS) = 4 := by
  rw [← L3.BS_card S hS, ← Fintype.card_coe, ← Nat.card_eq_fintype_card]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun x => Iff.rfl)

section Three

variable {G : Subgroup (MulAut V)} {U Z : Subgroup V} (D : L3Data G U Z)

omit [Finite V] in
include D in
theorem le_centQuot_three (hcard : Nat.card V = 16) (hZ : Z = ⊥) : G ≤ centQuot U := by
  have hU8 := D.card_U
  rw [hZ, Subgroup.card_bot] at hU8
  have hidx : U.index = 2 := by
    have h := Subgroup.card_mul_index U
    rw [hcard, hU8] at h
    omega
  intro g hg v
  rw [Subgroup.mul_mem_iff_of_index_two hidx]
  have h1 : g v ∈ U ↔ v ∈ U := by
    constructor
    · intro h
      have := D.inv_U g⁻¹ (G.inv_mem hg) _ h
      simpa using this
    · exact D.inv_U g hg v
  rw [h1]
  exact ⟨fun h => U.inv_mem h, fun h => U.inv_mem_iff.1 h⟩

include D in
theorem fixV_rho_three (hV : ∀ v : V, v ^ 2 = 1) (hcard : Nat.card V = 16)
    (hZ : Z = ⊥) (hind : IsIndecompModule G) {δ : L3.Γ} (hδ : L3.IsInvol δ) :
    fixV (Subgroup.zpowers (D.rho δ)) = D.pre (fixSub δ) := by
  have haG : D.rho δ ∈ G := D.rho_mem δ
  have ha2 : D.rho δ ^ 2 = 1 := by rw [pow_two, ← map_mul, hδ.1, map_one]
  have ha1 : D.rho δ ≠ 1 := by
    intro h
    apply hδ.2
    apply D.rho_injective
    rw [h, map_one]
  have hF := card_fixV_involution_three D hV hcard hZ hind haG ha1 ha2
  have hCF : commV (Subgroup.zpowers (D.rho δ)) = fixV (Subgroup.zpowers (D.rho δ)) := by
    apply Subgroup.eq_of_le_of_card_ge (commV_zpowers_le_fixV_b4 hV ha2)
    have := card_commV_mul_card_fixV hV (D.rho δ)
    rw [hF, hcard] at this
    omega
  have hGU := le_centQuot_three D hcard hZ
  have hFU : fixV (Subgroup.zpowers (D.rho δ)) ≤ U := by
    intro v hv
    rw [← hCF, commV_zpowers_eq_map] at hv
    obtain ⟨v', -, rfl⟩ := hv
    exact hGU haG v'
  have hle : fixV (Subgroup.zpowers (D.rho δ)) ≤ D.pre (fixSub δ) := by
    intro v hv
    rw [D.mem_pre]
    refine ⟨hFU hv, ?_⟩
    have h1 := mem_fixV_zpowers_iff.mp hv
    have hmem : D.rho δ v ∈ U := D.inv_U _ haG _ (hFU hv)
    have h2 := D.β_rho δ v (hFU hv) hmem
    have h3 : (⟨D.rho δ v, hmem⟩ : ↥U) = ⟨v, hFU hv⟩ := Subtype.ext h1
    rw [h3] at h2
    show Multiplicative.toAdd (D.β ⟨v, hFU hv⟩) ∈ L3.fixS δ
    simp only [L3.fixS, Finset.mem_filter, Finset.mem_univ, true_and]
    have h4 := congrArg Multiplicative.toAdd h2
    exact h4.symm
  have hZc : Nat.card Z = 1 := by rw [hZ]; exact Subgroup.card_bot
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [D.card_pre, hZc, card_fixSub hδ, hF]

include D in
theorem fixV_rho_eq_iff_three (hV : ∀ v : V, v ^ 2 = 1) (hcard : Nat.card V = 16)
    (hZ : Z = ⊥) (hind : IsIndecompModule G) {δ γ : L3.Γ} (hδ : L3.IsInvol δ)
    (hγ : L3.IsInvol γ) :
    fixV (Subgroup.zpowers (D.rho δ)) = fixV (Subgroup.zpowers (D.rho γ)) ↔
      L3.fixS δ = L3.fixS γ := by
  rw [fixV_rho_three D hV hcard hZ hind hδ, fixV_rho_three D hV hcard hZ hind hγ]
  constructor
  · intro h
    exact fixSub_injective (D.pre_injective h)
  · intro h
    have : fixSub δ = fixSub γ := by
      unfold fixSub
      congr 1
    rw [this]

include D in
theorem El_three (hV : ∀ v : V, v ^ 2 = 1) (hcard : Nat.card V = 16)
    (hZ : Z = ⊥) (hind : IsIndecompModule G) :
    ∀ a ∈ G, a ≠ 1 → a ^ 2 = 1 → ∃ E : Subgroup (MulAut V), E ≤ G ∧ Nat.card E = 4 ∧
      IsElemAbelian2 E ∧ IsEqFixGroup G a E := by
  intro a haG ha1 ha2
  obtain ⟨γ, hγ, rfl⟩ := D.exists_invol haG ha2 ha1
  have hS := isPlane_fixS hγ
  refine ⟨(BSsub (L3.fixS γ) hS).map D.rho, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨δ, -, rfl⟩
    exact D.rho_mem δ
  · rw [Subgroup.card_map_of_injective D.rho_injective]
    exact card_BSsub hS
  · refine ⟨?_, ?_⟩
    · rintro _ ⟨δ₁, h₁, rfl⟩ _ ⟨δ₂, h₂, rfl⟩
      rw [← map_mul, ← map_mul, (L3.BS_elem _ hS δ₁ h₁ δ₂ h₂).1]
    · rintro _ ⟨δ₁, h₁, rfl⟩
      rw [pow_two, ← map_mul, (L3.BS_elem _ hS δ₁ h₁ δ₁ h₁).2, map_one]
  · intro g
    constructor
    · rintro ⟨δ, hδ, rfl⟩
      refine ⟨D.rho_mem δ, ?_⟩
      by_cases hδ1 : δ = 1
      · left
        rw [hδ1, map_one]
      · right
        have hinv : L3.IsInvol δ := ⟨(L3.BS_elem _ hS δ hδ δ hδ).2, hδ1⟩
        refine ⟨?_, ?_⟩
        · rw [pow_two, ← map_mul, hinv.1, map_one]
        · rw [fixV_rho_eq_iff_three D hV hcard hZ hind hinv hγ]
          exact L3.BS_fixS _ hS δ hδ hδ1
    · rintro ⟨hgG, hg⟩
      obtain ⟨δ, rfl⟩ := D.exists_rho hgG
      by_cases hg1 : D.rho δ = 1
      · rw [hg1]
        exact Subgroup.one_mem _
      · rcases hg with h | ⟨hg2, hgfix⟩
        · exact absurd h hg1
        · have hinv : L3.IsInvol δ := by
            refine ⟨?_, fun h => hg1 (by rw [h, map_one])⟩
            apply D.rho_injective
            rw [map_mul, map_one, ← pow_two, hg2]
          have hfixeq := (fixV_rho_eq_iff_three D hV hcard hZ hind hinv hγ).1 hgfix
          refine ⟨δ, ?_, rfl⟩
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun v hv => ?_⟩
          rw [← hfixeq] at hv
          simp only [L3.fixS, Finset.mem_filter, Finset.mem_univ, true_and] at hv
          exact hv

include D in
theorem offHyp_three (hV : ∀ v : V, v ^ 2 = 1) (hcard : Nat.card V = 16)
    (hZ : Z = ⊥) (hind : IsIndecompModule G) : OffHyp G where
  card_four := hcard
  sq := hV
  FF := fun _ ha ha1 ha2 => card_fixV_involution_three D hV hcard hZ hind ha ha1 ha2
  E4 := fun _ hA hAel => D.elemAbelian_card_le_four hA hAel
  El := El_three D hV hcard hZ hind

include D in
theorem eqFix_eq_centSub_three (hV : ∀ v : V, v ^ 2 = 1) (hcard : Nat.card V = 16)
    (hZ : Z = ⊥) (hind : IsIndecompModule G)
    {a : MulAut V} (haG : a ∈ G) (ha1 : a ≠ 1) (ha2 : a ^ 2 = 1) {E : Subgroup (MulAut V)}
    (hE : IsEqFixGroup G a E) : E = G ⊓ centSub (fixV (Subgroup.zpowers a)) := by
  obtain ⟨γ, hγ, rfl⟩ := D.exists_invol haG ha2 ha1
  have hS := isPlane_fixS hγ
  have hF := fixV_rho_three D hV hcard hZ hind hγ
  ext g
  constructor
  · intro hg
    obtain ⟨hgG, hg'⟩ := (hE g).1 hg
    refine ⟨hgG, fun v hv => ?_⟩
    rcases hg' with rfl | ⟨hg2, hgfix⟩
    · rfl
    · rw [← hgfix] at hv
      exact mem_fixV_zpowers_iff.mp hv
  · rintro ⟨hgG, hgc⟩
    refine (hE g).2 ⟨hgG, ?_⟩
    by_cases hg1 : g = 1
    · exact Or.inl hg1
    · right
      obtain ⟨δ, rfl⟩ := D.exists_rho hgG
      have hBS : δ ∈ L3.BS (L3.fixS γ) := by
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun w hw => ?_⟩
        obtain ⟨u, hu⟩ := D.β_surj (Multiplicative.ofAdd w)
        have hupre : (u : V) ∈ fixV (Subgroup.zpowers (D.rho γ)) := by
          rw [hF, D.mem_pre]
          refine ⟨u.2, ?_⟩
          show Multiplicative.toAdd (D.β ⟨(u : V), u.2⟩) ∈ L3.fixS γ
          have : (⟨(u : V), u.2⟩ : ↥U) = u := rfl
          rw [this, hu]
          exact hw
        have h1 := hgc _ hupre
        have hmem : D.rho δ (u : V) ∈ U := D.inv_U _ (D.rho_mem δ) _ u.2
        have h2 := D.β_rho δ (u : V) u.2 hmem
        have h3 : (⟨D.rho δ (u : V), hmem⟩ : ↥U) = ⟨(u : V), u.2⟩ := Subtype.ext h1
        rw [h3] at h2
        have h4 : (⟨(u : V), u.2⟩ : ↥U) = u := rfl
        rw [h4, hu] at h2
        have := congrArg Multiplicative.toAdd h2
        exact this.symm
      have hδ1 : δ ≠ 1 := fun h => hg1 (by rw [h, map_one])
      have hinv : L3.IsInvol δ := ⟨(L3.BS_elem _ hS δ hBS δ hBS).2, hδ1⟩
      refine ⟨?_, ?_⟩
      · rw [pow_two, ← map_mul, hinv.1, map_one]
      · rw [fixV_rho_eq_iff_three D hV hcard hZ hind hinv hγ]
        exact L3.BS_fixS _ hS δ hBS hδ1

end Three

section Final

variable {G : Subgroup (MulAut V)}

theorem B4_8_3 (hV : ∀ v : V, v ^ 2 = 1) (hcard : Nat.card V = 16)
    (hnat : BinaryNaturalSL G (commV G) ⊥ 3 1) (hind : IsIndecompModule G) :
    (∃ B : Subgroup (MulAut V), IsAxisTransvGroup G B ∧
        {A | IsFFStarOffender G A} = {A | ∃ g ∈ G, A = B1.conjAut g B}) ∧
      qOf G = 1 ∧
      (∀ a ∈ G, a ≠ 1 → a ^ 2 = 1 →
        commV (Subgroup.zpowers a) = fixV (Subgroup.zpowers a) ∧
          rk (fixV (Subgroup.zpowers a)) = 2 ∧ fixV (Subgroup.zpowers a) ≤ commV G) := by
  obtain ⟨D⟩ := hnat.toL3Coord
  have H := offHyp_three D hV hcard rfl hind
  have ha₁ : D.rho L3.x12 ∈ G := D.rho_mem _
  have ha₁sq : D.rho L3.x12 ^ 2 = 1 := by
    rw [pow_two, ← map_mul, L3.x12_invol.1, map_one]
  have ha₁ne : D.rho L3.x12 ≠ 1 := by
    intro h
    apply L3.x12_invol.2
    apply D.rho_injective
    rw [h, map_one]
  have hGU := le_centQuot_three D hcard rfl
  have hFF : ∀ a ∈ G, a ≠ 1 → a ^ 2 = 1 →
      commV (Subgroup.zpowers a) = fixV (Subgroup.zpowers a) ∧
        rk (fixV (Subgroup.zpowers a)) = 2 ∧ fixV (Subgroup.zpowers a) ≤ commV G := by
    intro a ha ha1 ha2
    have hF := H.FF a ha ha1 ha2
    have hC : commV (Subgroup.zpowers a) = fixV (Subgroup.zpowers a) := by
      apply Subgroup.eq_of_le_of_card_ge (commV_zpowers_le_fixV_b4 hV ha2)
      have := card_commV_mul_card_fixV hV a
      rw [hF, hcard] at this
      omega
    refine ⟨hC, ?_, ?_⟩
    · rw [card_eq_two_pow hV (fixV (Subgroup.zpowers a))] at hF
      have : (2 : ℕ) ^ rk (fixV (Subgroup.zpowers a)) = 2 ^ 2 := by rw [hF]; norm_num
      exact Nat.pow_right_injective (le_refl 2) this
    · rw [← hC]
      unfold commV
      apply Subgroup.closure_mono
      rintro _ ⟨x, hx, v, rfl⟩
      exact ⟨x, (Subgroup.zpowers_le.mpr ha) hx, v, rfl⟩
  refine ⟨?_, H.qOf_eq_one ⟨_, ha₁, ha₁ne, ha₁sq⟩, hFF⟩
  obtain ⟨E₁, hE₁G, hE₁c, hE₁el, hE₁⟩ := H.El _ ha₁ ha₁ne ha₁sq
  have hA₁ : E₁ = G ⊓ centSub (fixV (Subgroup.zpowers (D.rho L3.x12))) :=
    eqFix_eq_centSub_three D hV hcard rfl hind ha₁ ha₁ne ha₁sq hE₁
  refine ⟨E₁, ⟨fixV (Subgroup.zpowers (D.rho L3.x12)), (hFF _ ha₁ ha₁ne ha₁sq).2.2,
    H.FF _ ha₁ ha₁ne ha₁sq, hA₁⟩, ?_⟩
  ext B
  constructor
  · intro hB
    obtain ⟨a, haG, ha1, ha2, hBa⟩ := (H.isFFStarOffender_iff_eqFix B).1 hB
    obtain ⟨g, hg, hgab⟩ := D.exists_conj ha₁ ha₁sq ha₁ne haG ha2 ha1
    exact ⟨g, hg, eqFix_conj hg hgab hE₁ hBa⟩
  · rintro ⟨g, hg, rfl⟩
    exact B1.isFFStarOffender_conjAut ((H.isFFStarOffender_iff_eqFix E₁).2
      ⟨_, ha₁, ha₁ne, ha₁sq, hE₁⟩) hg

end Final

end CFSG.Quasithin
