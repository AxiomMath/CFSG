module

public import CFSG.Quasithin.Background.B4L3Key
public import CFSG.Quasithin.Background.B4L3Off
public import CFSG.Quasithin.Background.B4L3Syl
public import CFSG.Quasithin.Background.B4L3FactA

public section

namespace CFSG.Quasithin

variable {V : Type*} [CommGroup V] [Finite V]

@[expose] def IsCenterTransvGroup (G A : Subgroup (MulAut V)) : Prop :=
  ∃ C : Subgroup V, fixV G ≤ C ∧ Nat.card C = 4 ∧ A = G ⊓ centQuot C

@[expose] def ASsub (c : L3.Vec) (hc : c ≠ 0) : Subgroup L3.Γ where
  carrier := {δ | δ ∈ L3.AS {0, c}}
  one_mem' := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun v => ?_⟩
    simp [L3.act_one]
  mul_mem' := fun {x y} hx hy => L3.AS_mul c hc x hx y hy
  inv_mem' := fun {x} hx => by
    have h := (L3.AS_elem c hc x hx x hx).2
    have : x⁻¹ = x := inv_eq_of_mul_eq_one_right h
    rw [this]
    exact hx

theorem mem_ASsub {c : L3.Vec} {hc : c ≠ 0} {δ : L3.Γ} : δ ∈ ASsub c hc ↔ δ ∈ L3.AS {0, c} :=
  Iff.rfl

theorem card_ASsub {c : L3.Vec} (hc : c ≠ 0) : Nat.card (ASsub c hc) = 4 := by
  rw [← L3.AS_card c hc, ← Fintype.card_coe, ← Nat.card_eq_fintype_card]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun x => Iff.rfl)

section Two

variable {G : Subgroup (MulAut V)} {U Z : Subgroup V} (D : L3Data G U Z)

include D in
theorem fixV_rho_two (hV : ∀ v : V, v ^ 2 = 1) (hcard : Nat.card V = 16)
    (hU : U = ⊤) (hZ : Z = fixV G) (hind : IsIndecompModule G)
    {δ : L3.Γ} (hδ : L3.IsInvol δ) {c : L3.Vec} (hc : c ≠ 0) (hcim : L3.cim δ = {0, c}) :
    fixV (Subgroup.zpowers (D.rho δ)) = D.pre (Zc c) := by
  have haG : D.rho δ ∈ G := D.rho_mem δ
  have ha2 : D.rho δ ^ 2 = 1 := by rw [pow_two, ← map_mul, hδ.1, map_one]
  have ha1 : D.rho δ ≠ 1 := by
    intro h
    apply hδ.2
    apply D.rho_injective
    rw [h, map_one]
  have hF := card_fixV_involution_two D hV hcard hU hZ hind haG ha1 ha2
  have hCF : commV (Subgroup.zpowers (D.rho δ)) = fixV (Subgroup.zpowers (D.rho δ)) := by
    apply Subgroup.eq_of_le_of_card_ge (commV_zpowers_le_fixV_b4 hV ha2)
    have := card_commV_mul_card_fixV hV (D.rho δ)
    rw [hF, hcard] at this
    omega
  have hU8 := D.card_U
  subst hU
  rw [Subgroup.card_top, hcard] at hU8
  have hZ2 : Nat.card Z = 2 := by omega
  have hle : fixV (Subgroup.zpowers (D.rho δ)) ≤ D.pre (Zc c) := by
    intro v hv
    rw [← hCF, commV_zpowers_eq_map] at hv
    obtain ⟨v', -, rfl⟩ := hv
    rw [D.mem_pre]
    have hv'U : v' ∈ (⊤ : Subgroup V) := Subgroup.mem_top v'
    have hxU : commHom (D.rho δ) v' ∈ (⊤ : Subgroup V) := Subgroup.mem_top _
    refine ⟨hxU, ?_⟩
    have hmem : D.rho δ v' ∈ (⊤ : Subgroup V) := Subgroup.mem_top _
    have h1 : (⟨commHom (D.rho δ) v', hxU⟩ : ↥(⊤ : Subgroup V)) =
        ⟨D.rho δ v', hmem⟩ * ⟨v', hv'U⟩⁻¹ := rfl
    rw [h1, map_mul, map_inv, D.β_rho δ v' hv'U hmem]
    have hmem2 : L3.act δ (Multiplicative.toAdd (D.β ⟨v', hv'U⟩)) -
        Multiplicative.toAdd (D.β ⟨v', hv'U⟩) ∈ ({0, c} : Finset L3.Vec) := by
      rw [← hcim]
      exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
    have hx : Multiplicative.ofAdd (L3.act δ (Multiplicative.toAdd (D.β ⟨v', hv'U⟩))) *
        (D.β ⟨v', hv'U⟩)⁻¹ = Multiplicative.ofAdd (L3.act δ (Multiplicative.toAdd (D.β ⟨v', hv'U⟩)) -
          Multiplicative.toAdd (D.β ⟨v', hv'U⟩)) := by
      rw [ofAdd_sub, div_eq_mul_inv]
      rfl
    rw [hx]
    exact hmem2
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [D.card_pre, hZ2, card_Zc hc, hF]

theorem pair_eq_of_ne {c c' : L3.Vec} (hc : c ≠ 0) (h : ({0, c} : Finset L3.Vec) = {0, c'}) :
    c = c' := by
  have : c ∈ ({0, c'} : Finset L3.Vec) := by rw [← h]; simp
  simp only [Finset.mem_insert, Finset.mem_singleton] at this
  rcases this with h0 | h0
  · exact absurd h0 hc
  · exact h0

include D in
theorem fixV_rho_eq_iff_two (hV : ∀ v : V, v ^ 2 = 1) (hcard : Nat.card V = 16)
    (hU : U = ⊤) (hZ : Z = fixV G) (hind : IsIndecompModule G)
    {δ γ : L3.Γ} (hδ : L3.IsInvol δ) (hγ : L3.IsInvol γ) :
    fixV (Subgroup.zpowers (D.rho δ)) = fixV (Subgroup.zpowers (D.rho γ)) ↔
      L3.cim δ = L3.cim γ := by
  obtain ⟨cδ, hcδ0, hcδ⟩ := L3.invol_center δ hδ
  obtain ⟨cγ, hcγ0, hcγ⟩ := L3.invol_center γ hγ
  rw [fixV_rho_two D hV hcard hU hZ hind hδ hcδ0 hcδ,
    fixV_rho_two D hV hcard hU hZ hind hγ hcγ0 hcγ]
  constructor
  · intro h
    have h1 := D.pre_injective h
    have hmem : Multiplicative.ofAdd cδ ∈ Zc cγ := by
      rw [← h1]
      show cδ ∈ ({0, cδ} : Finset L3.Vec)
      simp
    have h2 : cδ ∈ ({0, cγ} : Finset L3.Vec) := hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at h2
    rcases h2 with h0 | h0
    · exact absurd h0 hcδ0
    · rw [hcδ, hcγ, h0]
  · intro h
    rw [hcδ, hcγ] at h
    rw [pair_eq_of_ne hcδ0 h]

include D in
theorem El_two (hV : ∀ v : V, v ^ 2 = 1) (hcard : Nat.card V = 16)
    (hU : U = ⊤) (hZ : Z = fixV G) (hind : IsIndecompModule G) :
    ∀ a ∈ G, a ≠ 1 → a ^ 2 = 1 → ∃ E : Subgroup (MulAut V), E ≤ G ∧ Nat.card E = 4 ∧
      IsElemAbelian2 E ∧ IsEqFixGroup G a E := by
  intro a haG ha1 ha2
  obtain ⟨γ, hγ, rfl⟩ := D.exists_invol haG ha2 ha1
  obtain ⟨c, hc0, hcim⟩ := L3.invol_center γ hγ
  refine ⟨(ASsub c hc0).map D.rho, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨δ, -, rfl⟩
    exact D.rho_mem δ
  · rw [Subgroup.card_map_of_injective D.rho_injective]
    exact card_ASsub hc0
  · refine ⟨?_, ?_⟩
    · rintro _ ⟨δ₁, h₁, rfl⟩ _ ⟨δ₂, h₂, rfl⟩
      rw [← map_mul, ← map_mul, (L3.AS_elem c hc0 δ₁ h₁ δ₂ h₂).1]
    · rintro _ ⟨δ₁, h₁, rfl⟩
      rw [pow_two, ← map_mul, (L3.AS_elem c hc0 δ₁ h₁ δ₁ h₁).2, map_one]
  · intro g
    constructor
    · rintro ⟨δ, hδ, rfl⟩
      refine ⟨D.rho_mem δ, ?_⟩
      by_cases hδ1 : δ = 1
      · left
        rw [hδ1, map_one]
      · right
        have hinv : L3.IsInvol δ := ⟨(L3.AS_elem c hc0 δ hδ δ hδ).2, hδ1⟩
        refine ⟨?_, ?_⟩
        · rw [pow_two, ← map_mul, hinv.1, map_one]
        · rw [fixV_rho_eq_iff_two D hV hcard hU hZ hind hinv hγ,
            L3.AS_cim c hc0 δ hδ hδ1, hcim]
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
          have hcimeq := (fixV_rho_eq_iff_two D hV hcard hU hZ hind hinv hγ).1 hgfix
          refine ⟨δ, ?_, rfl⟩
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun v => ?_⟩
          have : L3.act δ v - v ∈ L3.cim δ := Finset.mem_image_of_mem _ (Finset.mem_univ _)
          rw [hcimeq, hcim] at this
          exact this

include D in
theorem offHyp_two (hV : ∀ v : V, v ^ 2 = 1) (hcard : Nat.card V = 16)
    (hU : U = ⊤) (hZ : Z = fixV G) (hind : IsIndecompModule G) : OffHyp G where
  card_four := hcard
  sq := hV
  FF := fun _ ha ha1 ha2 => card_fixV_involution_two D hV hcard hU hZ hind ha ha1 ha2
  E4 := fun _ hA hAel => D.elemAbelian_card_le_four hA hAel
  El := El_two D hV hcard hU hZ hind

include D in
theorem eqFix_eq_centQuot_two (hV : ∀ v : V, v ^ 2 = 1) (hcard : Nat.card V = 16)
    (hU : U = ⊤) (hZ : Z = fixV G) (hind : IsIndecompModule G)
    {a : MulAut V} (haG : a ∈ G) (ha1 : a ≠ 1) (ha2 : a ^ 2 = 1) {E : Subgroup (MulAut V)}
    (hE : IsEqFixGroup G a E) : E = G ⊓ centQuot (fixV (Subgroup.zpowers a)) := by
  obtain ⟨γ, hγ, rfl⟩ := D.exists_invol haG ha2 ha1
  obtain ⟨c, hc0, hcim⟩ := L3.invol_center γ hγ
  have hF := fixV_rho_two D hV hcard hU hZ hind hγ hc0 hcim
  ext g
  constructor
  · intro hg
    obtain ⟨hgG, hg'⟩ := (hE g).1 hg
    refine ⟨hgG, fun v => ?_⟩
    rcases hg' with rfl | ⟨hg2, hgfix⟩
    · simp
    · rw [← hgfix]
      exact commV_zpowers_le_fixV_b4 hV hg2 (commHom_mem_commV g v)
  · rintro ⟨hgG, hgc⟩
    refine (hE g).2 ⟨hgG, ?_⟩
    by_cases hg1 : g = 1
    · exact Or.inl hg1
    · right
      obtain ⟨δ, rfl⟩ := D.exists_rho hgG
      have hAS : δ ∈ L3.AS {0, c} := by
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun w => ?_⟩
        obtain ⟨u, hu⟩ := D.β_surj (Multiplicative.ofAdd w)
        have h1 := hgc (u : V)
        rw [hF, D.mem_pre] at h1
        obtain ⟨hx, hxmem⟩ := h1
        have hmem : D.rho δ (u : V) ∈ U := D.inv_U _ (D.rho_mem δ) _ u.2
        rw [D.β_comm δ u hmem hx, hu] at hxmem
        exact hxmem
      have hδ1 : δ ≠ 1 := fun h => hg1 (by rw [h, map_one])
      have hinv : L3.IsInvol δ := ⟨(L3.AS_elem c hc0 δ hAS δ hAS).2, hδ1⟩
      refine ⟨?_, ?_⟩
      · rw [pow_two, ← map_mul, hinv.1, map_one]
      · rw [fixV_rho_eq_iff_two D hV hcard hU hZ hind hinv hγ,
          L3.AS_cim c hc0 δ hAS hδ1, hcim]

end Two

section Final

variable {G : Subgroup (MulAut V)}

theorem B4_8_2 (hV : ∀ v : V, v ^ 2 = 1) (hcard : Nat.card V = 16)
    (hnat : BinaryNaturalSL G ⊤ (fixV G) 3 1) (hind : IsIndecompModule G) :
    (∃ A : Subgroup (MulAut V), IsCenterTransvGroup G A ∧
        {B | IsFFStarOffender G B} = {B | ∃ g ∈ G, B = B1.conjAut g A}) ∧
      qOf G = 1 ∧
      (∀ T : Subgroup (MulAut V), CFSG.QuasithinUnique.IsSylowTwoOf T G → fixV T = fixV G) ∧
      (∀ a ∈ G, a ≠ 1 → a ^ 2 = 1 →
        commV (Subgroup.zpowers a) = fixV (Subgroup.zpowers a) ∧
          rk (fixV (Subgroup.zpowers a)) = 2) := by
  obtain ⟨D⟩ := hnat.toL3Coord
  have H := offHyp_two D hV hcard rfl rfl hind
  have ha₁ : D.rho L3.x12 ∈ G := D.rho_mem _
  have ha₁sq : D.rho L3.x12 ^ 2 = 1 := by
    rw [pow_two, ← map_mul, L3.x12_invol.1, map_one]
  have ha₁ne : D.rho L3.x12 ≠ 1 := by
    intro h
    apply L3.x12_invol.2
    apply D.rho_injective
    rw [h, map_one]
  have hFF : ∀ a ∈ G, a ≠ 1 → a ^ 2 = 1 →
      commV (Subgroup.zpowers a) = fixV (Subgroup.zpowers a) ∧
        rk (fixV (Subgroup.zpowers a)) = 2 := by
    intro a ha ha1 ha2
    have hF := H.FF a ha ha1 ha2
    refine ⟨?_, ?_⟩
    · apply Subgroup.eq_of_le_of_card_ge (commV_zpowers_le_fixV_b4 hV ha2)
      have := card_commV_mul_card_fixV hV a
      rw [hF, hcard] at this
      omega
    · rw [card_eq_two_pow hV (fixV (Subgroup.zpowers a))] at hF
      have : (2 : ℕ) ^ rk (fixV (Subgroup.zpowers a)) = 2 ^ 2 := by rw [hF]; norm_num
      exact Nat.pow_right_injective (le_refl 2) this
  refine ⟨?_, H.qOf_eq_one ⟨_, ha₁, ha₁ne, ha₁sq⟩, ?_, hFF⟩
  · obtain ⟨E₁, hE₁G, hE₁c, hE₁el, hE₁⟩ := H.El _ ha₁ ha₁ne ha₁sq
    have hA₁ : E₁ = G ⊓ centQuot (fixV (Subgroup.zpowers (D.rho L3.x12))) :=
      eqFix_eq_centQuot_two D hV hcard rfl rfl hind ha₁ ha₁ne ha₁sq hE₁
    refine ⟨E₁, ⟨fixV (Subgroup.zpowers (D.rho L3.x12)), ?_, H.FF _ ha₁ ha₁ne ha₁sq, hA₁⟩, ?_⟩
    · exact B1.fixV_le_fixV (Subgroup.zpowers_le.mpr ha₁)
    · ext B
      constructor
      · intro hB
        obtain ⟨a, haG, ha1, ha2, hBa⟩ := (H.isFFStarOffender_iff_eqFix B).1 hB
        obtain ⟨g, hg, hgab⟩ := D.exists_conj ha₁ ha₁sq ha₁ne haG ha2 ha1
        exact ⟨g, hg, eqFix_conj hg hgab hE₁ hBa⟩
      · rintro ⟨g, hg, rfl⟩
        exact B1.isFFStarOffender_conjAut ((H.isFFStarOffender_iff_eqFix E₁).2
          ⟨_, ha₁, ha₁ne, ha₁sq, hE₁⟩) hg
  · intro T hT
    obtain ⟨γ, δ, hγ, hδ, hγT, hδT, hne⟩ := D.exists_two_centers_in_sylow hT
    obtain ⟨cγ, hcγ0, hcγ⟩ := L3.invol_center γ hγ
    obtain ⟨cδ, hcδ0, hcδ⟩ := L3.invol_center δ hδ
    have hcne : cγ ≠ cδ := fun h => hne (by rw [hcγ, hcδ, h])
    apply le_antisymm
    · intro v hv
      have h1 : v ∈ fixV (Subgroup.zpowers (D.rho γ)) :=
        B1.fixV_le_fixV (Subgroup.zpowers_le.mpr hγT) hv
      have h2 : v ∈ fixV (Subgroup.zpowers (D.rho δ)) :=
        B1.fixV_le_fixV (Subgroup.zpowers_le.mpr hδT) hv
      rw [fixV_rho_two D hV hcard rfl rfl hind hγ hcγ0 hcγ, D.mem_pre] at h1
      rw [fixV_rho_two D hV hcard rfl rfl hind hδ hcδ0 hcδ, D.mem_pre] at h2
      obtain ⟨hx, h1'⟩ := h1
      obtain ⟨hx', h2'⟩ := h2
      have hβ : D.β ⟨v, hx⟩ = 1 := by
        have a1 : Multiplicative.toAdd (D.β ⟨v, hx⟩) ∈ ({0, cγ} : Finset L3.Vec) := h1'
        have a2 : Multiplicative.toAdd (D.β ⟨v, hx'⟩) ∈ ({0, cδ} : Finset L3.Vec) := h2'
        simp only [Finset.mem_insert, Finset.mem_singleton] at a1 a2
        rcases a1 with h0 | h0
        · exact Multiplicative.toAdd.injective h0
        · rcases a2 with h0' | h0'
          · exact Multiplicative.toAdd.injective h0'
          · exact absurd (h0.symm.trans h0') hcne
      exact (D.ker_β ⟨v, hx⟩).1 hβ
    · exact B1.fixV_le_fixV hT.1

end Final


end CFSG.Quasithin
