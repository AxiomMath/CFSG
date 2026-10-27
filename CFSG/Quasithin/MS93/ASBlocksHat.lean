module

public import CFSG.Quasithin.MS93.ASG2Natural
public import CFSG.Quasithin.EmptyFaithful.LRed6Hat
public import CFSG.Quasithin.Vol2.Ch12Sec2OrbitG2
public import CFSG.Quasithin.Background.SmithC27RTypeU33

public section

namespace CFSG.Quasithin.MS93

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

variable {G : Type} [Group G] [Finite G]

theorem isPerfect_autI {M T L : Subgroup G} (h : PUHyp M T L) (hV : IsElemAbelian 2 (Vq M L)) :
    Group.IsPerfect ↥(autI hV L) := by
  have hLN : L ≤ Subgroup.normalizer (Vq M L : Set G) :=
    h.L_le.trans (le_normalizer_Vq h.le_normalizer)
  have : Group.IsPerfect ↥L := Subgroup.isPerfect_iff.mpr h.perfect
  rw [← range_convHom hV L hLN]
  exact Group.IsPerfect.range _

omit [Finite G] in
theorem inf_centralizer_eq_bot_of_fixV {L V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hfix : fixV (autI hV L) = ⊥) : V ⊓ Subgroup.centralizer (L : Set G) = ⊥ := by
  refine eq_bot_iff.mpr fun v ⟨hvV, hvC⟩ => ?_
  have hmem : IntMod.mk hV ⟨v, hvV⟩ ∈ fixV (autI hV L) := by
    intro φ hφ
    obtain ⟨g, hg, rfl⟩ := (mem_autI hV).1 hφ
    apply IntMod.val_injective
    rw [convI_apply_val]
    show (g : G) * v * (g : G)⁻¹ = v
    rw [Subgroup.mem_centralizer_iff.mp hvC g hg, mul_inv_cancel_right]
  rw [hfix, Subgroup.mem_bot] at hmem
  rw [Subgroup.mem_bot]
  exact congrArg IntMod.val hmem

theorem isHatA6Block_of_case6 {M T L : Subgroup G} (h : PUHyp M T L) (h6 : MS93Case6 M L) :
    IsHatA6Block L := by
  obtain ⟨hVX, hV, h6⟩ := h6
  have hcard : Nat.card (IntMod (Vq M L) hV) = 2 ^ 6 := (LRed6.hat_conclusion h6).2
  have hHhat : IsHat ↥(autI hV L) ↥(alternatingGroup (Fin 6)) := by
    obtain ⟨K, hK, hKf, Γ₀, -, -, hhat, -, π, hπ⟩ := h6
    have hinj : Function.Injective π :=
      FFC.injective_of_faithful_sec (FFModel.nat_faithful _) hπ
    exact IsHat.of_mulEquiv (MulEquiv.ofBijective π ⟨hinj, hπ.1⟩) hhat
  obtain ⟨hfix, hirr⟩ := H13.hatA6SixIrreducible (IntMod (Vq M L) hV) IntMod.sq_eq_one hcard
    (autI hV L) (isPerfect_autI h hV) hHhat.2.1 hHhat.2.2
  have hinf := inf_centralizer_eq_bot_of_fixV hV hfix
  have hshort : IsShort2 L := by
    refine isShort2_of h hVX ?_ fun W hZW hWV hLW => ?_
    · rw [hinf]
      exact bot_lt_iff_ne_bot.mpr (vq_ne_bot h)
    · rw [hinf] at hZW ⊢
      exact eq_bot_or_eq_of_autI hV hirr hWV hLW
  refine ⟨hshort, IsHat.of_mulEquiv (quotEquivAutI h hVX hV).symm hHhat, ?_, ?_⟩
  · rw [blockU_eq h]
    exact hcard
  · rw [blockU_eq h]
    exact inf_centralizer_eq_pCoreOf h hVX

theorem isG2Block_of_case10_partial
    {M T L : Subgroup G} (h : PUHyp M T L) (h10 : MS93Case10 M L) :
    IsG2BlockPartial L := by
  obtain ⟨hVX, hV, h10⟩ := h10
  have hPSU : IsPSU 3 3 1 ↥(autI hV L) := by
    obtain ⟨K, _, _, hK, π, hπ⟩ := id h10
    have hK2 : Nat.card K = 2 := by rw [hK, pow_one]
    have : CharP K 2 := H13.charP_two_of_natCard_two hK2
    have hinj : Function.Injective π :=
      FFC.injective_of_faithful_sec (FFC.zornQ_faithful _ (Subgroup.commutator_le_self _)) hπ
    exact SmithC27.isPSU_of_equiv_g2Derived hK2 (MulEquiv.ofBijective π ⟨hinj, hπ.1⟩).symm
  have hcard : Nat.card (IntMod (Vq M L) hV) = 64 := by
    obtain ⟨e, -⟩ := B42U33.exists_equiv_of_g2NaturalDerived h10
    rw [Nat.card_congr e.toEquiv, H13.card_ModQ]
  obtain ⟨hlen, hsep⟩ := H13.Orbit.orbitG2Natural (IntMod (Vq M L) hV) (autI hV L) h10
  have htr : ∀ v w : IntMod (Vq M L) hV, v ≠ 1 → w ≠ 1 → ∃ φ ∈ autI hV L, φ v = w := by
    intro v w hv hw
    refine hsep v w hv hw ?_
    have h1 := hlen v hv
    have h2 := hlen w hw
    simp only [List.mem_singleton] at h1 h2
    rw [h1, h2]
  have hirr : ∀ W : Subgroup (IntMod (Vq M L) hV), (∀ φ ∈ autI hV L, ∀ w ∈ W, φ w ∈ W) →
      W = ⊥ ∨ W = ⊤ := by
    intro W hW
    by_cases hbot : W = ⊥
    · exact Or.inl hbot
    right
    obtain ⟨⟨w, hwW⟩, hw1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hbot
    have hw1' : w ≠ 1 := fun h1 => hw1 (Subtype.ext h1)
    refine eq_top_iff.mpr fun v _ => ?_
    by_cases hv : v = 1
    · rw [hv]
      exact W.one_mem
    obtain ⟨φ, hφ, rfl⟩ := htr w v hw1' hv
    exact hW φ hφ w hwW
  have hfix : fixV (autI hV L) = ⊥ := by
    refine eq_bot_iff.mpr fun v hv => ?_
    rw [Subgroup.mem_bot]
    by_contra hv1
    obtain ⟨w, hw1, hwv⟩ : ∃ w : IntMod (Vq M L) hV, w ≠ 1 ∧ w ≠ v := by
      by_contra hcon
      push Not at hcon
      have hsub : (Set.univ : Set (IntMod (Vq M L) hV)) ⊆ {1, v} := fun w _ => by
        by_cases hw : w = 1
        · exact Or.inl hw
        · exact Or.inr (hcon w hw)
      have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
      rw [Set.ncard_univ, hcard] at hle
      have := Set.ncard_insert_le 1 ({v} : Set (IntMod (Vq M L) hV))
      rw [Set.ncard_singleton] at this
      omega
    obtain ⟨φ, hφ, hφv⟩ := htr v w hv1 hw1
    exact hwv (hφv ▸ hv φ hφ)
  have hinf := inf_centralizer_eq_bot_of_fixV hV hfix
  have hshort : IsShort2 L := by
    refine isShort2_of h hVX ?_ fun W hZW hWV hLW => ?_
    · rw [hinf]
      exact bot_lt_iff_ne_bot.mpr (vq_ne_bot h)
    · rw [hinf] at hZW ⊢
      exact eq_bot_or_eq_of_autI hV hirr hWV hLW
  refine ⟨hshort, IsPSU.of_mulEquiv (quotEquivAutI h hVX hV).symm hPSU, ?_⟩
  rw [blockZ_eq h, blockU_eq h, hinf, Subgroup.bot_subgroupOf, Subgroup.index_bot]
  exact hcard

theorem isG2Block_of_case10
    {M T L : Subgroup G} (h : PUHyp M T L) (h10 : MS93Case10 M L) :
    IsG2Block L := by
  obtain ⟨hshort, hquotient, hindex⟩ := isG2Block_of_case10_partial h h10
  exact ⟨hshort, hquotient, hindex, isG2BlockNatural_of_case10 h h10⟩

end CFSG.Quasithin.MS93
