module

public import CFSG.LocalAnalysis.StandardType.GGK0LCDefs
public import CFSG.LocalAnalysis.StandardType.GGK0LCAct
public import CFSG.LocalAnalysis.StandardType.GGK0LCAffine
public import CFSG.LocalAnalysis.StandardType.GGK0LCReflect
public import CFSG.LocalAnalysis.StandardType.GGK0LCNeg

public section

namespace CFSG.StandardType.GGK0LC

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

namespace KacPt

private theorem lk0xlcdesc_act_invol {τ : Tag} (K : KacPt τ) {r : WeylGroup τ}
    (hr : r ∈ K.stab) (hr2 : r * r = 1) (a : AffPair τ) : K.act r (K.act r a) = a := by
  rw [← act_mul K hr hr a, hr2, act_one K a]

private theorem lk0xlcdesc_act_injective {τ : Tag} (K : KacPt τ) {r : WeylGroup τ}
    (hr : r ∈ K.stab) (hr2 : r * r = 1) : Function.Injective (K.act r) := fun a b h => by
  have h' := congrArg (K.act r) h
  rwa [lk0xlcdesc_act_invol K hr hr2 a, lk0xlcdesc_act_invol K hr hr2 b] at h'

theorem ncard_inv_mul
    {τ : Tag} (hT : KacBox τ) (K : KacPt τ) {z r : WeylGroup τ}
    (hz : z ∈ K.stab) (hr : r ∈ K.stab) {a₀ : AffPair τ} (ha₀ : IsRoot τ a₀.1)
    (hp0 : AffPos a₀) (hneg : AffNeg (K.act z a₀)) (hr1 : K.act r a₀ = -a₀) (hr2 : r * r = 1)
    (hr3 : ∀ a : AffPair τ, IsRoot τ a.1 → AffPos a → a ≠ a₀ → AffPos (K.act r a)) :
    (K.inv (z * r)).ncard + 1 = (K.inv z).ncard := by
  have hinvol : ∀ b : AffPair τ, K.act r (K.act r b) = b :=
    fun b => lk0xlcdesc_act_invol K hr hr2 b
  have hinj : Function.Injective (K.act r) := lk0xlcdesc_act_injective K hr hr2
  have ha₀mem : a₀ ∈ K.inv z := ⟨ha₀, hp0, hneg⟩
  have hact₀ : K.act (z * r) a₀ = -(K.act z a₀) := by
    rw [act_mul K hz hr a₀, hr1, act_neg K hz]
  have hpos₀ : AffPos (K.act (z * r) a₀) := by
    rw [hact₀]
    exact (affNeg_iff_affPos_neg (K.act z a₀)).mp hneg
  have hroot₀ : IsRoot τ (K.act (z * r) a₀).1 := IsRoot.smul ha₀ (z * r)
  have ha₀notmem : a₀ ∉ K.inv (z * r) := fun hmem =>
    (affPos_iff_not_affNeg hroot₀).mp hpos₀ hmem.2.2
  have himage : K.inv (z * r) = K.act r '' (K.inv z \ {a₀}) := by
    ext a
    constructor
    · rintro ⟨haroot, hapos, haneg⟩
      have ha_ne : a ≠ a₀ := fun h => ha₀notmem (h ▸ ⟨haroot, hapos, haneg⟩)
      refine ⟨K.act r a, ⟨⟨IsRoot.smul haroot r, hr3 a haroot hapos ha_ne, ?_⟩, ?_⟩, ?_⟩
      · have h' := haneg
        rw [act_mul K hz hr a] at h'
        exact h'
      · intro hb
        have hna₀ : ¬ AffNeg a₀ := (affPos_iff_not_affNeg ha₀).mp hp0
        have heq : a = -a₀ := by
          calc a = K.act r (K.act r a) := (hinvol a).symm
            _ = K.act r a₀ := by rw [hb]
            _ = -a₀ := hr1
        exact hna₀ ((affNeg_iff_affPos_neg a₀).mpr (heq ▸ hapos))
      · exact hinvol a
    · rintro ⟨b, hbmem, hba⟩
      obtain ⟨⟨hbroot, hbpos, hbneg⟩, hb_ne⟩ := hbmem
      rw [← hba]
      refine ⟨IsRoot.smul hbroot r, hr3 b hbroot hbpos hb_ne, ?_⟩
      have h' : K.act (z * r) (K.act r b) = K.act z b := by
        rw [act_mul K hz hr (K.act r b), hinvol b]
      rw [h']
      exact hbneg
  rw [himage, Set.ncard_image_of_injective _ hinj]
  exact Set.ncard_diff_singleton_add_one ha₀mem (inv_finite hT K hz)

theorem stab_le_refl_of_free
    {τ : Tag} (hT : KacBox τ) (K : KacPt τ)
    (h0 : ∀ z ∈ K.stab, K.inv z = ∅ → z = 1) : K.stab ≤ K.refl := by
  intro z hz
  let P : ℕ → Prop := fun n => ∀ z : WeylGroup τ, z ∈ K.stab → (K.inv z).ncard = n → z ∈ K.refl
  have hP : ∀ N, P N := fun N =>
    Nat.strong_induction_on N (fun n ih => by
      intro z hz hn
      by_cases hempty : K.inv z = ∅
      · rw [h0 z hz hempty]
        exact K.refl.one_mem
      · have hne : (K.inv z).Nonempty := Set.nonempty_iff_ne_empty.mpr hempty
        rcases exists_neg_simple hT K hz hne with ⟨j, hj⟩ | hext
        · have hj0 : K.s j = 0 := neg_node_zero hT K hz j hj
          obtain ⟨r, hr_mem, hr1, hr2, hr3⟩ := exists_refl_node K j hj0
          have hrstab : r ∈ K.stab := refl_le_stab K hr_mem
          have hzr : z * r ∈ K.stab := K.stab.mul_mem hz hrstab
          have hp0 : AffPos (simpleAff j) := by simp [AffPos, simpleAff]
          have ha₀ : IsRoot τ (simpleAff j).1 := isRoot_single τ j
          have hdes := ncard_inv_mul hT K hz hrstab ha₀ hp0 hj hr1 hr2 hr3
          have hlt : (K.inv (z * r)).ncard < n := by omega
          have hzr_refl : z * r ∈ K.refl := ih _ hlt (z * r) hzr rfl
          have hz_eq : z = (z * r) * r := by rw [mul_assoc, hr2, mul_one]
          rw [hz_eq]
          exact K.refl.mul_mem hzr_refl hr_mem
        · have h0s : K.s0 = 0 := neg_ext_zero hT K hz hext
          obtain ⟨r, hr_mem, hr1, hr2, hr3⟩ := exists_refl_ext hT K h0s
          have hrstab : r ∈ K.stab := refl_le_stab K hr_mem
          have hzr : z * r ∈ K.stab := K.stab.mul_mem hz hrstab
          have hp0 : AffPos (extAff τ) := by simp [AffPos, extAff]
          have ha₀ : IsRoot τ (extAff τ).1 := IsRoot.neg hT.2.1
          have hdes := ncard_inv_mul hT K hz hrstab ha₀ hp0 hext hr1 hr2 hr3
          have hlt : (K.inv (z * r)).ncard < n := by omega
          have hzr_refl : z * r ∈ K.refl := ih _ hlt (z * r) hzr rfl
          have hz_eq : z = (z * r) * r := by rw [mul_assoc, hr2, mul_one]
          rw [hz_eq]
          exact K.refl.mul_mem hzr_refl hr_mem)
  exact hP (K.inv z).ncard z hz rfl

end KacPt

end CFSG.StandardType.GGK0LC

end
