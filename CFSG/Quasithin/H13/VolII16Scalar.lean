module

public import CFSG.Quasithin.H13.VolII16Central
public import CFSG.Quasithin.H13.VolII16Restrict

public section

namespace CFSG.Quasithin.H13.VolI

open CFSG.Quasithin Subgroup

section Scalar

variable {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]

theorem top_mk_injective {M : Type*} [Group M] {m m' : ↥(⊤ : Subgroup M)}
    (h : (QuotientGroup.mk m : ↥(⊤ : Subgroup M) ⧸ (⊥ : Subgroup M).subgroupOf ⊤) =
      QuotientGroup.mk m') : (m : M) = m' := by
  have h1 := (QuotientGroup.eq (s := (⊥ : Subgroup M).subgroupOf ⊤) (a := m) (b := m')).1 h
  rw [mem_subgroupOf, mem_bot, coe_mul, coe_inv, inv_mul_eq_one] at h1
  exact h1

theorem nat_eq_bot_of_central_scalar {Γ : Subgroup (Matrix.GeneralLinearGroup ι K)} {g₀ : ↥Γ}
    (hg₀ : ∀ g : ↥Γ, g * g₀ = g₀ * g) {c : K} (hc : c ≠ 1)
    (hg₀c : ((g₀ : Matrix.GeneralLinearGroup ι K) : Matrix ι ι K) = c • 1) {k : ℕ} (hk : Odd k)
    (hg₀k : g₀ ^ k = 1) {W : Type} [CommGroup W] [Finite W] (hW2 : ∀ w : W, w ^ 2 = 1)
    {H : Subgroup (MulAut W)} {Z : Subgroup W} (hZ : Z ≤ fixV H) (hcomm : commV H = ⊤)
    (h : (FFModel.nat Γ).Realizes H ⊤ Z) : Z = ⊥ := by
  obtain ⟨π, hπs, -, -, -, -, -, -, β, hβs, hβk, hβe⟩ := h
  let π' : ↥Γ →* ↥H := π
  refine eq_bot_of_central_fpf (t := ((π' g₀ : ↥H) : MulAut W)) hW2 hZ hcomm (π' g₀).2
    (fun x hx => ?_) hk ?_ (fun w hw => ?_)
  · obtain ⟨γ₀, hγ⟩ := hπs ⟨x, hx⟩
    let γ : ↥Γ := γ₀
    have h1 : π' (γ * g₀) = π' (g₀ * γ) := by rw [hg₀ γ]
    rw [map_mul, map_mul] at h1
    have h2 := congrArg Subtype.val h1
    rw [Subgroup.coe_mul, Subgroup.coe_mul] at h2
    have hγ' : ((π' γ : ↥H) : MulAut W) = x := congrArg Subtype.val hγ
    rw [hγ'] at h2
    exact h2
  · rw [← Subgroup.coe_pow, ← map_pow, hg₀k, map_one]
    rfl
  · obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (β ⟨w, mem_top w⟩)
    have h1 := hβe g₀ ⟨w, mem_top w⟩ m (mem_top _) (mem_top _) hm.symm
    have hw' : (⟨((π g₀ : ↥H) : MulAut W) w, mem_top _⟩ : ↥(⊤ : Subgroup W)) =
        ⟨w, mem_top w⟩ := Subtype.ext hw
    rw [hw', ← hm] at h1
    let m₀ : ↥(⊤ : Subgroup (Multiplicative (ι → K))) := m
    have h2 : (m₀ : Multiplicative (ι → K)) = natAct Γ g₀ m₀ :=
      top_mk_injective (M := Multiplicative (ι → K)) h1
    have h3 : Multiplicative.toAdd (m₀ : Multiplicative (ι → K)) =
        c • Multiplicative.toAdd (m₀ : Multiplicative (ι → K)) := by
      have h8 : Multiplicative.toAdd (natAct Γ g₀ (m₀ : Multiplicative (ι → K))) =
          c • Multiplicative.toAdd (m₀ : Multiplicative (ι → K)) := by
        show Matrix.mulVec ((g₀ : Matrix.GeneralLinearGroup ι K) : Matrix ι ι K) _ = _
        rw [hg₀c, Matrix.smul_mulVec, Matrix.one_mulVec]
      exact (congrArg Multiplicative.toAdd h2).trans h8
    have h5 : Multiplicative.toAdd (m₀ : Multiplicative (ι → K)) = 0 := by
      have h6 : (c - 1) • Multiplicative.toAdd (m₀ : Multiplicative (ι → K)) = 0 := by
        rw [sub_smul, one_smul, ← h3, sub_self]
      exact (smul_eq_zero.1 h6).resolve_left (sub_ne_zero.2 hc)
    have hm1 : m₀ = 1 := Subtype.ext (Multiplicative.toAdd.injective (by rw [h5]; rfl))
    have hm1' : m = 1 := hm1
    have h7 : β ⟨w, mem_top w⟩ = 1 := by rw [← hm, hm1', QuotientGroup.mk_one]
    exact (hβk _).1 h7

end Scalar

theorem tripleA6Six_eq_bot {V : Type} [CommGroup V] [Finite V] (hV2 : ∀ v : V, v ^ 2 = 1)
    {L : Subgroup (MulAut V)} (hI : commV L ∈ IrrPlus L ⊤)
    (h : TripleA6Six L (commV L) (fixV L ⊓ commV L)) : fixV L ⊓ commV L = ⊥ := by
  obtain ⟨K, _, _, Γ₀, -, -, hhat, hsc, hR⟩ := h
  have hc3 : Nat.card (center ↥Γ₀) = 3 := hhat.2.1
  have hne : center ↥Γ₀ ≠ ⊥ := fun h0 => by
    rw [h0, card_bot] at hc3
    omega
  obtain ⟨⟨g₀, hg₀c⟩, hg₀1⟩ := (ne_bot_iff_exists_ne_one).1 hne
  have hg₀3 : g₀ ^ 3 = 1 := by
    have h1 : (⟨g₀, hg₀c⟩ : ↥(center ↥Γ₀)) ^ Nat.card ↥(center ↥Γ₀) = 1 := pow_card_eq_one'
    rw [hc3] at h1
    exact congrArg Subtype.val h1
  obtain ⟨c, hc⟩ := hsc g₀ hg₀c
  have hc1 : c ≠ 1 := by
    rintro rfl
    apply hg₀1
    apply Subtype.ext
    apply Subtype.ext
    apply Units.ext
    rw [hc, one_smul]
    rfl
  exact eq_bot_of_restrict _ (fun W _ _ hW2 H Z hZ hcomm hRW =>
    nat_eq_bot_of_central_scalar (fun g => (mem_center_iff.1 hg₀c g)) hc1 hc ⟨1, rfl⟩ hg₀3 hW2
      hZ hcomm hRW) hV2 hI hR

end CFSG.Quasithin.H13.VolI
