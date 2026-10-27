module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC13BCASixIrr

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.WeakClosure81

variable {G : Type} [Group G] [Finite G]

theorem s16c13bcA_map_conj_eq_of_commute {Γ : Type*} [Group Γ] {A : Subgroup Γ} {z : Γ}
    (h : ∀ l ∈ A, z * l = l * z) : A.map (MulAut.conj z).toMonoidHom = A := by
  ext x
  constructor
  · rintro ⟨l, hl, rfl⟩
    have h1 : z * l * z⁻¹ = l := by rw [h l hl]; group
    show z * l * z⁻¹ ∈ A
    rw [h1]
    exact hl
  · intro hx
    refine ⟨x, hx, ?_⟩
    show z * x * z⁻¹ = x
    rw [h x hx]
    group

theorem s16c13bcA_mem_normalizer_of_map_eq {Γ : Type*} [Group Γ] {A : Subgroup Γ} {g : Γ}
    (h : A.map (MulAut.conj g).toMonoidHom = A) : g ∈ Subgroup.normalizer (A : Set Γ) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have h1 : g * x * g⁻¹ ∈ A.map (MulAut.conj g).toMonoidHom := ⟨x, hx, rfl⟩
    rwa [h] at h1
  · intro hx
    rw [← h] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    have hyx' : g * y * g⁻¹ = g * x * g⁻¹ := hyx
    have hxy : y = x := by simpa using hyx'
    rwa [hxy] at hy

theorem s16c13bcA_map_eq_of_mem_normalizer {Γ : Type*} [Group Γ] {A : Subgroup Γ} {g : Γ}
    (h : g ∈ Subgroup.normalizer (A : Set Γ)) : A.map (MulAut.conj g).toMonoidHom = A := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (Subgroup.mem_normalizer_iff.1 h y).1 hy
  · intro hx
    refine ⟨g⁻¹ * x * g, (Subgroup.mem_normalizer_iff''.1 h x).1 hx, ?_⟩
    show g * (g⁻¹ * x * g) * g⁻¹ = x
    group

theorem s16c13bcA_wTil_map_conj (V₀ V : Subgroup G) (hV : IsElemAbelian 2 V)
    (L : Subgroup G) (x : MulAut (Vtil V₀ V hV)) :
    (wTil V₀ V hV L).map x.toMonoidHom =
      commSub ⊤ ((lBar V₀ V hV L).map (MulAut.conj x).toMonoidHom) :=
  (s15_Infra_commSub_top_map_conj (lBar V₀ V hV L) x).symm

theorem s16c13bcA_wTil_map_eq (V₀ V : Subgroup G) (hV : IsElemAbelian 2 V)
    (L : Subgroup G) {x : MulAut (Vtil V₀ V hV)}
    (h : (lBar V₀ V hV L).map (MulAut.conj x).toMonoidHom = lBar V₀ V hV L) :
    (wTil V₀ V hV L).map x.toMonoidHom = wTil V₀ V hV L := by
  rw [s16c13bcA_wTil_map_conj, h]
  rfl

theorem s16c13bcA_six_psi {W : Type} [CommGroup W] {L : Subgroup (MulAut W)} {J₀ : Subgroup W}
    (hψ₃ : ∀ n ∈ J₀, n ≠ 1 → ∃ ψ ∈ L, orderOf ψ = 3 ∧ ψ n = n)
    {z : MulAut W} (hzL : ∀ l ∈ L, z * l = l * z) {k : ℕ} {a : W}
    (ha : a ∈ J₀.map (z ^ k).toMonoidHom) (ha1 : a ≠ 1) :
    ∃ ψ ∈ L, orderOf ψ = 3 ∧ ψ a = a := by
  obtain ⟨b, hb, rfl⟩ := ha
  have hb1 : b ≠ 1 := fun h => ha1 (by rw [h]; exact map_one _)
  obtain ⟨ψ, hψL, hψo, hψb⟩ := hψ₃ b hb hb1
  refine ⟨ψ, hψL, hψo, ?_⟩
  have hcomm : z ^ k * ψ = ψ * z ^ k := (Commute.pow_left (hzL ψ hψL) k).eq
  show ψ ((z ^ k) b) = (z ^ k) b
  calc ψ ((z ^ k) b) = (ψ * z ^ k) b := rfl
    _ = (z ^ k * ψ) b := by rw [hcomm]
    _ = (z ^ k) (ψ b) := rfl
    _ = (z ^ k) b := by rw [hψb]

theorem s16c13bcA_stable_member_le {W : Type} [CommGroup W] {L : Subgroup (MulAut W)}
    {J₀ J₁ : Subgroup W} (hJ₀ : XMod.IsIrr ↥L J₀) (hJ₁ : XMod.IsIrr ↥L J₁) (hinf : J₀ ⊓ J₁ = ⊥)
    (hE₀ : Z391.EndUnitsTrivial L J₀) (hE₁ : Z391.EndUnitsTrivial L J₁)
    {z : MulAut W} (hz3 : z ^ 3 = 1) (hzL : ∀ l ∈ L, z * l = l * z)
    (hzW : (J₀ ⊔ J₁).map z.toMonoidHom = J₀ ⊔ J₁) (hzne : ∃ u ∈ J₀ ⊔ J₁, z u ≠ u)
    {N : Subgroup (MulAut W)} (hN : IsPGroup 2 N)
    (hNL : ∀ w ∈ N, w ∈ Subgroup.normalizer (L : Set (MulAut W)))
    (hNW : ∀ w ∈ N, (J₀ ⊔ J₁).map w.toMonoidHom = J₀ ⊔ J₁) :
    ∃ k : ℕ, J₀.map (z ^ k).toMonoidHom ≤ J₀ ⊔ J₁ ∧ J₀.map (z ^ k).toMonoidHom ≠ ⊥ ∧
      ∀ w ∈ N, (J₀.map (z ^ k).toMonoidHom).map w.toMonoidHom = J₀.map (z ^ k).toMonoidHom := by
  obtain ⟨k, -, hk⟩ := s16c13bcA_stable_member hJ₀ hJ₁ hinf hE₀ hE₁ hz3 hzL hzW hzne hN hNL hNW
  have hzpow : ∀ j : ℕ, (J₀ ⊔ J₁).map (z ^ j).toMonoidHom = J₀ ⊔ J₁ := by
    intro j
    induction j with
    | zero =>
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact hy
      · intro hx
        exact ⟨x, hx, rfl⟩
    | succ j ih =>
      rw [pow_succ]
      calc (J₀ ⊔ J₁).map (z ^ j * z).toMonoidHom
          = ((J₀ ⊔ J₁).map z.toMonoidHom).map (z ^ j).toMonoidHom := by
            rw [Subgroup.map_map]
            rfl
        _ = J₀ ⊔ J₁ := by rw [hzW, ih]
  refine ⟨k, (Subgroup.map_mono le_sup_left).trans (le_of_eq (hzpow k)), ?_, hk⟩
  intro h0
  exact hJ₀.2.1.ne'
    ((Subgroup.map_eq_bot_iff_of_injective J₀ (f := (z ^ k).toMonoidHom) (z ^ k).injective).1 h0)

theorem s16c13bcA_six_fixfree {W : Type} [CommGroup W] {L : Subgroup (MulAut W)}
    {J₀ : Subgroup W} (hfix₀ : J₀ ⊓ fixV L = ⊥) {z : MulAut W}
    (hzL : ∀ l ∈ L, z * l = l * z) (k : ℕ) : J₀.map (z ^ k).toMonoidHom ⊓ fixV L = ⊥ := by
  rw [eq_bot_iff]
  rintro u ⟨⟨b, hb, rfl⟩, hu⟩
  have hbfix : b ∈ fixV L := by
    rw [mem_fixV]
    intro l hl
    have hcomm : z ^ k * l = l * z ^ k := (Commute.pow_left (hzL l hl) k).eq
    have h1 : l ((z ^ k) b) = (z ^ k) b := mem_fixV.1 hu l hl
    apply (z ^ k).injective
    calc (z ^ k) (l b) = (z ^ k * l) b := rfl
      _ = (l * z ^ k) b := by rw [hcomm]
      _ = l ((z ^ k) b) := rfl
      _ = (z ^ k) b := h1
  have hb0 : b ∈ J₀ ⊓ fixV L := ⟨hb, hbfix⟩
  rw [hfix₀, Subgroup.mem_bot] at hb0
  rw [Subgroup.mem_bot]
  show (z ^ k) b = 1
  rw [hb0]
  exact map_one _

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
