module

public import CFSG.Quasithin.Background.E1Invariance
public import CFSG.Quasithin.Background.E1Amb

public section

namespace CFSG.Quasithin

namespace E1

open CFSG.Open CFSG.Quasithin.A1b
open scoped Pointwise

variable {G : Type*} [Group G]

theorem conjSub_eq_of_mem_normalizer {g : G} {H : Subgroup G}
    (hg : g ∈ Subgroup.normalizer (H : Set G)) : conjSub g H = H := by
  rw [Subgroup.mem_normalizer_iff''] at hg
  ext x
  rw [mem_conjSub_iff]
  exact (hg x).symm

theorem mem_normalizer_of_conjSub_eq {g : G} {H : Subgroup G} (h : conjSub g H = H) :
    g ∈ Subgroup.normalizer (H : Set G) := by
  rw [Subgroup.mem_normalizer_iff'']
  intro x
  rw [← mem_conjSub_iff, h]

@[expose] def eGenRes (j : ℕ) (H T : Subgroup G) (Ω : Set (Subgroup G)) : Subgroup G :=
  ⨆ A ∈ Ω, ⨆ (_ : A ≤ T), ⨆ K ∈ {K : Subgroup G | IsE j H T A K}, twoResidual K

theorem twoResidual_le_of_normal_two {H Y K : Subgroup G} (hKH : K ≤ H)
    (hHY : H ≤ Subgroup.normalizer (Y : Set G)) (h2 : ∀ x ∈ H, ∃ k : ℕ, x ^ 2 ^ k ∈ Y) :
    twoResidual K ≤ Y := by
  have h1 : twoResidual K ≤ K ⊓ Y := by
    refine twoResidual_le_of_isTwoQuotient inf_le_left
      (le_normalizer_inf_of_le_normalizer (hKH.trans hHY)) ?_
    intro y hy
    obtain ⟨k, hk⟩ := h2 y (hKH hy)
    exact ⟨k, Subgroup.mem_inf.mpr ⟨K.pow_mem hy _, hk⟩⟩
  exact h1.trans inf_le_right

theorem eGenRes_le {j : ℕ} {H Y T : Subgroup G} {Ω : Set (Subgroup G)}
    (hHY : H ≤ Subgroup.normalizer (Y : Set G)) (h2 : ∀ x ∈ H, ∃ k : ℕ, x ^ 2 ^ k ∈ Y) :
    eGenRes j H T Ω ≤ Y :=
  iSup₂_le fun _ _ => iSup_le fun _ => iSup₂_le fun _ hK =>
    twoResidual_le_of_normal_two hK.1 hHY h2

theorem le_normalizer_of_forall_conjSub_le {X T : Subgroup G} (h : ∀ t ∈ T, conjSub t X ≤ X) :
    T ≤ Subgroup.normalizer (X : Set G) := by
  intro t ht
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    exact h t ht (mem_conjSub_of_mem hx)
  · intro hx
    have := h t⁻¹ (T.inv_mem ht) (mem_conjSub_of_mem hx)
    simpa [mul_assoc] using this

theorem conjSub_inf_normalizer_le {t : G} {Y W : Subgroup G}
    (hY : t ∈ Subgroup.normalizer (Y : Set G)) (hW : t ∈ Subgroup.normalizer (W : Set G)) :
    conjSub t (Y ⊓ Subgroup.normalizer (W : Set G)) ≤ Y ⊓ Subgroup.normalizer (W : Set G) := by
  intro z hz
  rw [mem_conjSub_iff] at hz
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · have := (Subgroup.mem_normalizer_iff.mp hY (t⁻¹ * z * t)).mp hz.1
    simpa [mul_assoc] using this
  · have h1 := (Subgroup.normalizer (W : Set G)).mul_mem
      ((Subgroup.normalizer (W : Set G)).mul_mem hW hz.2)
      ((Subgroup.normalizer (W : Set G)).inv_mem hW)
    simpa [mul_assoc] using h1

theorem le_normalizer_weakClosure_of_inv {H T : Subgroup G} {Ω : Set (Subgroup G)} (hTH : T ≤ H)
    (hΩ : ∀ A ∈ Ω, ∀ h ∈ H, conjSub h A ∈ Ω) :
    T ≤ Subgroup.normalizer (weakClosure T Ω : Set G) := by
  intro t ht
  have h1 : ∀ A ∈ Ω, conjSub t A ∈ Ω := fun A hA => hΩ A hA t (hTH ht)
  have h2 : ∀ A ∈ Ω, conjSub t⁻¹ A ∈ Ω := fun A hA => hΩ A hA t⁻¹ (hTH (T.inv_mem ht))
  have h := weakClosure_conj t T h1 h2
  rw [conjSub_eq_of_mem_normalizer (Subgroup.le_normalizer ht)] at h
  exact mem_normalizer_of_conjSub_eq h.symm

theorem isE_conj_of_mem [Finite G] {j : ℕ} {H T A K : Subgroup G} (hTH : T ≤ H) {t : G} (ht : t ∈ T)
    (hK : IsE j H T A K) : IsE j H T (conjSub t A) (conjSub t K) := by
  have h := (isE_conj t).2 hK
  rwa [conjSub_eq_of_mem_normalizer (Subgroup.le_normalizer (hTH ht)),
    conjSub_eq_of_mem_normalizer (Subgroup.le_normalizer ht)] at h

theorem conjSub_eGenRes_le [Finite G] {j : ℕ} {H T : Subgroup G} {Ω : Set (Subgroup G)}
    (hTH : T ≤ H) (hΩ : ∀ A ∈ Ω, ∀ h ∈ H, conjSub h A ∈ Ω) {t : G} (ht : t ∈ T) :
    conjSub t (eGenRes j H T Ω) ≤ eGenRes j H T Ω := by
  show (eGenRes j H T Ω).map (MulAut.conj t).toMonoidHom ≤ _
  unfold eGenRes
  rw [Subgroup.map_iSup]
  refine iSup_le fun A => ?_
  rw [Subgroup.map_iSup]
  refine iSup_le fun hA => ?_
  rw [Subgroup.map_iSup]
  refine iSup_le fun hAT => ?_
  rw [Subgroup.map_iSup]
  refine iSup_le fun K => ?_
  rw [Subgroup.map_iSup]
  refine iSup_le fun hK => ?_
  rw [map_twoResidual]
  have hAt : conjSub t A ≤ T := by
    have := conjSub_mono t hAT
    rwa [conjSub_eq_of_mem_normalizer (Subgroup.le_normalizer ht)] at this
  exact le_iSup₂_of_le (conjSub t A) (hΩ A hA t (hTH ht))
    (le_iSup_of_le hAt (le_iSup₂_of_le (conjSub t K) (isE_conj_of_mem hTH ht hK) le_rfl))

theorem le_eGenRes_sup_normalizer [Finite G] {j : ℕ} {H Y T : Subgroup G} {Ω : Set (Subgroup G)}
    (hT : IsSylowIn 2 T H) (hYH : Y ≤ H) (hHY : H ≤ Subgroup.normalizer (Y : Set G))
    (h2 : ∀ x ∈ H, ∃ k : ℕ, x ^ 2 ^ k ∈ Y) (hΩ : ∀ A ∈ Ω, ∀ h ∈ H, conjSub h A ∈ Ω)
    (hgen : eGen j H T Ω ⊔ (H ⊓ Subgroup.normalizer (weakClosure T Ω : Set G)) = H) :
    Y ≤ eGenRes j H T Ω ⊔ (Y ⊓ Subgroup.normalizer (weakClosure T Ω : Set G)) := by
  have hTH : T ≤ H := hT.le
  set W := weakClosure T Ω with hW
  set R := eGenRes j H T Ω with hR
  set X := R ⊔ (Y ⊓ Subgroup.normalizer (W : Set G)) with hX
  have hTW : T ≤ Subgroup.normalizer (W : Set G) := le_normalizer_weakClosure_of_inv hTH hΩ
  have hTY : T ≤ Subgroup.normalizer (Y : Set G) := hTH.trans hHY
  have hRY : R ≤ Y := eGenRes_le hHY h2
  have hXY : X ≤ Y := sup_le hRY inf_le_left
  have hXT : ∀ t ∈ T, conjSub t X ≤ X := by
    intro t ht
    show X.map (MulAut.conj t).toMonoidHom ≤ X
    rw [Subgroup.map_sup]
    exact sup_le (le_sup_of_le_left (conjSub_eGenRes_le hTH hΩ ht))
      (le_sup_of_le_right (conjSub_inf_normalizer_le (hTY ht) (hTW ht)))
  have hTX : T ≤ Subgroup.normalizer (X : Set G) := le_normalizer_of_forall_conjSub_le hXT
  have hYT : H ≤ Y ⊔ T := by
    have h1 : twoResidual H ≤ Y := twoResidual_le_of_normal_two le_rfl hHY h2
    calc H = T ⊔ twoResidual H := (sup_twoResidual_eq hT).symm
      _ ≤ Y ⊔ T := sup_le le_sup_right (h1.trans le_sup_left)
  have hNX : Y ⊓ Subgroup.normalizer (W : Set G) ≤ X := le_sup_right
  have hHXT : H ≤ X ⊔ T := by
    rw [← hgen]
    refine sup_le ?_ ?_
    · refine iSup₂_le fun A hA => iSup_le fun hAT => iSup₂_le fun K hK => ?_
      have hKeq : (T ⊓ K) ⊔ twoResidual K = K := sup_twoResidual_eq hK.2.2.1
      have hRK : twoResidual K ≤ R :=
        le_iSup₂_of_le A hA (le_iSup_of_le hAT (le_iSup₂_of_le K hK le_rfl))
      rw [← hKeq]
      exact sup_le (inf_le_left.trans le_sup_right) (hRK.trans (le_sup_left.trans le_sup_left))
    · intro h hh
      have hhY : h ∈ Y ⊔ T := hYT hh.1
      have hmul : (↑(Y ⊔ T) : Set G) = Y * T :=
        Subgroup.coe_mul_of_right_le_normalizer_left Y T hTY
      have hhm : h ∈ (Y * T : Set G) := by rw [← hmul]; exact hhY
      obtain ⟨y, hy, t, ht, rfl⟩ := Set.mem_mul.mp hhm
      have hyW : y ∈ Subgroup.normalizer (W : Set G) := by
        have := (Subgroup.normalizer (W : Set G)).mul_mem hh.2
          ((Subgroup.normalizer (W : Set G)).inv_mem (hTW ht))
        simpa using this
      have hyX : y ∈ X := hNX ⟨hy, hyW⟩
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hyX) (Subgroup.mem_sup_right ht)
  intro y hy
  have hyXT : y ∈ X ⊔ T := hHXT (hYH hy)
  have hmul : (↑(X ⊔ T) : Set G) = X * T :=
    Subgroup.coe_mul_of_right_le_normalizer_left X T hTX
  have hym : y ∈ (X * T : Set G) := by rw [← hmul]; exact hyXT
  obtain ⟨x, hx, t, ht, rfl⟩ := Set.mem_mul.mp hym
  have hxY : x ∈ Y := hXY hx
  have htY : t ∈ Y := by
    have := Y.mul_mem (Y.inv_mem hxY) hy
    simpa using this
  exact X.mul_mem hx (hNX ⟨htY, hTW ht⟩)

theorem eGenRes_sup_normalizer_eq [Finite G] {j : ℕ} {H Y T : Subgroup G} {Ω : Set (Subgroup G)}
    (hT : IsSylowIn 2 T H) (hYH : Y ≤ H) (hHY : H ≤ Subgroup.normalizer (Y : Set G))
    (h2 : ∀ x ∈ H, ∃ k : ℕ, x ^ 2 ^ k ∈ Y) (hΩ : ∀ A ∈ Ω, ∀ h ∈ H, conjSub h A ∈ Ω)
    (hgen : eGen j H T Ω ⊔ (H ⊓ Subgroup.normalizer (weakClosure T Ω : Set G)) = H) :
    eGenRes j H T Ω ⊔ (Y ⊓ Subgroup.normalizer (weakClosure T Ω : Set G)) = Y :=
  le_antisymm (sup_le (eGenRes_le hHY h2) inf_le_left)
    (le_eGenRes_sup_normalizer hT hYH hHY h2 hΩ hgen)

end E1

end CFSG.Quasithin
