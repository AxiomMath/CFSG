module

public import CFSG.Quasithin.H13.NQCatA314Gen
public import CFSG.Quasithin.Vol2.Ch10SecKITu
public import CFSG.Quasithin.EmptyFaithful.A38c14CentralLift
public import CFSG.Quasithin.Background.A3Structure314Defs

public section

namespace CFSG.Quasithin.H13.NQCat.A314D

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Vol2Native.A312L
  CFSG.QuasithinUnique.Vol2Native.A312L.Seven Equiv

theorem conj_apply_eq_self_iff (k h : Perm (Fin 7)) (a : Fin 7) :
    (k * h * k⁻¹) a = a ↔ h (k⁻¹ a) = k⁻¹ a := by
  rw [Perm.mul_apply, Perm.mul_apply]
  exact Perm.eq_inv_iff_eq.symm

theorem conj_inv_apply_eq_self_iff (k h : Perm (Fin 7)) (a : Fin 7) :
    (k⁻¹ * h * k) a = a ↔ h (k a) = k a := by
  rw [Perm.mul_apply, Perm.mul_apply]
  exact Perm.inv_eq_iff_eq

theorem maps_s5_iff (k : Perm (Fin 7)) :
    (∀ x ∈ s5, k x ∈ s5) ↔ (k 4 = 4 ∨ k 4 = 5) ∧ (k 5 = 4 ∨ k 5 = 5) := by
  have hc : ∀ x : Fin 7, x ∉ s5 ↔ x = 4 ∨ x = 5 := by decide
  constructor
  · intro h
    have himg : s5.image k = s5 :=
      Finset.eq_of_subset_of_card_le (fun y hy => by
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
        exact h x hx) (Finset.card_image_of_injective _ k.injective).symm.le
    have key : ∀ a : Fin 7, a ∉ s5 → k a ∉ s5 := by
      intro a ha hka
      rw [← himg] at hka
      obtain ⟨x, hx, hxa⟩ := Finset.mem_image.mp hka
      rw [k.injective hxa] at hx
      exact ha hx
    exact ⟨(hc _).mp (key 4 (by decide)), (hc _).mp (key 5 (by decide))⟩
  · intro h x hx
    by_contra hkx
    rcases (hc _).mp hkx with h4 | h5
    · rcases fix_or_swap h.1 h.2 with ⟨a1, -⟩ | ⟨-, a2⟩
      · have := k.injective (h4.trans a1.symm)
        subst this
        exact absurd hx (by decide)
      · have := k.injective (h4.trans a2.symm)
        subst this
        exact absurd hx (by decide)
    · rcases fix_or_swap h.1 h.2 with ⟨-, a2⟩ | ⟨a1, -⟩
      · have := k.injective (h5.trans a2.symm)
        subst this
        exact absurd hx (by decide)
      · have := k.injective (h5.trans a1.symm)
        subst this
        exact absurd hx (by decide)

theorem mem_normalizer_rng5_iff (k : ↥A7s) :
    k ∈ Subgroup.normalizer (rng5 : Set ↥A7s) ↔
      (k.1 4 = 4 ∨ k.1 4 = 5) ∧ (k.1 5 = 4 ∨ k.1 5 = 5) := by
  constructor
  · intro hk
    have hcA : (swap (0 : Fin 7) 1 * swap 1 2 * swap 2 3 * swap 3 6) ∈ A7s :=
      Perm.mem_alternatingGroup.mpr (by decide)
    have hc5 : (⟨_, hcA⟩ : ↥A7s) ∈ rng5 := by
      rw [mem_rng5]
      exact ⟨by show (swap (0 : Fin 7) 1 * swap 1 2 * swap 2 3 * swap 3 6 : Perm (Fin 7)) 4 = 4
                decide,
        by show (swap (0 : Fin 7) 1 * swap 1 2 * swap 2 3 * swap 3 6 : Perm (Fin 7)) 5 = 5
           decide⟩
    have hmove : ∀ a : Fin 7,
        (swap (0 : Fin 7) 1 * swap 1 2 * swap 2 3 * swap 3 6 : Perm (Fin 7)) a = a →
          a = 4 ∨ a = 5 := by
      decide
    have h1 : k⁻¹ * ⟨_, hcA⟩ * k⁻¹⁻¹ ∈ rng5 :=
      (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hk) _).mp hc5
    rw [mem_rng5] at h1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, inv_inv] at h1
    rw [conj_inv_apply_eq_self_iff, conj_inv_apply_eq_self_iff] at h1
    exact ⟨hmove _ h1.1, hmove _ h1.2⟩
  · intro hk
    rw [Subgroup.mem_normalizer_iff]
    intro h
    show h ∈ rng5 ↔ k * h * k⁻¹ ∈ rng5
    rw [mem_rng5, mem_rng5]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [conj_apply_eq_self_iff, conj_apply_eq_self_iff]
    rcases fix_or_swap hk.1 hk.2 with ⟨a1, a2⟩ | ⟨a1, a2⟩
    · obtain ⟨c1, c2⟩ := inv_fix a1 a2
      rw [c1, c2]
    · obtain ⟨c1, c2⟩ := inv_swap a1 a2
      rw [c1, c2]
      exact and_comm

theorem stab_of_cover
    {X : Type} [Group X] [Finite X] (π : X →* ↥A7s)
    (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center X) {T B : Subgroup X}
    (hT : IsSylowTwoOf T ⊤) (hB : B ∈ lFamily T) (hA : IsAlt 5 ↥B) :
    ∃ f : X →* Perm (Fin 7), f.range = alternatingGroup (Fin 7) ∧
      f.ker ≤ Subgroup.center X ∧
      ∀ g : X, g ∈ Subgroup.normalizer (B : Set X) ↔ ∀ x ∈ s5, f g x ∈ s5 := by
  obtain ⟨g₀, hg₀⟩ := exists_conj_of_isSylowTwoOf (A312.isSylowTwoOf_top_map π hπ hT)
    isSylowTwoOf_T7
  set ρ : X →* ↥A7s := (MulAut.conj g₀).toMonoidHom.comp π with hρ
  have hρs : Function.Surjective ρ := (MulAut.conj g₀).surjective.comp hπ
  have hρk : ρ.ker ≤ Subgroup.center X := by
    intro x hx
    apply hker
    rw [MonoidHom.mem_ker] at hx ⊢
    have h1 : (MulAut.conj g₀) (π x) = 1 := hx
    exact (map_eq_one_iff _ (MulAut.conj g₀).injective).mp h1
  have hTρ : T.map ρ = T7 := by
    rw [hρ, ← Subgroup.map_map]
    exact hg₀
  obtain ⟨e5⟩ := hA
  have hinf : B ⊓ ρ.ker = ⊥ := by
    rw [eq_bot_iff]
    rintro b ⟨hb, hbk⟩
    have hbZ : b ∈ Subgroup.center X := hρk hbk
    have hc : e5 ⟨b, hb⟩ ∈ Subgroup.center (alternatingGroup (Fin 5)) := by
      rw [Subgroup.mem_center_iff]
      intro y
      obtain ⟨x, rfl⟩ := e5.surjective y
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (Subgroup.mem_center_iff.mp hbZ x.1)
    rw [Vol2.Ch10.SecB.C10KH.center_alt5, Subgroup.mem_bot, map_eq_one_iff _ e5.injective] at hc
    rw [Subgroup.mem_bot]
    exact congrArg Subtype.val hc
  have hBbar : B.map ρ ∈ lFamily T7 := by
    have h1 := A38c14.map_mem_lFamily ρ hρk hB
    rwa [hTρ] at h1
  have hB5 : B.map ρ = rng5 :=
    Vol2.Ch10.SecB.C10KH.eq_rng5 Vol2.Ch10.SecB.C10KH.a7s_quasisimple hBbar
      ⟨(A38c14.mapEquivOfInfKerEqBot ρ hinf).symm.trans e5⟩
  have hBp : ⁅B, B⁆ = B := perfect_of_mem_cComp (show B ∈ cComp (B ⊔ T) from hB)
  have hcore : perfectCore (B ⊔ Subgroup.center X) = B := by
    refine le_antisymm (perfectCore_le_of_sup_solvable le_sup_left ?_ rfl inferInstance)
      (le_perfectCore_of_perfect le_sup_left hBp)
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left]
    refine sup_le Subgroup.le_normalizer (fun z hz => ?_)
    rw [Subgroup.mem_normalizer_iff]
    intro a
    have hc := Subgroup.mem_center_iff.mp hz a
    rw [show z * a * z⁻¹ = a by rw [← hc, mul_inv_cancel_right]]
  have hconj : ∀ y : X, ρ y ∈ Subgroup.normalizer ((B.map ρ : Subgroup ↥A7s) : Set ↥A7s) →
      ∀ b ∈ B, y * b * y⁻¹ ∈ B := by
    intro y hy b hb
    have hCp : ⁅B.map (MulAut.conj y).toMonoidHom, B.map (MulAut.conj y).toMonoidHom⁆ =
        B.map (MulAut.conj y).toMonoidHom := by
      rw [← Subgroup.map_commutator, hBp]
    have hCle : B.map (MulAut.conj y).toMonoidHom ≤ B ⊔ Subgroup.center X := by
      rintro _ ⟨c, hc, rfl⟩
      have h1 : ρ (y * c * y⁻¹) ∈ B.map ρ := by
        rw [map_mul, map_mul, map_inv]
        exact (Subgroup.mem_normalizer_iff.mp hy (ρ c)).mp ⟨c, hc, rfl⟩
      have h2 : y * c * y⁻¹ ∈ (B.map ρ).comap ρ := h1
      rw [Subgroup.comap_map_eq] at h2
      exact sup_le_sup_left hρk B h2
    have h3 := le_perfectCore_of_perfect hCle hCp
    rw [hcore] at h3
    exact h3 ⟨b, hb, rfl⟩
  have hN : ∀ y : X, y ∈ Subgroup.normalizer (B : Set X) ↔
      ρ y ∈ Subgroup.normalizer ((B.map ρ : Subgroup ↥A7s) : Set ↥A7s) := by
    intro y
    constructor
    · intro hy
      exact Subgroup.le_normalizer_map ρ ⟨y, hy, rfl⟩
    · intro hy
      rw [Subgroup.mem_normalizer_iff]
      intro b
      refine ⟨fun hb => hconj y hy b hb, fun hb => ?_⟩
      have hy' : ρ y⁻¹ ∈ Subgroup.normalizer ((B.map ρ : Subgroup ↥A7s) : Set ↥A7s) := by
        rw [map_inv]
        exact Subgroup.inv_mem _ hy
      have h1 := hconj y⁻¹ hy' _ hb
      rwa [show y⁻¹ * (y * b * y⁻¹) * y⁻¹⁻¹ = b by group] at h1
  refine ⟨(alternatingGroup (Fin 7)).subtype.comp ρ, ?_, ?_, fun g => ?_⟩
  · ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact (ρ y).2
    · intro hx
      obtain ⟨y, hy⟩ := hρs ⟨x, hx⟩
      exact ⟨y, by rw [MonoidHom.comp_apply, hy]; rfl⟩
  · intro x hx
    apply hρk
    rw [MonoidHom.mem_ker] at hx ⊢
    exact Subtype.ext hx
  · rw [hN g, hB5, mem_normalizer_rng5_iff, ← maps_s5_iff]
    rfl

theorem desc_alt7
    (G : Type) [Group G] [Finite G] (L T B : Subgroup G)
    (hT : IsSylowTwoOf T L) (hB : B ∈ lFamily T) (hBL : B ≤ L) (_hne : B ≠ L)
    (hL : IsAlt 7 ↥L ∨ IsHat ↥L (alternatingGroup (Fin 7))) (hA : IsAlt 5 ↥B) :
    StabilizesFivePoints B L := by
  have hTL := hT.1
  obtain ⟨π, hπ, hker⟩ : ∃ π : ↥L →* ↥A7s, Function.Surjective π ∧
      π.ker ≤ Subgroup.center ↥L := by
    rcases hL with hL | hL
    · obtain ⟨e⟩ := hL
      refine ⟨e.toMonoidHom, e.surjective, fun x hx => ?_⟩
      rw [MonoidHom.mem_ker] at hx
      have h1 : x = 1 := (map_eq_one_iff _ e.injective).mp hx
      rw [h1]
      exact Subgroup.one_mem _
    · obtain ⟨-, -, ⟨e⟩⟩ := hL
      refine ⟨e.toMonoidHom.comp (QuotientGroup.mk' _),
        e.surjective.comp (QuotientGroup.mk'_surjective _), fun x hx => ?_⟩
      rw [MonoidHom.mem_ker] at hx
      have h1 : e (QuotientGroup.mk x) = 1 := hx
      rwa [map_eq_one_iff _ e.injective, QuotientGroup.eq_one_iff] at h1
  have hB' : B.subgroupOf L ∈ lFamily (T.subgroupOf L) := by
    show B.subgroupOf L ∈ cComp (B.subgroupOf L ⊔ T.subgroupOf L)
    rw [← Subgroup.subgroupOf_sup hBL hTL]
    exact A312.mem_cComp_subgroupOf (sup_le hBL hTL) hB
  obtain ⟨e5⟩ := hA
  obtain ⟨f, hf, hfk, hN⟩ := stab_of_cover π hπ hker (isSylowTwoOf_top_subgroupOf hT) hB'
    ⟨(Subgroup.subgroupOfEquivOfLe hBL).trans e5⟩
  refine ⟨f, hf, hfk, s5, card_s5, fun g => ?_⟩
  have h1 : (g : G) ∈ Subgroup.normalizer (B : Set G) ↔
      g ∈ Subgroup.normalizer ((B.subgroupOf L : Subgroup ↥L) : Set ↥L) := by
    rw [← Subgroup.subgroupOf_normalizer_eq hBL, Subgroup.mem_subgroupOf]
  exact h1.trans (hN g)

end CFSG.Quasithin.H13.NQCat.A314D
