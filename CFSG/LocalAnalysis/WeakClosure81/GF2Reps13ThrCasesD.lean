module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13ThrCasesC
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13Two

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.Quasithin CFSG.Open Subgroup
open scoped commutatorElement

variable {W : Type} [CommGroup W] [Finite W]

private theorem w16g_iso_pOnePlusTwo {p : ℕ} {X Y : Type} [Group X] [Group Y]
    (e : X ≃* Y) (h : IsPOnePlusTwo p X) : IsPOnePlusTwo p Y := by
  obtain ⟨hX, hc, hp⟩ := h
  haveI : CFSG.IsExtraspecial p X := hX
  refine ⟨isExtraspecial_of_mulEquiv e.symm, ?_, ?_⟩
  · rw [← Nat.card_congr e.toEquiv]; exact hc
  · intro y
    obtain ⟨x, rfl⟩ := e.surjective y
    rw [← map_pow, hp x, map_one]

private theorem w16g_map_pOnePlusTwo_iff {p : ℕ} {G N : Type} [Group G] [Group N]
    (f : G →* N) (hf : Function.Injective f) (H : Subgroup G) :
    IsPOnePlusTwo p ↥(H.map f) ↔ IsPOnePlusTwo p ↥H :=
  ⟨fun h => w16g_iso_pOnePlusTwo (Subgroup.equivMapOfInjective H f hf).symm h,
   fun h => w16g_iso_pOnePlusTwo (Subgroup.equivMapOfInjective H f hf) h⟩

private theorem w16g_subgroupOf_pOnePlusTwo_iff {p : ℕ} {G : Type} [Group G]
    {H K : Subgroup G} (h : H ≤ K) :
    IsPOnePlusTwo p ↥(H.subgroupOf K) ↔ IsPOnePlusTwo p ↥H :=
  ⟨fun hh => w16g_iso_pOnePlusTwo (Subgroup.subgroupOfEquivOfLe h) hh,
   fun hh => w16g_iso_pOnePlusTwo (Subgroup.subgroupOfEquivOfLe h).symm hh⟩

private theorem w16g_card_isZ3_81 {X : Type} [Group X]
    (h : IsZ3TimesPOnePlusTwo X ∨ IsZ3WrZ3 X) : Nat.card X = 81 := by
  rcases h with h | h
  · obtain ⟨H, hinstH, hP, ⟨e⟩⟩ := h
    letI := hinstH
    have hcardH : Nat.card H = 27 := by rw [hP.2.1]; norm_num
    have hcardZ : Nat.card (Multiplicative (ZMod 3)) = 3 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
    calc Nat.card X = Nat.card (Multiplicative (ZMod 3) × H) := Nat.card_congr e.toEquiv
      _ = Nat.card (Multiplicative (ZMod 3)) * Nat.card H := Nat.card_prod _ _
      _ = 3 * 27 := by rw [hcardZ, hcardH]
      _ = 81 := by norm_num
  · exact h.1

theorem w16g_four_via_min (hW : ∀ w : W, w * w = 1) {t : MulAut W} (ht : orderOf t = 2)
    (hrk : rk ↥(commSub ⊤ (Subgroup.zpowers t)) ≤ 3) {P : Subgroup (MulAut W)}
    (hP3 : IsPGroup 3 ↥P) (hne : P ≠ ⊥) (hn : ∀ x ∈ P, t * x * t⁻¹ ∈ P)
    (hc : ⁅P, Subgroup.zpowers t⁆ = P) (h4 : IsZ3TimesPOnePlusTwo ↥P ∨ IsZ3WrZ3 ↥P) :
    ∃ V₀ : Subgroup W, StableUnder (P ⊔ Subgroup.zpowers t) V₀ ∧
      commSub ⊤ (Subgroup.zpowers t) ≤ V₀ ∧
      ∃! Q : Subgroup (MulAut W), Q ≤ P ∧ IsPOnePlusTwo 3 ↥Q ∧ rk ↥(commSub V₀ Q) = 6 := by
  classical
  obtain ⟨V₀, ρ, t', hstab, hρinj, _hρact, _ht'act, hcfg, hmin, hE1, hE2⟩ :=
    w16g_exists_minRestr hW ht hrk hP3 hne hn hc
  have hW2 : ∀ w : W, w ^ 2 = 1 := fun w => by rw [pow_two]; exact hW w
  have hcardP : Nat.card ↥P = 81 := w16g_card_isZ3_81 (X := ↥P) h4
  have hcardrange : Nat.card ↥ρ.range = 81 := by
    have h := Nat.card_congr (MonoidHom.ofInjective hρinj).toEquiv
    rw [hcardP] at h
    exact h.symm
  have hmain := w4Lem13_2Min_holds (↥V₀) hcfg.hW t' hcfg.ht hcfg.hrk 3 ρ.range
    Nat.prime_three hcfg.hP hcfg.hne hcfg.hn hcfg.hc hmin
  have hfour : rk ↥(commSub ⊤ (Subgroup.zpowers t')) = 3 ∧
      ∃! Q : Subgroup (MulAut ↥V₀), Q ≤ ρ.range ∧ IsPOnePlusTwo 3 ↥Q ∧
        rk ↥(commSub ⊤ Q) = 6 := by
    rcases hmain with h1 | h2 | h3 | h4'
    · exfalso; omega
    · exfalso
      obtain ⟨k, hk3, ⟨e⟩⟩ := h2
      have hcardk : Nat.card ↥ρ.range = 3 ^ k := by
        rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, Fintype.card_multiplicative,
          Fintype.card_fun, ZMod.card, Fintype.card_fin]
      have hk : 3 ^ k ≤ 27 := by
        calc 3 ^ k ≤ 3 ^ 3 := Nat.pow_le_pow_right (by norm_num) hk3
          _ = 27 := by norm_num
      omega
    · exfalso
      have h := h3.1.2.1
      rw [hcardrange] at h
      norm_num at h
    · exact ⟨h4'.2.1, h4'.2.2⟩
  obtain ⟨hrk3, huniq⟩ := hfour
  obtain ⟨Qbar, ⟨hQbar_le, hQbar_ext, hQbar_rk⟩, hQbar_uniq⟩ := huniq
  have hE1' : rk ↥(commSub V₀ (Subgroup.zpowers t)) = 3 := by
    rw [← hE1]
    unfold rk
    rw [Subgroup.card_map_of_injective (K := commSub ⊤ (Subgroup.zpowers t'))
      (f := V₀.subtype) V₀.subtype_injective]
    exact hrk3
  have hEq : commSub V₀ (Subgroup.zpowers t) = commSub ⊤ (Subgroup.zpowers t) :=
    eq_of_le_of_rk_le hW2 (commSub_mono le_top le_rfl) (by rw [hE1']; exact hrk)
  have hle : commSub ⊤ (Subgroup.zpowers t) ≤ V₀ := by
    rw [← hEq]
    exact commSub_le_of_invariant
      (fun x hx v hv => hstab x (Subgroup.mem_sup_right hx) v hv)
  let Q₀ : Subgroup (MulAut W) := (Qbar.comap ρ).map P.subtype
  have hQ₀sub : Q₀.subgroupOf P = Qbar.comap ρ := by
    change ((Qbar.comap ρ).map P.subtype).subgroupOf P = Qbar.comap ρ
    ext x
    constructor
    · intro hx
      rw [Subgroup.mem_subgroupOf] at hx
      obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
      rw [Subgroup.mem_comap]
      have hyx' : y = x := Subgroup.subtype_injective P hyx
      rw [← hyx']
      exact hy
    · intro hx
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_map]
      exact ⟨x, hx, rfl⟩
  have hQ₀P : Q₀ ≤ P := Subgroup.map_subtype_le (Qbar.comap ρ)
  have hF : (Q₀.subgroupOf P).map ρ = Qbar := by
    rw [hQ₀sub, Subgroup.map_comap_eq, inf_eq_right.mpr hQbar_le]
  have hQ₀ext : IsPOnePlusTwo 3 ↥Q₀ := by
    have h1 : IsPOnePlusTwo 3 ↥((Q₀.subgroupOf P).map ρ) := by
      rw [hF]; exact hQbar_ext
    exact (w16g_subgroupOf_pOnePlusTwo_iff hQ₀P).mp
      ((w16g_map_pOnePlusTwo_iff ρ hρinj (Q₀.subgroupOf P)).mp h1)
  have hQ₀rk : rk ↥(commSub V₀ Q₀) = 6 := by
    have hmap : rk ↥((commSub ⊤ ((Q₀.subgroupOf P).map ρ)).map V₀.subtype) =
        rk ↥(commSub ⊤ ((Q₀.subgroupOf P).map ρ)) := by
      unfold rk
      rw [Subgroup.card_map_of_injective (K := commSub ⊤ ((Q₀.subgroupOf P).map ρ))
        (f := V₀.subtype) V₀.subtype_injective]
    rw [← hE2 Q₀ hQ₀P, hmap, hF]
    exact hQbar_rk
  refine ⟨V₀, hstab, hle, Q₀, ⟨hQ₀P, hQ₀ext, hQ₀rk⟩, ?_⟩
  rintro Q' ⟨hQ'P, hQ'ext, hQ'rk⟩
  have hFQ' : (Q'.subgroupOf P).map ρ = Qbar := by
    apply hQbar_uniq
    refine ⟨Subgroup.map_le_range ρ (Q'.subgroupOf P), ?_, ?_⟩
    · exact (w16g_map_pOnePlusTwo_iff ρ hρinj (Q'.subgroupOf P)).mpr
        ((w16g_subgroupOf_pOnePlusTwo_iff hQ'P).mpr hQ'ext)
    · have hmap : rk ↥(commSub ⊤ ((Q'.subgroupOf P).map ρ)) =
          rk ↥((commSub ⊤ ((Q'.subgroupOf P).map ρ)).map V₀.subtype) := by
        unfold rk
        rw [Subgroup.card_map_of_injective (K := commSub ⊤ ((Q'.subgroupOf P).map ρ))
          (f := V₀.subtype) V₀.subtype_injective]
      rw [hmap, hE2 Q' hQ'P]
      exact hQ'rk
  have hsubOf : Q'.subgroupOf P = Q₀.subgroupOf P :=
    Subgroup.map_injective hρinj (by rw [hFQ', hF])
  calc Q' = (Q'.subgroupOf P).map P.subtype := (Subgroup.map_subgroupOf_eq_of_le hQ'P).symm
    _ = (Q₀.subgroupOf P).map P.subtype := by rw [hsubOf]
    _ = Q₀ := Subgroup.map_subgroupOf_eq_of_le hQ₀P

end CFSG.LocalAnalysis.WeakClosure81
