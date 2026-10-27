module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineCOrbFam

public section

namespace CFSG.LocalAnalysis.WeakClosure81.TC914

open CFSG.Quasithin CFSG.Open Subgroup

variable {X : Type} [Group X] [Finite X]

theorem eq_one_of_irred {p : ℕ} (hp : p.Prime) {S Z : Subgroup X}
    (hirr : IrredOnFrattiniQuot S Z) (hZ : IsElemAbelian p Z)
    (hnt : ∃ y ∈ S ⊓ normalizer (Z : Set X), ∃ x ∈ Z, y * x * y⁻¹ ≠ x) {x : X} (hx : x ∈ Z)
    (hfix : ∀ s ∈ S ⊓ normalizer (Z : Set X), s * x * s⁻¹ = x) : x = 1 := by
  have hΦ := nineFrattini_eq_bot hp hZ
  have hinv : ∀ s ∈ S ⊓ normalizer (Z : Set X),
      ∀ u ∈ Z ⊓ centralizer ((S ⊓ normalizer (Z : Set X) : Subgroup X) : Set X),
        s * u * s⁻¹ ∈ Z ⊓ centralizer ((S ⊓ normalizer (Z : Set X) : Subgroup X) : Set X) := by
    intro s hs u hu
    rwa [mul_inv_eq_of_eq_mul (mem_centralizer_iff.1 hu.2 s hs)]
  rcases hirr.2 _ (by rw [hΦ]; exact bot_le) inf_le_left hinv with h | h
  · have hxU : x ∈ Z ⊓ centralizer ((S ⊓ normalizer (Z : Set X) : Subgroup X) : Set X) :=
      ⟨hx, mem_centralizer_iff.2 fun s hs => (mul_inv_eq_iff_eq_mul.1 (hfix s hs))⟩
    rwa [h, hΦ, mem_bot] at hxU
  · obtain ⟨y, hy, z, hz, hne⟩ := hnt
    have hzU : z ∈ Z ⊓ centralizer ((S ⊓ normalizer (Z : Set X) : Subgroup X) : Set X) := by
      rw [h]
      exact hz
    exact absurd (mul_inv_eq_of_eq_mul (mem_centralizer_iff.1 hzU.2 y hy)) hne

namespace OrbData

variable {Lb Tb A C F H₁ X₁ : Subgroup X} {p : ℕ} (d : OrbData Lb Tb A C F H₁ X₁ p)
include d

omit [Finite X] in
theorem mem_NKT_of_mem_C {g : X} (hg : g ∈ C) :
    g ∈ orbK Tb A C F H₁ ⊓ Tb ⊓ normalizer (orb C X₁ : Set X) :=
  ⟨⟨A_le_orbK (d.C_le hg), d.C_le_T hg⟩,
    le_normalizer_orb (Nm := ⊥) bot_le (T := C) (fun _ ht => permBy_of_mem ht) hg⟩

omit [Finite X] in
theorem mem_NKT {c : X} (hc : c ∈ C) {s : X}
    (hs : s ∈ conjSub c (H₁ ⊓ Tb) ⊓ normalizer (conjSub c X₁ : Set X)) :
    s ∈ orbK Tb A C F H₁ ⊓ Tb ⊓ normalizer (orb C X₁ : Set X) := by
  refine ⟨⟨orbS_le_orbK (mem_sup_left (mem_sup_left (conjSub_le_orb hc hs.1))),
    d.orb_T_le (conjSub_le_orb hc hs.1)⟩, ?_⟩
  refine le_normalizer_orb le_rfl (T := conjSub c (H₁ ⊓ Tb) ⊓ normalizer (conjSub c X₁ : Set X))
    (fun t ht => ?_) hs
  refine d.permBy_of_mem_conjSub hc (conjSub_mono _ (inf_le_left.trans d.H_le) ht.1)
    (centralizer_le_normalizer_of_le (d.X_le_H.trans d.H_le)) ?_
  have h1 : (MulAut.conj c).toMonoidHom (c⁻¹ * t * c) ∈
      normalizer ((X₁.map (MulAut.conj c).toMonoidHom : Subgroup X) : Set X) := by
    rw [show (MulAut.conj c).toMonoidHom (c⁻¹ * t * c) = t by
      simp [MulAut.conj_apply, mul_assoc]]
    exact ht.2
  exact (mem_normalizer_map_iff (MulAut.conj c).injective).1 h1

omit [Finite X] in
theorem nontriv_conjSub (k : X) :
    ∃ y ∈ conjSub k (H₁ ⊓ Tb) ⊓ normalizer (conjSub k X₁ : Set X), ∃ x ∈ conjSub k X₁,
      y * x * y⁻¹ ≠ x := by
  obtain ⟨y, ⟨hyS, hyN⟩, x, hx, hne⟩ := d.nontriv
  refine ⟨k * y * k⁻¹, ⟨mul_mem_conjSub hyS, ?_⟩, k * x * k⁻¹, mul_mem_conjSub hx, fun h => hne ?_⟩
  · exact (mem_normalizer_map_iff (MulAut.conj k).injective).2 hyN
  · have h' : k * (y * x * y⁻¹) * k⁻¹ = k * x * k⁻¹ := by
      rw [← h]
      group
    simpa using h'

theorem eq_of_inf_ne_bot {W : Subgroup X} (hWX : W ≤ orb C X₁)
    (hW : ∀ s ∈ orbK Tb A C F H₁ ⊓ Tb ⊓ normalizer (orb C X₁ : Set X), ∀ y ∈ W, s * y * s⁻¹ ∈ W)
    {c : X} (hc : c ∈ C) (hne : W ⊓ conjSub c X₁ ≠ ⊥) : W = orb C X₁ := by
  have hΦc : nineFrattini (conjSub c X₁) = ⊥ := nineFrattini_eq_bot d.irr.prime (d.elem.map _)
  rcases (d.irr_conjSub c).irred.2 (W ⊓ conjSub c X₁) (by rw [hΦc]; exact bot_le) inf_le_right
    (fun s hs w hw => ⟨hW s (d.mem_NKT hc hs) w hw.1, (mem_normalizer_iff.1 hs.2 w).1 hw.2⟩)
    with h | h
  · exact absurd (h.trans hΦc) hne
  have hcW : conjSub c X₁ ≤ W := h ▸ inf_le_left
  refine le_antisymm hWX (orb_le fun j hj x hx => ?_)
  have hx' : x = (j * c⁻¹) * (c * (j⁻¹ * x * j) * c⁻¹) * (j * c⁻¹)⁻¹ := by group
  rw [hx']
  exact hW _ (d.mem_NKT_of_mem_C (C.mul_mem hj (C.inv_mem hc))) _
    (hcW (mul_mem_conjSub (mem_conjSub.1 hx)))

theorem eq_bot_of_inf_eq_bot {W : Subgroup X} (hWX : W ≤ orb C X₁)
    (hW : ∀ s ∈ orbK Tb A C F H₁ ⊓ Tb ⊓ normalizer (orb C X₁ : Set X), ∀ y ∈ W, s * y * s⁻¹ ∈ W)
    (hex : ∀ c ∈ C, W ⊓ conjSub c X₁ = ⊥) : W = ⊥ := by
  refine le_bot_iff.1 fun w hw => ?_
  have : Fintype C := Fintype.ofFinite C
  classical
  have hpw := d.pairwise (d.X_le_H.trans d.H_le)
  obtain ⟨f, rfl⟩ := exists_noncommPiCoprod_eq hpw (hWX hw)
  have hf : ∀ k, (f k : X) = 1 := by
    intro k
    refine eq_one_of_irred d.irr.prime (d.irr_conjSub k).irred (d.elem.map _) (d.nontriv_conjSub k)
      (f k).2 fun s hs => ?_
    have hrs := (commute_noncommPiCoprod_update hpw f k (y := s) fun j hj x hx =>
      d.commute_of_ne k.2 j.2 (fun h => hj (Subtype.ext h).symm)
        (conjSub_mono _ (inf_le_left.trans d.H_le) hs.1)
        (conjSub_mono _ (d.X_le_H.trans d.H_le) hx)).inv_left.eq
    have h1 : s * (f k : X) * s⁻¹ * (f k : X)⁻¹ ∈ W ⊓ conjSub (k : X) X₁ := by
      refine Subgroup.mem_inf.2 ⟨?_, (conjSub (k : X) X₁).mul_mem
        ((mem_normalizer_iff.1 hs.2 _).1 (f k).2) ((conjSub (k : X) X₁).inv_mem (f k).2)⟩
      have h2 := W.mul_mem (hW s (d.mem_NKT k.2 hs) _ hw) (W.inv_mem hw)
      rw [noncommPiCoprod_eq_mul_update hpw f k] at h2
      have e : s * ((f k : X) * noncommPiCoprod hpw (Function.update f k 1)) * s⁻¹ *
          ((f k : X) * noncommPiCoprod hpw (Function.update f k 1))⁻¹ =
          s * (f k : X) * s⁻¹ * (f k : X)⁻¹ := by
        calc _ = s * (f k : X) * (s⁻¹ * noncommPiCoprod hpw (Function.update f k 1)) *
              (noncommPiCoprod hpw (Function.update f k 1))⁻¹ * (f k : X)⁻¹ := by
              rw [hrs]
              group
          _ = _ := by group
      rwa [e] at h2
    rw [hex k k.2, mem_bot] at h1
    exact mul_inv_eq_one.1 h1
  have hf1 : f = 1 := funext fun k => Subtype.ext (hf k)
  rw [hf1, map_one]
  exact one_mem _

theorem irred_K : IrredOnFrattiniQuot (orbK Tb A C F H₁ ⊓ Tb) (orb C X₁) := by
  have hΦ := nineFrattini_eq_bot d.irr.prime d.XB_elem
  have hX₁ : X₁ ≠ ⊥ := fun h => by
    have := d.irr.irred.1
    rw [h] at this
    exact not_lt_bot this
  refine ⟨?_, fun W _ hWX hW => ?_⟩
  · rw [hΦ, bot_lt_iff_ne_bot]
    exact fun h => hX₁ (le_bot_iff.1 (h ▸ le_orb C X₁))
  rw [hΦ]
  by_cases hex : ∃ c ∈ C, W ⊓ conjSub c X₁ ≠ ⊥
  · obtain ⟨c, hc, hne⟩ := hex
    exact Or.inr (d.eq_of_inf_ne_bot hWX hW hc hne)
  · push Not at hex
    exact Or.inl (d.eq_bot_of_inf_eq_bot hWX hW hex)

end OrbData

end CFSG.LocalAnalysis.WeakClosure81.TC914
