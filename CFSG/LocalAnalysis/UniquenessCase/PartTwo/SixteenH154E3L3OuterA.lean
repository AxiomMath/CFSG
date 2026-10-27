module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3L3Twist
import CFSG.Quasithin.Background.StabSubBasics
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3Fix
public import CFSG.Quasithin.Background.B4L3Coord

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup

variable {W : Type} [CommGroup W] [Finite W]

private theorem s16h_e3_l3_map_eq_self_of_mapsTo {Z : Subgroup W} {τ : MulAut W}
    (h : ∀ z ∈ Z, τ z ∈ Z) : Z.map τ.toMonoidHom = Z := by
  refine Subgroup.eq_of_le_of_card_ge ?_ ?_
  · rintro _ ⟨z, hz, rfl⟩
    exact h z hz
  · exact (Subgroup.card_map_of_injective (f := τ.toMonoidHom) τ.injective).ge

omit [Finite W] in
private theorem s16h_e3_l3_inv_mem_of_map_eq {Z : Subgroup W} {τ : MulAut W}
    (h : Z.map τ.toMonoidHom = Z) {z : W} (hz : z ∈ Z) : τ⁻¹ z ∈ Z := by
  have hz' : z ∈ Z.map τ.toMonoidHom := by rw [h]; exact hz
  obtain ⟨y, hy, hyz⟩ := hz'
  have : y = τ⁻¹ z := by
    rw [← hyz]
    simp
  rwa [this] at hy

theorem s16h_e3_l3_inf_map_eq_of_not_inner {L : Subgroup (MulAut W)} {I Z : Subgroup W}
    (hI : BinaryNaturalSL L I Z 3 1) {τ : MulAut W}
    (hτN : τ ∈ Subgroup.normalizer (L : Set (MulAut W))) (hτZ : ∀ z ∈ Z, τ z ∈ Z)
    (hout : ¬ ∃ γ ∈ L, ∀ l ∈ L, τ * l * τ⁻¹ = γ * l * γ⁻¹) :
    I ⊓ I.map τ.toMonoidHom = Z := by
  classical
  obtain ⟨D⟩ := BinaryNaturalSL.toL3Coord hI
  have hZmap : Z.map τ.toMonoidHom = Z := s16h_e3_l3_map_eq_self_of_mapsTo hτZ
  set X : Subgroup W := I ⊓ I.map τ.toMonoidHom with hX
  have hXI : X ≤ I := by rw [hX]; exact inf_le_left
  have hXmap : X ≤ I.map τ.toMonoidHom := by rw [hX]; exact inf_le_right
  have hZX : Z ≤ X := by
    intro z hz
    rw [hX]
    exact ⟨D.Z_le hz, ⟨τ⁻¹ z, D.Z_le (s16h_e3_l3_inv_mem_of_map_eq hZmap hz), by simp⟩⟩
  by_contra hne
  have hXZle : ¬ X ≤ Z := fun h => hne (le_antisymm h hZX)
  obtain ⟨x, hxX, hxZ⟩ := Set.not_subset.1 hXZle
  have hxI : x ∈ I := hXI hxX
  let fX : ↥X →* Multiplicative L3.Vec := D.β.comp (Subgroup.inclusion hXI)
  let B : Subgroup (Multiplicative L3.Vec) := fX.range
  have hv : fX ⟨x, hxX⟩ ≠ 1 := by
    intro h
    exact hxZ ((D.ker_β ⟨x, hxI⟩).1 h)
  have hXinv : ∀ l ∈ L, ∀ z ∈ X, l z ∈ X := by
    intro l hl z hz
    rw [hX]
    obtain ⟨w, hw, hwz⟩ := hXmap hz
    refine ⟨D.inv_U l hl z (hXI hz), ?_⟩
    refine ⟨(τ⁻¹ * l * τ) w,
      D.inv_U _ ((Subgroup.mem_normalizer_iff''.1 hτN l).1 hl) w hw, ?_⟩
    rw [← hwz]
    show τ ((τ⁻¹ * l * τ) w) = l (τ w)
    simp only [MulAut.mul_apply, MulAut.apply_inv_self]
  have hBinv : ∀ (γ : L3.Γ) (b : Multiplicative L3.Vec), b ∈ B →
      Multiplicative.ofAdd (L3.act γ (Multiplicative.toAdd b)) ∈ B := by
    intro γ b hb
    obtain ⟨y, rfl⟩ := MonoidHom.mem_range.1 hb
    refine MonoidHom.mem_range.2 ⟨⟨D.rho γ (y : W),
      hXinv (D.rho γ) (D.rho_mem γ) y y.2⟩, ?_⟩
    exact D.β_rho γ (y : W) (hXI y.2)
      (hXI (hXinv (D.rho γ) (D.rho_mem γ) y y.2))
  have hBtop : B = ⊤ := by
    rw [eq_top_iff]
    intro b _
    by_cases hb1 : b = 1
    · rw [hb1]; exact B.one_mem
    · have hb0 : Multiplicative.toAdd b ≠ 0 := fun h =>
        hb1 (by
          have := congrArg Multiplicative.ofAdd h
          simpa using this)
      have hv0 : Multiplicative.toAdd (fX ⟨x, hxX⟩) ≠ 0 := fun h =>
        hv (by
          have := congrArg Multiplicative.ofAdd h
          simpa using this)
      obtain ⟨γ, hγ⟩ := L3.act_trans (Multiplicative.toAdd (fX ⟨x, hxX⟩))
        (Multiplicative.toAdd b) hv0 hb0
      have hmem := hBinv γ (fX ⟨x, hxX⟩)
        (MonoidHom.mem_range.2 ⟨⟨x, hxX⟩, rfl⟩)
      rw [hγ] at hmem
      simpa using hmem
  have hIle : I ≤ X := by
    intro u hu
    have hmemB : D.β ⟨u, hu⟩ ∈ B := by
      rw [hBtop]
      exact Subgroup.mem_top _
    obtain ⟨y, hyβ⟩ := MonoidHom.mem_range.1 hmemB
    have h2 : D.β (Subgroup.inclusion hXI y) = D.β ⟨u, hu⟩ := hyβ
    have h1 : D.β (⟨u, hu⟩ * (Subgroup.inclusion hXI y)⁻¹) = 1 := by
      rw [map_mul, map_inv, h2]
      exact mul_inv_cancel _
    have hz : u * (y : W)⁻¹ ∈ Z := by
      simpa using (D.ker_β (⟨u, hu⟩ * (Subgroup.inclusion hXI y)⁻¹)).1 h1
    have hmul : u * (y : W)⁻¹ * (y : W) ∈ X := X.mul_mem (hZX hz) y.2
    simpa only [mul_assoc, inv_mul_cancel, mul_one] using hmul
  have hXeq : X = I := le_antisymm hXI hIle
  have hI_le_map : I ≤ I.map τ.toMonoidHom := (le_of_eq hXeq.symm).trans hXmap
  have hImap : I = I.map τ.toMonoidHom :=
    Subgroup.eq_of_le_of_card_ge hI_le_map
      (le_of_eq (Subgroup.card_map_of_injective (f := τ.toMonoidHom) τ.injective))
  have hτI : ∀ u ∈ I, τ u ∈ I := by
    intro u hu
    have : τ u ∈ I.map τ.toMonoidHom := Subgroup.mem_map_of_mem τ.toMonoidHom hu
    rw [hImap]
    exact this
  exact hout (s16h_e3_l3_inner_of_stab hI hτN hτI hτZ)

theorem s16h_e3_l3_section_outer {L : Subgroup (MulAut W)} {k : ℕ} (hk : 1 ≤ k)
    (hL3 : s16h_H5L3Sum L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) k) {τ : MulAut W}
    (hτN : τ ∈ Subgroup.normalizer (L : Set (MulAut W)))
    (hout : ¬ ∃ γ ∈ L, ∀ l ∈ L, τ * l * τ⁻¹ = γ * l * γ⁻¹) :
    rk ↥(commSub ⊤ L ⊓ fixV L) + 3 ≤
      rk ↥(commSub (commSub ⊤ L) (Subgroup.zpowers τ) ⊔ (commSub ⊤ L ⊓ fixV L)) := by
  classical
  set U : Subgroup W := commSub (⊤ : Subgroup W) L with hU
  set Z : Subgroup W := U ⊓ fixV L with hZ
  have hL3' : s16h_H5L3Sum L U Z k := hL3
  have hτstabU : τ ∈ stabSub U := by
    rw [hU]
    exact StabLat.mem_stabSub_commSub (X := L) (Y := ⊤) (g := τ)
      (mem_stabSub.2 fun u => by simp) hτN
  have hτU : ∀ u ∈ U, τ u ∈ U := fun u hu => (mem_stabSub.mp hτstabU u).2 hu
  have hτF : ∀ z ∈ fixV L, τ z ∈ fixV L :=
    fun z hz => fixV_apply_mem_of_mem_normalizer (L := L) hτN hz
  have hτZ : ∀ z ∈ Z, τ z ∈ Z := by
    intro z hz
    rw [hZ] at hz ⊢
    exact ⟨hτU z hz.1, hτF z hz.2⟩
  obtain ⟨-, hsum⟩ := hL3'
  obtain ⟨I, hZI, -, hsup, hnat⟩ := hsum
  let i₀ : Fin k := ⟨0, by omega⟩
  have hI₀ : BinaryNaturalSL L (I i₀) Z 3 1 := hnat i₀
  have hI₀_le_U : I i₀ ≤ U := by
    rw [← hsup]
    exact (le_iSup I i₀).trans le_sup_right
  have hinf : I i₀ ⊓ (I i₀).map τ.toMonoidHom = Z :=
    s16h_e3_l3_inf_map_eq_of_not_inner hI₀ hτN hτZ hout
  obtain ⟨D⟩ := BinaryNaturalSL.toL3Coord hI₀
  have hZmap : Z.map τ.toMonoidHom = Z := s16h_e3_l3_map_eq_self_of_mapsTo hτZ
  let φ : W →* W :=
    { toFun := fun w => τ w * w⁻¹
      map_one' := by simp
      map_mul' := fun a b => by
        simp only [map_mul, mul_inv_rev]
        ac_rfl }
  let A : Subgroup W := (I i₀).map φ
  let ψ : W →* W ⧸ Z := (QuotientGroup.mk' Z).comp φ
  have hA_le : A ≤ commSub U (Subgroup.zpowers τ) := by
    change (I i₀).map φ ≤ commSub U (Subgroup.zpowers τ)
    rw [Subgroup.map_le_iff_le_comap]
    intro u hu
    show τ u * u⁻¹ ∈ commSub U (Subgroup.zpowers τ)
    exact Subgroup.subset_closure ⟨τ, Subgroup.mem_zpowers τ, u, hI₀_le_U hu, rfl⟩
  have hphiZ : ∀ u ∈ I i₀, φ u ∈ Z ↔ u ∈ Z := by
    intro u hu
    constructor
    · intro h
      have hφI : φ u ∈ I i₀ := hZI i₀ h
      have hτu : τ u ∈ I i₀ := by
        have htu : τ u = φ u * u := by
          show τ u = τ u * u⁻¹ * u
          group
        rw [htu]
        exact (I i₀).mul_mem hφI hu
      have hmem : τ u ∈ I i₀ ⊓ (I i₀).map τ.toMonoidHom :=
        ⟨hτu, Subgroup.mem_map_of_mem τ.toMonoidHom hu⟩
      rw [hinf] at hmem
      have := s16h_e3_l3_inv_mem_of_map_eq hZmap hmem
      simpa using this
    · intro huZ
      exact Z.mul_mem (hτZ u huZ) (Z.inv_mem huZ)
  have hker : I i₀ ⊓ ψ.ker = Z := by
    apply le_antisymm
    · intro u hu
      rw [Subgroup.mem_inf] at hu
      have h2 : φ u ∈ Z := by
        have h1 : ψ u = 1 := MonoidHom.mem_ker.1 hu.2
        rw [show ψ u = (QuotientGroup.mk (φ u) : W ⧸ Z) from rfl] at h1
        exact (QuotientGroup.eq_one_iff (φ u)).1 h1
      exact (hphiZ u hu.1).1 h2
    · intro u hu
      refine Subgroup.mem_inf.2 ⟨hZI i₀ hu, ?_⟩
      change ψ u = 1
      rw [show ψ u = (QuotientGroup.mk (φ u) : W ⧸ Z) from rfl]
      exact (QuotientGroup.eq_one_iff (φ u)).2 ((hphiZ u (hZI i₀ hu)).2 hu)
  have hcardψ : Nat.card ↥((I i₀).map ψ) * Nat.card Z = 8 * Nat.card Z := by
    have h := B1More.card_map_mul_card_inf_ker (I i₀) ψ
    rw [hker, D.card_U] at h
    exact h
  have hψcard : Nat.card ↥((I i₀).map ψ) = 8 :=
    Nat.mul_right_cancel (card_subgroup_pos Z) hcardψ
  have hmap : (I i₀).map ψ = (A ⊔ Z).map (QuotientGroup.mk' Z) := by
    have h1 : (I i₀).map ψ = A.map (QuotientGroup.mk' Z) := by
      change (I i₀).map ((QuotientGroup.mk' Z).comp φ) = A.map (QuotientGroup.mk' Z)
      rw [show A = (I i₀).map φ from rfl]
      exact (Subgroup.map_map (K := I i₀) (g := QuotientGroup.mk' Z) (f := φ)).symm
    rw [h1]
    have hZbot : Z.map (QuotientGroup.mk' Z) = ⊥ :=
      (Subgroup.map_eq_bot_iff (H := Z) (f := QuotientGroup.mk' Z)).2
        (by rw [QuotientGroup.ker_mk'])
    rw [Subgroup.map_sup, hZbot, sup_bot_eq]
  have hcardA : Nat.card ↥(A ⊔ Z) = 8 * Nat.card Z := by
    have h := B1More.card_map_mul_card_inf_ker (A ⊔ Z) (QuotientGroup.mk' Z)
    have hkerA : (A ⊔ Z) ⊓ (QuotientGroup.mk' Z).ker = Z := by
      rw [QuotientGroup.ker_mk']
      exact inf_eq_right.mpr le_sup_right
    rw [hkerA, ← hmap, hψcard] at h
    exact h.symm
  have hrankA : rk ↥(A ⊔ Z) = rk ↥Z + 3 := by
    unfold rk
    rw [hcardA, show (8 : ℕ) = 2 ^ 3 by norm_num,
      padicValNat.mul (by norm_num) (card_subgroup_pos Z).ne', padicValNat.prime_pow]
    omega
  have hmono : rk ↥(A ⊔ Z) ≤ rk ↥(commSub U (Subgroup.zpowers τ) ⊔ Z) :=
    rk_mono (sup_le_sup_right hA_le Z)
  rw [hrankA] at hmono
  exact hmono

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
