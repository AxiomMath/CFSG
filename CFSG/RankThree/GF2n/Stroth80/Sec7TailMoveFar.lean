module

public import CFSG.RankThree.GF2n.Stroth80.Sec7TailMoveRank
public import CFSG.RankThree.GF2n.Stroth80.Sec7TailMoveDim
public import CFSG.RankThree.GF2n.Stroth80.Sec7TailMoveYBasic

public section

namespace CFSG.RankThree.GF2n.Stroth80

open Subgroup CFSG.CGT.Timmesfeld75
open scoped commutatorElement

variable {K E X : Type*} [Field K] [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  [Group X] [Finite X]
  {B : LinearMap.BilinForm K E} {φ : X →* (E ≃ₗ[K] E)} {V L Nb Rb : Subgroup X}
  {Tt : X → Submodule K E} {q : ℕ}

@[expose] def LOpmSup (M : Subgroup X) (ψ : X →* (E ≃ₗ[K] E)) : Submodule K E :=
  ⨆ s : M, LinearMap.range (opm (ψ (s : X)))

theorem range_opm_le_LOpmSup {s : X} (hs : s ∈ L) :
    LinearMap.range (opm (φ s)) ≤ LOpmSup L φ :=
  le_iSup (fun t : L => LinearMap.range (opm (φ (t : X)))) ⟨s, hs⟩

theorem MoveFrame.LOpmSup_isotropic (F : MoveFrame B φ V L Nb Rb Tt q) :
    ∀ x ∈ LOpmSup L φ, ∀ y ∈ LOpmSup L φ, B x y = 0 :=
  iSup_range_opm_isotropic B F.nondeg F.refl (fun s : L => φ (s : X)) (fun s => F.isom (s : X))
    (fun i j z => F.quad i.1 i.2 j.1 j.2 z)

theorem MoveFrame.LOpmSup_le_orthogonal (F : MoveFrame B φ V L Nb Rb Tt q) :
    LOpmSup L φ ≤ B.orthogonal (Tt 1) := by
  unfold LOpmSup
  refine iSup_le fun s => ?_
  rintro _ ⟨z, rfl⟩
  rw [opm_apply]
  exact sub_mem_orthogonal_of_fixes B (φ (s : X)) (F.isom (s : X)) (Tt 1)
    (F.Nb_fixes (s : X) (F.L_le_Nb s.2)) z

theorem MoveFrame.LOpmSup_invariant (F : MoveFrame B φ V L Nb Rb Tt q) :
    ∀ r ∈ Rb, ∀ w ∈ LOpmSup L φ, φ r w ∈ LOpmSup L φ := by
  intro r hr w hw
  unfold LOpmSup at hw
  refine Submodule.iSup_induction (motive := fun z => φ r z ∈ LOpmSup L φ) _ hw ?_ ?_ ?_
  · rintro s _ ⟨u, rfl⟩
    show φ r (opm (φ (s : X)) u) ∈ LOpmSup L φ
    have hL : r * (s : X) * r⁻¹ ∈ L := F.L_norm r (F.Rb_le_K r hr) (s : X) s.2
    have e : φ r (opm (φ (s : X)) u) = opm (φ (r * (s : X) * r⁻¹)) (φ r u) := by
      rw [opm_conj φ r (s : X) (φ r u), phi_inv_apply_phi φ r u]
    rw [e]
    exact range_opm_le_LOpmSup hL (LinearMap.mem_range_self _ _)
  · show φ r 0 ∈ LOpmSup L φ
    rw [map_zero]
    exact Submodule.zero_mem _
  · intro x y hx hy
    show φ r (x + y) ∈ LOpmSup L φ
    rw [map_add]
    exact Submodule.add_mem _ hx hy

theorem MoveFrame.Tt_one_le_LOpmSup (F : MoveFrame B φ V L Nb Rb Tt q) :
    Tt 1 ≤ LOpmSup L φ := by
  obtain ⟨a, ha, h1⟩ := F.exists_ne_one
  rw [← F.range_opm_V ha h1]
  exact range_opm_le_LOpmSup (F.V_le_L ha)

theorem range_opm_mul_le_sup {y y' : X} {T T' : Submodule K E}
    (hy : LinearMap.range (opm (φ y)) ≤ T) (hy' : LinearMap.range (opm (φ y')) ≤ T') :
    LinearMap.range (opm (φ (y * y'))) ≤ T ⊔ T' := by
  rintro _ ⟨z, rfl⟩
  rw [map_mul, opm_mul]
  refine Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_
  · exact Submodule.mem_sup_left (hy (LinearMap.mem_range_self _ _))
  · exact Submodule.mem_sup_right (hy' (LinearMap.mem_range_self _ _))
  · exact Submodule.mem_sup_left (hy (LinearMap.mem_range_self _ _))

theorem MoveFrame.range_opm_mul_le_inf (F : MoveFrame B φ V L Nb Rb Tt q) {y y' : X}
    {T T' : Submodule K E} (hy : LinearMap.range (opm (φ y)) ≤ T)
    (hy' : LinearMap.range (opm (φ y')) ≤ T') (hL : y * y' ∈ L) :
    LinearMap.range (opm (φ (y * y'))) ≤ (T ⊔ T') ⊓ B.orthogonal (Tt 1) ⊓ LOpmSup L φ := by
  refine le_inf (le_inf (range_opm_mul_le_sup hy hy') ?_) (range_opm_le_LOpmSup hL)
  rintro _ ⟨z, rfl⟩
  rw [opm_apply]
  exact sub_mem_orthogonal_of_fixes B (φ (y * y')) (F.isom (y * y')) (Tt 1)
    (F.Nb_fixes (y * y') (F.L_le_Nb hL)) z

theorem MoveFrame.map_opm_le_of_inf (F : MoveFrame B φ V L Nb Rb Tt q) {y : X}
    (hy : y ∈ normalizer (V : Set X)) {S Lm : Submodule K E}
    (hS : LinearMap.range (opm (φ y)) ≤ S) (hLS : S ⊓ B.orthogonal (Tt 1) ≤ Lm) :
    (B.orthogonal (Tt 1)).map (opm (φ y)) ≤ Lm := by
  rintro _ ⟨w, hw, rfl⟩
  refine hLS (Submodule.mem_inf.mpr ⟨hS (LinearMap.mem_range_self _ _), ?_⟩)
  rw [opm_apply]
  exact Submodule.sub_mem _ (F.map_orthogonal_le hy hw) hw

theorem conj_pair_eq (h x b : X) : x * (h * b * h⁻¹) * x⁻¹ = (x * h) * b * (x * h)⁻¹ := by
  group

theorem MoveFrame.Y_x_conj_mem_Rb (F : MoveFrame B φ V L Nb Rb Tt q) (h x : X)
    (H : ∀ a ∈ V, ∀ b ∈ V, (h * a * h⁻¹) * ((x * h) * b * (x * h)⁻¹) =
      ((x * h) * b * (x * h)⁻¹) * (h * a * h⁻¹)) {b : X} (hb : b ∈ V) :
    h⁻¹ * ((x * h) * b * (x * h)⁻¹) * h ∈ Rb := by
  obtain ⟨a, ha, ha1⟩ := F.exists_ne_one
  have hz : h * a * h⁻¹ ∈ conjSubgroup h V := mem_conjSubgroup_iff'.mpr ⟨a, ha, rfl⟩
  have hz1 : h * a * h⁻¹ ≠ 1 := by
    intro e
    apply ha1
    calc a = h⁻¹ * (h * a * h⁻¹) * h := by group
      _ = 1 := by rw [e]; group
  have hg : ((x * h) * b * (x * h)⁻¹) * (h * a * h⁻¹) * ((x * h) * b * (x * h)⁻¹)⁻¹ ∈
      conjSubgroup h V := by
    have e : ((x * h) * b * (x * h)⁻¹) * (h * a * h⁻¹) * ((x * h) * b * (x * h)⁻¹)⁻¹ =
        h * a * h⁻¹ := by
      rw [← H a ha b hb]
      group
    rw [e]
    exact hz
  have hk : h⁻¹ * ((x * h) * b * (x * h)⁻¹) * h ∈ normalizer (V : Set X) :=
    mem_normalizer_conjSubgroup_iff.mp (F.ti_conj h ((x * h) * b * (x * h)⁻¹) hz hz1 hg)
  have hkc : ∀ a' ∈ V, (h⁻¹ * ((x * h) * b * (x * h)⁻¹) * h) * a' =
      a' * (h⁻¹ * ((x * h) * b * (x * h)⁻¹) * h) := by
    intro a' ha'
    have hc : ((x * h) * b * (x * h)⁻¹) * (h * a' * h⁻¹) =
        (h * a' * h⁻¹) * ((x * h) * b * (x * h)⁻¹) := (H a' ha' b hb).symm
    calc h⁻¹ * ((x * h) * b * (x * h)⁻¹) * h * a'
        = h⁻¹ * (((x * h) * b * (x * h)⁻¹) * (h * a' * h⁻¹)) * h := by group
      _ = h⁻¹ * ((h * a' * h⁻¹) * ((x * h) * b * (x * h)⁻¹)) * h := by rw [hc]
      _ = a' * (h⁻¹ * ((x * h) * b * (x * h)⁻¹) * h) := by group
  have hyy : ((x * h) * b * (x * h)⁻¹) * ((x * h) * b * (x * h)⁻¹) = 1 := by
    calc ((x * h) * b * (x * h)⁻¹) * ((x * h) * b * (x * h)⁻¹)
        = (x * h) * (b * b) * (x * h)⁻¹ := by group
      _ = 1 := by rw [F.V_sq b hb]; group
  have hkk : (h⁻¹ * ((x * h) * b * (x * h)⁻¹) * h) * (h⁻¹ * ((x * h) * b * (x * h)⁻¹) * h) =
      1 := by
    calc (h⁻¹ * ((x * h) * b * (x * h)⁻¹) * h) * (h⁻¹ * ((x * h) * b * (x * h)⁻¹) * h)
        = h⁻¹ * (((x * h) * b * (x * h)⁻¹) * ((x * h) * b * (x * h)⁻¹)) * h := by group
      _ = 1 := by rw [hyy]; group
  exact F.two_elements _ hk hkc (isPGroup_two_zpowers_of_sq hkk)

theorem MoveFrame.finrank_mul_ge_eight (F : MoveFrame B φ V L Nb Rb Tt q) {y y' : X}
    (hcomm : y * y' = y' * y) (hy2 : ∀ w, opm (φ y) (opm (φ y) w) = 0)
    (hy2' : ∀ w, opm (φ y') (opm (φ y') w) = 0)
    (hT : Module.finrank K (LinearMap.range (opm (φ y))) = 6)
    (hT' : Module.finrank K (LinearMap.range (opm (φ y'))) = 6)
    (hi : Module.finrank K ↥(LinearMap.range (opm (φ y)) ⊓ LinearMap.range (opm (φ y'))) = 2) :
    8 ≤ Module.finrank K (LinearMap.range (opm (φ (y * y')))) := by
  have hab : φ y * φ y' = φ y' * φ y := by
    rw [← map_mul φ, ← map_mul φ, hcomm]
  have h := finrank_range_opm_mul_ge B F.nondeg F.refl F.char2 (φ y) (φ y') (F.isom y)
    (F.isom y') hab hy2 hy2' 6 2 hT hT' hi
  rw [← map_mul φ] at h
  omega

theorem MoveFrame.finrank_mul_le_seven (F : MoveFrame B φ V L Nb Rb Tt q) {g₁ g₂ y y' : X}
    (hy : LinearMap.range (opm (φ y)) = Tt g₁) (hy' : LinearMap.range (opm (φ y')) = Tt g₂)
    (hL : y * y' ∈ L) (h2 : 2 ≤ Module.finrank K ↥(Tt g₁ ⊓ Tt g₂))
    (hS : 2 ≤ Module.finrank K ↥((Tt g₁ ⊔ Tt g₂).map (B.orthogonal (Tt 1)).mkQ))
    (hnot : ¬ ((Tt g₁ ⊔ Tt g₂) ⊓ B.orthogonal (Tt 1) ≤ LOpmSup L φ)) :
    Module.finrank K (LinearMap.range (opm (φ (y * y')))) ≤ 7 := by
  have hu := F.range_opm_mul_le_inf hy.le hy'.le hL
  exact finrank_range_le_seven (Tt g₁) (Tt g₂) (B.orthogonal (Tt 1)) (LOpmSup L φ)
    (opm (φ (y * y'))) (F.Tt_rank g₁) (F.Tt_rank g₂) h2 hS hu hnot

theorem MoveFrame.Y_x_le_NbY (F : MoveFrame B φ V L Nb Rb Tt q) (h : X)
    (hK : ∀ a ∈ V, h * a * h⁻¹ ∈ normalizer (V : Set X))
    (hN : ¬ ∀ a ∈ V, h * a * h⁻¹ ∈ Nb)
    (hcomm : ∀ v ∈ V, ∀ a ∈ V, v * (h * a * h⁻¹) = (h * a * h⁻¹) * v)
    (hRb : ∀ a ∈ V, h * a * h⁻¹ ∈ Rb)
    (hYx : ∀ x ∈ L, ∀ a ∈ V, ∀ b ∈ V,
      (h * a * h⁻¹) * (x * (h * b * h⁻¹) * x⁻¹) = (x * (h * b * h⁻¹) * x⁻¹) * (h * a * h⁻¹)) :
    ∀ x ∈ L, ∀ b ∈ V, h⁻¹ * (x * (h * b * h⁻¹) * x⁻¹) * h ∈ Nb := by
  intro x hx b₀ hb₀
  by_contra hcon
  have hpair : ∀ a ∈ V, ∀ b ∈ V, (h * a * h⁻¹) * ((x * h) * b * (x * h)⁻¹) =
      ((x * h) * b * (x * h)⁻¹) * (h * a * h⁻¹) := by
    intro a ha b hb
    have e := hYx x hx a ha b hb
    rwa [conj_pair_eq h x b] at e
  have hneg : ¬ ∀ b ∈ V, h⁻¹ * ((x * h) * b * (x * h)⁻¹) * h ∈ Nb := by
    intro H
    apply hcon
    have e := H b₀ hb₀
    rwa [← conj_pair_eq h x b₀] at e
  have hRb' : ∀ b ∈ V, h⁻¹ * ((x * h) * b * (x * h)⁻¹) * h ∈ Rb :=
    fun b hb => F.Y_x_conj_mem_Rb h x hpair hb
  have hpd : Module.finrank K ↥(Tt h ⊓ Tt (x * h)) = 2 :=
    F.pair_dim h (x * h) hpair hRb' hneg
  obtain ⟨a, ha, ha1⟩ := F.exists_ne_one
  have hyR : LinearMap.range (opm (φ (h * a * h⁻¹))) = Tt h := F.Tt_range h a ha ha1
  have hy'R : LinearMap.range (opm (φ ((x * h) * a * (x * h)⁻¹))) = Tt (x * h) :=
    F.Tt_range (x * h) a ha ha1
  have hyy : (h * a * h⁻¹) * (h * a * h⁻¹) = 1 := by
    calc (h * a * h⁻¹) * (h * a * h⁻¹) = h * (a * a) * h⁻¹ := by group
      _ = 1 := by rw [F.V_sq a ha]; group
  have hyinv : (h * a * h⁻¹)⁻¹ = h * a * h⁻¹ := inv_eq_of_mul_eq_one_right hyy
  have hL : (h * a * h⁻¹) * ((x * h) * a * (x * h)⁻¹) ∈ L := by
    have e : (h * a * h⁻¹) * ((x * h) * a * (x * h)⁻¹) =
        (h * a * h⁻¹ * x * (h * a * h⁻¹)⁻¹) * x⁻¹ := by
      rw [hyinv]
      group
    rw [e]
    exact L.mul_mem (F.L_norm _ (hK a ha) x hx) (L.inv_mem hx)
  have hcomm_a : (h * a * h⁻¹) * ((x * h) * a * (x * h)⁻¹) =
      ((x * h) * a * (x * h)⁻¹) * (h * a * h⁻¹) := hpair a ha a ha
  have hS : 2 ≤ Module.finrank K ↥((Tt h ⊔ Tt (x * h)).map (B.orthogonal (Tt 1)).mkQ) :=
    le_trans (F.image_dim h hRb hN)
      (Submodule.finrank_mono (Submodule.map_mono (le_sup_left : Tt h ≤ Tt h ⊔ Tt (x * h))))
  have hnot : ¬ ((Tt h ⊔ Tt (x * h)) ⊓ B.orthogonal (Tt 1) ≤ LOpmSup L φ) := fun hle =>
    F.no_isotropic h hRb hN (LOpmSup L φ) F.Tt_one_le_LOpmSup F.LOpmSup_le_orthogonal
      F.LOpmSup_invariant F.LOpmSup_isotropic a ha ha1
      (F.map_opm_le_of_inf (hK a ha) (hyR.le.trans (le_sup_left : Tt h ≤ Tt h ⊔ Tt (x * h)))
        hle)
  have hlow := F.finrank_mul_ge_eight hcomm_a (F.opm_sq ha h) (F.opm_sq ha (x * h))
    (by rw [hyR]; exact F.Tt_rank h) (by rw [hy'R]; exact F.Tt_rank (x * h))
    (by rw [hyR, hy'R]; exact hpd)
  have hup := F.finrank_mul_le_seven hyR hy'R hL hpd.ge hS hnot
  omega

end CFSG.RankThree.GF2n.Stroth80
