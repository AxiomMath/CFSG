module

public import CFSG.LocalAnalysis.StandardType.GGInterfaceSix
public import CFSG.Assembly.Subnormal

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank

section Subnormal

variable {G : Type*} [Group G]

theorem ggIsSubnormal_le {H K : Subgroup G} (h : IsSubnormal H K) : H ≤ K :=
  h.le

theorem ggIsSubnormal_trans {A B C : Subgroup G} (h₁ : IsSubnormal A B)
    (h₂ : IsSubnormal B C) : IsSubnormal A C :=
  h₁.trans h₂

theorem ggIsSubnormal_of_normal {A B : Subgroup G} (hle : A ≤ B)
    (hN : (A.subgroupOf B).Normal) : IsSubnormal A B :=
  IsSubnormal.step hle hN (IsSubnormal.refl B)

theorem ggIsSubnormal_inf {A X : Subgroup G} (h : IsSubnormal A X) (Y : Subgroup G) :
    IsSubnormal (A ⊓ Y) (X ⊓ Y) :=
  h.inf Y

theorem ggIsSubnormal_of_le_of_le {A X Y : Subgroup G} (h : IsSubnormal A X) (hAY : A ≤ Y)
    (hYX : Y ≤ X) : IsSubnormal A Y := by
  have h' := ggIsSubnormal_inf h Y
  rwa [inf_eq_left.mpr hAY, inf_eq_right.mpr hYX] at h'

theorem ggMem_normalizer_of_normal {H M : Subgroup G} (hle : H ≤ M)
    (hN : (H.subgroupOf M).Normal) {m : G} (hm : m ∈ M) :
    m ∈ Subgroup.normalizer (H : Set G) := by
  have hN' := (Subgroup.normal_subgroupOf_iff hle).mp hN
  refine Subgroup.mem_normalizer_iff.mpr fun h => ⟨fun hh => hN' h m hh hm, fun hh => ?_⟩
  have h' := hN' _ m⁻¹ hh (M.inv_mem hm)
  simpa [mul_assoc] using h'

theorem ggIsSubnormal_sup_zpowers {A X : Subgroup G} (h : IsSubnormal A X) {z : G}
    (hz : z ∈ Subgroup.centralizer (X : Set G)) :
    IsSubnormal (Subgroup.zpowers z ⊔ A) (Subgroup.zpowers z ⊔ X) := by
  induction h with
  | refl => exact IsSubnormal.refl _
  | @step H M K hle hN hMK ih =>
    refine IsSubnormal.step (sup_le_sup_left hle _) ?_ (ih hz)
    have hzM : ∀ m ∈ M, m * z = z * m := fun m hm =>
      (Subgroup.mem_centralizer_iff.mp hz m (ggIsSubnormal_le hMK hm))
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer (sup_le_sup_left hle _)]
    refine sup_le ?_ fun m hm => ?_
    · rw [Subgroup.zpowers_le]
      exact Subgroup.le_normalizer (le_sup_left (a := Subgroup.zpowers z) (Subgroup.mem_zpowers z))
    · apply mem_normalizer_of_map_conj_eq
      have hmH := ggMem_normalizer_of_normal hle hN hm
      have hHm : H.map (MulAut.conj m).toMonoidHom = H := by
        refine le_antisymm ?_ fun h hh => ?_
        · rintro _ ⟨h, hh, rfl⟩
          exact (Subgroup.mem_normalizer_iff.mp hmH h).mp hh
        · have h' := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hmH) h).mp hh
          rw [inv_inv] at h'
          exact ⟨m⁻¹ * h * m, h', by simp [MulAut.conj_apply, mul_assoc]⟩
      rw [Subgroup.map_sup, hHm, MonoidHom.map_zpowers]
      congr 2
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [hzM m hm, mul_inv_cancel_right]

end Subnormal

section Fusion

variable {G : Type*} [Group G]

@[expose] def GGControlsStrongFusionIn (X H E : Subgroup G) : Prop :=
  E ≤ H ∧ H ≤ X ∧ ∀ g ∈ X, E.map (MulAut.conj g⁻¹).toMonoidHom ⊓ H ≠ ⊥ → g ∈ H

theorem GGControlsStrongFusion.inf_in {H E N : Subgroup G} (h : GGControlsStrongFusion H E)
    (hEN : E ≤ N) : GGControlsStrongFusionIn N (H ⊓ N) E := by
  refine ⟨le_inf h.1 hEN, inf_le_right, fun g hg hne => Subgroup.mem_inf.mpr ⟨h.2 g ?_, hg⟩⟩
  intro hbot
  apply hne
  rw [eq_bot_iff] at hbot ⊢
  exact le_trans (inf_le_inf_left _ inf_le_left) hbot

theorem GGControlsStrongFusion.mono_stepTwo {H E R : Subgroup G} (h : GGControlsStrongFusion H E)
    (hRE : R ≤ E) : GGControlsStrongFusion H R :=
  ggControlsStrongFusion_iff.mpr ⟨hRE.trans h.1, fun _ hr hr1 _ hg =>
    h.mem_of_conj_mem (hRE hr) hr1 hg⟩

theorem GGControlsStrongFusion.of_map_conj_le {H E R : Subgroup G}
    (h : GGControlsStrongFusion H E) {n : G} (hn : n ∈ H)
    (hR : R.map (MulAut.conj n⁻¹).toMonoidHom ≤ E) : GGControlsStrongFusion H R := by
  have hmem : ∀ r ∈ R, n⁻¹ * r * n ∈ E := fun r hr => by
    have h' := hR (Subgroup.mem_map_of_mem _ hr)
    simpa [MulAut.conj_apply] using h'
  refine ggControlsStrongFusion_iff.mpr ⟨fun r hr => ?_, fun r hr hr1 g hg => ?_⟩
  · have h' := H.mul_mem (H.mul_mem hn (h.1 (hmem r hr))) (H.inv_mem hn)
    simpa [mul_assoc] using h'
  · have he1 : n⁻¹ * r * n ≠ 1 := fun h1 => hr1 (by
      calc r = n * (n⁻¹ * r * n) * n⁻¹ := by group
        _ = 1 := by rw [h1]; group)
    have hg' : (n⁻¹ * g)⁻¹ * (n⁻¹ * r * n) * (n⁻¹ * g) ∈ H := by
      have heq : (n⁻¹ * g)⁻¹ * (n⁻¹ * r * n) * (n⁻¹ * g) = g⁻¹ * r * g := by group
      rw [heq]
      exact hg
    have h' := H.mul_mem hn (h.mem_of_conj_mem (hmem r hr) he1 hg')
    simpa using h'

end Fusion

section Defs

variable {G : Type} [Group G] [Finite G]

@[expose] def GGStepTwoPair (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G) (b : G)
    (L₁ : Subgroup G) : Prop :=
  b ∈ Bs ∧ b ≠ 1 ∧ IsComponentOf L₁ (ggG0 p B x L D J ⊓ Subgroup.centralizer {b}) ∧
    Nat.card (Bs ⊓ Subgroup.centralizer (L₁ : Set G) : Subgroup G) ≤ p ^ 2

end Defs

@[expose] def GGStepTwoLinearType (p : ℕ) (t : StatedLieTag) (f : ℕ) : Prop :=
  (t = .PSL ∧ p ∣ 2 ^ f - 1) ∨ (t = .PSU ∧ p ∣ 2 ^ f + 1)

section Steps

variable {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
  {L D J : Subgroup G}

omit [Finite G] in
theorem ggStepTwo_inf_normal (G₀ : Subgroup G) (b : G) :
    ((G₀ ⊓ Subgroup.centralizer {b}).subgroupOf
      (Subgroup.normalizer (G₀ : Set G) ⊓ Subgroup.centralizer {b})).Normal := by
  rw [Subgroup.normal_subgroupOf_iff (inf_le_inf_right _ Subgroup.le_normalizer)]
  intro h k hh hk
  obtain ⟨hhG, hhC⟩ := Subgroup.mem_inf.mp hh
  obtain ⟨hkN, hkC⟩ := Subgroup.mem_inf.mp hk
  exact Subgroup.mem_inf.mpr ⟨(Subgroup.mem_normalizer_iff.mp hkN h).mp hhG,
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hkC hhC) (Subgroup.inv_mem _ hkC)⟩

namespace GGStepTwoPair

variable {b : G} {L₁ : Subgroup G}

theorem isComponentOf_inf (h : GGStepTwoPair p B Bs x L D J b L₁) :
    IsComponentOf L₁ (ggM p B x L D J ⊓ Subgroup.centralizer {b}) := by
  obtain ⟨-, -, ⟨hle, hsn, hq⟩, -⟩ := h
  have hle' : ggG0 p B x L D J ⊓ Subgroup.centralizer {b} ≤
      ggM p B x L D J ⊓ Subgroup.centralizer {b} :=
    inf_le_inf_right _ Subgroup.le_normalizer
  exact ⟨hle.trans hle', ggIsSubnormal_trans hsn
    (ggIsSubnormal_of_normal hle' (ggStepTwo_inf_normal _ b)), hq⟩

theorem le_ggM (h : GGStepTwoPair p B Bs x L D J b L₁) : L₁ ≤ ggM p B x L D J :=
  h.isComponentOf_inf.1.trans inf_le_left

theorem le_centralizer (h : GGStepTwoPair p B Bs x L D J b L₁) :
    L₁ ≤ Subgroup.centralizer {b} :=
  h.2.2.1.1.trans inf_le_right

theorem isSubnormal_of_centralizer_le (h : GGStepTwoPair p B Bs x L D J b L₁)
    (hC : Subgroup.centralizer {b} ≤ ggM p B x L D J) :
    IsSubnormal L₁ (Subgroup.centralizer {b}) := by
  have h' := h.isComponentOf_inf.2.1
  rwa [inf_eq_right.mpr hC] at h'

theorem centralizer_le_of_mem (h : GGStepTwoPair p B Bs x L D J b L₁)
    (hBsM : Bs ≤ ggM p B x L D J) (hD : GGControlsStrongFusion (ggM p B x L D J) D)
    (hsn : IsSubnormal L₁ (Subgroup.centralizer {b})) {d : G} (hdD : d ∈ D) (hd1 : d ≠ 1)
    (hdR : d ∈ Subgroup.zpowers b ⊔ L₁) : Subgroup.centralizer {b} ≤ ggM p B x L D J := by
  have hbC : b ∈ Subgroup.centralizer (Subgroup.centralizer {b} : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun g hg => Subgroup.mem_centralizer_singleton_iff.mp hg
  have hsn' := ggIsSubnormal_sup_zpowers hsn hbC
  have htop : Subgroup.zpowers b ⊔ Subgroup.centralizer {b} = Subgroup.centralizer {b} :=
    sup_eq_right.mpr (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr rfl))
  rw [htop] at hsn'
  exact hD.le_of_isSubnormal hdD hd1 hdR
    (sup_le (Subgroup.zpowers_le.mpr (hBsM h.1)) h.le_ggM) hsn'

theorem stepTwo_of_fusion (h : GGStepTwoPair p B Bs x L D J b L₁) (hp : p.Prime)
    (hBs : IsElemAbelian p Bs) (hBsM : Bs ≤ ggM p B x L D J)
    (hC : Subgroup.centralizer {b} ≤ ggM p B x L D J)
    (hf : ∀ g : G, g⁻¹ * b * g ∈ ggM p B x L D J → g ∈ ggM p B x L D J) :
    IsSubnormal L₁ (Subgroup.centralizer {b}) ∧
      GGControlsStrongFusion (ggM p B x L D J) (Subgroup.zpowers b) := by
  have : Fact p.Prime := ⟨hp⟩
  have hb : orderOf b = p := orderOf_eq_prime (hBs.2 b h.1) h.2.1
  exact ⟨h.isSubnormal_of_centralizer_le hC,
    (ggControlsStrongFusion_zpowers_iff (hb ▸ hp)).mpr ⟨hBsM h.1, hf⟩⟩

theorem stepTwo_of_conj_mem (h : GGStepTwoPair p B Bs x L D J b L₁)
    (hD : GGControlsStrongFusion (ggM p B x L D J) D) {m : G} (hm : m ∈ ggM p B x L D J)
    (hmD : m⁻¹ * b * m ∈ D) :
    IsSubnormal L₁ (Subgroup.centralizer {b}) ∧
      GGControlsStrongFusion (ggM p B x L D J) (Subgroup.zpowers b) := by
  have hfus : GGControlsStrongFusion (ggM p B x L D J) (Subgroup.zpowers b) := by
    refine hD.of_map_conj_le hm ?_
    rw [MonoidHom.map_zpowers, Subgroup.zpowers_le]
    simpa [MulAut.conj_apply] using hmD
  exact ⟨h.isSubnormal_of_centralizer_le (hfus.centralizer_le (Subgroup.mem_zpowers b) h.2.1),
    hfus⟩

end GGStepTwoPair

end Steps

end CFSG.StandardType
