module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionSquareFieldFullAutomorphism
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecC

open CFSG.ProperTwoGeneratedCore.LocalCriterionSquareField
open scoped MatrixGroups

namespace O8S

variable {W : Type} [CommGroup W] {Hs Ks : Subgroup (MulAut W)} {F : Type} [Field F] {n : ℕ}

@[expose] noncomputable def phi (hn : 1 ≤ n) (hF : Nat.card F = 2 ^ n)
    (hHN : Hs ≤ Subgroup.normalizer (Ks : Set (MulAut W))) (e : ↥Ks ≃* SL(2, F)) :
    ↥Hs →* Gamma F :=
  (gammaEquivMulAut hn hF).symm.toMonoidHom.comp ((MulAut.congr e).toMonoidHom.comp
    (Ks.normalizerMonoidHom.comp (Subgroup.inclusion hHN)))

variable (hn : 1 ≤ n) (hF : Nat.card F = 2 ^ n)
  (hHN : Hs ≤ Subgroup.normalizer (Ks : Set (MulAut W))) (e : ↥Ks ≃* SL(2, F))

theorem gammaToMulAut_phi (h : ↥Hs) :
    gammaToMulAut F (phi hn hF hHN e h) =
      MulAut.congr e (Ks.normalizerMonoidHom (Subgroup.inclusion hHN h)) :=
  (gammaEquivMulAut hn hF).apply_symm_apply _

theorem phi_of_mem (hKH : Ks ≤ Hs) (k : ↥Ks) :
    phi hn hF hHN e ⟨k, hKH k.2⟩ = SemidirectProduct.inl (e k) := by
  apply (gammaToMulAut_bijective_of_card hF).1
  rw [gammaToMulAut_phi, gammaToMulAut_inl,
    ← CFSG.ComponentClassification.OuterAutomorphisms.congr_conj]
  congr 1

include hF in
theorem eq_one_of_mem_centralizer [Finite F] (e : ↥Ks ≃* SL(2, F)) {z : MulAut W} (hz : z ∈ Ks)
    (hzc : z ∈ Subgroup.centralizer (Ks : Set (MulAut W))) : z = 1 := by
  have : CharP F 2 := char_two_of_card hF
  have hcen : e ⟨z, hz⟩ ∈ Subgroup.center SL(2, F) := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨k, rfl⟩ := e.surjective g
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hzc k k.2)
  rw [sl2_center_eq_bot, Subgroup.mem_bot, map_eq_one_iff e e.injective] at hcen
  exact congrArg Subtype.val hcen

theorem centralizer_normal (hHN : Hs ≤ Subgroup.normalizer (Ks : Set (MulAut W))) :
    ((Hs ⊓ Subgroup.centralizer (Ks : Set (MulAut W))).subgroupOf Hs).Normal := by
  refine ⟨fun x hx g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hx ⊢
  refine ⟨(g * x * g⁻¹).2, Subgroup.mem_centralizer_iff.mpr fun k hk => ?_⟩
  have hk' : (g : MulAut W)⁻¹ * k * g ∈ Ks := by
    have := (hHN (inv_mem g.2) k).mp hk
    simpa [mul_assoc] using this
  have hxk := Subgroup.mem_centralizer_iff.mp hx.2 _ hk'
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  calc k * ((g : MulAut W) * x * (g : MulAut W)⁻¹)
      = g * (((g : MulAut W)⁻¹ * k * g) * x) * (g : MulAut W)⁻¹ := by group
    _ = g * (x * ((g : MulAut W)⁻¹ * k * g)) * (g : MulAut W)⁻¹ := by rw [hxk]
    _ = (g : MulAut W) * x * (g : MulAut W)⁻¹ * k := by group

include hF in
theorem centralizer_eq_bot [Finite F] (hHN : Hs ≤ Subgroup.normalizer (Ks : Set (MulAut W)))
    (e : ↥Ks ≃* SL(2, F)) (h2 : ∀ h ∈ Hs, ∃ k : ℕ, h ^ 2 ^ k ∈ Ks)
    (hO : CFSG.pCore 2 ↥Hs = ⊥) :
    Hs ⊓ Subgroup.centralizer (Ks : Set (MulAut W)) = ⊥ := by
  set N : Subgroup ↥Hs := (Hs ⊓ Subgroup.centralizer (Ks : Set (MulAut W))).subgroupOf Hs
    with hN
  have hNp : IsPGroup 2 N := by
    intro x
    obtain ⟨k, hk⟩ := h2 _ (x : ↥Hs).2
    have hxC : ((x : ↥Hs) : MulAut W) ∈ Subgroup.centralizer (Ks : Set (MulAut W)) :=
      (Subgroup.mem_subgroupOf.mp x.2).2
    have h1 := eq_one_of_mem_centralizer hF e hk (pow_mem hxC _)
    refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
    simpa using h1
  have hle : N ≤ CFSG.pCore 2 ↥Hs := le_sSup ⟨centralizer_normal hHN, hNp⟩
  rw [hO] at hle
  rw [eq_bot_iff]
  intro x hx
  have hxN : (⟨x, hx.1⟩ : ↥Hs) ∈ N := Subgroup.mem_subgroupOf.mpr hx
  have := hle hxN
  rw [Subgroup.mem_bot] at this
  exact Subgroup.mem_bot.mpr (congrArg Subtype.val this)

include hF in
theorem phi_injective [Finite F] (h2 : ∀ h ∈ Hs, ∃ k : ℕ, h ^ 2 ^ k ∈ Ks)
    (hO : CFSG.pCore 2 ↥Hs = ⊥) : Function.Injective (phi hn hF hHN e) := by
  rw [injective_iff_map_eq_one]
  intro h hh
  have h1 : MulAut.congr e (Ks.normalizerMonoidHom (Subgroup.inclusion hHN h)) = 1 := by
    rw [← gammaToMulAut_phi hn hF hHN e h, hh, map_one]
  have h3 : Ks.normalizerMonoidHom (Subgroup.inclusion hHN h) = 1 :=
    (map_eq_one_iff _ (MulAut.congr e).injective).mp h1
  have hc : (h : MulAut W) ∈ Hs ⊓ Subgroup.centralizer (Ks : Set (MulAut W)) := by
    refine ⟨h.2, Subgroup.mem_centralizer_iff.mpr fun k hk => ?_⟩
    have h4 := congrArg (fun α : MulAut ↥Ks => ((α ⟨k, hk⟩ : ↥Ks) : MulAut W)) h3
    change (h : MulAut W) * k * (h : MulAut W)⁻¹ = k at h4
    rw [mul_inv_eq_iff_eq_mul] at h4
    exact h4.symm
  rw [centralizer_eq_bot hF hHN e h2 hO, Subgroup.mem_bot] at hc
  exact Subtype.ext hc

include hF in
theorem mem_of_phi_mem [Finite F] (hKH : Ks ≤ Hs) (h2 : ∀ h ∈ Hs, ∃ k : ℕ, h ^ 2 ^ k ∈ Ks)
    (hO : CFSG.pCore 2 ↥Hs = ⊥) (h : ↥Hs) (hh : phi hn hF hHN e h ∈ linearKernel F) :
    (h : MulAut W) ∈ Ks := by
  rw [mem_linearKernel_iff] at hh
  set k : ↥Ks := e.symm (phi hn hF hHN e h).left
  have hk : phi hn hF hHN e ⟨k, hKH k.2⟩ = phi hn hF hHN e h := by
    rw [phi_of_mem hn hF hHN e hKH, MulEquiv.apply_symm_apply]
    exact SemidirectProduct.ext rfl hh.symm
  rw [← phi_injective hn hF hHN e h2 hO hk]
  exact k.2

end O8S

end CFSG.Quasithin.Vol2.Ch11.SecC
