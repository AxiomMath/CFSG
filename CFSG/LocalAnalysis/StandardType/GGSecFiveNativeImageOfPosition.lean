module

public import CFSG.LocalAnalysis.StandardType.GGOneFiveInputs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveIdentDefs
public import CFSG.LocalAnalysis.StandardType.GGSignedCoordBlocks
public import CFSG.LocalAnalysis.StandardType.GGSecFiveRest
import CFSG.LocalAnalysis.StandardType.GGSecFiveNativeImageNormA
import CFSG.LocalAnalysis.StandardType.GGSecFiveNativeImageNormB
import CFSG.LocalAnalysis.StandardType.GGSecFiveNativeImageNormD
import CFSG.LocalAnalysis.StandardType.GGSecFiveNativeImageF4Coords
import CFSG.LocalAnalysis.StandardType.GGRCWeylCard
import CFSG.LocalAnalysis.StandardType.GGSpFrameCoxeterCard
import CFSG.LocalAnalysis.StandardType.GGLineStabNormalizes
import CFSG.LocalAnalysis.StandardType.GGSecFiveReflMaxBasic
import CFSG.LocalAnalysis.StandardType.GGSecFiveJoinPrimed
import CFSG.LocalAnalysis.StandardType.GGSecFiveTier1OfPrim
import CFSG.LocalAnalysis.StandardType.GGSignedCoordFix

public section

namespace CFSG.StandardType

variable {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
  {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}

theorem GGSecFiveRouteCfg.conj_mem_ggAutomizer_of_fix (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    (ha₀ : GGLNoncyclicInput) (hx : x ∈ Bs) {φ : MulAut ↥Bs} (hφ : φ ∈ ggInduced ⊤ Bs)
    (hφx : φ ⟨x, hx⟩ = ⟨x, hx⟩)
    {a : MulAut ↥Bs} (ha : a ∈ ggAutomizer L Bs) : φ * a * φ⁻¹ ∈ ggAutomizer L Bs :=
  (Subgroup.mem_normalizer_iff.mp (ggAutomizer_mem_normalizer_of_zpowers ha₀ hR.1.1.1 hx
    (Subgroup.subset_closure hφ) (by rw [hφx]; exact Subgroup.mem_zpowers _)) a).mp ha

open SpCoord Multiplicative

section Transport

private theorem toAdd_coord_mul_pow_inv {n : ℕ} {Bs : Subgroup G}
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))}
    (φ a : MulAut ↥Bs) (b : ↥Bs) (c : ℕ) (k : Fin n) :
    toAdd (eta (φ b * (a b ^ c)⁻¹) k) =
      toAdd (MulAut.congr eta φ (eta b) k) -
        (c : ZMod p) * toAdd (MulAut.congr eta a (eta b) k) := by
  have hφ : MulAut.congr eta φ (eta b) = eta (φ b) := by
    simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  have ha : MulAut.congr eta a (eta b) = eta (a b) := by
    simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  have h : eta (φ b * (a b ^ c)⁻¹) =
      MulAut.congr eta φ (eta b) * (MulAut.congr eta a (eta b) ^ c)⁻¹ := by
    rw [hφ, ha, map_mul, map_inv, map_pow]
  rw [h, toAdd_mul_apply, toAdd_inv_apply, toAdd_pow_apply]
  ring

private theorem congr_normalizes_of_map_eq {n : ℕ} {Bs : Subgroup G}
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))}
    {P : Subgroup (MulAut (Fin n → Multiplicative (ZMod p)))}
    (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦) (ha₀ : GGLNoncyclicInput) (hx : x ∈ Bs)
    {φ : MulAut ↥Bs} (hφ : φ ∈ ggInduced ⊤ Bs) (hφx : φ ⟨x, hx⟩ = ⟨x, hx⟩)
    (hmap : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = P) :
    ∀ w ∈ P, MulAut.congr eta φ * w * (MulAut.congr eta φ)⁻¹ ∈ P := by
  intro w hw
  rw [← hmap] at hw ⊢
  obtain ⟨a, ha, haeq⟩ := Subgroup.mem_map.mp hw
  rw [← haeq]
  change MulAut.congr eta φ * MulAut.congr eta a * (MulAut.congr eta φ)⁻¹ ∈
    Subgroup.map (MulAut.congr eta).toMonoidHom (ggAutomizer L Bs)
  have hconj : MulAut.congr eta φ * MulAut.congr eta a * (MulAut.congr eta φ)⁻¹ =
      MulAut.congr eta (φ * a * φ⁻¹) := by
    rw [← map_mul, ← map_inv, ← map_mul]
  rw [hconj]
  exact Subgroup.mem_map_of_mem _
    (GGSecFiveRouteCfg.conj_mem_ggAutomizer_of_fix hR ha₀ hx hφ hφx ha)

private theorem eta_x_fixed_of_map_eq {n : ℕ} {Bs : Subgroup G} {x : G}
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))}
    {P : Subgroup (MulAut (Fin n → Multiplicative (ZMod p)))}
    (hmap : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = P) (hx : x ∈ Bs)
    (hxfix : ∀ a ∈ ggAutomizer L Bs, a ⟨x, hx⟩ = ⟨x, hx⟩) :
    ∀ u ∈ P, u (eta ⟨x, hx⟩) = eta ⟨x, hx⟩ := by
  intro u hu
  rw [← hmap] at hu
  obtain ⟨a, ha, haeq⟩ := Subgroup.mem_map.mp hu
  rw [← haeq]
  change MulAut.congr eta a (eta ⟨x, hx⟩) = eta ⟨x, hx⟩
  have h1 : MulAut.congr eta a (eta ⟨x, hx⟩) = eta (a ⟨x, hx⟩) := by
    simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  rw [h1, hxfix a ha]

private theorem eta_apply_ne_one_of_ne_one {n : ℕ} {G : Type} [Group G] {Bs : Subgroup G}
    {x : G} (hx : x ∈ Bs) {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))}
    (hx1 : x ≠ 1) : eta ⟨x, hx⟩ ≠ 1 := by
  intro h
  apply hx1
  have h' : (⟨x, hx⟩ : ↥Bs) = 1 := eta.injective (by simpa using h)
  simpa using congrArg Subtype.val h'

private theorem permAut_mem_aPermutationFull_of_perm {n p : ℕ} (σ : Equiv.Perm (Fin n)) :
    SpCoord.permAut (p := p) σ ∈ aPermutationFull n p := by
  refine Equiv.Perm.swap_induction_on (motive := fun σ : Equiv.Perm (Fin n) =>
    SpCoord.permAut (p := p) σ ∈ aPermutationFull n p) σ ?_ ?_
  · have h1 : SpCoord.permAut (p := p) (1 : Equiv.Perm (Fin n)) = 1 := by
      apply MulEquiv.ext
      intro f
      funext i
      rfl
    rw [h1]
    exact Subgroup.one_mem _
  · intro τ a b hab hτ
    have hmul : SpCoord.permAut (p := p) (Equiv.swap a b * τ) =
        SpCoord.permAut (p := p) (Equiv.swap a b) * SpCoord.permAut (p := p) τ := by
      apply MulEquiv.ext
      intro f
      funext i
      rfl
    rw [hmul]
    exact Subgroup.mul_mem _ (Subgroup.subset_closure ⟨a, b, hab, rfl⟩) hτ

private theorem mem_zpowers_of_supported_of_axis {p n : ℕ} (hp : p.Prime)
    {u w : Fin n → Multiplicative (ZMod p)} (i0 : Fin n)
    (hu : ∀ i, i ≠ i0 → u i = 1) (hw : ∀ i, i ≠ i0 → w i = 1)
    (hui : u i0 ≠ 1) : w ∈ Subgroup.zpowers u := by
  have : Fact p.Prime := ⟨hp⟩
  have hA : (u i0).toAdd ≠ 0 := fun h => hui (toAdd_eq_zero.mp h)
  obtain ⟨c, hc⟩ : ∃ c : ℕ, (u i0) ^ c = w i0 := by
    refine ⟨(((w i0).toAdd / (u i0).toAdd).val), ?_⟩
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow, nsmul_eq_mul, ZMod.natCast_zmod_val]
    exact div_mul_cancel₀ (w i0).toAdd hA
  rw [Subgroup.mem_zpowers_iff]
  refine ⟨(c : ℤ), ?_⟩
  rw [zpow_natCast]
  funext i
  rw [Pi.pow_apply]
  by_cases hi : i = i0
  · subst hi; exact hc
  · rw [hu i hi, hw i hi, one_pow]

private theorem mem_zpowers_of_const {p n : ℕ} (hp : p.Prime)
    {u w : Fin n → Multiplicative (ZMod p)} (i0 : Fin n)
    (hu : ∀ i j, u i = u j) (hw : ∀ i j, w i = w j) (hui : u i0 ≠ 1) :
    w ∈ Subgroup.zpowers u := by
  have : Fact p.Prime := ⟨hp⟩
  have hA : (u i0).toAdd ≠ 0 := fun h => hui (toAdd_eq_zero.mp h)
  obtain ⟨c, hc⟩ : ∃ c : ℕ, (u i0) ^ c = w i0 := by
    refine ⟨(((w i0).toAdd / (u i0).toAdd).val), ?_⟩
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow, nsmul_eq_mul, ZMod.natCast_zmod_val]
    exact div_mul_cancel₀ (w i0).toAdd hA
  rw [Subgroup.mem_zpowers_iff]
  refine ⟨(c : ℤ), ?_⟩
  rw [zpow_natCast]
  funext i
  rw [Pi.pow_apply, hu i i0, hw i i0]
  exact hc

end Transport

private theorem GGSecFiveRouteCfg.nativeImage_of_axis (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    (ha₀ : GGLNoncyclicInput) {n : ℕ} {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))}
    {i0 : Fin n} {W : Subgroup (MulAut (Fin n → Multiplicative (ZMod p)))}
    (hLW : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = W)
    (hfixW : ∀ f : Fin n → Multiplicative (ZMod p), (∀ u ∈ W, u f = f) → ∀ k, k ≠ i0 → f k = 1)
    (hnormW : ∀ u : MulAut (Fin n → Multiplicative (ZMod p)), (∀ w ∈ W, u * w * u⁻¹ ∈ W) →
      ∃ (γ : ZMod p) (w : MulAut (Fin n → Multiplicative (ZMod p))), w ∈ W ∧
        ∀ (f : Fin n → Multiplicative (ZMod p)) (k : Fin n), k ≠ i0 →
          toAdd (u f k) = γ * toAdd (w f k))
    (hx : x ∈ Bs) {φ : MulAut ↥Bs} (hφ : φ ∈ ggInduced ⊤ Bs) (hφx : φ ⟨x, hx⟩ = ⟨x, hx⟩) :
    ∃ (c : ℕ) (a : MulAut ↥Bs), a ∈ ggAutomizer L Bs ∧
      ∀ b : ↥Bs, φ b * (a b ^ c)⁻¹ ∈ Subgroup.zpowers (⟨x, hx⟩ : ↥Bs) := by
  obtain ⟨hp, -⟩ := ggRouteCfg_prime hR
  haveI : Fact p.Prime := ⟨hp⟩
  have hx1 : x ≠ 1 := hR.1.1.1.2.2.2.2.2.2.1.2.2.1
  obtain ⟨γ, w, hw, hrel⟩ := hnormW _ (congr_normalizes_of_map_eq hR ha₀ hx hφ hφx hLW)
  rw [← hLW] at hw
  obtain ⟨a, ha, haeq⟩ := Subgroup.mem_map.mp hw
  refine ⟨γ.val, a, ha, fun b => ?_⟩
  have hxi0 : ∀ k, k ≠ i0 → eta ⟨x, hx⟩ k = 1 :=
    hfixW _ (eta_x_fixed_of_map_eq hLW hx
      (ggRM_AL_fixes_x (ggSecFiveRouteCfg'_of_routeCfg hR) hx))
  have heta_ne_one : eta ⟨x, hx⟩ ≠ 1 := eta_apply_ne_one_of_ne_one hx hx1
  have hui : eta ⟨x, hx⟩ i0 ≠ 1 := by
    intro h
    exact heta_ne_one (funext fun k => by
      by_cases hk : k = i0
      · simpa [hk] using h
      · exact hxi0 k hk)
  have haeq' : MulAut.congr eta a = w := haeq
  have hsupp : ∀ k, k ≠ i0 → eta (φ b * (a b ^ γ.val)⁻¹) k = 1 := by
    intro k hk
    rw [← toAdd_eq_zero, toAdd_coord_mul_pow_inv, haeq', ZMod.natCast_zmod_val,
      hrel (eta b) k hk]
    ring
  have hmem : eta (φ b * (a b ^ γ.val)⁻¹) ∈ Subgroup.zpowers (eta ⟨x, hx⟩) :=
    mem_zpowers_of_supported_of_axis hp i0 hxi0 hsupp hui
  rw [Subgroup.mem_zpowers_iff] at hmem ⊢
  obtain ⟨t, ht⟩ := hmem
  exact ⟨t, eta.injective (by rw [map_zpow]; exact ht)⟩

theorem GGSecFiveRouteCfg.nativeImage_of_bCoordinateBlock (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    (ha₀ : GGLNoncyclicInput) {n : ℕ} (hn : 4 ≤ n)
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))} {i0 : Fin n}
    (hLB : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock n p i0)
    (hx : x ∈ Bs) {φ : MulAut ↥Bs} (hφ : φ ∈ ggInduced ⊤ Bs) (hφx : φ ⟨x, hx⟩ = ⟨x, hx⟩) :
    ∃ (c : ℕ) (a : MulAut ↥Bs), a ∈ ggAutomizer L Bs ∧
      ∀ b : ↥Bs, φ b * (a b ^ c)⁻¹ ∈ Subgroup.zpowers (⟨x, hx⟩ : ↥Bs) := by
  obtain ⟨hp, hp2⟩ := ggRouteCfg_prime hR
  exact hR.nativeImage_of_axis ha₀ hLB (fun f => (forall_bCoordinateBlock_fix_iff hp hp2 i0 f).mp)
    (fun _ hu => exists_smul_mem_bCoordinateBlock_of_normalizes hp hp2 hn i0 hu) hx hφ hφx

theorem GGSecFiveRouteCfg.nativeImage_of_dCoordinateBlock_four
    (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦) (ha₀ : GGLNoncyclicInput)
    {eta : ↥Bs ≃* (Fin 4 → Multiplicative (ZMod p))} {i0 : Fin 4}
    (hLD : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = dCoordinateBlock 4 p i0)
    (hx : x ∈ Bs) {φ : MulAut ↥Bs} (hφ : φ ∈ ggInduced ⊤ Bs) (hφx : φ ⟨x, hx⟩ = ⟨x, hx⟩) :
    ∃ (c : ℕ) (a : MulAut ↥Bs), a ∈ ggAutomizer L Bs ∧
      ∀ b : ↥Bs, φ b * (a b ^ c)⁻¹ ∈ Subgroup.zpowers (⟨x, hx⟩ : ↥Bs) := by
  obtain ⟨hp, hp2⟩ := ggRouteCfg_prime hR
  exact hR.nativeImage_of_axis ha₀ hLD
    (fun f => (forall_dCoordinateBlock_fix_iff hp hp2 (by norm_num) i0 f).mp)
    (fun _ hu => exists_smul_mem_dCoordinateBlock_four_of_normalizes hp hp2 i0 hu) hx hφ hφx

private theorem card_fixed_mulAut_congr {n p : ℕ} {G : Type} [Group G] {Bs : Subgroup G}
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))} (ψ : MulAut ↥Bs) :
    Nat.card {v : Fin n → Multiplicative (ZMod p) // MulAut.congr eta ψ v = v} =
      Nat.card {b : ↥Bs // ψ b = b} := by
  refine Nat.card_congr (Equiv.subtypeEquiv eta.toEquiv (fun b => ?_)).symm
  change ψ b = b ↔ MulAut.congr eta ψ (eta b) = eta b
  have hb : MulAut.congr eta ψ (eta b) = eta (ψ b) := by
    simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  rw [hb]
  exact ⟨fun h' => by rw [h'], fun h' => eta.injective h'⟩

private theorem ggIsReflection_congr {n p : ℕ} {G : Type} [Group G] {Bs : Subgroup G}
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))} {ψ : MulAut ↥Bs}
    (h : GGIsReflection p ψ) :
    (MulAut.congr eta ψ) ^ 2 = 1 ∧
      Nat.card {v : Fin n → Multiplicative (ZMod p) // MulAut.congr eta ψ v = v} * p =
        Nat.card (Fin n → Multiplicative (ZMod p)) := by
  refine ⟨?_, ?_⟩
  · rw [← map_pow, h.1, map_one]
  · rw [card_fixed_mulAut_congr (eta := eta) ψ, h.2, Nat.card_congr eta.toEquiv]

theorem GGSecFiveRouteCfg.nativeImage_of_le_bCoordinateBlock_four
    (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦) (ha₀ : GGLNoncyclicInput)
    {eta : ↥Bs ≃* (Fin 4 → Multiplicative (ZMod p))}
    (hLe : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom ≤ bCoordinateBlock 4 p 3)
    (hT : GGWeylOfType p (CoxeterMatrix.A 3) (ggAutomizer L Bs) ∨
      GGWeylOfType p (CoxeterMatrix.B 3) (ggAutomizer L Bs))
    (hx : x ∈ Bs) {φ : MulAut ↥Bs} (hφ : φ ∈ ggInduced ⊤ Bs) (hφx : φ ⟨x, hx⟩ = ⟨x, hx⟩) :
    ∃ (c : ℕ) (a : MulAut ↥Bs), a ∈ ggAutomizer L Bs ∧
      ∀ b : ↥Bs, φ b * (a b ^ c)⁻¹ ∈ Subgroup.zpowers (⟨x, hx⟩ : ↥Bs) := by
  obtain ⟨hp, hp2⟩ := ggRouteCfg_prime hR
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite (MulAut (Fin 4 → Multiplicative (ZMod p))) :=
    Finite.of_injective (fun f : MulAut _ => (f : _ → _)) DFunLike.coe_injective
  have hcardA : Nat.card ↥((ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom) =
      Nat.card ↥(ggAutomizer L Bs) :=
    Subgroup.card_map_of_injective (MulAut.congr eta).injective
  rcases hT with ⟨e, he⟩ | ⟨e, he⟩
  ·
    let f : MulAut ↥Bs →* MulAut (Fin 4 → Multiplicative (ZMod p)) :=
      (MulAut.congr eta).toMonoidHom
    have hf : Function.Injective f := (MulAut.congr eta).injective
    let e' : (CoxeterMatrix.A 3).Group ≃*
        ↥((ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom) :=
      e.trans (Subgroup.equivMapOfInjective (ggAutomizer L Bs) f hf)
    have hcoe : ∀ g : (CoxeterMatrix.A 3).Group,
        ((e' g : ↥((ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom)) :
          MulAut (Fin 4 → Multiplicative (ZMod p))) = MulAut.congr eta (e g) := by
      intro g
      exact Subgroup.coe_equivMapOfInjective_apply _ f hf (e g)
    have he' : ∀ i : Fin 3,
        ((e' ((CoxeterMatrix.A 3).simple i) :
            ↥((ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom)) :
          MulAut (Fin 4 → Multiplicative (ZMod p))) ^ 2 = 1 ∧
        Nat.card {v : Fin 4 → Multiplicative (ZMod p) //
          ((e' ((CoxeterMatrix.A 3).simple i) :
            ↥((ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom)) :
            MulAut (Fin 4 → Multiplicative (ZMod p))) v = v} * p =
          Nat.card (Fin 4 → Multiplicative (ZMod p)) := by
      intro i
      have htrans := ggIsReflection_congr (eta := eta) (he i)
      refine ⟨?_, ?_⟩
      · rw [hcoe]
        exact htrans.1
      · have hfix : Nat.card {v : Fin 4 → Multiplicative (ZMod p) //
            ((e' ((CoxeterMatrix.A 3).simple i) :
              ↥((ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom)) :
              MulAut (Fin 4 → Multiplicative (ZMod p))) v = v} =
            Nat.card {v : Fin 4 → Multiplicative (ZMod p) //
              MulAut.congr eta (e ((CoxeterMatrix.A 3).simple i)) v = v} := by
          refine Nat.card_congr (Equiv.subtypeEquiv (Equiv.refl _) (fun v => ?_))
          simpa only [hcoe, Equiv.refl_apply]
        rw [hfix]
        exact htrans.2
    have hLD : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom ≤
        dCoordinateBlock 4 p 3 :=
      le_dCoordinateBlock_of_coxeterA3 hp hp2 hLe e' he'
    have hcardR : Nat.card ↥((ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom) = 24 := by
      rw [hcardA, ← Nat.card_congr e.toEquiv, l05nK3a_card_coxeterA 3]
      norm_num
    have hcardD : Nat.card ↥(dCoordinateBlock 4 p 3) ≤
        Nat.card ↥((ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom) := by
      rw [hcardR]
      exact card_dCoordinateBlock_four_le hp
    exact hR.nativeImage_of_dCoordinateBlock_four ha₀
      (Subgroup.eq_of_le_of_card_ge hLD hcardD) hx hφ hφx
  ·
    have hcardR : Nat.card ↥((ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom) =
        Nat.card (CoxeterMatrix.B 3).Group := by
      rw [hcardA]
      exact (Nat.card_congr e.toEquiv).symm
    have hge : 48 ≤ Nat.card ↥((ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom) := by
      rw [hcardR]
      have h := SpFrame.card_coxeterB_ge 3 (by norm_num)
      norm_num at h
      exact h
    have hcardB : Nat.card ↥(bCoordinateBlock 4 p 3) ≤
        Nat.card ↥((ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom) :=
      (card_bCoordinateBlock_four_le hp).trans hge
    exact hR.nativeImage_of_bCoordinateBlock ha₀ (by norm_num)
      (Subgroup.eq_of_le_of_card_ge hLe hcardB) hx hφ hφx

theorem GGSecFiveRouteCfg.nativeImage_of_aPermutationFull
    (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦) (ha₀ : GGLNoncyclicInput) {n : ℕ} (hn : 4 ≤ n)
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))}
    (hLA : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = aPermutationFull n p)
    (hx : x ∈ Bs) {φ : MulAut ↥Bs} (hφ : φ ∈ ggInduced ⊤ Bs) (hφx : φ ⟨x, hx⟩ = ⟨x, hx⟩) :
    ∃ (c : ℕ) (a : MulAut ↥Bs), a ∈ ggAutomizer L Bs ∧
      ∀ b : ↥Bs, φ b * (a b ^ c)⁻¹ ∈ Subgroup.zpowers (⟨x, hx⟩ : ↥Bs) := by
  obtain ⟨hp, hp2⟩ := ggRouteCfg_prime hR
  haveI : Fact p.Prime := ⟨hp⟩
  have hx1 : x ≠ 1 := hR.1.1.1.2.2.2.2.2.2.1.2.2.1
  have hnorm : ∀ w ∈ aPermutationFull n p,
      MulAut.congr eta φ * w * (MulAut.congr eta φ)⁻¹ ∈ aPermutationFull n p :=
    congr_normalizes_of_map_eq hR ha₀ hx hφ hφx hLA
  obtain ⟨α, σ, hrel⟩ :=
    exists_smul_perm_of_normalizes_aPermutationFull hp hp2 hn hnorm
  have hσmem : SpCoord.permAut (p := p) σ ∈
      (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom := by
    rw [hLA]
    exact permAut_mem_aPermutationFull_of_perm σ
  obtain ⟨a, ha, haeq⟩ := Subgroup.mem_map.mp hσmem
  refine ⟨α.val, a, ha, fun b => ?_⟩
  have hxfix : ∀ a' ∈ ggAutomizer L Bs, a' ⟨x, hx⟩ = ⟨x, hx⟩ :=
    ggRM_AL_fixes_x (ggSecFiveRouteCfg'_of_routeCfg hR) hx
  have hfixP : ∀ u ∈ aPermutationFull n p, u (eta ⟨x, hx⟩) = eta ⟨x, hx⟩ :=
    eta_x_fixed_of_map_eq hLA hx hxfix
  have hxconst : ∀ i j, eta ⟨x, hx⟩ i = eta ⟨x, hx⟩ j :=
    (forall_aPermutationFull_fix_iff (n := n) (p := p) (eta ⟨x, hx⟩)).mp hfixP
  have heta_ne_one : eta ⟨x, hx⟩ ≠ 1 := eta_apply_ne_one_of_ne_one hx hx1
  let i0 : Fin n := ⟨0, by omega⟩
  have hui : eta ⟨x, hx⟩ i0 ≠ 1 := by
    intro h
    exact heta_ne_one (funext fun k => by
      rw [hxconst k i0]
      exact h)
  have haeq' : MulAut.congr eta a = SpCoord.permAut σ := haeq
  have hconst : ∀ i j, eta (φ b * (a b ^ α.val)⁻¹) i =
      eta (φ b * (a b ^ α.val)⁻¹) j := by
    obtain ⟨s, hs⟩ := hrel (eta b)
    have hcoord : ∀ i, toAdd (eta (φ b * (a b ^ α.val)⁻¹) i) = s := by
      intro i
      rw [toAdd_coord_mul_pow_inv, haeq', ZMod.natCast_zmod_val, hs i,
        permAut_apply, Function.comp_apply]
      ring
    intro i j
    exact toAdd.injective (by rw [hcoord i, hcoord j])
  have hmem : eta (φ b * (a b ^ α.val)⁻¹) ∈ Subgroup.zpowers (eta ⟨x, hx⟩) :=
    mem_zpowers_of_const hp i0 hxconst hconst hui
  rw [Subgroup.mem_zpowers_iff] at hmem ⊢
  obtain ⟨t, ht⟩ := hmem
  exact ⟨t, eta.injective (by rw [map_zpow]; exact ht)⟩

end CFSG.StandardType

end
