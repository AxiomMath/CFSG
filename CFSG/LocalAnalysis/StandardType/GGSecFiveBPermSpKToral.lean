module

public import CFSG.LocalAnalysis.StandardType.GGAssemblyTwoHypSix
public import CFSG.LocalAnalysis.StandardType.GGSpJoinPlaneTorusDefs
import CFSG.GroupTheory.ElemAbelianClosure
import CFSG.LocalAnalysis.StandardType.GGSpJoinNbrCentralizer

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal

private theorem injective_of_pow_le_card_range {p n : ℕ} [NeZero p] {H : Type*} [Group H]
    (D : (Fin n → Multiplicative (ZMod p)) →* H) (h : p ^ n ≤ Nat.card D.range) :
    Function.Injective D := by
  have hcard : Nat.card (Fin n → Multiplicative (ZMod p)) = p ^ n := by
    rw [Nat.card_fun, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod, Nat.card_fin]
  have hmul : Nat.card D.ker * Nat.card D.range = p ^ n := by
    rw [← Subgroup.index_ker D, Subgroup.card_mul_index, hcard]
  have hpos : 0 < Nat.card D.range := lt_of_lt_of_le (pow_pos (NeZero.pos p) n) h
  have hle : Nat.card D.ker * Nat.card D.range ≤ 1 * Nat.card D.range := by
    rw [hmul, one_mul]
    exact h
  have hker : Nat.card D.ker ≤ 1 := Nat.le_of_mul_le_mul_right hle hpos
  exact (MonoidHom.ker_eq_bot_iff D).mp (Subgroup.eq_bot_of_card_le D.ker hker)

private theorem pow_le_card_inf_of_card_split {G : Type} [Group G] [Finite G] {p r : ℕ}
    {Bs K : Subgroup G}
    (hcard_split : Nat.card Bs = Nat.card ↥(Bs ⊓ K) *
      Nat.card ↥(Bs ⊓ Subgroup.centralizer (K : Set G)))
    (hcard : p ^ (r + 1) * Nat.card ↥(Bs ⊓ Subgroup.centralizer (K : Set G)) ≤
      Nat.card ↥Bs) :
    p ^ (r + 1) ≤ Nat.card ↥(Bs ⊓ K) := by
  have hpos : 0 < Nat.card ↥(Bs ⊓ Subgroup.centralizer (K : Set G)) :=
    Nat.card_pos_iff.mpr ⟨⟨1, by simp⟩, inferInstance⟩
  have hle : p ^ (r + 1) * Nat.card ↥(Bs ⊓ Subgroup.centralizer (K : Set G)) ≤
      Nat.card ↥(Bs ⊓ K) * Nat.card ↥(Bs ⊓ Subgroup.centralizer (K : Set G)) := by
    rw [← hcard_split]
    exact hcard
  exact Nat.le_of_mul_le_mul_right hle hpos

private theorem exists_toral_conj_of_split {G S : Type} [Group G] [Group S] {p r : ℕ}
    [Fact p.Prime] {Bs K : Subgroup G} {κ : S →* G} (hκrange : κ.range = K)
    (hsplit : ∀ b ∈ Bs, ∃ x ∈ Bs ⊓ K,
      ∃ c ∈ Bs ⊓ Subgroup.centralizer (K : Set G), b = x * c)
    {D : (Fin (r + 1) → Multiplicative (ZMod p)) →* S}
    (htoral : ∀ x ∈ Bs ⊓ K, ∃ t : Fin (r + 1) → Multiplicative (ZMod p),
      x = κ (D t)) :
    ∀ b ∈ Bs, ∃ t : Fin (r + 1) → Multiplicative (ZMod p), ∀ s,
      b * κ s * b⁻¹ = κ (D t * s * (D t)⁻¹) := by
  intro b hb
  obtain ⟨x, hx, c', hc', rfl⟩ := hsplit b hb
  obtain ⟨t, ht⟩ := htoral x hx
  refine ⟨t, fun s => ?_⟩
  have hsK : κ s ∈ K := hκrange ▸ MonoidHom.mem_range.mpr ⟨s, rfl⟩
  have hcs : κ s * c' = c' * κ s := Subgroup.mem_centralizer_iff.mp hc'.2 (κ s) hsK
  have hc'conj : c' * κ s * c'⁻¹ = κ s := by
    rw [← hcs]
    group
  calc (x * c') * κ s * (x * c')⁻¹ = x * (c' * κ s * c'⁻¹) * x⁻¹ := by group
    _ = x * κ s * x⁻¹ := by rw [hc'conj]
    _ = κ (D t) * κ s * (κ (D t))⁻¹ := by rw [ht]
    _ = κ (D t * s * (D t)⁻¹) := by simp only [map_mul, map_inv]

private theorem exists_conj_comap_eq_torus {G S : Type} [Group G] [Group S] [Finite G]
    {p r : ℕ} [Fact p.Prime] {B Bs K : Subgroup G} (hBs : GGBstar p B Bs)
    (hZ : Subgroup.center K = ⊥) (hNK : Bs ≤ Subgroup.normalizer (K : Set G))
    (hinner : ∀ b ∈ Bs, ∃ g ∈ K, ∀ k ∈ K, b * k * b⁻¹ = g * k * g⁻¹)
    (hcard : p ^ (r + 1) * Nat.card ↥(Bs ⊓ Subgroup.centralizer (K : Set G)) ≤
      Nat.card ↥Bs)
    (φ : S →* G) (hφinj : Function.Injective φ) (hφrange : φ.range = K)
    {D : (Fin (r + 1) → Multiplicative (ZMod p)) →* S}
    (hconj : ∀ E : Subgroup S, CFSG.Open.IsElemAbelian p E → p ^ (r + 1) ≤ Nat.card E →
      ∃ β : MulAut S, E.map β.toMonoidHom = D.range) :
    Function.Injective D ∧ ∃ β : MulAut S,
      ((Bs ⊓ K).comap φ).map β.toMonoidHom = D.range := by
  classical
  have hcard_split := card_ggBstar_split (X := K) hBs hZ hNK hinner
  have hcardK : p ^ (r + 1) ≤ Nat.card ↥(Bs ⊓ K) :=
    pow_le_card_inf_of_card_split hcard_split hcard
  let E' : Subgroup S := (Bs ⊓ K).comap φ
  have hE'map : E'.map φ = Bs ⊓ K := by
    show ((Bs ⊓ K).comap φ).map φ = Bs ⊓ K
    exact Subgroup.map_comap_eq_self (by rw [← hφrange]; exact inf_le_right)
  have hcardE' : Nat.card E' = Nat.card ↥(Bs ⊓ K) := by
    rw [← hE'map]
    exact (Subgroup.card_map_of_injective (K := E') hφinj).symm
  have hE'ab : CFSG.Open.IsElemAbelian p E' :=
    CFSG.Open.IsElemAbelian.comap (hBs.2.1.mono inf_le_left) hφinj
  have hcardE'ge : p ^ (r + 1) ≤ Nat.card E' := by rw [hcardE']; exact hcardK
  obtain ⟨β, hβ⟩ := hconj E' hE'ab hcardE'ge
  refine ⟨injective_of_pow_le_card_range _ ?_, β, hβ⟩
  rw [← hβ, Subgroup.card_map_of_injective (f := β.toMonoidHom) β.injective]
  exact hcardE'ge

private theorem exists_conj_torus_lift {G S : Type} [Group G] [Group S] [Finite G] {p r : ℕ}
    [Fact p.Prime] {B Bs K : Subgroup G} (hBs : GGBstar p B Bs)
    (hZ : Subgroup.center K = ⊥) (hNK : Bs ≤ Subgroup.normalizer (K : Set G))
    (hinner : ∀ b ∈ Bs, ∃ g ∈ K, ∀ k ∈ K, b * k * b⁻¹ = g * k * g⁻¹)
    (hcard : p ^ (r + 1) * Nat.card ↥(Bs ⊓ Subgroup.centralizer (K : Set G)) ≤
      Nat.card ↥Bs)
    (φ : S →* G) (hφinj : Function.Injective φ) (hφrange : φ.range = K)
    {D : (Fin (r + 1) → Multiplicative (ZMod p)) →* S}
    (hconj : ∀ E : Subgroup S, CFSG.Open.IsElemAbelian p E → p ^ (r + 1) ≤ Nat.card E →
      ∃ β : MulAut S, E.map β.toMonoidHom = D.range) :
    Function.Injective D ∧
      ∃ κ : S →* G, Function.Injective κ ∧ κ.range = K ∧
        ∀ x ∈ Bs ⊓ K, ∃ t : Fin (r + 1) → Multiplicative (ZMod p),
          x = κ (D t) := by
  classical
  obtain ⟨hDinj, β, hβ⟩ :=
    exists_conj_comap_eq_torus hBs hZ hNK hinner hcard φ hφinj hφrange hconj
  let E' : Subgroup S := (Bs ⊓ K).comap φ
  let κ : S →* G := φ.comp β.symm.toMonoidHom
  have hκrange : κ.range = K := by
    change (φ.comp β.symm.toMonoidHom).range = K
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr β.symm.surjective, Subgroup.map_top,
      hφrange]
  have hκinj : Function.Injective κ := hφinj.comp β.symm.injective
  refine ⟨hDinj, κ, hκinj, hκrange, ?_⟩
  intro x hx
  have hxr : x ∈ φ.range := by rw [hφrange]; exact hx.2
  obtain ⟨w, hw⟩ := MonoidHom.mem_range.mp hxr
  have hwE : w ∈ E' := by
    show φ w ∈ Bs ⊓ K
    exact ⟨hw ▸ hx.1, hw ▸ hx.2⟩
  have huT : β w ∈ D.range := by
    rw [← hβ]
    exact Subgroup.mem_map.mpr ⟨w, hwE, rfl⟩
  obtain ⟨t, ht⟩ := MonoidHom.mem_range.mp huT
  refine ⟨t, ?_⟩
  have hκu : κ (β w) = x := by
    change φ (β.symm (β w)) = x
    rw [MulEquiv.symm_apply_apply, hw]
  rw [ht, hκu]

theorem ggSecFiveBPermSpK_exists_toral_of_inner {G S : Type} [Group G] [Group S] [Finite G]
    {p r : ℕ} [Fact p.Prime] {B Bs K : Subgroup G} (hBs : GGBstar p B Bs)
    {φ : S →* G} (hφinj : Function.Injective φ) (hφrange : φ.range = K)
    (hZ : Subgroup.center K = ⊥)
    (hinner : ∀ b ∈ Bs, ∃ g ∈ K, ∀ k ∈ K, b * k * b⁻¹ = g * k * g⁻¹)
    (hcard : p ^ (r + 1) * Nat.card ↥(Bs ⊓ Subgroup.centralizer (K : Set G)) ≤ Nat.card ↥Bs)
    {D : (Fin (r + 1) → Multiplicative (ZMod p)) →* S}
    (hconj : ∀ E : Subgroup S, CFSG.Open.IsElemAbelian p E → p ^ (r + 1) ≤ Nat.card E →
      ∃ β : MulAut S, E.map β.toMonoidHom = D.range) :
    Function.Injective D ∧ ∃ κ : S →* G, Function.Injective κ ∧ κ.range = K ∧
      ∀ b ∈ Bs, ∃ t : Fin (r + 1) → Multiplicative (ZMod p), ∀ s,
        b * κ s * b⁻¹ = κ (D t * s * (D t)⁻¹) := by
  classical
  have hNK : Bs ≤ Subgroup.normalizer (K : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro b hb k hk
    obtain ⟨g, hgK, hgact⟩ := hinner b hb
    rw [hgact k hk]
    exact K.mul_mem (K.mul_mem hgK hk) (K.inv_mem hgK)
  have hsplit := ggBstar_split_of_inner (X := K) hBs hZ hNK hinner
  obtain ⟨hDinj, κ, hκinj, hκrange, htoral⟩ :=
    exists_conj_torus_lift hBs hZ hNK hinner hcard φ hφinj hφrange hconj
  exact ⟨hDinj, κ, hκinj, hκrange, exists_toral_conj_of_split hκrange hsplit htoral⟩


theorem ggSecFiveBPermSpK_exists_toral (hMp : GGInnerDiagMpInput) {G : Type} [Group G]
    [Finite G] {p r f : ℕ} [Fact p.Prime] (hf : 1 ≤ f) (hr : 2 ≤ r)
    {B Bs K : Subgroup G} (hBs : GGBstar p B Bs) (hmark : GGInnerDiagOn Bs K)
    (e : ↥K ≃* StatedSp (r + 1) (GaloisField 2 f))
    (hcard : p ^ (r + 1) * Nat.card ↥(Bs ⊓ Subgroup.centralizer (K : Set G)) ≤ Nat.card ↥Bs)
    {ζ : Multiplicative (ZMod p) →* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f)}
    (hζc : SpJoin.SpPlaneConj (GaloisField 2 f) p ζ) :
    Function.Injective (SpJoin.spPlaneTorus (r + 1) ζ) ∧
      ∃ κ : StatedSp (r + 1) (GaloisField 2 f) →* G, Function.Injective κ ∧ κ.range = K ∧
        ∀ b ∈ Bs, ∃ t : Fin (r + 1) → Multiplicative (ZMod p), ∀ s,
          b * κ s * b⁻¹ = κ (SpJoin.spPlaneTorus (r + 1) ζ t * s *
            (SpJoin.spPlaneTorus (r + 1) ζ t)⁻¹) := by
  classical
  let κ₀ : StatedSp (r + 1) (GaloisField 2 f) →* G := K.subtype.comp e.symm.toMonoidHom
  have hκ₀inj : Function.Injective κ₀ := K.subtype_injective.comp e.symm.injective
  have hκ₀range : κ₀.range = K := by
    show (K.subtype.comp e.symm.toMonoidHom).range = K
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr e.symm.surjective, Subgroup.map_top,
      Subgroup.range_subtype]
  have hZ : Subgroup.center K = ⊥ := by
    have h := center_range_statedSp_eq_bot κ₀ hκ₀inj
    rwa [hκ₀range] at h
  have hadm : StatedLieAdmissible .PSp (r + 1) 2 f :=
    ⟨Nat.prime_two, by omega, by omega, by
      intro h
      rw [Prod.mk.injEq] at h
      exact absurd h.1 (by omega)⟩
  have hinner : ∀ b ∈ Bs, ∃ g ∈ K, ∀ k ∈ K, b * k * b⁻¹ = g * k * g⁻¹ :=
    ggSpInnerAction_of_mp hMp (m := r) (by omega) hadm hmark κ₀ hκ₀inj hκ₀range
  exact ggSecFiveBPermSpK_exists_toral_of_inner (D := SpJoin.spPlaneTorus (r + 1) ζ) hBs
    hκ₀inj hκ₀range hZ hinner hcard fun E hE hcardE =>
      (hζc (r + 1) E hE hcardE).elim fun c hc => ⟨MulAut.conj c, hc⟩

end CFSG.StandardType

end
