module

public import CFSG.RankThree.GF2n.Stroth80.Sec11TorusPhi
public import CFSG.RankThree.GF2n.Stroth80.Sec3Defs
import CFSG.RankThree.GF2n.Stroth80.Sec11TorusElt
import CFSG.RankThree.GF2n.Stroth80.Sec34Trans

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

section Def

variable {G : Type} [Group G]

structure IsLBTorus (M Q Z B : Subgroup G) [(Q.subgroupOf M).Normal] (y : G) : Prop where
  mem_sup : y ∈ Q ⊔ QB B
  mem_M : y ∈ M
  normalizes_Z : y ∈ Subgroup.normalizer (Z : Set G)
  normalizes_B : y ∈ Subgroup.normalizer (B : Set G)
  orderOf_eq : orderOf y = Nat.card Z - 1
  regular_Z : ∀ i : ℕ, 0 < i → i < Nat.card Z - 1 → ∀ v ∈ Z, y ^ i * v = v * y ^ i → v = 1
  fpf : ∀ i : ℕ, 0 < i → i < Nat.card Z - 1 → ∀ l ∈ LB M Q B,
    y ^ i * l * (y ^ i)⁻¹ * l⁻¹ ∈ Q → l ∈ Q
  card_invariant : ∀ U : Subgroup (Mbar M Q), U ≤ bar M Q (LB M Q B) →
    (∀ u ∈ U, QuotientGroup.mk' (Q.subgroupOf M) ⟨y, mem_M⟩ * u *
      (QuotientGroup.mk' (Q.subgroupOf M) ⟨y, mem_M⟩)⁻¹ ∈ U) →
    ∃ d : ℕ, Nat.card U = Nat.card Z ^ d
  comm_centralizes : ∀ k ∈ Subgroup.centralizer (Z : Set G),
    k ∈ Subgroup.normalizer (B : Set G) → ∀ l ∈ LB M Q B, ⁅y * k * y⁻¹ * k⁻¹, l⁆ ∈ Q
  line_closed : ∀ l ∈ LB M Q B, ∀ i j : ℕ,
    y ^ i * l * (y ^ i)⁻¹ * (y ^ j * l * (y ^ j)⁻¹) ∈ Q ∨
      ∃ k < Nat.card Z - 1, y ^ i * l * (y ^ i)⁻¹ * (y ^ j * l * (y ^ j)⁻¹) *
        (y ^ k * l * (y ^ k)⁻¹)⁻¹ ∈ Q

end Def

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

variable [(Q.subgroupOf M).Normal]

private theorem abelianization_of_injective (hc : Ctx M Q Z B) :
    Function.Injective (Abelianization.of :
      ↥(bar M Q (LB M Q B)) →* Abelianization ↥(bar M Q (LB M Q B))) := by
  have := hc.isElemAbelian_bar_LB.1
  exact (MonoidHom.ker_eq_bot_iff _).mp (by rw [Abelianization.ker_of, commutator_eq_bot])

private noncomputable def lbVecOf {U : Subgroup (Mbar M Q)} (hU : U ≤ bar M Q (LB M Q B))
    (u : ↥U) : LBSpace M Q B :=
  Additive.ofMul (Abelianization.of ⟨u, hU u.2⟩)

private theorem lbVecOf_injective (hc : Ctx M Q Z B) {U : Subgroup (Mbar M Q)}
    (hU : U ≤ bar M Q (LB M Q B)) : Function.Injective (lbVecOf hU) := by
  intro u u' h
  have h1 := abelianization_of_injective hc (Additive.ofMul.injective h)
  exact Subtype.ext (congrArg (fun x : ↥(bar M Q (LB M Q B)) => (x : Mbar M Q)) h1)

omit [Finite G] in
private theorem lbVecOf_mul {U : Subgroup (Mbar M Q)} (hU : U ≤ bar M Q (LB M Q B))
    (u u' : ↥U) : lbVecOf hU (u * u') = lbVecOf hU u + lbVecOf hU u' :=
  congrArg Additive.ofMul (map_mul Abelianization.of (⟨u, hU u.2⟩ : ↥(bar M Q (LB M Q B)))
    ⟨u', hU u'.2⟩)

omit [Finite G] in
private theorem lbVecOf_one {U : Subgroup (Mbar M Q)} (hU : U ≤ bar M Q (LB M Q B)) :
    lbVecOf hU 1 = 0 :=
  congrArg Additive.ofMul (map_one (Abelianization.of (G := ↥(bar M Q (LB M Q B)))))

namespace LBFrame

variable (fr : LBFrame Q Z B)

omit [Finite G] in
private theorem regular_Z_of_phi {y : G} (hy : y ∈ Q ⊔ QB B) {c : fr.Kˣ}
    (hc0 : orderOf c = Nat.card Z - 1)
    (hφ : fr.φ ⟨y, hy⟩ = Timmesfeld.ARS.NaturalModule.diagElt c⁻¹) {i : ℕ} (hi0 : 0 < i)
    (hi : i < Nat.card Z - 1) {v : G} (hv : v ∈ Z) (hyv : y ^ i * v = v * y ^ i) : v = 1 := by
  have hpow : ∀ n : ℕ, (Timmesfeld.ARS.NaturalModule.diagElt c⁻¹) ^ n =
      Timmesfeld.ARS.NaturalModule.diagElt (c⁻¹ ^ n) := by
    intro n
    induction n with
    | zero => rw [pow_zero, pow_zero, Timmesfeld.ARS.NaturalModule.diagElt_one]
    | succ n ih => rw [pow_succ, ih, Timmesfeld.ARS.NaturalModule.diagElt_mul_diagElt, pow_succ]
  have hφi : fr.φ (⟨y, hy⟩ ^ i) = Timmesfeld.ARS.NaturalModule.diagElt (c⁻¹ ^ i) := by
    rw [map_pow, hφ, hpow]
  rcases fr.diag_fix_Z (⟨y, hy⟩ ^ i) (c⁻¹ ^ i) hφi hv (by simpa using hyv) with h | h
  · exfalso
    have h1 := orderOf_dvd_of_pow_eq_one h
    rw [orderOf_inv, hc0] at h1
    have := Nat.le_of_dvd hi0 h1
    omega
  · exact h

private theorem fpf_of_action (hc : Ctx M Q Z B) {y : G} (hyM : y ∈ M)
    (hyB : y ∈ Subgroup.normalizer (B : Set G)) {c : fr.Kˣ} (hc0 : orderOf c = Nat.card Z - 1)
    (hact : ∀ a ∈ QB B ⊓ M, lbVec M Q B (y * a * y⁻¹) = fr.lbPhiHom hc c (lbVec M Q B a))
    {i : ℕ} (hi0 : 0 < i) (hi : i < Nat.card Z - 1) {l : G} (hl : l ∈ LB M Q B)
    (h : y ^ i * l * (y ^ i)⁻¹ * l⁻¹ ∈ Q) : l ∈ Q := by
  have hX := hc.conj_mem_LB_of_mem_normalizer (M.pow_mem hyM i) (Subgroup.pow_mem _ hyB i) hl
  have hli : l⁻¹ ∈ LB M Q B := Subgroup.inv_mem _ hl
  have h1 : lbVec M Q B (y ^ i * l * (y ^ i)⁻¹) = lbVec M Q B l := by
    rw [lbVec_eq_of_mul_mem hc hX hli h, lbVec_eq_of_mul_mem hc hli hl (by simp)]
  rw [fr.lbVec_conj_pow hc hyM hyB hact i hl] at h1
  have hne : (c : fr.K) ^ i + 1 ≠ 0 := by
    intro h0
    have h2 : c ^ i = 1 := Units.ext (by
      rw [Units.val_pow_eq_pow_val]
      exact CharTwo.add_eq_zero.mp h0)
    have h3 := orderOf_dvd_of_pow_eq_one h2
    rw [hc0] at h3
    have := Nat.le_of_dvd hi0 h3
    omega
  have h2 : fr.lbPhiHom hc ((c : fr.K) ^ i + 1) (lbVec M Q B l) = 0 := by
    rw [fr.lbPhiHom_add_apply, fr.lbPhiHom_one_apply, h1, lbVec_add_self hc hl]
  have h3 : lbVec M Q B l = 0 := by
    rw [← fr.lbPhiHom_one_apply hc (lbVec M Q B l), ← inv_mul_cancel₀ hne,
      fr.lbPhiHom_mul_apply, h2, map_zero]
  exact (lbVec_eq_zero_iff hc hl).mp h3

private theorem lbPhiHom_lbVecOf (hc : Ctx M Q Z B) {y : G} (hyM : y ∈ M)
    (hyB : y ∈ Subgroup.normalizer (B : Set G)) {c : fr.K}
    (hact : ∀ a ∈ QB B ⊓ M, lbVec M Q B (y * a * y⁻¹) = fr.lbPhiHom hc c (lbVec M Q B a))
    {U : Subgroup (Mbar M Q)} (hU : U ≤ bar M Q (LB M Q B))
    (hinv : ∀ u ∈ U, QuotientGroup.mk' (Q.subgroupOf M) ⟨y, hyM⟩ * u *
      (QuotientGroup.mk' (Q.subgroupOf M) ⟨y, hyM⟩)⁻¹ ∈ U) (u : ↥U) :
    fr.lbPhiHom hc c (lbVecOf hU u) = lbVecOf hU ⟨_, hinv u u.2⟩ := by
  obtain ⟨m, hm, hmu⟩ := Subgroup.mem_map.mp (hU u.2)
  have hmLB : (m : G) ∈ LB M Q B := Subgroup.mem_subgroupOf.mp hm
  have hymLB := hc.conj_mem_LB_of_mem_normalizer hyM hyB hmLB
  have h1 : lbVecOf hU u = lbVec M Q B m := (lbVec_of_mem ⟨hmLB, m.2⟩ ⟨u, hU u.2⟩ hmu).symm
  have h2 : lbVecOf hU ⟨_, hinv u u.2⟩ = lbVec M Q B (y * m * y⁻¹) := by
    refine (lbVec_of_mem ⟨hymLB, hc.LB_le_M hymLB⟩ ⟨_, hU (hinv u u.2)⟩ ?_).symm
    show QuotientGroup.mk' (Q.subgroupOf M) ⟨y * m * y⁻¹, hc.LB_le_M hymLB⟩ =
      QuotientGroup.mk' (Q.subgroupOf M) ⟨y, hyM⟩ * ↑u *
        (QuotientGroup.mk' (Q.subgroupOf M) ⟨y, hyM⟩)⁻¹
    have e : QuotientGroup.mk' (Q.subgroupOf M) ⟨y * m * y⁻¹, hc.LB_le_M hymLB⟩ =
        QuotientGroup.mk' (Q.subgroupOf M) (⟨y, hyM⟩ * m * ⟨y, hyM⟩⁻¹) := rfl
    rw [e, map_mul, map_mul, map_inv, hmu]
  have h3 := fr.lbVec_conj_pow hc hyM hyB hact 1 hmLB
  rw [pow_one, pow_one] at h3
  rw [h1, h2, h3]

private theorem lbPhiHom_mem_range (hc : Ctx M Q Z B) {y : G} (hyM : y ∈ M)
    (hyB : y ∈ Subgroup.normalizer (B : Set G)) {c : fr.Kˣ} (hc0 : orderOf c = Nat.card Z - 1)
    (hact : ∀ a ∈ QB B ⊓ M, lbVec M Q B (y * a * y⁻¹) = fr.lbPhiHom hc c (lbVec M Q B a))
    {U : Subgroup (Mbar M Q)} (hU : U ≤ bar M Q (LB M Q B))
    (hinv : ∀ u ∈ U, QuotientGroup.mk' (Q.subgroupOf M) ⟨y, hyM⟩ * u *
      (QuotientGroup.mk' (Q.subgroupOf M) ⟨y, hyM⟩)⁻¹ ∈ U) (t : fr.K) {v : LBSpace M Q B}
    (hv : v ∈ Set.range (lbVecOf hU)) : fr.lbPhiHom hc t v ∈ Set.range (lbVecOf hU) := by
  have hpow : ∀ (k : ℕ) (v : LBSpace M Q B), v ∈ Set.range (lbVecOf hU) →
      fr.lbPhiHom hc ((c : fr.K) ^ k) v ∈ Set.range (lbVecOf hU) := by
    intro k
    induction k with
    | zero => intro v hv; rwa [pow_zero, fr.lbPhiHom_one_apply]
    | succ k ih =>
      intro v hv
      obtain ⟨u, hu⟩ := ih v hv
      rw [pow_succ', fr.lbPhiHom_mul_apply, ← hu, fr.lbPhiHom_lbVecOf hc hyM hyB hact hU hinv u]
      exact ⟨_, rfl⟩
  by_cases ht : t = 0
  · rw [ht, map_zero]
    exact ⟨1, lbVecOf_one hU⟩
  obtain ⟨k, -, hk⟩ := fr.exists_pow_lt_eq hc hc0 (Units.mk0 t ht)
  have htk : t = (c : fr.K) ^ k := by rw [← Units.val_pow_eq_pow_val, hk, Units.val_mk0]
  rw [htk]
  exact hpow k v hv

private theorem card_invariant_of_action (hc : Ctx M Q Z B) {y : G} (hyM : y ∈ M)
    (hyB : y ∈ Subgroup.normalizer (B : Set G)) {c : fr.Kˣ} (hc0 : orderOf c = Nat.card Z - 1)
    (hact : ∀ a ∈ QB B ⊓ M, lbVec M Q B (y * a * y⁻¹) = fr.lbPhiHom hc c (lbVec M Q B a))
    (U : Subgroup (Mbar M Q)) (hU : U ≤ bar M Q (LB M Q B))
    (hinv : ∀ u ∈ U, QuotientGroup.mk' (Q.subgroupOf M) ⟨y, hyM⟩ * u *
      (QuotientGroup.mk' (Q.subgroupOf M) ⟨y, hyM⟩)⁻¹ ∈ U) :
    ∃ d : ℕ, Nat.card U = Nat.card Z ^ d := by
  let _ : Module fr.K (LBSpace M Q B) := Module.compHom _ (fr.lbPhiHom hc)
  let W : Submodule fr.K (LBSpace M Q B) :=
    { carrier := Set.range (lbVecOf hU)
      add_mem' := by
        rintro _ _ ⟨u, rfl⟩ ⟨u', rfl⟩
        exact ⟨u * u', lbVecOf_mul hU u u'⟩
      zero_mem' := ⟨1, lbVecOf_one hU⟩
      smul_mem' := fun t v hv => fr.lbPhiHom_mem_range hc hyM hyB hc0 hact hU hinv t hv }
  refine ⟨Module.finrank fr.K W, ?_⟩
  rw [← fr.natCard_K_eq hc, ← Module.natCard_eq_pow_finrank (K := fr.K) (V := ↥W)]
  exact (Nat.card_range_of_injective (lbVecOf_injective hc hU)).symm

private theorem lbVec_conj_mul_comm (hc : Ctx M Q Z B) {y : G} (hyM : y ∈ M)
    (hyB : y ∈ Subgroup.normalizer (B : Set G)) {c : fr.K}
    (hact : ∀ a ∈ QB B ⊓ M, lbVec M Q B (y * a * y⁻¹) = fr.lbPhiHom hc c (lbVec M Q B a))
    {k : G} (hkZ : k ∈ Subgroup.centralizer (Z : Set G))
    (hkB : k ∈ Subgroup.normalizer (B : Set G)) {a : G} (ha : a ∈ QB B ⊓ M) :
    lbVec M Q B (y * k * a * (y * k)⁻¹) = lbVec M Q B (k * y * a * (k * y)⁻¹) := by
  have hkM : k ∈ M := hc.hyp.normalizer_Z.1 ▸ Subgroup.centralizer_le_normalizer _ hkZ
  have hka := hc.conj_mem_PB_of_mem_normalizer hkM hkB ha
  have hya := hc.conj_mem_PB_of_mem_normalizer hyM hyB ha
  have hb := fr.lbPhi_mem hc c ha
  have h2 : (y * a * y⁻¹)⁻¹ * fr.lbPhi c a ∈ Q := by
    rw [← lbVec_eq_iff hc (mem_LB_of_mem_QB_inf hya) (mem_LB_of_mem_QB_inf hb), hact a ha,
      fr.lbPhiHom_apply, fr.lbPhiEnd_lbVec hc c ha]
  have h3 : (k * (y * a * y⁻¹) * k⁻¹)⁻¹ * (k * fr.lbPhi c a * k⁻¹) ∈ Q := by
    have e : (k * (y * a * y⁻¹) * k⁻¹)⁻¹ * (k * fr.lbPhi c a * k⁻¹) =
        k * ((y * a * y⁻¹)⁻¹ * fr.lbPhi c a) * k⁻¹ := by group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hkM) _).mp h2
  have hkya := hc.conj_mem_PB_of_mem_normalizer hkM hkB hya
  have hkb := hc.conj_mem_PB_of_mem_normalizer hkM hkB hb
  have e1 : y * k * a * (y * k)⁻¹ = y * (k * a * k⁻¹) * y⁻¹ := by group
  have e2 : k * y * a * (k * y)⁻¹ = k * (y * a * y⁻¹) * k⁻¹ := by group
  rw [e1, e2, hact _ hka,
    (lbVec_eq_iff hc (mem_LB_of_mem_QB_inf hkya) (mem_LB_of_mem_QB_inf hkb)).mpr h3,
    (lbVec_eq_iff hc (mem_LB_of_mem_QB_inf hkb)
      (mem_LB_of_mem_QB_inf (fr.lbPhi_mem hc c hka))).mpr (fr.lbPhi_conj hc hkZ hkB c ha),
    ← fr.lbPhiEnd_lbVec hc c hka, ← fr.lbPhiHom_apply]

private theorem lbVec_conj_eq_of_PB (hc : Ctx M Q Z B) {g g' : G} (hgM : g ∈ M) (hg'M : g' ∈ M)
    (hgB : g ∈ Subgroup.normalizer (B : Set G)) (hg'B : g' ∈ Subgroup.normalizer (B : Set G))
    (h : ∀ a ∈ QB B ⊓ M, lbVec M Q B (g * a * g⁻¹) = lbVec M Q B (g' * a * g'⁻¹)) {l : G}
    (hl : l ∈ LB M Q B) : lbVec M Q B (g * l * g⁻¹) = lbVec M Q B (g' * l * g'⁻¹) := by
  obtain ⟨s, hs, q, hq, rfl⟩ := hc.exists_mul_of_mem_LB hl
  have hQ : ∀ {x : G}, x ∈ Q → x ∈ LB M Q B := fun hx => (le_sup_left : Q ≤ Q ⊔ (QB B ⊓ M)) hx
  have key : ∀ {g : G}, g ∈ M → g ∈ Subgroup.normalizer (B : Set G) →
      lbVec M Q B (g * (s * q) * g⁻¹) = lbVec M Q B (g * s * g⁻¹) := by
    intro g hgM hgB
    have hgq : g * q * g⁻¹ ∈ Q :=
      (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hgM) q).mp hq
    have e : g * (s * q) * g⁻¹ = (g * s * g⁻¹) * (g * q * g⁻¹) := by group
    rw [e, lbVec_mul hc (mem_LB_of_mem_QB_inf (hc.conj_mem_PB_of_mem_normalizer hgM hgB hs))
      (hQ hgq), (lbVec_eq_zero_iff hc (hQ hgq)).mpr hgq, add_zero]
  rw [key hgM hgB, key hg'M hg'B, h s hs]

private theorem comm_centralizes_of_action (hc : Ctx M Q Z B) {y : G} (hyM : y ∈ M)
    (hyB : y ∈ Subgroup.normalizer (B : Set G)) {c : fr.K}
    (hact : ∀ a ∈ QB B ⊓ M, lbVec M Q B (y * a * y⁻¹) = fr.lbPhiHom hc c (lbVec M Q B a))
    {k : G} (hkZ : k ∈ Subgroup.centralizer (Z : Set G))
    (hkB : k ∈ Subgroup.normalizer (B : Set G)) {l : G} (hl : l ∈ LB M Q B) :
    ⁅y * k * y⁻¹ * k⁻¹, l⁆ ∈ Q := by
  have hkM : k ∈ M := hc.hyp.normalizer_Z.1 ▸ Subgroup.centralizer_le_normalizer _ hkZ
  have hg2M : k * y ∈ M := M.mul_mem hkM hyM
  have hg2B : k * y ∈ Subgroup.normalizer (B : Set G) := Subgroup.mul_mem _ hkB hyB
  have hl' := hc.conj_mem_LB_of_mem_normalizer (M.inv_mem hg2M) (Subgroup.inv_mem _ hg2B) hl
  have h1 := lbVec_conj_eq_of_PB hc (M.mul_mem hyM hkM) hg2M (Subgroup.mul_mem _ hyB hkB) hg2B
    (fun a ha => fr.lbVec_conj_mul_comm hc hyM hyB hact hkZ hkB ha) hl'
  rw [show y * k * ((k * y)⁻¹ * l * (k * y)⁻¹⁻¹) * (y * k)⁻¹ =
      y * k * y⁻¹ * k⁻¹ * l * (y * k * y⁻¹ * k⁻¹)⁻¹ by group,
    show k * y * ((k * y)⁻¹ * l * (k * y)⁻¹⁻¹) * (k * y)⁻¹ = l by group] at h1
  have hgM : y * k * y⁻¹ * k⁻¹ ∈ M :=
    M.mul_mem (M.mul_mem (M.mul_mem hyM hkM) (M.inv_mem hyM)) (M.inv_mem hkM)
  have hgB : y * k * y⁻¹ * k⁻¹ ∈ Subgroup.normalizer (B : Set G) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hyB hkB)
      (Subgroup.inv_mem _ hyB)) (Subgroup.inv_mem _ hkB)
  have hgl := hc.conj_mem_LB_of_mem_normalizer hgM hgB hl
  have h2 := (lbVec_eq_iff hc hgl hl).mp h1
  have e : ⁅y * k * y⁻¹ * k⁻¹, l⁆ = (y * k * y⁻¹ * k⁻¹ * l * (y * k * y⁻¹ * k⁻¹)⁻¹) *
      ((y * k * y⁻¹ * k⁻¹ * l * (y * k * y⁻¹ * k⁻¹)⁻¹)⁻¹ * l)⁻¹ *
      (y * k * y⁻¹ * k⁻¹ * l * (y * k * y⁻¹ * k⁻¹)⁻¹)⁻¹ := by
    simp only [commutatorElement_def]
    group
  rw [e]
  exact (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 (hc.LB_le_M hgl)) _).mp (Q.inv_mem h2)

private theorem line_closed_of_action (hc : Ctx M Q Z B) {y : G} (hyM : y ∈ M)
    (hyB : y ∈ Subgroup.normalizer (B : Set G)) {c : fr.Kˣ} (hc0 : orderOf c = Nat.card Z - 1)
    (hact : ∀ a ∈ QB B ⊓ M, lbVec M Q B (y * a * y⁻¹) = fr.lbPhiHom hc c (lbVec M Q B a))
    {l : G} (hl : l ∈ LB M Q B) (i j : ℕ) :
    y ^ i * l * (y ^ i)⁻¹ * (y ^ j * l * (y ^ j)⁻¹) ∈ Q ∨
      ∃ k < Nat.card Z - 1, y ^ i * l * (y ^ i)⁻¹ * (y ^ j * l * (y ^ j)⁻¹) *
        (y ^ k * l * (y ^ k)⁻¹)⁻¹ ∈ Q := by
  have hX : ∀ n : ℕ, y ^ n * l * (y ^ n)⁻¹ ∈ LB M Q B := fun n =>
    hc.conj_mem_LB_of_mem_normalizer (M.pow_mem hyM n) (Subgroup.pow_mem _ hyB n) hl
  have hv : ∀ n : ℕ, lbVec M Q B (y ^ n * l * (y ^ n)⁻¹) =
      fr.lbPhiHom hc ((c : fr.K) ^ n) (lbVec M Q B l) := fun n =>
    fr.lbVec_conj_pow hc hyM hyB hact n hl
  have hij := Subgroup.mul_mem _ (hX i) (hX j)
  have hsum : lbVec M Q B (y ^ i * l * (y ^ i)⁻¹ * (y ^ j * l * (y ^ j)⁻¹)) =
      fr.lbPhiHom hc ((c : fr.K) ^ i + (c : fr.K) ^ j) (lbVec M Q B l) := by
    rw [lbVec_mul hc (hX i) (hX j), hv i, hv j, fr.lbPhiHom_add_apply]
  by_cases h0 : (c : fr.K) ^ i + (c : fr.K) ^ j = 0
  · left
    rw [← lbVec_eq_zero_iff hc hij, hsum, h0]
    simp
  · right
    obtain ⟨k, hk, hck⟩ := fr.exists_pow_lt_eq hc hc0 (Units.mk0 _ h0)
    refine ⟨k, hk, ?_⟩
    have hk' : (c : fr.K) ^ k = (c : fr.K) ^ i + (c : fr.K) ^ j := by
      have := congrArg Units.val hck
      rwa [Units.val_pow_eq_pow_val, Units.val_mk0] at this
    have hki := Subgroup.inv_mem _ (hX k)
    rw [← lbVec_eq_zero_iff hc (Subgroup.mul_mem _ hij hki), lbVec_mul hc hij hki, hsum,
      lbVec_eq_of_mul_mem hc hki (hX k) (by rw [inv_mul_cancel]; exact Q.one_mem), hv k, hk']
    exact lbSpace_add_self hc _

theorem exists_isLBTorus_action (hc : Ctx M Q Z B) :
    ∃ (y : G) (c : fr.Kˣ), IsLBTorus M Q Z B y ∧ orderOf c = Nat.card Z - 1 ∧
      ∀ a ∈ QB B ⊓ M, lbVec M Q B (y * a * y⁻¹) = fr.lbPhiHom hc c (lbVec M Q B a) := by
  obtain ⟨y, hy, c, hc0, hyo, hφ, hact⟩ := fr.exists_lbTorus hc
  obtain ⟨hyZ, hyB⟩ := fr.diag_normalizes hc ⟨y, hy⟩ c⁻¹ hφ
  have hyM : y ∈ M := hc.hyp.normalizer_Z.1 ▸ hyZ
  refine ⟨y, c, ⟨hy, hyM, hyZ, hyB, hyo, ?_, ?_, ?_, ?_, ?_⟩, hc0, hact⟩
  · exact fun i hi0 hi v hv h => regular_Z_of_phi fr hy hc0 hφ hi0 hi hv h
  · exact fun i hi0 hi l hl h => fpf_of_action fr hc hyM hyB hc0 hact hi0 hi hl h
  · exact fun U hU hinv => card_invariant_of_action fr hc hyM hyB hc0 hact U hU hinv
  · exact fun k hkZ hkB l hl => comm_centralizes_of_action fr hc hyM hyB hact hkZ hkB hl
  · exact fun l hl i j => line_closed_of_action fr hc hyM hyB hc0 hact hl i j

end LBFrame

theorem Ctx.exists_isLBTorus (hc : Ctx M Q Z B) : ∃ y : G, IsLBTorus M Q Z B y := by
  obtain ⟨fr⟩ := hc.nonempty_lbFrame
  obtain ⟨y, -, hy, -⟩ := fr.exists_isLBTorus_action hc
  exact ⟨y, hy⟩

end CFSG.RankThree.GF2n.Stroth80
