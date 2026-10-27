module

import Lean
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosDefs
import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosCommAux
import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosRank
import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosPermAux9

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal CFSG.ClassicalInvolution.Phan
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits Matrix

open scoped MatrixGroups

private theorem ggNSPosLE_mem_center_iff {K : Type} [Field K] {n : ℕ} {A : GL (Fin n) K} :
    A ∈ Subgroup.center (GL (Fin n) K) ↔
      ∃ c : Kˣ, A = Matrix.GeneralLinearGroup.scalar (Fin n) c := by
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
  simp only [MonoidHom.mem_range]
  exact ⟨fun ⟨c, hc⟩ => ⟨c, hc.symm⟩, fun ⟨c, hc⟩ => ⟨c, hc.symm⟩⟩

private theorem ggNSPosLE_scalar_ne_zero {K : Type} [Field K] {n : ℕ} (hn : 0 < n)
    {g : GL (Fin n) K} {c : K}
    (hc : ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = Matrix.scalar (Fin n) c) : c ≠ 0 := by
  have hdet := Matrix.GeneralLinearGroup.det_ne_zero g
  rw [hc] at hdet
  have hdet2 : (Matrix.scalar (Fin n) c).det = c ^ n := by
    rw [Matrix.scalar_apply, Matrix.det_diagonal]
    simp [Finset.prod_const]
  rw [hdet2] at hdet
  intro h0
  exact hdet (by rw [h0, zero_pow (by omega)])

private theorem ggNSPosLE_induces_inv {G : Type} [Group G] {K : Type} [Field K] [Finite K] [CharP K 2]
    {f n : ℕ} {ψ : Su K 2 f n →* G} {b : G} {g : GL (Fin n) K}
    (hg : GGInducesUnitary (p := 2) (f := f) ψ b g) :
    GGInducesUnitary (p := 2) (f := f) ψ b⁻¹ g⁻¹ := by
  have hzU : ggIsUnitaryMat (p := 2) (f := f) g⁻¹ := ggNSPosPA_ggIsUnitaryMat_inv hg.1
  refine ⟨hzU, fun x => ?_⟩
  let x' : Su K 2 f n := ⟨g⁻¹ * (x : GL (Fin n) K) * g, InnerDiagSU.conj_mem_SUid hzU x.2⟩
  obtain ⟨y, hy, hby⟩ := hg.2 x'
  have hyx : y = x := by
    apply Subtype.ext
    rw [hy]
    change g * (g⁻¹ * (x : GL (Fin n) K) * g) * g⁻¹ = (x : GL (Fin n) K)
    group
  refine ⟨x', ?_, ?_⟩
  · change (x' : GL (Fin n) K) = g⁻¹ * (x : GL (Fin n) K) * (g⁻¹)⁻¹
    rw [inv_inv]
  · rw [hyx] at hby
    rw [show (b⁻¹)⁻¹ = b from inv_inv b]
    rw [← hby]
    group

private theorem ggNSPosLE_commutator_mem_center {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {K : Type} [Field K] [Finite K] [CharP K 2] {f n : ℕ}
    {ψ : Su K 2 f n →* G} (h : GGNSLocalHyp p B Bs K f n ψ) {b₁ b₂ : G}
    (hb₁ : b₁ ∈ Bs) (hb₂ : b₂ ∈ Bs) {g₁ g₂ : GL (Fin n) K}
    (h₁ : GGInducesUnitary (p := 2) (f := f) ψ b₁ g₁)
    (h₂ : GGInducesUnitary (p := 2) (f := f) ψ b₂ g₂) :
    ggNSPosPF_commutator g₁ g₂ ∈ Subgroup.center (GL (Fin n) K) := by
  rw [Subgroup.mem_center_iff]
  intro u
  obtain ⟨z, hz⟩ := ggNSPosPF_commutator_scalar h hb₁ hb₂ h₁ h₂
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, hz]
  simp [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]

private theorem ggNSPosLE_lift_pow_scalar {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {K : Type} [Field K] [Finite K] [CharP K 2] {f n : ℕ}
    {ψ : Su K 2 f n →* G} (h : GGNSLocalHyp p B Bs K f n ψ) {b : G}
    (hb : b ∈ Bs) {g : GL (Fin n) K} (hg : GGInducesUnitary (p := 2) (f := f) ψ b g) :
    ∃ c : Kˣ, g ^ p = Matrix.GeneralLinearGroup.scalar (Fin n) c := by
  have hbp : b ^ p = 1 := h.bstar.2.1.2 b hb
  have hgp : GGInducesUnitary (p := 2) (f := f) ψ (b ^ p) (g ^ p) :=
    ggNSPosPA7_induces_pow (ψ := ψ) hg p
  rw [hbp] at hgp
  have hzU : ggIsUnitaryMat (p := 2) (f := f) (g ^ p) := hgp.1
  have hzt : ∀ x : Su K 2 f n,
      ψ ⟨(g ^ p) * (x : GL (Fin n) K) * ((g ^ p))⁻¹,
        InnerDiagSU.conj_mem_SUid hzU x.2⟩ = ψ x := by
    intro x
    obtain ⟨w, hw, hbw⟩ := hgp.2 x
    have hw' : w = ⟨(g ^ p) * (x : GL (Fin n) K) * ((g ^ p))⁻¹,
        InnerDiagSU.conj_mem_SUid hzU x.2⟩ := Subtype.ext hw
    rw [hw'] at hbw
    simpa using hbw.symm
  obtain ⟨c, hc⟩ := ggNSPosPA_scalar_of_conj_trivial h hzU hzt
  have hc0 : c ≠ 0 := ggNSPosLE_scalar_ne_zero (n := n) (by have := h.four_le; omega) hc
  refine ⟨Units.mk0 c hc0, ?_⟩
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.coe_scalar]
  exact hc

private theorem ggNSPosLE_mk_eq_of_same_lift {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {K : Type} [Field K] [Finite K] [CharP K 2] {f n : ℕ}
    {ψ : Su K 2 f n →* G} (h : GGNSLocalHyp p B Bs K f n ψ) {b : G}
    {g₁ g₂ : GL (Fin n) K} (h₁ : GGInducesUnitary (p := 2) (f := f) ψ b g₁)
    (h₂ : GGInducesUnitary (p := 2) (f := f) ψ b g₂) :
    QuotientGroup.mk' (Subgroup.center (GL (Fin n) K)) g₁ =
      QuotientGroup.mk' (Subgroup.center (GL (Fin n) K)) g₂ := by
  have hz := ggNSPosPA_conj_inv_mul_of_same_action (ψ := ψ) h₁ h₂
  have hzU : ggIsUnitaryMat (p := 2) (f := f) (g₁⁻¹ * g₂) :=
    ggNSPosPA_ggIsUnitaryMat_mul (ggNSPosPA_ggIsUnitaryMat_inv h₁.1) h₂.1
  obtain ⟨c, hc⟩ := ggNSPosPA_scalar_of_conj_trivial h hzU hz
  have hc0 : c ≠ 0 := ggNSPosLE_scalar_ne_zero (n := n) (by have := h.four_le; omega) hc
  have hmem : g₁⁻¹ * g₂ ∈ Subgroup.center (GL (Fin n) K) :=
    (ggNSPosLE_mem_center_iff).mpr ⟨Units.mk0 c hc0, by
      apply Units.ext
      rw [Matrix.GeneralLinearGroup.coe_scalar]
      exact hc⟩
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply]
  exact QuotientGroup.eq.mpr hmem

private theorem ggNSPosLE_centralizer_of_scalar_lift {G : Type} [Group G] {K : Type} [Field K]
    [Finite K] [CharP K 2] {f n : ℕ} {ψ : Su K 2 f n →* G} {b : G} {g : GL (Fin n) K}
    (hg : GGInducesUnitary (p := 2) (f := f) ψ b g)
    (hc : ∃ c : Kˣ, g = Matrix.GeneralLinearGroup.scalar (Fin n) c) :
    b ∈ Subgroup.centralizer (ψ.range : Set G) := by
  obtain ⟨c, rfl⟩ := hc
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  obtain ⟨x, rfl⟩ := hw
  obtain ⟨z, hz_eq, hz_psi⟩ := hg.2 x
  have hzx : z = x := by
    apply Subtype.ext
    rw [hz_eq]
    rw [Matrix.GeneralLinearGroup.scalar_commute]
    group
  rw [hzx] at hz_psi
  have hb : b * ψ x = ψ x * b := by
    calc b * ψ x = b * ψ x * b⁻¹ * b := by group
      _ = ψ x * b := by rw [hz_psi]
  exact hb.symm

theorem ggNSPosLE_exists_E {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {K : Type} [Field K]
    [Finite K] [CharP K 2] {f n : ℕ} {ψ : Su K 2 f n →* G} (h : GGNSLocalHyp p B Bs K f n ψ) :
    ∃ E : Subgroup (GL (Fin n) K ⧸ Subgroup.center (GL (Fin n) K)),
      CFSG.Open.IsElemAbelian p E ∧ p ^ (n - 3) ≤ Nat.card E ∧ p ^ 3 ≤ Nat.card E ∧
      (∀ b ∈ Bs, ∀ g : GL (Fin n) K, GGInducesUnitary (p := 2) (f := f) ψ b g →
        QuotientGroup.mk' (Subgroup.center (GL (Fin n) K)) g ∈ E) ∧
      (∀ x : GL (Fin n) K, QuotientGroup.mk' (Subgroup.center (GL (Fin n) K)) x ∈ E →
        ∃ b ∈ Bs, ∃ g : GL (Fin n) K, GGInducesUnitary (p := 2) (f := f) ψ b g ∧
          ∃ c : Kˣ, x = g * Matrix.GeneralLinearGroup.scalar (Fin n) c) := by
  classical
  let L : Subgroup (GL (Fin n) K) :=
    { carrier := {g | ∃ b ∈ Bs, GGInducesUnitary (p := 2) (f := f) ψ b g}
      one_mem' := ⟨1, Bs.one_mem, by
        simpa using ggNSPosPA_induces_self (ψ := ψ) (1 : Su K 2 f n)⟩
      mul_mem' := by
        rintro a b ⟨b₁, hb₁, ha⟩ ⟨b₂, hb₂, hb⟩
        exact ⟨b₁ * b₂, Bs.mul_mem hb₁ hb₂, ggNSPosPA7_induces_mul ha hb⟩
      inv_mem' := by
        rintro a ⟨b, hb, ha⟩
        exact ⟨b⁻¹, Bs.inv_mem hb, ggNSPosLE_induces_inv ha⟩ }
  let mk := QuotientGroup.mk' (Subgroup.center (GL (Fin n) K))
  have hmk : ∀ g : GL (Fin n) K,
      mk g = (↑g : GL (Fin n) K ⧸ Subgroup.center (GL (Fin n) K)) :=
    fun g => QuotientGroup.mk'_apply _ g
  let E : Subgroup (GL (Fin n) K ⧸ Subgroup.center (GL (Fin n) K)) := Subgroup.map mk L
  have hBle : B ≤ Bs := h.bstar.1
  let lift : ↥B → GL (Fin n) K := fun b => Classical.choose (h.acts (b : G) (hBle b.2))
  have hlift : ∀ b : ↥B, GGInducesUnitary (p := 2) (f := f) ψ (b : G) (lift b) :=
    fun b => Classical.choose_spec (h.acts (b : G) (hBle b.2))
  let ρ : ↥B →* (GL (Fin n) K ⧸ Subgroup.center (GL (Fin n) K)) :=
    { toFun := fun b => mk (lift b)
      map_one' := by
        have h1 : GGInducesUnitary (p := 2) (f := f) ψ (1 : G) (lift 1) := by
          simpa using hlift 1
        have h2 : GGInducesUnitary (p := 2) (f := f) ψ (1 : G) (1 : GL (Fin n) K) := by
          simpa using ggNSPosPA_induces_self (ψ := ψ) (1 : Su K 2 f n)
        rw [ggNSPosLE_mk_eq_of_same_lift h h1 h2]
        exact map_one mk
      map_mul' := by
        intro b₁ b₂
        have h1 : GGInducesUnitary (p := 2) (f := f) ψ ((b₁ * b₂ : ↥B) : G) (lift (b₁ * b₂)) :=
          hlift (b₁ * b₂)
        have h2 : GGInducesUnitary (p := 2) (f := f) ψ ((b₁ * b₂ : ↥B) : G) (lift b₁ * lift b₂) := by
          have hm := ggNSPosPA7_induces_mul (hlift b₁) (hlift b₂)
          simpa only [Subgroup.coe_mul] using hm
        rw [ggNSPosLE_mk_eq_of_same_lift h h1 h2, map_mul] }
  have hrange_le : ρ.range ≤ E := by
    rintro y ⟨b, rfl⟩
    exact Subgroup.mem_map_of_mem mk ⟨(b : G), hBle b.2, hlift b⟩
  have hker_le : Subgroup.map (Subgroup.subtype B) ρ.ker ≤
      B ⊓ Subgroup.centralizer (ψ.range : Set G) := by
    rintro x ⟨b, hbker, rfl⟩
    rw [Subgroup.mem_inf]
    refine ⟨b.2, ?_⟩
    have hρb : ρ b = 1 := (MonoidHom.mem_ker).mp hbker
    have hmem : lift b ∈ Subgroup.center (GL (Fin n) K) := by
      have h1 : mk (lift b) = 1 := hρb
      rw [hmk (lift b), QuotientGroup.eq_one_iff] at h1
      exact h1
    obtain ⟨c, hc⟩ := (ggNSPosLE_mem_center_iff).mp hmem
    exact ggNSPosLE_centralizer_of_scalar_lift (hlift b) ⟨c, hc⟩
  have hcardmap : Nat.card (Subgroup.map (Subgroup.subtype B) ρ.ker) = Nat.card ρ.ker :=
    Subgroup.card_map_of_injective (K := ρ.ker) (f := Subgroup.subtype B) (fun a b hab => Subtype.ext hab)
  have hcardker : Nat.card ρ.ker ≤ p := by
    rw [← hcardmap]
    calc Nat.card (Subgroup.map (Subgroup.subtype B) ρ.ker)
        ≤ Nat.card ↥(B ⊓ Subgroup.centralizer (ψ.range : Set G)) := Subgroup.card_le_of_le hker_le
      _ = p := h.cent
  have hcardrange : Nat.card ρ.range ≤ Nat.card E := Subgroup.card_le_of_le hrange_le
  have hbound : Nat.card ↥B ≤ p * Nat.card E := by
    rw [← Subgroup.card_ker_mul_card_range ρ]
    exact Nat.mul_le_mul hcardker hcardrange
  have hrank : p ^ (n - 2) ≤ Nat.card ↥B := ggNSLocal_rank_ge h
  have hpq : 0 < p := h.prime.pos
  have hn4 : 4 ≤ n := h.four_le
  have hpow : p ^ (n - 2) = p * p ^ (n - 3) := by
    rw [show n - 2 = (n - 3) + 1 by omega, pow_succ, mul_comm]
  have hgeom : p ^ (n - 3) ≤ Nat.card E := by
    refine Nat.le_of_mul_le_mul_left ?_ hpq
    rw [← hpow]
    exact hrank.trans hbound
  have hpow4 : p ^ 4 = p * p ^ 3 := by ring
  have hthree : p ^ 3 ≤ Nat.card E := by
    refine Nat.le_of_mul_le_mul_left ?_ hpq
    rw [← hpow4]
    exact h.rank.trans hbound
  refine ⟨E, ?_, hgeom, hthree, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · rw [isMulCommutative_iff]
      intro a b
      obtain ⟨u, huL, hu⟩ := Subgroup.mem_map.mp a.2
      obtain ⟨v, hvL, hv⟩ := Subgroup.mem_map.mp b.2
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hu, ← hv]
      obtain ⟨b₁, hb₁, h₁⟩ := huL
      obtain ⟨b₂, hb₂, h₂⟩ := hvL
      have hcomm := ggNSPosLE_commutator_mem_center h hb₁ hb₂ h₁ h₂
      have hcomm1 : mk (ggNSPosPF_commutator u v) = 1 := by
        rw [hmk (ggNSPosPF_commutator u v), QuotientGroup.eq_one_iff]
        exact hcomm
      have hmul : u * v = ggNSPosPF_commutator u v * (v * u) := by
        unfold ggNSPosPF_commutator
        group
      calc mk u * mk v = mk (u * v) := (map_mul mk u v).symm
        _ = mk (ggNSPosPF_commutator u v * (v * u)) := by rw [hmul]
        _ = mk (ggNSPosPF_commutator u v) * (mk v * mk u) := by rw [map_mul, map_mul]
        _ = 1 * (mk v * mk u) := by rw [hcomm1]
        _ = mk v * mk u := one_mul _
    · intro x hx
      obtain ⟨u, huL, hu⟩ := Subgroup.mem_map.mp hx
      obtain ⟨b, hb, hbind⟩ := huL
      rw [← hu]
      obtain ⟨c, hc⟩ := ggNSPosLE_lift_pow_scalar h hb hbind
      calc (mk u) ^ p = mk (u ^ p) := (map_pow mk u p).symm
        _ = mk (Matrix.GeneralLinearGroup.scalar (Fin n) c) := by rw [hc]
        _ = 1 := by
          rw [hmk, QuotientGroup.eq_one_iff]
          exact (ggNSPosLE_mem_center_iff).mpr ⟨c, rfl⟩
  · intro b hb g hg
    exact Subgroup.mem_map_of_mem mk ⟨b, hb, hg⟩
  · intro x hx
    obtain ⟨u, huL, hu⟩ := Subgroup.mem_map.mp hx
    obtain ⟨b, hb, hbind⟩ := huL
    have hux : u⁻¹ * x ∈ Subgroup.center (GL (Fin n) K) := by
      have h1 : (↑u : GL (Fin n) K ⧸ Subgroup.center (GL (Fin n) K)) = ↑x := by
        rw [← hmk u, ← hmk x]
        exact hu
      exact QuotientGroup.eq.mp h1
    obtain ⟨c, hc⟩ := (ggNSPosLE_mem_center_iff).mp hux
    refine ⟨b, hb, u, hbind, c, ?_⟩
    rw [← hc]
    group

end CFSG.StandardType

end
