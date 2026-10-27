module

public import CFSG.Open.PGLModelDefs
import CFSG.RankThree.PartTwo.Sec20.SimsAsc1412L3F3U3Core
import CFSG.RankThree.PartTwo.Sec20.SimsAsc1412L3Outer
import CFSG.Open.PGLModelStated

public section

namespace CFSG.RankThree.PartTwo.Sec20

open CFSG.PGLModel (projSU)
open CFSG.UnitaryThreeRecognition.Model CFSG.BenderSuzuki.MatrixGroups
open scoped MatrixGroups

theorem gen_normalizer_omega1412_U3 {G : Type} [Group G] [Finite G] {L : Subgroup G} [L.Normal]
    (hC : Subgroup.centralizer (L : Set G) = ⊥) {p : ℕ} [Fact p.Prime] (hp3 : 3 < p)
    (hp : p % 3 = 1) (e : ↥L ≃* projSU 3 p 1) {b : G} (hbL : b ∉ L)
    (hb2 : orderOf b = 2) {y : G} (hyL : y ∈ L) (hy3 : orderOf y = 3) :
    L ≤ Subgroup.normalizer (Subgroup.zpowers y : Set G) ⊔
      ⁅L ⊓ Subgroup.centralizer {b}, L ⊓ Subgroup.centralizer {b}⁆ := by
  have hpp : p.Prime := Fact.out
  have hp7 : 7 ≤ p := by
    rcases (show p = 4 ∨ 7 ≤ p by omega) with h | h
    · exact absurd (h ▸ hpp) (by norm_num)
    · exact h
  obtain ⟨⟨eΩ⟩, -, -, -⟩ := outerData1412 hC ⟨hp3, Or.inr ⟨hp, ⟨e⟩⟩⟩ hbL hb2
  have hcard : Nat.card (GaloisField p (2 * 1)) = (p ^ 1) ^ 2 := by
    rw [GaloisField.card p (2 * 1) (by norm_num), ← pow_mul, mul_comm]
  obtain ⟨J, hJ, -, hfix⟩ := exists_standardHermitianForm (K := GaloisField p (2 * 1)) p 1 hcard
  obtain ⟨e₁⟩ := nonempty_psu_equiv_statedProj J (p ^ 1) hcard hfix
  have hK : Nat.card (GaloisField p (2 * 1)) = p ^ 2 := by rw [hcard, pow_one]
  have hfix' : Nat.card {x : GaloisField p (2 * 1) // J.conj x = x} = p := by rw [hfix, pow_one]
  set φ : ↥L ≃* ProjectiveSpecialUnitaryMatrixGroup J :=
    e.trans ((CFSG.PGLModel.projSUEquivStatedProj 3 p 1).trans e₁.symm) with hφ
  set F : ProjectiveSpecialUnitaryMatrixGroup J →* G := L.subtype.comp φ.symm.toMonoidHom with hF
  have hFinj : Function.Injective F := L.subtype_injective.comp φ.symm.injective
  have hFφ : ∀ l : L, F (φ l) = l := fun l => by simp [hF]
  set Ω : Subgroup G := ⁅L ⊓ Subgroup.centralizer ({b} : Set G),
    L ⊓ Subgroup.centralizer ({b} : Set G)⁆ with hΩ
  set S : Subgroup G := Subgroup.normalizer (Subgroup.zpowers y : Set G) ⊔ Ω with hS
  have hΩL : Ω ≤ L :=
    (Subgroup.commutator_mono inf_le_left inf_le_left).trans (Subgroup.commutator_le_left L L)
  have hΩ'map : (Ω.comap F).map F = Ω :=
    Subgroup.map_comap_eq_self fun x hx => ⟨φ ⟨x, hΩL hx⟩, hFφ _⟩
  have eΩ' : ↥(Ω.comap F) ≃* PSL(2, ZMod p) :=
    (((Ω.comap F).equivMapOfInjective F hFinj).trans (MulEquiv.subgroupCongr hΩ'map)).trans eΩ
  have hFy' : F (φ ⟨y, hyL⟩) = y := hFφ _
  have hy'3 : orderOf (φ ⟨y, hyL⟩) = 3 := by
    rw [← orderOf_injective F hFinj, hFy', hy3]
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hpg : IsPGroup 3 (Subgroup.zpowers (φ ⟨y, hyL⟩)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hy'3, pow_one])
  have hmod := hpg.card_modEq_card_fixedPoints (IsoPoint J)
  rw [card_isoPoint J hJ p hK hfix'] at hmod
  have hp31 : (p ^ 3 + 1) % 3 = 2 := by
    rw [Nat.add_mod, Nat.pow_mod, hp]
  have hfix2 : 1 < (MulAction.fixedPoints (Subgroup.zpowers (φ ⟨y, hyL⟩)) (IsoPoint J)).ncard := by
    rw [← Nat.card_coe_set_eq]
    have h1 : Nat.card (MulAction.fixedPoints (Subgroup.zpowers (φ ⟨y, hyL⟩)) (IsoPoint J)) % 3 =
        2 := by
      have h := hmod.symm
      unfold Nat.ModEq at h
      exact h.trans hp31
    omega
  obtain ⟨Q₁, Q₂, hQ₁, hQ₂, hQ⟩ := (Set.one_lt_ncard_iff (Set.toFinite _)).mp hfix2
  obtain ⟨c, hc₁, hc₂⟩ := (MulAction.is_two_pretransitive_iff.mp
    (isMultiplyPretransitive_two J hJ p hK hfix')) (pinf_ne_pzero J hJ) hQ
  have hy'Q : ∀ Q ∈ MulAction.fixedPoints (Subgroup.zpowers (φ ⟨y, hyL⟩)) (IsoPoint J),
      φ ⟨y, hyL⟩ • Q = Q := fun Q hQ =>
    MulAction.mem_fixedPoints.mp hQ ⟨φ ⟨y, hyL⟩, Subgroup.mem_zpowers _⟩
  have htD : c⁻¹ * φ ⟨y, hyL⟩ * c ∈ torusGroup J hJ := by
    rw [← stabilizer_pinf_inf_stabilizer_pzero J hJ p hK hfix']
    refine ⟨MulAction.mem_stabilizer_iff.mpr ?_, MulAction.mem_stabilizer_iff.mpr ?_⟩
    · rw [mul_smul, mul_smul, hc₁, hy'Q Q₁ hQ₁, ← hc₁, inv_smul_smul]
    · rw [mul_smul, mul_smul, hc₂, hy'Q Q₂ hQ₂, ← hc₂, inv_smul_smul]
  have hDcomm : ∀ a ∈ torusGroup J hJ, ∀ d ∈ torusGroup J hJ, a * d = d * a := by
    have := isCyclic_torusGroup J hJ p hK hfix'
    intro a ha d hd
    exact congrArg Subtype.val
      ((IsCyclic.isMulCommutative (α := torusGroup J hJ)).is_comm.comm ⟨a, ha⟩ ⟨d, hd⟩)
  have hDT : torusGroup J hJ ≤ (S.comap F).map (MulAut.conj c⁻¹).toMonoidHom := by
    intro d hd
    refine ⟨c * d * c⁻¹, ?_, by simp [MulAut.conj_apply, mul_assoc]⟩
    have hcomm : Commute (φ ⟨y, hyL⟩) (c * d * c⁻¹) := by
      have h := hDcomm _ htD d hd
      calc φ ⟨y, hyL⟩ * (c * d * c⁻¹) = c * ((c⁻¹ * φ ⟨y, hyL⟩ * c) * d) * c⁻¹ := by group
        _ = c * (d * (c⁻¹ * φ ⟨y, hyL⟩ * c)) * c⁻¹ := by rw [h]
        _ = (c * d * c⁻¹) * φ ⟨y, hyL⟩ := by group
    have hN : c * d * c⁻¹ ∈ Subgroup.normalizer
        (Subgroup.zpowers (φ ⟨y, hyL⟩) : Set (ProjectiveSpecialUnitaryMatrixGroup J)) := by
      apply Subgroup.centralizer_le_normalizer
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
      exact (hcomm.zpow_left k).eq
    have h2 := Subgroup.le_normalizer_map F ⟨_, hN, rfl⟩
    rw [MonoidHom.map_zpowers, hFy'] at h2
    rw [SetLike.mem_coe, Subgroup.mem_comap, hS]
    exact Subgroup.mem_sup_left h2
  have hΩT : (Ω.comap F).map (MulAut.conj c⁻¹).toMonoidHom ≤
      (S.comap F).map (MulAut.conj c⁻¹).toMonoidHom :=
    Subgroup.map_mono (Subgroup.comap_mono (by rw [hS]; exact le_sup_right))
  have eΩ'' : ↥((Ω.comap F).map (MulAut.conj c⁻¹).toMonoidHom) ≃* PSL(2, ZMod p) :=
    ((Ω.comap F).equivMapOfInjective _ (MulAut.conj c⁻¹).injective).symm.trans eΩ'
  have htop := F3U3.torusGroup_sup_eq_top_of_mulEquiv_psl2 J hJ hK hfix' hp7 hp eΩ''
  have hT : (S.comap F).map (MulAut.conj c⁻¹).toMonoidHom = ⊤ := by
    rw [eq_top_iff, ← htop]
    exact sup_le hDT hΩT
  intro l hl
  obtain ⟨s, hs, hs'⟩ : (MulAut.conj c⁻¹).toMonoidHom (φ ⟨l, hl⟩) ∈
      (S.comap F).map (MulAut.conj c⁻¹).toMonoidHom := hT ▸ Subgroup.mem_top _
  have hsl : s = φ ⟨l, hl⟩ := (MulAut.conj c⁻¹).injective hs'
  rw [hsl, SetLike.mem_coe, Subgroup.mem_comap, hFφ] at hs
  exact hs

end CFSG.RankThree.PartTwo.Sec20
