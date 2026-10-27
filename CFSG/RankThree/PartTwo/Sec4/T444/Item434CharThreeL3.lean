module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434CharThree
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434CharThreeL3Tools
import CFSG.LieType.Steinberg.CentralExt.SLCentrallyClosed
import CFSG.RankThree.PartTwo.Sec4.T444.Item434AltPerm
import CFSG.RankThree.PartTwo.Sec5.Tools
import CFSG.RankThree.PartTwo.Source.GammaTwoSubgroups
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.ClassicalGroups.Symplectic.Simple
public import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple
public import CFSG.Permutation.AlternatingAutomorphism
public import CFSG.RankThree.PartTwo.KFacts.AutKindsUnique
public import CFSG.RankThree.PartTwo.Sec12.Notation
public import CFSG.RankThree.PartTwo.Sec4.Item47Diag
public import CFSG.RankThree.PartTwo.Sec4.Item47Statement
public import CFSG.RankThree.PartTwo.Sec4.Item47Witness
public import CFSG.RankThree.PartTwo.Sec4.LThreePiItem411
public import CFSG.RankThree.PartTwo.Sec4.ProjSLEquiv
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434Kit
public import CFSG.RankThree.PartTwo.Sec8.Statements

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.LocalCores Matrix
open CFSG.Assembly.RankThreeEven (projSL)
open scoped MatrixGroups

namespace Item434CharThree

theorem center_eq_bot_of_split {L X : Type} [Group L] [Group X] (hL : IsQuasisimple L)
    (θ : L ⧸ Subgroup.center L ≃* X)
    (hsplit : ∀ {E : Type} [Group E] {π : E →* X}, Function.Surjective π →
      π.ker ≤ Subgroup.center E → ∃ σ : X →* E, ∀ x, π (σ x) = x) :
    Subgroup.center L = ⊥ := by
  have : Group.IsPerfect L := hL.1
  set π : L →* X := θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center L)) with hπdef
  have hπ : Function.Surjective π := θ.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : π.ker = Subgroup.center L := by
    ext x
    rw [MonoidHom.mem_ker, hπdef, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  obtain ⟨σ, hσ⟩ := hsplit hπ hker.le
  have htop : σ.range = ⊤ := Item434Alt.eq_top_of_range_le_map π hker.le (by
    rintro _ ⟨x, rfl⟩
    exact ⟨σ (π x), ⟨_, rfl⟩, hσ _⟩)
  rw [eq_bot_iff, ← hker]
  intro z hz
  obtain ⟨x, rfl⟩ : z ∈ σ.range := htop ▸ Subgroup.mem_top z
  rw [MonoidHom.mem_ker, hσ] at hz
  rw [hz, map_one]
  exact Subgroup.one_mem _

variable {G : Type} [Group G] [Finite G] {A M Q : Subgroup G}

theorem false_of_projSL_three_large (h : Ctx434Core G A M Q) {e : ℕ} (he2 : 2 ≤ e) (he3 : e ≤ 3)
    (e₀ : layer G ⧸ Subgroup.center (layer G) ≃* projSL 3 (GaloisField 3 e)) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set K := GaloisField 3 e with hK
  have hKc : Nat.card K = 3 ^ e := GaloisField.card 3 e (by omega)
  set θ : layer G ⧸ Subgroup.center (layer G) ≃* SL(3, K) :=
    e₀.trans (slEquivProjSL K).symm with hθ
  have h5 : 5 ≤ Nat.card K := by
    rw [hKc]
    calc 5 ≤ 3 ^ 2 := by norm_num
      _ ≤ 3 ^ e := Nat.pow_le_pow_right (by norm_num) he2
  have hZ : Subgroup.center (layer G) = ⊥ :=
    center_eq_bot_of_split h.isQuasisimple θ fun hπ hcen =>
      CFSG.LieType.Steinberg.CentralExt.SLClosed.sl_exists_section_of_central (m := 2) le_rfl h5
        hπ hcen
  have hR := card_lineSub (K := K) (a₀ := 1) (b₀ := 0) (Or.inl one_ne_zero)
  obtain ⟨D₀, hD₀⟩ := Sylow.exists_subgroup_card_pow_prime 3 (G := lineSub (1 : K) 0) (n := 3)
    (by rw [hR, hKc, ← pow_mul]; exact pow_dvd_pow 3 (by omega))
  have hD : CFSG.Assembly.IsElemAbelian 3 (D₀.map (lineSub (1 : K) 0).subtype) :=
    Source.isElemAbelian_of_le (isElemAbelian_lineSub 1 0) (Subgroup.map_subtype_le D₀)
  have hD27 : Nat.card (D₀.map (lineSub (1 : K) 0).subtype) = 27 := by
    rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _), hD₀]
    norm_num
  have hCA := Item434Kit.inf_centralizer_layer_eq_bot h hZ θ hD hD27
  have hA27 := Item434Kit.card_map_quotConj h hCA θ
  have hAe := Item434Kit.isElemAbelian_map_quotConj h θ
  set Astar := A.map (Item434Alt.quotConj θ) with hAstar
  set I := CFSG.ComponentClassification.OuterAutomorphisms.inner SL(3, K) with hI
  have h9 : 9 ≤ Nat.card (Astar ⊓ I : Subgroup (MulAut SL(3, K))) := by
    have hsplit := Item434Alt.card_eq_card_inf_ker_mul_card_map (QuotientGroup.mk' I) Astar
    rw [QuotientGroup.ker_mk', hA27] at hsplit
    have hd1 : Nat.card (Astar.map (QuotientGroup.mk' I)) ∣ 27 :=
      hA27 ▸ Subgroup.card_map_dvd _ _
    have hd2 : Nat.card (Astar.map (QuotientGroup.mk' I)) ∣ 2 * e :=
      (Subgroup.card_subgroup_dvd_card _).trans (card_outer_SL_three_dvd (by omega))
    have hle : Nat.card (Astar.map (QuotientGroup.mk' I)) ≤ 3 := by
      have h6 := Nat.le_of_dvd (by omega) hd2
      obtain ⟨m, hm⟩ : ∃ m, Nat.card (Astar.map (QuotientGroup.mk' I)) = m := ⟨_, rfl⟩
      rw [hm] at hd1 h6 ⊢
      have h6' : m ≤ 6 := by omega
      interval_cases m <;> omega
    by_contra hlt
    push Not at hlt
    have : Nat.card (Astar ⊓ I : Subgroup (MulAut SL(3, K))) *
        Nat.card (Astar.map (QuotientGroup.mk' I)) ≤ 8 * 3 := Nat.mul_le_mul (by omega) hle
    omega
  have hinj := Item434Kit.conj_injective_of_center_eq_bot (center_SL_three_eq_bot K)
  set P : Subgroup SL(3, K) := (Astar ⊓ I).comap (MulAut.conj : SL(3, K) →* MulAut SL(3, K))
    with hP
  have hPmap : P.map (MulAut.conj : SL(3, K) →* MulAut SL(3, K)) = Astar ⊓ I :=
    Subgroup.map_comap_eq_self inf_le_right
  have hPe : CFSG.Assembly.IsElemAbelian 3 P :=
    Item434Kit.isElemAbelian_of_map_injective hinj
      (by rw [hPmap]; exact Source.isElemAbelian_of_le hAe inf_le_left)
  have hPp : IsPGroup 3 P := Sec5.isPGroup_of_isElemAbelian hPe
  have : Finite SL(3, K) := Finite.of_injective _ Subtype.val_injective
  obtain ⟨g, hg⟩ := Item434AltPerm.exists_le_map_conj_of_card (P₀ := heis K)
    (by rw [card_heis, hKc, factorization_card_SL_three (by omega), ← pow_mul, mul_comm])
    hPp
  have hPg : P.map (MulAut.conj g⁻¹).toMonoidHom ≤ heis K := Item434AltPerm.map_conj_inv_le hg
  have hPgc : ∀ x ∈ P.map (MulAut.conj g⁻¹).toMonoidHom,
      ∀ y ∈ P.map (MulAut.conj g⁻¹).toMonoidHom, x * y = y * x := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul]
    exact congrArg _ (congrArg Subtype.val (hPe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩))
  obtain ⟨a₀, b₀, hab, hle⟩ := exists_le_lineSub hPg hPgc
  set D := (lineSub a₀ b₀).map (MulAut.conj g).toMonoidHom with hDdef
  have hDe : CFSG.Assembly.IsElemAbelian 3 D :=
    CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_map 3 _ _ (isElemAbelian_lineSub a₀ b₀)
  have hDcard : Nat.card D = 3 ^ (2 * e) := by
    rw [hDdef, Subgroup.card_map_of_injective (MulAut.conj g).injective, card_lineSub hab, hKc,
      ← pow_mul, mul_comm]
  have h81 : 81 ≤ Nat.card D := by
    rw [hDcard]
    calc 81 = 3 ^ 4 := by norm_num
      _ ≤ 3 ^ (2 * e) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hB9 := h9.trans (Item434Kit.card_le_card_inf_comap θ (inf_le_left : Astar ⊓ I ≤ Astar))
  refine Item434Kit.false_of_fixed h hZ θ inf_le_left hB9 hDe h81 ?_
  rintro b ⟨-, hb⟩ d hd
  obtain ⟨p, hp⟩ := hb.2
  have hpP : p ∈ P := by
    change MulAut.conj p ∈ Astar ⊓ I
    rw [hp]
    exact hb
  rw [← hp, MulAut.conj_apply]
  obtain ⟨d', hd', rfl⟩ := hd
  have hp' : g⁻¹ * p * g⁻¹⁻¹ ∈ lineSub a₀ b₀ := hle ⟨p, hpP, rfl⟩
  have hcomm := lineSub_commute hp' hd'
  change p * (g * d' * g⁻¹) * p⁻¹ = g * d' * g⁻¹
  have hpe : p = g * (g⁻¹ * p * g⁻¹⁻¹) * g⁻¹ := by group
  rw [hpe]
  calc g * (g⁻¹ * p * g⁻¹⁻¹) * g⁻¹ * (g * d' * g⁻¹) * (g * (g⁻¹ * p * g⁻¹⁻¹) * g⁻¹)⁻¹ =
      g * ((g⁻¹ * p * g⁻¹⁻¹) * d') * (g⁻¹ * p * g⁻¹⁻¹)⁻¹ * g⁻¹ := by group
    _ = g * (d' * (g⁻¹ * p * g⁻¹⁻¹)) * (g⁻¹ * p * g⁻¹⁻¹)⁻¹ * g⁻¹ := by rw [hcomm]
    _ = g * d' * g⁻¹ := by group

end Item434CharThree

open Item434CharThree

section Families


theorem item434CharThreeL3Large : Item434CharThreeL3Large := by
  intro G₀ _ _ hG₀ H G _ _ f hf hker A M Q hc hL
  obtain ⟨e, he2, he3, ⟨e₀⟩⟩ := hL
  exact (false_of_projSL_three_large hc he2 he3 e₀).elim

end Families

end CFSG.RankThree.PartTwo.Sec4
