module

public import CFSG.LocalAnalysis.StandardType.GGF4LabelPieces
public import Certificates.Certificate2012
public import Certificates.Certificate8064
public import Certificates.Certificate26122
import CFSG.Adapters.LieModelSimple
import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.OutU42Aut
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenThreeThreeTransvU42
import CFSG.LocalAnalysis.StandardType.GGRemTableBLLine63H5LayerGroup
import CFSG.LocalAnalysis.StandardType.GGResE6DepOrders
import CFSG.LocalAnalysis.StandardType.GGTBJConfigFacts
import CFSG.LocalAnalysis.StandardType.GGTableBTransport
import TauCeti.RepresentationTheory.CharacterTable.Solvable

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.EvenSporadicStandard.M22Std
  CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.TransvW.U42

private theorem ggF4H2_conj_injective {E : Type} [Group E]
    (h : CFSG.Blueprint.LieModel E .PSU 4 2 1) :
    Function.Injective (MulAut.conj : E →* MulAut E) := by
  obtain ⟨-, hcard⟩ := card_mulAut_of_lieModel_psu42 h
  haveI : Finite E := Nat.finite_of_card_ne_zero (by omega)
  haveI : IsSimpleGroup E :=
    CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) h
  obtain ⟨a, b, hab⟩ := not_commutative_of_lieModel_psu42 h
  have hZ : Subgroup.center E = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center E) with h0 | h1
    · exact h0
    · exact absurd (Subgroup.mem_center_iff.1 (h1 ▸ Subgroup.mem_top b) a) hab
  rw [injective_iff_map_eq_one]
  intro z hz
  have hzc : z ∈ Subgroup.center E := by
    rw [Subgroup.mem_center_iff]
    intro x
    have h1 := congrArg (fun σ : MulAut E => σ x) hz
    simp only [MulAut.conj_apply, MulAut.one_apply] at h1
    calc x * z = (z * x * z⁻¹) * z := by rw [h1]
      _ = z * x := by group
  rwa [hZ, Subgroup.mem_bot] at hzc

theorem ggF4H2_isSolvable_centralizer_u42
    {E : Type} [Group E]
    (h : CFSG.Blueprint.LieModel E .PSU 4 2 1) {g : E} (hg : orderOf g = 3) :
    Group.IsSolvable ↥(Subgroup.centralizer ({g} : Set E)) := by
  obtain ⟨-, hcard⟩ := card_mulAut_of_lieModel_psu42 h
  haveI : Finite E := Nat.finite_of_card_ne_zero (by omega)
  have h5 : ¬ 5 ∣ Nat.card (Subgroup.centralizer ({g} : Set E)) := by
    intro h5
    haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' 5 h5
    have hu' : orderOf (u : E) = 5 := by rw [Subgroup.orderOf_coe]; exact hu
    have hcomm : Commute g (u : E) := by
      have h1 := Subgroup.mem_centralizer_singleton_iff.1 u.2
      exact h1.symm
    have hord : orderOf (g * (u : E)) = 15 :=
      calc orderOf (g * (u : E)) = orderOf g * orderOf (u : E) :=
            hcomm.orderOf_mul_eq_mul_orderOf_of_coprime (by rw [hg, hu']; norm_num)
        _ = 3 * 5 := by rw [hg, hu']
        _ = 15 := by norm_num
    exact not_orderOf_fifteen_u42 h _ hord
  have hdvd : Nat.card (Subgroup.centralizer ({g} : Set E)) ∣ 2 ^ 6 * 3 ^ 4 := by
    have h1 : Nat.card (Subgroup.centralizer ({g} : Set E)) ∣ Nat.card E :=
      Subgroup.card_subgroup_dvd_card _
    rw [hcard] at h1
    have h2 : Nat.card (Subgroup.centralizer ({g} : Set E)) ∣ 2 ^ 6 * 3 ^ 4 * 5 := by
      have h25920 : (25920 : ℕ) = 2 ^ 6 * 3 ^ 4 * 5 := by norm_num
      rw [← h25920]
      exact h1
    exact (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).2 h5)).dvd_of_dvd_mul_right
      h2
  exact TauCeti.isSolvable_of_card_dvd_prime_pow_mul_prime_pow Nat.prime_two Nat.prime_three hdvd

private theorem ggF4H2_isSolvable_of_central_quot {G : Type} [Group G] {L K : Subgroup G}
    (hKL : K ≤ L) {g : ↥L ⧸ Subgroup.center ↥L}
    (hC : Group.IsSolvable ↥(Subgroup.centralizer ({g} : Set (↥L ⧸ Subgroup.center ↥L))))
    (hK : ∀ k : ↥K, (QuotientGroup.mk (Subgroup.inclusion hKL k) : ↥L ⧸ Subgroup.center ↥L) ∈
      Subgroup.centralizer ({g} : Set (↥L ⧸ Subgroup.center ↥L))) :
    Group.IsSolvable ↥K := by
  let ψ : ↥K →* ↥(Subgroup.centralizer ({g} : Set (↥L ⧸ Subgroup.center ↥L))) :=
    ((QuotientGroup.mk' (Subgroup.center ↥L)).comp (Subgroup.inclusion hKL)).codRestrict _ hK
  have hker : ∀ a b : ↥ψ.ker, a * b = b * a := by
    intro a b
    have hcen : ∀ c : ↥ψ.ker, Subgroup.inclusion hKL (c : ↥K) ∈ Subgroup.center ↥L := by
      intro c
      have h1 : (QuotientGroup.mk (Subgroup.inclusion hKL (c : ↥K)) : ↥L ⧸ Subgroup.center ↥L) =
          1 := congrArg Subtype.val (MonoidHom.mem_ker.1 c.2)
      exact (QuotientGroup.eq_one_iff _).1 h1
    have h2 := Subgroup.mem_center_iff.1 (hcen a) (Subgroup.inclusion hKL (b : ↥K))
    apply Subtype.ext
    apply Subtype.ext
    exact (congrArg (fun l : ↥L => (l : G)) h2).symm
  haveI : Group.IsSolvable ↥ψ.ker := Group.isSolvable_of_comm hker
  exact Group.isSolvable_of_ker_le_range ψ.ker.subtype ψ (by simp)

theorem ggF4LabelH2_holds :
    GGF4LabelH2 := by
  intro G _ _ B Bs x L D J hcfg hlab
  classical
  obtain ⟨-, -, -, hperf⟩ := hcfg.data_L
  have hS : LargeEvenSStar 3 B x L := hcfg.1.2.2.2.2.2.2.1
  have hStd : LargeEvenStandardType 3 B x L := hcfg.1.2.2.2.2.2.2.2
  obtain ⟨hDB, hDe, hDc, -, -, hJc, -⟩ : LargeEvenStdSubPre 3 B x L D J := hcfg.2.2.1
  have hD3 : ∀ g ∈ D, g ^ 3 = 1 := hDe.2
  have hDnot : ¬ D ≤ Subgroup.centralizer (L : Set G) := by
    intro hle
    have hp : IsPGroup 3 D := fun g => ⟨1, Subtype.ext (by simpa using hD3 g g.2)⟩
    have hcyc : IsCyclic D := hS.2.2.2.2 D hle hp
    obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := D)
    have hg3 : g ^ 3 = 1 := Subtype.ext (by simpa using hD3 g g.2)
    have h1 : orderOf g ∣ 3 := orderOf_dvd_of_pow_eq_one hg3
    rw [hg, hDc] at h1
    exact absurd h1 (by norm_num)
  obtain ⟨d, hdD, hdL⟩ : ∃ d ∈ D, d ∉ Subgroup.centralizer (L : Set G) := by
    by_contra hcon
    exact hDnot (fun d hd => by_contra fun hnot => hcon ⟨d, hd, hnot⟩)
  have hBN : B ≤ Subgroup.normalizer (L : Set G) := by
    obtain ⟨-, lab, -, hraw⟩ := hStd.1
    obtain ⟨R, _, I, F, -, -, θ, -, hN, -⟩ := largeEvenRawDatum_exists hraw
    exact hN
  have hnt : Nontrivial (↥L ⧸ Subgroup.center ↥L) := by
    obtain ⟨-, lab, -, hraw⟩ := hStd.1
    obtain ⟨R, _, I, F, hRs, -, θ, -⟩ := largeEvenRawDatum_exists hraw
    haveI := hRs.toNontrivial
    exact θ.toEquiv.nontrivial
  have hdN : d ∈ Subgroup.normalizer (L : Set G) := hBN (hDB hdD)
  have hΛ : LargeEvenInLambda2 (⟨.twA, 3, 1⟩ : LargeEvenLabel) := by
    refine ⟨le_rfl, ?_⟩
    show 2 ≤ 3 ∧ (3 = 2 → 2 ≤ 1)
    exact ⟨by norm_num, fun h => absurd h (by norm_num)⟩
  have hm : MarkedModel (⟨.twA, 3, 1⟩ : LargeEvenLabel) (↥L ⧸ Subgroup.center ↥L) :=
    l05nL4h_markedModel hperf hnt hΛ hlab
  have hLie : CFSG.Blueprint.LieModel (↥L ⧸ Subgroup.center ↥L) .PSU 4 2 1 := by
    first
      | exact hm
      | simpa [MarkedModel, markTag, markRank, markChar, markDeg] using hm
  have hα3 : (ggLAut L (MulEquiv.refl (↥L ⧸ Subgroup.center ↥L)) ⟨d, hdN⟩) ^ 3 = 1 := by
    rw [← map_pow]
    have h1 : (⟨d, hdN⟩ : Subgroup.normalizer (L : Set G)) ^ 3 = 1 :=
      Subtype.ext (by simpa using hD3 d hdD)
    rw [h1, map_one]
  have hodd : Odd (orderOf (ggLAut L (MulEquiv.refl (↥L ⧸ Subgroup.center ↥L)) ⟨d, hdN⟩)) := by
    rcases (Nat.dvd_prime Nat.prime_three).1 (orderOf_dvd_of_pow_eq_one hα3) with h | h
    · rw [h]; exact odd_one
    · rw [h]; exact ⟨1, rfl⟩
  obtain ⟨g, hgα, -⟩ := exists_conj_of_odd_u42 hLie hodd
  have hinj := ggF4H2_conj_injective hLie
  have hg1 : g ≠ 1 := by
    rintro rfl
    have hα1 : ggLAut L (MulEquiv.refl (↥L ⧸ Subgroup.center ↥L)) ⟨d, hdN⟩ = 1 := by
      rw [← hgα]; exact map_one _
    exact hdL (mem_centralizer_of_ggLAut_eq_one L (MulEquiv.refl _) hperf hα1)
  have hg3 : g ^ 3 = 1 := hinj (by rw [map_pow, hgα, hα3, map_one])
  have hgord : orderOf g = 3 := by
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact orderOf_eq_prime hg3 hg1
  have hCs := ggF4H2_isSolvable_centralizer_u42 hLie hgord
  have hKL : L ⊓ Subgroup.centralizer (D : Set G) ≤ L := inf_le_left
  have hKsolv : Group.IsSolvable ↥(L ⊓ Subgroup.centralizer (D : Set G)) := by
    refine ggF4H2_isSolvable_of_central_quot hKL hCs fun k => ?_
    have hkD : (k : G) ∈ Subgroup.centralizer (D : Set G) := k.2.2
    have hdk : d * (k : G) = (k : G) * d := Subgroup.mem_centralizer_iff.1 hkD d hdD
    have h2 : L.normalizerMonoidHom ⟨d, hdN⟩ (Subgroup.inclusion hKL k) =
        Subgroup.inclusion hKL k := by
      apply Subtype.ext
      rw [normalizerMonoidHom_coe]
      show d * (k : G) * d⁻¹ = (k : G)
      rw [hdk, mul_assoc, mul_inv_cancel, mul_one]
    have h3 := ggLAut_apply L (MulEquiv.refl (↥L ⧸ Subgroup.center ↥L)) ⟨d, hdN⟩
      (Subgroup.inclusion hKL k)
    rw [h2] at h3
    have h4 : (MulAut.conj g) (QuotientGroup.mk (Subgroup.inclusion hKL k) :
        ↥L ⧸ Subgroup.center ↥L) = QuotientGroup.mk (Subgroup.inclusion hKL k) := by
      rw [hgα]; exact h3
    rw [MulAut.conj_apply] at h4
    refine Subgroup.mem_centralizer_singleton_iff.2 ?_
    calc (QuotientGroup.mk (Subgroup.inclusion hKL k) : ↥L ⧸ Subgroup.center ↥L) * g
        = (g * QuotientGroup.mk (Subgroup.inclusion hKL k) * g⁻¹) * g := by rw [h4]
      _ = g * QuotientGroup.mk (Subgroup.inclusion hKL k) := by group
  exact Line63.H5.false_of_isComponentOf_of_isSolvable hKsolv hJc

end CFSG.StandardType

end
