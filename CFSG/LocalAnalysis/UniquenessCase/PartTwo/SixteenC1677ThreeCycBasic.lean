module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs16a
public import CFSG.Quasithin.Background.Asc81cTenFourA
public import CFSG.Walter.Bender1970.S3.Involution
public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupExhaustion
public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupRanks
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicCongruenceCut
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicFourLarge
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicTwoFourGenerators
public import CFSG.LocalAnalysis.LargeEvenClassification.MacWilliamsReduction
public import CFSG.LocalAnalysis.LargeEvenClassification.SmallCfourFullObstruction
public import CFSG.LocalAnalysis.LargeEvenClassification.SmallCfourProperSubgroups
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.SubnormalPSubgroupLeQCore
public import CFSG.Walter.Bender1970.S2
public import CFSG.Walter.Bender1970.S3.Basic
public import CFSG.Walter.Bender1970.S3.Tools
public import CFSG.Walter.PSL2Facts
public import Certificates.Certificate1
public import Certificates.Certificate10
public import Certificates.Certificate100
public import Certificates.Certificate101
public import Certificates.Certificate102
public import Certificates.Certificate103
public import Certificates.Certificate104
public import Certificates.Certificate105
public import Certificates.Certificate106
public import Certificates.Certificate107
public import Certificates.Certificate108
public import Certificates.Certificate109
public import Certificates.Certificate11
public import Certificates.Certificate12
public import Certificates.Certificate2
public import Certificates.Certificate3
public import Certificates.Certificate4
public import Certificates.Certificate42
public import Certificates.Certificate44
public import Certificates.Certificate5
public import Certificates.Certificate6
public import Certificates.Certificate7
public import Certificates.Certificate8
public import Certificates.Certificate9
public import Certificates.Certificate96
public import Certificates.Certificate97
public import Certificates.Certificate98
public import Certificates.Certificate99

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup
open scoped commutatorElement Pointwise

variable {W : Type} [CommGroup W]

private theorem s168e3_cyc_natCard_multiplicative (α : Type*) :
    Nat.card (Multiplicative α) = Nat.card α :=
  Nat.card_congr Multiplicative.ofAdd.symm

private theorem s168e3_cyc_card_of_isElemAbelianOfRank {p n : ℕ} {X : Type*} [Group X]
    (h : IsElemAbelianOfRank p n X) : Nat.card X = p ^ n := by
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv, s168e3_cyc_natCard_multiplicative, Nat.card_fun, Nat.card_fin,
    Nat.card_zmod]

theorem s168e3_cyc_gen {L : Subgroup (MulAut W)} {p : ℕ} (hp : p.Prime)
    (hL : IsElemAbelianOfRank p 1 ↥L) :
    ∃ x : MulAut W, L = Subgroup.zpowers x ∧ orderOf x = p := by
  have hcardL : Nat.card ↥L = p := by
    simpa using s168e3_cyc_card_of_isElemAbelianOfRank hL
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : IsCyclic ↥L := isCyclic_of_prime_card hcardL
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥L)
  have horder : orderOf g = p := (orderOf_eq_card_of_forall_mem_zpowers hg).trans hcardL
  refine ⟨(g : MulAut W), ?_, ?_⟩
  · have htop : Subgroup.zpowers g = ⊤ := (Subgroup.zpowers g).eq_top_iff'.mpr hg
    have hmap : (Subgroup.zpowers g).map L.subtype = Subgroup.zpowers (g : MulAut W) :=
      MonoidHom.map_zpowers L.subtype g
    rw [htop] at hmap
    rw [← hmap]
    exact le_antisymm (fun x hx => ⟨⟨x, hx⟩, Subgroup.mem_top _, rfl⟩)
      (Subgroup.map_subtype_le (⊤ : Subgroup ↥L))
  · rw [Subgroup.orderOf_coe, horder]

theorem s168e3_cyc_inv {A L : Subgroup (MulAut W)} {t x : MulAut W} {p : ℕ} (hp : p.Prime)
    (hLx : L = Subgroup.zpowers x) (hx : orderOf x = p) (ht : t ∈ A) (ht2 : t ^ 2 = 1)
    (hLn : ∀ g ∈ A, L.map (MulAut.conj g).toMonoidHom = L)
    (hne : ⁅L, Subgroup.zpowers t⁆ ≠ ⊥) : t * x * t⁻¹ = x⁻¹ := by
  have hcardL : Nat.card ↥L = p := by rw [hLx, Nat.card_zpowers, hx]
  have ht2' : t * t = 1 := by simpa [pow_two] using ht2
  have htn : t ∈ Subgroup.normalizer (L : Set (MulAut W)) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.2 (hLn t ht)
  rcases CFSG.Walter.conj_eq_or_conj_eq_inv_of_card_eq_prime hp hcardL ht2' htn with
    hcom | hinv
  · exfalso
    apply hne
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro l hl
    rw [Subgroup.mem_centralizer_iff]
    intro n hn
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
    have htl : Commute t l := by
      show t * l = l * t
      calc t * l = (t * l * t⁻¹) * t := by group
        _ = l * t := by rw [hcom l hl]
    exact (htl.zpow_left k).eq
  · exact hinv x (by rw [hLx]; exact Subgroup.mem_zpowers x)

theorem s168e3_cyc_fpf [Finite W] (hW : ∀ w : W, w ^ 2 = 1) {L : Subgroup (MulAut W)}
    {x : MulAut W} (hLx : L = Subgroup.zpowers x) (hodd : Odd (orderOf x))
    (hWL : commSub ⊤ L = ⊤) : ∀ w : W, x w = w → w = 1 := by
  intro w hw
  have hcardL : Nat.card ↥L = orderOf x := by rw [hLx, Nat.card_zpowers]
  have hoddL : Odd (Nat.card ↥L) := by rw [hcardL]; exact hodd
  have hfix : w ∈ fixV L := by
    rw [hLx, mem_fixV]
    intro y hy
    have hxstab : x ∈ MulAction.stabilizer (MulAut W) w := by
      rw [MulAction.mem_stabilizer_iff, MulAut.smul_def]
      exact hw
    exact (Subgroup.zpowers_le.mpr hxstab) hy
  have hmem : w ∈ fixV L ⊓ commSub ⊤ L := by
    refine ⟨hfix, ?_⟩
    rw [hWL]
    exact Subgroup.mem_top w
  rw [CFSG.Quasithin.Asc81c.fixV_inf_commSub_eq_bot' hW hoddL, Subgroup.mem_bot] at hmem
  exact hmem

theorem s168e3_cyc_card_dvd [Finite W] {A L : Subgroup (MulAut W)} {p : ℕ} (hp : p.Prime)
    (hLcard : Nat.card ↥L = p) (hLn : ∀ g ∈ A, L.map (MulAut.conj g).toMonoidHom = L) :
    Nat.card ↥A ∣ (p - 1) * Nat.card ↥(A ⊓ Subgroup.centralizer (L : Set (MulAut W))) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite ↥L := Nat.finite_of_card_ne_zero (hLcard ▸ hp.ne_zero)
  haveI : IsCyclic ↥L := isCyclic_of_prime_card hLcard
  have hAN : A ≤ Subgroup.normalizer (L : Set (MulAut W)) := fun g hg =>
    Subgroup.mem_normalizer_iff_map_conj_eq.2 (hLn g hg)
  let φ : ↥A →* MulAut ↥L :=
    (Subgroup.normalizerMonoidHom L).comp (Subgroup.inclusion hAN)
  have hker : Nat.card ↥φ.ker =
      Nat.card ↥(A ⊓ Subgroup.centralizer (L : Set (MulAut W))) := by
    have hker_eq : φ.ker = (A ⊓ Subgroup.centralizer (L : Set (MulAut W))).subgroupOf A := by
      ext a
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf, and_iff_right a.2]
      constructor
      · intro ha
        have hmem : Subgroup.inclusion hAN a ∈ (Subgroup.normalizerMonoidHom L).ker := ha
        rwa [Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf] at hmem
      · intro ha
        show (Subgroup.normalizerMonoidHom L) (Subgroup.inclusion hAN a) = 1
        rw [← MonoidHom.mem_ker, Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf]
        exact ha
    rw [hker_eq]
    exact Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe
        (inf_le_left : A ⊓ Subgroup.centralizer (L : Set (MulAut W)) ≤ A)).toEquiv
  have h1 : Nat.card ↥A = Nat.card ↥φ.ker * Nat.card ↥φ.range := by
    rw [← Subgroup.index_ker, Subgroup.card_mul_index]
  have hrange : Nat.card ↥φ.range ∣ p - 1 := by
    have h := Subgroup.card_subgroup_dvd_card φ.range
    rwa [IsCyclic.card_mulAut, hLcard, Nat.totient_prime hp] at h
  rw [h1, hker]
  simpa [mul_comm] using
    mul_dvd_mul_left (Nat.card ↥(A ⊓ Subgroup.centralizer (L : Set (MulAut W)))) hrange

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
