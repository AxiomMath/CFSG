module

public import CFSG.RankThree.PartOne.S11d.ThetaCalc2
public import CFSG.RankThree.PartOne.S11d.FourClaimAux
import CFSG.RankThree.PartOne.S10.EmbeddingTransport
import CFSG.RankThree.PartOne.S10.SelectedPrimeNormalizeThetaComponents
public import CFSG.RankThree.PartOne.S12.Sec125Moved


public section

namespace CFSG.RankThree.PartOne

open Subgroup CFSG CFSG.Assembly CFSG.Blueprint CFSG.RankThree CFSG.RankThree.LocalRank
  CFSG.RankThree.GroupTheory CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement

namespace Sec11Indeed

variable {G : Type} [Group G] [Finite G]


theorem four_main (hS : SchreierFor InCatalog) (h112 : InSec11Two)
    (hbridge : CFSG.Assembly.CatalogImp InCatalog Catalog)
    (hK : CatalogPrimeTwoAutomorphismsInner) (hLS : FieldAutCoset) (hFix : FieldFixedPElements)
    (hCent : FieldFixedCentralizer) {p : ℕ} {A : Subgroup G} {c : G} {L : Subgroup G} {a d : G}
    (sit : Sit p A c L a d) {f : G} {i j : ℤ} (hij : f = a ^ i * c ^ j) (hi : ¬ (p : ℤ) ∣ i)
    (hf1 : f ≠ 1) {R : Subgroup G} (hR : WitnessAt A c f R) {K₀ : Subgroup G}
    (hK₀ : K₀ ∈ thetaComponentsAt p f)
    (hEK₀ : inSubgroup perfectResidual (L ⊓ centralizer ({f} : Set G)) ≤ K₀)
    (hmove' : ∃ r ∈ R, ∃ k ∈ K₀,
      r * k * r⁻¹ * k⁻¹ ∉ inSubgroup (aschbacherSolvableCore p) K₀) :
    K₀ ∈ sectionTenAt p (sectionTenZeroStar p A ∩ sectionTenTwo p A) f ∧
      CFSG.IsQuasisimple ↥K₀ ∧ A ⊓ L ≤ K₀ ∧ FieldAutSetting p K₀ c ∧
      inSubgroup perfectResidual (L ⊓ centralizer ({f} : Set G)) =
        inSubgroup perfectResidual (K₀ ⊓ centralizer ({c} : Set G)) := by
  classical
  have hp := sit.prime
  have hp3 := sit.three_lt
  have hp5 := sit.five_le
  have : Fact p.Prime := ⟨hp⟩
  have hcA := sit.c_mem
  have he : evenRank G ≤ 3 := (sectionTenSetup_evenRank_eq sit.setup).le
  have hcp : c ^ p = 1 := sit.pow_eq_one hcA
  have hfA : f ∈ A := by
    rw [hij]
    exact A.mul_mem (A.zpow_mem sit.a_mem i) (A.zpow_mem hcA j)
  have hfa : InducesFieldAut p f L := hij ▸ sit.inducesFieldAut_mul j hi
  have hEq := fixedRes_isQuasisimple hfa
  set E := inSubgroup perfectResidual (L ⊓ centralizer ({f} : Set G)) with hE
  have hK₀F : K₀ ∈ thetaComponentFamily p A :=
    mem_thetaComponentFamily_iff.mpr ⟨f, hfA, hf1, hK₀⟩
  have hAK₀ : A ≤ normalizer (K₀ : Set G) :=
    selected_prime_elements_normalize_theta_components.2 G he p hp hp3 A sit.A_elem K₀ hK₀F
  have hcf : c ∈ centralizer ({f} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact sit.A_comm hcA hfA
  have hRK₀ : R ≤ normalizer (K₀ : Set G) :=
    commutator_normalizes_thetaComponentsAt he hp hp3 hcf ⟨1, by
      rw [pow_one]; exact orderOf_eq_prime hcp sit.c_ne_one⟩ hR.le_cent hR.comm.le hK₀
  have hcN : c ∈ normalizer (K₀ : Set G) := hAK₀ hcA
  have hcact : ¬ ∀ k ∈ K₀, c * k * c⁻¹ * k⁻¹ ∈ inSubgroup (aschbacherSolvableCore p) K₀ := by
    intro hc
    have := acts_trivially_of_commutator hRK₀ hcN hc hR.comm.le
    obtain ⟨r, hr, k, hk, hno⟩ := hmove'
    exact hno (this r hr k hk)
  have hRA : ⁅R, A⁆ = R := by
    refine le_antisymm (Subgroup.le_normalizer_iff_commutator_le_left.mp hR.norm) ?_
    calc R = ⁅R, zpowers c⁆ := hR.comm
      _ ≤ ⁅R, A⁆ := Subgroup.commutator_mono le_rfl (Subgroup.zpowers_le.mpr hcA)
  have hF0 : K₀ ∈ sectionTenZero p A :=
    exists_zero_of_action hbridge hK sit.setup hfA hf1 hK₀ hAK₀ hR.le_cent hRK₀ hR.two hR.norm
      hRA hmove'
  have hZ := sit.kernel_le_zpowers hCent hij hi hfa hK₀ hAK₀ hEK₀ hcact
  have hFs : K₀ ∈ sectionTenStar p A := mem_sectionTenStar_of_cent sit.setup hfA hf1 hK₀ hAK₀ hZ
  have hK₀zs : K₀ ∈ sectionTenZeroStar p A := ⟨hF0, hFs⟩
  obtain ⟨hq₀, -, -⟩ := moving_maximal_data_at hS sit.setup hK₀zs hfA hf1 hK₀
  have hdf : d * f = f * d := sit.A_comm sit.d_mem hfA
  have hdE : d ∈ E := by
    exact hFix G p L f (sit.fieldAutSetting hfa) (sit.pow_eq_one hfA) (sit.fieldAutRank hfA) d
      ⟨sit.d_mem_L, Subgroup.mem_centralizer_singleton_iff.mpr hdf⟩
      ⟨1, by rw [pow_one]; exact orderOf_eq_prime (sit.pow_eq_one sit.d_mem) sit.d_ne_one⟩
  have hALK₀ : A ⊓ L ≤ K₀ := by
    rw [← sit.d_gen]
    exact zpowers_le.mpr (hEK₀ hdE)
  have hK₀two : K₀ ∈ sectionTenTwo p A := by
    refine ⟨hK₀F, fun h1 => ?_⟩
    exact sit.fail K₀ ⟨hK₀zs, h1⟩ hALK₀
  obtain ⟨hEvenK, hndvdK, a', d', ha'A, hd'A, hd'1, hAeq, hd'K, hfa'⟩ :=
    h112 G p A sit.setup f hfA hf1 K₀ ⟨⟨hK₀zs, hK₀two⟩, hK₀⟩
  have hK₀C : K₀ ≤ centralizer ({f} : Set G) := (mem_thetaComponentsAt_iff.mp hK₀).1
  have hdK₀ : d ∈ K₀ := hEK₀ hdE
  have hdAK : d ∈ A ⊓ K₀ := ⟨sit.d_mem, hdK₀⟩
  have hdd' : zpowers d = zpowers d' := by
    have hle : zpowers d ≤ zpowers d' := by
      rw [hd'K]
      exact zpowers_le.mpr hdAK
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [Nat.card_zpowers, Nat.card_zpowers, orderOf_eq_prime (sit.pow_eq_one sit.d_mem)
      sit.d_ne_one, orderOf_eq_prime (sit.pow_eq_one hd'A) hd'1]
  obtain ⟨x, y, z, hcxyz⟩ := exists_zpow_coords_of_sup hAeq
    (fun _ hx _ hy => sit.A_comm hx hy) hd'A hcA
  have ha'p : a' ^ p = 1 := sit.pow_eq_one ha'A
  have hx : ¬ (p : ℤ) ∣ x := by
    intro hdiv
    have ha'x : a' ^ x = 1 := by
      obtain ⟨u, rfl⟩ := hdiv
      rw [zpow_mul, zpow_natCast, ha'p, one_zpow]
    have hc2 : c = f ^ y * d' ^ z := by rw [hcxyz, ha'x, one_mul]
    have hnot := sit.c_not_mem_sup j hi
    rw [← hij, hdd'] at hnot
    apply hnot
    rw [hc2]
    exact Subgroup.mul_mem_sup (zpow_mem (mem_zpowers f) y) (zpow_mem (mem_zpowers d') z)
  have hd'z : d' ^ z ∈ K₀ := (mem_inf.mp (hd'K ▸ zpow_mem (mem_zpowers d') z)).2
  have hd'p : d' ^ p = 1 := sit.pow_eq_one hd'A
  have hd'zp : (d' ^ z) ^ p = 1 := by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hd'p, one_zpow]
  have ha'd' : a' * d' ^ z = d' ^ z * a' :=
    (Commute.zpow_right (show Commute a' d' from sit.A_comm ha'A hd'A) z).eq
  have hrank₀ : FieldAutRank p K₀ a' :=
    ⟨he, f, Subgroup.mem_centralizer_iff.mpr fun g hg =>
      Subgroup.mem_centralizer_singleton_iff.mp (hK₀C hg), hf1, sit.pow_eq_one hfA,
      sit.A_comm ha'A hfA⟩
  have hcoset := hLS G p K₀ a' (d' ^ z) hp hp5 hq₀ hEvenK hndvdK hfa' ha'p hrank₀ hd'z hd'zp
    ha'd' x hx
  have hfd : Commute (f ^ y) (d' ^ z) := by
    have h1 : Commute f d' := sit.A_comm hfA hd'A
    exact h1.zpow_zpow y z
  have hcc : c = (a' ^ x * d' ^ z) * f ^ y := by
    rw [hcxyz]
    calc a' ^ x * f ^ y * d' ^ z = a' ^ x * (f ^ y * d' ^ z) := by rw [mul_assoc]
      _ = a' ^ x * (d' ^ z * f ^ y) := by rw [hfd.eq]
      _ = a' ^ x * d' ^ z * f ^ y := by rw [mul_assoc]
  have hfy : f ^ y ∈ centralizer (K₀ : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    have h1 : g * f = f * g := Subgroup.mem_centralizer_singleton_iff.mp (hK₀C hg)
    exact (Commute.zpow_right (show Commute g f from h1) y).eq
  have hcfield : InducesFieldAut p c K₀ := by
    rw [hcc]
    refine hcoset.mul_centralizer hfy ?_
    rw [← hcc, hcp]
    exact Subgroup.one_mem _
  have hsetK : FieldAutSetting p K₀ c :=
    ⟨hp, hp5, hq₀, hEvenK, (Sec9A.evenRank_subgroup_le (K₀ ⊔ zpowers c)).trans he, hndvdK,
      hcfield⟩
  have hEL : E ≤ L := (inSubgroup_perfectResidual_le _).trans inf_le_left
  have hEc : E ≤ centralizer ({c} : Set G) := hEL.trans sit.L_le_centralizer
  have hEp : Group.IsPerfect ↥E := EmbeddingFixedResidual.isPerfect_inSubgroup_perfectResidual _
  have hEE₂ : E ≤ inSubgroup perfectResidual (K₀ ⊓ centralizer ({c} : Set G)) :=
    EmbeddingTransport.le_inSubgroup_perfectResidual_of_isPerfect (le_inf hEK₀ hEc) hEp
  have hE₂X : inSubgroup perfectResidual (K₀ ⊓ centralizer ({c} : Set G)) ≤
      centralizer ({c} : Set G) ⊓ centralizer ({f} : Set G) := fun g hg =>
    have h1 := inSubgroup_perfectResidual_le _ hg
    ⟨h1.2, hK₀C h1.1⟩
  have hq₂ := fixedRes_isQuasisimple hcfield
  have hsn := fixedRes_subnormal (f := f) sit.L_mem.2
  have hEne : E ≠ ⊥ := Sec125.ne_bot_of_isQuasisimple hEq
  have hE₂E := le_of_isSubnormal_of_quasisimple hq₂ hEE₂ hE₂X hsn hEp hEne
  have hEeq : inSubgroup perfectResidual (L ⊓ centralizer ({f} : Set G)) =
      inSubgroup perfectResidual (K₀ ⊓ centralizer ({c} : Set G)) := le_antisymm hEE₂ hE₂E
  exact ⟨⟨⟨hK₀zs, hK₀two⟩, hK₀⟩, hq₀, hALK₀, hsetK, hEeq⟩

end Sec11Indeed

end CFSG.RankThree.PartOne
