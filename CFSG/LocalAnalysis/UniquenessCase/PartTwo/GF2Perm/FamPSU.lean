module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.GF2Perm.OfType
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.GF2Perm.TorusE9
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.GF2Perm.EndNodes
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.GF2Perm.SUOddTorus
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.GOrbFamSU
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.GOrbNodes

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.GF2Perm

open CFSG.Open CFSG.AGLEmbedding.ParabHub CFSG.AGLEmbedding.ParabPrime CFSG.LieType.Universal
  CFSG.LieType.CurtisTits CFSG.LieType.RootSystem CFSG.LieType.Steinberg
  CFSG.LieType.Universal.Unitary CFSG.LieType.Universal.Unitary.SUExtras CFSG.LieType.BorelTits
  CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank CFSG.AGLEmbeddingD2.Tits.GN516.Nodes
  CFSG.AGLEmbeddingD2.Tits.GN516.Fam CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinPar
  Matrix

private theorem permWitness_of_su_odd {F : Type} [Field F] [Finite F] [CharP F 2]
    (hF : Nat.card F = (2 ^ 1) ^ 2) {n : ℕ} (hn4 : 4 ≤ n) (hodd : ¬ Even n)
    {Y : Type} [Group Y] [Finite Y]
    {nn : Fin (rootDatum hF n).rank → SU (unitaryInvolution F 2 1) n}
    {π : SU (unitaryInvolution F 2 1) n →* Y}
    (h : BorelQuotient (rootDatum hF n) nn (levelTorus (unitaryInvolution F 2 1)) π 3)
    (hker : ∀ z ∈ π.ker, ∃ u : Fˣ,
      mat (unitaryInvolution F 2 1) n z = Matrix.scalar (Fin n) (u : F)) :
    PermWitness Y := by
  have : Fintype F := Fintype.ofFinite F
  have : Finite (SU (unitaryInvolution F 2 1) n) :=
    Finite.of_injective _ Subtype.val_injective
  have hn5 : 5 ≤ n := by
    rw [Nat.not_even_iff_odd] at hodd
    obtain ⟨k, hk⟩ := hodd
    omega
  obtain ⟨E, hE, hE1, hE9⟩ := su_exists_E9_le_borel_odd hF hodd hn5 h hker
  exact permWitness_of_borelQuotient h (by norm_num) (J := ∅) (by simp) (by simp) (by simp)
    hE hE1 hE9

private theorem permWitness_of_su_even {F : Type} [Field F] [Finite F] [CharP F 2]
    (hF : Nat.card F = (2 ^ 1) ^ 2) {n : ℕ} (hn4 : 4 ≤ n) (he : Even n)
    {Y : Type} [Group Y] [Finite Y]
    {nn : Fin (rootDatum hF n).rank → SU (unitaryInvolution F 2 1) n}
    {π : SU (unitaryInvolution F 2 1) n →* Y}
    (h : BorelQuotient (rootDatum hF n) nn (levelTorus (unitaryInvolution F 2 1)) π 3) :
    PermWitness Y := by
  have : Fintype F := Fintype.ofFinite F
  have : Finite (SU (unitaryInvolution F 2 1) n) :=
    Finite.of_injective _ Subtype.val_injective
  have h2 : 2 ≤ n / 2 := by
    have h := Nat.two_mul_div_two_of_even he
    omega
  let a : Fin (rootDatum hF n).rank := ⟨n / 2 - 1, by change n / 2 - 1 < n / 2; omega⟩
  let b : Fin (rootDatum hF n).rank := ⟨0, by change 0 < n / 2; omega⟩
  have hlast : ¬ a.val + 1 < n / 2 := by
    change ¬ n / 2 - 1 + 1 < n / 2
    omega
  have hfirst : b.val + 1 < n / 2 := by
    change 0 + 1 < n / 2
    omega
  have h6card : Nat.card (rankOne (rootDatum hF n).rootGroup a) = 6 :=
    su_last_even_card hF he (k := a) hlast
  have h6a : Nat.card (rankOne (rootDatum hF n).rootGroup a) = 6 ∧
      ∃ x ∈ rankOne (rootDatum hF n).rootGroup a,
        ∃ y ∈ rankOne (rootDatum hF n).rootGroup a, x * y ≠ y * x :=
    ⟨h6card, noncomm_of_card_six_of_hasOrderThree h h6card (hasOrderThree_su hF a)⟩
  have hs : HasTorusSL2 (rootDatum hF n) (levelTorus (unitaryInvolution F 2 1)) b F :=
    hasTorusSL2_su_short hF hfirst
  have h4 : Nat.card F = 4 := by rw [hF]; norm_num
  have hb : 2 < Nat.card ↥((rootDatum hF n).rootGroup (Pi.single b 1)) := by
    have hle := card_le_card_rootGroup_of_hasTorusSL2 hs
    omega
  have hpath : ∀ i j : Fin (rootDatum hF n).rank, i ≠ j →
      ((rootDatum hF n).cartan i j ≠ 0 ↔ i.val + 1 = j.val ∨ j.val + 1 = i.val) :=
    fun i j hij => cartan_ne_zero_iff (n := n) hij
  have hJeq : endNodesThree (rootDatum hF n) (levelTorus (unitaryInvolution F 2 1)) = {a} :=
    endNodesThree_eq_of_path h (by change 2 ≤ n / 2; omega) hpath
      (Or.inr ⟨rfl, by change n / 2 - 1 + 1 = n / 2; omega⟩) h6a hb
  obtain ⟨E, hEP, hE1, hE9⟩ :=
    exists_E9_le_parJ_singleton h hs (hasOrderThree_su hF a) h6a
  exact permWitness_of_borelQuotient_singleton h (by norm_num) hJeq h6a hEP hE1 hE9

theorem permWitnessPSU_holds : PermWitnessPSU := by
  intro G _ _ m hm hL
  have hSG : StatedClassicalModel G .PSU m 2 1 := hL.statedClassicalModel (by decide)
  obtain ⟨⟨-, -, hn, -⟩, F, hF, hFfin, hcard, ⟨e⟩⟩ := hSG
  have : Finite F := hFfin
  have : Fintype F := Fintype.ofFinite F
  have : CharP F 2 := charP_of_card_eq_prime_pow (f := 1 * 2)
    (by rw [← Nat.card_eq_fintype_card, hcard, pow_mul])
  obtain ⟨ζ, hζ⟩ := exists_traceZero_ne_zero hcard
  have : Finite (SU (unitaryInvolution F 2 1) m) :=
    Finite.of_injective _ Subtype.val_injective
  have hM : Nat.card F - 1 = 3 := by rw [hcard]; norm_num
  let π : SU (unitaryInvolution F 2 1) m →* G :=
    e.symm.toMonoidHom.comp ((QuotientGroup.mk' ((StatedScalars (Fin m) F).subgroupOf
      (StatedSU m (2 ^ 1) F))).comp (equivStatedSU hcard m).toMonoidHom)
  have h0 : BorelQuotient (rootDatum hcard m) (levelWeyl (unitaryInvolution_involutive hcard) ζ)
      (levelTorus (unitaryInvolution F 2 1)) π (Nat.card F - 1) :=
    borelQuotient_su hcard (by omega : 2 ≤ m) ζ hζ e
  rw [hM] at h0
  have hker : ∀ z ∈ π.ker, ∃ u : Fˣ,
      mat (unitaryInvolution F 2 1) m z = Matrix.scalar (Fin m) (u : F) := by
    intro z hz
    rw [MonoidHom.mem_ker] at hz
    have hz1 : ((QuotientGroup.mk' ((StatedScalars (Fin m) F).subgroupOf
        (StatedSU m (2 ^ 1) F))).comp (equivStatedSU hcard m).toMonoidHom) z = 1 := by
      apply e.symm.injective
      simpa [π] using hz
    exact (mem_ker_su_iff hcard z).mp (by simpa only [MonoidHom.mem_ker] using hz1)
  by_cases he : Even m
  · exact permWitness_of_su_even hcard hm he h0
  · exact permWitness_of_su_odd hcard hm he h0 hker

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.GF2Perm
