module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatHeCertificate
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtElRestBase
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtElRestSyl
public import CFSG.Quasithin.Background.F420Basic
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatHe
import all CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatHe
public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicHe
public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamilies
public import CFSG.Sporadic.He

public section

namespace CFSG.Quasithin.ModH

open CFSG.Blueprint CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1.SporLat
  CFSG.QuasithinUnique.Ch1.SporLat.He CFSG.QuasithinUnique.K1.SporadicPerm CFSG.Sporadic.He

theorem he_center_data :
    ∃ (Q : Subgroup J) (zJ : J), IsSylowTwoOf Q ⊤ ∧
      ∀ c ∈ Q, (∀ q ∈ Q, c * q = q * c) → c = 1 ∨ c = zJ := by
  have h := center_closure_of_baseCertS (n := 8330) heB he_base_lt he_base_property
    (a : J) (b : J) heProg he_valid heQp 170 249 253 251 255 heEnum.1 heEnum.2.1 heEnum.2.2 10
    3935925 he_card (by decide) he_cert'
  exact ⟨_, _, h.1, h.2⟩

theorem he_normalizer_sylow
    {X : Type} [Group X]
    (hX : Nonempty (X ≃* NativeSporadic.Carrier .He)) {T : Subgroup X} (hT : IsSylowTwoOf T ⊤) :
    ∀ g ∈ Subgroup.normalizer (T : Set X), g ∈ T := by
  obtain ⟨e⟩ := hX
  have hXc : Nat.card X = 2 ^ 10 * 3935925 := by
    rw [Nat.card_congr e.toEquiv,
      show Nat.card (NativeSporadic.Carrier .He) = Nat.card NativeSporadic.He from rfl, card_He]
    norm_num
  have : Finite X := Nat.finite_of_card_ne_zero (by rw [hXc]; norm_num)
  have hTc : Nat.card T = 2 ^ 10 := card_eq_pow_of_isSylowTwoOf_top hT hXc (by norm_num)
  have hTp : IsPGroup 2 T := (K1.isSylowTwoOf_top_iff.1 hT).1
  have hTK : T ≤ Subgroup.normalizer (T : Set X) := Subgroup.le_normalizer
  have hle : T ≤ pCoreOf 2 (Subgroup.normalizer (T : Set X)) :=
    le_pCoreOf_of_normalizes hTK le_rfl hTp
  have hX' : Nonempty (X ≃* NativeSporadic.Carrier .He) := ⟨e⟩
  rcases he_overgroups hX' hT hTK with htop | ⟨m, hm, hord, ho2, -⟩
  · exfalso
    have hnorm : T.Normal := Subgroup.normalizer_eq_top_iff.1 htop
    have hsimple : IsSimpleGroup X := by
      have : IsSimpleGroup (NativeSporadic.Carrier .He) := (fam_he_simplicity).2.2
      exact e.isSimpleGroup
    rcases hsimple.eq_bot_or_eq_top_of_normal T with h | h
    · rw [h, Subgroup.card_bot] at hTc
      exact absurd hTc (by norm_num)
    · rw [h, Subgroup.card_top, hXc] at hTc
      exact absurd hTc (by norm_num)
  · have hcard := Subgroup.card_le_of_le hle
    rw [ho2, hTc] at hcard
    simp only [heMems, List.mem_cons, List.not_mem_nil, or_false] at hm
    have hm0 : m = ⟨1024, 1024, 1024⟩ := by
      rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        first | rfl | (exfalso; revert hcard; decide)
    subst hm0
    have hK : Subgroup.normalizer (T : Set X) = T :=
      (Subgroup.eq_of_le_of_card_ge hTK (by rw [hord, hTc]; norm_num)).symm
    intro g hg
    rw [← hK]
    exact hg

theorem he_smallCentralizerWitness :
    F420.SmallCentralizerWitness (NativeSporadic.Carrier .He) := by
  obtain ⟨Q, zJ, hQ, hQz⟩ := he_center_data
  have key : ∃ (T : Subgroup (NativeSporadic.Carrier .He)) (z : NativeSporadic.Carrier .He),
      IsSylowTwoOf T ⊤ ∧ IsPGroup 2 T ∧
        ∀ c ∈ T, (∀ t ∈ T, c * t = t * c) → c = 1 ∨ c = z :=
    @exists_sylow_center_of_equiv J (NativeSporadic.Carrier .He) _ _ heEquivJ.symm Q zJ hQ hQz
  obtain ⟨T, z, hT, hTp, hz⟩ := key
  refine ⟨T, z, hTp, fun x hx => ?_⟩
  have hxn : x ∈ Subgroup.normalizer (T : Set (NativeSporadic.Carrier .He)) :=
    Subgroup.centralizer_le_normalizer _
      (Subgroup.mem_centralizer_iff.2 fun t ht => (hx t ht).symm)
  exact hz x (he_normalizer_sylow ⟨MulEquiv.refl _⟩ hT x hxn) hx

end CFSG.Quasithin.ModH
