module

public import CFSG.RankThree.PartTwo.Sec5.Tools
import CFSG.RankThree.PartTwo.Sec5.Item37
import CFSG.RankThree.PartTwo.Source.OrderThreeMinimalTwoGroup
public import CFSG.RankThree.PartTwo.Sec5.Hyp

public section

namespace CFSG.RankThree.PartTwo.Sec5

open CFSG
open scoped Pointwise

universe u

variable {G : Type u} [Group G] [Finite G]

omit [Finite G] in
theorem normalizer_le_normalizer_centralizer (H : Subgroup G) :
    Subgroup.normalizer (H : Set G) ≤
      Subgroup.normalizer (Subgroup.centralizer (H : Set G) : Set G) := by
  intro g hg
  have hconj : ∀ h ∈ H, g⁻¹ * h * g ∈ H := fun h hh =>
    (Subgroup.mem_normalizer_iff.mp hg (g⁻¹ * h * g)).mpr (by simpa [mul_assoc] using hh)
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    rw [Subgroup.mem_centralizer_iff] at hx ⊢
    intro h hh
    have h1 := hx _ (hconj h hh)
    calc h * (g * x * g⁻¹) = g * ((g⁻¹ * h * g) * x) * g⁻¹ := by group
      _ = g * (x * (g⁻¹ * h * g)) * g⁻¹ := by rw [h1]
      _ = g * x * g⁻¹ * h := by group
  · intro hx
    rw [Subgroup.mem_centralizer_iff] at hx ⊢
    intro h hh
    have h1 := hx (g * h * g⁻¹) ((Subgroup.mem_normalizer_iff.mp hg h).mp hh)
    have h2 : g * (h * x) * g⁻¹ = g * (x * h) * g⁻¹ := by
      calc g * (h * x) * g⁻¹ = g * h * g⁻¹ * (g * x * g⁻¹) := by group
        _ = g * x * g⁻¹ * (g * h * g⁻¹) := h1
        _ = g * (x * h) * g⁻¹ := by group
    simpa using h2

theorem mem_of_le_normalizer (he : CFSG.Assembly.evenRank G = 3) {A T : Subgroup G}
    (hA : CFSG.Assembly.IsElemAbelian 3 A) (hAcard : Nat.card A = 27) (hT : T ≠ ⊥)
    (hT2 : IsPGroup 2 T) (hAT : A ≤ Subgroup.normalizer (T : Set G)) {y : G}
    (hyT : y ∈ Subgroup.normalizer (T : Set G)) (hyA : y ∈ Subgroup.centralizer (A : Set G))
    (hy3 : y ^ 3 = 1) : y ∈ A := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra hy
  obtain ⟨hE, hcard⟩ := isElemAbelian_sup_zpowers hA hy hy3
    (fun a ha => Subgroup.mem_centralizer_iff.mp hyA a ha)
  have hle := card_le_of_le_normalizer he hT hT2 hE (sup_le hAT (Subgroup.zpowers_le.mpr hyT))
  rw [hcard, hAcard] at hle
  omega

theorem lt_inf_normalizer_of_lt {S T : Subgroup G} (hS : IsPGroup 2 S) (hTS : T < S) :
    T < S ⊓ Subgroup.normalizer (T : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsNilpotent S := hS.isNilpotent
  have htop : T.subgroupOf S < ⊤ := by
    refine lt_top_iff_ne_top.mpr fun h => hTS.not_ge ?_
    rwa [Subgroup.subgroupOf_eq_top] at h
  have hlt := Group.normalizerCondition_of_isNilpotent (T.subgroupOf S) htop
  rw [← Subgroup.subgroupOf_normalizer_eq hTS.le] at hlt
  have hmap := (Subgroup.map_lt_map_iff_of_injective (f := S.subtype) S.subtype_injective).mpr hlt
  rw [Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
    inf_eq_left.mpr hTS.le, inf_comm] at hmap
  exact hmap

theorem commutator_inf_centralizer_eq_bot {A S : Subgroup G}
    (h : SectionFiveHyp A S) {T : Subgroup G} (hT : T ≠ ⊥) (hTS : T ≤ S)
    (hAT : A ≤ Subgroup.normalizer (T : Set G)) :
    ⁅CFSG.pCore 3 G ⊓ Subgroup.centralizer (T : Set G),
      S ⊓ Subgroup.normalizer (T : Set G)⁆ = ⊥ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hP3 : IsPGroup 3 (CFSG.pCore 3 G) := CFSG.pCore_isPGroup
  have hT2 : IsPGroup 2 T := h.isPGroup.to_le hTS
  have hNP : ∀ g : G, g ∈ Subgroup.normalizer ((CFSG.pCore 3 G : Subgroup G) : Set G) := by
    intro g
    rw [Subgroup.normalizer_eq_top]
    exact Subgroup.mem_top g
  have hNQ : Subgroup.normalizer (T : Set G) ≤
      Subgroup.normalizer ((CFSG.pCore 3 G ⊓ Subgroup.centralizer (T : Set G) : Subgroup G) :
        Set G) := fun g hg =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hNP g, normalizer_le_normalizer_centralizer T hg⟩
  refine rank3II_3_7 G 3 Nat.prime_three (by norm_num) A (S ⊓ Subgroup.normalizer (T : Set G))
    (CFSG.pCore 3 G ⊓ Subgroup.centralizer (T : Set G)) h.elemAbelian
    (Source.not_three_dvd_card_of_isPGroup_two (h.isPGroup.to_le inf_le_left))
    (fun a ha => Subgroup.inf_normalizer_le_normalizer_inf
      ⟨h.le_normalizer ha, Subgroup.le_normalizer (hAT ha)⟩)
    (hP3.to_le inf_le_left) (fun a ha => hNQ (hAT ha)) (fun s hs => hNQ hs.2) ?_
  intro y hy hy3
  have hyN : y ∈ Subgroup.normalizer (T : Set G) := by
    refine (sup_le hAT ?_) hy.1
    exact inf_le_right.trans (Subgroup.centralizer_le_normalizer (T : Set G))
  exact mem_of_le_normalizer h.evenRank_eq h.elemAbelian h.card_eq hT hT2 hAT hyN hy.2 hy3

theorem rank3II_5_2 {A S : Subgroup G} (h : SectionFiveHyp A S)
    {T : Subgroup G} (hT : T ≠ ⊥) (hTS : T ≤ S) (hAT : A ≤ Subgroup.normalizer (T : Set G)) :
    CFSG.pCore 3 G ⊓ Subgroup.centralizer (T : Set G) =
      CFSG.pCore 3 G ⊓ Subgroup.centralizer (S : Set G) := by
  induction hn : Nat.card S - Nat.card T using Nat.strong_induction_on generalizing T with
  | _ n ih =>
  by_cases hTeq : T = S
  · rw [hTeq]
  have hlt : T < S ⊓ Subgroup.normalizer (T : Set G) :=
    lt_inf_normalizer_of_lt h.isPGroup (lt_of_le_of_ne hTS hTeq)
  set K := S ⊓ Subgroup.normalizer (T : Set G)
  have hK : K ≠ ⊥ := ne_bot_of_gt (bot_lt_iff_ne_bot.mpr hT |>.trans hlt)
  have hAK : A ≤ Subgroup.normalizer (K : Set G) := fun a ha =>
    Subgroup.inf_normalizer_le_normalizer_inf
      ⟨h.le_normalizer ha, Subgroup.le_normalizer (hAT ha)⟩
  have hcardK : Nat.card T < Nat.card K := Subgroup.card_lt_of_lt hlt
  have hKS : Nat.card K ≤ Nat.card S := Subgroup.card_le_of_le inf_le_left
  have ihK := ih (Nat.card S - Nat.card K) (by omega) hK inf_le_left hAK rfl
  apply le_antisymm
  · rw [← ihK]
    refine le_inf inf_le_left ?_
    have hc := commutator_inf_centralizer_eq_bot h hT hTS hAT
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hc
  · exact inf_le_inf_left _ (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hTS))

theorem rank3II_5_3 {A S : Subgroup G} (h : SectionFiveHyp A S) :
    S ⊓ Subgroup.centralizer (CFSG.pCore 3 G : Set G) = ⊥ := by
  by_contra hT
  have hAT : A ≤ Subgroup.normalizer
      ((S ⊓ Subgroup.centralizer (CFSG.pCore 3 G : Set G) : Subgroup G) : Set G) := by
    intro a ha
    refine Subgroup.inf_normalizer_le_normalizer_inf ⟨h.le_normalizer ha, ?_⟩
    refine normalizer_le_normalizer_centralizer _ ?_
    rw [Subgroup.normalizer_eq_top]
    exact Subgroup.mem_top a
  have h52 := rank3II_5_2 h hT inf_le_left hAT
  have hP : CFSG.pCore 3 G ≤ Subgroup.centralizer (S : Set G) := by
    have hle : CFSG.pCore 3 G ≤ CFSG.pCore 3 G ⊓ Subgroup.centralizer
        ((S ⊓ Subgroup.centralizer (CFSG.pCore 3 G : Set G) : Subgroup G) : Set G) := by
      refine le_inf le_rfl ?_
      rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm,
        Subgroup.commutator_eq_bot_iff_le_centralizer]
      exact inf_le_right
    rw [h52] at hle
    exact hle.trans inf_le_right
  exact h.commutator_ne_bot (Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hP)

theorem no_fourGroup_centralizer {A S : Subgroup G}
    (h : SectionFiveHyp A S) {V : Subgroup G} (hVS : V ≤ S ⊓ Subgroup.centralizer (A : Set G))
    (hV : CFSG.Assembly.IsElemAbelian 2 V) (hVcard : Nat.card V = 4) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hP3 : IsPGroup 3 (CFSG.pCore 3 G) := CFSG.pCore_isPGroup
  have hcop : Nat.Coprime 2 (Nat.card (CFSG.pCore 3 G)) := by
    obtain ⟨k, hk⟩ := hP3.exists_card_eq
    rw [hk]
    exact Nat.Coprime.pow_right k (by norm_num)
  have hVP : V ≤ Subgroup.normalizer ((CFSG.pCore 3 G : Subgroup G) : Set G) := by
    rw [Subgroup.normalizer_eq_top]
    exact le_top
  have hP : CFSG.pCore 3 G ≤ Subgroup.centralizer (S : Set G) := by
    refine le_of_forall_inf_centralizer_le Nat.prime_two hV (by rw [hVcard]; norm_num) hVP hcop ?_
    intro v hv hv1
    have hz : Subgroup.zpowers v ≠ ⊥ := fun hb => hv1 (by
      simpa [hb] using Subgroup.mem_zpowers v)
    have hAz : A ≤ Subgroup.normalizer ((Subgroup.zpowers v : Subgroup G) : Set G) := by
      intro a ha
      refine Subgroup.centralizer_le_normalizer _ ?_
      rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure, Subgroup.mem_centralizer_iff]
      rintro _ rfl
      exact (Subgroup.mem_centralizer_iff.mp (hVS hv).2 a ha).symm
    have h52 := rank3II_5_2 h hz (Subgroup.zpowers_le.mpr (hVS hv).1) hAz
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure] at h52
    rw [h52]
    exact inf_le_right
  exact h.commutator_ne_bot (Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hP)

theorem rank3II_5_4 {A S : Subgroup G} (h : SectionFiveHyp A S) :
    CFSG.Assembly.pRank 2 (S ⊓ Subgroup.centralizer (A : Set G)) ≤ 1 := by
  by_contra hlt
  obtain ⟨V, hVS, hV, hVcard⟩ := exists_elemAbelian_le_of_le_pRank Nat.prime_two
    (X := S ⊓ Subgroup.centralizer (A : Set G)) (k := 2) (by omega)
  exact no_fourGroup_centralizer h hVS hV (by rw [hVcard]; norm_num)

end CFSG.RankThree.PartTwo.Sec5
