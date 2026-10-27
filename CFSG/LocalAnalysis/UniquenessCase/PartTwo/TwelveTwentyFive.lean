module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs12c4
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveTwentyFiveA
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveTwentyThreeOne

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace TwelveTwentyFive

theorem not_isPGroup_map (D : Data G) {V L : Subgroup G} (hV : InCalW D.M D.T V)
    (hL : F12.IsComponentModO2 D.M L) (hLV : ⁅L, V⁆ ≠ ⊥)
    (hJL : ⁅F12.jOf D.T, L⁆ ≤ pCoreOf 2 L) :
    ¬ IsPGroup 2 ↥((L.subgroupOf (normalizer (proofE D : Set G))).map
      (uc22br4_conjAut (normalizer (proofE D : Set G)) (proofE D) le_rfl)) := by
  intro h2
  have hLE := le_normalizer_proofE D hL hJL
  apply hLV
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  have hV' : InCalV D.M V := hV.1.1
  have hMV : D.M ≤ normalizer (V : Set G) := hV'.2.2.1
  have hPV : pCoreOf 2 D.M ≤ centralizer (V : Set G) :=
    TwelveTwentyThree.pCoreOf_le_centralizer_of_twoReduced hMV hV.2.2
  refine le_centralizer_of_forall_odd hL hMV hPV (fun c hc hodd => ?_)
  refine mem_centralizer_of_odd D hV' (hL.2.1 hc) hodd (fun j hj => ?_) ?_
  · have h1 : ⁅j, c⁆ ∈ pCoreOf 2 L := hJL (Subgroup.commutator_mem_commutator hj hc)
    rw [pCoreOf_eq hL] at h1
    rw [← commutatorElement_inv]
    exact Subgroup.inv_mem _ (hPV h1)
  · set ρ := uc22br4_conjAut (normalizer (proofE D : Set G)) (proofE D) le_rfl with hρ
    have hmem : ρ ⟨c, hLE hc⟩ ∈ (L.subgroupOf (normalizer (proofE D : Set G))).map ρ :=
      Subgroup.mem_map_of_mem ρ (show (⟨c, hLE hc⟩ : ↥(normalizer (proofE D : Set G))) ∈
        L.subgroupOf _ from hc)
    obtain ⟨k, hk⟩ := h2 ⟨_, hmem⟩
    have hk' : (ρ ⟨c, hLE hc⟩) ^ (2 ^ k) = 1 := by
      have := congrArg Subtype.val hk
      simpa using this
    have hc' : (ρ ⟨c, hLE hc⟩) ^ (orderOf c) = 1 := by
      rw [← map_pow]
      have : (⟨c, hLE hc⟩ : ↥(normalizer (proofE D : Set G))) ^ orderOf c = 1 := by
        apply Subtype.ext
        simp [pow_orderOf_eq_one]
      rw [this, map_one]
    have hone : ρ ⟨c, hLE hc⟩ = 1 := by
      have hd1 := orderOf_dvd_of_pow_eq_one hk'
      have hd2 := orderOf_dvd_of_pow_eq_one hc'
      have hcop : Nat.Coprime (2 ^ k) (orderOf c) :=
        Nat.Coprime.pow_left _ (Nat.coprime_two_left.2 hodd)
      rw [← orderOf_eq_one_iff]
      exact Nat.dvd_one.1 (hcop ▸ Nat.dvd_gcd hd1 hd2)
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    have h3 : c * e * c⁻¹ = e :=
      congrArg (fun f : MulAut ↥(proofE D) => ((f ⟨e, he⟩ : ↥(proofE D)) : G)) hone
    calc e * c = c * e * c⁻¹ * c := by rw [h3]
      _ = c * e := by group

theorem conj_mem_of_mem_proofS (D : Data G) {V L : Subgroup G} (hV : InCalW D.M D.T V)
    (hL : F12.IsComponentModO2 D.M L) (hLV : ⁅L, V⁆ ≠ ⊥)
    (hJL : ⁅F12.jOf D.T, L⁆ ≤ pCoreOf 2 L) {s : G} (hs : s ∈ proofS D) :
    ∀ y ∈ L, s * y * s⁻¹ ∈ L := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLE := le_normalizer_proofE D hL hJL
  have hLM : L ≤ D.M := hL.2.1
  have hsM : s ∈ D.M := D.sylowM.le hs.1
  set π : ↥D.M →* UC22.Bar2 D.M := QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) with hπ
  have hker : ∀ m : ↥D.M, π m = 1 ↔ (m : G) ∈ pCoreOf 2 D.M := by
    intro m
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact (Subgroup.mem_map_iff_mem D.M.subtype_injective).symm
  have hC := isComponent_map hL
  set C := (L.subgroupOf D.M).map π with hCdef
  set σ : UC22.Bar2 D.M ≃* UC22.Bar2 D.M := MulAut.conj (π ⟨s, hsM⟩) with hσ
  have hC' := CFSG.LocalCores.isComponent_map_mulEquiv σ hC
  have hsy : ∀ y ∈ L, ∀ hy : s * y * s⁻¹ ∈ D.M,
      π ⟨s * y * s⁻¹, hy⟩ ∈ C.map σ.toMonoidHom := by
    intro y hy hyM
    refine ⟨π ⟨y, hLM hy⟩, ⟨⟨y, hLM hy⟩, hy, rfl⟩, ?_⟩
    have e : (⟨s * y * s⁻¹, hyM⟩ : ↥D.M) = ⟨s, hsM⟩ * ⟨y, hLM hy⟩ * ⟨s, hsM⟩⁻¹ := rfl
    rw [e, map_mul, map_mul, map_inv]
    rfl
  have hsyM : ∀ y ∈ L, s * y * s⁻¹ ∈ D.M := fun y hy =>
    D.M.mul_mem (D.M.mul_mem hsM (hLM hy)) (D.M.inv_mem hsM)
  rcases CFSG.LocalCores.distinct_components_commute hC hC' with heq | hcomm
  · intro y hy
    have hmem := hsy y hy (hsyM y hy)
    rw [← heq] at hmem
    obtain ⟨l, hl, hlπ⟩ := hmem
    have h1 : π (l⁻¹ * ⟨s * y * s⁻¹, hsyM y hy⟩) = 1 := by
      rw [map_mul, map_inv, hlπ, inv_mul_cancel]
    rw [hker] at h1
    have h2 : s * y * s⁻¹ = (l : G) * ((l⁻¹ * ⟨s * y * s⁻¹, hsyM y hy⟩ : ↥D.M) : G) := by simp
    rw [h2]
    exact L.mul_mem hl (hL.1 h1)
  · exfalso
    apply not_isPGroup_map D hV hL hLV hJL
    set N := normalizer (proofE D : Set G) with hNdef
    set ρ := uc22br4_conjAut N (proofE D) le_rfl with hρ
    have hP : IsPGroup 2 ↥(((pCoreOf 2 D.M).subgroupOf N).map ρ) :=
      ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 D.M).comap_subtype).map ρ
    refine hP.to_le ?_
    have hON : pCoreOf 2 D.M ≤ N := (uc22p22e_pCoreOf_le_T D).trans (T_le_normalizer_proofE D)
    have hsN : s ∈ N := T_le_normalizer_proofE D hs.1
    have hsE : ρ ⟨s, hsN⟩ = 1 := by
      ext e
      show s * (e : G) * s⁻¹ = e
      have h3 := Subgroup.mem_centralizer_iff.1 hs.2 (e : G) e.2
      calc s * (e : G) * s⁻¹ = (e : G) * s * s⁻¹ := by rw [← h3]
        _ = e := by group
    set Q : Subgroup G := ((((pCoreOf 2 D.M).subgroupOf N).map ρ).comap ρ).map N.subtype
      with hQ
    have hmemQ : ∀ (g : G) (hg : g ∈ N),
        g ∈ Q ↔ ρ ⟨g, hg⟩ ∈ ((pCoreOf 2 D.M).subgroupOf N).map ρ := by
      intro g hg
      constructor
      · rintro ⟨n, hn, rfl⟩
        exact hn
      · intro h
        exact ⟨⟨g, hg⟩, h, rfl⟩
    have hOQ : pCoreOf 2 D.M ≤ Q := fun p hp =>
      (hmemQ p (hON hp)).2 (Subgroup.mem_map_of_mem ρ hp)
    have hcomQ : ⁅L, L⁆ ≤ Q := by
      rw [Subgroup.commutator_le]
      intro a ha b hb
      have hab : ⁅a, s * b * s⁻¹⁆ ∈ pCoreOf 2 D.M := by
        have h1 : π ⁅(⟨a, hLM ha⟩ : ↥D.M), ⟨s * b * s⁻¹, hsyM b hb⟩⁆ = 1 := by
          rw [map_commutatorElement]
          have hmem := Subgroup.commutator_mem_commutator
            (show π ⟨a, hLM ha⟩ ∈ C from ⟨⟨a, hLM ha⟩, ha, rfl⟩) (hsy b hb (hsyM b hb))
          rw [hcomm] at hmem
          exact hmem
        exact (hker _).1 h1
      have habN : ⁅a, b⁆ ∈ N := by
        rw [commutatorElement_def]
        exact N.mul_mem (N.mul_mem (N.mul_mem (hLE ha) (hLE hb)) (N.inv_mem (hLE ha)))
          (N.inv_mem (hLE hb))
      have habsN : ⁅a, s * b * s⁻¹⁆ ∈ N := hON hab
      refine (hmemQ _ habN).2 ?_
      have e1 : (⟨⁅a, b⁆, habN⟩ : ↥N) = ⁅(⟨a, hLE ha⟩ : ↥N), ⟨b, hLE hb⟩⁆ := rfl
      have e2 : (⟨⁅a, s * b * s⁻¹⁆, habsN⟩ : ↥N) =
          ⁅(⟨a, hLE ha⟩ : ↥N), ⟨s, hsN⟩ * ⟨b, hLE hb⟩ * ⟨s, hsN⟩⁻¹⁆ := rfl
      have e3 : ρ ⟨⁅a, b⁆, habN⟩ = ρ ⟨⁅a, s * b * s⁻¹⁆, habsN⟩ := by
        rw [e1, e2, map_commutatorElement, map_commutatorElement, map_mul, map_mul, map_inv,
          hsE, one_mul, inv_one, mul_one]
      rw [e3]
      exact Subgroup.mem_map_of_mem ρ hab
    have hLQ : L ≤ Q := by
      intro x hx
      obtain ⟨y, hy, hyx⟩ := exists_mem_commutator hL hx
      have e : x = y * (y⁻¹ * x) := by group
      rw [e]
      exact Q.mul_mem (hcomQ hy) (hOQ hyx)
    rintro _ ⟨⟨x, hxN⟩, hx, rfl⟩
    exact (hmemQ x hxN).1 (hLQ hx)

theorem commutator_mem_of_mem_proofS (D : Data G) {V L : Subgroup G} (hV : InCalW D.M D.T V)
    (hL : F12.IsComponentModO2 D.M L) (hLV : ⁅L, V⁆ ≠ ⊥)
    (hJL : ⁅F12.jOf D.T, L⁆ ≤ pCoreOf 2 L) :
    ∀ x ∈ L, ∀ s ∈ proofS D, ⁅x, s⁆ ∈ pCoreOf 2 D.M := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLE := le_normalizer_proofE D hL hJL
  have hLCE : L ≤ normalizer ((centralizer (proofE D : Set G) : Subgroup G) : Set G) :=
    A1a.le_normalizer_centralizer hLE
  have hLM : L ≤ D.M := hL.2.1
  set π : ↥D.M →* UC22.Bar2 D.M := QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) with hπ
  have hker : ∀ m : ↥D.M, π m = 1 ↔ (m : G) ∈ pCoreOf 2 D.M := by
    intro m
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact (Subgroup.mem_map_iff_mem D.M.subtype_injective).symm
  have hC := isComponent_map hL
  set C := (L.subgroupOf D.M).map π with hCdef
  set U : Subgroup G := L ⊓ centralizer (proofE D : Set G) with hUdef
  set Ũ := (U.subgroupOf D.M).map π with hŨ
  have hUC : Ũ ≤ C := Subgroup.map_mono (fun x hx => hx.1)
  have hUn : (Ũ.subgroupOf C).Normal := by
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨u, hu, hun⟩ := hn
    obtain ⟨l, hl, hlg⟩ := g.2
    refine ⟨l * u * l⁻¹, ⟨?_, ?_⟩, ?_⟩
    · exact L.mul_mem (L.mul_mem hl hu.1) (L.inv_mem hl)
    · exact (Subgroup.mem_normalizer_iff.1 (hLCE hl) _).1 hu.2
    · rw [map_mul, map_mul, map_inv, hun, hlg]
      rfl
  have hUsn : Ũ.IsSubnormal := Subgroup.IsSubnormal.step Ũ C hUC hC.2 hUn
  rcases CFSG.LocalCores.component_subnormal_subgroup hC hUsn with hle | hcomm
  · exfalso
    apply not_isPGroup_map D hV hL hLV hJL
    set N := normalizer (proofE D : Set G) with hNdef
    set ρ := uc22br4_conjAut N (proofE D) le_rfl with hρ
    have hP : IsPGroup 2 ↥(((pCoreOf 2 D.M).subgroupOf N).map ρ) :=
      ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 D.M).comap_subtype).map ρ
    refine hP.to_le ?_
    have hON : pCoreOf 2 D.M ≤ N := (uc22p22e_pCoreOf_le_T D).trans (T_le_normalizer_proofE D)
    rintro _ ⟨⟨x, hxN⟩, hx, rfl⟩
    obtain ⟨u, hu, huπ⟩ := hle ⟨⟨x, hLM hx⟩, hx, rfl⟩
    have h1 : π (u⁻¹ * ⟨x, hLM hx⟩) = 1 := by rw [map_mul, map_inv, huπ, inv_mul_cancel]
    rw [hker] at h1
    have huN : (u : G) ∈ N := hLE hu.1
    have huE : ρ ⟨u, huN⟩ = 1 := by
      ext e
      show (u : G) * (e : G) * (u : G)⁻¹ = e
      have h3 : (e : G) * (u : G) = (u : G) * e := Subgroup.mem_centralizer_iff.1 hu.2 (e : G) e.2
      calc (u : G) * (e : G) * (u : G)⁻¹ = (e : G) * u * (u : G)⁻¹ := by rw [← h3]
        _ = e := by group
    refine ⟨⟨(u : G)⁻¹ * x, hON h1⟩, h1, ?_⟩
    have e : (⟨x, hxN⟩ : ↥N) = ⟨u, huN⟩ * ⟨(u : G)⁻¹ * x, hON h1⟩ := by
      apply Subtype.ext
      show x = (u : G) * ((u : G)⁻¹ * x)
      group
    rw [e, map_mul, huE, one_mul]
  · intro x hx s hs
    have hsM : s ∈ D.M := D.sylowM.le hs.1
    set Sb := ((proofS D).subgroupOf D.M).map π with hSb
    have hCS : ⁅C, Sb⁆ ≤ Ũ := by
      rw [Subgroup.commutator_le]
      rintro _ ⟨y, hy, rfl⟩ _ ⟨t, ht, rfl⟩
      rw [← map_commutatorElement]
      refine ⟨⁅y, t⁆, ⟨?_, ?_⟩, rfl⟩
      · show (y : G) * t * (y : G)⁻¹ * (t : G)⁻¹ ∈ L
        have h1 := conj_mem_of_mem_proofS D hV hL hLV hJL ht (y : G)⁻¹ (L.inv_mem hy)
        have e : (y : G) * t * (y : G)⁻¹ * (t : G)⁻¹ =
            (y : G) * ((t : G) * (y : G)⁻¹ * (t : G)⁻¹) := by group
        rw [e]
        exact L.mul_mem hy h1
      · show (y : G) * t * (y : G)⁻¹ * (t : G)⁻¹ ∈ centralizer (proofE D : Set G)
        exact Subgroup.mul_mem _ ((Subgroup.mem_normalizer_iff.1 (hLCE hy) _).1 ht.2)
          (Subgroup.inv_mem _ ht.2)
    have h2 : ⁅⁅C, Sb⁆, C⁆ = ⊥ := by
      refine le_bot_iff.1 ((Subgroup.commutator_mono hCS le_rfl).trans ?_)
      rw [Subgroup.commutator_comm, hcomm]
    have h3 := CFSG.LocalCores.perfect_double_commutator hC.1.1 h2
    have hmem : ⁅π ⟨x, hLM hx⟩, π ⟨s, hsM⟩⁆ ∈ ⁅C, Sb⁆ :=
      Subgroup.commutator_mem_commutator ⟨⟨x, hLM hx⟩, hx, rfl⟩ ⟨⟨s, hsM⟩, hs, rfl⟩
    rw [h3, Subgroup.mem_bot, ← map_commutatorElement, hker] at hmem
    exact hmem

theorem le_normalizer_proofS (D : Data G) {V L : Subgroup G} (hV : InCalW D.M D.T V)
    (hL : F12.IsComponentModO2 D.M L) (hLV : ⁅L, V⁆ ≠ ⊥)
    (hJL : ⁅F12.jOf D.T, L⁆ ≤ pCoreOf 2 L) :
    L ⊔ D.T ≤ normalizer (proofS D : Set G) := by
  have hLE := le_normalizer_proofE D hL hJL
  have hLCE : L ≤ normalizer ((centralizer (proofE D : Set G) : Subgroup G) : Set G) :=
    A1a.le_normalizer_centralizer hLE
  have key : ∀ x ∈ L, ∀ s ∈ proofS D, x * s * x⁻¹ ∈ proofS D := by
    intro x hx s hs
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · have h1 := commutator_mem_of_mem_proofS D hV hL hLV hJL x hx s hs
      have h2 : x * s * x⁻¹ = ⁅x, s⁆ * s := by simp only [commutatorElement_def]; group
      rw [h2]
      exact D.T.mul_mem (uc22p22e_pCoreOf_le_T D h1) hs.1
    · exact (Subgroup.mem_normalizer_iff.1 (hLCE hx) s).1 hs.2
  refine sup_le (fun x hx => ?_) ?_
  · rw [Subgroup.mem_normalizer_iff]
    intro s
    refine ⟨key x hx s, fun hs => ?_⟩
    have := key x⁻¹ (L.inv_mem hx) _ hs
    simpa [mul_assoc] using this
  · exact A1a.le_normalizer_inf Subgroup.le_normalizer
      (A1a.le_normalizer_centralizer (T_le_normalizer_proofE D))

theorem not_commutator_le (D : Data G) (h640 : UC6.R6_40_2 D) {V L : Subgroup G}
    (hV : InCalW D.M D.T V) (hCle : centralizer (D.Z : Set G) ≤ D.M)
    (hL : F12.IsComponentModO2 D.M L) (hU : UniqueMax D.M (L ⊔ D.T)) (hLV : ⁅L, V⁆ ≠ ⊥) :
    ¬ ⁅F12.jOf D.T, L⁆ ≤ pCoreOf 2 L := fun hJL =>
  uc22p22p_not_calCGS_le_of_6_40 D h640 hCle
    (uc22p22p_calCGS_le_of_normalizes D inf_le_left (le_normalizer_proofS D hV hL hLV hJL)
      (fun _ hH hRH => uc22p22p_le_of_uniqueMax hU hH hRH))

end TwelveTwentyFive

theorem twelve_twentyFive (D : Data G) (h640 : UC6.R6_40_2 D) (hFF : W4Thm12McClurg)
    {V : Subgroup G} (hV : InCalW D.M D.T V) (hCle : centralizer (D.Z : Set G) ≤ D.M) :
    (⁅F12.jOf D.T, V⁆ ≠ ⊥ ∧ ¬ UC6.calCGS (CFSG.RankThree.PartOne.pushingUpS D.T) ≤ D.M) ∧
    ∀ L : Subgroup G, F12.IsComponentModO2 D.M L → UniqueMax D.M (L ⊔ D.T) → ⁅L, V⁆ ≠ ⊥ →
      ¬ ⁅F12.jOf D.T, L⁆ ≤ pCoreOf 2 L ∧ ClassicalEvenAltG2Der (UC22.Bar2 L) := by
  refine ⟨uc22p22p_r1225_one_of_6_40 D h640 V hV hCle, fun L hL hU hLV => ?_⟩
  have h2a := TwelveTwentyFive.not_commutator_le D h640 hV hCle hL hU hLV
  exact ⟨h2a, hFF G D.M D.T V L (D.standing.kProper.isKGroup D.M (uc22br4_M_ne_top D))
    D.sylowM hV.1.1 hV.2.2 hL hLV h2a⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
