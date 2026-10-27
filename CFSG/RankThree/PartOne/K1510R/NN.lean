module

public import CFSG.RankThree.PartOne.K1510R.Cent
public import CFSG.RankThree.PartOne.S12.Sec1510Node
public import CFSG.RankThree.PartOne.S15K.Node158E3
public import CFSG.RankThree.PartOne.U5E.Reinst
import CFSG.RankThree.PartOne.U5E.KF1510E
public import CFSG.RankThree.PartOne.S12.Sec1510FiveAut
public import CFSG.RankThree.PartOne.S12.Sec1510FiveSyl

public section

namespace CFSG.RankThree.PartOne.K1510R

open CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.RankThree CFSG.RankThree.LocalRank
  CFSG.RankThree.GroupTheory CFSG.RankThree.PartOne Sec153

variable {G : Type} [Group G] [Finite G]

theorem cent_le_of_LN (h155 : Node155) (h158 : Node158) (h158E3 : S15K.Node158E3)
    (hR : U5E.Reinst5) (hInn : KFInnLayerFive) (hKE : KF1510E) {p : ℕ} {A : Subgroup G} {c : G}
    {L E : Subgroup G} (h15 : Sec15Hyp G p A c L E) (hF : Sec12Facts G p A c L E)
    (hout : Outcome152Five p E A (lieGenerated p E)) {e : G} (heE : e ∈ E) (he1 : e ≠ 1)
    (hcen : CentralizesE p E e) (hLN : ∀ Z ∈ thetaComponentsAt p e, Z ≤ lieNormalizer p E) :
    Subgroup.centralizer ({e} : Set G) ≤ lieNormalizer p E := by
  classical
  have h := h15.h12
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  have hout' : Outcome152 p E A (lieGenerated p E) := Or.inr (Or.inr (Or.inr (Or.inr hout)))
  have hEel : IsElementaryAbelian p ↥E := h.E_elem
  have hAE : A ≤ E := h.A_le_E
  have hAel : IsElementaryAbelian p ↥A := h.A_elem
  have hAcard : Nat.card ↥A = p ^ 3 := h.A_card
  have hNA : ∀ B : Subgroup G, B ≤ A → ¬ IsCyclic ↥B →
      Subgroup.normalizer (B : Set G) ≤ lieNormalizer p E := fun B hBA hBcyc =>
    h158 G p A c L E h15 hF hout' B hBA hBcyc
  have hJ : ∀ Q : Subgroup G, E ≤ Q → Q ≤ Subgroup.normalizer (E : Set G) → IsPGroup p ↥Q →
      thompsonElem p Q = E := fun Q hEQ hQW hQ =>
    Sec15FA.thompson_eq_of_node155 h155 h15 hF hout' hEQ hQW hQ
  have hWN : torusNormalizer E ≤ lieNormalizer p E := torusNormalizer_le_lieNormalizer hp E
  obtain ⟨P, hPsyl, hEP, hPW, hPΩ, hPc⟩ :=
    Sec1510Five.exists_sylow_cent hp h155 h15 hF hout heE hcen
  have hND : ∀ D : Subgroup G,
      (∀ x : G, x ∈ D ↔ x ∈ E ∧ ∀ l ∈ thetaLayer p e, x * l * x⁻¹ * l⁻¹ ∈ thetaCore p e) →
        ¬ IsCyclic ↥D → Subgroup.normalizer (D : Set G) ≤ lieNormalizer p E := by
    intro D hD hcD
    have hDE : D ≤ E := fun x hx => ((hD x).1 hx).1
    rcases hKE G p A c L E h15 hF hout e heE he1 hcen hLN D hD with hcyc | h3 | ⟨A', hA', hDA'⟩
    · exact absurd hcyc hcD
    · exact h158E3 G p A c L E h15 hF hout D hDE h3
    · obtain ⟨c', L', h15', hF', hout''⟩ := hR G p A c L E h15 hF hout A' hA'
      exact h158 G p A' c' L' E h15' hF'
        (Or.inr (Or.inr (Or.inr (Or.inr hout'')))) D hDA' hcD
  exact Sec1510Node.centralizer_le_gen hp hEel hAE hAel hAcard hJ hWN hNA hND heE he1 hLN
    (hInn G p A c L E h15 hF hout e heE he1 hcen hLN) hPsyl hEP (hPW.trans hWN) hPΩ hPc

theorem exists_nonregular_plane (h154 : Node154) (hMod : KFU5Mod) (hAt : KFU5At) {p : ℕ}
    {A : Subgroup G} {c : G} {L E : Subgroup G} (h15 : Sec15Hyp G p A c L E)
    (hF : Sec12Facts G p A c L E) (hout : Outcome152Five p E A (lieGenerated p E)) :
    ∃ D ∈ admissibleTriples p E, D ≤ E ∧ Nat.card ↥D = p ^ 3 ∧
      ∀ b ∈ D, b ≠ 1 → CentralizesE p E b := by
  classical
  obtain ⟨M⟩ := Sec153.nonempty_modData hMod h15 hF hout
  have h := h15.h12
  have hp := h.prime
  have hp5 : 5 ≤ p := by
    have h3 := h.three_lt
    by_contra hlt
    have h4 : p = 4 := by omega
    exact absurd (h4 ▸ hp) (by norm_num)
  obtain ⟨f, hf, hpf, ⟨e₀⟩, -, hcardE, -⟩ := id hout
  obtain ⟨t, ht, -⟩ := Sec153.exists_reflection_swap hp M.θ M.refl 0 1 (by decide)
  have hAtt := hAt G p A c L E f h15 hF hout hf hpf ⟨e₀⟩ t ht
  refine ⟨autFixedInG E t, U5E.autFixedInG_mem_admissible h15 hcardE ht hAtt,
    Subgroup.map_subtype_le _, S15K.card_autFixedInG_five h hcardE ht, ?_⟩
  intro b hb hb1
  by_cases hp7 : 7 ≤ p
  · exact centralizesE_of_seven hp hp7 h15 hF h154 hout b
  · have h6 : p ≠ 6 := fun h6 => by rw [h6] at hp; norm_num at hp
    have hp5eq : p = 5 := by omega
    subst hp5eq
    exact centralizesE_of_mem_autFixedInG_five h M ht hb hb1

theorem sq_dvd_card_of_noncyclic {p : ℕ} (hp : p.Prime) {B : Subgroup G}
    (hB : IsElementaryAbelian p ↥B) (hnc : ¬ IsCyclic ↥B) : p ^ 2 ∣ Nat.card ↥B := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, hk⟩ := (IsElementaryAbelian.isPGroup p ↥B).exists_card_eq
  rcases Nat.lt_or_ge k 2 with hk2 | hk2
  · exfalso
    apply hnc
    interval_cases k
    · have : Nat.card ↥B = 1 := by simpa using hk
      have : Subsingleton ↥B := (Nat.card_eq_one_iff_unique.1 this).1
      exact isCyclic_of_subsingleton
    · exact isCyclic_of_prime_card (by simpa using hk)
  · rw [hk]
    exact pow_dvd_pow p hk2

theorem normalizer_le_of_noncyclic (h154 : Node154) (h155 : Node155) (h158 : Node158)
    (h158E3 : S15K.Node158E3) (h159 : Node159Five) (hR : U5E.Reinst5) (hInn : KFInnLayerFive)
    (hKE : KF1510E) (hMod : KFU5Mod) (hAt : KFU5At) {p : ℕ} {A : Subgroup G} {c : G}
    {L E : Subgroup G} (h15 : Sec15Hyp G p A c L E) (hF : Sec12Facts G p A c L E)
    (hout : Outcome152Five p E A (lieGenerated p E)) {B : Subgroup G} (hBE : B ≤ E)
    (hB : ¬ IsCyclic ↥B) : Subgroup.normalizer (B : Set G) ≤ lieNormalizer p E := by
  classical
  have h := h15.h12
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  have hout' : Outcome152 p E A (lieGenerated p E) := Or.inr (Or.inr (Or.inr (Or.inr hout)))
  have hEel : IsElementaryAbelian p ↥E := h.E_elem
  have hEcard : Nat.card ↥E = p ^ 4 := by
    obtain ⟨-, -, -, -, -, hc, -⟩ := hout
    exact hc
  have hJ : ∀ Q : Subgroup G, E ≤ Q → Q ≤ Subgroup.normalizer (E : Set G) → IsPGroup p ↥Q →
      thompsonElem p Q = E := fun Q hEQ hQW hQ =>
    Sec15FA.thompson_eq_of_node155 h155 h15 hF hout' hEQ hQW hQ
  have hWN : torusNormalizer E ≤ lieNormalizer p E := torusNormalizer_le_lieNormalizer hp E
  obtain ⟨D, hDB, hDE, hDcard, hDcen⟩ := exists_nonregular_plane h154 hMod hAt h15 hF hout
  have hBel : IsElementaryAbelian p ↥B := Sec159.isElementaryAbelian_of_le hEel hBE
  have hsq : p ^ 2 ∣ Nat.card ↥B := sq_dvd_card_of_noncyclic hp hBel hB
  obtain ⟨K, hKcard, -, hKB⟩ := Sylow.exists_subgroup_card_pow_prime_le_le hp (H := ⊥) (L := B)
    (n := 2) (by rw [Subgroup.card_bot]; exact one_dvd _) hsq bot_le
  obtain ⟨b, hbDK, hb1⟩ := S15K.exists_ne_one_mem_inf_of_card hp hEcard hDE (hKB.trans hBE)
    (by rw [hDcard]) hKcard
  have hbD : b ∈ D := hbDK.1
  have hbB : b ∈ B := hKB hbDK.2
  have hbE : b ∈ E := hDE hbD
  have hLN : ∀ Z ∈ thetaComponentsAt p b, Z ≤ lieNormalizer p E := fun Z hZ =>
    h159 G p A c L E h15 hF hout Z ⟨D, hDB, mem_thetaComponentFamily_iff.2 ⟨b, hbD, hb1, hZ⟩⟩
  have hCb := cent_le_of_LN h155 h158 h158E3 hR hInn hKE h15 hF hout hbE hb1 (hDcen b hbD hb1) hLN
  have hC : Subgroup.centralizer (B : Set G) ≤ lieNormalizer p E :=
    (Subgroup.centralizer_le (Set.singleton_subset_iff.2 hbB)).trans hCb
  exact Sec15FA.normalizer_le_of_centralizer_le hp hEel hJ hBE hWN hC

end CFSG.RankThree.PartOne.K1510R
