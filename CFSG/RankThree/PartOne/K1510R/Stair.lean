module

public import CFSG.RankThree.PartOne.K1510R.StairQ
public import CFSG.RankThree.PartOne.K1510R.StairThomp
public import CFSG.RankThree.PartOne.S12.Sec1510Node
import CFSG.RankThree.PartOne.S10.AmbientTheta
import CFSG.RankThree.PartOne.S12.Sec12FusChoice

public section

namespace CFSG.RankThree.PartOne.K1510R

open CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.RankThree CFSG.RankThree.LocalRank
  CFSG.RankThree.GroupTheory CFSG.RankThree.PartOne Sec153

variable {G : Type} [Group G] [Finite G]

theorem stair_of_empty {p : ℕ} (hp5 : p = 5) (h155 : Node155) {A : Subgroup G} {c : G}
    {L E : Subgroup G} (h15 : Sec15Hyp G p A c L E) (hF : Sec12Facts G p A c L E)
    (hout : Outcome152Five p E A (lieGenerated p E)) (M : ModData p E)
    (hNn : ∀ B : Subgroup G, B ≤ E → ¬ IsCyclic ↥B →
      Subgroup.normalizer (B : Set G) ≤ lieNormalizer p E)
    {e : G} (heE : e ∈ E) (hempty : ∀ Z : Subgroup G, Z ∉ thetaComponentsAt p e) :
    Subgroup.centralizer ({e} : Set G) ≤ lieNormalizer p E := by
  classical
  subst hp5
  have h := h15.h12
  have hp := h.prime
  have : Fact (Nat.Prime 5) := ⟨hp⟩
  have hout' : Outcome152 5 E A (lieGenerated 5 E) := Or.inr (Or.inr (Or.inr (Or.inr hout)))
  have hEel : IsElementaryAbelian 5 ↥E := h.E_elem
  have hEp : IsPGroup 5 ↥E := hEel.isPGroup 5 ↥E
  have hEcard : Nat.card ↥E = 5 ^ 4 := by
    obtain ⟨-, -, -, -, -, hc, -⟩ := hout
    exact hc
  have hAE : A ≤ E := h.A_le_E
  have hAel : IsElementaryAbelian 5 ↥A := h.A_elem
  have hAcard : Nat.card ↥A = 5 ^ 3 := h.A_card
  have hNA : ∀ B : Subgroup G, B ≤ A → ¬ IsCyclic ↥B →
      Subgroup.normalizer (B : Set G) ≤ lieNormalizer 5 E := fun B hBA hBc =>
    hNn B (hBA.trans hAE) hBc
  have hJ : ∀ Q : Subgroup G, E ≤ Q → Q ≤ Subgroup.normalizer (E : Set G) → IsPGroup 5 ↥Q →
      thompsonElem 5 Q = E := fun Q hEQ hQW hQ =>
    Sec15FA.thompson_eq_of_node155 h155 h15 hF hout' hEQ hQW hQ
  have hWN : torusNormalizer E ≤ lieNormalizer 5 E := torusNormalizer_le_lieNormalizer hp E
  set Ce : Subgroup G := Subgroup.centralizer ({e} : Set G) with hCe
  have hEC : E ≤ Ce := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.2
      (congrArg Subtype.val (hEel.is_comm.comm ⟨x, hx⟩ ⟨e, heE⟩))
  have hle : E ≤ Ce ⊓ Subgroup.normalizer (E : Set G) := le_inf hEC Subgroup.le_normalizer
  obtain ⟨P, hP0, hEP⟩ := Sec12Fus.exists_isSylowOf_ge (p := 5) hle hEp
  have hPsyl : IsSylowOf 5 P Ce := Sec15FA.sylow_of_torus_normalizer hJ hP0 hEP
  have hPW : P ≤ Subgroup.normalizer (E : Set G) := hP0.1.trans inf_le_right
  have hPC : P ≤ Ce := hP0.1.trans inf_le_left
  have hPp : IsPGroup 5 ↥P := hP0.2.1
  obtain ⟨PW, hPWsyl, hPPW⟩ := Sec12Fus.exists_isSylowOf_ge (p := 5) hPW hPp
  set θ : Subgroup ↥Ce := aschbacherSolvableCore 5 ↥Ce with hθ
  have hθn : θ.Normal := inferInstanceAs (aschbacherSolvableCore 5 ↥Ce).Normal
  have hThetaEmpty : thetaComponents 5 ↥Ce = ∅ := by
    refine Set.eq_empty_iff_forall_notMem.2 fun Y hY => ?_
    exact hempty (Y.map Ce.subtype) ⟨Y, hY, rfl⟩
  have hlayer : layer (↥Ce ⧸ θ) = ⊥ := by
    rw [← Sec1510Node.layer_quotient_eq (H := ↥Ce) hp, hThetaEmpty, sSup_empty, Subgroup.map_bot]
  have hPsyl' : IsSylowOf 5 (P.subgroupOf Ce) ⊤ :=
    ⟨le_top, hPsyl.2.1.comap_subtype, by rw [Subgroup.relIndex_top_right]; exact hPsyl.2.2⟩
  obtain ⟨Q', hQ'P, hQ'norm, hQ'frat, hQ'cent⟩ := exists_Q (V := θ) (P := P.subgroupOf Ce) hlayer
    (fun M' hMn hnil hMp => Sec1510Node.theta_quotient_nilpotent_bot hp hMn hnil hMp) hPsyl'
  set Q : Subgroup G := Q'.map Ce.subtype with hQdef
  have hQsub : Q.subgroupOf Ce = Q' := Subgroup.comap_map_eq_self_of_injective Ce.subtype_injective Q'
  have hQP : Q ≤ P := by
    rintro _ ⟨q', hq', rfl⟩
    exact Subgroup.mem_subgroupOf.1 (hQ'P hq')
  have hQC : Q ≤ Ce := hQP.trans hPC
  have hQnormP : ∀ g ∈ P, ∀ q ∈ Q, g * q * g⁻¹ ∈ Q := by
    rintro g hg _ ⟨q', hq', rfl⟩
    have hg' : (⟨g, hPC hg⟩ : ↥Ce) ∈ P.subgroupOf Ce := hg
    exact ⟨_, hQ'norm _ hg' q' hq', rfl⟩
  have hQcent : ∀ x ∈ P, (∀ q ∈ Q, x * q = q * x) → x ∈ Q := by
    intro x hx hc
    have hx' : (⟨x, hPC hx⟩ : ↥Ce) ∈ P.subgroupOf Ce := hx
    have := hQ'cent _ hx' (fun q' hq' => Subtype.ext (hc q' ⟨q', hq', rfl⟩))
    exact ⟨_, this, rfl⟩
  have hQnormE : ∀ u ∈ E, ∀ q ∈ Q, u * q * u⁻¹ ∈ Q := fun u hu q hq => hQnormP u (hEP hu) q hq
  have hEQ3 : 5 ^ 3 ≤ Nat.card ↥(E ⊓ Q) := by
    by_cases hcQ : ∀ q ∈ Q, ∀ u ∈ E, q * u = u * q
    · have hEQ : E ≤ Q := fun u hu => hQcent u (hEP hu) (fun q hq => (hcQ q hq u hu).symm)
      have : E ⊓ Q = E := inf_eq_left.2 hEQ
      rw [this, hEcard]
      exact Nat.pow_le_pow_right (by norm_num) (by norm_num)
    · push Not at hcQ
      obtain ⟨y, hyQ, u, huE, hyu⟩ := hcQ
      have hyP : y ∈ P := hQP hyQ
      have hyN : y ∈ Subgroup.normalizer (E : Set G) := hPW hyP
      obtain ⟨k, hk⟩ := hPp ⟨y, hyP⟩
      have hyk : y ^ (5 ^ k) = 1 := by simpa using congrArg Subtype.val hk
      have hpow : conjAut E y hyN ^ (5 ^ k) = 1 := by
        unfold conjAut
        rw [← map_pow]
        have : (⟨y, hyN⟩ : ↥(Subgroup.normalizer (E : Set G))) ^ (5 ^ k) = 1 :=
          Subtype.ext (by simpa using hyk)
        rw [this, map_one]
      have hne : conjAut E y hyN ≠ 1 := by
        intro h1
        apply hyu
        have h2 := Equivariance.coe_conjAut hyN ⟨u, huE⟩
        rw [h1] at h2
        have h3 : u = y * u * y⁻¹ := h2
        calc y * u = y * u * y⁻¹ * y := by group
          _ = u * y := by rw [← h3]
      exact card_inf_ge_of_moved h M hEcard hQnormE hyQ hyN hpow hne
  have hR : ∀ R : Subgroup G, R ≤ PW → IsElementaryAbelian 5 ↥R → 5 ^ 3 ≤ Nat.card ↥R → R ≤ E :=
    fun R hRPW hRel hRc => le_E_of_elemAb3 hp h155 h15 hF hout hPWsyl hRPW
      (fun b hb => CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 5) (A := R) b hb)
      (fun a ha b hb => congrArg Subtype.val (hRel.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)) hRc
  obtain ⟨hJE, hJnc⟩ := thompsonElem_le_E hp hEel hR (hQP.trans hPPW) hEQ3
  have hNJ : ∀ n ∈ Subgroup.normalizer (Q : Set G), n ∈ lieNormalizer 5 E := fun n hn =>
    hNn _ hJE hJnc (Sec15FA.mem_normalizer_thompsonElem hn)
  have hVN : θ ≤ (lieNormalizer 5 E).subgroupOf Ce := by
    have h1 : E ≤ Subgroup.normalizer
        ((inSubgroup (aschbacherSolvableCore 5) Ce : Subgroup G) : Set G) :=
      le_normalizer_theta_of_le_normalizer hp (hEC.trans Subgroup.le_normalizer)
    have h2 : ¬ 5 ∣ Nat.card ↥(inSubgroup (aschbacherSolvableCore 5) Ce) :=
      (theta_solvable_and_not_dvd hp Ce).2
    have h3 := Sec159.le_of_pPrime_normalized hp hAel hAcard hNA (fun a ha => h1 (hAE ha)) h2
    exact fun v hv => Subgroup.mem_subgroupOf.2 (h3 ⟨v, hv, rfl⟩)
  have hQ'N : Q' ≤ (lieNormalizer 5 E).subgroupOf Ce := fun q hq =>
    Subgroup.mem_subgroupOf.2 (hWN (hPW (hQP ⟨q, hq, rfl⟩)))
  have hN' : ∀ n ∈ Subgroup.normalizer (Q' : Set ↥Ce), n ∈ (lieNormalizer 5 E).subgroupOf Ce := by
    intro n hn
    refine Subgroup.mem_subgroupOf.2 (hNJ _ ?_)
    rw [← hQsub] at hn
    exact Sec1510Node.mem_normalizer_of_subgroupOf hQC hn
  intro g hg
  obtain ⟨k, hk, hkn⟩ := hQ'frat ⟨g, hg⟩
  have hk' : k ∈ (lieNormalizer 5 E).subgroupOf Ce := (sup_le hVN hQ'N) hk
  have h3 := Subgroup.mul_mem _ hk' (hN' _ hkn)
  have h4 : (⟨g, hg⟩ : ↥Ce) ∈ (lieNormalizer 5 E).subgroupOf Ce := by simpa using h3
  exact Subgroup.mem_subgroupOf.1 h4

end CFSG.RankThree.PartOne.K1510R
